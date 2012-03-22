#include <string>
#include <map>

#include "llvm/GlobalValue.h"
#include "llvm/CallingConv.h"
#include "llvm/DerivedTypes.h"
#include "llvm/InstrTypes.h"
#include "llvm/Instructions.h"
#include "llvm/Support/raw_ostream.h"

#include "Port.hpp"
#include "Channel.hpp"
#include "SimpleChannel.hpp"
#include "SCCFactory.hpp"
#include "SCElab.h"
#include "PromelaWriter.h"
#include "SCConstruct.hpp"
#include "EventConstruct.hpp"
#include "ReadConstruct.hpp"
#include "WriteConstruct.hpp"
#include "Process.hpp"
#include "IRModule.hpp"
#include "SCJit.hpp"

#include "utils.h"
#include "config.h"

static Instruction* pointerToInst;
static Process* currentProcess;

/***************************************************************************
 *************** Static functions ******************************************
 **************************************************************************/

// isInlineAsm - Check if the instruction is a call to an inline asm chunk
static bool isInlineAsm(const Instruction & I)
{
	if (isa < CallInst > (&I) && isa < InlineAsm > (I.getOperand(0)))
		return true;
	return false;
}

// isInlinableInst - Attempt to inline instructions into their uses to build
// trees as much as possible.  To do this, we have to consistently decide
// what is acceptable to inline, so that variable declarations don't get
// printed and an extra copy of the expr is not emitted.
//
static bool isInlinableInst(const Instruction & I)
{
	// Always inline cmp instructions, even if they are shared by multiple
	// expressions.  GCC generates horrible code if we don't.
	if (isa < CmpInst > (I))
		return true;

	// Must be an expression, must be used exactly once.  If it is dead, we
	// emit it inline where it would go.
	if (I.getType() == Type::getVoidTy(I.getContext())
		|| !I.hasOneUse() || isa < TerminatorInst > (I)
		|| isa < CallInst > (I) || isa < PHINode > (I)
		|| isa < LoadInst > (I) || isa < VAArgInst > (I)
		|| isa < InsertElementInst > (I)
		|| isa < InsertValueInst > (I))
		// Don't inline a load across a store or other bad things!
		return false;

	// Must not be used in inline asm, extractelement, or shufflevector.
	if (I.hasOneUse()) {
		const Instruction & User =
			cast < Instruction > (*I.use_back());
		if (isInlineAsm(User) || isa < ExtractElementInst > (User)
			|| isa < ShuffleVectorInst > (User))
			return false;
	}
	// Only inline instruction it if it's use is in the same BB as the inst.
	return I.getParent() == cast < Instruction >
		(I.use_back())->getParent();
}

// isDirectAlloca - Define fixed sized allocas in the entry block as direct
// variables which are accessed with the & operator.  This causes GCC to
// generate significantly better code than to emit alloca calls directly.
//
static const AllocaInst *isDirectAlloca(const Value * V)
{
	const AllocaInst *AI = dyn_cast < AllocaInst > (V);
	if (!AI)
		return false;
	if (AI->isArrayAllocation())
		return 0;	// FIXME: we can also inline fixed size array allocas!
	if (AI->getParent() !=
		&AI->getParent()->getParent()->getEntryBlock())
		return 0;
	return AI;
}

/***************************************************************************
 ******************* Constructors ******************************************
 **************************************************************************/

PromelaWriter::PromelaWriter(Frontend* fe, formatted_raw_ostream &o, bool encodeEventsAsBool, bool useRelativeClocks, bool bug)
	: ModulePass(&ID), Out(o), IL(0), Mang(0), LI(0), 
	  TheModule(0), TAsm(0), TD(0), OpaqueCounter(0), NextAnonValueNumber(0) {
	FPCounter = 0;
	this->sccfactory = fe->getConstructs();
	this->elab = fe->getElab();
	this->scjit = fe->getJit();
	this->relativeClocks = useRelativeClocks;
	this->eventsAsBool = encodeEventsAsBool;
	this->insertBug = bug;
}

PromelaWriter::PromelaWriter(formatted_raw_ostream &o)
	: ModulePass(&ID), Out(o), IL(0), Mang(0), LI(0), 
	  TheModule(0), TAsm(0), TD(0), OpaqueCounter(0), NextAnonValueNumber(0) {
	FPCounter = 0;
}


/***************************************************************************
 **************** Print functions ******************************************
 **************************************************************************/

/// printStructReturnPointerFunctionType - This is like printType for a struct
/// return type, except, instead of printing the type as void (*)(Struct*, ...)
/// print it as "Struct (*)(...)", for struct return functions.
void PromelaWriter::
printStructReturnPointerFunctionType(formatted_raw_ostream & Out,
				const AttrListPtr & PAL,
				const PointerType * TheTy)
{
	const FunctionType *FTy = cast < FunctionType > (TheTy->getElementType());
	std::stringstream FunctionInnards;
	FunctionInnards << " (*) (";
	bool PrintedType = false;

	FunctionType::param_iterator I = FTy->param_begin(), E =
		FTy->param_end();
	const Type *RetTy =
		cast < PointerType > (I->get())->getElementType();
	unsigned Idx = 1;
	for (++I, ++Idx; I != E; ++I, ++Idx) {
		if (PrintedType)
			FunctionInnards << ", ";
		const Type *ArgTy = *I;
		if (PAL.paramHasAttr(Idx, Attribute::ByVal)) {
			assert(isa < PointerType > (ArgTy));
			ArgTy =	cast < PointerType > (ArgTy)->getElementType();
		}
		printType(FunctionInnards, ArgTy,
			/*isSigned= */ PAL.paramHasAttr(Idx,
							Attribute::SExt),
			"");
		PrintedType = true;
	}
	if (FTy->isVarArg()) {
		if (PrintedType)
			FunctionInnards << ", ...";
	} else if (!PrintedType) {
		FunctionInnards << "void";
	}
	FunctionInnards << ')';
	std::string tstr = FunctionInnards.str();
	printType(Out, RetTy,
		/*isSigned= */ PAL.paramHasAttr(0, Attribute::SExt),
		tstr);
}

raw_ostream &
PromelaWriter::printSimpleType(formatted_raw_ostream & Out,
			const Type * Ty, bool isSigned,
			const std::string & NameSoFar)
{
	assert((Ty->isPrimitiveType() || Ty->isInteger()
			|| isa < VectorType > (Ty))
		&& "Invalid type for printSimpleType");

	switch (Ty->getTypeID()) {
	case Type::VoidTyID:
		return Out << "void ";
	case Type::IntegerTyID:{
		unsigned NumBits = cast < IntegerType > (Ty)->getBitWidth();
		if (NumBits == 1)
			return Out << "bit " + NameSoFar;
		else if (NumBits <= 8)
			return Out << "byte " + NameSoFar;
		else if (NumBits <= 16)
			return Out << "short " + NameSoFar;
		else
			return Out << "int " + NameSoFar;
	}
	case Type::FloatTyID:
		triggerError(Out, "NYI : float type");
	case Type::DoubleTyID:
		triggerError(Out, "NYI : double type");
	case Type::X86_FP80TyID:
	case Type::PPC_FP128TyID:
	case Type::FP128TyID:
		triggerError(Out, "NYI : long type");
	case Type::VectorTyID:{
		triggerError(Out, "NYI : Vector type");
		const VectorType *VTy = cast < VectorType > (Ty);
		printSimpleType(Out, VTy->getElementType(),
				isSigned,
				NameSoFar + "[" + utostr(TD->getTypeAllocSize(VTy))+ "]");		
	}

	default:
#ifndef NDEBUG
		errs() << "Unknown primitive type: " << *Ty << "\n";
#endif
		llvm_unreachable(0);
	}
}

std::ostream &
PromelaWriter::printSimpleType(std::ostream & Out, const Type * Ty,
			bool isSigned,
			const std::string & NameSoFar)
{
	assert((Ty->isPrimitiveType() || Ty->isInteger()
			|| isa < VectorType > (Ty))
		&& "Invalid type for printSimpleType");

	if (NameSoFar != "")
		Out << NameSoFar << " : ";

	switch (Ty->getTypeID()) {
	case Type::VoidTyID:
		return Out << "void ";
	case Type::IntegerTyID:{
		unsigned NumBits =
			cast < IntegerType > (Ty)->getBitWidth();
		return Out << (isSigned ? "sint" : "uint") << "["
			   << NumBits << "]";
	}
	case Type::FloatTyID:
		return Out << "float ";
	case Type::DoubleTyID:
		return Out << "double ";
		// Lacking emulation of FP80 on PPC, etc., we assume whichever of these is
		// present matches host 'long double'.
	case Type::X86_FP80TyID:
	case Type::PPC_FP128TyID:
	case Type::FP128TyID:
		return Out << "long double ";

	case Type::VectorTyID:{
		triggerError(this->Out, "NYI : Vector type");
		const VectorType *VTy = cast < VectorType > (Ty);
		return printSimpleType(Out, VTy->getElementType(),
				isSigned,
				" __attribute__((vector_size("
				+
				utostr(TD->getTypeAllocSize(VTy)) + " ))) ");
	}

	default:
#ifndef NDEBUG
		errs() << "Unknown primitive type: " << *Ty << "\n";
#endif
		llvm_unreachable(0);
	}
}

// Pass the Type* and the variable name and this prints out the variable
// declaration.
//
raw_ostream &
PromelaWriter::printType(formatted_raw_ostream & Out,
			const Type * Ty,
			bool isSigned, const std::string & NameSoFar,
			bool IgnoreName, const AttrListPtr & PAL)
{
	if (Ty->isPrimitiveType() || Ty->isInteger() || isa < VectorType > (Ty)) {
		printSimpleType(Out, Ty, isSigned, NameSoFar);
		return Out;
	}
	// Check to see if the type is named.
	if (!IgnoreName || isa < OpaqueType > (Ty)) {
		std::map < const Type *, std::string >::iterator ITN = TypeNames.find(Ty), ETN = TypeNames.end();
		if (ITN != ETN) {
			std::string tName = ITN->second;
			return Out << tName << " " << NameSoFar;
		}
	}

	switch (Ty->getTypeID()) {
	case Type::FunctionTyID:{
		ErrorMsg << "NYI : use of complex type : FunctionTy : " << NameSoFar;
		triggerError(Out);

		const FunctionType *FTy =
			cast < FunctionType > (Ty);
		std::stringstream FunctionInnards;
		FunctionInnards << " (" << NameSoFar << ") (";
		unsigned Idx = 1;
		for (FunctionType::param_iterator I =
			     FTy->param_begin(), E = FTy->param_end();
		     I != E; ++I) {
			const Type *ArgTy = *I;
			if (PAL.paramHasAttr(Idx, Attribute::ByVal)) {
				assert(isa < PointerType >(ArgTy));
				ArgTy =	cast < PointerType > (ArgTy)->getElementType();
			}
			if (I != FTy->param_begin())
				FunctionInnards << ", ";
			printType(FunctionInnards, ArgTy, PAL.paramHasAttr(Idx, Attribute::SExt), "");
			++Idx;
		}
		if (FTy->isVarArg()) {
			if (FTy->getNumParams())
				FunctionInnards << ", ...";
		} else if (!FTy->getNumParams()) {
			FunctionInnards << "void";
		}
		FunctionInnards << ')';
		std::string tstr = FunctionInnards.str();
		printType(Out, FTy->getReturnType(), PAL.paramHasAttr(0, Attribute::SExt), tstr);
		return Out;
	}
	case Type::StructTyID:{
		const StructType *STy = cast < StructType > (Ty);
		TRACE_4("/**** Handling StructTy type in printType() ****/\n");
		Out << NameSoFar + " {\n";
		unsigned Idx = 0;
		bool fieldPrinted = false;
		for (StructType::element_iterator I = STy->element_begin(), E = STy->element_end(); I != E; ++I) {
			TRACE_4("\n/**** Dumping struct element in printType() ****/\n");
			if (! isSystemCType(*I)) {
				
				if (fieldPrinted)
					Out << ";\n";
				else
					Out << " ";
				printType(Out, *I, false, "field" + utostr(Idx));
				fieldPrinted = true;
			}
			Idx++;
		}
		TRACE_4("\n/**** struct elements printed ****/\n");
		Out << '}';
		return Out;
	}

	case Type::PointerTyID:{
		const PointerType *PTy = cast < PointerType > (Ty);
		std::string ptrName = NameSoFar;

		TRACE_4("/**** Handling PointerTy type in printType() ****/\n");

		if (isa < ArrayType > (PTy->getElementType()) ||
			isa < VectorType > (PTy->getElementType()))
			ptrName = "(" + ptrName + ")";

		if (!PAL.isEmpty())
			// Must be a function ptr cast!
			return printType(Out, PTy->getElementType(), false, ptrName, true, PAL);
		return printType(Out, PTy->getElementType(), false, ptrName);
	}

	case Type::ArrayTyID:{
		ErrorMsg <<
			"NYI : use of complex type : ArrayTy : " <<
			NameSoFar;
		triggerError(Out);

		const ArrayType *ATy = cast < ArrayType > (Ty);
		unsigned NumElements = ATy->getNumElements();
		if (NumElements == 0)
			NumElements = 1;
		// Arrays are wrapped in structs to allow them to have normal
		// value semantics (avoiding the array "decay").
		Out << NameSoFar << " { ";
		printType(Out, ATy->getElementType(), false,
			"array[" + utostr(NumElements) + "]");
		return Out << "; }";
	}

	case Type::OpaqueTyID:{
		ErrorMsg <<"NYI : use of complex type : OpaqueTy : " <<	NameSoFar;
		triggerError(Out);

		std::string TyName = "struct opaque_" + itostr(OpaqueCounter++);
		assert(TypeNames.find(Ty) == TypeNames.end());
		insertTypeName(Ty, TyName);
		return Out << TyName << ' ' << NameSoFar;
	}
	default:
		llvm_unreachable("Unhandled case in getTypeProps!");
	}

	return Out;
}


// Pass the Type* and the variable name and this prints out the variable
// declaration.
//
std::ostream &
PromelaWriter::printType(std::ostream & Out,
			const Type * Ty,
			bool isSigned, const std::string & NameSoFar,
			bool IgnoreName, const AttrListPtr & PAL)
{
	if (Ty->isPrimitiveType() || Ty->isInteger()
		|| isa < VectorType > (Ty)) {
		printSimpleType(Out, Ty, isSigned, NameSoFar);
		return Out;
	}
	// Check to see if the type is named.
	if (!IgnoreName || isa < OpaqueType > (Ty)) {
		if (isSystemCType(Ty))
			return Out;

		std::map < const Type *, std::string >::iterator I = TypeNames.find(Ty);
		if (I != TypeNames.end())
			return Out << I->second << ' ' << NameSoFar;
	}

	switch (Ty->getTypeID()) {
	case Type::FunctionTyID:{
		ErrorMsg << "NYI : use of complex type : FunctionTy : " << NameSoFar;
		triggerError(this->Out);

		const FunctionType *FTy =
			cast < FunctionType > (Ty);
		std::stringstream FunctionInnards;
		FunctionInnards << " (" << NameSoFar << ") (";
		unsigned Idx = 1;
		for (FunctionType::param_iterator I =
			     FTy->param_begin(), E = FTy->param_end();
		     I != E; ++I) {
			const Type *ArgTy = *I;
			if (PAL.
				paramHasAttr(Idx, Attribute::ByVal)) {
				assert(isa < PointerType >
					(ArgTy));
				ArgTy =
					cast < PointerType >
					(ArgTy)->getElementType();
			}
			if (I != FTy->param_begin())
				FunctionInnards << ", ";
			printType(FunctionInnards, ArgTy,
				/*isSigned= */
				PAL.paramHasAttr(Idx,
						Attribute::
						SExt), "");
			++Idx;
		}
		if (FTy->isVarArg()) {
			if (FTy->getNumParams())
				FunctionInnards << ", ...";
		} else if (!FTy->getNumParams()) {
			FunctionInnards << "void";
		}
		FunctionInnards << ')';
		std::string tstr = FunctionInnards.str();
		printType(Out, FTy->getReturnType(),
			/*isSigned= */ PAL.paramHasAttr(0,
							Attribute::
							SExt),
			tstr);
		return Out;
	}
	case Type::StructTyID:{
		const StructType *STy = cast < StructType > (Ty);
		TRACE_4("/**** Handling StructTy type in printType() ****/\n");
		Out << NameSoFar + " {\n";
		unsigned Idx = 0;
		bool fieldPrinted = false;
		for (StructType::element_iterator I = STy->element_begin(), E = STy->element_end(); I != E; ++I) {
			TRACE_4("\n/**** dump struct element ****/\n");
			if (isSystemCType(*I)) {
				if (fieldPrinted)
					Out << " , ";
				else
					Out << " ";
				printType(Out, *I, false, "field" + utostr(Idx));
//			Out << ";\n";
				fieldPrinted = true;
			}
			Idx++;
		}
		TRACE_4("\n/**** struct elements printed ****/\n");

		Out << '}';
		return Out;
	}

	case Type::PointerTyID:{
		const PointerType *PTy = cast < PointerType > (Ty);
		std::string ptrName = "*" + NameSoFar;

		TRACE_4("/**** Handling PointerTy type in printType() ****/\n");

		if (isa < ArrayType > (PTy->getElementType()) ||
			isa < VectorType > (PTy->getElementType()))
			ptrName = "(" + ptrName + ")";

		if (!PAL.isEmpty())
			// Must be a function ptr cast!
			return printType(Out, PTy->getElementType(), false, ptrName, true, PAL);
		return printType(Out, PTy->getElementType(), false, ptrName);
	}

	case Type::ArrayTyID:{
		ErrorMsg <<
			"NYI : use of complex type : ArrayTy : " <<
			NameSoFar;
		triggerError(this->Out);

		const ArrayType *ATy = cast < ArrayType > (Ty);
		unsigned NumElements = ATy->getNumElements();
		if (NumElements == 0)
			NumElements = 1;
		// Arrays are wrapped in structs to allow them to have normal
		// value semantics (avoiding the array "decay").
		Out << NameSoFar << " { ";
		printType(Out, ATy->getElementType(), false,
			"array[" + utostr(NumElements) + "]");
		return Out << "; }";
	}

	case Type::OpaqueTyID:{
		ErrorMsg <<
			"NYI : use of complex type : OpaqueTy : " <<
			NameSoFar;
		triggerError(this->Out);

		std::string TyName =
			"struct opaque_" + itostr(OpaqueCounter++);
		assert(TypeNames.find(Ty) == TypeNames.end());
		insertTypeName(Ty, TyName);
		return Out << TyName << ' ' << NameSoFar;
	}
	default:
		llvm_unreachable("Unhandled case in getTypeProps!");
	}

	return Out;
}


void
PromelaWriter::printConstantArray(ConstantArray * CPA, bool Static)
{

	// As a special case, print the array as a string if it is an array of
	// ubytes or an array of sbytes with positive values.
	//
	const Type *ETy = CPA->getType()->getElementType();
	bool isString = (ETy == Type::getInt8Ty(CPA->getContext()) ||
			ETy == Type::getInt8Ty(CPA->getContext()));

	// Make sure the last character is a null char, as automatically added by C
	if (isString && (CPA->getNumOperands() == 0 ||
				!cast < Constant >
				(*(CPA->op_end() - 1))->isNullValue()))
		isString = false;

	if (isString) {
		Out << '\"';
		// Keep track of whether the last number was a hexadecimal escape
		bool LastWasHex = false;

		// Do not include the last character, which we know is null
		for (unsigned i = 0, e = CPA->getNumOperands() - 1; i != e;
		     ++i) {
			unsigned char C =
				cast < ConstantInt >
				(CPA->getOperand(i))->getZExtValue();

			// Print it out literally if it is a printable character.  The only thing
			// to be careful about is when the last letter output was a hex escape
			// code, in which case we have to be careful not to print out hex digits
			// explicitly (the C compiler thinks it is a continuation of the previous
			// character, sheesh...)
			//
			if (isprint(C) && (!LastWasHex || !isxdigit(C))) {
				LastWasHex = false;
				if (C == '"' || C == '\\')
					Out << "\\" << (char) C;
				else
					Out << (char) C;
			} else {
				LastWasHex = false;
				switch (C) {
				case '\n':
					Out << "\\n";
					break;
				case '\t':
					Out << "\\t";
					break;
				case '\r':
					Out << "\\r";
					break;
				case '\v':
					Out << "\\v";
					break;
				case '\a':
					Out << "\\a";
					break;
				case '\"':
					Out << "\\\"";
					break;
				case '\'':
					Out << "\\\'";
					break;
				default:
					Out << "\\x";
					Out << (char) ((C / 16 < 10)
						? (C / 16 +
							'0') : (C / 16 -
								10 +
								'A'));
					Out << (char) (((C & 15) < 10)
						? ((C & 15) +
							'0') : ((C & 15)
								- 10 +
								'A'));
					LastWasHex = true;
					break;
				}
			}
		}
		Out << '\"';
	} else {
		Out << '{';
		if (CPA->getNumOperands()) {
			Out << ' ';
			printConstant(cast < Constant >
				(CPA->getOperand(0)), Static);
			for (unsigned i = 1, e = CPA->getNumOperands();
			     i != e; ++i) {
				Out << ", ";
				printConstant(cast < Constant >
					(CPA->getOperand(i)),
					Static);
			}
		}
		Out << " }";
	}
}

void PromelaWriter::printConstantVector(ConstantVector * CP, bool Static)
{
	Out << '{';
	if (CP->getNumOperands()) {
		Out << ' ';
		printConstant(cast < Constant > (CP->getOperand(0)),
			Static);
		for (unsigned i = 1, e = CP->getNumOperands(); i != e; ++i) {
			Out << ", ";
			printConstant(cast < Constant >
				(CP->getOperand(i)), Static);
		}
	}
	Out << " }";
}

// isFPCSafeToPrint - Returns true if we may assume that CFP may be written out
// textually as a double (rather than as a reference to a stack-allocated
// variable). We decide this by converting CFP to a string and back into a
// double, and then checking whether the conversion results in a bit-equal
// double to the original value of CFP. This depends on us and the target C
// compiler agreeing on the conversion process (which is pretty likely since we
// only deal in IEEE FP).
//
static bool isFPCSafeToPrint(const ConstantFP * CFP)
{
	bool ignored;
	// Do long doubles in hex for now.
	if (CFP->getType() != Type::getFloatTy(CFP->getContext()) &&
		CFP->getType() != Type::getDoubleTy(CFP->getContext()))
		return false;
	APFloat APF = APFloat(CFP->getValueAPF());	// copy
	if (CFP->getType() == Type::getFloatTy(CFP->getContext()))
		APF.convert(APFloat::IEEEdouble,
			APFloat::rmNearestTiesToEven, &ignored);
#if HAVE_PRINTF_A && ENABLE_CBE_PRINTF_A
	char Buffer[100];
	sprintf(Buffer, "%a", APF.convertToDouble());
	if (!strncmp(Buffer, "0x", 2) ||
		!strncmp(Buffer, "-0x", 3) || !strncmp(Buffer, "+0x", 3))
		return APF.bitwiseIsEqual(APFloat(atof(Buffer)));
	return false;
#else
	std::string StrVal = ftostr(APF);

	while (StrVal[0] == ' ')
		StrVal.erase(StrVal.begin());

	// Check to make sure that the stringized number is not some string like "Inf"
	// or NaN.  Check that the string matches the "[-+]?[0-9]" regex.
	if ((StrVal[0] >= '0' && StrVal[0] <= '9') ||
		((StrVal[0] == '-' || StrVal[0] == '+') &&
			(StrVal[1] >= '0' && StrVal[1] <= '9')))
		// Reparse stringized version!
		return APF.bitwiseIsEqual(APFloat(atof(StrVal.c_str())));
	return false;
#endif
}

/// Print out the casting for a cast operation. This does the double casting
/// necessary for conversion to the destination type, if necessary. 
/// @brief Print a cast
void PromelaWriter::printCast(unsigned opc, const Type * SrcTy,
			const Type * DstTy)
{
	// Print the destination type cast
	switch (opc) {
	case Instruction::UIToFP:
	case Instruction::SIToFP:
	case Instruction::IntToPtr:
	case Instruction::Trunc:
	case Instruction::BitCast:
	case Instruction::FPExt:
	case Instruction::FPTrunc:	// For these the DstTy sign doesn't matter
		Out << '(';
		printType(Out, DstTy);
		Out << ')';
		break;
	case Instruction::ZExt:
	case Instruction::PtrToInt:
	case Instruction::FPToUI:	// For these, make sure we get an unsigned dest
		Out << '(';
		printSimpleType(Out, DstTy, false);
		Out << ')';
		break;
	case Instruction::SExt:
	case Instruction::FPToSI:	// For these, make sure we get a signed dest
		Out << '(';
		printSimpleType(Out, DstTy, true);
		Out << ')';
		break;
	default:
		llvm_unreachable("Invalid cast opcode");
	}

	// Print the source type cast
	switch (opc) {
	case Instruction::UIToFP:
	case Instruction::ZExt:
		Out << '(';
		printSimpleType(Out, SrcTy, false);
		Out << ')';
		break;
	case Instruction::SIToFP:
	case Instruction::SExt:
		Out << '(';
		printSimpleType(Out, SrcTy, true);
		Out << ')';
		break;
	case Instruction::IntToPtr:
	case Instruction::PtrToInt:
		// Avoid "cast to pointer from integer of different size" warnings
		Out << "(unsigned long)";
		break;
	case Instruction::Trunc:
	case Instruction::BitCast:
	case Instruction::FPExt:
	case Instruction::FPTrunc:
	case Instruction::FPToSI:
	case Instruction::FPToUI:
		break;		// These don't need a source cast.
	default:
		llvm_unreachable("Invalid cast opcode");
		break;
	}
}

// printConstant - The LLVM Constant to Simple Constant converter.
void PromelaWriter::printConstant(Constant * CPV, bool Static)
{
	TRACE_4("/**** Printing constant ****/\n");

	if (const ConstantExpr * CE = dyn_cast < ConstantExpr > (CPV)) {
		switch (CE->getOpcode()) {
		case Instruction::Trunc:
		case Instruction::ZExt:
		case Instruction::SExt:
		case Instruction::FPTrunc:
		case Instruction::FPExt:
		case Instruction::UIToFP:
		case Instruction::SIToFP:
		case Instruction::FPToUI:
		case Instruction::FPToSI:
		case Instruction::PtrToInt:
		case Instruction::IntToPtr:
		case Instruction::BitCast:
			Out << "(";
			printCast(CE->getOpcode(),
				CE->getOperand(0)->getType(),
				CE->getType());
			if (CE->getOpcode() == Instruction::SExt
				&& CE->getOperand(0)->getType() ==
				Type::getInt1Ty(CPV->getContext())) {
				// Make sure we really sext from bool here by subtracting from 0
				Out << "0-";
			}
			printConstant(CE->getOperand(0), Static);
			if (CE->getType() ==
				Type::getInt1Ty(CPV->getContext())
				&& (CE->getOpcode() == Instruction::Trunc
					|| CE->getOpcode() == Instruction::FPToUI
					|| CE->getOpcode() == Instruction::FPToSI
					|| CE->getOpcode() ==
					Instruction::PtrToInt)) {
				// Make sure we really truncate to bool here by anding with 1
				Out << "&1u";
			}
			Out << ')';
			return;

		case Instruction::GetElementPtr:
			Out << "(";
			printGEPExpression(CE->getOperand(0),
					gep_type_begin(CPV),
					gep_type_end(CPV), Static);
			Out << ")";
			return;
		case Instruction::Select:
			Out << '(';
			printConstant(CE->getOperand(0), Static);
			Out << '?';
			printConstant(CE->getOperand(1), Static);
			Out << ':';
			printConstant(CE->getOperand(2), Static);
			Out << ')';
			return;
		case Instruction::Add:
		case Instruction::FAdd:
		case Instruction::Sub:
		case Instruction::FSub:
		case Instruction::Mul:
		case Instruction::FMul:
		case Instruction::SDiv:
		case Instruction::UDiv:
		case Instruction::FDiv:
		case Instruction::URem:
		case Instruction::SRem:
		case Instruction::FRem:
		case Instruction::And:
		case Instruction::Or:
		case Instruction::Xor:
		case Instruction::ICmp:
		case Instruction::Shl:
		case Instruction::LShr:
		case Instruction::AShr:
		{
			Out << '(';
			bool NeedsClosingParens =
				printConstExprCast(CE, Static);
			printConstantWithCast(CE->getOperand(0),
					CE->getOpcode());
			switch (CE->getOpcode()) {
			case Instruction::Add:
			case Instruction::FAdd:
				Out << " + ";
				break;
			case Instruction::Sub:
			case Instruction::FSub:
				Out << " - ";
				break;
			case Instruction::Mul:
			case Instruction::FMul:
				Out << " * ";
				break;
			case Instruction::URem:
			case Instruction::SRem:
			case Instruction::FRem:
				Out << " % ";
				break;
			case Instruction::UDiv:
			case Instruction::SDiv:
			case Instruction::FDiv:
				Out << " / ";
				break;
			case Instruction::And:
				Out << " & ";
				break;
			case Instruction::Or:
				Out << " | ";
				break;
			case Instruction::Xor:
				Out << " ^ ";
				break;
			case Instruction::Shl:
				Out << " << ";
				break;
			case Instruction::LShr:
			case Instruction::AShr:
				Out << " >> ";
				break;
			case Instruction::ICmp:
				switch (CE->getPredicate()) {
				case ICmpInst::ICMP_EQ:
					Out << " == ";
					break;
				case ICmpInst::ICMP_NE:
					Out << " != ";
					break;
				case ICmpInst::ICMP_SLT:
				case ICmpInst::ICMP_ULT:
					Out << " < ";
					break;
				case ICmpInst::ICMP_SLE:
				case ICmpInst::ICMP_ULE:
					Out << " <= ";
					break;
				case ICmpInst::ICMP_SGT:
				case ICmpInst::ICMP_UGT:
					Out << " > ";
					break;
				case ICmpInst::ICMP_SGE:
				case ICmpInst::ICMP_UGE:
					Out << " >= ";
					break;
				default:
					llvm_unreachable
						("Illegal ICmp predicate");
				}
				break;
			default:
				llvm_unreachable
					("Illegal opcode here!");
			}
			printConstantWithCast(CE->getOperand(1),
					CE->getOpcode());
			if (NeedsClosingParens)
				Out << "))";
			Out << ')';
			return;
		}
		case Instruction::FCmp:{
			Out << '(';
			bool NeedsClosingParens =
				printConstExprCast(CE, Static);
			if (CE->getPredicate() ==
				FCmpInst::FCMP_FALSE)
				Out << "0";
			else if (CE->getPredicate() ==
				FCmpInst::FCMP_TRUE)
				Out << "1";
			else {
				const char *op = 0;
				switch (CE->getPredicate()) {
				default:
					llvm_unreachable
						("Illegal FCmp predicate");
				case FCmpInst::FCMP_ORD:
					op = "ord";
					break;
				case FCmpInst::FCMP_UNO:
					op = "uno";
					break;
				case FCmpInst::FCMP_UEQ:
					op = "ueq";
					break;
				case FCmpInst::FCMP_UNE:
					op = "une";
					break;
				case FCmpInst::FCMP_ULT:
					op = "ult";
					break;
				case FCmpInst::FCMP_ULE:
					op = "ule";
					break;
				case FCmpInst::FCMP_UGT:
					op = "ugt";
					break;
				case FCmpInst::FCMP_UGE:
					op = "uge";
					break;
				case FCmpInst::FCMP_OEQ:
					op = "oeq";
					break;
				case FCmpInst::FCMP_ONE:
					op = "one";
					break;
				case FCmpInst::FCMP_OLT:
					op = "olt";
					break;
				case FCmpInst::FCMP_OLE:
					op = "ole";
					break;
				case FCmpInst::FCMP_OGT:
					op = "ogt";
					break;
				case FCmpInst::FCMP_OGE:
					op = "oge";
					break;
				}
				Out << "llvm_fcmp_" << op << "(";
				printConstantWithCast(CE->
						getOperand
						(0),
						CE->
						getOpcode());
				Out << ", ";
				printConstantWithCast(CE->
						getOperand
						(1),
						CE->
						getOpcode());
				Out << ")";
			}
			if (NeedsClosingParens)
				Out << "))";
			Out << ')';
			return;
		}
		default:
#ifndef NDEBUG
			errs() <<
				"PromelaWriter Error: Unhandled constant expression: "
			       << *CE << "\n";
#endif
			llvm_unreachable(0);
		}
	} else if (isa < UndefValue > (CPV)
		&& CPV->getType()->isSingleValueType()) {
		Out << "((";
		printType(Out, CPV->getType());	// sign doesn't matter
		Out << ")/*UNDEF*/";
		if (!isa < VectorType > (CPV->getType())) {
			Out << "0)";
		} else {
			Out << "{})";
		}
		return;
	}

	if (ConstantInt * CI = dyn_cast < ConstantInt > (CPV)) {
		const Type *Ty = CI->getType();
		if (Ty == Type::getInt1Ty(CPV->getContext()))
			Out << (CI->getZExtValue()? '1' : '0');
		else if (Ty == Type::getInt32Ty(CPV->getContext()))
			Out << CI->getZExtValue();
		else if (Ty->getPrimitiveSizeInBits() > 32)
			Out << CI->getZExtValue() << "ull";
		else {
			Out << "((";
			printSimpleType(Out, Ty, false) << ')';
			if (CI->isMinValue(true))
				Out << CI->getZExtValue();
			else
				Out << CI->getSExtValue();
			Out << ')';
		}
		return;
	}

	switch (CPV->getType()->getTypeID()) {
	case Type::FloatTyID:
	case Type::DoubleTyID:
	case Type::X86_FP80TyID:
	case Type::PPC_FP128TyID:
	case Type::FP128TyID:{
		ConstantFP *FPC = cast < ConstantFP > (CPV);
		std::map < const ConstantFP *,
				unsigned >::iterator I =
			FPConstantMap.find(FPC);
		if (I != FPConstantMap.end()) {
			// Because of FP precision problems we must load from a stack allocated
			// value that holds the value in hex.
			Out << "(*(" << (FPC->getType() ==
					Type::getFloatTy(CPV->
							getContext
							())?
					"float" : FPC->
					getType() ==
					Type::getDoubleTy(CPV->
							getContext
							())?
					"double" : "long double")
			    << "*)&FPConstant" << I->second << ')';
		} else {
			double V;
			if (FPC->getType() ==
				Type::getFloatTy(CPV->getContext()))
				V = FPC->getValueAPF().
					convertToFloat();
			else if (FPC->getType() ==
				Type::getDoubleTy(CPV->
						getContext()))
				V = FPC->getValueAPF().
					convertToDouble();
			else {
				// Long double.  Convert the number to double, discarding precision.
				// This is not awesome, but it at least makes the CBE output somewhat
				// useful.
				APFloat Tmp = FPC->getValueAPF();
				bool LosesInfo;
				Tmp.convert(APFloat::IEEEdouble,
					APFloat::rmTowardZero,
					&LosesInfo);
				V = Tmp.convertToDouble();
			}

			if (IsNAN(V)) {
				// The value is NaN

				// FIXME the actual NaN bits should be emitted.
				// The prefix for a quiet NaN is 0x7FF8. For a signalling NaN,
				// it's 0x7ff4.
				const unsigned long QuietNaN =
					0x7ff8UL;
				//const unsigned long SignalNaN = 0x7ff4UL;

				// We need to grab the first part of the FP #
				char Buffer[100];

				uint64_t ll = DoubleToBits(V);
				sprintf(Buffer, "0x%llx",
					static_cast <
					long long >(ll));

				std::string Num(&Buffer[0],
						&Buffer[6]);
				unsigned long Val =
					strtoul(Num.c_str(), 0, 16);

				if (FPC->getType() ==
					Type::getFloatTy(FPC->
							getContext()))
					Out << "LLVM_NAN" << (Val
							==
							QuietNaN
							? ""
							:
							"S")
					    << "F(\"" << Buffer <<
						"\") /*nan*/ ";
				else
					Out << "LLVM_NAN" << (Val
							==
							QuietNaN
							? ""
							:
							"S")
					    << "(\"" << Buffer <<
						"\") /*nan*/ ";
			} else if (IsInf(V)) {
				// The value is Inf
				if (V < 0)
					Out << '-';
				Out << "LLVM_INF" <<
					(FPC->getType() ==
						Type::getFloatTy(FPC->
								getContext
								())? "F" :
						"")
				    << " /*inf*/ ";
			} else {
				std::string Num;
#if HAVE_PRINTF_A && ENABLE_CBE_PRINTF_A
				// Print out the constant as a floating point number.
				char Buffer[100];
				sprintf(Buffer, "%a", V);
				Num = Buffer;
#else
				Num = ftostr(FPC->getValueAPF());
#endif
				Out << Num;
			}
		}
		break;
	}

	case Type::ArrayTyID:
		// Use C99 compound expression literal initializer syntax.
		if (!Static) {
			Out << "(";
			printType(Out, CPV->getType());
			Out << ")";
		}
		Out << "{ ";	// Arrays are wrapped in struct types.
		if (ConstantArray * CA = dyn_cast < ConstantArray > (CPV)) {
			printConstantArray(CA, Static);
		} else {
			assert(isa < ConstantAggregateZero > (CPV)
				|| isa < UndefValue > (CPV));
			const ArrayType *AT =
				cast < ArrayType > (CPV->getType());
			Out << '{';
			if (AT->getNumElements()) {
				Out << ' ';
				Constant *CZ =
					Constant::getNullValue(AT->
							getElementType
							());
				printConstant(CZ, Static);
				for (unsigned i = 1, e =
					     AT->getNumElements(); i != e; ++i) {
					Out << ", ";
					printConstant(CZ, Static);
				}
			}
			Out << " }";
		}
		Out << " }";	// Arrays are wrapped in struct types.
		break;

	case Type::VectorTyID:
		// Use C99 compound expression literal initializer syntax.
		if (!Static) {
			Out << "(";
			printType(Out, CPV->getType());
			Out << ")";
		}
		if (ConstantVector * CV =
			dyn_cast < ConstantVector > (CPV)) {
			printConstantVector(CV, Static);
		} else {
			assert(isa < ConstantAggregateZero > (CPV)
				|| isa < UndefValue > (CPV));
			const VectorType *VT =
				cast < VectorType > (CPV->getType());
			Out << "{ ";
			Constant *CZ =
				Constant::getNullValue(VT->getElementType());
			printConstant(CZ, Static);
			for (unsigned i = 1, e = VT->getNumElements();
			     i != e; ++i) {
				Out << ", ";
				printConstant(CZ, Static);
			}
			Out << " }";
		}
		break;

	case Type::StructTyID:
		// Use C99 compound expression literal initializer syntax.
		if (!Static) {
			Out << "(";
			printType(Out, CPV->getType());
			Out << ")";
		}
		if (isa < ConstantAggregateZero > (CPV)
			|| isa < UndefValue > (CPV)) {
			const StructType *ST =
				cast < StructType > (CPV->getType());
			Out << '{';
			if (ST->getNumElements()) {
				Out << ' ';
				printConstant(Constant::
					getNullValue(ST->
						getElementType
						(0)), Static);
				for (unsigned i = 1, e =
					     ST->getNumElements(); i != e; ++i) {
					Out << ", ";
					printConstant(Constant::
						getNullValue(ST->
							getElementType
							(i)),
						Static);
				}
			}
			Out << " }";
		} else {
			Out << '{';
			if (CPV->getNumOperands()) {
				Out << ' ';
				printConstant(cast < Constant >
					(CPV->getOperand(0)),
					Static);
				for (unsigned i = 1, e =
					     CPV->getNumOperands(); i != e; ++i) {
					Out << ", ";
					printConstant(cast < Constant >
						(CPV->getOperand(i)),
						Static);
				}
			}
			Out << " }";
		}
		break;

	case Type::PointerTyID:
		if (isa < ConstantPointerNull > (CPV)) {
			Out << "((";
			printType(Out, CPV->getType());	// sign doesn't matter
			Out << ")/*NULL*/0)";
			break;
		} else if (GlobalValue * GV =
			dyn_cast < GlobalValue > (CPV)) {
			writeOperand(GV, Static);
			break;
		}
		// FALL THROUGH
	default:
#ifndef NDEBUG
		errs() << "Unknown constant type: " << *CPV << "\n";
#endif
		llvm_unreachable(0);
	}
}

// Some constant expressions need to be casted back to the original types
// because their operands were casted to the expected type. This function takes
// care of detecting that case and printing the cast for the ConstantExpr.
bool PromelaWriter::printConstExprCast(const ConstantExpr * CE, bool Static)
{
	bool NeedsExplicitCast = false;
	const Type *Ty = CE->getOperand(0)->getType();
	bool TypeIsSigned = false;
	switch (CE->getOpcode()) {
	case Instruction::Add:
	case Instruction::Sub:
	case Instruction::Mul:
		// We need to cast integer arithmetic so that it is always performed
		// as unsigned, to avoid undefined behavior on overflow.
	case Instruction::LShr:
	case Instruction::URem:
	case Instruction::UDiv:
		NeedsExplicitCast = true;
		break;
	case Instruction::AShr:
	case Instruction::SRem:
	case Instruction::SDiv:
		NeedsExplicitCast = true;
		TypeIsSigned = true;
		break;
	case Instruction::SExt:
		Ty = CE->getType();
		NeedsExplicitCast = true;
		TypeIsSigned = true;
		break;
	case Instruction::ZExt:
	case Instruction::Trunc:
	case Instruction::FPTrunc:
	case Instruction::FPExt:
	case Instruction::UIToFP:
	case Instruction::SIToFP:
	case Instruction::FPToUI:
	case Instruction::FPToSI:
	case Instruction::PtrToInt:
	case Instruction::IntToPtr:
	case Instruction::BitCast:
		Ty = CE->getType();
		NeedsExplicitCast = true;
		break;
	default:
		break;
	}
	if (NeedsExplicitCast) {
		Out << "((";
		if (Ty->isInteger()
			&& Ty != Type::getInt1Ty(Ty->getContext()))
			printSimpleType(Out, Ty, TypeIsSigned);
		else
			printType(Out, Ty);	// not integer, sign doesn't matter
		Out << ")(";
	}
	return NeedsExplicitCast;
}

//  Print a constant assuming that it is the operand for a given Opcode. The
//  opcodes that care about sign need to cast their operands to the expected
//  type before the operation proceeds. This function does the casting.
void PromelaWriter::printConstantWithCast(Constant * CPV, unsigned Opcode)
{

	// Extract the operand's type, we'll need it.
	const Type *OpTy = CPV->getType();

	// Indicate whether to do the cast or not.
	bool shouldCast = false;
	bool typeIsSigned = false;

	// Based on the Opcode for which this Constant is being written, determine
	// the new type to which the operand should be casted by setting the value
	// of OpTy. If we change OpTy, also set shouldCast to true so it gets
	// casted below.
	switch (Opcode) {
	default:
		// for most instructions, it doesn't matter
		break;
	case Instruction::Add:
	case Instruction::Sub:
	case Instruction::Mul:
		// We need to cast integer arithmetic so that it is always performed
		// as unsigned, to avoid undefined behavior on overflow.
	case Instruction::LShr:
	case Instruction::UDiv:
	case Instruction::URem:
		shouldCast = true;
		break;
	case Instruction::AShr:
	case Instruction::SDiv:
	case Instruction::SRem:
		shouldCast = true;
		typeIsSigned = true;
		break;
	}

	// Write out the casted constant if we should, otherwise just write the
	// operand.
	if (shouldCast) {
		Out << "((";
		printSimpleType(Out, OpTy, typeIsSigned);
		Out << ")";
		printConstant(CPV, false);
		Out << ")";
	} else
		printConstant(CPV, false);
}

std::string PromelaWriter::GetValueName(const Value * Operand)
{
	std::string res;

	if (isa<Function>(Operand))

	// Mangle globals with the standard mangler interface for LLC compatibility.
	if (const GlobalValue * GV = dyn_cast < GlobalValue > (Operand)) {
		res = Mang->getMangledName(GV);
		return replaceAll(res, ".", "");
	}
	std::string Name = Operand->getName();

	if (Name.empty()) {	// Assign unique names to local temporaries.
		unsigned &No = AnonValueNumbers[Operand];
		if (No == 0)
			No = ++NextAnonValueNumber;
		Name = "tmp__" + utostr(No);
	}

	std::string VarName;
	VarName.reserve(Name.capacity());

	for (std::string::iterator I = Name.begin(), E = Name.end();
	     I != E; ++I) {
		char ch = *I;

		if (! ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_')) {
			char buffer[5];
			sprintf(buffer, "_%x_", ch);
			VarName += buffer;
		} else
			VarName += ch;
	}

	res = "llvm_cbe_" + VarName;
	return replaceAll(res, ".", "");
}

/// writeInstComputationInline - Emit the computation for the specified
/// instruction inline, with no destination provided.
void PromelaWriter::writeInstComputationInline(Instruction & I)
{
	// We can't currently support integer types other than 1, 8, 16, 32, 64.
	// Validate this.
	const Type *Ty = I.getType();
	if (Ty->isInteger() && (Ty != Type::getInt1Ty(I.getContext()) &&
					Ty != Type::getInt8Ty(I.getContext()) &&
					Ty != Type::getInt16Ty(I.getContext()) &&
					Ty != Type::getInt32Ty(I.getContext()) &&
					Ty != Type::getInt64Ty(I.getContext()))) {
		llvm_report_error("The Simple backend does not currently support integer types"
				"of widths other than 1, 8, 16, 32, 64.\n"
				"This is being tracked as PR 4158.");
	}

	// If this is a non-trivial bool computation, make sure to truncate down to
	// a 1 bit value.  This is important because we want "add i1 x, y" to return
	// "0" when x and y are true, not "2" for example.
	bool NeedBoolTrunc = false;
	if (I.getType() == Type::getInt1Ty(I.getContext()) && !isa < ICmpInst > (I) && !isa < FCmpInst > (I))
		NeedBoolTrunc = true;

	if (NeedBoolTrunc)
		Out << "((";

	TRACE_4("/***** Visiting " << I.getOpcodeName() << " ( writeInstComputationInline() ) ******/ \n");
//	Out << "/***** Visiting " << I.getOpcodeName() << " ( writeInstComputationInline() ) ******/ \n";
	visit(I);
//	Out << "\n/***** Visited " << I.getOpcodeName() << "******/ \n";
	TRACE_4("\n");
	TRACE_4("/***** Visited " << I.getOpcodeName() << "******/ \n");

	if (NeedBoolTrunc)
		Out << ")&1)";
}

/// isAddressExposed - Return true if the specified value's name needs to
/// have its address taken in order to get a  value of the correct type.
/// This happens for global variables, byval parameters, and direct allocas.
bool PromelaWriter::isAddressExposed(const Value * V) const
{
	if (const Argument * A = dyn_cast < Argument > (V))
		return ByValParams.count(A);
	return isa < GlobalVariable > (V) || isDirectAlloca(V);
}


/// writeOperandDeref - Print the result of dereferencing the specified
/// operand with '*'.  This is equivalent to printing '*' then using
/// writeOperand, but avoids excess syntax in some cases.
void PromelaWriter::writeOperandDeref(Value * Operand)
{
	if (isAddressExposed(Operand)) {
		// Already something with an address exposed.
		writeOperandInternal(Operand);
	} else {
		Out << "*(";
		writeOperand(Operand);
		Out << ")";
	}
}


void PromelaWriter::writeOperandInternal(Value * Operand, bool Static)
{
	if (Instruction * I = dyn_cast < Instruction > (Operand))
		// Should we inline this instruction to build a tree?
		if (isInlinableInst(*I) && !isDirectAlloca(I)) {
			Out << '(';
			writeInstComputationInline(*I);
			Out << ')';
			return;
		}

	Constant *CPV = dyn_cast < Constant > (Operand);

	if (CPV && !isa < GlobalValue > (CPV))
		printConstant(CPV, Static);
	else
		Out << GetValueName(Operand);
}

void PromelaWriter::writeOperand(Value * Operand, bool Static)
{
	TRACE_4("/**** writeOperand() ****/\n");

//   bool isAddressImplicit = isAddressExposed(Operand);
//   if (isAddressImplicit)
//     Out << "(&";  // Global variables are referenced as their addresses by llvm

	writeOperandInternal(Operand, Static);

//   if (isAddressImplicit)
//     Out << ')';
}

// Some instructions need to have their result value casted back to the 
// original types because their operands were casted to the expected type. 
// This function takes care of detecting that case and printing the cast 
// for the Instruction.
bool PromelaWriter::writeInstructionCast(const Instruction & I)
{
	const Type *Ty = I.getOperand(0)->getType();
	switch (I.getOpcode()) {
	case Instruction::Add:
	case Instruction::Sub:
	case Instruction::Mul:
		// We need to cast integer arithmetic so that it is always performed
		// as unsigned, to avoid undefined behavior on overflow.
	case Instruction::LShr:
	case Instruction::URem:
	case Instruction::UDiv:
		Out << "((";
		printSimpleType(Out, Ty, false);
		Out << ")(";
		return true;
	case Instruction::AShr:
	case Instruction::SRem:
	case Instruction::SDiv:
		Out << "((";
		printSimpleType(Out, Ty, true);
		Out << ")(";
		return true;
	default:
		break;
	}
	return false;
}

// Write the operand with a cast to another type based on the Opcode being used.
// This will be used in cases where an instruction has specific type
// requirements (usually signedness) for its operands. 
void PromelaWriter::writeOperandWithCast(Value * Operand, unsigned Opcode)
{

	// Extract the operand's type, we'll need it.
	const Type *OpTy = Operand->getType();

	// Indicate whether to do the cast or not.
	bool shouldCast = false;

	// Indicate whether the cast should be to a signed type or not.
	bool castIsSigned = false;

	// Based on the Opcode for which this Operand is being written, determine
	// the new type to which the operand should be casted by setting the value
	// of OpTy. If we change OpTy, also set shouldCast to true.
	switch (Opcode) {
	default:
		// for most instructions, it doesn't matter
		break;
	case Instruction::Add:
	case Instruction::Sub:
	case Instruction::Mul:
		// We need to cast integer arithmetic so that it is always performed
		// as unsigned, to avoid undefined behavior on overflow.
	case Instruction::LShr:
	case Instruction::UDiv:
	case Instruction::URem:	// Cast to unsigned first
		shouldCast = true;
		castIsSigned = false;
		break;
	case Instruction::GetElementPtr:
	case Instruction::AShr:
	case Instruction::SDiv:
	case Instruction::SRem:	// Cast to signed first
		shouldCast = true;
		castIsSigned = true;
		break;
	}

	// Write out the casted operand if we should, otherwise just write the
	// operand.
	if (shouldCast) {
		Out << "((";
		printSimpleType(Out, OpTy, castIsSigned);
		Out << ")";
		writeOperand(Operand);
		Out << ")";
	} else
		writeOperand(Operand);
}

// Write the operand with a cast to another type based on the icmp predicate 
// being used. 
void PromelaWriter::writeOperandWithCast(Value * Operand,
					const ICmpInst & Cmp)
{
	// This has to do a cast to ensure the operand has the right signedness. 
	// Also, if the operand is a pointer, we make sure to cast to an integer when
	// doing the comparison both for signedness and so that the C compiler doesn't
	// optimize things like "p < NULL" to false (p may contain an integer value
	// f.e.).
	bool shouldCast = Cmp.isRelational();

	// Write out the casted operand if we should, otherwise just write the
	// operand.
	if (!shouldCast) {
		writeOperand(Operand);
		return;
	}
	// Should this be a signed comparison?  If so, convert to signed.
	bool castIsSigned = Cmp.isSignedPredicate();

	// If the operand was a pointer, convert to a large integer type.
	const Type *OpTy = Operand->getType();
	if (isa < PointerType > (OpTy))
		OpTy = TD->getIntPtrType(Operand->getContext());

	Out << "((";
	printSimpleType(Out, OpTy, castIsSigned);
	Out << ")";
	writeOperand(Operand);
	Out << ")";
}

// generateCompilerSpecificCode - This is where we add conditional compilation
// directives to cater to specific compilers as need be.
//
static void generateCompilerSpecificCode(formatted_raw_ostream & Out,
					const TargetData * TD)
{
	// Alloca is hard to get, and we don't want to include stdlib.h here.
	Out << "/* get a declaration for alloca */\n"
	    << "#if defined(__CYGWIN__) || defined(__MINGW32__)\n"
	    << "#define  alloca(x) __builtin_alloca((x))\n"
	    << "#define _alloca(x) __builtin_alloca((x))\n"
	    << "#elif defined(__APPLE__)\n"
	    << "extern void *__builtin_alloca(unsigned long);\n"
	    << "#define alloca(x) __builtin_alloca(x)\n"
	    << "#define longjmp _longjmp\n"
	    << "#define setjmp _setjmp\n"
	    << "#elif defined(__sun__)\n"
	    << "#if defined(__sparcv9)\n"
	    << "extern void *__builtin_alloca(unsigned long);\n"
	    << "#else\n"
	    << "extern void *__builtin_alloca(unsigned int);\n"
	    << "#endif\n"
	    << "#define alloca(x) __builtin_alloca(x)\n"
	    <<
		"#elif defined(__FreeBSD__) || defined(__NetBSD__) || defined(__OpenBSD__) || defined(__DragonFly__) || defined(__arm__)\n"
	    << "#define alloca(x) __builtin_alloca(x)\n" <<
		"#elif defined(_MSC_VER)\n" << "#define inline _inline\n" <<
		"#define alloca(x) _alloca(x)\n" << "#else\n" <<
		"#include <alloca.h>\n" << "#endif\n\n";

	// We output GCC specific attributes to preserve 'linkonce'ness on globals.
	// If we aren't being compiled with GCC, just drop these attributes.
	Out <<
		"#ifndef __GNUC__  /* Can only support \"linkonce\" vars with GCC */\n"
	    << "#define __attribute__(X)\n" << "#endif\n\n";

	// On Mac OS X, "external weak" is spelled "__attribute__((weak_import))".
	Out << "#if defined(__GNUC__) && defined(__APPLE_CC__)\n"
	    << "#define __EXTERNAL_WEAK__ __attribute__((weak_import))\n"
	    << "#elif defined(__GNUC__)\n"
	    << "#define __EXTERNAL_WEAK__ __attribute__((weak))\n"
	    << "#else\n" << "#define __EXTERNAL_WEAK__\n" << "#endif\n\n";

	// For now, turn off the weak linkage attribute on Mac OS X. (See above.)
	Out << "#if defined(__GNUC__) && defined(__APPLE_CC__)\n"
	    << "#define __ATTRIBUTE_WEAK__\n"
	    << "#elif defined(__GNUC__)\n"
	    << "#define __ATTRIBUTE_WEAK__ __attribute__((weak))\n"
	    << "#else\n" << "#define __ATTRIBUTE_WEAK__\n" << "#endif\n\n";

	// Add hidden visibility support. FIXME: APPLE_CC?
	Out << "#if defined(__GNUC__)\n"
	    <<
		"#define __HIDDEN__ __attribute__((visibility(\"hidden\")))\n"
	    << "#endif\n\n";

	// Define NaN and Inf as GCC builtins if using GCC, as 0 otherwise
	// From the GCC documentation:
	//
	//   double __builtin_nan (const char *str)
	//
	// This is an implementation of the ISO C99 function nan.
	//
	// Since ISO C99 defines this function in terms of strtod, which we do
	// not implement, a description of the parsing is in order. The string is
	// parsed as by strtol; that is, the base is recognized by leading 0 or
	// 0x prefixes. The number parsed is placed in the significand such that
	// the least significant bit of the number is at the least significant
	// bit of the significand. The number is truncated to fit the significand
	// field provided. The significand is forced to be a quiet NaN.
	//
	// This function, if given a string literal, is evaluated early enough
	// that it is considered a compile-time constant.
	//
	//   float __builtin_nanf (const char *str)
	//
	// Similar to __builtin_nan, except the return type is float.
	//
	//   double __builtin_inf (void)
	//
	// Similar to __builtin_huge_val, except a warning is generated if the
	// target floating-point format does not support infinities. This
	// function is suitable for implementing the ISO C99 macro INFINITY.
	//
	//   float __builtin_inff (void)
	//
	// Similar to __builtin_inf, except the return type is float.
	Out << "#ifdef __GNUC__\n"
	    <<
		"#define LLVM_NAN(NanStr)   __builtin_nan(NanStr)   /* Double */\n"
	    <<
		"#define LLVM_NANF(NanStr)  __builtin_nanf(NanStr)  /* Float */\n"
	    <<
		"#define LLVM_NANS(NanStr)  __builtin_nans(NanStr)  /* Double */\n"
	    <<
		"#define LLVM_NANSF(NanStr) __builtin_nansf(NanStr) /* Float */\n"
	    <<
		"#define LLVM_INF           __builtin_inf()         /* Double */\n"
	    <<
		"#define LLVM_INFF          __builtin_inff()        /* Float */\n"
	    << "#define LLVM_PREFETCH(addr,rw,locality) "
		"__builtin_prefetch(addr,rw,locality)\n" <<
		"#define __ATTRIBUTE_CTOR__ __attribute__((constructor))\n" <<
		"#define __ATTRIBUTE_DTOR__ __attribute__((destructor))\n" <<
		"#define LLVM_ASM           __asm__\n" << "#else\n" <<
		"#define LLVM_NAN(NanStr)   ((double)0.0)           /* Double */\n"
	    <<
		"#define LLVM_NANF(NanStr)  0.0F                    /* Float */\n"
	    <<
		"#define LLVM_NANS(NanStr)  ((double)0.0)           /* Double */\n"
	    <<
		"#define LLVM_NANSF(NanStr) 0.0F                    /* Float */\n"
	    <<
		"#define LLVM_INF           ((double)0.0)           /* Double */\n"
	    <<
		"#define LLVM_INFF          0.0F                    /* Float */\n"
	    <<
		"#define LLVM_PREFETCH(addr,rw,locality)            /* PREFETCH */\n"
	    << "#define __ATTRIBUTE_CTOR__\n" <<
		"#define __ATTRIBUTE_DTOR__\n" << "#define LLVM_ASM(X)\n" <<
		"#endif\n\n";

	Out << "#if __GNUC__ < 4 /* Old GCC's, or compilers not GCC */ \n"
	    << "#define __builtin_stack_save() 0   /* not implemented */\n"
	    << "#define __builtin_stack_restore(X) /* noop */\n"
	    << "#endif\n\n";

	// Output typedefs for 128-bit integers. If these are needed with a
	// 32-bit target or with a C compiler that doesn't support mode(TI),
	// more drastic measures will be needed.
	Out << "#if __GNUC__ && __LP64__ /* 128-bit integer types */\n"
	    << "typedef int __attribute__((mode(TI))) llvmInt128;\n"
	    << "typedef unsigned __attribute__((mode(TI))) llvmUInt128;\n"
	    << "#endif\n\n";

	// Output target-specific code that should be inserted into main.
	Out <<
		"#define CODE_FOR_MAIN() /* Any target-specific code for main()*/\n";
}

/// FindStaticTors - Given a static ctor/dtor list, unpack its contents into
/// the StaticTors set.
static void FindStaticTors(GlobalVariable * GV,
			std::set < Function * >&StaticTors)
{
	ConstantArray *InitList =
		dyn_cast < ConstantArray > (GV->getInitializer());
	if (!InitList)
		return;

	for (unsigned i = 0, e = InitList->getNumOperands(); i != e; ++i)
		if (ConstantStruct * CS =
			dyn_cast < ConstantStruct >
			(InitList->getOperand(i))) {
			if (CS->getNumOperands() != 2)
				return;	// Not array of 2-element structs.

			if (CS->getOperand(1)->isNullValue())
				return;	// Found a null terminator, exit printing.
			Constant *FP = CS->getOperand(1);
			if (ConstantExpr * CE =
				dyn_cast < ConstantExpr > (FP))
				if (CE->isCast())
					FP = CE->getOperand(0);
			if (Function * F = dyn_cast < Function > (FP))
				StaticTors.insert(F);
		}
}

/// getGlobalVariableClass - If this is a global that is specially recognized
/// by LLVM, return a code that indicates how we should handle it.
static SpecialGlobalClass getGlobalVariableClass(const GlobalVariable * GV)
{
	// If this is a global ctors/dtors list, handle it now.
	if (GV->hasAppendingLinkage() && GV->use_empty()) {
		if (GV->getName() == "llvm.global_ctors")
			return GlobalCtors;
		else if (GV->getName() == "llvm.global_dtors")
			return GlobalDtors;
	}
	// Otherwise, it it is other metadata, don't print it.  This catches things
	// like debug information.
	if (GV->getSection() == "llvm.metadata")
		return NotPrinted;

	return NotSpecial;
}

// PrintEscapedString - Print each character of the specified string, escaping
// it if it is not printable or if it is an escape char.
static void PrintEscapedString(const char *Str, unsigned Length,
			raw_ostream & Out)
{
	for (unsigned i = 0; i != Length; ++i) {
		unsigned char C = Str[i];
		if (isprint(C) && C != '\\' && C != '"')
			Out << C;
		else if (C == '\\')
			Out << "\\\\";
		else if (C == '\"')
			Out << "\\\"";
		else if (C == '\t')
			Out << "\\t";
		else
			Out << "\\x" << hexdigit(C >> 4) << hexdigit(C &
								0x0F);
	}
}

// PrintEscapedString - Print each character of the specified string, escaping
// it if it is not printable or if it is an escape char.
static void PrintEscapedString(const std::string & Str, raw_ostream & Out)
{
	PrintEscapedString(Str.c_str(), Str.size(), Out);
}


/// Output all floating point constants that cannot be printed accurately...
void PromelaWriter::printFloatingPointConstants(Function & F)
{
	// Scan the module for floating point constants.  If any FP constant is used
	// in the function, we want to redirect it here so that we do not depend on
	// the precision of the printed form, unless the printed form preserves
	// precision.
	//
	for (constant_iterator I = constant_begin(&F), E =
		     constant_end(&F); I != E; ++I)
		printFloatingPointConstants(*I);

	Out << '\n';
}

void PromelaWriter::printFloatingPointConstants(const Constant * C)
{
	// If this is a constant expression, recursively check for constant fp values.
	if (const ConstantExpr * CE = dyn_cast < ConstantExpr > (C)) {
		for (unsigned i = 0, e = CE->getNumOperands(); i != e; ++i)
			printFloatingPointConstants(CE->getOperand(i));
		return;
	}
	// Otherwise, check for a FP constant that we need to print.
	const ConstantFP *FPC = dyn_cast < ConstantFP > (C);
	if (FPC == 0 ||
		// Do not put in FPConstantMap if safe.
		isFPCSafeToPrint(FPC) ||
		// Already printed this constant?
		FPConstantMap.count(FPC))
		return;

	FPConstantMap[FPC] = FPCounter;	// Number the FP constants

	if (FPC->getType() == Type::getDoubleTy(FPC->getContext())) {
		double Val = FPC->getValueAPF().convertToDouble();
		uint64_t i =
			FPC->getValueAPF().bitcastToAPInt().getZExtValue();
		Out << "static const ConstantDoubleTy FPConstant" <<
			FPCounter++ << " = 0x" << utohexstr(i)
		    << "ULL;    /* " << Val << " */\n";
	} else if (FPC->getType() == Type::getFloatTy(FPC->getContext())) {
		float Val = FPC->getValueAPF().convertToFloat();
		uint32_t i =
			(uint32_t) FPC->getValueAPF().
			bitcastToAPInt().getZExtValue();
		Out << "static const ConstantFloatTy FPConstant" <<
			FPCounter++ << " = 0x" << utohexstr(i)
		    << "U;    /* " << Val << " */\n";
	} else if (FPC->getType() ==
		Type::getX86_FP80Ty(FPC->getContext())) {
		// api needed to prevent premature destruction
		APInt api = FPC->getValueAPF().bitcastToAPInt();
		const uint64_t *p = api.getRawData();
		Out << "static const ConstantFP80Ty FPConstant" <<
			FPCounter++ << " = { 0x" << utohexstr(p[0])
		    << "ULL, 0x" << utohexstr((uint16_t) p[1]) <<
			",{0,0,0}" << "}; /* Long double constant */\n";
	} else if (FPC->getType() ==
		Type::getPPC_FP128Ty(FPC->getContext())
		|| FPC->getType() ==
		Type::getFP128Ty(FPC->getContext())) {
		APInt api = FPC->getValueAPF().bitcastToAPInt();
		const uint64_t *p = api.getRawData();
		Out << "static const ConstantFP128Ty FPConstant" <<
			FPCounter++ << " = { 0x" << utohexstr(p[0]) << ", 0x"
		    << utohexstr(p[1])
		    << "}; /* Long double constant */\n";

	} else {
		llvm_unreachable("Unknown float type!");
	}
}


void
PromelaWriter::insertTypeName(const Type* Ty, std::string TyName)
{
	this->TypeNames[Ty] = replaceAll(TyName, ".", "");
}

int
PromelaWriter::getTypeNamesSize()
{
	return this->TypeNames.size();
}

/// printSymbolTable - Run through symbol table looking for type names.  If a
/// type name is found, emit its declaration...
///
void PromelaWriter::printModuleTypes(const TypeSymbolTable & TST)
{
 	std::set < const Type *>StructPrinted;
	TRACE_2("PromelaWriter > Emitting types\n");
	Out << "\n\n/*---- Types ----*/\n";

	// We are only interested in the type plane of the symbol table.
	TypeSymbolTable::const_iterator I = TST.begin();
	TypeSymbolTable::const_iterator End = TST.end();

	// If there are no type names, exit early.
	if (I == End)
		return;

	// Print out forward declarations for structure types before anything else!
	Out << "/* Structure forward decls */\n";
	for (; I != End; ++I) {
//		TRACE_6(":::::::::::::::::::::::::::: " << I->first << " -> " << I->second << "\n");
		std::string Name = I->first; //not using Mang->makeNameProper(...)
		insertTypeName(I->second, Name);
//		TypeNames.insert(std::make_pair(I->second, Name));
		//		TypeNames[I->second] = Name;
	}
	Out << '\n';

	vector < Process * >::iterator processIt = this->elab->getProcesses()->begin();
	vector < Process * >::iterator endIt = this->elab->getProcesses()->end();

	for (; processIt < endIt; ++processIt) {

		Process *proc = *processIt;
		Function::arg_iterator argI = proc->getMainFct()->arg_begin();
		const Value* moduleArg = &*argI;
		
		const PointerType* PTy = cast<PointerType>(moduleArg->getType());
		fillContainedStructs(PTy->getElementType(), StructPrinted);
	}

	std::set < const Type *>::iterator itS;
	for (itS = StructPrinted.begin() ; itS != StructPrinted.end(); ++itS) {
		// Print structure type out.
		const Type* Ty = *itS;
		std::string Name = TypeNames[Ty];
		TRACE_5("Emitting type " << Name << "\n");
		Out << "typedef ";
		printType(Out, Ty, true, Name, true);
		Out << ";\n\n";
	}
// 		std::vector < Function * >*usedFcts = proc->getUsedFunctions();
// 		currentProcess = proc;

// 		for (std::vector < Function * >::iterator itF = usedFcts->begin();
// 		     itF < usedFcts->end(); ++itF) {

// 			Function *F = *itF;
// 			TRACE_4("PromelaWriter > printing function : " << F->getNameStr() << "\n");

	
	// Now we can print out typedefs.  Above, we guaranteed that this can only be
	// for struct or opaque types.
// 	Out << "/* Typedefs */\n";
// 	for (I = TST.begin(); I != End; ++I) {
// 		std::string Name = "l_" + Mang->makeNameProper(I->first);
// 		Out << "typedef ";
// 		printType(Out, I->second, false, Name);
// 		Out << ";\n";
// 	}

// 	Out << '\n';

// 	// Keep track of which structures have been printed so far...
// 	std::set < const Type *>StructPrinted;

// 	// Loop over all structures then push them into the stack so they are
// 	// printed in the correct order.
// 	//
// 	Out << "/* Structure contents */\n";
// 	for (I = TST.begin(); I != End; ++I)
// 		if (isa < StructType > (I->second)
// 			|| isa < ArrayType > (I->second))
// 			// Only print out used types!
// 			printContainedStructs(I->second, StructPrinted);
}

// Push the struct onto the stack and recursively push all structs
// this one depends on.
//
// TODO:  Make this work properly with vector types
//
void PromelaWriter::fillContainedStructs(const Type * Ty,
					std::set <const Type * >&StructPrinted)
{
	// Don't walk through pointers.
	if (isa < PointerType > (Ty) || Ty->isPrimitiveType() || Ty->isInteger())
		return;

	// Print all contained types first.
	for (Type::subtype_iterator I = Ty->subtype_begin(), E = Ty->subtype_end(); I != E; ++I) {
		Type* subTy = *I;
		if (isSystemCType(subTy))
			continue;
		
		fillContainedStructs(subTy, StructPrinted);
	}
	if (isa < StructType > (Ty) || isa < ArrayType > (Ty)) {
		// Check to see if we have already printed this struct.
		StructPrinted.insert(Ty);
	}
}

void PromelaWriter::printFunctionSignature(const Function * F,
					bool Prototype, bool inlineFct)
{
	TRACE_5("PromelaWriter > printing function signature\n");

	/// isStructReturn - Should this function actually return a struct by-value?
// 	bool isStructReturn = F->hasStructRetAttr();
	
	//   if (F->hasLocalLinkage()) Out << "static ";
	//   if (F->hasDLLImportLinkage()) Out << "__declspec(dllimport) ";
	//   if (F->hasDLLExportLinkage()) Out << "__declspec(dllexport) ";  
	switch (F->getCallingConv()) {
	case CallingConv::X86_StdCall:
		triggerError(Out, "NYI : callingconv (stcall here)");
		Out << "__attribute__((stdcall)) ";
		break;
	case CallingConv::X86_FastCall:
		triggerError(Out, "NYI : callingconv (fastcall here)");
		Out << "__attribute__((fastcall)) ";
		break;
	default:
		break;
	}
	
	// Loop over the arguments, printing them...
//	const AttrListPtr &PAL = F->getAttributes();
	const FunctionType *FT = cast<FunctionType>(F->getFunctionType());
	
	if (FT->isVarArg()) {
		triggerError(Out, "Error : not able to manage vararg functions\n");
	}  
				
	// Print out the name...
	if (inlineFct)
		Out << "inline ";
	else
		Out << "proctype ";

	
	std::string fctName = GetValueName(F) + "_pnumber_" + intToString(currentProcess->getPid());
	Out << fctName << '(';
	
//	std::vector<pair<std::string, const Type*> >* args = new std::vector<pair<std::string, const Type*> >();
//	std::vector<pair<std::string, const Type*> >* ret = new std::vector<pair<std::string, const Type*> >();

//	fillDependencies(F, string(""), args, ret);
	
	bool printedArg = false;
//	if (!args->empty()) {
	Function::const_arg_iterator argI = F->arg_begin(), argE = F->arg_end();
	for (; argI != argE; ++argI) {
		const Value* currentArg = &*argI;
		
		std::string ArgName = GetValueName(currentArg);
		TRACE_7("PRINTING ARG : " << ArgName << "\n");
		if (printedArg)
			Out << ", ";
		if (inlineFct)
			Out << ArgName;
		else
			printType(Out, currentArg->getType(), /*isSigned*/true, ArgName, false);
		printedArg = true;
	}
//	}
	Out << ')';
}

void
PromelaWriter::addVectors(std::vector<pair<std::string, const Type*> >* from,
			std::vector<pair<std::string, const Type*> >* to)
{
	std::vector<pair<std::string, const Type*> >::iterator itFrom;
	for (itFrom = from->begin(); itFrom != from->end(); ++itFrom) {
		to->push_back(*itFrom);
	}
}

bool
PromelaWriter::isSystemCType(const Type* ty)
{
	if (ty->isPrimitiveType() || ty->isInteger())
		return false;

	return true;

// 	while (isa<PointerType>(ty)) {
// 		ty = cast<PointerType>(ty)->getElementType();
// 	}

// 	std::string typeName = this->TypeNames.find(ty)->second;
// 	return typeName.substr(0, 16).compare("struct.sc_core::") == 0 || typeName.substr(0, 12).compare("struct.std::") == 0;
}

static inline bool isFPIntBitCast(const Instruction & I)
{
	if (!isa < BitCastInst > (I))
		return false;
	const Type *SrcTy = I.getOperand(0)->getType();
	const Type *DstTy = I.getType();
	return (SrcTy->isFloatingPoint() && DstTy->isInteger()) ||
		(DstTy->isFloatingPoint() && SrcTy->isInteger());
}

void PromelaWriter::printFunction(Function & F, bool inlineFct)
{
	/// isStructReturn - Should this function actually return a struct by-value?
// 	bool isStructReturn = F.hasStructRetAttr();

	printFunctionSignature(&F, false, inlineFct);
	Out << "\n";
	Out << "{\n";


	// If this is a struct return function, handle the result with magic.
// 	if (isStructReturn) {
// 		triggerError(Out, "NYI : function returning a struct.");
// 		const Type *StructTy =
// 			cast < PointerType >
// 			(F.arg_begin()->getType())->getElementType();
// 		Out << "  ";
// 		printType(Out, StructTy, false, "StructReturn");
// 		Out << ";  /* Struct return temporary */\n";

// 		Out << "  ";
// 		printType(Out, F.arg_begin()->getType(), false,
// 			GetValueName(F.arg_begin()));
// 		Out << " = &StructReturn;\n";
// 	}

	TRACE_5("PromelaWriter > printing locals\n");

	// print local variable information for the function
	for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
		if (const AllocaInst * AI = isDirectAlloca(&*I)) {
			printType(Out, AI->getAllocatedType(), false, GetValueName(AI));
			Out << ";\n    ";
			
		} else if (I->getType() != Type::getVoidTy(F.getContext()) && !isInlinableInst(*I) && ! isSystemCType(I->getType())) {
			TRACE_7("Adding new local variable : " << GetValueName(&*I) << "  ->  " );
			I->dump();

			printType(Out, I->getType(), false, GetValueName(&*I));
			Out << ";\n    ";

			if (isa < PHINode > (*I)) {	// Print out PHI node temporaries as well...
				printType(Out, I->getType(), false, GetValueName(&*I) +	"__PHI_TEMPORARY");
				Out << ";\n    ";
			}
		}
		// We need a temporary for the BitCast to use so it can pluck a value out
		// of a union to do the BitCast. This is separate from the need for a
		// variable to hold the result of the BitCast. 
		if (isFPIntBitCast(*I)) {
			ErrorMsg << "NYI : bitcast ????";
			triggerError(Out);
			Out << "    llvmBitCastUnion " << GetValueName(&*I)
			    << "__BITCAST_TEMPORARY;\n";
		}
	}
	Out << "\n";
	TRACE_5("PromelaWriter > printing basic blocks\n");
	if (! inlineFct)
		Out << "atomic {\n";

	// print the basic blocks
	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		if (Loop * L = LI->getLoopFor(BB)) {
			if (L->getHeader() == BB && L->getParentLoop() == 0)
				printLoop(L);
		} else {
			printBasicBlock(BB);
		}
	}
	if (! inlineFct)
		Out << "}\n";

	
	if (currentProcess->getPid() == (this->elab->getNumProcesses() - 1)) {
		if (this->insertBug)
			Out << "    assert(false);\n";
	}

	Out << "}\n\n";
}

void PromelaWriter::printLoop(Loop * L)
{
//	Out << "/* Syntactic loop " << L->getHeader()->getName() << "*/\n";
//   Out << "  while (true)     ;
//   Out << "  do\n";

	for (unsigned i = 0, e = L->getBlocks().size(); i != e; ++i) {
		BasicBlock *BB = L->getBlocks()[i];
		Loop *BBLoop = LI->getLoopFor(BB);
		if (BBLoop == L)
			printBasicBlock(BB);
		else if (BB == BBLoop->getHeader()
			&& BBLoop->getParentLoop() == L)
			printLoop(BBLoop);
	}
//   Out << "  done; /* end of syntactic loop '"
//       << L->getHeader()->getName() << "' */\n";
}

void PromelaWriter::printBasicBlock(BasicBlock * BB)
{
	TRACE_6("PromelaWriter > printing basic block : " << BB->getNameStr() << "\n");

	// Don't print the label for the basic block if there are no uses, or if
	// the only terminator use is the predecessor basic block's terminator.
	// We have to scan the use list because PHI nodes use basic blocks too but
	// do not require a label to be generated.
	//
	bool NeedsLabel = false;
	for (pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; ++PI)
		if (isGotoCodeNecessary(*PI, BB)) {
			NeedsLabel = true;
			break;
		}
	
	if (NeedsLabel)
		Out << "\n" << GetValueName(BB) << ":\n";
	Out << "    skip;\n";

	// Output all of the instructions in the basic block...
	for (BasicBlock::iterator II = BB->begin(), E = --BB->end();
	     II != E; ++II) {
		if (!isInlinableInst(*II) && !isDirectAlloca(II) && !isSystemCType(II->getType())) {
			if (II->getType() != Type::getVoidTy(BB->getContext()) && !isInlineAsm(*II)) {
//        TRACE_4("\n/**** before outputLValue ****/\n");
				outputLValue(II);
			} else {
				Out << "    ";
			}
			pointerToInst = &*II;
			writeInstComputationInline(*II);
			Out << ";\n";
		} else {
			TRACE_4("/***** SKIPPING inlinable inst or direct alloca ****/\n");
		}
	}

	TRACE_4("/***** Visit terminator : " << *BB->getTerminator()->getOpcodeName() << "*****/\n");
	// Don't emit prefix or suffix for the terminator.
	visit(*BB->getTerminator());
	TRACE_4("/***** Visited terminator ****/\n");

}


// Specific Instruction type classes... note that all of the casts are
// necessary because we use the instruction classes as opaque types...
//
void PromelaWriter::visitReturnInst(ReturnInst & I)
{
	TRACE_4("/***** Visiting return inst ****/\n");

	// If this is a struct return function, return the temporary struct.
// 	bool isStructReturn =
// 		I.getParent()->getParent()->hasStructRetAttr();

// 	if (isStructReturn) {
// 		Out << "  return StructReturn;\n";
// 		return;
// 	}
	// Don't output a void return if this is the last basic block in the function
	if (I.getNumOperands() == 0 &&
		&*--I.getParent()->getParent()->end() == I.getParent() &&
		!I.getParent()->size() == 1) {
		return;
	}

	TRACE_4("/**** Nb operands : " << I.
		getNumOperands() << "****/\n");

	if (I.getNumOperands() >= 1) {
//     Out << "  {\n";
//     Out << "    ";
//     printType(Out, I.getParent()->getParent()->getReturnType());
		Out << "   llvm_cbe_mrv_temp = ";
		for (unsigned i = 0, e = I.getNumOperands(); i != e; ++i) {
			Out << "    ";
			writeOperand(I.getOperand(i));
			if (i != e - 1)
				Out << ",";
			Out << "\n";
		}
		Out << "    ;\n";
		Out << "    return llvm_cbe_mrv_temp;\n";
		return;
	}
//   Out << ";\n";
}

void PromelaWriter::visitSwitchInst(SwitchInst & SI)
{
	Out << "    switch (";
	writeOperand(SI.getOperand(0));
	Out << ") {\n  default:\n";
	printPHICopiesForSuccessor(SI.getParent(), SI.getDefaultDest(), 2);
	printBranchToBlock(SI.getParent(), SI.getDefaultDest(), 2);
	Out << ";\n";
	for (unsigned i = 2, e = SI.getNumOperands(); i != e; i += 2) {
		Out << "    case ";
		writeOperand(SI.getOperand(i));
		Out << ":\n";
		BasicBlock *Succ =
			cast < BasicBlock > (SI.getOperand(i + 1));
		printPHICopiesForSuccessor(SI.getParent(), Succ, 2);
		printBranchToBlock(SI.getParent(), Succ, 2);
		if (Function::iterator(Succ) ==
			next(Function::iterator(SI.getParent())))
			Out << "    break;\n";
	}
	Out << "    }\n";
}

void PromelaWriter::visitInvokeInst(InvokeInst & I)
{
	llvm_unreachable("Lowerinvoke pass didn't work!");
}

void PromelaWriter::visitUnwindInst(UnwindInst & I)
{
	llvm_unreachable("Lowerinvoke pass didn't work!");
}

void PromelaWriter::visitUnreachableInst(UnreachableInst & I)
{
	Out << "    /*UNREACHABLE*/;\n";
}

void PromelaWriter::visitInstruction(Instruction & I)
{
#ifndef NDEBUG
	errs() << "C Writer does not know about " << I;
#endif
	llvm_unreachable(0);
}

void PromelaWriter::outputLValue(Instruction * I)
{
	Out << "    /*OutputLValue*/ " << GetValueName(I) << " = ";
}

bool PromelaWriter::isGotoCodeNecessary(BasicBlock * From, BasicBlock * To)
{
	/// FIXME: This should be reenabled, but loop reordering safe!!
	return true;

	if (next(Function::iterator(From)) != Function::iterator(To))
		return true;	// Not the direct successor, we need a goto.

	//isa<SwitchInst>(From->getTerminator())

	if (LI->getLoopFor(From) != LI->getLoopFor(To))
		return true;
	return false;
}

bool PromelaWriter::printPHICopiesForSuccessor(BasicBlock * CurBlock,
					BasicBlock * Successor,
					unsigned Indent)
{
	bool printed = false;
	for (BasicBlock::iterator I = Successor->begin(); isa < PHINode > (I); ++I) {
		PHINode *PN = cast < PHINode > (I);
		// Now we have to do the printing.
		Value *IV = PN->getIncomingValueForBlock(CurBlock);
		if (!isa < UndefValue > (IV)) {
			Out << std::string(Indent, ' ');
			Out << "    " << GetValueName(I) << "__PHI_TEMPORARY = ";
			writeOperand(IV);
			Out << "    /* for PHI node */";
			printed = true;
		}
	}
	return printed;
}

void PromelaWriter::printBranchToBlock(BasicBlock * CurBB,
				BasicBlock * Succ, unsigned Indent)
{
	if (isGotoCodeNecessary(CurBB, Succ)) {
		Out << std::string(Indent, ' ') << "    goto ";
		writeOperand(Succ);
		Out << ";";
	}
}

/***************************************************************************
 **************** Visit functions ******************************************
 **************************************************************************/


// Branch instruction printing - Avoid printing out a branch to a basic block
// that immediately succeeds the current one.
//
void PromelaWriter::visitBranchInst(BranchInst & I)
{
	if (I.isConditional()) {
//		if (isGotoCodeNecessary(I.getParent(), I.getSuccessor(0))) {
			Out << "    if\n";
			Out << "        :: ";
			writeOperand(I.getCondition());
			Out << " -> "; 
			
			if (printPHICopiesForSuccessor(I.getParent(), I.getSuccessor(0), 2))
				Out << ";        \n";
			printBranchToBlock(I.getParent(), I.getSuccessor(0), 2);
			
			Out << "\n        :: true -> ";

// 			if (isGotoCodeNecessary(I.getParent(), I.getSuccessor(1))) {
			if (printPHICopiesForSuccessor(I.getParent(), I.getSuccessor(1), 2))
				Out << ";        \n";
			printBranchToBlock(I.getParent(), I.getSuccessor(1), 2);
			
//			}
// 		} else {
// 			// First goto not necessary, assume second one is...
// 			Out << "  if\n";
// 			Out << "    :: ";
// 			writeOperand(I.getCondition());
// 			Out << " -> ";
// 			printPHICopiesForSuccessor(I.getParent(),
// 						I.getSuccessor(1), 2);
// 			printBranchToBlock(I.getParent(),
// 					I.getSuccessor(1), 2);
// 		}

		Out << "\n    fi;\n";
	} else {
		if (printPHICopiesForSuccessor(I.getParent(), I.getSuccessor(0), 0))
			Out << ";    \n";
		printBranchToBlock(I.getParent(), I.getSuccessor(0), 0);
	}
	Out << "\n";
}

// PHI nodes get copied into temporary values at the end of predecessor basic
// blocks.  We now need to copy these temporary values into the REAL value for
// the PHI.
void PromelaWriter::visitPHINode(PHINode & I)
{
	writeOperand(&I);
	Out << "__PHI_TEMPORARY";
}


void PromelaWriter::visitBinaryOperator(Instruction & I)
{
	// binary instructions, shift instructions, setCond instructions.
	assert(!isa < PointerType > (I.getType()));
	TRACE_4("/**** visitBinaryOperator() ****/\n");

	// We must cast the results of binary operations which might be promoted.
//   bool needsCast = false;
//   if ((I.getType() == Type::getInt8Ty(I.getContext())) ||
//       (I.getType() == Type::getInt16Ty(I.getContext())) 
//       || (I.getType() == Type::getFloatTy(I.getContext()))) {
//     needsCast = true;
//     Out << "((";
//     printType(Out, I.getType(), false);
//     Out << ")(";
//   }

	// If this is a negation operation, print it out as such.  For FP, we don't
	// want to print "-0.0 - X".
	if (BinaryOperator::isNeg(&I)) {
		Out << "-(";
		writeOperand(BinaryOperator::
			getNegArgument(cast < BinaryOperator > (&I)));
		Out << ")";
	} else if (BinaryOperator::isFNeg(&I)) {
		Out << "-(";
		writeOperand(BinaryOperator::
			getFNegArgument(cast < BinaryOperator >
					(&I)));
		Out << ")";
	} else if (I.getOpcode() == Instruction::FRem) {
		// Output a call to fmod/fmodf instead of emitting a%b
		if (I.getType() == Type::getFloatTy(I.getContext()))
			Out << "fmodf(";
		else if (I.getType() == Type::getDoubleTy(I.getContext()))
			Out << "fmod(";
		else		// all 3 flavors of long double
			Out << "fmodl(";
		writeOperand(I.getOperand(0));
		Out << ", ";
		writeOperand(I.getOperand(1));
		Out << ")";
	} else {

		// Write out the cast of the instruction's value back to the proper type
		// if necessary.
//     bool NeedsClosingParens = writeInstructionCast(I);

		// Certain instructions require the operand to be forced to a specific type
		// so we use writeOperandWithCast here instead of writeOperand. Similarly
		// below for operand 1
		//    writeOperandWithCast(I.getOperand(0), I.getOpcode());
		writeOperand(I.getOperand(0), I.getOpcode());

		switch (I.getOpcode()) {
		case Instruction::Add:
		case Instruction::FAdd:
			Out << " + ";
			break;
		case Instruction::Sub:
		case Instruction::FSub:
			Out << " - ";
			break;
		case Instruction::Mul:
		case Instruction::FMul:
			Out << " * ";
			break;
		case Instruction::URem:
		case Instruction::SRem:
		case Instruction::FRem:
			Out << " % ";
			break;
		case Instruction::UDiv:
		case Instruction::SDiv:
		case Instruction::FDiv:
			Out << " / ";
			break;
		case Instruction::And:
			Out << " & ";
			break;
		case Instruction::Or:
			Out << " | ";
			break;
		case Instruction::Xor:
			Out << " ^ ";
			break;
		case Instruction::Shl:
			Out << " << ";
			break;
		case Instruction::LShr:
		case Instruction::AShr:
			Out << " >> ";
			break;
		default:
#ifndef NDEBUG
			errs() << "Invalid operator type!" << I;
#endif
			llvm_unreachable(0);
		}

		//    writeOperandWithCast(I.getOperand(1), I.getOpcode());
		writeOperand(I.getOperand(1), I.getOpcode());
//     if (NeedsClosingParens)
//       Out << "))";
	}

//   if (needsCast) {
//     Out << "))";
//   }
}

void PromelaWriter::visitICmpInst(ICmpInst & I)
{
	// We must cast the results of icmp which might be promoted.
//   bool needsCast = false;

	// Write out the cast of the instruction's value back to the proper type
	// if necessary.
//   bool NeedsClosingParens = writeInstructionCast(I);

	// Certain icmp predicate require the operand to be forced to a specific type
	// so we use writeOperandWithCast here instead of writeOperand. Similarly
	// below for operand 1
//   writeOperandWithCast(I.getOperand(0), I);
	writeOperand(I.getOperand(0));

	switch (I.getPredicate()) {
	case ICmpInst::ICMP_EQ:
		Out << " == ";
		break;
	case ICmpInst::ICMP_NE:
		Out << " != ";
		break;
	case ICmpInst::ICMP_ULE:
	case ICmpInst::ICMP_SLE:
		Out << " <= ";
		break;
	case ICmpInst::ICMP_UGE:
	case ICmpInst::ICMP_SGE:
		Out << " >= ";
		break;
	case ICmpInst::ICMP_ULT:
	case ICmpInst::ICMP_SLT:
		Out << " < ";
		break;
	case ICmpInst::ICMP_UGT:
	case ICmpInst::ICMP_SGT:
		Out << " > ";
		break;
	default:
#ifndef NDEBUG
		errs() << "Invalid icmp predicate!" << I;
#endif
		llvm_unreachable(0);
	}

//   writeOperandWithCast(I.getOperand(1), I);
	writeOperand(I.getOperand(1));
//   if (NeedsClosingParens)
//     Out << "))";

//   if (needsCast) {
//     Out << "))";
//   }
}

void PromelaWriter::visitFCmpInst(FCmpInst & I)
{
	if (I.getPredicate() == FCmpInst::FCMP_FALSE) {
		Out << "0";
		return;
	}
	if (I.getPredicate() == FCmpInst::FCMP_TRUE) {
		Out << "1";
		return;
	}

	const char *op = 0;
	switch (I.getPredicate()) {
	default:
		llvm_unreachable("Illegal FCmp predicate");
	case FCmpInst::FCMP_ORD:
		op = "ord";
		break;
	case FCmpInst::FCMP_UNO:
		op = "uno";
		break;
	case FCmpInst::FCMP_UEQ:
		op = "ueq";
		break;
	case FCmpInst::FCMP_UNE:
		op = "une";
		break;
	case FCmpInst::FCMP_ULT:
		op = "ult";
		break;
	case FCmpInst::FCMP_ULE:
		op = "ule";
		break;
	case FCmpInst::FCMP_UGT:
		op = "ugt";
		break;
	case FCmpInst::FCMP_UGE:
		op = "uge";
		break;
	case FCmpInst::FCMP_OEQ:
		op = "oeq";
		break;
	case FCmpInst::FCMP_ONE:
		op = "one";
		break;
	case FCmpInst::FCMP_OLT:
		op = "olt";
		break;
	case FCmpInst::FCMP_OLE:
		op = "ole";
		break;
	case FCmpInst::FCMP_OGT:
		op = "ogt";
		break;
	case FCmpInst::FCMP_OGE:
		op = "oge";
		break;
	}

	Out << "llvm_fcmp_" << op << "(";
	// Write the first operand
	writeOperand(I.getOperand(0));
	Out << ", ";
	// Write the second operand
	writeOperand(I.getOperand(1));
	Out << ")";
}

static const char *getFloatBitCastField(const Type * Ty)
{
	switch (Ty->getTypeID()) {
	default:
		llvm_unreachable("Invalid Type");
	case Type::FloatTyID:
		return "Float";
	case Type::DoubleTyID:
		return "Double";
	case Type::IntegerTyID:{
		unsigned NumBits =
			cast < IntegerType > (Ty)->getBitWidth();
		if (NumBits <= 32)
			return "Int32";
		else
			return "Int64";
	}
	}
}

void PromelaWriter::visitCastInst(CastInst & I)
{
	const Type *DstTy = I.getType();
	const Type *SrcTy = I.getOperand(0)->getType();

	if (isFPIntBitCast(I)) {
		Out << '(';
		// These int<->float and long<->double casts need to be handled specially
		Out << GetValueName(&I) << "__BITCAST_TEMPORARY."
		    << getFloatBitCastField(I.getOperand(0)->
					    getType()) << " = ";
		writeOperand(I.getOperand(0));
		Out << ", " << GetValueName(&I) << "__BITCAST_TEMPORARY."
		    << getFloatBitCastField(I.getType());
		Out << ')';
		return;
	}
//   Out << '(';
//   printCast(I.getOpcode(), SrcTy, DstTy);

	// Make a sext from i1 work by subtracting the i1 from 0 (an int).
	if (SrcTy == Type::getInt1Ty(I.getContext()) &&
		I.getOpcode() == Instruction::SExt)
		Out << "0-";

	writeOperand(I.getOperand(0));

	if (DstTy == Type::getInt1Ty(I.getContext()) &&
		(I.getOpcode() == Instruction::Trunc ||
			I.getOpcode() == Instruction::FPToUI ||
			I.getOpcode() == Instruction::FPToSI ||
			I.getOpcode() == Instruction::PtrToInt)) {
		// Make sure we really get a trunc to bool by anding the operand with 1 
		Out << "&1u";
	}
//   Out << ')';
}

void PromelaWriter::visitSelectInst(SelectInst & I)
{
	ErrorMsg << "NYI : SelectInst\n";
	triggerError(Out);

	Out << "((";
	writeOperand(I.getCondition());
	Out << ") ? (";
	writeOperand(I.getTrueValue());
	Out << ") : (";
	writeOperand(I.getFalseValue());
	Out << "))";
}


void PromelaWriter::lowerIntrinsics(Function & F)
{
	// This is used to keep track of intrinsics that get generated to a lowered
	// function. We must generate the prototypes before the function body which
	// will only be expanded on first use (by the loop below).
	std::vector < Function * >prototypesToGen;

	// Examine all the instructions in this function to find the intrinsics that
	// need to be lowered.
	for (Function::iterator BB = F.begin(), EE = F.end(); BB != EE;
	     ++BB)
		for (BasicBlock::iterator I = BB->begin(), E = BB->end();
		     I != E;)
			if (CallInst * CI = dyn_cast < CallInst > (I++))
				if (Function * F = CI->getCalledFunction())
					switch (F->getIntrinsicID()) {
					case Intrinsic::not_intrinsic:
					case Intrinsic::memory_barrier:
					case Intrinsic::vastart:
					case Intrinsic::vacopy:
					case Intrinsic::vaend:
					case Intrinsic::returnaddress:
					case Intrinsic::frameaddress:
					case Intrinsic::setjmp:
					case Intrinsic::longjmp:
					case Intrinsic::prefetch:
					case Intrinsic::dbg_stoppoint:
					case Intrinsic::powi:
					case Intrinsic::x86_sse_cmp_ss:
					case Intrinsic::x86_sse_cmp_ps:
					case Intrinsic::x86_sse2_cmp_sd:
					case Intrinsic::x86_sse2_cmp_pd:
					case Intrinsic::ppc_altivec_lvsl:
						// We directly implement these intrinsics
						break;
					default:
						// If this is an intrinsic that directly corresponds to a GCC
						// builtin, we handle it.
						const char *BuiltinName =
							"";
#define GET_GCC_BUILTIN_NAME
#include "llvm/Intrinsics.gen"
#undef GET_GCC_BUILTIN_NAME
						// If we handle it, don't lower it.
						if (BuiltinName[0])
							break;

						// All other intrinsic calls we must lower.
						Instruction *Before = 0;
						if (CI != &BB->front())
							Before =
								prior
								(BasicBlock::
									iterator(CI));

						IL->LowerIntrinsicCall(CI);
						if (Before) {	// Move iterator to instruction after call
							I = Before;
							++I;
						} else {
							I = BB->begin();
						}
						// If the intrinsic got lowered to another call, and that call has
						// a definition then we need to make sure its prototype is emitted
						// before any calls to it.
						if (CallInst * Call =
							dyn_cast < CallInst >
							(I))
							if (Function *
								NewF =
								Call->
								getCalledFunction
								())
								if (!NewF->
									isDeclaration
									())
									prototypesToGen.
										push_back
										(NewF);

						break;
					}
	// We may have collected some prototypes to emit in the loop above. 
	// Emit them now, before the function that uses them is emitted. But,
	// be careful not to emit them twice.
	std::vector < Function * >::iterator I = prototypesToGen.begin();
	std::vector < Function * >::iterator E = prototypesToGen.end();
	for (; I != E; ++I) {
		if (intrinsicPrototypesAlreadyGenerated.insert(*I).second) {
			Out << '\n';
			printFunctionSignature(*I, true, true);
			Out << ";\n";
		}
	}
}

void
PromelaWriter::printCodingGlobals()
{
 	int nbThreads = this->elab->getNumProcesses();
 	int nbEvents = this->elab->getNumEvents();
//	int ct;
	
	Out << 	"#define NBTHREADS " << nbThreads << "\n"
		"#define NBEVENTS " << nbEvents << "\n"
		"bool finished[NBTHREADS];\n\n"
		"int Tg;\n"
		"int T[NBTHREADS];\n"
		"int S[NBEVENTS];\n"
		"\n";

	if (this->eventsAsBool) {
		Out <<	"bool waiters[NBTHREADS];\n\n";
			
		vector < Process * >::iterator processIt = this->elab->getProcesses()->begin();
		vector < Process * >::iterator endIt = this->elab->getProcesses()->end();

		for (; processIt < endIt; ++processIt) {
			Process *proc = *processIt;
			std::vector < Event* >* events = proc->getEvents();
			vector < Event * >::iterator evIt = events->begin();
			vector < Event * >::iterator endEvIt = events->end();
		
			for (; evIt < endEvIt; ++evIt) {
				Event* event = *evIt;
				Out << "bool " << getEventName(proc, event) << " = false;\n"; 
			}
		}
	} else {
		
		Out <<	"int e[NBTHREADS];\n";
	}
	Out << "\n";
}

void
PromelaWriter::printWaitTimePrimitive()
{
	int nbThreads = this->elab->getNumProcesses();
	int ct;

	if (this->relativeClocks) {
		triggerError(Out, "NYI : relative encoding for time in PromelaBackend\n\n");
	}

	Out << ""
		"inline wait(pnumber, time)\n"
		"{\n"
		"    assert(T[pnumber] == Tg);\n"
		"    T[pnumber] = T[pnumber] + time;         \n";
	for (ct = 0; ct < nbThreads - 1; ct++) {
		Out << "    ( finished[" + intToString(ct) + "] || e[" + intToString(ct) + "] != 0 || T[pnumber] <= T["+ intToString(ct) + "] ) && \n";
	}
	Out << "    ( finished[" + intToString(nbThreads - 1) + "] || e[" + intToString(nbThreads - 1) + "] != 0 || T[pnumber] <= T["+ intToString(nbThreads - 1) + "] );\n";
	Out <<"    Tg = T[pnumber];\n"
		"}\n\n";
}


void
PromelaWriter::printNotifyPrimitive()
{
//	int nbThreads = this->elab->getNumProcesses();
// 	int ct;

// 	vector < Process * >::iterator processIt = this->elab->getProcesses()->begin();
// 	vector < Process * >::iterator endIt = this->elab->getProcesses()->end();

// 	for (; processIt < endIt; ++processIt) {
// 		Process *proc = *processIt;
 		std::vector < Event* >* events = this->elab->getEvents();
		vector < Event * >::iterator evIt = events->begin();
		vector < Event * >::iterator endEvIt = events->end();
		
		for (; evIt < endEvIt; ++evIt) {
			Event* event = *evIt;
			
			Out << "inline notify_" << getEventName(NULL, event) << "(pnumber)\n"
				"{\n";
			vector < Process * >::iterator processIt2 = event->getProcesses()->begin();
			vector < Process * >::iterator endIt2 = event->getProcesses()->end();
			
			for (; processIt2 < endIt2; ++processIt2) {
				Process *proc2 = *processIt2;
				
				if (this->eventsAsBool) {
					Out << "    if\n";
					Out << "      :: " << getEventName(proc2, event) << " == true ->\n";
					Out << "        " << getEventName(proc2, event) << " = false;\n";
					Out << "        assert(T[" << proc2->getPid() << "] <= T[pnumber]);\n";
					Out << "        T[" << proc2->getPid() << "] = T[pnumber];\n";
					Out << "        waiters[" << proc2->getPid() << "] = false;\n";
					Out << "      :: (" << getEventName(proc2, event) << ") == false -> skip;\n";
					Out << "    fi;\n";
				} else {
					Out << "    if\n"
						"    :: e[" << proc2->getPid() << "] == " << event->getNumEvent() << "  ->\n"
						"       e[" << proc2->getPid() << "] = 0;\n"
						"       assert(T[" << proc2->getPid() << "] <= T[pnumber]);\n"
						"       T[" << proc2->getPid() << "]=T[pnumber];\n"
						"    :: else -> skip;"
						"\n";
					Out << "    fi;\n";

				}
			}
			Out << "    S[" << event->getNumEvent() << "] = " << "T[pnumber];\n";
			Out << "}\n\n";
		}
//	}
}

void
PromelaWriter::printWaitEventPrimitive()
{
// 	int nbThreads = this->elab->getNumProcesses();
// 	int ct;

	vector < Process * >::iterator processIt = this->elab->getProcesses()->begin();
	vector < Process * >::iterator endIt = this->elab->getProcesses()->end();
	
	for (; processIt < endIt; ++processIt) {
		Process *proc = *processIt;
		std::vector < Event* >* events = proc->getEvents();
		vector < Event * >::iterator evIt = events->begin();
		vector < Event * >::iterator endEvIt = events->end();
		
		for (; evIt < endEvIt; ++evIt) {
			Event* event = *evIt;
			
			Out << "inline wait_" << getEventName(proc, event) << "()\n"
				"{\n";
			
			if (this->eventsAsBool) {
				Out << "    assert(T[" << proc->getPid() << "] == Tg);\n"
					"    " << getEventName(proc, event) << " = true;\n"
					"    waiters[" << proc->getPid() << "] = true;\n"
					"     " << getEventName(proc, event) << " == false;\n"
					"    assert(T[" << proc->getPid() << "] == S[" << event->getNumEvent() << "]);\n"
					"    Tg = T[" << proc->getPid() << "];\n";
			} else {
				Out << 	"    assert(T[" << proc->getPid() << "] == Tg);\n"
					"    e[" << proc->getPid() << "] = " << event->getNumEvent() << ";\n"
					"    e[" << proc->getPid() << "] == 0;\n"
					"    assert(T[" << proc->getPid() << "] == S[" << event->getNumEvent() << "]);\n"
					"    Tg = T[" << proc->getPid() << "];\n";
			}
			Out << "}\n\n";
		}
	}
}



void
PromelaWriter::printPrimitives()
{
	Out << "\n\n/*---- Encoding ----*/\n";
	printCodingGlobals();
	printWaitTimePrimitive();
	printNotifyPrimitive();
	printWaitEventPrimitive();
}

void
PromelaWriter::printGlobalVariables(Mangler* mang)
{
	vector < GlobalValue * >::iterator globalIt = this->elab->getGlobalVariables()->begin();
	vector < GlobalValue * >::iterator globalEnd = this->elab->getGlobalVariables()->end();

	TRACE_2("PromelaWriter > Emitting Global variables\n");

	Out << "/*---- Global variables ----*/\n";
	for (; globalIt < globalEnd; ++globalIt) {
		GlobalValue* gv = *globalIt;
		printType(Out, gv->getType(), false, mang->getMangledName(gv));
		Out << ";\n";
	}
}

void
PromelaWriter::printProcesses()
{
	vector < Process * >::iterator processIt = this->elab->getProcesses()->begin();
	vector < Process * >::iterator endIt = this->elab->getProcesses()->end();

	TRACE_2("PromelaWriter > Emitting Processes\n");
	Out << "\n\n/*---- Threads ----*/\n";
	for (; processIt < endIt; ++processIt) {

		Process *proc = *processIt;
		std::vector < Function * >*usedFcts = proc->getUsedFunctions();
		currentProcess = proc;
		this->scjit->setCurrentProcess(currentProcess);
		TRACE_3("PromelaWriter > printing process : " << proc->getName() << "\n");
		TRACE_3("Info : nb of used functions : " << usedFcts->size() << "\n");

		for (std::vector < Function * >::iterator itF = usedFcts->begin();
		     itF < usedFcts->end(); ++itF) {

			Function *F = *itF;
			TRACE_4("PromelaWriter > printing function : " << F->getNameStr() << "\n");

			// Do not codegen any 'available_externally' functions at all, they have
			// definitions outside the translation unit.
			if (F->hasAvailableExternallyLinkage())
				continue;

			LI = &getAnalysis < LoopInfo > (*F);

			// Get rid of intrinsics we can't handle.
			lowerIntrinsics(*F);

			// Output all floating point constants that cannot be printed accurately.
			printFloatingPointConstants(*F);

			printFunction(*F, false);
		}
	}
}


void
PromelaWriter::printInitSection()
{
	vector < Process * >::iterator processIt = this->elab->getProcesses()->begin();
	vector < Process * >::iterator endIt = this->elab->getProcesses()->end();
	
	TRACE_2("PromelaWriter > Emitting init section \n");
	Out << "/* ----------------------------- Init --------------------------------- */\n"
		"init\n{\n"
		"    int i = 0;\n";

	if (this->eventsAsBool) {
		Out << ""
			"    Tg=0;\n"
			"    do\n"
			"      :: i == NBTHREADS -> break;\n"
			"      :: else ->\n"
			"         T[i] = 0;\n"
			"         waiters[i]= false;\n"
			"         finished[i] = false;\n"
			"         i++;\n"
			"    od;\n"
			"    i = 0;\n"
			"    do\n"
			"      :: i == NBEVENTS -> break;\n"
			"      :: else ->\n"
			"         S[i] = 0;\n"
			"         i++;\n"
			"    od;\n"
			"    \n";
	} else {
		Out <<  "    Tg=0;\n"
			"    do\n"
			"      :: i == NBTHREADS -> break;\n"
			"      :: else ->\n"
			"         e[i] = 0;\n"
			"         T[i] = 0;\n"
			"         finished[i] = false;\n"
			"         i++;\n"
			"    od;\n"
			"    i = 0;\n"
			"    do\n"
			"      :: i == NBEVENTS -> break;\n"
			"      :: else ->\n"
			"         S[i] = 0;\n"
			"         i++;\n"
			"    od;\n"
			"\n";
	}

	for (; processIt < endIt; ++processIt) {
		Process *proc = *processIt;
		const std::string fctName = GetValueName(proc->getMainFct()) + "_pnumber_" + intToString(proc->getPid());
		const std::string modName = "mod_" + proc->getModule()->getUniqueName();
		Out << "    ";
		printType(Out, proc->getMainFct()->arg_begin()->getType() , false, modName, false, AttrListPtr());
		Out << ";\n";
	}

	Out << "\n";
	Out <<
		"    mod_Sink.field3 = true;\n"
		"    mod_Source.field2 = true;\n"
		"\n"
		"    atomic {\n";

	processIt = this->elab->getProcesses()->begin();
	for (; processIt < endIt; ++processIt) {
		Process *proc = *processIt;
		const std::string fctName = GetValueName(proc->getMainFct()) + "_pnumber_" + intToString(proc->getPid());
		const std::string modName = "mod_" + proc->getModule()->getUniqueName();
		Out << "        run " + fctName + "(" << modName << ");\n";
	}
	
	Out << "    }\n}\n";
}

std::string
PromelaWriter::getEventName(Process* proc, Event* event)
{
	std::stringstream ss;
	if (proc == NULL)
		ss << event->toString();
	else
		ss << event->toString() << "_" << proc->getPid();
	return ss.str();
}

/*
 * TODO : manage the case where events and time couldn't be determined statically
 */
void
PromelaWriter::visitSCConstruct(SCConstruct * scc)
{
	TimeConstruct* tc;
	NotifyConstruct* notifyC;
	EventConstruct* eventC;	
	ReadConstruct* rc;
	WriteConstruct* wc;
	Event* event;
	Port* port;
	vector<Channel*>* channels;
	vector<Channel*>::iterator channelsIt;
	SimpleChannel* sc;

	TRACE_4("/***** visitSCConstruct() *****/\n");
	switch(scc->getID()) {
	case WAITEVENTCONSTRUCT:
		eventC = (EventConstruct*) scc;
		event = eventC->getWaitedEvent();
		if (eventC->isStaticallyFound()) {
			Out << "wait_" << getEventName(currentProcess, event) << "();\n";
		} else {
			Out << "/* TODO: wait_e() on event not determined statically  */";
                        /* todo */
		}
		break;
	case NOTIFYCONSTRUCT:
		notifyC = (NotifyConstruct*) scc;
		if (notifyC->isStaticallyFound()) {
			event = notifyC->getNotifiedEvent();
			Out << "    notify_" << getEventName(NULL, event) << "(" << currentProcess->getPid() << ");\n";
		} else {
			Out << "/* TODO: notify() event not determined statically */";
			/* todo */
		}
		break;
	case TIMECONSTRUCT:
		tc = (TimeConstruct*) scc;
		if (tc->isStaticallyFound()) {
			Out << "wait(" << currentProcess->getPid() << ", ";
			Out << intToString(tc->getTime());
			Out << ")";
		} else {
			Out << "/* Todo: wait() time not determined statically */";
			/* todo */
		}
		break;
	case READCONSTRUCT:
		rc = (ReadConstruct*) scc;
		port = rc->getPort();
		
		if (port->getChannelID() == SIMPLE_CHANNEL) {
			if (port->getChannels()->size() != 1 ) {
				ERROR("Reading in a port binded to more than one channel is not possible\n");
			} else {
				SimpleChannel* sc = (SimpleChannel*) port->getChannel();
				Out << "/* read() on simpleport */\n";
				sc->getGlobalVariableName();
			}
		} else {
			Out << "/* TODO : read() on a non simple channel */";
			/* todo */
		}
		break;
	case WRITECONSTRUCT:
		wc = (WriteConstruct*) scc;		
		port = wc->getPort();
		channels = port->getChannels();
		
		switch(port->getChannelID()) {
		case SIMPLE_CHANNEL:
			for (channelsIt = channels->begin() ; channelsIt != channels->end() ; ++channelsIt) {
				sc = (SimpleChannel*) *channelsIt;
//			if (port->getGlobalVariableType()->getTypeID() != Type::PointerTyID) {
				Out << "/* write() on simpleport */\n";
				Out << sc->getGlobalVariableName() << " = " << wc->getValue();
 				if (channelsIt != channels->end())
 					Out << ";\n";
//			}
			break;
		case FORWARDING_CHANNEL:
			Out << "/* TODO : write() on a forwarding channel */";
			/* todo */
			for (channelsIt = channels->begin() ; channelsIt != channels->end() ; ++channelsIt) {
				/* NYI */
			}
			break;
		case FIFO_CHANNEL:
			Out << "/* TODO : write() on a FIFO */";
			/* todo */
			for (channelsIt = channels->begin() ; channelsIt != channels->end() ; ++channelsIt) {
				/* NYI */
			}
			break;
		case CLOCK_CHANNEL:
			/* IMPOSSIBLE case */
			ERROR("How can we write on a CLOCK channel ??\n");
			break;
		default:
			Out << "/* write() on port ??? */\n";
			break;
 		}

// 		if (wc->isStaticallyFound()) {
// 			Out << wc->getGlobalVariable() << " = " << wc->getValue() << "\n";
// 		} else {
			/* todo */
 		}
		break;
	default:
		ErrorMsg << "Construction not managed in Simple backend: " << scc->getID();
		triggerError(Out);
	}
}

void PromelaWriter::visitCallInst(CallInst & I)
{
	std::map <CallInst*, std::map<Process*, SCConstruct*> >::iterator itC;
	CallInst* pI = cast<CallInst>(pointerToInst);
	itC = this->sccfactory->getConstructs()->find(pI);
	if (itC != this->sccfactory->getConstructs()->end()) {
		std::map<Process*, SCConstruct * > CbyP = itC->second;
		return visitSCConstruct(CbyP.find(currentProcess)->second);
	}
	TRACE_4("Visiting CallInst, function is : " << I.getCalledFunction()->getNameStr() << "\n");
	if (isa < InlineAsm > (I.getOperand(0)))
		return visitInlineAsm(I);

	bool WroteCallee = false;

	// Handle intrinsic function calls first...
	if (Function * F = I.getCalledFunction())
		if (Intrinsic::ID ID = (Intrinsic::ID) F->getIntrinsicID())
			if (visitBuiltinCall(I, ID, WroteCallee))
				return;

	Value *Callee = I.getCalledValue();

	const PointerType *PTy = cast < PointerType > (Callee->getType());
	const FunctionType *FTy = cast < FunctionType > (PTy->getElementType());

	// If this is a call to a struct-return function, assign to the first
	// parameter instead of passing it to the call.
	const AttrListPtr & PAL = I.getAttributes();
	bool hasByVal = I.hasByValArgument();
 	bool isStructRet = I.hasStructRetAttr();
// 	if (isStructRet) {
// 		writeOperandDeref(I.getOperand(1));
// 		Out << " = ";
// 	}

	if (I.isTailCall())
		Out << " /*tail*/ ";

	if (!WroteCallee) {
		// If this is an indirect call to a struct return function, we need to cast
		// the pointer. Ditto for indirect calls with byval arguments.
		bool NeedsCast = (hasByVal || isStructRet) && !isa < Function > (Callee);

		// GCC is a real PITA.  It does not permit codegening casts of functions to
		// function pointers if they are in a call (it generates a trap instruction
		// instead!).  We work around this by inserting a cast to void* in between
		// the function and the function pointer cast.  Unfortunately, we can't just
		// form the constant expression here, because the folder will immediately
		// nuke it.
		//
		// Note finally, that this is completely unsafe.  ANSI C does not guarantee
		// that void* and function pointers have the same size. :( To deal with this
		// in the common case, we handle casts where the number of arguments passed
		// match exactly.
		//
		if (ConstantExpr * CE = dyn_cast < ConstantExpr > (Callee)) {
			if (CE->isCast())
				if (Function * RF = dyn_cast < Function > (CE->getOperand(0))) {
					NeedsCast = true;
					Callee = RF;
				}
		}
		if (NeedsCast) {
			// Ok, just cast the pointer type.
			Out << "((";
			if (isStructRet)
				printStructReturnPointerFunctionType(Out, PAL, cast <PointerType>(I.getCalledValue()->getType()));
			else if (hasByVal)
				printType(Out,
					I.getCalledValue()->getType(),
					false, "", true, PAL);
			else
				printType(Out,
					I.getCalledValue()->getType());
			Out << ")(void*)";
		}
		writeOperand(Callee);
		Out << "_pnumber_" << currentProcess->getPid();
		Function* cf = pI->getCalledFunction();
		Function* pf = pI->getParent()->getParent();
		if (cf->getArgumentList().size() != 0) {
			Value* arg = pI->getOperand(1);
			void* mod = this->scjit->jitAddr(pf, arg);
			TRACE_4("################# Module jitted : " << mod << "\n");
			TRACE_4("################# IRModule associated : " << this->elab->getIRModule(mod) << "\n");
		}
		if (NeedsCast)
			Out << ')';
	}

	Out << '(';

	unsigned NumDeclaredParams = FTy->getNumParams();

	CallSite::arg_iterator AI = I.op_begin() + 1, AE = I.op_end();
	unsigned ArgNo = 0;
// 	if (isStructRet) {	// Skip struct return argument.
// 		++AI;
// 		++ArgNo;
// 	}

	bool PrintedArg = false;
	for (; AI != AE; ++AI, ++ArgNo) {
		if (AI->getUser()->getNumUses() == 0) {
			continue;
		}
		if (PrintedArg)
			Out << ", ";
		if (ArgNo < NumDeclaredParams &&
			(*AI)->getType() != FTy->getParamType(ArgNo)) {
			Out << '(';
			printType(Out, FTy->getParamType(ArgNo),/*isSigned= */ PAL.paramHasAttr(ArgNo + 1, Attribute::SExt));
			Out << ')';
		}
		// Check if the argument is expected to be passed by value.
		if (I.paramHasAttr(ArgNo + 1, Attribute::ByVal))
			writeOperandDeref(*AI);
		else
			writeOperand(*AI);
		PrintedArg = true;
	}
	Out << ')';
}

/// visitBuiltinCall - Handle the call to the specified builtin.  Returns true
/// if the entire call is handled, return false it it wasn't handled, and
/// optionally set 'WroteCallee' if the callee has already been printed out.
bool PromelaWriter::visitBuiltinCall(CallInst & I, Intrinsic::ID ID,
				bool & WroteCallee)
{
	switch (ID) {
	default:{
		// If this is an intrinsic that directly corresponds to a GCC
		// builtin, we emit it here.
		const char *BuiltinName = "";
		Function *F = I.getCalledFunction();
#define GET_GCC_BUILTIN_NAME
#include "llvm/Intrinsics.gen"
#undef GET_GCC_BUILTIN_NAME
		assert(BuiltinName[0]
			&& "Unknown LLVM intrinsic!");

		Out << BuiltinName;
		WroteCallee = true;
		return false;
	}
	case Intrinsic::memory_barrier:
		Out << "__sync_synchronize()";
		return true;
	case Intrinsic::vastart:
		Out << "0; ";

		Out << "va_start(*(va_list*)";
		writeOperand(I.getOperand(1));
		Out << ", ";
		// Output the last argument to the enclosing function.
		if (I.getParent()->getParent()->arg_empty()) {
			std::string msg;
			raw_string_ostream Msg(msg);
			Msg <<
				"The C backend does not currently supoprt zero "
			    << "argument varargs functions, such as '" <<
				I.getParent()->getParent()->getName() << "'!";
			llvm_report_error(Msg.str());
		}
		writeOperand(--I.getParent()->getParent()->arg_end());
		Out << ')';
		return true;
	case Intrinsic::vaend:
		if (!isa < ConstantPointerNull > (I.getOperand(1))) {
			Out << "0; va_end(*(va_list*)";
			writeOperand(I.getOperand(1));
			Out << ')';
		} else {
			Out << "va_end(*(va_list*)0)";
		}
		return true;
	case Intrinsic::vacopy:
		Out << "0; ";
		Out << "va_copy(*(va_list*)";
		writeOperand(I.getOperand(1));
		Out << ", *(va_list*)";
		writeOperand(I.getOperand(2));
		Out << ')';
		return true;
	case Intrinsic::returnaddress:
		Out << "__builtin_return_address(";
		writeOperand(I.getOperand(1));
		Out << ')';
		return true;
	case Intrinsic::frameaddress:
		Out << "__builtin_frame_address(";
		writeOperand(I.getOperand(1));
		Out << ')';
		return true;
	case Intrinsic::powi:
		Out << "__builtin_powi(";
		writeOperand(I.getOperand(1));
		Out << ", ";
		writeOperand(I.getOperand(2));
		Out << ')';
		return true;
	case Intrinsic::setjmp:
		Out << "setjmp(*(jmp_buf*)";
		writeOperand(I.getOperand(1));
		Out << ')';
		return true;
	case Intrinsic::longjmp:
		Out << "longjmp(*(jmp_buf*)";
		writeOperand(I.getOperand(1));
		Out << ", ";
		writeOperand(I.getOperand(2));
		Out << ')';
		return true;
	case Intrinsic::prefetch:
		Out << "LLVM_PREFETCH((const void *)";
		writeOperand(I.getOperand(1));
		Out << ", ";
		writeOperand(I.getOperand(2));
		Out << ", ";
		writeOperand(I.getOperand(3));
		Out << ")";
		return true;
	case Intrinsic::stacksave:
		// Emit this as: Val = 0; *((void**)&Val) = __builtin_stack_save()
		// to work around GCC bugs (see PR1809).
		Out << "0; *((void**)&" << GetValueName(&I)
		    << ") = __builtin_stack_save()";
		return true;
	case Intrinsic::dbg_stoppoint:{
		// If we use writeOperand directly we get a "u" suffix which is rejected
		// by gcc.
		DbgStopPointInst & SPI =
			cast < DbgStopPointInst > (I);
		std::string dir;
		GetConstantStringInfo(SPI.getDirectory(), dir);
		std::string file;
		GetConstantStringInfo(SPI.getFileName(), file);
		Out << "\n#line " << SPI.getLine()
		    << " \"" << dir << '/' << file << "\"\n";
		return true;
	}
	case Intrinsic::x86_sse_cmp_ss:
	case Intrinsic::x86_sse_cmp_ps:
	case Intrinsic::x86_sse2_cmp_sd:
	case Intrinsic::x86_sse2_cmp_pd:
		Out << '(';
		printType(Out, I.getType());
		Out << ')';
		// Multiple GCC builtins multiplex onto this intrinsic.
		switch (cast < ConstantInt >
			(I.getOperand(3))->getZExtValue()) {
		default:
			llvm_unreachable("Invalid llvm.x86.sse.cmp!");
		case 0:
			Out << "__builtin_ia32_cmpeq";
			break;
		case 1:
			Out << "__builtin_ia32_cmplt";
			break;
		case 2:
			Out << "__builtin_ia32_cmple";
			break;
		case 3:
			Out << "__builtin_ia32_cmpunord";
			break;
		case 4:
			Out << "__builtin_ia32_cmpneq";
			break;
		case 5:
			Out << "__builtin_ia32_cmpnlt";
			break;
		case 6:
			Out << "__builtin_ia32_cmpnle";
			break;
		case 7:
			Out << "__builtin_ia32_cmpord";
			break;
		}
		if (ID == Intrinsic::x86_sse_cmp_ps
			|| ID == Intrinsic::x86_sse2_cmp_pd)
			Out << 'p';
		else
			Out << 's';
		if (ID == Intrinsic::x86_sse_cmp_ss
			|| ID == Intrinsic::x86_sse_cmp_ps)
			Out << 's';
		else
			Out << 'd';

		Out << "(";
		writeOperand(I.getOperand(1));
		Out << ", ";
		writeOperand(I.getOperand(2));
		Out << ")";
		return true;
	case Intrinsic::ppc_altivec_lvsl:
		Out << '(';
		printType(Out, I.getType());
		Out << ')';
		Out << "__builtin_altivec_lvsl(0, (void*)";
		writeOperand(I.getOperand(1));
		Out << ")";
		return true;
	}
}

//TODO: assumptions about what consume arguments from the call are likely wrong
//      handle communitivity
void PromelaWriter::visitInlineAsm(CallInst & CI)
{
	triggerError(Out, "Cannot handle inline ASM\n");
}

void PromelaWriter::visitMallocInst(MallocInst & I)
{
	llvm_unreachable("lowerallocations pass didn't work!");
}

void PromelaWriter::visitAllocaInst(AllocaInst & I)
{
	TRACE_4("visitAllocaInst()\n");
	Out << '(';
	printType(Out, I.getType());
	Out << ") alloca(sizeof(";
	printType(Out, I.getType()->getElementType());
	Out << ')';
	if (I.isArrayAllocation()) {
		Out << " * ";
		writeOperand(I.getOperand(0));
	}
	Out << ')';
}

void PromelaWriter::visitFreeInst(FreeInst & I)
{
	llvm_unreachable("lowerallocations pass didn't work!");
}

void
PromelaWriter::printGEPExpression(Value * Ptr, gep_type_iterator I,	gep_type_iterator E, bool Static)
{
	TRACE_4("/**** printGEPExpression() ****/\n");

	// If there are no indices, just print out the pointer.
	if (I == E) {
		writeOperand(Ptr);
		return;
	}
	// Find out if the last index is into a vector.  If so, we have to print this
	// specially.  Since vectors can't have elements of indexable type, only the
	// last index could possibly be of a vector element.
	const VectorType *LastIndexIsVector = 0;
	{
		for (gep_type_iterator TmpI = I; TmpI != E; ++TmpI)
			LastIndexIsVector =
				dyn_cast < VectorType > (*TmpI);
	}

	Out << "(";

	// If the last index is into a vector, we can't print it as &a[i][j] because
	// we can't index into a vector with j in GCC.  Instead, emit this as
	// (((float*)&a[i])+j)
	if (LastIndexIsVector) {
		Out << "((";
		printType(Out,
			PointerType::getUnqual(LastIndexIsVector->
					getElementType()));
		Out << ")(";
	}
//   Out << '&';

	// If the first index is 0 (very typical) we can do a number of
	// simplifications to clean up the code.
	Value *FirstOp = I.getOperand();
	if (!isa < Constant > (FirstOp)
		|| !cast < Constant > (FirstOp)->isNullValue()) {
		TRACE_4("/****  first index is not 0 ****/\n");
		// First index isn't simple, print it the hard way.
		writeOperand(Ptr);
	} else {
		++I;		// Skip the zero index.

		TRACE_4("/****  first index is 0 ****/\n");

		// Okay, emit the first operand. If Ptr is something that is already address
		// exposed, like a global, avoid emitting (&foo)[0], just emit foo instead.
		if (isAddressExposed(Ptr)) {
			TRACE_4("   /**** address is exposed ****/\n");
			writeOperandInternal(Ptr, Static);
		} else if (I != E && isa < StructType > (*I)) {
			TRACE_4("/**** struct type ****/\n");
			// If we didn't already emit the first operand, see if we can print it as
			// P->f instead of "P[0].f"
			writeOperand(Ptr);
			Out << ".field" << cast < ConstantInt >
				(I.getOperand())->getZExtValue();

//       Out << "->field" << cast<ConstantInt>(I.getOperand())->getZExtValue();
			++I;	// eat the struct index as well.
		} else {
			TRACE_4("/**** else case... ****/\n");

			// Instead of emitting P[0][1], emit (*P)[1], which is more idiomatic.
			Out << "(*";
			writeOperand(Ptr);
			Out << ")";
		}
	}

	for (; I != E; ++I) {
		if (isa < StructType > (*I)) {
			Out << ".field" << cast < ConstantInt >
				(I.getOperand())->getZExtValue();
		} else if (isa < ArrayType > (*I)) {
			Out << ".array[";
//       writeOperandWithCast(I.getOperand(), Instruction::GetElementPtr);
			writeOperand(I.getOperand(),
				Instruction::GetElementPtr);
			Out << ']';
		} else if (!isa < VectorType > (*I)) {
			Out << '[';
//       writeOperandWithCast(I.getOperand(), Instruction::GetElementPtr);
			writeOperand(I.getOperand(),
				Instruction::GetElementPtr);
			Out << ']';
		} else {
			// If the last index is into a vector, then print it out as "+j)".  This
			// works with the 'LastIndexIsVector' code above.
			if (isa < Constant > (I.getOperand()) &&
				cast < Constant >
				(I.getOperand())->isNullValue()) {
				Out << "))";	// avoid "+0".
			} else {
				Out << ")+(";
//         writeOperandWithCast(I.getOperand(), Instruction::GetElementPtr);
				writeOperand(I.getOperand(),
					Instruction::GetElementPtr);
				Out << "))";
			}
		}
	}
	Out << ")";
}

void PromelaWriter::writeMemoryAccess(Value * Operand,
				const Type * OperandType,
				bool IsVolatile, unsigned Alignment)
{
//   bool IsUnaligned = Alignment &&
//     Alignment < TD->getABITypeAlignment(OperandType);

//   if (!IsUnaligned)
//     Out << '*';
//   if (IsVolatile || IsUnaligned) {
//     Out << "((";
//     if (IsUnaligned)
//       Out << "struct __attribute__ ((packed, aligned(" << Alignment << "))) {";
//     printType(Out, OperandType, false, IsUnaligned ? "data" : "volatile*");
//     if (IsUnaligned) {
//       Out << "; } ";
//       if (IsVolatile) Out << "volatile ";
//       Out << "*";
//     }
//     Out << ")";
//   }

	writeOperand(Operand);
//   if (IsVolatile || IsUnaligned) {
//     Out << ')';
//     if (IsUnaligned)
//       Out << "->data";
//   }
}

void PromelaWriter::visitLoadInst(LoadInst & I)
{
	writeMemoryAccess(I.getOperand(0), I.getType(), I.isVolatile(),
			I.getAlignment());

}

void PromelaWriter::visitStoreInst(StoreInst & I)
{
	writeMemoryAccess(I.getPointerOperand(),
			I.getOperand(0)->getType(), I.isVolatile(),
			I.getAlignment());
	Out << " = /* visitStore */";
	Value *Operand = I.getOperand(0);
	Constant *BitMask = 0;
	if (const IntegerType * ITy =
		dyn_cast < IntegerType > (Operand->getType())) {
		if (!ITy->isPowerOf2ByteWidth()) {
			// We have a bit width that doesn't match an even power-of-2 byte
			// size. Consequently we must & the value with the type's bit mask
			BitMask = ConstantInt::get(ITy, ITy->getBitMask());
		}
	}
	if (BitMask)
		Out << "((";
	writeOperand(Operand);
	if (BitMask) {
		Out << ") & ";
		printConstant(BitMask, false);
		Out << ")";
	}
}

void PromelaWriter::visitGetElementPtrInst(GetElementPtrInst & I)
{
	printGEPExpression(I.getPointerOperand(), gep_type_begin(I), gep_type_end(I), false);
}

void PromelaWriter::visitVAArgInst(VAArgInst & I)
{
	Out << "va_arg(*(va_list*)";
	writeOperand(I.getOperand(0));
	Out << ", ";
	printType(Out, I.getType());
	Out << ");\n ";
}

void PromelaWriter::visitInsertElementInst(InsertElementInst & I)
{
	const Type *EltTy = I.getType()->getElementType();
	writeOperand(I.getOperand(0));
	Out << ";\n  ";
	Out << "((";
	printType(Out, PointerType::getUnqual(EltTy));
	Out << ")(&" << GetValueName(&I) << "))[";
	writeOperand(I.getOperand(2));
	Out << "] = (";
	writeOperand(I.getOperand(1));
	Out << ")";
}

void PromelaWriter::visitExtractElementInst(ExtractElementInst & I)
{
	// We know that our operand is not inlined.
	Out << "((";
	const Type *EltTy =
		cast < VectorType >
		(I.getOperand(0)->getType())->getElementType();
	printType(Out, PointerType::getUnqual(EltTy));
	Out << ")(&" << GetValueName(I.getOperand(0)) << "))[";
	writeOperand(I.getOperand(1));
	Out << "]";
}

void PromelaWriter::visitShuffleVectorInst(ShuffleVectorInst & SVI)
{
	Out << "(";
	printType(Out, SVI.getType());
	Out << "){ ";
	const VectorType *VT = SVI.getType();
	unsigned NumElts = VT->getNumElements();
	const Type *EltTy = VT->getElementType();

	for (unsigned i = 0; i != NumElts; ++i) {
		if (i)
			Out << ", ";
		int SrcVal = SVI.getMaskValue(i);
		if ((unsigned) SrcVal >= NumElts * 2) {
			Out << " 0/*undef*/ ";
		} else {
			Value *Op =
				SVI.getOperand((unsigned) SrcVal >= NumElts);
			if (isa < Instruction > (Op)) {
				// Do an extractelement of this value from the appropriate input.
				Out << "((";
				printType(Out,
					PointerType::getUnqual(EltTy));
				Out << ")(&" << GetValueName(Op)
				    << "))[" << (SrcVal & (NumElts - 1)) <<
					"]";
			} else if (isa < ConstantAggregateZero > (Op)
				|| isa < UndefValue > (Op)) {
				Out << "0";
			} else {
				printConstant(cast < ConstantVector >
					(Op)->
					getOperand(SrcVal &
						(NumElts - 1)),
					false);
			}
		}
	}
	Out << "}";
}

void PromelaWriter::visitInsertValueInst(InsertValueInst & IVI)
{
	// Start by copying the entire aggregate value into the result variable.
	writeOperand(IVI.getOperand(0));
	Out << ";\n  ";
	
	// Then do the insert to update the field.
	Out << GetValueName(&IVI);
	for (const unsigned *b = IVI.idx_begin(), *i = b, *e =
		     IVI.idx_end(); i != e; ++i) {
		const Type *IndexedTy =
			ExtractValueInst::getIndexedType(IVI.getOperand(0)->
							getType(), b, i + 1);
		if (isa < ArrayType > (IndexedTy))
			Out << ".array[" << *i << "]";
		else
			Out << ".field" << *i;
	}
	Out << " = /* insertvalue */";
	writeOperand(IVI.getOperand(1));
}

void PromelaWriter::visitExtractValueInst(ExtractValueInst & EVI)
{
	Out << "(";
	if (isa < UndefValue > (EVI.getOperand(0))) {
		Out << "(";
		printType(Out, EVI.getType());
		Out << ") 0/*UNDEF*/";
	} else {
		Out << GetValueName(EVI.getOperand(0));
		for (const unsigned *b = EVI.idx_begin(), *i = b, *e =
			     EVI.idx_end(); i != e; ++i) {
			const Type *IndexedTy =
				ExtractValueInst::getIndexedType(EVI.
								getOperand
								(0)->
								getType(), b,
								i + 1);
			if (isa < ArrayType > (IndexedTy))
				Out << ".array[" << *i << "]";
			else
				Out << ".field" << *i;
		}
	}
	Out << ")";
}



extern "C" void
LLVMInitializePromelaBackendTarget()
{ 
  // Register the target.
  RegisterTargetMachine<PromelaTargetMachine> X(ThePromelaBackendTarget);
}

/***************************************************************************
 ***************** Main functions ******************************************
 **************************************************************************/

bool PromelaWriter::runOnModule(Module & M)
{
	TD = new TargetData(&M);
	IL = new IntrinsicLowering(*TD);
	IL->AddPrototypes(M);

	// Ensure that all structure types have names...
	Mang = new Mangler(M);
	Mang->markCharUnacceptable('.');

	// Keep track of which functions are static ctors/dtors so they can have
	// an attribute added to their prototypes.
// 	std::set < Function * >StaticCtors, StaticDtors;
// 	for (Module::global_iterator I = M.global_begin(), E =
// 	     M.global_end(); I != E; ++I) {
// 		switch (getGlobalVariableClass(I)) {
// 		default:
// 			break;
// 		case GlobalCtors:
// 			FindStaticTors(I, StaticCtors);
// 			break;
// 		case GlobalDtors:
// 			FindStaticTors(I, StaticDtors);
// 			break;
// 		}
// 	}

// 	if (!M.global_empty()) {
// 		Out << "\n\n/* Global Variable Declarations */\n";
// 		for (Module::global_iterator I = M.global_begin(), E =
// 		     M.global_end(); I != E; ++I)
// 			if (!I->isDeclaration()) {
// 				// Ignore special globals, such as debug info.
// 				if (getGlobalVariableClass(I))
// 					continue;

// 				//           if (I->hasLocalLinkage())
// 				//             Out << "static ";
// 				//           else
// 				//             Out << "extern ";

// 				// Thread Local Storage
// 				if (I->isThreadLocal())
// 					Out << "__thread ";

// 				I->dump();
// // 				printType(Out,
// // 					  I->getType()->getElementType(),
// // 					  false, GetValueName(I));

// 				if (I->hasLinkOnceLinkage())
// 					Out << " __attribute__((common))";
// 				else if (I->hasCommonLinkage())	// FIXME is this right?
// 					Out << " __ATTRIBUTE_WEAK__";
// 				else if (I->hasWeakLinkage())
// 					Out << " __ATTRIBUTE_WEAK__";
// 				else if (I->hasExternalWeakLinkage())
// 					Out << " __EXTERNAL_WEAK__";
// 				if (I->hasHiddenVisibility())
// 					Out << " __HIDDEN__";
// 				Out << ";\n";
// 			}
// 	}
	/* Fill types table */
	printModuleTypes(M.getTypeSymbolTable());
	
	/* Print Global variables from the program */
	printGlobalVariables(Mang);
	
	/* Print all stuff relative to encoding */
	printPrimitives();

	/* Print all processes and functions */
	printProcesses();

	/* Print init section (launch processes */
	printInitSection();

	// Free memory...
	delete IL;
	delete TD;
	delete Mang;
	FPConstantMap.clear();
	TypeNames.clear();
	ByValParams.clear();
	intrinsicPrototypesAlreadyGenerated.clear();
	return false;

}

void PromelaWriter::getAnalysisUsage(AnalysisUsage & AU) const
{
	AU.addRequired < LoopInfo > ();
	AU.setPreservesAll();
}

const char *PromelaWriter::getPassName() const
{
	return "Promela backend";
}

char PromelaWriter::ID = 0;
