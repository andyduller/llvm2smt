#include <iostream>
#include <sstream>

#include "llvm/CallingConv.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Module.h"
#include "llvm/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
//#include "llvm/TypeSymbolTable.h"
#include "llvm/Intrinsics.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/InlineAsm.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/ConstantsScanner.h"
#include "llvm/Analysis/FindUsedTypes.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/IntrinsicLowering.h"
#include "llvm/Transforms/Scalar.h"
//#include "llvm/Target/TargetAsmInfo.h"
#include "llvm/Target/TargetData.h"
//#include "llvm/Target/TargetRegistry.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstVisitor.h"
//#include "llvm/Support/Mangler.h"
#include "llvm/Support/MathExtras.h"
//#include "llvm/System/Host.h"
#include "llvm/Config/config.h"

#include "SMTBackend_decl.h"

// #define COMMENT

using namespace llvm;
using namespace std;

int SMTBackend_decl::num_local = 0;
int SMTBackend_decl::nstop = 0;
int SMTBackend_decl::nwarn = 0;
int SMTBackend_decl::nfail = 0;

const char *SMTBackend_decl::getPassName() const {
	return "not implemented";
}

void SMTBackend_decl::printFunction(Function* F) {
	bool empty = true;
	for (Function::iterator i = F->begin(), e = F->end(); i != e; ++i) {
		Out << ":extrapreds ((" << i->getName() << "))\n";
		empty = false;
	}
	
	if (!empty) {
		branchements->insert(pair<string,string>("entry","true"));
		Out << "\n";
		for (Function::arg_iterator AI = F->arg_begin(),
			     AE = F->arg_end();
		     AI != AE;
		     ++AI) {
			Out << ":extrafuns (("
			    << AI->getName()
			    << " Int"
			    << "))\n";
		}
		
		Out << "\n";
		for (Function::iterator i = F->begin(), e = F->end();
		     i != e; ++i) {
			printBasicBlock(i);
		}
		Out << "\n";

		// creating predicates for stop, warn and fail
		for (int i=0; i < nstop; i++) {
			Out << ":extrapreds ((stop_"
			    << i
			    <<"))\n";
		}
		for (int i=0; i < nwarn; i++) {
			Out << ":extrapreds ((warn_"
			    << i
			    <<"))\n";
		}
		for (int i=0; i < nfail; i++) {
			Out << ":extrapreds ((fail_"
			    << i
			    <<"))\n";
		}
		Out << "\n\n";
	}
	
}

void SMTBackend_decl::printBasicBlock(BasicBlock* blk) {

	for (BasicBlock::iterator i = blk->begin(), e = blk->end();
	     i != e; ++i) {
		visit(*i);
	}
}



string GetConstantName_decl(const Constant * Value) {
	string Name;
	stringstream ss;
	
	if (const ConstantInt * Const = dyn_cast < ConstantInt > (Value)) {
		// Out << "This is a ConstantInt\n";
		uint64_t Val = Const->getLimitedValue();
		ss << Val;
		Name =  ss.str();
	}

	if (Name.empty()) {
		Name = "undef_Constant";
	}
	return Name;
}

string SMTBackend_decl::GetUserName(const User * Value) {

	string Name;
	stringstream ss;
	
	if (const Constant * Const = dyn_cast < Constant > (Value)) {
		return GetConstantName_decl(Const);
	}
	if (const Instruction * Inst = dyn_cast < Instruction > (Value)) {
		Name = (*locals_name)[Inst];
		if (Name.empty()) {
			Name = "undef_Instruction";
		}
	}
	if (Name.empty()) {
		Name = "undef_User";
	}
	return Name;
}

string SMTBackend_decl::GetValueName(const Value * Operand) {
	
        string Name = Operand->getName().str();

	if (const User * Const = dyn_cast < User > (Operand)) {
		return GetUserName(Const);
	}
	if (Name.empty()) {
		Name = "undef_Value";
	}	
	return Name;
	
}

// Opcode Implementations
void SMTBackend_decl::visitReturnInst(ReturnInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitReturnInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitBranchInst(BranchInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitBranchInst\n;; " << I << "\n";
#endif
	ostringstream oss;
	
	if (I.isConditional()) {
		oss << GetValueName(I.getCondition());
		
		branchements->insert(pair<string,string>(I.getSuccessor(0)->getName(),"(and "+(string)I.getParent()->getName()+" "+oss.str()+")"));
		branchements->insert(pair<string,string>(I.getSuccessor(1)->getName(),"(and "+(string)I.getParent()->getName()+" (not "+oss.str()+"))"));
			} else {
		branchements->insert(pair<string,string>(I.getSuccessor(0)->getName(),(string)I.getParent()->getName()));
	}
}

void SMTBackend_decl::visitSwitchInst(SwitchInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitSwitchInst\n;; " << I << "\n";
#endif
	string cond = GetValueName(I.getCondition());
	ostringstream ossdefault;

	ossdefault << "(and ";
	
	for (unsigned i=1;i<I.getNumCases();i++) {
		ostringstream oss;
		oss << "(and (= "
		    << cond << " "
		    << GetConstantName_decl(I.getCaseValue(i))
		    << ") "
		    << (string)I.getParent()->getName()
		    << ")";

		ossdefault << "(distinct "
			   <<  cond << " "
			   << GetConstantName_decl(I.getCaseValue(i))
			   << ") ";
		
		branchements->insert(pair<string,string>(I.getSuccessor(i)->getName(),oss.str()));
	}
	
	ossdefault << (string)I.getParent()->getName()
		   << ")";
	
	branchements->insert(pair<string,string>(I.getDefaultDest()->getName(),ossdefault.str()));
	
	
}

void SMTBackend_decl::visitBinaryOperator(BinaryOperator &I){
#ifdef COMMENT
	Out << ";; " << I << "\n"; 
#endif
	// this instruction creates a new local variable
	ostringstream oss;
	oss << "x_" << num_local;
	(*locals_name)[&I] = oss.str();
	num_local++;	

	switch (I.getOpcode()) {
	case Instruction::Add:
	case Instruction::FAdd:
	case Instruction::Sub:
	case Instruction::FSub:
	case Instruction::Mul:
	case Instruction::FMul:
	case Instruction::URem:
	case Instruction::SRem:
	case Instruction::FRem:
	case Instruction::UDiv:
	case Instruction::SDiv:
	case Instruction::FDiv:
		Out << ":extrafuns ((" << (*locals_name)[&I] << " Int))\n";
		break;
	case Instruction::And:
	case Instruction::Or:
	case Instruction::Xor:
		Out << ":extrapreds ((" << (*locals_name)[&I] << "))\n";
		break;
	case Instruction::Shl:
	case Instruction::LShr:
	case Instruction::AShr:
	case Instruction::BinaryOpsEnd:
		break;
	}	
}

void SMTBackend_decl::visitICmpInst(ICmpInst &I){
#ifdef COMMENT
	Out << ";; " << I << "\n";
#endif
	// this instruction creates a new local variable
	ostringstream oss;
	oss << "x_" << num_local;
	(*locals_name)[&I] = oss.str();
	num_local++;

	Out << ":extrapreds ((" << (*locals_name)[&I] << "))\n";
}

void SMTBackend_decl::visitFCmpInst(FCmpInst &I){
#ifdef COMMENT
	Out << ";; " << I << "\n";
#endif
	// this instruction creates a new local variable
	ostringstream oss;
	oss << "x_" << num_local;
	(*locals_name)[&I] = oss.str();
	num_local++;

	Out << ":extrapreds ((" << (*locals_name)[&I] << "))\n";
}

#if ALLOCATION_INST
void SMTBackend_decl::visitAllocationInst(AllocationInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitAllocationInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitFreeInst(FreeInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitFreeInst\n;; " << I << "\n";
#endif
}
#endif

void SMTBackend_decl::visitLoadInst(LoadInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitLoadInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitStoreInst(StoreInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitStoreInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitGetElementPtrInst(GetElementPtrInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitGetElementPtrInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitPHINode(PHINode &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitPHINode\n;; " << I << "\n";
#endif
	// this instruction creates a new local variable
	ostringstream oss;
	oss << "x_" << num_local;
	(*locals_name)[&I] = oss.str();
	num_local++;		
	
	Out << ":extrafuns ((" << (*locals_name)[&I] << " Int))\n";
}

void SMTBackend_decl::visitTruncInst(TruncInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitTruncInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitZExtInst(ZExtInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitZExtInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitSExtInst(SExtInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitSExtInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitFPTruncInst(FPTruncInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitFPTruncInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitFPExtInst(FPExtInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitFPExtInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitUIToFPInst(UIToFPInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitUIToFPInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitSIToFPInst(SIToFPInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitSIToFPInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitFPToUIInst(FPToUIInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitFPToUIInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitFPToSIInst(FPToSIInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitFPToSIInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitPtrToIntInst(PtrToIntInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitPtrToIntInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitIntToPtrInst(IntToPtrInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitIntToPtrInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitBitCastInst(BitCastInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitBitCastInst\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitSelectInst(SelectInst &I){
	// this instruction creates a new local variable
	ostringstream oss;
	oss << "x_" << num_local;
	(*locals_name)[&I] = oss.str();
	num_local++;	

	Out << ":extrafuns ((" << (*locals_name)[&I] << " Int))\n";
}
  
void SMTBackend_decl::visitCallSite(CallSite CS){
	ostringstream oss;
	Instruction* I = CS.getInstruction();

	std::string str2;
	raw_string_ostream oss2(str2);
	oss2 << *(CS.getCalledFunction());
	if (str2.compare(1,29,"declare void @verif_stop(...)") == 0) {
		// this is the stop function
		oss << "stop_" << nstop;
		(*locals_name)[I] = oss.str();
		nstop++;
		return;
	}
	if (str2.compare(1,29,"declare void @verif_warn(...)") == 0) {
		// this is the warn function
		oss << "warn_" << nwarn;
		(*locals_name)[I] = oss.str();
		nwarn++;
		return;
	}
	if (str2.compare(1,29,"declare void @verif_fail(...)") == 0) {
		// this is the fail function
		oss << "fail_" << nfail;
		(*locals_name)[I] = oss.str();
		nfail++;
		return;
	}
	
	oss << "ret_" << num_local;	

	// existing TypeID :
	// , FloatTyID, DoubleTyID, X86_FP80TyID,
	// FP128TyID, PPC_FP128TyID, LabelTyID, MetadataTyID,
	// IntegerTyID, FunctionTyID, StructTyID, UnionTyID,
	// ArrayTyID, PointerTyID, OpaqueTyID, VectorTyID,
	// NumTypeIDs, 
	
	switch (CS.getType()->getTypeID()) {
	case Type::VoidTyID:
		return;
	default:	
		(*locals_name)[I] = oss.str();
		num_local++;
		break;
	}
	Out << ":extrafuns ((" << (*locals_name)[I] << " Int))\n";
}

//void SMTBackend_decl::visitUnwindInst(UnwindInst &I){
//#ifdef COMMENT
//	Out << ";; NOT IMPLEMENTED : visitUnwindInst\n;; " << I << "\n";
//#endif
//}

void SMTBackend_decl::visitUnreachableInst(UnreachableInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitUnreachableInst\n;; " << I << "\n";
#endif
}
 
void SMTBackend_decl::visitShl(BinaryOperator &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitShl\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitLShr(BinaryOperator &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitLShr\n;; " << I << "\n";
#endif
}

void SMTBackend_decl::visitAShr(BinaryOperator &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitAShr\n;; " << I << "\n";
#endif
}
 
void SMTBackend_decl::visitVAArgInst(VAArgInst &I){
#ifdef COMMENT
	Out << ";; NOT IMPLEMENTED : visitVAArgInst\n;; " << I << "\n";
#endif
}

