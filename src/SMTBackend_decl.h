#ifndef _SMTBACKEND_DECL_H
#define _SMTBACKEND_DECL_H

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

using namespace llvm;



class SMTBackend_decl : public InstVisitor<SMTBackend_decl> {
private:
	formatted_raw_ostream &Out;
	std::set<const Argument*> ByValParams;
	std::map<const Instruction*,std::string> * locals_name;
	/* map containing the informations of branchement of the basicblocks */
	std::multimap<std::string,std::string> * branchements;
	static int num_local;
	static int nstop, nwarn, nfail;
public:	
	
	/* constructor */
	SMTBackend_decl (formatted_raw_ostream &o,
			 std::map<const Instruction*,std::string> * Map,
			 std::multimap<std::string,std::string> * branch) :
	Out(o), locals_name(Map), branchements(branch) {}

	/* destructor */
	~SMTBackend_decl() {}

	const char *getPassName() const;
	/* void getAnalysisUsage(AnalysisUsage &AU) const; */
	bool runOnModule(Module &M);
	
	void printFunction(Function* F);

	void printBasicBlock(BasicBlock* blk);
	
	std::string GetValueName(const Value * Operand);
	std::string GetUserName(const User * Value);

	// Opcode Implementations
	void visitReturnInst(ReturnInst &I);
	void visitBranchInst(BranchInst &I);
	void visitSwitchInst(SwitchInst &I);
 
	void visitBinaryOperator(BinaryOperator &I);
	void visitICmpInst(ICmpInst &I);
	void visitFCmpInst(FCmpInst &I);
#if ALLOCATION_INST
	void visitAllocationInst(AllocationInst &I);
	void visitFreeInst(FreeInst &I);
#endif
	void visitLoadInst(LoadInst &I);
	void visitStoreInst(StoreInst &I);
	void visitGetElementPtrInst(GetElementPtrInst &I);
	void visitPHINode(PHINode &I);
	void visitTruncInst(TruncInst &I);
	void visitZExtInst(ZExtInst &I);
	void visitSExtInst(SExtInst &I);
	void visitFPTruncInst(FPTruncInst &I);
	void visitFPExtInst(FPExtInst &I);
	void visitUIToFPInst(UIToFPInst &I);
	void visitSIToFPInst(SIToFPInst &I);
	void visitFPToUIInst(FPToUIInst &I);
	void visitFPToSIInst(FPToSIInst &I);
	void visitPtrToIntInst(PtrToIntInst &I);
	void visitIntToPtrInst(IntToPtrInst &I);
	void visitBitCastInst(BitCastInst &I);
	void visitSelectInst(SelectInst &I);
  
	void visitCallSite(CallSite CS);
	void visitCallInst(CallInst &I) { visitCallSite (CallSite (&I)); }
	void visitInvokeInst(InvokeInst &I) { visitCallSite (CallSite (&I)); }
//	void visitUnwindInst(UnwindInst &I);
	void visitUnreachableInst(UnreachableInst &I);
 
	void visitShl(BinaryOperator &I);
	void visitLShr(BinaryOperator &I);
	void visitAShr(BinaryOperator &I);
 
	void visitVAArgInst(VAArgInst &I);
	void visitInstruction(Instruction &I) {
#if PRINT_INSTRUCTION
		std::cerr << I;
#endif
		assert(0 && "Instruction not interpretable yet!");
	}
};

#endif
