#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"


using namespace llvm;

namespace{
	struct Sample : public FunctionPass{
		static  char ID;
		Sample() : FunctionPass(ID) {}
		static unsigned int done;
		
		bool runOnFunction(Function &F){
			
			for(BasicBlock& B : F){
				
				for(Instruction& I : B){
					if(auto *op = dyn_cast<BinaryOperator>(&I)){
						IRBuilder<> builder(op);
						
						Value *lv = op->getOperand(0);
						Value *rv = op->getOperand(1);
						Value *mol = builder.CreateMul(lv,rv);
						
						for(auto &U: op->uses()){
							User *user = U.getUser();
							user->setOperand(U.getOperandNo(), mol);
						}
						op->dump();
						lv->dump();
						rv->dump();
						mol->dump();
						done = 1;
					}
				}
			}
		
		if(done)
			return true;
		F.dump();	
		return false;
		}
		
	
	};
	
}

char Sample::ID = 0;
unsigned int Sample::done = 0;

static void registerSamplePass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new Sample());
}
static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
registerSamplePass);

//static RegisterStandardPasses is a class, we declared an object of that class named
//RegisterMyPass.

//static RegisterPass<Sample> X("sample", "Sample Pass that substitutes xor with and");


