
#include <list>
#include <llvm/Analysis/BasicAliasAnalysis.h>
#include <llvm/Analysis/PostDominators.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Attributes.h>
#include <map>
#include <queue>
#include <set>
#include <stack>
#include <string>

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"


#include "Util/Annotation/MetadataInfo.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "../../../../../SVF-project/SVF/include/WPA/WPAPass.h"
#include "../../../../../SVF-project/SVF/include/WPA/Andersen.h"

#include "llvm/Analysis/CFG.h"

//#include "../../Utils/SkelUtils/CallingDAE.cp

//#define LIBRARYNAME "FKernelPrefetch"
#define PRINTSTREAM errs() // raw_ostream

#define F_KERNEL_SUBSTR "__kernel__tm__"
#define FUNCTION_MARKING "TMFUNC_"
#define TX_MARKING "TXFUNC_"
#define ACCESS_MARKING "ACCESS_PHASE_"
#define ACCESS_MARKING_SIZE (13)
#define FUNCTION_MARKING_SIZE (7)
#define LOOP_MARKING "LOOPFUNC_"
#define CLONE_SUFFIX "_clone"
#define CLONE_SUFFIX_SIZE (6)
#define TERMINATORnoRet_MARKING "TERMINATOR_noRet_"
#define TERMINATORNOnoRet_MARKING "TERMINATOR_!noRet_"
#define TERMINATORnoRet_MARKING_SIZE (17)
#define TERMINATORNOnoRet_MARKING_SIZE (18)
#define EMPRYTRUE_MARKING "EMPRYTRUE__"
#define RECURSION_MARKING "RECURSION_"
#define RECURSION_MARKING_SIZE (10)

using namespace llvm;
using namespace std;
using namespace util;
enum PrefInsertResult { Inserted, BadDeps, IndirLimit, Redundant };
enum FollowRules {FollowMust, FollowMay, FollowPartial};
bool FP = false; //filter rule: struct pointers
bool LOOP_MODE = false;
AliasAnalysis *AA;
std::vector<AliasAnalysis * > AAV;
std::vector<LoopInfo * > LIV;
LoopInfo *LI;
WPAPass* svf;
Function * MomAP;
bool removeUnlist = true;
bool IsClone = true;
bool IsIP = false; // Inter-procedural analysis. Works for all cases: inlined and non-inlined version. We can not inline everything. So even for the inlined version there might be some cases where IP is helpfull
bool DeleteUnused = true;
bool wpa_available = false;
bool Inline = false;//Depth loops ignore - ignoring applying depth for loop functions
//Motivation for DLI: loop functions are expansive, so might be a good idea to prefetch everythign we can find inside loops
int Deep = 100;//it is a depth of a load chain to control amount of prefetches
bool  RuleAlias = false;// Should be may by default
bool TransAP = false; //transactional memory mode
bool DUPLAP = false; //duplicate of AP
llvm::Pass *PP;//pass Pointer
bool allocaAllowed = true;
bool oracleVersion = false;
std::map<Function*, std::set<Instruction*>>* GlobalInstructionMap;
std::vector<Function *> vectorOfFunctions;
std::vector<std::set<Instruction*> > *vectorOftoKeepLoadsSets;
std::vector<std::set<Instruction*> > *vectorOftoKeepStoresSets;
std::vector<std::set<Instruction*> > *vectorOftoKeepFuncSets;
std::vector<std::set<Instruction*> > *vectorOftoKeepTerminatorsSets;
std::vector<std::set<Instruction*> > *vectorOftoKeepReturnsSets;
std::vector<std::set<Function*> > *vectorOfcalledFunctionsSets;
std::vector<std::list<LoadInst*> > *vectorOftoPrefLists;
std::vector<Instruction* > vectorOftempInst;
bool deleteUnusedBranches(Function *fun, bool val);
void replaceBranchIfMetadata(BasicBlock &block, bool val);

void anotateStores(Function &fun, list<LoadInst *> &toPref); 
void findStores(Function &F, list<StoreInst *> &StoreList); 
void findStores(Function &F, set<Instruction *> &StoreList); 
AliasResult crossCheck(StoreInst *store, list<LoadInst *> &toPref);
bool findAccessInsts(Function &, set<Instruction *> &,list<LoadInst *> &, bool val, Instruction * inst);
void printDiff(Function &fun, set<Instruction *> toKeep, set<Instruction *> toKeepPref);
void printDiff(Function *fun1, set<Instruction *>);
bool isFKernel(Function &);
Function *cloneFunction(Function *F);
void findLoads(Function &F, list<LoadInst *> &LoadList);
void findStoresToArgs(Function &F, set<Instruction *> &LoadList);
void findOracleLoads(Function &F, list<LoadInst *> &LoadList);
void findVisibleLoads(list<LoadInst *> &LoadList, list<LoadInst *> &VisList);
void findFPLoads(list<LoadInst *> &LoadList, list<LoadInst *> &VisList); 
void findTerminators(Function &F, set<Instruction *> &CfgSet);
void findReturns(Function &F, set<Instruction *> &CfgSet);
bool followDeps(set<Instruction *> &Set, set<Instruction *> &DepSet, vector<Function*> &FV);
bool findArgsInstr(Function &fun, set<Instruction *> &DepSet);
void followFuncDeps(set<Instruction *> &Set, set<Instruction *> &DepSet, bool noRet, vector<Function *>);
//void followFuncDepsWithTransformation(set<Instruction *> &Set, set<Instruction *> &DepSet, bool val, bool checkTerm = false);
bool TryAccessPhase(Instruction * I, set<Instruction *> &DepSet, queue<Instruction *> &Q, bool noRet);
bool TryAccessPhase_SVFDESIGN(Instruction * I, set<Instruction *> &DepSet, queue<Instruction *> &Q, bool noRet);
bool followDeps(Instruction *Inst, set<Instruction *> &DepSet, vector<Function *> &FV);
void enqueueOperands(Instruction *Inst, set<Instruction *> &Set,queue<Instruction *> &Q, bool, vector<Function*> &);
void enqueueInst(Value *Val, set<Instruction *> &Set,queue<Instruction *> &Q, bool);
void enqueueStores(Value *Pointer, Instruction * , Instruction *LInst, set<Instruction *> &Set,queue<Instruction *> &Q, int rule);
void enqueueStoresIP(Value* Pointer, Instruction *LInst, vector<Function *> &interproc_Func, set<Instruction *> &Set, queue<Instruction *> &Q, int rule, vector<Function *> &Seen, bool initial);
bool isLocalPointer(Value *Pointer);
bool isNonLocalPointer(Value *Pointer); 
AliasResult pointerAlias(Value *P1, Value *P2, const DataLayout &DL, bool);
void removeUnlisted(Function &F, set<Instruction *> &KeepSet);
bool isUnderThreshold(set<Instruction*> Deps);
PrefInsertResult insertPrefetch(LoadInst *LInst, set<Instruction *> &toKeep, map<LoadInst *, pair<CastInst *, CallInst *>> &prefs);
bool ExtractLoop(Loop *L, DominatorTree *DT, LoopInfo *);
BasicBlock *getCaller(Function *F);
void TransferPassResults(AliasAnalysis *, LoopInfo *, llvm::Pass*, WPAPass *, bool);
void TransferPassAttributes(bool AllocaNotAllowed, bool, bool, bool, bool, bool, bool, bool, bool, bool, vector<Function*> &, vector<std::set<Instruction*>> &,vector<std::set<Instruction*>> &, vector<std::set<Instruction*>> &,vector<std::set<Instruction*>> &, vector<std::set<Instruction *>> &, vector<std::list<LoadInst*>> &, std::vector<std::set<Function*>> &, bool FilterRuleFP);
bool formAccessPhaseRecursion(Function *, Instruction*, bool val);
int insertPrefetches(list<LoadInst *> &toPref, set<Instruction *> &toKeep,bool printRes = false, bool onlyPrintOnSuccess = false);
StringRef getFuncName(CallInst *);
void findFuncCalls(Function &, set<Instruction *> &);
//bool createAccessPhase = false;//If inside function there are no prefetches, but other access phases of functions, then notify formAccessPhaseRecirsively that this function should be prefetched
void insertAccessExecute(Function *, Function *, Instruction *);
void insertAtoAExtoEx(Function *, Function *, Function *);
void getControlDepsPreliminary(Function &f, set<Instruction *> &toKeep);
bool deleteDeadBlockIfMetadata(BasicBlock * dst);
void refineFuncCalls(set<Instruction*> &toKeep, set<Instruction *> &Deps);
void refineFuncCalls(set<Instruction*> &toKeep, set<Instruction *> &Deps, set<Instruction *> &toKeepA);
Function * findOriginal(Function *access);
bool solveRecursion(Function * access, Function * innerfunc);
std::string cleanFuncName(Function *access, bool naked = false);
Function * findAP(Function *access, bool noRet, bool * possible);
bool checkDepsRecursion(Instruction * I);
bool checkRecursionEggChickenProblem(Function *Dfunc, Function * Ofunc, vector<Function *> *);
void refineLoadsPrefs(set<Instruction *> toKeep, set<Instruction * > toKeepPref);
void RipAP(Function*);
bool createDUPLAPs(Function * AP);
void refineUnique(set<Instruction *> &toKeep, list<LoadInst *> &toPref);
void refineUnique(set<Instruction *> &toKeep, set<Instruction *> &toPref);
void CreateFuncChain(Function *fun, vector<Function *> &RelevantFunc_InterProc, vector<Function*> &InMomChecked);
bool PrePointerAnalysis(StoreInst * SInst, Instruction * LInst, Value * Pointer, set<Instruction *> &Set, queue<Instruction *> &Q);
bool checkTheInstructionInTheSet(Instruction * Inst);
void CleanFuncChain(Function * F, vector<Function* > RelevantFunc_InterProc);

Function * getFunction(CallInst * CI)
{
	if (Function * calledFunction = CI->getCalledFunction())
	{
		if (!calledFunction->isDeclaration() && !calledFunction->isIntrinsic())
		{
			return calledFunction;
		}
	}else
	{		
		if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
		{
			if (CstExpr->isCast())
			{
				// In this category we have call %1
				// I guess we also need to take care of it
				if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
				{
					if (!bitcastFunction->isDeclaration() && !bitcastFunction->isIntrinsic())
					{
						return bitcastFunction;
					}
				}
			}
		}
	}
	return nullptr;
}

void checkIfFuncEmpty(vector<std::set<Function *> > vectorCalledFunctions, vector<Function* > vectorFunc, vector<std::set<Instruction* >> vectorToKeepLoads, vector<std::set<Instruction* >> vectorToKeepStores, vector<std::list<LoadInst* >> vectorToPref, vector<Function *> &seen)
{
	outs() << "Check if it is empty\n";
	int iter = 0;
	for (Function * func: vectorFunc)
	{
		outs() << "called function " << func->getName().str() << "\n";
		if (std::find(seen.begin(), seen.end(), func) == seen.end())
		{
			seen.push_back(func);
		}else
		{
			outs() << "Seen\n";
			iter++;
			continue;
		}
		bool empty = true;
		outs() << "iter " << iter << "\n";
		outs() << "vectortoKeepLoads " << vectorToKeepLoads[iter].size() << "\n";
		outs() << "vectortoPref " << vectorToPref[iter].size() << "\n";
		outs() << "vectortoKeepStores " << vectorToKeepStores[iter].size() << "\n";
		if ((vectorToKeepLoads[iter].size() == 0) && (vectorToPref[iter].size() == 0) && (vectorToKeepStores[iter].size() == 0))
		{
			for (Function * f: vectorCalledFunctions[iter])
			{
				outs() << "called subfunction " << f->getName().str() << "\n";
				if (std::find(seen.begin(), seen.end(), f) == seen.end())
				{
					checkIfFuncEmpty(vectorCalledFunctions, vectorFunc, vectorToKeepLoads, vectorToKeepStores, vectorToPref, seen);
					if (f->getName().str().find("_EMPTYLOAD") == string::npos)
					{
						empty = false;
						break;
					}
				}else
				{
					outs() << "Seen\n";
					if (f->getName().str().find("_EMPTYLOAD") == string::npos)
					{
						empty = false;
						break;
					}
				}
			}
			if (empty)
			{
				if (func->getName().str().find("_EMPTYLOAD") == string::npos)
				{
        				std::string postfix = "_EMPTYLOAD";
					func->setName(Twine(func->getName().str() + postfix));
					outs() << "Make a function " << func->getName().str() << " empty\n";
				}

			}
		}
		else
		{
			outs() << "Not empty itself\n";
			iter++;
			continue;
		}
		iter++;
	}

}
bool IfFuncReturns(Function * f, vector<std::set<Function* >> VCFS, vector<Function*> VF, vector<Function* > Seen)
{
	int it = 0;
	Seen.push_back(f);
	for (set<Function *> SCF: VCFS)
	{
		for (Function * CF: SCF)
		{
			if (CF == f)
			{
				Function* func = VF[it];
				string funcName = func->getName().str();
				if (funcName.find("_RETURN") != string::npos)
				{
					return true;

				}else
				{
					if (std::find(Seen.begin(), Seen.end(), func) == Seen.end())
					{	
						if (IfFuncReturns(func, VCFS, VF, Seen))
						{
							return true;
						}
					}
				}
			}
		}
		it++;
	}
	return false;
}

void RipAP(Function *func, int total, int goal)
{
	outs() << "RIP starts\n";
	//The idea is to go backwards from the last instruction 
	//            \/  \/
	//             \  /
	//               .
	//And count a number of instructons on the current level
	//if func_number_of_instruction - RTS = SUM_of_instruction_till_this_level
	//We cut off an AP at this level
	//
	//BUt the first thing we need to do is to find last BBs
	//For that lets find DAE_endAccessPhase function call
	//
	bool flag = true;
	set<BasicBlock *> BBs;
	BBs.insert(&(func->getEntryBlock()));

	int delta = 0;
	set<BasicBlock * > NLBBs;//NextLevel
	set<BasicBlock * > SNLBBs;//SaveNextLevel
	while(flag)
	{
	
		for(auto &BB: BBs)
		{
			for (auto iter = BB->begin(); iter != BB->end(); iter++)
			{
				delta++;
			}
			//Instruction * TI = BB->getTerminator();
			for (auto it = succ_begin(BB), et = succ_end(BB); it != et; it++)
			{
				if (NLBBs.insert(*it).second)
				{
					SNLBBs.insert(*it);
				}
			}
		}
		outs() << "delta is " << delta << "\n";
		if ((delta > goal) || (SNLBBs.size() == 0))
		{
			//Our goal achived or everything crashed
			flag = false;
		}else
		{
			
			BBs = SNLBBs;
			SNLBBs.clear();
		}
	}	
	//Ok, at this point we have a set of "leave" BBs
	//But before make them real "leave" BBs
	//Let's check that they are far away enough from the beggining of the function
	
	//outs() << "Before inserting" << SNLBBs.size() <<"\n";
	for (auto &BB: BBs)	
	{
		Module *Mod = func->getParent();
		Instruction * inst = BB->getTerminator();
		FunctionType *FTy = FunctionType::get(llvm::Type::getVoidTy(Mod->getContext()), 0);
		IRBuilder<> builder(&*(func->begin()));
		builder.SetInsertPoint(inst);
		Constant *c = Mod->getOrInsertFunction("DAE_endAccessPhase", FTy);
		Function *marker_func = cast<Function>(c);
		marker_func->setCallingConv(CallingConv::C);
		builder.CreateCall(marker_func);
		builder.CreateRetVoid();
		
		BranchInst *TI = dyn_cast<BranchInst>(inst);
		SwitchInst *SI = dyn_cast<SwitchInst>(inst);
		if (TI)
		{
			for (unsigned int i = 0; i < TI->getNumSuccessors(); ++i)
			{
				BasicBlock *dst = TI->getSuccessor(i);
				//outs() << "For instruction " << *TI << "\n";
				dst->removePredecessor(BB);
			}
		}else if (SI)
		{
			for (unsigned int i = 0; i < SI->getNumSuccessors(); ++i)
			{
				BasicBlock *dst = SI->getSuccessor(i);
				//outs() << "For instruction " << *TI << "\n";
				dst->removePredecessor(BB);
			}

		}else
		{
			outs() << "Not For instruction " << *inst << "\n";
		}

		inst->eraseFromParent();
		//outs() << "We did something\n";
	}	
	//outs() << "After inserting\n";
	
}


void clear(std::queue<Instruction *> &q)
{
	std::queue<Instruction *> empty;
	std::swap(q, empty);
}

//can not delete bicast function for some reason
//decided to make them empty
//I use only in TM_DAE_integrated.cpp
void makeHelperFuncEmpty(Function *F)
{
	for (auto &BB: *F)
	{
		for (auto iter = BB.begin(); iter != BB.end();)
		{
			outs() << "i != e " << &*iter <<"\n";
			Instruction * I = &*iter;
			iter++;
			//Need to keep return instr
			//Otherwise compiler complains
			//I use this for helper functions, which contain a memory barrier 
			//I need to delete this barrier
			if (!isa<TerminatorInst>(I))
			{
				(&*I)->replaceAllUsesWith(UndefValue::get((&*I)->getType()));
				//outs() << "makeHelperFunctionEmpty: instruction is erased\n";
       				(&*I)->eraseFromParent();
			}

		}
	}
}

void deleteAccessPhase(Function *access)
{
	//outs() << "Deleting\n";
	//CallInst *I;
  	Value::user_iterator i = access->user_begin(), e = access->user_end();
  	while (i != e) {
		//outs() << "i != e " << *(*i) <<"\n";
		Instruction *Inst = dyn_cast<Instruction>(*i);	
		Inst->replaceAllUsesWith(UndefValue::get(Inst->getType()));
		//outs() << "deleteAccessPhase: instruction is erased\n";
       		Inst->eraseFromParent();
		
		/*Instruction *Inst = dyn_cast<Instruction>(*i);	
		outs() << "It is nor a bitcast"<< Inst->getOpcodeName() <<"\n";
    		if (isa<CallInst>(*i)) {
      			I = dyn_cast<CallInst>(*i);
			I->replaceAllUsesWith(UndefValue::get(I->getType()));
			outs() << "Function was erased\n";
        		I->eraseFromParent();
		}else if (!isa<CastInst>(*i))
		{
			//Instruction *Inst = dyn_cast<Instruction>(*i);	
			//outs() << "It is nor a bitcast"<< Inst->getOpcodeName() <<"\n";
      			//CastInst *BI = dyn_cast<CastInst>(*i);
			//BI->replaceAllUsesWith(UndefValue::get(BI->getType()));
			//outs() << "Function was erased\n";
        		//BI->eraseFromParent();

		}*/
		++i;
	}

}

void insertAccessExecute(Function *F, Function *cF, Instruction *inst) {
  	CallInst *I;
  	Value::user_iterator i = F->user_begin(), e = F->user_end();
  	while (i != e) {
    		if (isa<CallInst>(*i)) {
      			I = dyn_cast<CallInst>(*i);
      			CallInst *ci = dyn_cast<CallInst>(I->clone());
			//outs() << "setCalledF5\n";		
			I->setCalledFunction(cF);
			ci->insertBefore(inst);
			//I->replaceAllUsesWith(ci);
		}
		++i;
	}
}

void insertAtoAExtoEx(Function *access, Function *execute, Function *accessParent) {
  	CallInst *I;
  	BasicBlock *BB;
  	Value::user_iterator i = access->user_begin();
  	while (i != access->user_end()) {
		//outs() << "User\n";
    		if (CallInst *I =dyn_cast<CallInst>(*i)) {
			if (I->getParent()->getParent() != accessParent)
			{
				I->setCalledFunction(execute);
				i = access->user_begin();
			}else
			{
				++i;
			}
		}else
		{			
			++i;
		}
	}
}

void insertDUPLAPs(Function *access, Function *execute, Instruction *  I)
{
	auto &functionList = access->getParent()->getFunctionList();
	for (auto &function: functionList)
	{
		for (auto & bb: function)
		{
			for (auto &instruction: bb)
			{
				if (CallInst * CI = dyn_cast<CallInst>(&instruction))
				{
					if (Function * calledFunction = CI->getCalledFunction())
					{
						if (calledFunction == access && &instruction != I)
						{
							CI->setCalledFunction(execute);
						}
					}else
					{		
						if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
						{
							if (CstExpr->isCast())
							{
								// In this category we have call %1
								// I guess we also need to take care of it
								if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
								{
									if (bitcastFunction == access && &instruction != I)
									{
										CI->setCalledFunction(execute);
									}

								}
							}
						}
					}
				}
			}
		}
	}
}
bool CreateDUPLas_core(Function* AP, Function *access, CallInst * CI)
{
	string funName = access->getName().str();
	bool sanity_check = false;
	if ((funName.find(CLONE_SUFFIX) != string::npos))
	{
		string cleaned_name = cleanFuncName(access, false);
		//outs() << "Cleaned name is " << cleaned_name << "\n";
		for (Module::iterator MI = AP->getParent()->begin();MI != AP->getParent()->end();++MI)
		{
			if ((*MI).isIntrinsic() || (*MI).empty())
				continue;
			string funcName = (*MI).getName().str();
			if (funcName.find(cleaned_name) != string::npos && funcName.find(CLONE_SUFFIX) == string::npos)
			{
				if ((*MI).getReturnType() == access->getReturnType() && (*MI).arg_size() == access->arg_size())
				{
					CI->setCalledFunction(&*MI);
					//outs() << "CLONE replaced\n";
					sanity_check = true;
					break;
				}
			}
				
		}
		if (!sanity_check)
		{
			outs() << "PANIK: error for a function" << access->getName().str()<< "\n";
			return false;
		}
		//sanity_check = false;	
	}else
	if ((funName.find(FUNCTION_MARKING) != string::npos) || (funName.find(LOOP_MARKING) != string::npos))
	{
		//outs() << "New clone created\n";
        	Function *execute = cloneFunction(access);
		//insertAtoAExtoEx(access, execute, AP);
		insertDUPLAPs(access, execute, cast<Instruction>(CI));
		if (funName.find(FUNCTION_MARKING) != string::npos)
		{
            		access->removeFnAttr(Attribute::NoInline);
        		access->addFnAttr(Attribute::AlwaysInline);
		}else if (funName.find(LOOP_MARKING) != string::npos)
		{
            		access->removeFnAttr(Attribute::AlwaysInline);
        		access->addFnAttr(Attribute::NoInline);

		}
		if(!createDUPLAPs(access))
		{
			return false;
		}
	}
}
bool createDUPLAPs(Function * AP)
{
	for (inst_iterator I = inst_begin(AP); I != inst_end(AP); I++)
	{
		if (CallInst *CI = dyn_cast<CallInst>(&*I))
		{
			Function *access = CI->getCalledFunction();
			if (access == NULL)//mightbe bitcast here
			{	
				if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
				{
					if (CstExpr->isCast())
					{
						// In this category we have call %1
						// I guess we also need to take care of it
						if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
						{
							if (bitcastFunction == NULL)
							{
								return false;
							}else
							{
								access = bitcastFunction;
							}
						}
					}
				}
			}

			if (access != NULL && !access->isIntrinsic() && !access->isDeclaration())
			{
				/*for (auto it = access->arg_begin(); it != access->arg_end(); it++)
				{
					outs() << "onit << "\n";
					if (Value * val_bitcast = dyn_cast<Value>(*&it))
					{
						Value * val = val_bitcast->stripPointerCasts();
						outs() << "CreateDUPs: " << *val << "\n";
					}
				}*/
				//string funName = access->getName().str();
				//outs() << "Good function name is " << funName << "\n";
				//if ((funName.find("_avlnew") != string::npos))
				//{
					//outs() << "CreateDUPs: " << *CI << "\n";
				for (unsigned i = 0; i < CI->getNumArgOperands(); ++i)
				{
					Value *val = CI->getArgOperand(i);
					if (!isa<Instruction>(val))
					{
						val = val->stripPointerCasts();	
					}
						//outs() << "Val: " << *val << "\n";
					if (Function* FUF = dyn_cast<Function>(val))
					{
								//outs() << "CreateDUPs: FUNC: " << *val << "\n";
							//CreateDUPLas_core(AP, FUF, CI);
					}
				}

				CreateDUPLas_core(AP, access, CI);
			}
		}
	}
	return true;
}

bool formAccessPhaseRecursion(Function *fI, Instruction *Inst, bool noRet)
{
	//if (IsClone)
	//{
        	BasicAAResult BAR(createLegacyPMBasicAAResult(*PP, *fI));
        	AAResults AAR(createLegacyPMAAResults(*PP, *fI, BAR));
        	AliasAnalysis *AAT = &AAR;
		AAV.push_back(AAT);
	//}


        Function *access = fI; // the original
	set<Instruction *> OriginalSet;
	int num = 0;
	/*for (inst_iterator I = inst_begin(access); I != inst_end(access); ++I)
	{
		OriginalSet.insert(&*I);
		num++;
	}*/
	//outs() << "##########################################################################\n";
	//outs() << "BEFORE: Number of static instructions inside " << access->getName().str() << " is " << num<< "\n";
	//outs() << "##########################################################################\n";
	Function * execute;
	if (IsClone)
	{
		#ifdef DEBUGE
		outs() << "Clone the function " << access->getName().str() << "\n";
		#endif
        	execute = cloneFunction(access);
        	//execute->removeFnAttr(Attribute::NoInline);
        	//execute->addFnAttr(Attribute::AlwaysInline);
		insertAtoAExtoEx(access, execute, Inst->getParent()->getParent());
	}
        std::list<LoadInst *> toPref;   // LoadInsts to prefetch
        std::set<Instruction *> toKeep; // Instructions to keep
	bool res = findAccessInsts(*access, toKeep, toPref, noRet, Inst);
	if (!res && IsClone)
	{

		//outs() << "No pref and no func\n";
		string _name = access->getName().str();
		std::size_t found = _name.find(TERMINATORnoRet_MARKING);
		if (found != std::string::npos)
		{
			execute->setName(Twine(TERMINATORnoRet_MARKING + execute->getName().str()));
		}
		found = _name.find(TERMINATORNOnoRet_MARKING);
		if (found != std::string::npos)
		{
			execute->setName(Twine(TERMINATORNOnoRet_MARKING + execute->getName().str()));
		}
		
		AAV.pop_back();
	  	return false;
	}else
	if (!res)
	{
		AAV.pop_back();
	}
	if (toPref.size() > 0 && !IsIP && removeUnlist) {
          	// insert prefetches
		#ifdef DEBUGE
	   	outs() << "INSERT PREFETCH\n";
		#endif
          	int prefs = insertPrefetches(toPref, toKeep, true);
	}
	if (removeUnlist && !IsIP)//IP needs to keep all instructions till the end 
	{
		removeUnlisted(*access, toKeep);
	}else if (IsIP && !IsClone)//IsClone is about SVFDESIGN
	{
		//Where we do not clone at all
		//But do inter-procedural analysis
		//
		//I think we processed everything till this point
		//But I might be wrong
	}
	num =0;
	/*for (inst_iterator I = inst_begin(access); I != inst_end(access); ++I)
	{
		num++;
	}*/
	//outs() << "##########################################################################\n";
	//outs() << "AFTER: Number of static instructions inside " << access->getName().str() << " is " << num<< "\n";
	//outs() << "##########################################################################\n";
	/*if (DepthLoopIgn)
	{
        	access->removeFnAttr(Attribute::AlwaysInline);
        	access->addFnAttr(Attribute::NoInline);
	}*/
        std::string prefix = noRet ? ACCESS_MARKING + (string)"_TRUE_": ACCESS_MARKING + (string)"_FALSE_";
	access->setName(Twine(prefix + access->getName().str()));
	
	//Means that in this function has recursion
	//now find all function recursive function calls(they were not replaced to an appropriate access phase)
	// and replace them
	if (access->getName().find(RECURSION_MARKING) != string::npos && IsClone)
	{
		outs() << "SOLVE RECURSION STARTS\n";	
		if(!solveRecursion(access, access))
		{
			if (IsClone)
			{
				AAV.pop_back();
			}
			return false;
		}
		outs() << "SOLVE RECURSION STARTS\n";	
	}	

	//outs() << "\n ULTIMATELY " << access->getName().str() << "\n\n";
	//if (IsClone)
	//{
		AAV.pop_back();
	//}
        // - Inlining of the A phase.
        // - This is questionable if statement
        if (Inline)
	{
        	access->removeFnAttr(Attribute::NoInline);
        	access->addFnAttr(Attribute::AlwaysInline);
	}
	printDiff(access, OriginalSet);
	return true;
}

bool solveRecursion(Function * access, Function * innerfunc)
{
	outs() << "solveRecursion for " << access->getName().str() << " but inside " << innerfunc->getName().str() << "\n";
	for (inst_iterator i = inst_begin(innerfunc);;)
	{
		if (i == inst_end(innerfunc))
			break;
		Instruction * I = &*i;
		++i;
		if (CallInst * CI = dyn_cast<CallInst>(I))
		{
			outs() << "Instr " << *CI << "\n";
			if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
			{
				if (CstExpr->isCast())
				{
					continue;
				}
			}

			//Check for declarations 
			//and call %1, assume they can not be recursion calls
			else if (CI->getCalledFunction() != NULL)
			{
				if (CI->getCalledFunction()->isDeclaration())
				{
					continue;
				}
			}else
			{
				continue;
			}
			//if (CI->getCalledFunction()->getName().find(CLONE_SUFFIX) != string::npos && CI->getCalledFunction()->getName().find(ACCESS_MARKING)  == string::npos && CI->getCalledFunction()->getName().find(TERMINATORnoRet_MARKING) == string::npos && CI->getCalledFunction()->getName().find(TERMINATORNOnoRet_MARKING) == string::npos)
			if (CI->getCalledFunction()->getName().find(CLONE_SUFFIX) != string::npos && CI->getCalledFunction()->getName().find(ACCESS_MARKING) == string::npos)
			{
				if (Value * v = dyn_cast<Value>(I))
				{
					bool noRet = true;
					//Means it is dependent function
					if (v->user_begin() != v->user_end())
					//if (v->getNumUses() != 0)
					{
						outs() << "noRet is false for a function " << CI->getCalledFunction()->getName().str()<< "\n";
						noRet = false;
					}
					bool possible = false;
					//Try to find an AP
					Function * AP = findAP(CI->getCalledFunction(), noRet, &possible);
					//If found (it is already checked for the same number of arguments)
					//replace finction call with Ap
					if (AP)
					{
						//outs() << "set Called function to found AP\n";
						outs() << "setCalledF7\n";		
						CI->setCalledFunction(AP);
					}else{		
					//If AP is not found
					//it could be still possible to create a new one
					//So, try to do it
					//if (possible)
					//{
						/*Function * f = findOriginal(CI->getCalledFunction());
						if (f != nullptr)
						{*/

						//if an attempt failed
						//and it was an independent function(noRet = true) --> replace with an AP for recursion parent
						//if it was a dependent function(noRet = false) --> check dependencies, maybe you can get rid of them
						if(!possible || !formAccessPhaseRecursion(CI->getCalledFunction(), I, noRet))
						{
							if (noRet)
							{
								outs() << "noRet is true so we just replaced\n";
								Function * APR = findAP(CI->getCalledFunction(), !noRet, &possible);
								//If found (it is already checked for the same number of arguments)
								//replace finction call with Ap
								if (APR)
								{
									//outs() << "set Called function to found AP\n";
									outs() << "setCalledF8\n";		
									CI->setCalledFunction(APR);
								}else
								{
									//return false;
									outs() << "Almost Unresolved dependencie\n";
									outs() << "checkRecursion4 @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n";
									//if (!checkDepsRecursion(I))
									//{
										//Unresolved dependencies
										outs() << "Unresolved dependencies\n";
										return false;
									//}
									i = inst_begin(innerfunc);
								}	
								/*if(!possible || !formAccessPhaseRecursion(CI->getCalledFunction(), I, noRet))
								{
									return false;
								}*/
								
							}else
							{
								outs() << "Almost Unresolved dependencie\n";
								outs() << "checkRecursion3 @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n";
								//if (!checkDepsRecursion(I))
								//{
									//Unresolved dependencies
									outs() << "Unresolved dependencies\n";
									return false;
								//}
								i = inst_begin(innerfunc);
							}
						}
						outs() << "Success\n";
					}	

			}
			}else if (CI->getCalledFunction()->getName().find(RECURSION_MARKING) == string::npos)
			{
				outs() << "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n";
				if (!solveRecursion(access, CI->getCalledFunction()))
				{
					outs() << "checkRecursion1 @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n";
					//if (!checkDepsRecursion(I))
					//{
						return false;
					//}
					i = inst_begin(innerfunc);

				}
			}
		}		
	}
	return true;
}
bool checkDepsRecursion(Instruction * I)
{
	if (Value *v = dyn_cast<Value>(I))
	{
		//outs() << "Current inst for a user: " << *I << "\n";
		//outs() << "Num of uses " << v->getNumUses() << "\n";
		//for (Value::use_iterator i = v->user_begin();;++i)
		for (auto U: v->users())
		{
			//if (i == v->user_end())
			//	break;
			//bool increase = true;
			Instruction *vv = dyn_cast<Instruction>(U);
			//outs() << "Current user: " << *vv << " for " << *I << "\n";
			if (TerminatorInst * ti = dyn_cast<TerminatorInst>(vv))
			{
				//outs() << "Terminator  " << *ti << " for " << *I << "\n";
				if (ti->getParent()->getParent()->getReturnType()->isVoidTy())
				{
					outs() << "Terminator is VOID\n";
				}else {
					outs() << "Terminator is SOMETHING\n";	
				}
				outs() << "We are before\n";
				if (I->getParent()->getParent()->getName().find("_TRUE_") != std::string::npos || I->getParent()->getParent()->getName().find("_ONLYTRUE_") != std::string::npos)
				{
					outs() << "We are in\n";
					if (I->getParent()->getParent()->getReturnType()->isVoidTy())
					{
						IRBuilder<> Builder(vv);
						Builder.CreateRetVoid();
					}else
					{
						Value *val = Constant::getNullValue(I->getParent()->getParent()->getReturnType());
						IRBuilder<> builder(vv);
						builder.CreateRet(val);
					}
					vv->eraseFromParent();
					continue;

						
				}
				outs() << "We are out/ Return false\n";
				return false;
			}
			outs() << "checkRecursion2 @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n";
			if (!checkDepsRecursion(vv))
			{
				outs() << "Bed deps recurs " << *vv << " for " << *I << "\n";
				return false;
			}
		}
	}else
	{
		outs() << "Not a value  for " << *I << "\n";
		//Can I return true here?
		return false;
	}
	outs() << "Erased1 recurs" << *I << "\n";
	I->eraseFromParent();
	outs() << "Erased2 recurs\n";
	return true;
}
std::string cleanFuncName(Function *access, bool naked)
{
	//TODO: check what else can be found
	string subname = access->getName().str();
	std::size_t found = subname.find(CLONE_SUFFIX);
	while (found != std::string::npos)
	{
		subname.erase(subname.begin() + found, subname.end());
		found = subname.find(CLONE_SUFFIX);
	}
	found = subname.find(TERMINATORNOnoRet_MARKING);
	while (found != std::string::npos)
	{
		subname.erase(found, TERMINATORNOnoRet_MARKING_SIZE);
		found = subname.find(TERMINATORNOnoRet_MARKING);
	}
	found = subname.find(TERMINATORnoRet_MARKING);
	while (found != string::npos)
	{
		subname.erase(found, TERMINATORnoRet_MARKING_SIZE);
		found = subname.find(TERMINATORnoRet_MARKING);
	}
	found = subname.find(ACCESS_MARKING);
	while (found != string::npos)
	{
		subname.erase(found, ACCESS_MARKING_SIZE);
		found = subname.find(ACCESS_MARKING);
	}
	found = subname.find("_ONLYTRUE_");
	while (found != string::npos)
	{
		subname.erase(found, 10);
		found = subname.find("_ONLYTRUE_");
	}
	found = subname.find("_TRUE_");
	while (found != string::npos)
	{
		subname.erase(found, 6);
		found = subname.find("_TRUE_");
	}
	found = subname.find("_FALSE_");
	while (found != string::npos)
	{
		subname.erase(found, 7);
		found = subname.find("_FALSE_");
	}
	found = subname.find("_ARGUMENT");
	while (found != string::npos)
	{
		subname.erase(found, 9);
		found = subname.find("_ARGUMENT");
	}
	found = subname.find("_LOADS");
	while (found != string::npos)
	{
		subname.erase(found, 6);
		found = subname.find("_LOADS");
	}
	found = subname.find("_RETURN");
	while (found != string::npos)
	{
		subname.erase(found, 7);
		found = subname.find("_RETURN");
	}

	found = subname.find(RECURSION_MARKING);
	while (found != string::npos)
	{
		subname.erase(found, RECURSION_MARKING_SIZE);
		found = subname.find(RECURSION_MARKING);
	}
	if (naked)
	{
		found = subname.find(FUNCTION_MARKING);
		while (found != string::npos)
		{
			subname.erase(found, FUNCTION_MARKING_SIZE);
			found = subname.find(FUNCTION_MARKING);
		}
		/*found = subname.find(LOOP_MARKING);
		if (found != string::npos)
		{
			subname.erase(found, LOOP_MARKING_SIZE);
		}*/
	}
	//outs() << "clean name " << subname << "================================================================\n";

	return subname;

}
Function * findOriginal(Function *access)
{	
	std::string subname = cleanFuncName(access);
	Module * m = access->getParent();
	for (Module::iterator mi = m->begin(); mi != m->end(); ++mi)
	{
		if ((*mi).getName().find(subname) != string::npos && (*mi).getName().find(CLONE_SUFFIX) != string::npos)
		{
			if ((*mi).getReturnType() == access->getReturnType()&& (*mi).arg_size() == access->arg_size())
			{
    				for (Function::arg_iterator aI = access->arg_begin(), aE = access->arg_end(), acI = (*mi).arg_begin(), acE = (*mi).arg_end(); aI != aE; ++aI, ++acI)
				{
					if ((&*aI)->getType() != (&*acI)->getType())
					{
						break;
					}
					return &*mi;
				}
			}
		}
	}
	return nullptr;
}

Function * findAP(Function *access, bool noRet, bool * possible)
{	
	std::string subname = cleanFuncName(access);
	std::string  flag = noRet? "_TRUE_": "_FALSE";
	Module * m = access->getParent();
	for (Module::iterator mi = m->begin(); mi != m->end(); ++mi)
	{
		if ((*mi).getName().find(subname) != string::npos && ((*mi).getName().find(flag) != string::npos || ((*mi).getName().find("_ONLYTRUE_") != string::npos && noRet)))
		{
			if ((*mi).getReturnType() == access->getReturnType() && (*mi).arg_size() == access->arg_size())
			{
    				for (Function::arg_iterator aI = access->arg_begin(), aE = access->arg_end(), acI = (*mi).arg_begin(), acE = (*mi).arg_end(); aI != aE; ++aI, ++acI)
				{
					if ((&*aI)->getType() != (&*acI)->getType())
					{
						*possible = true;
						return nullptr;
					}
				} 
				//outs() << "AP Function was found" << (*mi).getName().str() << "\n";
				return &*mi;
			}
		}
		if ((*mi).getName().find(subname) != string::npos && ((noRet && (*mi).getName().find(TERMINATORnoRet_MARKING) != string::npos) || (!noRet && (*mi).getName().find(TERMINATORNOnoRet_MARKING) != string::npos)))
		{
			*possible = false;
			return nullptr;
		}
	}
	*possible = true;
	return nullptr;
}
//This function passes some calculated parameters from a parent pass to helper functions
void TransferPassResults(AliasAnalysis *TAA, LoopInfo*TLI, llvm::Pass * pp, WPAPass * wpa, bool wpa_av)
{
	PP = pp;
	AA = TAA;
	svf = wpa;
	wpa_available = wpa_av;
	AAV.push_back(AA);
	LI = TLI;
	LIV.push_back(LI);
	return;
}

void TransferPassAttributes(bool allocaNotAllowed, bool oracle, bool mustmaypart, bool tap, bool dli, bool dupl, bool remove, bool nodeleteunused, bool isSVFdesign, bool isInterProc, std::vector<Function*> &FV, std::vector<std::set<Instruction *>> &VIL,std::vector<std::set<Instruction *>> &VIF ,std::vector<std::set<Instruction *>> &VIT ,std::vector<std::set<Instruction *>> &VIR , std::vector<std::set<Instruction *>> &VIS, std::vector<std::list<LoadInst*>> &PI, vector<std::set<Function* >> &VF, bool FiltFP)
//std::map<Function*, std::set<Instruction*>> *mapOfInstructions)
{
	allocaAllowed = !allocaNotAllowed;
	oracleVersion = oracle;
	RuleAlias = mustmaypart;
	TransAP = tap;
	DUPLAP = dupl;
	//outs() << "depth is " << depth;
	/*if (depth != 0)
	{
		Deep = depth;
	}*/
	Inline = dli;
	//outs() << "DLI is " << dli;
	removeUnlist = !remove;
	DeleteUnused = !nodeleteunused;
	IsClone = !isSVFdesign;
	IsIP = isInterProc;
	vectorOfFunctions = FV;
	vectorOftoKeepLoadsSets = &VIL;
	vectorOftoKeepStoresSets = &VIS;
	vectorOftoKeepFuncSets = &VIF;
	vectorOftoKeepTerminatorsSets = &VIT;
	vectorOftoKeepReturnsSets = &VIR;
	vectorOftoPrefLists = &PI;
	vectorOfcalledFunctionsSets = &VF;
	FP = FiltFP;
	//GlobalInstructionMap = mapOfInstructions;
	
}

BasicBlock *getCaller(Function *F) {
  for (Value::user_iterator I = F->user_begin(), E = F->user_end(); I != E;
       ++I) {
    if (isa<CallInst>(*I) || isa<InvokeInst>(*I)) {
      Instruction *User = dyn_cast<Instruction>(*I);
      return User->getParent();
    }
  }
  return 0;
}
//This function extracts loop to a new function if is possible 
bool ExtractLoop(Loop *L, DominatorTree *DT, LoopInfo *LI)
{
	// If LoopSimplify form is not available, stay out of trouble.
  	if (!L->isLoopSimplifyForm()) {
    		return false;
  	}	
	bool Changed = false;
	bool ShouldExtractLoop = false;
	// Extract the loop if the entry block doesn't branch to the loop header.
  	TerminatorInst *EntryTI =
      		L->getHeader()->getParent()->getEntryBlock().getTerminator();
  	if (!isa<BranchInst>(EntryTI) ||
      		!cast<BranchInst>(EntryTI)->isUnconditional() ||
      			EntryTI->getSuccessor(0) != L->getHeader()) {
    			ShouldExtractLoop = true;
  	} else {
    	// Check to see if any exits from the loop are more than just return
    	// blocks.
    		SmallVector<BasicBlock *, 8> ExitBlocks;
    		L->getExitBlocks(ExitBlocks);
    		for (unsigned i = 0, e = ExitBlocks.size(); i != e; ++i)
      		if (!isa<ReturnInst>(ExitBlocks[i]->getTerminator())) {
        		ShouldExtractLoop = true;
        		break;
      		}
  	}
	if (!ShouldExtractLoop) {
    		// Loop is already a function, it is actually not necessary to extract the
    		// loop.
    		//ShouldExtractLoop = true;
  	}	
  	if (ShouldExtractLoop) {
    		// We must omit landing pads. Landing pads must accompany the invoke
    		// instruction. But this would result in a loop in the extracted
    		// function. An infinite cycle occurs when it tries to extract that loop as
    		// well.
    		SmallVector<BasicBlock *, 8> ExitBlocks;
    		L->getExitBlocks(ExitBlocks);
    		for (unsigned i = 0, e = ExitBlocks.size(); i != e; ++i)
      			if (ExitBlocks[i]->isLandingPad()) {
        			ShouldExtractLoop = false;
        			break;
      			}
 	 }
	if (ShouldExtractLoop) {
		llvm::DominatorTree DTI = llvm::DominatorTree();
		DTI.recalculate(*(L->getHeader()->getParent()));

    		CodeExtractor Extractor(DTI, *L);
    		Function *nF = Extractor.extractCodeRegion();
    		if (nF != 0) {
			string funName = nF->getName().str();
			//outs() << "Extracted loop with a new name " << funName << "\n";
			std::size_t found = funName.find(FUNCTION_MARKING);
			while (found != std::string::npos)
			{
				funName.replace(found, FUNCTION_MARKING_SIZE, LOOP_MARKING);
		 		found = funName.find(FUNCTION_MARKING);
			}
			found = funName.find(TX_MARKING);
			while (found != std::string::npos)
			{
				funName.replace(found, FUNCTION_MARKING_SIZE, "");
		 		found = funName.find(TX_MARKING);
			}


			nF->setName(funName);
      			//BasicBlock *codeRepl = getCaller(nF);
      			//nF->addFnAttr(Attribute::AlwaysInline);
       		}
  	}

  	return Changed;

}

// Anotates stores in fun with the closest alias type to
// any of the loads in toPref. (To be clear alias analysis are
// performed between the address of each store and the address
// of each load.) Results are annotated as metadata.
void anotateStores(Function &fun, list<LoadInst *> &toPref) {
    list<StoreInst *> StoreList;
    findStores(fun, StoreList);
    for (list<StoreInst *>::iterator I = StoreList.begin(), E = StoreList.end();
         I != E; I++) {
      string aliasLevel;

	//outs() << "Cross checking\n";
      switch (crossCheck(*I, toPref)) {
      case AliasResult::NoAlias:
        aliasLevel = "NoAlias";
        break;
      case AliasResult::MayAlias:
        aliasLevel = "MayAlias";
        break;
      case AliasResult::PartialAlias:
        aliasLevel = "PartialAlias";
        break;
      case AliasResult::MustAlias:
        aliasLevel = "MustAlias";
        break;
      }
      AttachMetadata(*I, "GlobalAlias", aliasLevel);
    }
}
		
// Adds pointers to all StoreInsts in F to StoreList.
void findStores(Function &F, list<StoreInst *> &StoreList) {
	//bool flag = true;
	//auto &Args = F.getArgumentList();
	//outs() << "Look for stores\n";
    	for (inst_iterator iI = inst_begin(F), iE = inst_end(F); iI != iE; ++iI) {
    	  if (StoreInst::classof(&(*iI))) {
		/*Value * val = (&*iI)->getOperand(1);
		for (auto &Arg: Args)
		{
			if (auto *CPtr = dyn_cast<ConstantExpr>(&Arg))
			{
				if (val == &Arg)
				{
					flag = false;
					break;
				}
			}
		
		}
		if (flag)
		{*/
        		StoreList.push_back((StoreInst *)&(*iI));
		/*}else
		{
			flag = true;
		}*/
      	}
    	}
	//outs() << "Found all stores\n";
}

void findStores(Function &F, set<Instruction *> &StoreList) {
	//bool flag = true;
	//auto &Args = F.getArgumentList();
	//outs() << "Look for stores\n";
    	for (inst_iterator iI = inst_begin(F), iE = inst_end(F); iI != iE; ++iI) {
    	  if (StoreInst::classof(&(*iI))) {
		/*Value * val = (&*iI)->getOperand(1);
		for (auto &Arg: Args)
		{
			if (auto *CPtr = dyn_cast<ConstantExpr>(&Arg))
			{
				if (val == &Arg)
				{
					flag = false;
					break;
				}
			}
		
		}
		if (flag)
		{*/
        		StoreList.insert(&(*iI));
		/*}else
		{
			flag = true;
		}*/
      	}
    	}
	//outs() << "Found all stores\n";
}


  // Returns the closest alias between store and any of the LoadInsts
  // in toPref.
  AliasResult crossCheck(StoreInst *store, list<LoadInst *> &toPref) {
    AliasResult closest = AliasResult::NoAlias;
    Value *storePointer = store->getPointerOperand();
    for (list<LoadInst *>::iterator I = toPref.begin(), E = toPref.end();
         I != E && closest != AliasResult::MustAlias; ++I) {
      Value *loadPointer = (*I)->getPointerOperand();
	//false, because try to use both analysis
      switch (pointerAlias(storePointer, loadPointer,
                           (*I)->getModule()->getDataLayout(), false)) {
      case AliasResult::NoAlias:
        break; // Already default value.
      case AliasResult::MayAlias:
        if (closest == AliasResult::NoAlias) {
          closest = AliasResult::MayAlias;
        }
        break;
      case AliasResult::PartialAlias:
        if (closest == AliasResult::NoAlias ||
            closest == AliasResult::MayAlias) {
          closest = AliasResult::PartialAlias;
        }
        break;
      case AliasResult::MustAlias:
        closest = AliasResult::MustAlias; // Highest value.
        break;
      }
    }
    return closest;
  }

//For the example below:
//%1 = getelement
//%2 = load **%1
//%3 = cmp eq %2, null
//br = %3
//I decided to delete prefetches of loads 
//that are used by other instructions
void refineUnique(set<Instruction *> &toKeep, set<Instruction *> &toPref)
{
	//int p = 0;
	bool f = true;
	//outs() << "The size is " << toPref.size() << "\n";
    	set<Instruction *>::iterator IP = toPref.begin();
	while (IP != toPref.end())
	{
		//outs() << ++p<<"\n";
		for (set<Instruction *>::iterator  IK = toKeep.begin(); IK != toKeep.end(); ++IK)
		{
			if (*IK == *IP)
			{
				//outs() << "Delete\n";
				toPref.erase(*IP);
				IP = toPref.begin();
				f = false;
				//outs() << "The size is " << toPref.size() << "\n";
				break;
			}
		}
		if (f)
			++IP;
		f = true;
	}
	//Here let's also refine toKeep to avoid doing the same operations with 
	//the same instructions again and again	
	/*for (set<Instruction *>::iterator  IK = toKeep.begin(); IK != toKeep.end(); IK++)
	{
		for (set<Instruction *>::iterator AK = IK; AK != toKeep.end(); ++AK)
		{
			if (IK != AK && *IK == *AK)
			{
				outs() << "INstructions is deleted " << *AK << "\n";
				toKeep.erase(*AK);
			}
		}
	}*/
	/*outs() << "The size is " << toPref.size() << "\n";
	outs() << "Ola is " << p<<"\n";*/
}
void refineUnique(set<Instruction *> &toKeep, list<LoadInst *> &toPref)
{
	for (auto load: toKeep)
	{
		if (isa<LoadInst>(load))
		{
			//outs() << "Load: " << *load << "\n";
			list<LoadInst* >::iterator it = toPref.begin();
			while (it != toPref.end())
			{
				bool incr = true;
				Instruction * pref_instr = cast<Instruction>(*it);
				//outs() << "Pref: " << *pref_instr << "\n";
				if (load == pref_instr)
				{
					outs() << "PANIK ATTACK\n";
					toPref.erase(it);
					it = toPref.begin();
					incr = false;
				}
				if (incr)
				{
					it++;
				}
			}
		}
	}


}
bool checkTheInstructionInTheSet(Instruction * inst)
{
	int iter = 0;
	Function * fun = inst->getParent()->getParent();
	//Check if it is in temporal arrays
	//Becuase if it is then we will not think these instructions are included
	//And will repeat the whle process for them
	//It is a recursion trap
	/*for (auto ii: vectorOftempInst)
	{
		if (ii == inst)
		{
			#ifdef DEBUG
			outs() << "IPINFO: The store is in temporal vectors!\n";
			#endif
			return true;
		}
	}*/
	for (Function *f: vectorOfFunctions)
	{
		#ifdef DEBUGE
		outs() << "IPINFO F1: " << f->getName().str() << " F2: " << fun->getName().str() << "\n";
		#endif
		//if (f->getName().str().find(fun->getName().str()) != string::npos)
		if (f == fun)
		{
			#ifdef DEBUGE
			outs() << "IPINFO: Got it!\n";
			#endif
			break;
		} 
		iter++;
	}
	if (iter == vectorOfFunctions.size())
	{
		outs() << "IPERROR: vectors of Functions are wrong for" << fun->getName().str() << "\n";
		return false;
	}
	else
	{
		//1.Check if it is alredy there 
		for (auto &I: (*vectorOftoKeepLoadsSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in KeepLoads!\n";
				#endif
				return true;
			}
		}
		for (auto &I: (*vectorOftoKeepFuncSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in keepFunc!\n";
				#endif
				return true;
			}
		}
		for (auto &I: (*vectorOftoKeepTerminatorsSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in KeepTerm!\n";
				#endif
				return true;
			}
		}
		for (auto &I: (*vectorOftoKeepReturnsSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in KeepReturns!\n";
				#endif
				return true;
			}
		}
		for (auto &I: (*vectorOftoKeepStoresSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in KeepStores!\n";
				#endif
				return true;
			}
		}
	}
	return false;

}
bool includeTheStoreIntoASet(StoreInst *SInst)
{
	int iter = 0;
	Function * fun = SInst->getParent()->getParent();
	Instruction * inst = cast<Instruction>(SInst);
	//Check if it is in temporal arrays
	//Becuase if it is then we will not think these instructions are included
	//And will repeat the whle process for them
	//It is a recursion trap
	for (auto ii: vectorOftempInst)
	{
		if (ii == inst)
		{
			#ifdef DEBUGE
			outs() << "IPINFO: The store is in temporal vectors!\n";
			#endif
			return true;
		}
	}
	for (Function *f: vectorOfFunctions)
	{
		#ifdef DEBUGE
		outs() << "IPINFO F1: " << f->getName().str() << " F2: " << fun->getName().str() << "\n";
		#endif
		if (f->getName().str().find(fun->getName().str()) != string::npos)
		{
			#ifdef DEBUGE
			outs() << "IPINFO: Got it!\n";
			#endif
			break;
		} 
		iter++;
	}
	if (iter == vectorOfFunctions.size())
	{
		outs() << "IPERROR: vectors of Functions are wrong for" << fun->getName().str() << "\n";
		return false;
	}
	else
	{
		//1.Check if it is alredy there 
		for (auto &I: (*vectorOftoKeepLoadsSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in KeepLoads!\n";
				#endif
				return true;
			}
		}
		for (auto &I: (*vectorOftoKeepFuncSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in keepFunc!\n";
				#endif
				return true;
			}
		}
		for (auto &I: (*vectorOftoKeepTerminatorsSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in KeepTerm!\n";
				#endif
				return true;
			}
		}
		for (auto &I: (*vectorOftoKeepReturnsSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in KeepReturns!\n";
				#endif
				return true;
			}
		}
		for (auto &I: (*vectorOftoKeepStoresSets)[iter])
		{
			if (inst == I)
			{
				//It is alredy there, do nothing
				#ifdef DEBUGE
				outs() << "IPINFO: The store is in KeepStores!\n";
				#endif
				return true;
			}
		}



		//2. If the store is not there
		//Find all its deps
		set<Instruction* > OneStore;	
		set<Instruction* > DepsForOneStore;	
		OneStore.insert(inst);
		bool res = false;
		vector<Function* > RelevantFunc_InterProc;
		vector<Function* > InMomChecked;
		//outs() << "Create chain: includeTheStore start --> " << *SInst<< "\n";
		CreateFuncChain(inst->getParent()->getParent(), RelevantFunc_InterProc, InMomChecked);
		//outs() << "Create chain: includeTheStore end\n";
		vectorOftempInst.push_back(inst);
		res = followDeps(OneStore, DepsForOneStore, RelevantFunc_InterProc);
		CleanFuncChain(inst->getParent()->getParent(), RelevantFunc_InterProc);
		if (!res)
		{
			//There are prohibited deps on the way
			outs() << "IPINFO: The store " << *SInst << " has prohibited deps!\n";
			return false;
		}else
		{
			//The store is perfectly fine
			//It is time to insert it with its deps into the found set
			#ifdef DEBUGE
			outs() << "IPINFO: The store " << *SInst << " has been included into KeepStores for "<< fun->getName().str() << "!\n";
			#endif
			(*vectorOftoKeepStoresSets)[iter].insert(DepsForOneStore.begin(), DepsForOneStore.end());
			(*vectorOftoKeepStoresSets)[iter].insert(inst);
		}
	}	

	
}

bool enqueueStoresFromOtherFunc(CallInst * CInst, Function * func, Instruction * LI, vector<Function *> Seen)
{
    Seen.push_back(func);
    //BasicBlock *loadBB = LInst->getParent();
    Value *Pointer = (cast<LoadInst>(LI))->getPointerOperand()->stripPointerCasts();
    /*if (Instruction *Inst = dyn_cast<Instruction>(Pointer))
    {
	outs() << "BITCAST, do something!\n";
    }*/
    //queue<BasicBlock *> BBQ;
    //set<BasicBlock *> BBSet;
    //BBQ.push(loadBB);
    bool first = true;
    bool found = false;

    //while (!BBQ.empty()) {
    //  BasicBlock *BB = BBQ.front();
    //  BBQ.pop();
    //found = false;
    Function::BasicBlockListType &BBL = func->getBasicBlockList();
    for(auto iter = BBL.rbegin(); iter != BBL.rend(); iter++) {
	for (auto &iI: *iter)
	{
		if (CallInst::classof(&iI))
		{
			CallInst *CI = dyn_cast<CallInst>(&iI);
			Function *fun = CI->getCalledFunction();
			if (fun == NULL)
			{
				if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
				{
					if (CstExpr->isCast())
					{
						// In this category we have call %1
						// I guess we also need to take care of it
						if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
						{
							if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
							{
								continue;
							}
							//outs() << "Prevet\n";
							//name = bitcastFunction->getName();
							//outs() << "Poka\n";
							fun = bitcastFunction;
							//bitcast_flag = true;
							//bitcast = true;
							//return false;
						}
					}
				}
			}

			StringRef funName = getFuncName(CI);
			if (funName != "inderect call")
			{
				if (!fun->isDeclaration())
				{
					#ifdef DEBUGE
					outs() << "IPINFO: function " << funName << " is inside function " << func->getName().str() <<  "!\n";
					#endif
					if (std::find(Seen.begin(), Seen.end(), fun) == Seen.end())
					{	
						enqueueStoresFromOtherFunc(CI, fun, LI, Seen);
					}
				}	
			}
		}
        
	   if (StoreInst::classof(&iI)) {
          	StoreInst *SInst = (StoreInst *)(&iI);
		#ifdef DEBUGE
		outs() << "StoreFromAnotherFunction " << *&iI << " pointer " << SInst->getPointerOperand() << " with " << *Pointer <<"\n";
		#endif
		if (SInst->getPointerOperand() == Pointer)
		{
			#ifdef DEBUGE
			outs() << "IPINFO: operands match!! " << *&iI << "\n";
			#endif
			includeTheStoreIntoASet(SInst);
			found = true;
			return true; 
		}else 
		{
			switch (pointerAlias((SInst->getPointerOperand())->stripPointerCasts(), Pointer->stripPointerCasts(),
                               	SInst->getModule()->getDataLayout(), true)) {
          			case AliasResult::NoAlias:
					#ifdef DEBUGE
					outs() << "IPINFO: NoAlias" << *&iI << " and " << *Pointer << "\n";
					outs() << "IPINFO: NoAlias" << *(SInst->getPointerOperand()) << " and " << *(Pointer->stripPointerCasts()) << "\n";
					#endif
           				break;
          			case AliasResult::MayAlias:
						#ifdef DEBUGE
						outs() << "IPINFO: They do alias with may" << *&iI << " and " << *Pointer << " \n";
						#endif
					if (RuleAlias)
					{
						includeTheStoreIntoASet(SInst);
					}
					break;
          			case AliasResult::PartialAlias:
						#ifdef DEBUGE
						outs() << "IPINFO: They do alias with part" << *&iI << " and " << *Pointer << " \n";
						#endif
					if (RuleAlias)
					{
						includeTheStoreIntoASet(SInst);
					}
					break;
				default:
					#ifdef DEBUGE
					outs() << "IPINFO: They do alias with must" << *&iI << " and " << *Pointer << " \n";
					#endif
					//Here we need to include the store into an associated set
					//with all its dependencies
					//So,
					//1. find a set
					//2. check if the store is already there
					//3. if yes, then do nothing
					//4. if no, then get dependencies and include the store with all dependencies into the right set
					includeTheStoreIntoASet(SInst);
					//found = true;
					return true; 
				}
		}


	}else if (Pointer == &(iI)) {
	//Calrify it
	  #ifdef DEBUGE
	  outs() << "Stoped looking at " << *&iI << "\n"; 
	  #endif
          found = true;
	  return true; 
        }
      }//inst
     }//BB
}
bool checkIfAPinMomAP(Function* fun, vector<Function * > &Seen, vector<Function*> &InMomChecked)
{
	#ifdef DEBUGE
	outs() << "CheckIfMom for: " << fun->getName().str() << "\n";
	#endif
	int iter = 0;
	if (fun == MomAP)
	{
		#ifdef DEBUGE
		outs() << "Function " << (vectorOfFunctions[iter])->getName().str() << " is MomAP\n";
		#endif
		InMomChecked.push_back(vectorOfFunctions[iter]);
		Seen.push_back(vectorOfFunctions[iter]);
		return true;
	}
	if (std::find(InMomChecked.begin(), InMomChecked.end(), fun) != InMomChecked.end())
	{
		#ifdef DEBUGE
		outs() << "Function " << (vectorOfFunctions[iter])->getName().str() << " is inside MomAP\n";
		#endif
		InMomChecked.push_back(vectorOfFunctions[iter]);
		Seen.push_back(vectorOfFunctions[iter]);
		return true;
	}

	for (set<Function*> FuncSet: *vectorOfcalledFunctionsSets)
	{
		for (auto F: FuncSet)
		{
			if (F == fun)
			{
				if (std::find(InMomChecked.begin(), InMomChecked.end(), vectorOfFunctions[iter]) != InMomChecked.end())
				{
					#ifdef DEBUGE
					outs() << "Function " << (vectorOfFunctions[iter])->getName().str() << " is inside MomAP\n";
					#endif
					InMomChecked.push_back(vectorOfFunctions[iter]);
					Seen.push_back(vectorOfFunctions[iter]);
					return true;
				}

				#ifdef DEBUGE
				outs() << "Function " << (vectorOfFunctions[iter])->getName().str() << " is a candidate for being inside MomAP\n";
				#endif
				if ((vectorOfFunctions[iter])->getName().str().find(TX_MARKING) != string::npos)
				{
					#ifdef DEBUGE
					outs() << "Function has TX_MARKING\n";
					#endif
					//We found outter AP
					if (vectorOfFunctions[iter] == MomAP)
					{
						#ifdef DEBUGE
						outs() << "Function " << (vectorOfFunctions[iter])->getName().str() << " is MomAP\n";
						#endif
						Seen.push_back(vectorOfFunctions[iter]);
						InMomChecked.push_back(vectorOfFunctions[iter]);
						return true;
					}else
					{
						#ifdef DEBUGE
						outs() << "Function " << (vectorOfFunctions[iter])->getName().str() << " is not MomAP\n";
						#endif
						Seen.push_back(vectorOfFunctions[iter]);
						break;
					}
				}else if (find(Seen.begin(), Seen.end(), vectorOfFunctions[iter]) == Seen.end())
				{
						Seen.push_back(vectorOfFunctions[iter]);
						if (checkIfAPinMomAP(vectorOfFunctions[iter], Seen, InMomChecked))
						{
							#ifdef DEBUGE
							outs() << "Function " << (vectorOfFunctions[iter])->getName().str() << " is inside MomAP\n";
							#endif
							InMomChecked.push_back(vectorOfFunctions[iter]);
							Seen.push_back(vectorOfFunctions[iter]);
							return true;
						}else
						{
							#ifdef DEBUGE
							outs() << "Function " << (vectorOfFunctions[iter])->getName().str() << " is not inside MomAP\n";
							#endif
							Seen.push_back(vectorOfFunctions[iter]);
							break;

						}
				}else
				{
					#ifdef DEBUGE
					outs() << "Function has no TX_MARKING and has been seen\n";
					#endif
					break;
				}
			}
		}
		iter++;
	}
	#ifdef DEBUGE
	outs() << "Function " << fun->getName().str() << " is not MomAP\n";
	#endif
	Seen.push_back(fun);
	return false;



}
void CreateFuncChain (Function* fun, vector<Function*> & FuncChain, vector<Function* > &InMomChecked)
{
	//outs() << "Mom is " << MomAP->getName().str() << "\n";
	//How to create a function chain in the case above?
	//The chain should depend on an AP being processed. 
	//
	//In this loop we try to find functions the fun is called from
	//Example:
	//func1:
	//      call func2
	//      	call func4
	//      call func3
	//      	call func5
	//      	call fun
	//      	call func6
	//
	//The chain will contain: func3, func1
	StringRef Kind1 = "DAE-interproc-calledfrom";
	outs() << "CreateFuncChain: " << fun->getName().str() << "\n";
	StringRef Val1 = fun->getName().str();
	int iter = 0;
	vector<Function* > Seen;
	for (set<Function*> FuncSet: *vectorOfcalledFunctionsSets)
	{
		for (auto F: FuncSet)
		{
			if (F == fun)
			{
				//What if the following situation happens:
				//AP1:
				//	call func
				//
				//AP2:
				//	call func
				//
				//We store the current AP in MomAP variable
				//InMomChecked is for this purpose
				//checkIfAPinMomAP is for this purpose too
				#ifdef DEBUGE
				outs() << "The function is " << (vectorOfFunctions[iter])->getName().str() << "\n";
				#endif
				Seen.push_back(vectorOfFunctions[iter]);
				if (std::find(InMomChecked.begin(), InMomChecked.end(), vectorOfFunctions[iter]) != InMomChecked.end())
				{
					if (std::find(FuncChain.begin(), FuncChain.end(), vectorOfFunctions[iter]) == FuncChain.end())
					{
						#ifdef DEBUGE
						outs() << "The function is " << (vectorOfFunctions[iter])->getName().str() << "\n";
						#endif
						//vectorOfFunctions[iter]->addFnAttr(Kind1, Val1);
						//vectorOfFunctions[iter]->
						FuncChain.push_back(vectorOfFunctions[iter]);
						//InMomChecked.push_back(vectorOfFunctions[iter]);
						CreateFuncChain(vectorOfFunctions[iter], FuncChain, InMomChecked);
					}

					
				}else
				if (checkIfAPinMomAP(vectorOfFunctions[iter],Seen, InMomChecked))
				{
					if (std::find(FuncChain.begin(), FuncChain.end(), vectorOfFunctions[iter]) == FuncChain.end())
					{
						#ifdef DEBUGE
						outs() << "The function is " << (vectorOfFunctions[iter])->getName().str() << "\n";
						#endif
						//vectorOfFunctions[iter]->addFnAttr(Kind1, Val1);
						FuncChain.push_back(vectorOfFunctions[iter]);
						InMomChecked.push_back(vectorOfFunctions[iter]);
						CreateFuncChain(vectorOfFunctions[iter], FuncChain, InMomChecked);
					}
					Seen.clear();
					break;
				}
				Seen.clear();
			}
		}
		iter++;
	}
	#ifdef DEBUG
	//outs() << "Start\n";
	for (auto F: FuncChain)
	{
		outs() << "FuncChain: " << F->getName().str() << "\n";
	}
	#endif
	//however from the previous example we miss
	//func5(will be processed witt enqueueStoresIP)
	//func2, func4
	//With the following loop, we will try to find them
	//Please note, that func6 is not needed since it is after fun and there are no LOOPFUNC_
	//
	//Another example -> with loops:
	//LOOPFUNC_func1:
	//	call fun
	//	call func2
	//
	//In the case above, we need func2 and LOOPFUNC_func1
	vector<Function* > FuncChain_tail;
	for (Function * F: FuncChain)
	{
		llvm::DominatorTree DTI = llvm::DominatorTree();
		DTI.recalculate(*F);
		llvm::LoopInfo LI = LoopInfo();
		//llvm::PostDominatorTree PDTI = llvm::PostDominatorTree();
		//PDTI.runOnFunction(*F);
		iter = 0;
		for (Function * F1: vectorOfFunctions)
		{
			if (F1 == F)	
			{
				break;
			}
			iter++;
		}
		if (iter >= vectorOfFunctions.size())
		{
			outs() << "Error: can not find " << F->getName().str() << " inside vectorOfFunctions\n"; 
		}
		// if function is LOOPFUNC_ or it has an attribute that it is in a loop
		// then we include all functions from inside
		StringRef Kind = "DAE-interproc";
		if (F->getName().str().find(LOOP_MARKING) != string::npos || F->hasFnAttribute(Kind) || F->getName().str().find(RECURSION_MARKING) != string::npos)
		{
			for (Function * func: (*vectorOfcalledFunctionsSets)[iter])
			{
			if (std::find(FuncChain.begin(), FuncChain.end(), func) == FuncChain.end())
			{
				if (std::find(FuncChain_tail.begin(), FuncChain_tail.end(), func) == FuncChain_tail.end())
				{
					FuncChain_tail.push_back(func);
				}
			}

			}
		}else // If a functions does not repetetive than
			//we need only functions that are above the fun
			//above means that there is a path from a BB where our function is
			//and a BB where another function is
		{
			//Let's say we have 
			//func:
			//	call func1
			//	call func2
			//		call fun
			//	call func3
			//
			//We need only func1 in addition to func2
			//So first we need to find func2 in FuncChain
			//Then we will find the corresponding instruction for this function and a BB
			//Then we will try to find out if there is a path between "call func2"
			//"call func1" and "call func3"
			for (auto F2: (*vectorOfcalledFunctionsSets)[iter])
			{
				for (auto F3: FuncChain)
				{
					if (F2 == F3)
					{
						//this is func2
						//there could be several func2
						//
						//Find out a corresponding call instruction
						CallInst * CI;
						for (auto ci: F3->users())
						{
							if (CallInst * cii = dyn_cast<CallInst>(ci))
							{
								if (cii->getParent()->getParent() == F)
								{
									CI = cii;
									for (auto F4: (*vectorOfcalledFunctionsSets)[iter])
									{
										if (std::find(FuncChain_tail.begin(), FuncChain_tail.end(), F4) == FuncChain_tail.end())
										{
											if (F4 != F3)
											{
												for (auto ci: F4->users())
												{
													if (CallInst * cii = dyn_cast<CallInst>(ci))
													{
														if (cii->getParent()->getParent() == F)//Meaning F4 and F3 are from the same function
														{
															//Now it is time to figure out
															//if there is a path between "call F4"(CI) and "call F3"(cii)
															Instruction * CII = dyn_cast<Instruction>(CI);
															Instruction * ciiI = dyn_cast<Instruction>(cii);
															#ifdef DEBUGE
															outs() << "Instruction1: " << *CII << "\n";
															outs() << "Instruction2: " << *ciiI << "\n";
															#endif
															if (isPotentiallyReachable(ciiI, CII, &DTI, nullptr))
															{
																FuncChain_tail.push_back(F4);
															}
														}
													}
												}
											}
										}
									}

								}
							}

						}
						
					}
				}
			}	
		}
	}
	for (auto F: FuncChain_tail)
	{
		if (find(FuncChain.begin(), FuncChain.end(), F) == FuncChain.end())
		{
			if (F != NULL)
			{
				FuncChain.push_back(F);
			}
		}
	}
	//FuncChain.insert(FuncChain.end(), FuncChain_tail.begin(), FuncChain_tail.end());
	if (find(FuncChain.begin(), FuncChain.end(), fun) == FuncChain.end())
	{
		if (fun != NULL)
		{
			//fun->addFnAttr(Kind1, Val1);
			FuncChain.push_back(fun);
		}
	}
	StringRef Kind = "DAE-interproc";
	outs() << "For function: " << fun->getName().str() << "\n";
	for (auto F : FuncChain)
	{
		if (F->hasFnAttribute(Kind))
		{
			outs() << "Loop-related: " << F->getName().str() << "\n";
		}else if (F->hasFnAttribute(Val1))
		{
			outs() << "Called from: " << F->getName().str() << "\n";
		}else
		{
			outs() << "Function chain: " << F->getName().str() << "\n";
		}
	}
	outs() << "The end\n";
		
}

void findStoresFromOtherFunc_GLOBAL(vector<Function*> &FuncChain, Function * fun)
{
	//FuncChain.push_back(fun);
	//CreateFuncChain(fun, FuncChain);
	StringRef Kind = "DAE-interproc";
	for (auto F : FuncChain)
	{
		if (F->hasFnAttribute(Kind))
		{
			outs() << "Loop-related: " << F->getName().str() << "\n";
		}else
		{
			outs() << "Function chain: " << F->getName().str() << "\n";
		}
		
		/*for (auto inst = F->inst_begin(); inst != F->inst_end(); inst++)
		{
			if (isa<StoreInst>(inst))
			{

			}
		}*/
	}
}

//The idea that we go back from an instruction 
//find all function calls on the same level 
//go inside and check all stores if they alias 
//If none of the loads alias with stores from other instructions
//we know that this step is redundant 
void findStoresFromOtherFunc(set<Instruction*> toKeepPref, Instruction *inst)
{
	Function * F = inst->getParent()->getParent();// find a parent function
	llvm::DominatorTree DTI = llvm::DominatorTree();
	DTI.recalculate(*F);
	//For situation:
	//alloca r1
	//func(r1)
	//load r1
	//do stuff with r
	BasicBlock *loadBB = inst->getParent();
    	queue<BasicBlock *> BBQ;
    	set<BasicBlock *> BBSet;
    	BBQ.push(loadBB);
    	bool first = true;
    	bool found = false;
    	while (!BBQ.empty()) {
     		BasicBlock *BB = BBQ.front();
      		BBQ.pop();
      	
		BasicBlock::reverse_iterator RI(inst->getIterator());
      		for (BasicBlock::reverse_iterator iI = first ? RI : BB->rbegin(), iE = BB->rend(); iI != iE; ++iI)
		{
			if (CallInst * CI = dyn_cast<CallInst>(&*iI))
			{
				if (DTI.dominates(&*iI, inst))
				{
					Function *fn = CI->getCalledFunction();
					if (fn != NULL)
					{
						if (fn->isDeclaration())
						{
							continue;
						}
						#ifdef DEBUGE
						outs() << "IPINFO: function " << fn->getName().str() << " will be processed\n";
						#endif
						for (auto I: toKeepPref)
						{
							#ifdef DEBUGE
							outs() << "The instruction from toKeepPref: " << *I << "\n";
							#endif
							vector<Function *> seen;
							if(enqueueStoresFromOtherFunc(CI,fn, I, seen))
							{
								found = true;
							}
						}
					}else
					if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
					{
						//What does it mean? Why is it bad when the first operand is const? Avoiding casts?
						//It is not actually correct, because of the following example
						//alloca %2
						//call bitcast %1(%2, %3) --> lets say this function modifies %2 and %3
						//reload %2
						//do stuff with %2
						if (CstExpr->isCast())
						{
							//FIXME: technically it is not correct anyway
							//if (fn = dyn_cast<Function>(CstExpr->getOperand(0)))
							if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
							{
								if (!bitcastFunction->isDeclaration() && !bitcastFunction->empty())
								{
									#ifdef DEBUGE
									outs() << "IPINFO: function " << bitcastFunction->getName().str() << " will be processed\n";
									#endif
									for (auto I: toKeepPref)
									{
										#ifdef DEBUGE
										outs() << "The instruction from toKeepPref: " << *I << "\n";
										#endif
										vector<Function*> seen;
										if (enqueueStoresFromOtherFunc(CI,bitcastFunction, I, seen))
										{
											found = true;
										}
									}
								}
							}
							continue;
						}
					}
				
				}
			}
		}
		if (!found)
		{
        		for (pred_iterator pI = pred_begin(BB), pE = pred_end(BB); pI != pE; ++pI) 
			{
          			if (BBSet.insert(*pI).second) 
				{
            				BBQ.push(*pI);
          			}
			}
        	}
      		first = false;
	}

}

bool findAccessInsts(Function &fun, set<Instruction *> &toKeep, list<LoadInst *> &toPref, bool noRet, Instruction * I) {
	if (I != NULL)
	{
		//outs() << "Instruction: " << *I << "\n";
	}else
	{
		MomAP = &fun;
	}
	if (&fun == NULL)
	{
		//outs() << "MYSTERY1: \n";
		return false;
	}
	//fun.dump();

	//return true;
	//fun.dump();
	/*outs() << "INFO find AccessInst:                   " << fun.getName().str() << " with " << noRet <<"\n";
	bool LOOP_MODE_HELPER_FLAG = false;
	if (fun.getName().str().find(LOOP_MARKING) != string::npos)
	{
		if (LOOP_MODE == false)
		{
			LOOP_MODE = true;
		}else
		{
			LOOP_MODE_HELPER_FLAG = true;//already in this mode
		}
	}*/
	vector<Function* > RelevantFunc_InterProc;
	vector<Function* > InMomChecked;
	//outs() << "Create chain: finAccessInst start\n";
	CreateFuncChain(&fun, RelevantFunc_InterProc, InMomChecked);
	/*for (auto F: RelevantFunc_InterProc)
	{
		outs() << "Function chain contains: " << F->getName().str() << "\n";
	}*/
	//outs() << "Create chain: finAccessInst end\n";
	//Andersensvf->releaseAndersenWaveDiff();
	//Andersensvf = AndersenWaveDiff::createAndersenWaveDiff(*CM);
	Type *rt = fun.getReturnType();
	/*int TempDeep = 0;
	if (DepthLoopIgn && fun.getName().str().find(LOOP_MARKING) != string::npos)
	{
		TempDeep = Deep;
		Deep = 100;
	}*/
	// Find instructions to keep
    	// Find return instructions
    	bool res = true;
	//outs() << "1\n";
	//set<Instruction *> toKeepReturns;
	//set<Instruction *> DepsReturns;
	//TODO: form it in a nice function
	//if (!TransAP && !noRet && !fun.getReturnType()->isVoidTy())
	/*{
		findReturns(fun, toKeepReturns);
		if (toKeepReturns.size() > 0)
		{
			res = followDeps(toKeepReturns, DepsReturns);
			if (!res)
			{
				toKeepReturns.clear();
				DepsReturns.clear();
				outs() << "Error: Return value has bad deps\n";
				//outs() << "INFO The end for finding AccessInst:                   " << fun.getName().str() << "\n";
				fun.setName(Twine(TERMINATORNOnoRet_MARKING + fun.getName().str()));
				//if (TempDeep != 0)
				//{
				//	Deep = TempDeep;
				//}
				return false;
			}
		}else
		{
			//if (TempDeep != 0)
			//{
			//	Deep = TempDeep;
			//}
			outs() << "Error: no returns\n";
			return false;
		}
	}*/
	#ifdef DEBUGE
	outs() << "2\n";
	#endif
    	list<LoadInst *> LoadList;
	if (!oracleVersion)
	{
    		findLoads(fun, LoadList);
		findVisibleLoads(LoadList, toPref);
		if (FP)
		{
    			list<LoadInst *> toPrefTemp;
    			findFPLoads(toPref, toPrefTemp);
			#ifdef DEBUGE
			outs() << "FPFILTER INFO: before " << toPref.size() << " after " << toPrefTemp.size() << "\n";
			#endif
			toPref.clear();
			for (LoadInst *I: toPrefTemp)
			{
				toPref.push_back(I);
			}
		}
	}else{
		outs() << "Find oracle prefs\n";
		findOracleLoads(fun, toPref);
	}
	//toPref.clear();
	#ifdef DEBUGE
	outs() << "2.1\n";
	#endif
	//if (LoadList.size() != 0)
	//outs() << "After refining it remained  " << LoadList.size() << " of oracle loads\n";
    	// anotate stores
    	//anotateStores(fun, toPref);
	set<Instruction *> toKeepPref(std::begin(toPref), std::end(toPref));
	#ifdef DEBUGE
	outs() << "2.1.1\n";
	#endif
    	set<Instruction *> Deps;
	if (toKeepPref.size() != 0)
	{
		#ifdef DEBUGE
		outs() << "2.3\n";
		#endif
		// Follow CFG dependencies
    		res = followDeps(toKeepPref, Deps, RelevantFunc_InterProc);
		#ifdef DEBUGE
		outs() << "2.2\n";
		#endif
	
		if (!res)
		{
			//outs() << "INFO:                   Loads error!\n";
			//outs() << "INFO: Function " << fun.getName().str() << ": prefetch dependency error\n";
			toPref.clear();
			toKeepPref.clear();
			Deps.clear();
			res = true;
		}
	}else
	{
		//outs() << "INFO: there are no prefetches and " << LoadList.size() <<"\n";
	}
	if (toKeepPref.size() != 0)
	{
		if (fun.getName().str().find("_LOADS") == string::npos)
		{
			fun.setName(Twine(fun.getName().str() + "_LOADS"));
		}
		getControlDepsPreliminary(fun, toKeepPref);
		
	}	
	
	if (I != NULL && IsIP)
	{
		#ifdef DEBUGE
		outs() << "IPFindStoresFromOtherFunc: start\n";
		outs() << "IPFindStoresFromOtherFunc: " << *I << "\n";
		#endif
		//findStoresFromOtherFunc(toKeepPref, I);//We need a list of loads from this function and also a call instruction that we know 
		//findStoresFromOtherFunc_GLOBAL(VF, &fun);//We need a list of loads from this function and also a call instruction that we know 
		#ifdef DEBUGE
		outs() << "IPFindStoresFromOtherFunc: end\n";
		#endif
		//where this function is called from
	}
	#ifdef DEBUGE
	outs() << "2.2\n";
	#endif

	//alloca arg1
	//func(*arg1) --> we are intereseted in all changes that happen inside the function with arg1, namely stores are interesting.
	//load arg1
	//do smth with arg1
	//
	//Another thing that we need store to arg1 only if we reuse this value. 
	//Wold be nice to check this deps
	//But for now lets go simple. If function has a pointer argument, lets keep store to this value, just to be safe.
	

	//FIXME: we do not need to do it here
	//but it is over safe
	set<Instruction *> toKeepStoresToArgs;
	set<Instruction *> DepsStoresToArgs;
	/*if (fun.getName().str().find(TX_MARKING) == string::npos)
	{
		findStoresToArgs(fun, toKeepStoresToArgs);
		#ifdef DEBUGE
		outs() << "2.3\n";
		#endif
		if (toKeepStoresToArgs.size() != 0)
		{
			#ifdef DEBUGE
			outs() << "Stores to ARgs are found\n";
			#endif

			//It would be nice to notify our followers if we can not keep stores
			//Before it worked, but I also discard much more.
			#ifdef DEBUGE
			outs() << "2.4\n";
			#endif
			res = followDeps(toKeepStoresToArgs, DepsStoresToArgs);
			#ifdef DEBUGE
			outs() << "2.5\n";
			#endif
			if (!res)
			{
				toKeepStoresToArgs.clear();
				DepsStoresToArgs.clear();
				res = true;
			}
		}
	}*/


	//if (toPref.size() != 0)
	//outs() << "After annotation it remained  " << toPref.size() << " of oracle loads\n";
		// I think we have the same logic inside findStoresToArgs
	// a little bit different, but similar
	/*set<Instruction *> toKeepArgsInstr;
	set<Instruction *> DepsArgs;
	findArgsInstr(fun, toKeepArgsInstr);	
	if (toKeepArgsInstr.size() > 0)
	{
		//refineUnique(Deps, toKeepCalls);
		followDeps(toKeepArgsInstr, DepsArgs);
		if (toKeepArgsInstr.size() == 0)
		{
			toKeepArgsInstr.clear();
			DepsArgs.clear();
		}


	}*/

	#ifdef DEBUGE
	outs() << "3Calls start\n";
	#endif
	//Update prefetch
	//Find Call inst to trasfer them in access phases
	set<Instruction *> toKeepCalls;
	set<Instruction *> DepsCalls;
	findFuncCalls(fun, toKeepCalls);
	//if any functions were found, process them
	if (toKeepCalls.size() > 0)
	{
		//refineUnique(Deps, toKeepCalls);
		followFuncDeps(toKeepCalls, DepsCalls, true, RelevantFunc_InterProc);
		if (toKeepCalls.size() == 0)
		{
			toKeepCalls.clear();
			DepsCalls.clear();
		}


	}
	/*set<Instruction *> FunchasLoads;
	for (auto inst:toKeepCalls)
	{
		Function * F = (cast<CallInst>(inst))->getCalledFunction();
		if (F == NULL)
		{
			if (auto *CstExpr = dyn_cast<ConstantExpr>((cast<CallInst>(inst))->getOperand(0)))
			{
				if (CstExpr->isCast())
				{
					// In this category we have call %1
					// I guess we also need to take care of it
					//outs() << "TryAccessPhase failed --> bitcast " << name << " and " << noRet << "\n";
					//return false;
					if (Function * bitcastFunction = dyn_cast<Function>(cast<CallInst>(inst)->getCalledValue()->stripPointerCasts()))
					{
						if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
						{
							//outs() << "Double fail\n";
							continue;
						}
						if ((bitcastFunction->getName().str().find("_LOADS") != string::npos))
						{	
							if (fun.getName().str().find("_LOADS") == string::npos)
							{
								fun.setName(Twine(fun.getName().str() + "_LOADS"));
							}
							FunchasLoads.insert(inst);
						}
					}
				}
			}

			
		}else
		if ((cast<CallInst>(inst))->getCalledFunction()->getName().str().find("_LOADS") != string::npos)
		{
			if (fun.getName().str().find("_LOADS") == string::npos)
			{
				fun.setName(Twine(fun.getName().str() + "_LOADS"));
			}
			FunchasLoads.insert(inst);
		}
	}
	getControlDepsPreliminary(fun, FunchasLoads);*/

	
	#ifdef DEBUGE
	outs() << "3Calls end\n";
	#endif
	//refineUnique(DepsCalls, toKeepCalls);
	//outs() << "4\n";
	//When all loads and functions were found
	//Lets find terminator instructions and there deps	
	toKeep.insert(Deps.begin(), Deps.end());
	//toKeep.insert(DepsArgs.begin(), DepsArgs.end());
	toKeep.insert(DepsStoresToArgs.begin(), DepsStoresToArgs.end());
	toKeep.insert(DepsCalls.begin(), DepsCalls.end());
	toKeep.insert(toKeepStoresToArgs.begin(), toKeepStoresToArgs.end());
	toKeep.insert(toKeepCalls.begin(), toKeepCalls.end());
	//toKeep.insert(toKeepArgsInstr.begin(), toKeepArgsInstr.end());
		
	//if there are no prefs and func calls
	//then no need to refine terminators if this functions is stand alone function (noRet=true) or
	//this function returns void
	/*if (toKeepPref.size() == 0 && toKeep.size() == 0 && (noRet || fun.getReturnType()->isVoidTy()))
	{	
		outs() << "INFO Empty as a lake in a desert " << fun.getName().str() <<"\n";
		//Delete all BB
		//Then create only one with return value
		//It is valid only with noRet=true, because in this case we don't care about return value
		//But we don't want to return false
		//because then there is a cloned function without any access phase function
		//it makes harder to deal with such function in TryAccessPhase function
		for (auto BB = fun.begin();;)
		{
			if (BB == fun.end())
				break;
			outs() << "BB is erased from parent\n";
			(&*BB)->eraseFromParent();
			BB = fun.begin();
		}
		BasicBlock * BN = BasicBlock::Create(getGlobalContext(), "exit_bb", &fun);
		if (fun.getReturnType()->isVoidTy())
		{
			IRBuilder<> builder(BN);
			builder.CreateRetVoid();
		}else
		{
			Value *val = Constant::getNullValue(fun.getReturnType());
			IRBuilder<> builder(BN);
			builder.CreateRet(val);
		}
		AttachMetadata(BN->getTerminator(), "CFGMust", "1");
		if (BN == &(BN->getParent()->getEntryBlock()))
		{
			AttachMetadata(BN->getTerminator(), "EntryBlock", "1");
		}
		toKeep.clear();
		toPref.clear();	
		for (auto &BB: fun)
		{
			//outs() << "1\n";
			for (auto &I: BB)
			{
				toKeep.insert(&I);
			}
		}*/
		/*if (TempDeep != 0)
		{
			Deep = TempDeep;
		}*/

		//return true;

	//}
	//Clean toKeep and toPref to keep only unique loads in each category
	//if load contains in toPref, delete it from toKeep
	//refineUnique(toKeep, toKeepPref);
	/*if (toPref.size() == 0)
		outs() << "No oracles after refining\n";*/
	//outs() << "5\n";
	
	/*for (auto I: toKeepPref)
	{
		outs() << " : " << *I << "\n";
	}
	for (auto I: toKeep)
	{
		outs() << " : " << *I << "\n";
	}*/
	//if there is anything usufull there
	//go through the hell of refinig terminators
	//if (!TransAP)
	//{
	/*for(auto I: toKeep)
	{
		outs() << "Instruction " << *I << "\n";
	}*/
	//if (DeleteUnused && (fun.getName().str().find(LOOP_MARKING) == string::npos))
	//
	//
	//
	//
	//
	//
	//TODO: maybe we can do it later
	/*if (fun.getReturnType()->isVoidTy() && (fun.getName().str().find(LOOP_MARKING) == string::npos))
	{
		//getControlDepsPreliminary(fun, toKeepPref);
		//outs() << "5.1\n";
		getControlDepsPreliminary(fun, toKeep);
		if (!deleteUnusedBranches(&fun, true))
		{
			outs() << "SDDESIGN: AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA " << fun.getName().str() << "\n";
		
			//outs() << "5.3\n";
			toKeep.clear();
			toPref.clear();	
			for (auto &BB: fun)
			{
				for (auto &I: BB)
				{
					toKeep.insert(&I);
				}
			}
			//outs() << "5.4\n";
			//outs() << "INFO The end for finding AccessInst with false deleteBrunches:                   " << fun.getName().str() << "\n";
    			toPref.clear();
			for (auto I: toKeepPref)
			{
				toPref.push_back((LoadInst *)I);
			}
			//outs() << "5.5\n";
			//outs() << "3\n";
			//if (toPref.size() == 0)
			//outs() << "No oracles\n";
			//if (TempDeep != 0)
			//{
			//		Deep = TempDeep;
			//}
			//return true;
		}
	}*/
	//outs() << "6\n";


	//Now when all unnesseccary branches were deleted
	//We can start to find terminators
	set<Instruction *> toKeepTerminators;
    	findTerminators(fun, toKeepTerminators);
    	set<Instruction *> DepsTerminators;
	#ifdef DEBUGE
	outs() << "Follow Terminators starts\n";
	#endif
	res = followDeps(toKeepTerminators, DepsTerminators, RelevantFunc_InterProc);
	#ifdef DEBUGE
	outs() << "Follow Terminators ends\n";
	#endif
	if (!res)
	{
		//return false;
		//outs() << "INFO:                   Terminator error!\n";
		//toKeepTerminators.clear();
		//DepsTerminators.clear();
		toKeep.clear();
		toPref.clear();
		#ifdef DEBUGE
		outs() << "INFO The end for finding AccessInst with false followTerminatDeps:                   " << fun.getName().str() << "and " << noRet<<"\n";
		#endif
		if (noRet)
		{
			fun.setName(Twine(TERMINATORnoRet_MARKING + fun.getName().str()));
		}else
		{
			fun.setName(Twine(TERMINATORNOnoRet_MARKING + fun.getName().str()));
		}
		/*if (TempDeep != 0)
		{
			Deep = TempDeep;
		}*/
		outs() << "Error: Return value has bad deps\n";
		//return false;
	}
    	toKeep.insert(DepsTerminators.begin(), DepsTerminators.end());
    	toKeep.insert(toKeepTerminators.begin(), toKeepTerminators.end());

	#ifdef DEBUGE
	outs() << "Looking for returns\n";
	#endif	
	set<Instruction *> toKeepReturns;
	set<Instruction *> DepsReturns;
	findReturns(fun, toKeepReturns);
	if (toKeepReturns.size() > 0)
	{
		res = followDeps(toKeepReturns, DepsReturns, RelevantFunc_InterProc);
		if (!res)
		{
			toKeepReturns.clear();
			DepsReturns.clear();
			outs() << "Error: Return value has bad deps\n";
			//outs() << "INFO The end for finding AccessInst:                   " << fun.getName().str() << "\n";
			fun.setName(Twine(TERMINATORNOnoRet_MARKING + fun.getName().str()));
			/*if (TempDeep != 0)
			{
				Deep = TempDeep;
			}*/
			//return false;
		}
	}else
	{
		/*if (TempDeep != 0)
		{
			Deep = TempDeep;
		}*/
		outs() << "Error: no returns\n";
		//return false;
	}
	toKeep.insert(DepsReturns.begin(), DepsReturns.end());
    	toKeep.insert(toKeepReturns.begin(), toKeepReturns.end());

	set<Instruction *> toKeepStores;
	set<Instruction *> DepsStores;
	//findStores(fun, toKeepStores);
	//res = followDeps(toKeepStores, DepsStores, RelevantFunc_InterProc);
	//The idea is that we keep in toKeepPref loads which are "leaf" loads
	//We will prefetch them
	//All other loads are deps, we need to load them 
	//refineUnique(toKeep, toKeepPref);//Double on purpose

	//printDiff(fun, toKeep, toKeepPref);
	
    	toPref.clear();
	for (auto I: toKeepPref)
	{
		toPref.push_back((LoadInst *)I);
	}
	#ifdef DEBUGE
	outs() << "IP time\n";
	#endif	
	if (IsIP)
	{
		int iter = 0;
		for (Function *f: vectorOfFunctions)
		{
			#ifdef DEBUGE
			outs() << "F1: " << f->getName().str() << " F2: " << fun.getName().str() << "\n";
			#endif
			if (f->getName().str().find(fun.getName().str()) != string::npos)
			{
				if ((fun.getReturnType() == f->getReturnType()) && (fun.arg_size() == f->arg_size()))
				{
					#ifdef DEBUGE
					outs() << "Got it!\n";
					#endif
					break;
				}
			} 
			iter++;
		}
		if (iter == vectorOfFunctions.size())
		{
			#ifdef DEBUGE
			outs() << "IPERROR: vectors of Functions are fucked up for" << fun.getName().str() << "\n";
			#endif
			if (fun.getName().str().find(LOOP_MARKING) != string::npos)
			{
				if (LOOP_MODE != true)
				{
					LOOP_MODE = false;
				}
			}
			vectorOftempInst.clear();
			CleanFuncChain(&fun, RelevantFunc_InterProc);
			return false;
		}
		else
		{
			//for (auto &I: toKeep)
			//{
			#ifdef DEBUGE
			outs() << "IPINFO: toKeep handler\n";
			#endif
			vectorOftempInst.clear();
			//(*vectorOftoKeepLoadsSets)[iter].insert(toKeep.begin(), toKeep.end());
			(*vectorOftoKeepLoadsSets)[iter].insert(Deps.begin(), Deps.end());
			(*vectorOftoKeepFuncSets)[iter].insert(DepsCalls.begin(), DepsCalls.end());
			(*vectorOftoKeepFuncSets)[iter].insert(DepsStoresToArgs.begin(), DepsStoresToArgs.end());
			(*vectorOftoKeepFuncSets)[iter].insert(toKeepCalls.begin(), toKeepCalls.end());
			(*vectorOftoKeepFuncSets)[iter].insert(toKeepStoresToArgs.begin(), toKeepStoresToArgs.end());
			(*vectorOftoKeepTerminatorsSets)[iter].insert(DepsTerminators.begin(), DepsTerminators.end());
			(*vectorOftoKeepTerminatorsSets)[iter].insert(toKeepTerminators.begin(), toKeepTerminators.end());
			(*vectorOftoKeepReturnsSets)[iter].insert(DepsReturns.begin(), DepsReturns.end());
			(*vectorOftoKeepReturnsSets)[iter].insert(toKeepReturns.begin(), toKeepReturns.end());
			(*vectorOftoKeepStoresSets)[iter].insert(toKeepStores.begin(), toKeepStores.end());
			(*vectorOftoKeepStoresSets)[iter].insert(DepsStores.begin(), DepsStores.end());
			std::set<Function*> calledFs;
			for (auto FC: toKeepCalls)
			{
				Function * func;
				if (CallInst *CI = dyn_cast<CallInst>(&*FC))
				{
					func = CI->getCalledFunction();
					if (func == NULL)
					{
						if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
						{
							// In this category we have call %1
							// I guess we also need to take care of it
							if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
							{
								if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
								{	
									continue;
								}
								func = bitcastFunction;
							}
						}
					}
					calledFs.insert(func);
				}

			}
			(*vectorOfcalledFunctionsSets)[iter].insert(calledFs.begin(), calledFs.end());
			#ifdef DEBUGE
			for (Instruction *inst: (*vectorOftoKeepLoadsSets)[iter])
			{
				outs() << "IPINFO: Set contains " << *inst << "\n";
			}
			#endif
			//}
			#ifdef DEBUGE
			outs() << "IPINFO: toPref handler\n";
			#endif
			for (auto I: toKeepPref)
			{
				(*vectorOftoPrefLists)[iter].push_back((LoadInst *)I);
				//#ifdef DEBUGE
				//outs() << "IPINFO: List contains " << *((*vectorOftoPrefLists)[iter].back()) << "\n";
				//#endif
			}
		}	
	}
	//outs() << "7\n";
	/*if (toPref.size() == 0)
		outs() << "No oracles\n";*/

	//outs() << "INFO The end for finding AccessInst with true:                   " << fun.getName().str() << "\n";
	//refineLoadsPrefs(toKeep, toKeepPref);
	/*if (TempDeep != 0)
	{
		Deep = TempDeep;
	}*/
	/*outs() << "Here is the error\n";
	if (fun.getName().str().find(TX_MARKING) != string::npos)
	{
		vector<Function* > Seen;
		int num_return_func;
		int delta = 1;
		while(delta != 0)
		{
				num_return_func = 0;
				int iter = 0;
				for (Function *f: vectorOfFunctions)
				{
					if ((f->getName().str().find("_RETURN") != string::npos))
					{
						outs() << "RETURNPROBLEM: Function is " << f->getName().str() << "\n";
						num_return_func++;
					if (std::find(Seen.begin(), Seen.end(), f) == Seen.end())
					{
						Seen.push_back(f);
						getControlDepsPreliminary(*f, (*vectorOftoKeepReturnsSets)[iter]);
						set<Instruction *> toKeepReturns;
						set<Instruction *> DepsReturns;
						findReturns(*f, toKeepReturns);
						if (toKeepReturns.size() > 0)
						{
							int res = true;
							//LoopInfo *LI = &getAnalysis<LoopInfoWrapperPass>(*f).getLoopInfo();
        						//BasicAAResult BAR(createLegacyPMBasicAAResult(*this, *f));
        						//AAResults AAR(createLegacyPMAAResults(*this, *f, BAR));
        						//AA = &AAR;
							//TransferPassResults(AA, LI, this, wpa, true);//true stands for wpa_flag
							res = followDeps(toKeepReturns, DepsReturns, RelevantFunc_InterProc);
							if (!res)
							{
								outs() << "ERROR: no return instructions\n";
							}
						}else
						{
							outs() << "ERROR: no return instructions\n";
						}
						//vectortoKeepReturns[iter].insert(toKeepReturns.begin(), toKeepReturns.end());
						//vectortoKeepReturns[iter].insert(DepsReturns.begin(), DepsReturns.end());
					}
					}
					iter++;

				}
				delta = 0;
				for (Function *f: vectorOfFunctions)
				{
					if ((f->getName().str().find("_RETURN") != string::npos))
					{
						delta++;
					}
			
				}
				delta = delta - num_return_func;
		}
	}
	if (fun.getName().str().find(LOOP_MARKING) != string::npos)
	{
		if (LOOP_MODE != true)
		{
			LOOP_MODE = false;
		}
	}*/
	CleanFuncChain(&fun, RelevantFunc_InterProc);
	return true;
}

void CleanFuncChain(Function* FF, vector<Function* > RelevantFunc_InterProc)
{
	StringRef Kind = "DAE-interproc";
	StringRef Kind1 = "DAE-interproc-calledfrom";
	StringRef Val1 = FF->getName().str();
	/*for (auto F: RelevantFunc_InterProc)
	{
		if (F->hasFnAttribute(Kind))
		{
			F->removeFnAttr(Kind);
		}
		if (F->hasFnAttribute(Kind1))
		{
			outs() << "Found such an attribute\n";
			Module * Mod = FF->getParent();
			AttributeSet AS = FF->getAttributes();
			AttributeSet AS_remove;
			AS_remove.addAttribute(Mod->getContext(), 0, FF->getFnAttribute(Kind).getKindAsString());
			F->setAttributes(AS.removeAttributes(Mod->getContext(), AttributeSet::FunctionIndex, AS_remove));
		}
	}*/
}
void printDiff(Function &fun, set<Instruction *> toKeep, set<Instruction *> toKeepPref)
{
	bool flag = false;
	#ifdef DEBUGE
	outs() << "DIFF for function" << fun.getName() << "\n";
	#endif
	for (inst_iterator I = inst_begin(fun); I != inst_end(fun); ++I)
	{
		for (auto &tK: toKeep)
		{
			if (tK == &*I)
			{
				flag = true;
			}
		}
		for (auto &tKP: toKeepPref)
		{
			if (tKP == &*I)
			{
				flag = true;
			}
			
		}
		if (!flag)
		{
			#ifdef DEBUGE
			outs() << "DIFF instruction " << *I << "\n";
			#endif
		}else
		{
			flag = false;
		}
	}
}

void printDiff(Function *fun1, set<Instruction *> SetToKeep)
{
	bool flag = false;
	#ifdef DEBUGE
	outs() << "DIFF for function" << fun1->getName().str() << "\n";
	#endif
	for (auto &II: SetToKeep)
	{
		for (inst_iterator I = inst_begin(fun1); I != inst_end(fun1); ++I)
		{
			if (II == &*I)
			{
				//outs() << "THE SAME instruction " << *I << "\n";
				flag = true;
			}
		}
		if (!flag)
		{
			#ifdef DEBUGE
			outs() << "DIFF instruction " <<  II << "\n";
			#endif
		}else
		{
			flag = false;
		}
	}
}



void refineLoadsPrefs(set<Instruction *> toKeep, set<Instruction * > toKeepPref)
{
	for (auto &I : toKeepPref)
	{
		for (auto &II: toKeep)
		{
			if (&I == &II)
			{
				toKeep.erase(II);
			}
		}
	}
}
bool deleteUnusedBranches(Function *fun, bool noRet)
{
	outs() << "SDDESIGN: delete unused branhces\n";
	for (Function::iterator block = fun->begin(), blockEnd = fun->end(); block != blockEnd; ++block)
	{
		outs() << "SDDESIGN: -1.\n";
		replaceBranchIfMetadata(*block, noRet);	
		outs() << "SDDESIGN: 0.\n"; 
	}
	Function::iterator block = fun->begin();
	for(;;)
	{
		if (block == fun->end())
			break;
		outs() << "SDDESIGN: 1.\n"; 
		bool incr = deleteDeadBlockIfMetadata(&*block);
		outs() << "SDDESIGN: 2.\n"; 
		if (!incr)
		{
			++block;
		}else
		{
			block = fun->begin();
		}
	}
	//outs() << "Deleted everything \n";
	//Means that now function is empty
	//We deleted all basic blocks
	//Lets insert one BB with only return instruction
	//This function will be deleted anyway
	//So It will not add additional overhead
	block = fun->begin();
	if (block == fun->end())
	{
		outs() << "SDDESIGN: ???????????????????????????????????????????????Did it happend? No way "<< fun->getName().str() <<"\n";
		BasicBlock * BN = BasicBlock::Create(getGlobalContext(), "exit_bb", fun);
		if (fun->getReturnType()->isVoidTy())
		{
			IRBuilder<> builder(BN);
			builder.CreateRetVoid();
		}else
		{
			Value *val = Constant::getNullValue(fun->getReturnType());
			IRBuilder<> builder(BN);
			builder.CreateRet(val);
		}
		AttachMetadata(BN->getTerminator(), "CFGMust", "1");
		if (BN == &(BN->getParent()->getEntryBlock()))
		{
			AttachMetadata(BN->getTerminator(), "EntryBlock", "1");
		}
		return false;
	}
	return true;
		
}

bool deleteDeadBlockIfMetadata(BasicBlock * dst)
{
	//delete this BB if it has no preds
	int pred_num = 0;
	for (BasicBlock * Pred: predecessors(dst))
	{
		++pred_num;
	}
	//Second condition to prevet deleting of entry block
	//maybe we do not need this part
	//Idealy I wanted to deal with PHI instructions here, but it seems it is done automatically
	if(pred_num == 0 && !InstrhasMetadata(dst->getTerminator(), "EntryBlock", "1"))//&& !InstrhasMetadata(dst->getTerminator(), "Leave", "1"))
	{
		/*outs() << "Yes1! "<< *(dst->getTerminator())<<" "<< pred_num<<" and " << dst->getParent()->getName().str()<<"\n"; 
	}*/
	//if(pred_num == 0 && !InstrhasMetadata(dst->getTerminator(), "CFGMust", "1") && !InstrhasMetadata(dst->getTerminator(), "Leave", "1"))
	//{
		//outs() << "Yes2! "<< *(dst->getTerminator())<<" "<< pred_num<<" and " << dst->getParent()->getName().str()<<"\n";
		//outs() << *dst << "\n";
		//Get all ancestors
		/*for (unsigned iter = 0, E = dst->getTerminator()->getNumSuccessors(); iter < E; iter++)
		{
			BasicBlock::iterator I = (dst->getTerminator()->getSuccessor(iter))->begin();
			//outs() << "Instruction " << *I << "\n";
			if (PHINode * PN = dyn_cast<PHINode>(&*I))
			{
				outs() << "PHInode instruction found\n";
			}	
		}*/
		//Check their first instruction. If it is not a PHI node, just delete then
		//If it is a PHI node, replace value with null
		DeleteDeadBlock(dst);
		//dst->eraseFromParent();
		return true;
	}
	return false;
}

void replaceBranchIfMetadata(BasicBlock &block, bool noRet)
{
	TerminatorInst *TInst = block.getTerminator();
	bool isVoid = block.getParent()->getReturnType()->isVoidTy();
	if (isVoid && isa<ReturnInst>(TInst))
	{
		return;
	}
	BranchInst * uncondBI;
	ReturnInst * retInst;
	BasicBlock *dst, *comp;
	BranchInst * BI = dyn_cast<BranchInst>(TInst);
	SwitchInst * SI = dyn_cast<SwitchInst>(TInst);
	//if (SI && !BI)
	//	outs() << "\n\n                         Switch                            \n\n";
	if (BI || SI)
	{
		//1. Just leave BBs
		Instruction * I;
		if (BI)
		{
			I = BI;
		}
		else if (SI)
		{
			I = SI;
		}
		if (isVoid || noRet)
		{
			outs() << "Voooooooooooooooooooooid           oooooooooooooooooooooor                      Reeeeeeeeeeeeeeeeeeeeet\n";
			//It is a leave block which is not the end of the loop
			if (InstrhasMetadata(I, "Leave", "1") && !InstrhasMetadata(I, "LoopExitBranch", "1") && !InstrhasMetadata(I, "CFGMust", "1"))
			{
				outs() << "SDDESIGN: remove predecessor for an instruction " << *I <<"\n";
				//Remove all successor to make this block a leave in the real world
				if (BI)
				{
					for (unsigned int i = 0; i < BI->getNumSuccessors(); ++i)
					{
						dst = BI->getSuccessor(i);
						dst->removePredecessor(&block);
					}
				}
				else if (SI)
				{
					//outs() << "SI inside\n";
					for (unsigned int i = 0; i < SI->getNumSuccessors(); ++i)
					{
						dst = SI->getSuccessor(i);
						dst->removePredecessor(&block);
					}


				}
				//if it this func returns void
				//Create new (return void) instruction, insert it before previous terminator inst
				//Delete previous terminator instr
				//Attach metadata
				//Otherwise it will be deleted
				if (block.getParent()->getReturnType()->isVoidTy())
				{
					IRBuilder<> Builder(TInst);
					Builder.CreateRetVoid();

				}else
				 if (noRet)
				{
					Value *val = Constant::getNullValue(block.getParent()->getReturnType());
					IRBuilder<> builder(TInst);
					builder.CreateRet(val);
					//outs() << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

				}
				TInst->eraseFromParent();
				AttachMetadata(block.getTerminator(), "CFGMust", "1");
				if (&block == &(block.getParent())->getEntryBlock())
				{
					AttachMetadata(block.getTerminator(), "EntryBlock", "1");
				}
				//outs() << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% " << *(block.getTerminator()) <<"\n";
				
		 		return;
	
			}else
			// it is leave but it ends a loop
			if (InstrhasMetadata(I, "Leave", "1") && InstrhasMetadata(I, "LoopExitBranch", "1") && !InstrhasMetadata(I, "CFGMust", "1"))
			
			{
				outs() << "SDDESIGN: remove predecessor for an instruction " << *I <<"\n";
				AttachMetadata(I, "CFGMust", "1");
				
				//Create new basic block and populate it with return inst only
				//But defferent return instr for different types of function
				BasicBlock * BN = BasicBlock::Create(getGlobalContext(), "exit_bb", block.getParent());
				IRBuilder<> builder(BN);
				if (block.getParent()->getReturnType()->isVoidTy())
				{
					builder.CreateRetVoid();
				}else if (noRet)
				{
					Value *val = Constant::getNullValue(block.getParent()->getReturnType());
					builder.CreateRet(val);
					//outs() << "½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½½\n";

				}
				//The idea behind this implementation is following
				//It is leave node, namely it is the last touched basic block
				//but it is the exit for a loop
				//we don't want to delete backedge to loop header
				//more likely that header was touched before
				//so we look for a successor, which terminator inst doesn't have CFGMust metadata
				//assume that it loop exit
				if (BI)
				{
					for (unsigned int i = 0; i < BI->getNumSuccessors(); ++i)
					{
						dst = BI->getSuccessor(i);
						if (!InstrhasMetadata(dst->getTerminator(), "CFGMust", "1") &&!InstrhasMetadata(dst->getTerminator(), "Leave", "1"))
						{
							BI->setSuccessor(i, BN);
							dst->removePredecessor(&block);
							break;
						}
					}
				}
				else if(SI)
				{
					//outs() << "ALARM-2\n";
					for (unsigned int i = 0; i < SI->getNumSuccessors(); ++i)
					{
						dst = SI->getSuccessor(i);
						if (!InstrhasMetadata(dst->getTerminator(), "CFGMust", "1") &&!InstrhasMetadata(dst->getTerminator(), "Leave", "1"))
						{
							SI->setSuccessor(i, BN);
							dst->removePredecessor(&block);
							break;
						}
					}


				}
				//Attach Metadata
				//otherwise it will be deleted later
				AttachMetadata(BN->getTerminator(), "CFGMust", "1");
				if (BN == &(BN->getParent()->getEntryBlock()))
				{
					AttachMetadata(BN->getTerminator(), "EntryBlock", "1");
				}

				return;
			}
		}
		
		//2. Pass some BBs		
		//Don't optimize unconditional branches
		if (SI)
		{
			//outs() << "Switch instruction. Do not know how to deal with it\n";
			return;
		}
		if (BI->isUnconditional() || InstrhasMetadata(BI, "LoopExitBranch", "1") || (BI->getNumSuccessors() < 2))
			return;

		//3. It is inner BBs
		//Process them the same way for all "return" situations
		//There is prefetch on the left side
		if (InstrhasMetadata(BI, "SideLeft", "1") && !InstrhasMetadata(BI, "SideRight", "1"))
		{
			outs() << "LEFT LEFT LEFT LEFT" << *I << "\n";
			dst = BI->getSuccessor(0);
			comp = BI->getSuccessor(1);
			if (block.getParent()->getReturnType()->isVoidTy())
			{
				BasicBlock * BN = BasicBlock::Create(getGlobalContext(), "exit_bb_left", block.getParent());
				IRBuilder<> builder(BN);
				builder.CreateRetVoid();
				for (pred_iterator pred = pred_begin(comp); pred != pred_end(comp); pred++)
				{
					if (*pred == &block)
					{
						outs() << "Is a pred\n";
						comp->removePredecessor(&block);
					}else
					{
						outs() << "Not a pred\n";
					}
				}
				BI->setSuccessor(1, BN);

				AttachMetadata(BN->getTerminator(), "CFGMust", "1");
				if (BN == &(BN->getParent()->getEntryBlock()))
				{
					AttachMetadata(BN->getTerminator(), "EntryBlock", "1");
				}
			}
			else if (noRet)
			{
				Value *val = Constant::getNullValue(block.getParent()->getReturnType());
				BasicBlock * BN = BasicBlock::Create(getGlobalContext(), "exit_bb_left", block.getParent());
				IRBuilder<> builder(BN);
				builder.CreateRet(val);
				for (pred_iterator pred = pred_begin(comp); pred != pred_end(comp); pred++)
				{
					if (*pred == &block)
					{
						outs() << "Is a pred\n";
						comp->removePredecessor(&block);
					}else
					{
						outs() << "Not a pred\n";
					}
				}

				BI->setSuccessor(1, BN);	
				AttachMetadata(BN->getTerminator(), "CFGMust", "1");
				if (BN == &(BN->getParent()->getEntryBlock()))
				{
					AttachMetadata(BN->getTerminator(), "EntryBlock", "1");
				}
				// I do not think that creating uncond branch is right
				// Because then we execute it always
				// regardless runtime control flow
				//uncondBI = BranchInst::Create(dst);
				//comp->removePredecessor(&block);
				//ReplaceInstWithInst(TInst, uncondBI);
				//AttachMetadata(uncondBI, "CFGMust", "1");
				//if (&block == &(block.getParent())->getEntryBlock())
				//{
				//	AttachMetadata(uncondBI, "EntryBlock", "1");
				//}
			}
		}else
		//There is prefetch on the right side
		if (!InstrhasMetadata(BI, "SideLeft", "1") && InstrhasMetadata(BI, "SideRight", "1"))
		{
			outs() << "RIGHT RIGHT RIGHT RIGHT " <<*I << "\n";
			dst = BI->getSuccessor(0);
			comp = BI->getSuccessor(1);
			if (block.getParent()->getReturnType()->isVoidTy())
			{
				BasicBlock * BN = BasicBlock::Create(getGlobalContext(), "exit_bb_right", block.getParent());
				IRBuilder<> builder(BN);
				builder.CreateRetVoid();
				for (pred_iterator pred = pred_begin(dst); pred != pred_end(dst); pred++)
				{
					if (*pred == &block)
					{
						outs() << "Is a pred\n";
						dst->removePredecessor(&block);
					}else
					{
						outs() << "Not a pred\n";
					}
				}
				BI->setSuccessor(0, BN);

				AttachMetadata(BN->getTerminator(), "CFGMust", "1");
				if (BN == &(BN->getParent()->getEntryBlock()))
				{
					AttachMetadata(BN->getTerminator(), "EntryBlock", "1");
				}
			}
			else if (noRet)
			{
				Value *val = Constant::getNullValue(block.getParent()->getReturnType());
				BasicBlock * BN = BasicBlock::Create(getGlobalContext(), "exit_bb_right", block.getParent());
				IRBuilder<> builder(BN);
				builder.CreateRet(val);
				for (pred_iterator pred = pred_begin(dst); pred != pred_end(dst); pred++)
				{
					if (*pred == &block)
					{
						outs() << "Is a pred\n";
						dst->removePredecessor(&block);
					}else
					{
						outs() << "Not a pred\n";
					}
				}
				BI->setSuccessor(0, BN);	
				AttachMetadata(BN->getTerminator(), "CFGMust", "1");
				if (BN == &(BN->getParent()->getEntryBlock()))
				{
					AttachMetadata(BN->getTerminator(), "EntryBlock", "1");
				}
				//uncondBI = BranchInst::Create(comp);
				//dst->removePredecessor(&block);
				//ReplaceInstWithInst(TInst, uncondBI);
				//AttachMetadata(uncondBI, "CFGMust", "1");
				//if (&block == &(block.getParent())->getEntryBlock())
				//{
				//		AttachMetadata(uncondBI, "EntryBlock", "1");
				//}
			}
		}
		/*else
		//there is prefetch on the both sides
		//No need to do anything with this branch
		if (InstrhasMetadata(BI, "SideLeft", "1") && InstrhasMetadata(BI, "SideRight", "1"))
		{
			//outs() << "BOTH BRANCH BOTH BRANCH BOTH BRANCH\n";
		}*/
	}
}

//Annotate all branches
//for loads, funccalls and their deps
void getControlDepsPreliminary(Function &f, set<Instruction *> &toKeep)
{
	if (!InstrhasMetadata(f.getEntryBlock().getTerminator(), "EntryBlock", "1"))
	{
		//outs() << "Entry point" << f.getName().str()<< "for terminator" << *(f.getEntryBlock().getTerminator()) << "\n";
		AttachMetadata(f.getEntryBlock().getTerminator(), "EntryBlock", "1");	
	}
	//outs() << "Entry point" << f.getName().str()<< "for terminator" << *(f.getEntryBlock().getTerminator()) << "\n";
	std::queue<BasicBlock *> Ancestors;
	set<BasicBlock *> Starred;
	for (auto I: toKeep)
	{
		//(&*I)->getType()->dump();
		if (Instruction * inst = dyn_cast<Instruction>(&*I))
		{
			#ifdef DEBUGE
			outs () << "METADATA: " << *I <<"\n";
			#endif
		}else
		{
			continue;
			(&*I)->getType()->dump();
		}
		std::queue<BasicBlock *>().swap(Ancestors);
		Starred.clear();
		BasicBlock *BB = (&*I)->getParent();
		if (!InstrhasMetadata(BB->getTerminator(), "Leave", "1"))
		{
			AttachMetadata(BB->getTerminator(), "Leave", "1");
		}
		//outs() << "GetControlPrelim  "<< *I <<" termin " << *(BB->getTerminator())<<"\n";
		/*if (Ancestors.size() != 0)
		{

			outs() << "Dangerous error!\n";
		}*/
		Ancestors.push(BB);
		Starred.insert(BB);
		
		while(!Ancestors.empty())
		{
			//outs() << "2\n";
			BasicBlock * B = Ancestors.front();
			//try to find an entry BB
			Ancestors.pop();
			//outs() << "2.1:\n";
			for (auto P = pred_begin(B), PE = pred_end(B); P != PE; ++P)
			{
				//outs() << "3\n";
				if(Starred.insert(*P).second)
				{
					Ancestors.push(*P);
					Instruction * TI = (*P)->getTerminator();
					//outs() << "4\n";
					//Must keep this branch anyway
					if (!InstrhasMetadata(TI, "CFGMust", "1"))
					{
						AttachMetadata(TI, "CFGMust", "1");
					}
					//outs() << "5\n";
					if (BranchInst * BI = dyn_cast<BranchInst>(TI))
					{
						if (!BI->isUnconditional() && !InstrhasMetadata(BI, "LoopExitBranch", "1"))
						{
							if (BI->getSuccessor(0) == B)
							{
								if (!InstrhasMetadata(BI, "SideLeft", "1"))	
								{
									AttachMetadata(BI, "SideLeft", "1");
								}	
							}
							if (BI->getSuccessor(1) == B)
							{
								if (!InstrhasMetadata(BI, "SideRight", "1"))	
								{
									AttachMetadata(BI, "SideRight", "1");
								}	
							}
						}
					}
				}
			}
		}
	}
	//outs() << "The end\n";
}


  // Returns true iff F is an F_kernel function.
bool isFKernel(Function &F) {
    return F.getName().str().find(F_KERNEL_SUBSTR) != string::npos &&
           F.getName().str().find(CLONE_SUFFIX) == string::npos;
}

  
// Clones Function F to its parent Module. A pointer to the
// clone is returned.
Function *cloneFunction(Function *F) {
    	ValueToValueMapTy VMap;
    	Function *cF =
        	Function::Create(F->getFunctionType(), F->getLinkage(),
                         F->getName() + CLONE_SUFFIX, F->getParent());
    	for (Function::arg_iterator aI = F->arg_begin(), aE = F->arg_end(),
                                acI = cF->arg_begin(), acE = cF->arg_end();
         			aI != aE; ++aI, ++acI) 
	{
      		assert(acI != acE);
      		acI->setName(aI->getName());
      		VMap.insert(std::pair<Value *, Value *>((Value *)&*aI, (Value *)&*acI));
    	}
    	SmallVector<ReturnInst *, 8> Returns; // Ignored
    	CloneFunctionInto(cF, F, VMap, false, Returns);

    return cF;
  }
//func(*arg1)--> we need all stores to this arg to have a correct value after this function
//load arg1
//use arg1
void findStoresToArgs(Function &F, set<Instruction *> &StoresToArgsList) {
	list<StoreInst *> StoreList;
	//svf->runOnModule(*(F.getParent()));
	findStores(F, StoreList);
	outs() << "Found Stores\n";
	
	for (auto A = F.arg_begin(); A != F.arg_end(); A++)
	{
		if (auto* CstExpr = dyn_cast<ConstantExpr>(A))
		{
			if (CstExpr->isCast())
			{
				//need to process bitcasts here as well
				//outs() << "((((((((((((((((((((((((((((((((FindStoresToArgs and it is a bitcast\n";
			}
			continue;
		}else
		{
			for (auto & storeInst: StoreList)
			{
				//outs() << "STORES we are dealing with"  << *storeInst <<"   "<< *(storeInst->getPointerOperand())<< "   "<< *A <<"\n";
				if (storeInst->getPointerOperand() == &*A)
				{
					//outs() << "Pushed ARGS STORES"  << *storeInst <<"\n";
        				StoresToArgsList.insert((Instruction *)&(*storeInst));
				}else if (!isa<GlobalVariable>(storeInst->getPointerOperand()))
				{
					//false = try to use both AA
					switch (pointerAlias((storeInst->getPointerOperand())->stripPointerCasts(), (&*A)->stripPointerCasts(),
                               			storeInst->getModule()->getDataLayout(), false)) {
          					case AliasResult::NoAlias:
							//outs() << "NoAlias\n";
           					 	break;
          					case AliasResult::MayAlias:
							//outs() << "They do alias somehow with MAY" << *storeInst << " and value " << *A << "\n";
							if (RuleAlias)
							{
        							StoresToArgsList.insert((Instruction *)&(*storeInst));
							}
							break;
          					case AliasResult::PartialAlias:
							//outs() << "They do alias somehow with PART" << *storeInst << " and value " << *A  << "\n";
							if (RuleAlias)
							{
        							StoresToArgsList.insert((Instruction *)&(*storeInst));
							}
							break;
						default:
							//outs() << "They do alias somehow with MUST" << *storeInst << " and value " << *A << "\n";
        						StoresToArgsList.insert((Instruction *)&(*storeInst));
							break;
						
          				}
				
				}

			}
		}
	}
	//This is a funny for loop
	//we collect all stores to global variables
	/*for (auto &storeInst: StoreList)
	{
		if (!isLocalPointer(storeInst->getPointerOperand()))
		{
			//outs() << "Pushed ARGS STORES"<< *storeInst <<"\n";
			StoresToArgsList.insert((Instruction*) &(*storeInst));
		}
	}*/
	
}

// Adds pointer to all LoadInsts in F to LoadList.
void findLoads(Function &F, list<LoadInst *> &LoadList) {
    	for (inst_iterator iI = inst_begin(F), iE = inst_end(F); iI != iE; ++iI) 
	{
      		if (LoadInst::classof(&(*iI))) {
        		LoadList.push_back((LoadInst *)&(*iI));
      		}
    	}
}
// Adds pointer to all LoadInsts in F to LoadList.
void findOracleLoads(Function &F, list<LoadInst *> &LoadList) {
    for (inst_iterator iI = inst_begin(F), iE = inst_end(F); iI != iE; ++iI) {
      if (LoadInst::classof(&(*iI))) {
       	if((*iI).hasMetadata())
	{
		if (MDNode *N = (*iI).getMetadata(LLVMContext::MD_prof))
		{
			if (cast<MDString>(N->getOperand(0))->getString() == "oracle")
			{
				outs() << "ORACLE INFO:                         Orcale load found: " << *iI <<"\n\n";
        			LoadList.push_back((LoadInst *)&(*iI));
			}
		}
	}
      }
    }
}


  // Adds LoadInsts in LoadList to VisList if they
  // operate on visible data.
void findVisibleLoads(list<LoadInst *> &LoadList, list<LoadInst *> &VisList) 
{
    	for (list<LoadInst *>::iterator I = LoadList.begin(), E = LoadList.end(); I != E; ++I) 
	{
		Value * val = (*I)->getPointerOperand();
      		if (isNonLocalPointer((*I)->getPointerOperand())) 
		{
   			VisList.push_back(*I);
      		}else
		{
			#ifdef DEBUGE
			outs() << "Not visible instruction " << val <<"\n";
			#endif
		}
    	}
}

void findFPLoads(list<LoadInst *> &LoadList, list<LoadInst *> &VisList) 
{
    	for (list<LoadInst *>::iterator I = LoadList.begin(), E = LoadList.end(); I != E; ++I) 
	{
		Value * val = (*I)->getPointerOperand();
    		if (PointerType::classof(val->getType()))
		{
			if (Instruction * inst = dyn_cast<Instruction>(val))
			{
				if(isa<GetElementPtrInst>(inst) || isa<SelectInst>(inst))
				{
					if (StructType::classof((cast<GetElementPtrInst>(inst))->getSourceElementType()))
					{
						#ifdef DEBUGE
						outs() << "FPFILTER INFO:  " << *val <<"\n";
						#endif
   						VisList.push_back(*I);
					}else
					{
						#ifdef DEBUGE
						outs() << "FPFILTER INFO: filtered away instruction " << *val <<"\n";
						#endif
					}
				}else
				{
					#ifdef DEBUGE
					outs() << "FPFILTER INFO: filtered away instruction " << *val <<"\n";
					#endif
				}
			}else
			{
				#ifdef DEBUGE
				outs() << "FPFILTER INFO: filtered away instruction " << *val <<"\n";
				#endif
			}
		}else
		{
			#ifdef DEBUGE
			outs() << "FPFILTER INFO: filtered away instruction " << *val <<"\n";
			#endif
		}

     	}
}

// Adds the Instructions in F that terminates a BasicBlock to CfgSet.
// Find terminators, but not returns, no need to do it twice
void findTerminators(Function &F, set<Instruction *> &CfgSet) 
{
	//outs() << "Terminator instructions for functions: " << F.getName() << "\n";
    for (Function::iterator bbI = F.begin(), bbE = F.end(); bbI != bbE; ++bbI) {
      	TerminatorInst *TInst = bbI->getTerminator();
      	if(ReturnInst *RInst = dyn_cast<ReturnInst>(TInst))
	{
		continue;
	}
	//outs() << "Terminator instruction: " << *TInst<< "\n";
	//ReturnInst     *RI = dyn_cast<ReturnInst>(TInst);
	//BranchInst     *BI = dyn_cast<BranchInst>(TInst);
	//bool findReturn = (RI != NULL) && F.getReturnType()->isVoidTy();
      	if (TInst != NULL) {
        	CfgSet.insert(TInst);
      	}
    }
}

void findReturns(Function &F, set<Instruction *> &CfgSet) 
{
    for (Function::iterator bbI = F.begin(), bbE = F.end(); bbI != bbE; ++bbI) {
      if(ReturnInst *RInst = dyn_cast<ReturnInst>(bbI->getTerminator()))
      {	
        CfgSet.insert(RInst);
      }
    }
}


void findFuncCalls(Function &F, set<Instruction *> &CfgSet)
{
	set<Instruction*> Filter_set;
	for(inst_iterator it = inst_begin(F); it != inst_end(F); ++it)
	{
		if (CallInst *CI = dyn_cast<CallInst>(&*it))
		{
			//StringRef name = getFuncName(CI);
			//outs() << "findFuncCalls " << name << "\n";
			//if a func has ACCESS_MARKING, it means that it has already been processed
			//and Access phase was created successfully
			//It could be only if load instr depends on a function
			//So this function is in Deps list
			//README: changes approach above for a consistent solutions: refine for each deps list
			//if (name != "inderect call" && name.find("RTM_fallback") == string::npos && (name.find(LOOP_MARKING) != string::npos || name.find(FUNCTION_MARKING) != string::npos) && name.find(ACCESS_MARKING) == string::npos)
			//outs() << "Function call that was found " << name << "\n";
			//if (name != "inderect call" && name.find("RTM_fallback") == string::npos && (name.find(LOOP_MARKING) != string::npos || name.find(FUNCTION_MARKING) != string::npos))
			//if (name !=)
			//{
				//outs() << "Function call that was found " << name << "\n";
			//	CfgSet.insert(&*it);
			//}else if (name == "abortTransaction")
			//{
				//outs() << "Funct " << name << "\n";
			//}
			Function * func = CI->getCalledFunction();
			if (func != NULL)
			{
				if ((func->getName().str().find(FUNCTION_MARKING) != string::npos) || (func->getName().str().find(LOOP_MARKING) != string::npos))
				{
					/*if (func->mayReadAnyGlobal())
					{
						outs() << "Function: " << *CI << " may read any globals\n";

					}*/
					if (Filter_set.insert(&*it).second)
					{
						//outs() << "FindFuncCalls: " << *CI << "\n";
						CfgSet.insert(&*it);
					}
				}
			}else if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
			{
				if (CstExpr->isCast())
				{
					// In this category we have call %1
					// I guess we also need to take care of it
				//outs() << "TryAccessPhase failed --> bitcast " << name << " and " << noRet << "\n";
				//return false;
				if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
				{
					if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
					{
						outs() << "Double fail\n";
						continue;
					}
					if ((bitcastFunction->getName().str().find(FUNCTION_MARKING) != string::npos) || (bitcastFunction->getName().str().find(LOOP_MARKING) != string::npos))
					{
						//outs() << "FindFuncCalls: " << *CI << "\n";
						if (Filter_set.insert(&*it).second)
						{
							CfgSet.insert(&*it);
						}
					}
				}
				}
			}
	
		}
	}
}

StringRef getFuncName(CallInst *ci)
{
	Function *func = ci->getCalledFunction();
	if (func != NULL)
	{
		if (func->isDeclaration())
		{
			//outs() << "TryAccessPhase failed --> declaration " << name << " and " << noRet << "\n";
			return StringRef("declaration");
		}
	}else 
	if (auto *CstExpr = dyn_cast<ConstantExpr>(ci->getOperand(0)))
	{
		if (CstExpr->isCast())
		{
			// In this category we have call %1
			if (Function * bitcastFunction = dyn_cast<Function>(ci->getCalledValue()->stripPointerCasts()))
			{
					func = bitcastFunction;
					//outs() << "This is a bitcast function\n";
					//bitcast = true;
					//return false;
			}
		}
	}

	if (func)
		return func->getName();
	else return StringRef("inderect call");//Apparently nothing can be done with inderect calls
}

//FIXME: in theory we might want TRUE and FALSE functions for SVFDESIGN as well. 
//So fix it after debugging
bool TryAccessPhase_SVFDESIGN(Instruction * I, set<Instruction *> &DepSet, queue<Instruction *> &Q, bool noRet)
{
	//This part is to get a correct function
	//Options are:
	//call FUNC
	//call bitcast FUNC
	//call intrinsic
	CallInst * CI = dyn_cast<CallInst>(I);
	StringRef name = getFuncName(CI);
	bool bitcast_flag = false;
	//outs() << "TryAccessPhase_SVFDESIGN " << name << " and " << noRet << "\n";
	//outs() << "TryAccessPhase_SVFDESIGN " << *I << "\n";

	//Detect bitcast and functions declarations
	Function * func = CI->getCalledFunction();
	if (func != NULL)
	{
		if (func->isDeclaration() || func->isIntrinsic())
		{
			//outs() << "TryAccessPhase failed --> declaration " << name << " and " << noRet << "\n";
			return false;
		}
		//outs() << "Normal function\n";
	}else 
	if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
	{
		if (CstExpr->isCast())
		{
			// In this category we have call %1
			// I guess we also need to take care of it
			//outs() << "TryAccessPhase failed --> bitcast " << name << " and " << noRet << "\n";
			//return false;
			if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
			{
					if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
					{
						outs() << "Double fail\n";
						return false;
					}
					#ifdef DEBUGE
					outs() << "Bitcast function: " << name << " was successfuly processed\n";
					#endif
					name = bitcastFunction->getName();
					//outs() << "Poka\n";
					func = bitcastFunction;
					bitcast_flag = true;
					//bitcast = true;
					//return false;
			}
			//outs() << "\n";
		}
	}else
	{
		outs() << "?????????????????????????????????????" << *I << "\n";
		return true;
	}

	//When we obtained a function
	//We need to create an access phase if it was not created before
	//Or just leave it as it is if AP already exists
	if (name != "inderect call" && ((name.find(LOOP_MARKING) != string::npos) || (name.find(FUNCTION_MARKING) != string::npos)) && (name.find(ACCESS_MARKING) == string::npos) && (name.find(CLONE_SUFFIX) == string::npos) && (name.find(RECURSION_MARKING) == string::npos))
	{
		vector<Function* > VF;	
		if (checkRecursionEggChickenProblem(CI->getParent()->getParent(), func, &VF))
		{
			//For situation:
			//func:
			//    call func
			//
			//After process will be:
			//RECURSION_func:
			//    call RECURSION_func
			//
			//
			//At some point it will be
			//AP_RECURSION_func:
			//    call AP_RECURSION_func
			if (func->getName().str().find(RECURSION_MARKING) != string::npos)
			{
				outs() << "TryAccessPhase succeeded -> RECURSION " << func->getName().str() << " and " << noRet << " and \n";
				outs() << "TryAccessPhase succeeded -> RECURSION " << CI->getParent()->getParent()->getName().str() << " and " << noRet << " and \n";
				return true;
			}
			outs() << "TryAccessPhase failed -> RECURSION " << func->getName().str() << " and " << noRet << " and \n";
			outs() << "TryAccessPhase failed -> RECURSION " << CI->getParent()->getParent()->getName().str() << " and " << noRet << " and \n";
		}
		
          	//outs() << "INFO: Function  "<< func->getName().str() <<" will be processed\n";
          	//outs() << "INFO: Function  "<< name <<" will be processed\n";
          	//true parameter means that we don't have to keep return values 
          	//and keep their dependencies
          	
		if(!formAccessPhaseRecursion(func,I, false))
		{
			outs() << "TryAccessPhase failed --> !form " << func->getName().str() << " and " << noRet << "\n";
			return false;
		}else
		{
			//outs() << "INFO; Creating access phase succeeded\n";
			//enqueueOperands(I, DepSet, Q);
			outs() << "TryAccessPhase succeeded " << func->getName().str() << " and " << noRet << "\n";
			return true;
		}
	}else
	if ((name.find(ACCESS_MARKING) != string::npos) || (name.find(RECURSION_MARKING) != string::npos))
	{
		return true;
	}else if (name.find(CLONE_SUFFIX) != string::npos)
	{
		outs() << "PANIC CLONE: for function " << func->getName().str() << "\n";
		return false;
	}else 
	{
		outs() << "PANIC NOT SUIT: for function " << func->getName().str() << "\n";
		return false;	
	}


}

bool TryAccessPhase(Instruction * I, set<Instruction *> &DepSet, queue<Instruction *> &Q, bool noRet)
{
	CallInst * CI = dyn_cast<CallInst>(I);
	StringRef name = getFuncName(CI);
	bool bitcast_flag = false;
	//outs() << "TryAccessPhase " << name << " and " << noRet << "\n";

	//Detect bitcast and functions declarations
	Function * func = CI->getCalledFunction();
	if (func != NULL)
	{
		if (func->isDeclaration() || func->isIntrinsic())
		{
			//outs() << "TryAccessPhase failed --> declaration " << name << " and " << noRet << "\n";
			return false;
		}
	}else 
	if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
	{
		if (CstExpr->isCast())
		{
			// In this category we have call %1
			// I guess we also need to take care of it
			//outs() << "TryAccessPhase failed --> bitcast " << name << " and " << noRet << "\n";
			//return false;
			if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
			{
					if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
					{
						outs() << "Double fail\n";
						return false;
					}
					//outs() << "Prevet\n";
					name = bitcastFunction->getName();
					//outs() << "Poka\n";
					func = bitcastFunction;
					bitcast_flag = true;
					//bitcast = true;
					//return false;
			}
			//outs() << "Out\n";
		}
	}else
	{
		//outs() << "?????????????????????????????????????" << *I << "\n";
		return true;
	}
	if (auto* CstExpr = dyn_cast<ConstantExpr>(I->getOperand(0)))
	{
		if (CstExpr->isCast() && isa<Function>(CstExpr->getOperand(0)))
		{
			Function * fun = dyn_cast<Function>(CstExpr->getOperand(0));
			//outs() << "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!Wierd thing: " << fun->getName() << "\n";
			}
	}

	

	std::size_t found_term_noRet = name.find(TERMINATORnoRet_MARKING);
	std::size_t found_term_NOnoRet = name.find(TERMINATORNOnoRet_MARKING);
	if (found_term_noRet != std::string::npos && noRet)
	{
		//outs() << "TryAccessPhase failed --> noRet " << name << " and " << noRet << "\n";
		return false;
	}else if (found_term_NOnoRet != std::string::npos && !noRet)
	{
		//outs() << "TryAccessPhase failed --> !noRet " << name << " and " << noRet << "\n";
		return false;
	}
	if (name != "inderect call" && ((name.find(LOOP_MARKING) != string::npos) || (name.find(FUNCTION_MARKING) != string::npos)) && (name.find(ACCESS_MARKING) == string::npos) && (name.find(CLONE_SUFFIX) == string::npos))
	{	
		
          	//outs() << "INFO: Function  "<< func->getName().str() <<" will be processed\n";
          	//outs() << "INFO: Function  "<< name <<" will be processed\n";
          	//true parameter means that we don't have to keep return values 
          	//and keep their dependencies
          	
		if(!formAccessPhaseRecursion(func,I, noRet))
		{
			//outs() << "TryAccessPhase failed --> !form " << func->getName().str() << " and " << noRet << "\n";
			return false;
		}else
		{
			//outs() << "INFO; Creating access phase succeeded\n";
			//enqueueOperands(I, DepSet, Q);
			//outs() << "TryAccessPhase succeeded " << func->getName().str() << " and " << noRet << "\n";
			return true;
		}
	}
	else if (name.find(ACCESS_MARKING) != string::npos)
	{
		if (!noRet)
		{
			std::size_t found = name.find("_TRUE_");
			std::size_t found_only = name.find("_ONLYTRUE_");

			//Means that we need to recreate the access phase with noRet=false;
			if (found != std::string::npos)
			{
				std::string subname = cleanFuncName(func);
				bool possible = false;	
				Function * AP = findAP(func, false, &possible);	
				if (AP && !bitcast_flag)
				{	
					outs() << "setCalledF1\n";		
					CI->setCalledFunction(AP);
					//enqueueOperands(I, DepSet, Q);
					//outs() << "TryAccessPhase succeeded -> AP " << func->getName().str() << " and " << noRet << "\n";
					return true;
				}else if (AP && bitcast_flag)//bitcast function
				{
					outs() << "PANIC1!!!!\n";
					/*Value* val = CI->getCalledValue();
					val = cast<Value>(AP);
					return true;*/
				}
				//before we change this function lets save it in case creating access phase withret fails
				Function * old_AccessPhase;
				if (!bitcast_flag)
				{
					old_AccessPhase = CI->getCalledFunction();
				}else 
				{
					if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
					{
						old_AccessPhase = bitcastFunction;
					}else
					{
						outs() << "PANIC!!!!2\n";
						return false;
					}
				}

				//2. if 1st attempt failed then
				//find original function
				//and try to recreate an acees phase
				Function * O = findOriginal(func);
				if (O && !O->empty() && !O->isIntrinsic() && !bitcast_flag)
				{
					//outs() << "setCalledF2 " << O->getName().str()<< " vs " << func->getName().str() << "\n";		
					CI->setCalledFunction(O);
					//it is important to delete CLONE_SUFFIX (as to start from the beginning)
					string _name = O->getName().str();

					std::size_t found = _name.find(CLONE_SUFFIX);
					_name.erase(found);
					CI->getCalledFunction()->setName(_name);
					O->setName(_name);
					outs() << "___________________________________" << _name << "\n";
							
					if(!formAccessPhaseRecursion(O,I, false))
					{
						//We know for sure that Access phase with noRet could be formed 								
						//outs() << "setCalledF3\n";		
						CI->setCalledFunction(old_AccessPhase);
						_name = CI->getCalledFunction()->getName().str();
						//Add additional prefix to know that access phase for this function can be 
						//created obly with noRet=true flag
						std::size_t found = _name.find("_TRUE_");
						_name.replace(found,6, "_ONLYTRUE_");
						CI->getCalledFunction()->setName(_name);
								
						//outs() << "After make up___________________________________" << CI->getCalledFunction()->getName().str() << "\n";
						//outs() << "TryAccessPhase failed --> !form " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
						return false;
					}else
					{
						//CI->setCalledFunction(O);
						//outs() << "After make up___________________________________" << CI->getCalledFunction()->getName().str() << "\n";
						//enqueueOperands(I, DepSet, Q);
						//outs() << "TryAccessPhase succeeded -> form " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
						return true;
					}
				}else if (O && bitcast_flag)
				{
					outs() << "PANIC3!!!\n";
				}
				//Means that among all functions we could not find original one
				//It should not happen
				//outs() << "it is extremly wierd!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!We did not find original function\n";
				return false;
			}else if (found_only != string::npos)
			{
				//outs() << "TryAccessPhase failed --> ONLYTRUE " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
				return false;
			}else 
			{
				//Means that _TRUE_ is not there, this access phase was created with _FALSE_
				//conservative case
				//enqueueOperands(I, DepSet, Q);
				//outs() << "TryAccessPhase succeeded -> _FALSE_ " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
				return true;

			}
		}else
		{
			//If noRet = true, any version of function is ok
			//enqueueOperands(I, DepSet, Q);
			//outs() << "TryAccessPhase succeeded -> _TRUE_ " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
			return true;
		}
	}
	else if (name.find(CLONE_SUFFIX) != string::npos)
	{
		//In case it is cloned function and somewhere there is an access phase for it
		string _name = cleanFuncName(func);
				
		//Check recursion
		//outs() << "Recursion check " << CI->getCalledFunction()->getName().str()<< " vs " << CI->getParent()->getParent()->getName().str()  <<" \n";
		//In this case this recursion is not catched
		vector<Function *> VF; 
		if (checkRecursionEggChickenProblem(CI->getParent()->getParent(), func, &VF))
		{
			//enqueueOperands(I, DepSet, Q);
			//outs() << "TryAccessPhase succeeded -> RECURSION " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
			return true;
		}
		bool possible = false;
		Function * AP = findAP(func, noRet, &possible);	
		if (AP)
		{			
			//outs() << "setCalledF4\n";		
			CI->setCalledFunction(AP);
			//enqueueOperands(I, DepSet, Q);
			//outs() << "TryAccessPhase succeeded -> AP " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
			return true;
		}

		//Function can have 4 prefixes:
		//TERMINATOR_noREt: if access phase can not be created with noRet=true
		//ACCESS_PHASE_TRUE: if access phase was created with noRet=true
		//TERMINATOR_!noREt: if access phase can not be created with noRet=false
		//ACCESS_PHASE_FALSE: if access phase was created with noRet=false
		else if (possible)
		{
			func->setName(_name);
			if(!formAccessPhaseRecursion(func,I, noRet))
			{
				//outs() << "TryAccessPhase failed -> possible_clone_!form " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
				return false;
			}else
			{
				//enqueueOperands(I, DepSet, Q);
				//outs() << "TryAccessPhase succeeded -> possible_clone_form " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
				return true;
			}
		}else
		{		
			//outs() << "TryAccessPhase failed -> !possible_clone " << CI->getCalledFunction()->getName().str() << " and " << noRet << "\n";
			return false;
		}

	}
	//outs() << "TryAccessPhase failed -> should not happen " << func->getName().str() << " and " << noRet << "\n";
	return true;//FIXME: it was false, because we assumed that it can never happen
}

bool checkRecursionEggChickenProblem(Function *Dfunc, Function * Ofunc, std::vector<Function *> *VF)
{
	(*VF).push_back(Ofunc);
	//outs() << "Check recursion for " << Dfunc->getName().str() << " and " << Ofunc->getName().str() << "\n";
	if (Dfunc == Ofunc)
	{
		if (Dfunc->getName().find(RECURSION_MARKING) == string::npos)
		{
			Dfunc->setName(Twine(RECURSION_MARKING + Dfunc->getName().str()));
		}
		return true;
	}
	for (inst_iterator I = inst_begin(Ofunc); I != inst_end(Ofunc); I++)
	{
		if (CallInst * CI = dyn_cast<CallInst>(&*I))
		{
			Function *CF = CI->getCalledFunction();
			if (CF != NULL)
			{
				if (CF == Dfunc)
				{
					//Recursion
					if (Dfunc->getName().find(RECURSION_MARKING) == string::npos)
					{
						Dfunc->setName(Twine(RECURSION_MARKING + Dfunc->getName().str()));
					}
					//outs() << "True\n";
					return true;
				}
				else
				{
					bool checked_func = false;
					for (auto F: *VF)
					{
						if (F == CF)
						{
							checked_func = true;
							break;
						}
					}
					//Still a call let's go inside and ask the same question
					if (!checked_func && checkRecursionEggChickenProblem(Dfunc, CF, VF))
					{
						//outs() << "True\n";
						return true;
					}else
					{
						//outs() << "False\n";
						//return false;
					}
				}
			}
		}

	}
	return false;
	//Recursion may be more difficult
	//func:
	//	LOOP_func:
	//		func
	/*string _name = cleanFuncName(Ofunc, true);
	string name = cleanFuncName(Ofunc);
	if (Dfunc->getName().find(_name) != string::npos)
	{
		//outs() << "Check recursion: It is hard to believe but it is recursion " << Ofunc->getName().str() <<" \n";
		Function * Rfunc = Dfunc;
		// Somehow sometimes arguments are different
		// lets check whether arguments are the same
		if (Dfunc->getName().find(name) == string::npos || (Ofunc->getReturnType() != Dfunc->getReturnType()) || (Dfunc->arg_size() != Ofunc->arg_size()))
		{
			Module * m = Ofunc->getParent();
			for (Module::iterator mi = m->begin(); mi != m->end(); ++mi)
			{
				//TODO: add all cases
				if ((*mi).getName().find(name) != string::npos && (*mi).getName().find(CLONE_SUFFIX) == string::npos && (*mi).getName().find(ACCESS_MARKING) == string::npos)
				{
					//FIXME:what a hell?? How is possible to find a function with the same return type, same arguments and it is not the same function? 
					//It does not make sence!!!!!!
					if ((&*mi)->getReturnType() == Ofunc->getReturnType() && (&*mi)->arg_size() == Ofunc->arg_size() && &*mi != Ofunc)
					{
						//outs() << "Check recursion: Chicken was found " << (*mi).getName().str() <<" \n";
						Rfunc = &*mi;
						break;
					}
				}
			}
		}
		if (Rfunc->getName().find(RECURSION_MARKING) == string::npos)
		{
			Rfunc->setName(Twine(RECURSION_MARKING + Rfunc->getName().str()));
		}
		return true;
	}
	return false;*/
}
void followFuncDeps(set<Instruction *> &Set, set<Instruction *> &DepSet, bool noRet, vector<Function*> FuncChain) {
    	bool res;
   	queue<Instruction *> Q;
	set<Instruction* > Seen;
	//outs() << "INFO: Follow function's dependency wothout transformation\n\n";
    	for (set<Instruction *>::iterator I = Set.begin();;) 
	{
		set<Instruction *> DepSetForEachFunc;
		if (I == Set.end())
			break;
		//outs() << "FollowFuncDeps: " << **I << "\n";
		res = true;
		bool return_keep = false;

		clear(Q);
		//First create acceess phase for funcCall
		if (CallInst::classof(*I)) 
		{
			//outs() << "1\n";
			CallInst * CI = cast<CallInst>(*I);
			StringRef name = getFuncName(CI);
			if (name == "inderect call")
			{
				//outs() << "inderect call\n";
				res = false;//keep them only as deps
			}else
			{
			#ifdef DEBUGE
			outs() << "not inderect\n";
			#endif 
			Function *func = CI->getCalledFunction();	
			if (func != NULL)
			{
				#ifdef DEBUGE
				outs() << "not NULL\n";
				outs() << "Function is a process: " << **I << "\n";
				#endif
				if ((name != "abortTransaction")  && (func->getIntrinsicID() != 1954) && (name != "__assert_fail") && (func->getIntrinsicID() != 1939) && (func->getIntrinsicID() != 1938))//llvm.memset, life.start, life.end	
				{
					//outs() << "not weird " << name << "\n";
					//outs() << "not weird " << func->getName() << "\n";
					if (!func->isDeclaration() && (func->getName().str().find(FUNCTION_MARKING) != string::npos) || (func->getName().str().find(LOOP_MARKING) != string::npos))
					{
						//outs() << "not declar and FUNC or LOOP\n";
						//outs() << "IsClone is " << IsClone << "\n";
						if (IsClone)
						{
							res = TryAccessPhase(*I, DepSetForEachFunc, Q, true);//FIXME: Marina NOTE, noRet(true) here
						}else
						{
							//outs() << "TryACCESSPHASE_SVF\n";
							res = TryAccessPhase_SVFDESIGN(*I, DepSetForEachFunc, Q, false);//FIXME: Marina NOTE, noRet(true) here
						}
					}
					//outs() << "declar and FUNC or LOOP\n";
					//outs() << "Intrinsic ID" << **I  << " with ID = " << func->getIntrinsicID() << "\n";
					/*if (IntrinsicInst::classof(*I))
					{
						outs() << "Yes\n";
					}*/
				}else if (func->getIntrinsicID() != 1954 && name != "abortTransaction")//memset is here
				{
					//res = false;//Marina FIXME: we can pick this functions if they are in deps of something 
				}
			}else if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
			{
				if (CstExpr->isCast())
				{
					// In this category we have call %1
					// I guess we also need to take care of it
					//outs() << "TryAccessPhase failed --> bitcast " << name << " and " << noRet << "\n";
					//return false;
					if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
					{
						if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
						{
							//do nothing
						}else if ((bitcastFunction->getName().str().find(FUNCTION_MARKING) != string::npos) || (bitcastFunction->getName().str().find(LOOP_MARKING) != string::npos))
						{
							//outs() << "not declar and FUNC or LOOP\n";
							//outs() << "IsClone is " << IsClone << "\n";
							if (IsClone)
							{
								res = TryAccessPhase(*I, DepSetForEachFunc, Q, true);//FIXME: Marina NOTE, noRet(true) here
							}else
							{
								//outs() << "TryACCESSPHASE_SVF\n";
								res = TryAccessPhase_SVFDESIGN(*I, DepSetForEachFunc, Q, false);//FIXME: Marina NOTE, noRet(true) here
							}
						}
					}
				}
			}else
			{
				#ifdef DEBUGE
				outs() << "MYSTERY: Something we do not know about: " << **I << "\n";
				#endif
				//outs() << "NULL\n";
				//res = false;//Marina FIXME: we can pick this functions if they are in deps of smth
				//It is either call %1 or bitcats call 
				//I decided not to take of them here
				//But rather if something depends on them

			}
			//outs() << "just because\n";
			/*if (name != "abortTransaction")
			{
				res = TryAccessPhase(*I, DepSetForEachFunc, Q, noRet);
			}*/
			}
		}
		if (!res)
		{
			//outs() << "Function was erased " << *(*I) << "\n";
			Set.erase(I);
			++I;
			continue;
		}else
		{
			if (CallInst *CI = dyn_cast<CallInst>(*I))
			{
				Function * f = CI->getCalledFunction();
				if (f != NULL)
				{
					if (f->getName().str().find("_ARGUMENT") != string::npos)
					{
						return_keep = true;
					}
				}else if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
				{
					if (CstExpr->isCast())
					{
						// In this category we have call %1
						// I guess we also need to take care of it
						//outs() << "TryAccessPhase failed --> bitcast " << name << " and " << noRet << "\n";
						//return false;
						if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
						{
							if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
							{
							}else if (bitcastFunction->getName().str().find("_ARGUMENT") != string::npos)
							{
								return_keep = true;
							}

						}
					}
				}

				if (DepSet.find(*I) == DepSet.end() && !checkTheInstructionInTheSet(*I))
				{
					enqueueOperands(*I, DepSetForEachFunc, Q, return_keep, FuncChain);
				}

			}

		}
		//outs() << "toKeepFuncCalls cantains " << getFuncName((CallInst *)(*I)) << " and " << return_keep << "\n";
		while (!Q.empty() && res) {
      			Instruction *Inst = Q.front();
      			Q.pop();
			//outs() << "	ANNOUNCMENT: dependent instruction " << *Inst << "\n";
			if (DepSet.find(Inst) != DepSet.end() || checkTheInstructionInTheSet(Inst))
			{
				continue;
			}
			if (Seen.find(Inst) != Seen.end())
			{
				continue;
			}
			Seen.insert(Inst);

      			//non-local stores are prohibited.
			if (CallInst::classof(Inst)) {
				CallInst * CI = dyn_cast<CallInst>(Inst);
				Function *f = CI->getCalledFunction();
				StringRef name = getFuncName(CI);
				//They are normal functions, but probably from a standart library
				if ((f != NULL) && (name.find("RTM_fallback") == string::npos) && ((name.find(LOOP_MARKING) == string::npos) && (name.find(FUNCTION_MARKING) == string::npos)))
				{
					bool onlyReadsMemory = ((CallInst *)Inst)->onlyReadsMemory();
        				bool annotatedToBeLocal = InstrhasMetadata(Inst, "Call", "Local");

        				//res = onlyReadsMemory || annotatedToBeLocal;
				}else
				{
					//outs() << "	ANNOUNCMENT: dependent instruction " << *Inst << "\n";
					//outs() << "I am not going to process this function " << *Inst << "\n";
					//bitcasts functions go here as well
					//together with call %1
					/*if (IsClone)
					{
						res = TryAccessPhase(Inst, DepSetForEachFunc, Q, false);
					}else
					{
						res = TryAccessPhase_SVFDESIGN(Inst, DepSetForEachFunc, Q, false);
					}*/
				}
			}
      			else if (StoreInst::classof(Inst)) {
				if (!TransAP)
				{
        				res = isLocalPointer(((StoreInst *)Inst)->getPointerOperand());
        				if (!res) {
         		 			//outs() << " <!store Func " << *Inst << "!>\n";
        				}
				}
      			}else if (AllocaInst::classof(Inst) && !allocaAllowed)
			{
				res = false;
         		 	//outs() << " <!alloca Func" << *Inst << "!>\n";
			}
			
      			if (res) 
      			{
				//outs() << "EnqueueOperands start\n";
        			enqueueOperands(Inst, DepSetForEachFunc, Q, return_keep, FuncChain);
				//outs() << "EnqueueOperands end\n";
			}else
			{
				//outs() << "Erase function " << getFuncName((CallInst *)(*I)) << "\n";
				//outs() << "Function was erased" << **I << "  because deps " << *Inst << "\n";
				Set.erase(I);	
			}
    		}
		if (res)
		{
			DepSet.insert(DepSetForEachFunc.begin(), DepSetForEachFunc.end());
		}
		++I;
    	}
	#ifdef DEBUGE
	outs() << "INFO:  going out of followFuncDeps\n";
	#endif
        return;
  }

//If function has arguments that are changed inside
//we should add proper instructions to an AP
bool findArgsInstr(Function &fun, set<Instruction *> &DepSet)
{
	auto &Args = fun.getArgumentList();
		
	for (auto &Arg: Args)
	{
		if (auto *CstExpr = dyn_cast<ConstantExpr>(&Arg))
			continue;
		//outs() << "Args instructions: " << Arg << " for function" << fun.getName().str() << "\n";
		for (inst_iterator i = inst_begin(fun), IE = inst_end(fun); i != IE; ++i)
		{
			if (Value * iv = dyn_cast<Value>(&*i))
			{
				//outs() << "Value " << *iv << "\n";
				if (isa<StoreInst>(&*i))
				{
					//for (auto num = 0; num < (&*i)->getNumOperands(); num++)
					//{
						Value * val = (&*i)->getOperand(1);
						if (val == &Arg && !InstrhasMetadata(&*i, "GlobalAlias", "MayAlias") && !InstrhasMetadata(&*i, "GlobalAlias", "MustAlias") && !InstrhasMetadata(&*i, "GlobalAlias", "NoAlias"))
						{
        						if (isLocalPointer(((StoreInst *)(&*i))->getPointerOperand()))
							{
								//outs() << "Local argument\n";
								DepSet.insert(&*i);
							}
						}
					//}
				}
				if (iv == &Arg)
				{
					DepSet.insert(&*i);
				}
			}	
		}
	}
}

  // Adds dependencies of the Instructions in Set to DepSet.
  // Dependencies are considered to be the operators of an Instruction
  // with the exceptions of calls. In case a LoadInst is a dependency
  // the coresponding StoreInst is also considered as a dependency
  // as long it does not operate on visible memory.
  // Retrurns false iff a prohibited instruction are required.
  // The contents of Set and DepSet are only reliable if the result
  // is true.
bool followDeps(set<Instruction *> &Set, set<Instruction *> &DepSet, vector<Function *> &interproc_Func) {
	#ifdef DEBUGE
	outs() << "I start following Deps\n";
	#endif
    	bool res;
   	queue<Instruction *> Q;
	set<Instruction * > Seen;
	int counter = 0;
    	for (set<Instruction *>::iterator I = Set.begin();I != Set.end(); I++) 
	{
		res = true;
		clear(Q);
		set<Instruction *> DepSetForEachInst;
		//For each original instruction get deps
		//first enqueueOperands
		//then for loads and calls enqueueStores
		//
		//We do it once more for all deps instructions
		//I could combine it together to have more elegant code, but due to time constrains 
		//We have what we have
		bool return_flag = false;
		if (isa<LoadInst>(*I))
		{
			return_flag = true;
		}
		if (isa<TerminatorInst>(*I))
		{
			if(InstrhasMetadata(*I, "CFGMust", "1"))
			{
				return_flag = true;
			}
		}
		if (isa<ReturnInst>(*I))
		{
			#ifdef DEBUGE
			outs() << "Return instruction: " << &*I << "\n";
			#endif
			if(InstrhasMetadata(*I, "Leave", "1"))
			{
				return_flag = true;
			}
		}

		#ifdef DEBUGE
		outs() << "The instruction: " << **I << " set??\n";
		#endif
		if (!checkTheInstructionInTheSet(*I))
		{
			#ifdef DEBUGE
			outs() << "The instruction: " << **I << " is not in the set\n";
			#endif
			enqueueOperands(*I, DepSetForEachInst, Q, return_flag, interproc_Func);
		}
		   
    		while (!Q.empty() && res) {
      			Instruction *Inst = Q.front();
      			Q.pop();
			
			if (DepSet.find(Inst) != DepSet.end() || checkTheInstructionInTheSet(Inst))
			{
				continue;
			}
			if (Seen.find(Inst) != Seen.end())
			{
				continue;
			}
			Seen.insert(Inst);
			#ifdef DEBUGE
			outs() << "	ANNOUNCMENT: dependent instruction " << *Inst << "\n";
			#endif
      			// Calls and non-local stores are prohibited.
      			if (CallInst::classof(Inst)) {
				//TODO: add safity check
        			//outs() << " call " << *Inst << "!>\n";
				CallInst * CI = dyn_cast<CallInst>(Inst);
				StringRef name = getFuncName(CI);
				if (name.find(LOOP_MARKING) == string::npos && name.find(FUNCTION_MARKING) == string::npos)
				{	
					bool onlyReadsMemory = ((CallInst *)Inst)->onlyReadsMemory();
        				bool annotatedToBeLocal = InstrhasMetadata(Inst, "Call", "Local");

        				//res = onlyReadsMemory || annotatedToBeLocal;
					//outs() << "!Check function for locality " << res << "\n";
				}else if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
				{
					if (CstExpr->isCast())
					{
						//outs() << "BITCAST function for instr " << *Inst << "\n"; 
					}
				
				}else
				{
					//outs() << "I am not going to process the function: " << *Inst << "\n";
					/*if (IsClone)
					{
						res = TryAccessPhase(Inst, DepSetForEachInst, Q, false);
					}else
					{
						res = TryAccessPhase_SVFDESIGN(Inst, DepSetForEachInst, Q, false);
					}
					if (!res)
					{
						outs() << "!TryAccessPhase was not created for " << *Inst <<"\n";
					}*/

				}
      			} else if (StoreInst::classof(Inst)) {
				if (!TransAP)
				{
        				res = isLocalPointer(((StoreInst *)Inst)->getPointerOperand());
        				if (!res) {
         		 			outs() << " <!storeB " << *Inst << "!>\n";
        				}
				}
      			}else if (AllocaInst::classof(Inst) && !allocaAllowed)
			{
				res = false;
         		 	outs() << " <!alloca " << *Inst << "!>\n";
			}
			/*else if (LoadInst::classof(Inst) && (Deep != 100))
			{
				counter--;
				if(counter < 0)
				{
         		 		outs() << " <!load " << *Inst << "!>\n";
					res = false; 
					// It means that this load depends on a chain of loads which is 
					//longer than depth(Deep)
				}
			}*/
			
			if (!res)
			{
				//outs() << "\n\nRES:" << res << " for not lucky inst " << *Inst << "\n\n";
				//outs() << "Pula\n";
				if (isa<TerminatorInst>(*I))
				{
					//That is realy bad
					Instruction * ti = dyn_cast<Instruction>(*I);
					//outs() << "INFO: This is really bad --> TerminatorInst: " << *ti << "\n";
					return false;
					/*if (counter >= 0) 
					{
					return false;
					}
					else 
					{
						//The goal is to reduce a number of loads and not 
						//to delete all of them
						//So if this load is so critical
						//just leave it as it is
						res = true;
					}*/
					//BasicBlock * BB = (*I)->getParent();
					//BB->eraseFromParent();
				}else
				{
					//outs() << "INFO: That is not bad --> SomeInst: " << *(*I) << "\n"; 
					//outs() << "Kola\n";
					Set.erase(I);
				}
			}

      			if (res) 
      			{
				//outs() << "enqueueOperands() /for " << *Inst<< "\n";
        			enqueueOperands(Inst, DepSetForEachInst, Q, return_flag, interproc_Func);							
      			}
		}
		if (res)
		{
			//outs() << "DepSet insert for"<< **I<<"\n";
			/*if (DepSetForEachInst.size() == 0 && LoadInst::classof(*I))
			{
				outs() << "DepSet is zero "<< **I<<"\n";
				Set.erase(I);
			}else
			{*/
				if (isa<LoadInst>(*I) || isa<TerminatorInst>(*I))
				{
					int num = 0;
					int numS = 0;
					for (auto &inst: DepSetForEachInst)
					{
						if (isa<LoadInst>(inst))
						{
							num++;
							#ifdef DEBUGE
							outs() << "Load: " << *inst << "\n";
							#endif
						}else
						if (isa<StoreInst>(inst))
						{
							numS++;
						}
					}
					#ifdef DEBUGE
					if (isa<LoadInst>(*I))
					{
						outs() << "Number of loads is " << num << " Stores: " << numS << " for an instruction " << **I << " and size is " << DepSetForEachInst.size() << "\n";
					}else
					{
						outs() << "Number of loads is " << num << " Stores: " << numS << " for an instruction " << **I << " and size is " << DepSetForEachInst.size() << "\n";

					}
					#endif
				}
				DepSet.insert(DepSetForEachInst.begin(), DepSetForEachInst.end());
			//}
			
		}
    	}
	/*if (Set.size() != 0)
	{
		//outs() << "INFO: not all instr were erased\n";
		return true;
	}
    	else {
		//outs() << "INFO: all instr were erased\n";
		return false;
	}*/
	return true;
}

  // Convinience call
  bool followDeps(Instruction *Inst, set<Instruction *> &DepSet, vector<Function *> &FV) {
    set<Instruction *> Set;
    Set.insert(Inst);
    return followDeps(Set, DepSet, FV);
  }

//This function is needed to solve the following case:
//call func(arg *a1)
//var1 = do smth with a1
//
//In this case potentially a1 variable can be changed inside the function
//of course if argument is a constant we do not include this function
//Also this function should dominate instruction, otherwise all changes do not affect actual value 
void enqueueArgs(Instruction *Inst, Value * I, set<Instruction *> &Set, queue<Instruction *> &Q)
{
	//outs() << "\nDeps for: " << *Inst<<" \n";
	//Check if the value a constant, then we do not need to care about it
	if (ConstantExpr::classof(I))
	{
		return;
	}
	
	Function * F = Inst->getParent()->getParent();
	llvm::DominatorTree DTI = llvm::DominatorTree();
	DTI.recalculate(*F);
	//For situation:
	//alloca r1
	//func(r1)
	//load r1
	//do stuff with r1
	BasicBlock *loadBB = Inst->getParent();
    	queue<BasicBlock *> BBQ;
    	set<BasicBlock *> BBSet;
    	BBQ.push(loadBB);
    	bool first = true;
    	bool found = false;
    	while (!BBQ.empty()) {
     		BasicBlock *BB = BBQ.front();
      		BBQ.pop();
      	
		BasicBlock::reverse_iterator RI(Inst->getIterator());
      		for (BasicBlock::reverse_iterator i = first ? RI : BB->rbegin(), iE = BB->rend(); i != iE; ++i)
		{
			if (CallInst * CI = dyn_cast<CallInst>(&*i))
			{
				if (DTI.dominates(&*i, Inst))
				{
					if (Instruction * IInst = dyn_cast<Instruction>(I))
					{
						if (!DTI.dominates(IInst, &*i))
						{
							continue;
						}
					}
					Function *fn = CI->getCalledFunction();
					if (fn != NULL)
					{
						if (fn->isDeclaration())
						{
							continue;
						}
						//outs() << "Call dominates instruction: " << *i<<" \n";
						for (unsigned j = 0; j < CI->getNumArgOperands(); ++j)
						{
							Value *val = CI->getArgOperand(j);
							//outs() << "Argument is 1: " << *val <<" \n";
							//outs() << "Argument is 2: " << *I <<" \n";
							//outs() << "Argument is : " << &*val <<" \n";
							if (val == I)
							{
								//outs() << "Call dominates instruction: " << *i<<" \n";
								//outs() << "Equal\n\n";
								enqueueInst(&*i, Set, Q, false);
								found = true;
								break;
							}
						}
					}else
					if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
					{
						//What does it mean? Why is it bad when the first operand is const? Avoiding casts?
						//It is not actually correct, because of the following example
						//alloca %2
						//call bitcast %1(%2, %3) --> lets say this function modifies %2 and %3
						//reload %2
						//do stuff with %2
						if (CstExpr->isCast())
						{
							//FIXME: technically it is not correct anyway
							//if (fn = dyn_cast<Function>(CstExpr->getOperand(0)))
							if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
							{
								for (auto &A: bitcastFunction->getArgumentList())
								{
									if (I == &A)
									{
										enqueueInst(&*i, Set, Q, false);
										found = true;
										break;
									}
								}
							}
							continue;
						}
					}
				
				}
			}
		}
		if (!found)
		{
			for (pred_iterator pI = pred_begin(BB), pE = pred_end(BB); pI != pE;
             		++pI) {
          			if (BBSet.insert(*pI).second) 
				{
            				BBQ.push(*pI);
          			}
        		}
		}
      		first = false;
	}
}

void arg_involved(Instruction* Inst, Value * val)
{
	Function * parent = Inst->getParent()->getParent();
	int iter = 0;
	for (auto arg = parent->arg_begin(); arg != parent->arg_end(); arg++)
	{
		if (&*arg == val)
		{
			if (parent->getName().str().find("_ARGUMENT") == string::npos)
			{
        			std::string postfix = "_ARGUMENT";
				parent->setName(Twine(parent->getName().str() + postfix));
				
			}
			parent->addAttribute(iter, Attribute::InReg);	
			return;
		}
		iter++;
	}
}

  // Enques the operands of Inst.
  // We do it in 2 steps:
  // 			v1 = instr v2, v3
  // 			1. chech whether v2 or v3 are instructions and enqueue them
  // 			2. chech whether v2 and v3 are function arguments of a function that dominates the current instruction.
  //
  void enqueueOperands(Instruction *Inst, set<Instruction *> &Set,
                       queue<Instruction *> &Q, bool keep_return, vector<Function *> &interproc_Func) {
	//Function calls are allowded now
	//So need to process dependencies with function arguments
	#ifdef DEBUGE
	outs() << "I start enqueueing Operands\n";
	#endif
    	if (CallInst * CI = dyn_cast<CallInst>(Inst))
    	{	
		#ifdef DEBUGE
		outs() << "Call Instruction: " << *Inst << "\n";
		#endif 
		Function * f = CI->getCalledFunction();
		//for call %1
		Value * fv;
		if (f == NULL)
		{
			fv = (CI->getCalledValue())->stripPointerCasts();
			if (Instruction::classof(fv))
			{
				enqueueInst(fv, Set, Q, keep_return);
			}
			#ifdef DEBUGE
			outs() << "Call Instruction: " << *Inst << "\n";
			#endif
			for (unsigned i = 0; i < CI->getNumArgOperands(); ++i)
			{
				Value *val = CI->getArgOperand(i);
				#ifdef DEBUGE
				outs() << "Call value: " << *val << "\n";
				#endif
				/*if (ConstantExpr::classof(val))
				{
					continue;	
				}*/
				//keep_return is only true if we care about args of this function
				enqueueInst(val, Set, Q, keep_return);
				//enqueueArgs(Inst, val, Set, Q);
				// if it is not special Transactional Access phase mode
				//enqueueStores(val, Inst, Inst, Set, Q, 1);//MARINA FIXME The last argument is a rule, later need to provide a real argument
				//outs() << "For function " << Inst->getParent()->getParent()->getName().str() << "\n";
				vector<Function * > Seen;
				Seen.insert(Seen.end(), interproc_Func.begin(), interproc_Func.end());
				enqueueStoresIP(val, Inst, interproc_Func, Set, Q, 1, Seen, 1);
				if (keep_return)
				{
					arg_involved(Inst, val);
				}
			}
				
			//outs() << "Funky function " << *fv << "\n";
						
		}else
		{
			//outs() << "Call Instruction for enqueueOperands " << *Inst << "\n";
			for (unsigned i = 0; i < CI->getNumArgOperands(); ++i)
			{
				Value *val = CI->getArgOperand(i);
				/*if (!isa<Instruction>(val))
				{
					//I did for an example:
					//call TMFUNC_1(bitcast TMFUNC_2)
					//So, bitcast TMFUNC_2 is a value, so it will be not tacken care of
					//
					Value *FUF_val = val->stripPointerCasts();
					if (Function * FUF = dyn_cast<Function>(FUF_val))
					{
						for (auto it = FUF->arg_begin(); it != FUF->arg_end(); it++)
						{
							if (Value * FUF_arg = dyn_cast<Value>(*&it))
							{
								#ifdef DEBUG
								outs() << "FUF arg: " << FUF_arg << "\n";
								#endif
								//enqueueInst(FUF_arg, Set, Q, true);
							}
						}
					}	
				}*/
				//outs() << "Val: " << *val << "\n";
				/*if (ConstantExpr::classof(val))
				{
					continue;	
				}*/
				//keep_return is only true if we care about args of this function
				if (f->getAttributes().hasAttribute(i, Attribute::InReg))
				{
					enqueueInst(val, Set, Q, true);
				}else
				{
					enqueueInst(val, Set, Q, false);
				}
				//enqueueInst(val, Set, Q, keep_return);
				//enqueueArgs(Inst, val, Set, Q);
				// if it is not special Transactional Access phase mode
				//enqueueStores(val, Inst, Inst,Set, Q, 1);//MARINA FIXME rule
				//outs() << "For function " << Inst->getParent()->getParent()->getName().str() << "\n";
				vector<Function * > Seen;
				Seen.insert(Seen.end(), interproc_Func.begin(), interproc_Func.end());
				enqueueStoresIP(val, Inst, interproc_Func, Set, Q, 1, Seen, 1);
				if (keep_return)
				{
					arg_involved(Inst, val);
				}
			}
		}
	}
	else if (StoreInst *str = dyn_cast<StoreInst>(Inst)){
		Value * val = str->getValueOperand();
		#ifdef DEBUGE
		outs() << "Call store value: " << *val << "\n";
		#endif
		enqueueInst(val, Set, Q, keep_return);
		//enqueueArgs(Inst, val, Set, Q);
		if (keep_return)
		{
			arg_involved(Inst, val);
		}
		//outs() << "Store instruction for Store instruction\n";
		// if it is not special Transactional Access phase mode
		//enqueueStores(val, Inst, Set, Q, 0);//MARINA FIXME rule
		val = str->getPointerOperand();
		#ifdef DEBUGE
		outs() << "Call store pointer value: " << *val << "\n";
		#endif
		enqueueInst(val, Set, Q, keep_return);
		//enqueueArgs(Inst, val, Set, Q);
		if (keep_return)
		{
			arg_involved(Inst, val);
		}
	}
	else if (LoadInst *ldi = dyn_cast<LoadInst>(Inst)) {
		#ifdef DEBUG
		outs() << "Load processed " << *Inst << "\n";
		#endif 
		Value *ptr = ldi->getPointerOperand();
		//outs() << "Operand: " << *ptr << "\n";
		if (!isa<Instruction>(ptr))
		{
			ptr = ptr->stripPointerCasts();
			//outs() << "Operand without cast: " << *ptr << "\n";
		}
		/*if (ConstantExpr::classof(ptr) || Constant::classof(ptr))
		{
			//do nothing
			#ifdef DEBUGE
			outs() << "Constant and not a pointer\n";
			#endif	
		}else*/
		//{
		// if it is not special Transactional Access phase mode
          	//enqueueStores(ptr, Inst, Inst, Set, Q, 0);
          	#ifdef DEBUGE
		if (ldi->getParent()->getParent()->getName().find("TMFUNC_TMrbtree_get") != string::npos){
		if (ldi->getParent()->getParent()->getName().find("LOOPFUNC") == string::npos){
          	for (auto F: interproc_Func)
		{
			outs() << "Function for inter_proc: " << F->getName().str() << "\n";
		}}}
		#endif
		//outs() << "For function " << Inst->getParent()->getParent()->getName().str() << "\n";
		vector<Function * > Seen;
		Seen.insert(Seen.end(), interproc_Func.begin(), interproc_Func.end());
          	enqueueStoresIP(ptr, Inst, interproc_Func, Set, Q, 0, Seen, 1);
		enqueueInst(ptr, Set, Q, keep_return);
		//enqueueArgs(Inst, ptr, Set, Q);
		if (keep_return)
		{
			arg_involved(Inst, ptr);
		}
		//}
        }else if (BranchInst * BI = dyn_cast<BranchInst>(Inst))
	{
		if (BI->isConditional())
		{
			Value* val = BI->getCondition();
      			enqueueInst(val, Set, Q, keep_return);
			//outs() << "For function " << Inst->getParent()->getParent()->getName().str() << "\n";
			vector<Function * > Seen;
			Seen.insert(Seen.end(), interproc_Func.begin(), interproc_Func.end());
          		enqueueStoresIP(val, Inst, interproc_Func, Set, Q, 0, Seen, 1);
		}
	}else
	{
		#ifdef DEBUGE
		outs() << "Instruction: " << *Inst << "\n";
		#endif 
		vector<Value *> operands;
    		for (User::value_op_iterator I = Inst->value_op_begin(),
                                 E = Inst->value_op_end(); I != E; ++I) 
		{
			//outs() << "Operand: " << **I << "\n";
			bool unique = true;
			for (auto val: operands)
			{
				if (val == *I)
				{
					unique = false;
					break;
				}
			}
			if (unique)
			{
				//outs() << "enqueueInst\n";
      				enqueueInst(*I, Set, Q, keep_return);
				//outs() << "enqueueArgs\n";
				//enqueueArgs(Inst, *I, Set, Q);//TODO:FIXME
          			//enqueueStores(*I, Inst, Inst, Set, Q, 0);
				//outs() << "enqueueStoresIP\n";
				//outs() << "For function " << Inst->getParent()->getParent()->getName().str() << "\n";
				vector<Function * > Seen;
				Seen.insert(Seen.end(), interproc_Func.begin(), interproc_Func.end());
          			enqueueStoresIP(*I, Inst, interproc_Func, Set, Q, 0, Seen, 1);
				if (keep_return)
				{
					arg_involved(Inst, *I);
				}
				operands.push_back(*I);
			}
			// if it is not special Transactional Access phase mode
			//enqueueStores(*I, Inst, Set, Q, 0);// MARINA FIXME rule
		}
		//outs() << "enqueueOperands for a noraml instruction is finished\n";
    	}
}

  // Adds Val to Set and Q provided it is an Instruction that has
  // never before been enqued to Q. This assumes that an Instruction
  // is present in Set iff it has been added to Q.
  // ret argument shows if val is a return value of a function
  // or it is a function's argument
  // ret = false (it is just a function argument)
  // ret = true (it is a return value of a function)
void enqueueInst(Value *Val, set<Instruction *> &Set,
                   queue<Instruction *> &Q, bool ret) {
	if (Instruction::classof(Val)) 
	{
      		if (Instruction *Inst = dyn_cast<Instruction>(Val))
		{
			if (ret)
			{
				if (CallInst * CI = dyn_cast<CallInst>(Inst))
				{
	
					//This part here is just for marking
					//functions that produce a return value that is used for loads or other functions
					//outs() << "SDDEDIGN: Function call!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! " << *Inst << "\n";
					Function * fun = CI->getCalledFunction();
					bool flag = true;
					if (fun == NULL)
					{
						if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
						{
							if (CstExpr->isCast())
							{
								// In this category we have call %1
								// I guess we also need to take care of it
								if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
								{
									if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
									{	
										flag = false;
									}
									fun = bitcastFunction;
								}
							}
						}else
						{
							flag = false;
						}
					}

					if (flag && fun->isDeclaration())
					{
						flag = false;
					}
					if (flag)
					{
						if (fun->getName().str().find("_RETURN") == string::npos)
						{
        						std::string postfix = "_RETURN";
							fun->setName(Twine(fun->getName().str() + postfix));
						}
					}
				}
			}
      			//outs() << "enqueueOperands instruction inserted  not yet" << *Inst << "\n";
      			if (Set.insert(Inst).second) 
			{ // true if Inst was inserted
        			//outs() << "enqueueOperands instruction inserted " << *Inst << "\n";
        			//if (find(vectorOftempInst.begin(), vectorOftempInst.end(), Inst) == vectorOftempInst.end())
				//{
					//outs() << "The instruction will be enqueueed: " << *Inst << "\n";
        				vectorOftempInst.push_back(Inst);
					Q.push(Inst);
				//}
      			}
    		}
  	}
}
	
bool PrePointerAnalysis(StoreInst * SInst, Instruction * LInst, Value * Pointer, set<Instruction *> &Set, queue<Instruction *> &Q)
{
	bool svf_only = false;
	if ((SInst->getParent()->getParent() != LInst->getParent()->getParent()) && IsIP)
	{
		#ifdef DEBUGE
		outs() << "SVF_ONLY: " << SInst->getParent()->getParent()->getName().str() << " vs " << LInst->getParent()->getParent()->getName().str() << "\n";	
		outs() << "SInst: " << *SInst << "\n";
		outs() << "LInst: " << *LInst << "\n";
		#endif
		svf_only = true;
	}
	if (SInst->getPointerOperand() == Pointer)
	{
		//outs() << "Direct Store " << *SInst << " to value  " << *Pointer << "\n";
		if (svf_only)
		{
			includeTheStoreIntoASet(SInst);
		}else
		{
			enqueueInst(SInst, Set, Q, false);
			return true;
		}
	}else 
	{
		switch (pointerAlias(SInst->getPointerOperand()->stripPointerCasts(), Pointer->stripPointerCasts(), SInst->getModule()->getDataLayout(), svf_only)) 
		{
          		case AliasResult::NoAlias:
				#ifdef DEBUGE
				outs() << "NoAlias(p): " << *SInst << " and " << *Pointer << "\n";
				outs() << "NoAlias(i): " << *SInst << " and " << *LInst << "\n";
				#endif
           			break;
          		case AliasResult::MayAlias:
				#ifdef DEBUGE
				outs() << "They do alias somehow with " << *SInst << " and " << *Pointer << " \n";
				#endif
				if (RuleAlias)
				{
					if (svf_only)
					{
						#ifdef DEBUGE
						outs() << "They do alias with may" << *SInst << " and " << *Pointer << " \n";
						#endif
						includeTheStoreIntoASet(SInst);
					}else
					{
						#ifdef DEBUGE
						outs() << "They do alias with may" << *SInst << " and " << *Pointer << " \n";
						#endif
              					enqueueInst(SInst, Set, Q, false);
					}
				}
				break;
          		case AliasResult::PartialAlias:
				//outs() << "They do alias somehow with " << *SInst << " and " << *Pointer << " \n";
				if (RuleAlias)
				{
					if (svf_only)
					{
						#ifdef DEBUGE
						outs() << "They do alias with part" << *SInst << " and " << *Pointer << " \n";
						#endif
						includeTheStoreIntoASet(SInst);
					}else
					{
						#ifdef DEBUGE
						outs() << "They do alias with part" << *SInst << " and " << *Pointer << " \n";
						#endif
              					enqueueInst(SInst, Set, Q, false);
					}
				}
				break;
			default:
				if (svf_only)
				{
					#ifdef DEBUGE
					outs() << "MustAlias(p): " << *SInst << " and " << *Pointer << " \n";
					outs() << "MustAlias(i): " << *SInst << " and " << *LInst << " \n";
					#endif
					includeTheStoreIntoASet(SInst);
				}else
				{
              				enqueueInst(SInst, Set, Q, false);
					#ifdef DEBUGE
	  				outs() << "Stoped looking at " << *SInst << "\n"; 
					#endif
					return true;
				}
				break;
						
          	}
	}
}

/*void collectPotentiallyReachable(Function * F, vector<Instructions *> &CIs, vector<Instruction *> &FuncLeft)
{
	llvm::DominatorTree DTI = llvm::DominatorTree();
	DTI.recalculate(*F);
	bool couldBeATarget = true;
	for (int i = 0; i < CIs.size() - 1; i++)
	{
		couldBeATarget = true;
		//outs() << "MARINA_DEBUG: the round starts\n";
		for (int j = i + 1; j < CIs.size(); j++)
		{
			//outs() << "What a fuck is going on?\n";
			//outs() << "From: " << *CIs[i] << " To: " << *CIs[j] << "\n";
			if (isPotentiallyReachable(CIs[i], CIs[j], &DTI, nullptr))
			{
						//outs() << "Potentialy reachable\n";
						//outs() << "From: " << *CIs[i] << " To: " << *CIs[j] << "\n";
						couldBeATarget = false; 
						break;
						//It is not the target
						//Not precisecly of course	
			}
		}
		if (couldBeATarget)
		{
					if (std::find(FuncLeft.begin(), FuncLeft.end(), CIs[i]) == FuncLeft.end())
					{
						if (CallInst * CI = dyn_cast<CallInst>(CIs[i]))
						{
							Function * tempFunc = CI->getCalledFunction();
							if (tempFunc->getName().find(FUNCTION_MARKING) != string::npos || tempFunc->getName().find(LOOP_MARKING) != string::npos || tempFunc->getName().find(TX_MARKING) != string::npos)
							{
								//outs() << "This is a target: " << *CIs[i] << "\n";
								FuncLeft.push_back(CIs[i]);
							}
						}
					}
		}
				//outs() << "MARINA_DEBUG: the next round of checks\n";
	}

}*/

bool isCalledFromOrJustBefore(Function* CheckedFunction, Function* TargetedFunction, vector<Function* > &Seen)
{
	Seen.push_back(CheckedFunction);
	int iter = 0;
	for (Function *f: vectorOfFunctions)
	{
		#ifdef DEBUGE
		outs() << "IPINFO F1: " << f->getName().str() << " F2: " << fun->getName().str() << "\n";
		#endif
		//if (f->getName().str().find(fun->getName().str()) != string::npos)
		if (f == CheckedFunction)
		{
			#ifdef DEBUGE
			outs() << "IPINFO: Got it!\n";
			#endif
			break;
		} 
		iter++;
	}
	if (iter == vectorOfFunctions.size())
	{
		outs() << "IPERROR: vectors of Functions are wrong for" << CheckedFunction->getName().str() << "\n";
		return false;
	}
	for (Function* FF: (*vectorOfcalledFunctionsSets)[iter])
	{
		if (FF = TargetedFunction)
		{
			return true;
		}else
		{
			if (find(Seen.begin(), Seen.end(), FF) == Seen.end())
			{
				if (isCalledFromOrJustBefore(FF, TargetedFunction, Seen))
				{
					return true;
				}
			}
		}
	}
	return false;
}

// Adds all StoreInsts that could be responsible for the value read
// by LInst
// InterProcedural Analysis
void enqueueStoresIP(Value* Pointer, Instruction *LInst, vector<Function *> &FuncChain, set<Instruction *> &Set, queue<Instruction *> &Q, int rule, vector<Function* > &Seen, bool initial) {
    	//No need to process the whole function if 
    	//Pointer is constant
	//outs() << "enqueueStoresIP: start\n";
    	/*if (!PointerType::classof(Pointer->getType()))
    	{
		outs() << "Not a pointer\n";
		return;
    	}*/
	StringRef Kind = "DAE-interproc";
	StringRef Kind1 = "DAE-interproc-calledfrom";
	vector<Function *> TailFunctions;
	//int count = 0;
	outs() << "LInst from " << LInst->getParent()->getParent()->getName().str() << " is processed \n";
	for (auto F : FuncChain)
	{
		//count++;
		Seen.push_back(F);
		if (F == nullptr || F == NULL)
		{
			continue;
		}
		outs() << "Init: " << initial << " \n";
		if (!isa<Function>(F))
		{
			continue;
			//outs() << "Function in process: " << *F << "\n";
		}
		vector<Function *> Seen_local;
		bool CalledFrom = isCalledFromOrJustBefore(F, LInst->getParent()->getParent(), Seen_local);
		//outs() << "Just function: " << *F << "\n";
		//outs() << "Just function: " << F->getName().str() << "\n";
		//initial means that the enqueueStoresIP function is called the first time
		//During this time outside functions are processed
		//Next times, "inside" functions are processed.
		//Examples of inside functions:
		//func:
		//	func1:
		//		func2:
		//	func3:
		//		func_target:
		//			func1_inside
		//			func2_inside
		//			load 
		if (F->hasFnAttribute(Kind) || !CalledFrom || !initial)
		{
			//Here we need all Stores and all functions
			outs() << "Loop-related or called from related: " << F->getName().str() << "\n";
			for (auto inst = inst_begin(F); inst != inst_end(F); inst++)
			{
				if (StoreInst * SI = dyn_cast<StoreInst>(&*inst))
				{
					PrePointerAnalysis(SI, LInst, Pointer, Set, Q);
				}else if (CallInst * CI = dyn_cast<CallInst>(&*inst))
				{
					Function * FF = getFunction(CI);
					StringRef name = getFuncName(CI);
					//outs() << "Tail function " << name << "\n";
					if (FF != nullptr && FF != NULL && ((name.find(FUNCTION_MARKING) != string::npos) || (name.find(LOOP_MARKING) != string::npos) || (name.find(TX_MARKING) != string::npos)))
					{
						if (find(Seen.begin(), Seen.end(), FF) == Seen.end())
						{
							Seen.push_back(FF);
							//outs() << "Tail function accepted " << name << "\n";
							TailFunctions.push_back(FF);
						}
					}
				}
			}
		}else if (F == LInst->getParent()->getParent())// The function itself
		{
			outs() << "Func-itself: " << F->getName().str() << "\n";
			llvm::DominatorTree DTI = llvm::DominatorTree();
			DTI.recalculate(*F);
			enqueueStores(Pointer, LInst, LInst, Set, Q, rule);
			for (auto inst = inst_begin(F); inst != inst_end(F); inst++)
			{
				if (CallInst * CI = dyn_cast<CallInst>(&*inst))
				{
					Function * tempF = getFunction(CI);
					StringRef name = getFuncName(CI);
					//outs() << "Tail function " << name << "\n";
					if (tempF != nullptr && tempF != NULL && ((name.find(FUNCTION_MARKING) != string::npos) || (name.find(LOOP_MARKING) != string::npos) || (name.find(TX_MARKING) != string::npos)))
					{
						if (isPotentiallyReachable(&*inst, LInst, &DTI, nullptr))
						{
							if (find(Seen.begin(), Seen.end(), tempF) == Seen.end())
							{
								Seen.push_back(tempF);
								//outs() << "MARINA_DEBUG: a call to a function " << *CI << "\n";
								//outs() << "Tail function accepted " << name << "\n";
								//CIs.push_back(dyn_cast<Instruction>(CI));
								TailFunctions.push_back(tempF);
							}
						}
					}
				}
			}
		}else if (F != LInst->getParent()->getParent())//if it is not the function itself
		{
			// Example:
			// 	func:
			// 		call func1:
			// 			call func1_inside
			// 		call func2:
			// 			call func_targeted
			// 		call something_else
			// CASE1: If it is the func1, we need to fully process it (func1_inside will be processed separetely)
			// CASE2: if it is the func, we need to process it starting with the "call func2" upwards
			//
			//Because it is how we collect FuncChains, call something_else will not be ideally in the FuncChain vector
			//
			//here we need only stores that "dominate" the instruction
			//The question is how to identify it
			//Technically if we have all called functions that are at the same time inside FuncChain
			//we know that one of them is the targeted instruction
			//The thing is that only one
			//How do we pick the latest?
			//outs() << "Function chain: " << F->getName().str() << "\n";
			//outs() << "MARINA_DEBUG: calculated a dominator tree\n";
			vector<Instruction *> CIs;
			outs() << "CalledFrom: " << F->getName().str() << "\n";
			for (auto inst = inst_begin(F); inst != inst_end(F); inst++)
			{
				if (CallInst * CI = dyn_cast<CallInst>(&*inst))
				{
					Function * tempF = getFunction(CI);
					if (tempF != nullptr)
					{
						if (find(FuncChain.begin(), FuncChain.end(), tempF) != FuncChain.end())
						{
							//outs() << "MARINA_DEBUG: a call to a function " << *CI << "\n";
							//CIs.push_back(dyn_cast<Instruction>(CI));
							enqueueStores(Pointer, LInst, dyn_cast<Instruction>(CI), Set, Q, rule);
							for (auto inst = inst_begin(tempF); inst != inst_end(tempF); inst++)
							{
								if (CallInst * CII = dyn_cast<CallInst>(&*inst))
								{
									Function * FF = getFunction(CII);
									StringRef name = getFuncName(CII);
									//outs() << "Tail function " << name << "\n";
									if (FF != nullptr  && FF != NULL && ((name.find(FUNCTION_MARKING) != string::npos) || (name.find(LOOP_MARKING) != string::npos) || (name.find(TX_MARKING) != string::npos)))
									{
										if (find(Seen.begin(), Seen.end(), FF) == Seen.end())
										{
											Seen.push_back(FF);
											//outs() << "Tail function accepted " << name << "\n";
											TailFunctions.push_back(FF);
										}
									}
								}
							}

						}
					}
				}
			}
		}		
	}
	//outs() << "enqueueStoresIP end\n";
	if (TailFunctions.size() != 0)
	{
		enqueueStoresIP(Pointer, LInst, TailFunctions, Set, Q, rule, Seen, 0);
	}
	
}

  // Returns true if Pointer doe
  // Adds all StoreInsts that could be responsible for the value read
  // by LInst to Set and Q under the same condition as in enqueueInst.
  void enqueueStores(Value* Pointer, Instruction *LInst, Instruction *FInst, set<Instruction *> &Set,
                     queue<Instruction *> &Q, int rule) {
    //No need to process the whole function if 
    //Pointer is constant
    if (Pointer == NULL)
    {
	//outs() << "Not a pointer\n";
	return;
    }
    BasicBlock *loadBB = FInst->getParent();
    //loadBB->printAsOperand(outs(), false);
    //Value *Pointer = LInst->getPointerOperand();
    queue<BasicBlock *> BBQ;
    set<BasicBlock *> BBSet;
    BBQ.push(loadBB);
    bool first = true;
    bool found = false;
    //llvm::DominatorTree DTI = llvm::DominatorTree();
    //DTI.recalculate(*(loadBB->getParent()));
    while (!BBQ.empty()) {
      BasicBlock *BB = BBQ.front();
	//outs() << "Current blocki:\n";
	//BB->printAsOperand(outs(), false);
	//outs() << "\n";
      BBQ.pop();
      //found = false;

      BasicBlock::reverse_iterator RI(FInst->getIterator());
      for (BasicBlock::reverse_iterator iI = first ? RI : BB->rbegin(), iE = BB->rend(); iI != iE; ++iI) 
	{
	
	//if we have a situation:
	//call func(%5)
	//load %5
	//
	//func(%5):
	//	store %5
	//This situation will be captured by enqueueArgs
	//And we actually can not do it, because instructions inside other functions belong to those functions
	//
	//
	//But if in case of the following situation:
	//call func()
	//load * addr_global
	//
	//func():
	//   store *addr_global
	//
	//the store will be missed in the AP_func
	//
	//
	//
	//
	//INTER_PROCEDURAL ANALYSIS!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	//Do it only for loads
	/*if (IsIP && isa<LoadInst>(LInst) && !found)	
	{
		if (CallInst::classof(&(*iI)))
		{
			CallInst *CI = dyn_cast<CallInst>(&(*iI));
			Function *fun = CI->getCalledFunction();
			if (fun == NULL)
			{
				if (auto *CstExpr = dyn_cast<ConstantExpr>(CI->getOperand(0)))
				{
					if (CstExpr->isCast())
					{
						// In this category we have call %1
						// I guess we also need to take care of it
						if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
						{
							if (bitcastFunction == NULL || bitcastFunction->isIntrinsic())
							{
								continue;
							}
							//outs() << "Prevet\n";
							//name = bitcastFunction->getName();
							//outs() << "Poka\n";
							fun = bitcastFunction;
							//bitcast_flag = true;
							//bitcast = true;
							//return false;
						}
					}
				}
			}

			StringRef funName = getFuncName(CI);
			if (funName != "inderect call")
			{
				if (!fun->isDeclaration())
				{
					#ifdef DEBUGE
					outs() << "INTER-PROCEDURAL HELL with a function " << funName<< "!\n";
					#endif
					for (auto &BB: *fun)
					{
						if(BBSet.insert(&BB).second)
						{
							BBQ.push(&BB);
						}
					}
				}	
			}
		}
	}*/
	//INTER_PROCEDURAL ANALYSIS STOPS HERE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	//We need to find the closets store that dominates this load, right?
        if (StoreInst::classof(&(*iI))) {
          	StoreInst *SInst = (StoreInst *)&(*iI);
		//outs() << "Store instruction " << *SInst << "\n";
		//if (Instruction * inst = dyn_cast<Instruction>(Pointer))
		//{
		//If we go backwards we do not need to check for domination
		/*if (!DTI.dominates(&*iI, LInst))
		{
			if (StoreInst::classof(LInst))
			{	
				//outs() << "Instruction " << *iI << "does not dominate " << *LInst << "\n";
			}
			continue;		
		}*/
		/*if (StoreInst::classof(LInst))
		{	
			outs() << "Instruction " << *iI << " DOMINATE  " << *LInst << "\n";
		}*/
		//}
		if (!TransAP)
		{
			bool svf_only = false;
          		switch (pointerAlias(SInst->getPointerOperand()->stripPointerCasts(), Pointer->stripPointerCasts(),
                               iI->getModule()->getDataLayout(), svf_only)) {
          				case AliasResult::MustAlias:
            					if ((FollowRules::FollowMust == rule) || (rule == FollowRules::FollowPartial) || (rule == FollowRules::FollowMay)) {
              						//found = true;
              						enqueueInst(SInst, Set, Q, false);
							found = true;
            					}
            					break;
          				case AliasResult::PartialAlias:
            					if ((rule == FollowRules::FollowPartial) || (rule = FollowRules::FollowMay)) {
              						enqueueInst(SInst, Set, Q, false);
            					}
            					break;
          				case AliasResult::MayAlias:
            					if (rule == FollowRules::FollowMay) {
              					enqueueInst(SInst, Set, Q, false);
            					}
            					break;
          				case AliasResult::NoAlias:
           					 break;
          			}
		}else
		{
			if (PrePointerAnalysis(SInst, LInst, Pointer, Set, Q))
			{
				found = true;
			}
			/*bool svf_only = false;
			if ((SInst->getParent()->getParent() != LInst->getParent()->getParent()) && IsIP)
			{
				#ifdef DEBUGE
				outs() << "SVF_ONLY: " << SInst->getParent()->getParent()->getName().str() << " vs " << LInst->getParent()->getParent()->getName().str() << "\n";
				outs() << "SInst: " << *SInst << "\n";
				outs() << "LInst: " << *LInst << "\n";
				#endif
				svf_only = true;
			}
			if (SInst->getPointerOperand() == Pointer)
			{
				outs() << "Direct Store " << *SInst << " to value  " << *Pointer << "\n";
				if (svf_only)
				{
					includeTheStoreIntoASet(SInst);
				}else
				{
					enqueueInst(SInst, Set, Q, false);
					found = true;
				}
			}else 
			//if ((isa<GlobalVariable>(SInst->getPointerOperand()) && isa<GlobalVariable>(Pointer)) || (!isa<GlobalVariable>(SInst->getPointerOperand()) && !isa<GlobalVariable>(Pointer)))
			{
				//includeTheStoreIntoASet(SInst);
				switch (pointerAlias(SInst->getPointerOperand()->stripPointerCasts(), Pointer->stripPointerCasts(),
                               	SInst->getModule()->getDataLayout(), svf_only)) {
          					case AliasResult::NoAlias:
							outs() << "NoAlias" << *iI << " and " << *Pointer << "\n";
           					 	break;
          					case AliasResult::MayAlias:
							outs() << "They do alias somehow with " << *iI << " and " << *Pointer << " \n";
							if (RuleAlias && (rule == 0))
							{
								if (svf_only)
								{
									#ifdef DEBUGE
									outs() << "They do alias with may" << *iI << " and " << *Pointer << " \n";
									#endif
									includeTheStoreIntoASet(SInst);
								}else
								{
									#ifdef DEBUGE
									outs() << "They do alias with may" << *iI << " and " << *Pointer << " \n";
									#endif
              								enqueueInst(SInst, Set, Q, false);
								}
							}
							break;
          					case AliasResult::PartialAlias:
							outs() << "They do alias somehow with " << *iI << " and " << *Pointer << " \n";
							if (RuleAlias && (rule == 0))
							{
								if (svf_only)
								{
									#ifdef DEBUGE
									outs() << "They do alias with part" << *iI << " and " << *Pointer << " \n";
									#endif
									includeTheStoreIntoASet(SInst);
								}else
								{
									#ifdef DEBUGE
									outs() << "They do alias with part" << *iI << " and " << *Pointer << " \n";
									#endif
              								enqueueInst(SInst, Set, Q, false);
								}
							}
							break;
						default:
							if (svf_only)
							{
								#ifdef DEBUGE
								outs() << "They do alias with must" << *iI << " and " << *Pointer << " \n";
								#endif
								includeTheStoreIntoASet(SInst);
							}else
							{
              							enqueueInst(SInst, Set, Q, false);
								#ifdef DEBUGE
	  							outs() << "Stoped looking at " << *SInst << "\n"; 
								#endif
								found = true;
							}
							break;
						
          				}
			}*/


		}
        } else if (Pointer == &(*iI)) {
	//Calrify it
		#ifdef DEBUGE
	  //outs() << "Stoped looking at " << *iI << "\n"; 
		#endif
          found = true;
        }
      }
      if (!found) {
        for (pred_iterator pI = pred_begin(BB), pE = pred_end(BB); pI != pE;
             ++pI) {
          if (BBSet.insert(*pI).second) {
		//(*pI)->printAsOperand(outs(), false);
		//outs() << "\n";
            	BBQ.push(*pI);
          }
        }
      }
      first = false;
    }
  }

  // Returns true if Pointer does have a local destination.
  bool isLocalPointer(Value *Pointer) {
    //outs() << "¤%& " << *Pointer << "\n";
    if (!Instruction::classof(Pointer)) {
      return false;
    }
    Instruction *PtrInst = (Instruction *)Pointer;
    if (AllocaInst::classof(Pointer)) {
      // A locally defined memory location
      return true;
    }
    unsigned poi;
    if (GetElementPtrInst::classof(Pointer)) {
      poi = GetElementPtrInst::getPointerOperandIndex();
    } else if (CastInst::classof(Pointer)) {
      poi = 0; // The only operand
    } else if (LoadInst::classof(Pointer)) {
      // Assumes that global pointers are never stored in local
      // structures. Otherwise this could produce false positives.
      poi = LoadInst::getPointerOperandIndex();
    } else {
      return false;
    }
    Value *Pointer2 = PtrInst->getOperand(poi);
    return isLocalPointer(Pointer2);
  }

  // Convenience call
  bool isNonLocalPointer(Value *Pointer) { return !isLocalPointer(Pointer); }

  // Checks if two pointers alias
  AliasResult pointerAlias(Value *P1_in, Value *P2_in, const DataLayout &DL, bool svf_only) {
	AliasResult svfres = AliasResult::MustAlias;
	Value *P1 = P1_in->stripPointerCasts();
	Value *P2 = P2_in->stripPointerCasts();
	#ifdef DEBUGE
    	outs() << "pointerAlias for " << *P1 << " and " << *P2 << "\n";
	#endif
    	uint64_t P1Size = MemoryLocation::UnknownSize;
    	if (PointerType::classof(P1->getType()))
	{
		//outs() << "P1 " << *P1 << " is a pointer\n";
   		if (Type *P1ElTy = dyn_cast<PointerType>(P1->getType())->getElementType())
    		{
    			if (P1ElTy->isSized()) {
      				P1Size = DL.getTypeStoreSize(P1ElTy);
			}

    			uint64_t P2Size = MemoryLocation::UnknownSize;
			if (PointerType::classof(P2->getType()))
			{
				//outs() << "P2 " << *P2 << " is a pointer\n";
    				if (Type *P2ElTy = dyn_cast<PointerType>(P2->getType())->getElementType())
				{
    					if (P2ElTy->isSized()) {
						//Just to check if both globals
						if (P1 == P2)
						{
								//outs() << "Point to the same global variables\n";
								return AliasResult::MustAlias;
						}
						// This is a standart AA
						AliasResult AAres = AliasResult::MustAlias;
						if (!svf_only)
						{
      							P2Size = DL.getTypeStoreSize(P2ElTy);
      							AliasAnalysis * AAL = AAV[AAV.size()-1];
      							AAres = AA->alias(P1, P1Size, P2, P2Size);
							if (AAres == AliasResult::NoAlias)
							{
								#ifdef DEBUGE
								outs() << "AA: no alias\n";
								#endif
							}
							if (AAres == AliasResult::MustAlias)
							{
								#ifdef DEBUGE
								outs() << "AA: must alias\n";
								#endif
							}
							if (AAres == AliasResult::MayAlias)
							{
								#ifdef DEBUGE
								outs() << "AA: may alias\n";
								#endif
							}
							if (AAres == AliasResult::PartialAlias)
							{
								#ifdef DEBUGE
								outs() << "AA: part alias\n";
								#endif
							}
							//return AAres;
						}
						
						if (wpa_available && !svf_only)
						{
							/*if (isa<Instruction>(P1))
							{
								for (int op = 0; op < cast<Instruction>(P1)->getNumOperands(); op++)
								{
									svfres = pointerAlias((cast<Instruction>(P1))->getOperand(op), P2, cast<Instruction>(P1)->getModule()->getDataLayout(), true);
									if (svfres == AliasResult::MayAlias || svfres == AliasResult::MustAlias)
									{
										break;
									}
										
								}
							}else
							{
								svfres = svf->alias(P1, P2);
							}*/

							svfres = svf->alias(P1, P2);
							if (svfres == AliasResult::NoAlias)
							{
								#ifdef DEBUGE
								outs() << "sfv: no alias\n";
								#endif
							}
							if (svfres == AliasResult::MustAlias)
							{
								#ifdef DEBUGE
								outs() << "svf: must alias\n";
								#endif
							}
							if (svfres == AliasResult::MayAlias)
							{
								#ifdef DEBUGE
								outs() << "svf: may alias\n";
								#endif
							}
							if (svfres == AliasResult::PartialAlias)
							{
								#ifdef DEBUGE
								outs() << "svf: part alias\n";
								#endif
							}

							if (AAres == AliasResult::MustAlias)
							{
								return AliasResult::MustAlias;
							}else //TODO: Questionable thing
							if (svfres == AliasResult::NoAlias && AAres == AliasResult::PartialAlias)
							{
								return AliasResult::MayAlias;
							}else
							if (svfres == AliasResult::NoAlias || AAres == AliasResult::NoAlias)
							{
								return AliasResult::NoAlias;
							}
							{
								return svfres;
							}
						}else if (wpa_available && svf_only)
						{
							#ifdef DEBUGE
							outs() << "SVF results: \n";
							#endif
							svfres = svf->alias(P1, P2);
							if (svfres == AliasResult::NoAlias)
							{
								#ifdef DEBUGE
								outs() << "sfv: no alias\n";
								#endif
								return svfres;
							}else
							{
								#ifdef DEBUGE
								outs() << "sfv: may alias\n";
								#endif
								return AliasResult::MustAlias;
							}
							/*if (isa<Instruction>(P1))
							{
								for (int op = 0; op < cast<Instruction>(P1)->getNumOperands(); op++)
								{
									svfres = pointerAlias((cast<Instruction>(P1))->getOperand(op), P2, cast<Instruction>(P1)->getModule()->getDataLayout(), true);
									if (svfres == AliasResult::MayAlias || svfres == AliasResult::MustAlias)
									{
										return svfres;
									}
										
								}
							}else
							{
								return svf->alias(P1, P2);
							}*/
						}else
						if (!wpa_available && svf_only)
						{
							outs() << "ERROR: PointerALiasAnalysis !wpa_available && svf_only\n";
							return AliasResult::MayAlias;
						}else
						{
							return AAres;
						}
					}
				}
			}
		}
    	}
 	//return AliasResult::NoAlias;
 	return svfres;
}

void removeUnlisted(Function &F, set<Instruction *> &KeepSet) {
	#ifdef DEBUGE
	outs() << "REMOVE UNLISTED\n";
	#endif
    set<Instruction *>::iterator ksI = KeepSet.begin(), ksE = KeepSet.end();
    for (inst_iterator iI = inst_begin(F), iE = inst_end(F); iI != iE;) {
      Instruction *Inst = &(*iI);
      ++iI;
      if (find(ksI, ksE, Inst) == ksE) {
        Inst->replaceAllUsesWith(UndefValue::get(Inst->getType()));
	#ifdef DEBUGE
	outs() << "Erased!!!!" << *Inst << "\n";
	#endif
        Inst->eraseFromParent();
      }
    }
 }

// Inserts a prefetch for every LoadInst in toPref
// that fulfils the criterion of being inserted.
// All prefetches to be kept are added to toKeep
// (more unqualified prefetches may be added to the function).
// Returns the number of inserted prefetches.
int insertPrefetches(list<LoadInst *> &toPref, set<Instruction *> &toKeep,
                       bool printRes, bool onlyPrintOnSuccess) {
    int total = 0, ins = 0, bad = 0, indir = 0, red = 0;
    map<LoadInst *, pair<CastInst *, CallInst *>> prefs;
    set<Instruction *> prefToKeep;
    // Insert prefetches
    for (list<LoadInst *>::iterator I = toPref.begin(), E = toPref.end();
         I != E; I++) {
      switch (insertPrefetch(*I, prefToKeep, prefs)) {
      case Inserted:
        ++ins;
        break;
      case BadDeps:
        ++bad;
        break;
      case IndirLimit:
        ++indir;
        break;
      case Redundant:
        ++red;
        break;
      }
    }
    // Remove unqualified prefetches from toKeep
    //if (!KeepRedPrefs) {
      for (map<LoadInst *, pair<CastInst *, CallInst *>>::iterator
               I = prefs.begin(),
               E = prefs.end();
           I != E; ++I) {
        LoadInst *LInst = I->first;
        if (prefToKeep.count(LInst) != 0) {
          // Load present - remove prefetch
          CastInst *Cast = I->second.first;
          CallInst *Prefetch = I->second.second;
          prefToKeep.erase(Cast);
          prefToKeep.erase(Prefetch);
          ++red;
        }
      }
    //}
    toKeep.insert(prefToKeep.begin(), prefToKeep.end());
    // Print results
    if (printRes && (!onlyPrintOnSuccess || ins > 0)) {
      total = ins + bad + indir;
      //outs() << "\nPrefetches " << (*toKeep.begin())->getParent()->getParent()->getName().str() <<" : "
      //             << "Inserted: " << ins << "/" << total << "  (Bad: " << bad
      //             << "  Indir: " << indir << "  Red: " << red << ")\n";
    }
    return ins;
}

  // Inserts a prefetch for LInst as early as possible
  // (i.e. as soon as the adress has been computed).
  // The prefetch and all its dependencies will also
  // be inserted in toKeep.
  // Returns the result of the insertion.
  PrefInsertResult
  insertPrefetch(LoadInst *LInst, set<Instruction *> &toKeep,
                 map<LoadInst *, pair<CastInst *, CallInst *>> &prefs) {

    // Follow dependencies
    /*set<Instruction *> Deps;
    if (followDeps(LInst, Deps)) {
      if (isUnderThreshold(Deps)) {
        toKeep.insert(Deps.begin(), Deps.end());
      } else {
        return IndirLimit;
      }
    } else {
      return BadDeps;
    }*/

    // Extract usefull information
    bool prefetchExists = false;
    Value *DataPtr = LInst->getPointerOperand();
    BasicBlock *BB = LInst->getParent();
    BasicBlock *EntryBlock =
        &(LInst->getParent()->getParent()->getEntryBlock());
    for (map<LoadInst *, pair<CastInst *, CallInst *>>::iterator
             I = prefs.begin(),
             E = prefs.end();
         I != E; ++I) {
      LoadInst *LD = I->first;
      if (LD->getPointerOperand() == DataPtr) {
        // Might also be nullptr
        BasicBlock *LDBB = LD->getParent();
        if (BB == EntryBlock && LDBB == EntryBlock ||
            BB != EntryBlock && LDBB != EntryBlock) {
          prefetchExists = true;
          break;
        }
      }
    }

    if (prefetchExists) {
      return Redundant;
    }

    unsigned PtrAS = LInst->getPointerAddressSpace();
    LLVMContext &Context = DataPtr->getContext();

    // Make sure type is correct
    Instruction *InsertPoint = LInst;
    Type *I8Ptr = Type::getInt8PtrTy(Context, PtrAS);
    CastInst *Cast =
        CastInst::CreatePointerCast(DataPtr, I8Ptr, "", InsertPoint);

    // Insert prefetch
    IRBuilder<> Builder(InsertPoint);
    //outs() << "Load is detected " << *LInst << "\n";
    Module *M = LInst->getParent()->getParent()->getParent();
    Type *I32 = Type::getInt32Ty(LInst->getContext());
    Value *PrefFun = Intrinsic::getDeclaration(M, Intrinsic::prefetch);
    CallInst *Prefetch = Builder.CreateCall(
        PrefFun, {Cast, ConstantInt::get(I32, 0),                       // read
                  ConstantInt::get(I32, 3), ConstantInt::get(I32, 1)}); // data
    //outs() << "Prefetch is done\n";
    // Inset prefetch instructions into book keeping
    toKeep.insert(Cast);
    toKeep.insert(Prefetch);
    prefs.insert(make_pair(LInst, make_pair(Cast, Prefetch)));

    return Inserted;
  }

  bool isUnderThreshold(set<Instruction *> Deps) {
    //unsigned thresh = IndirThresh;
    unsigned thresh = 25;
    unsigned count = 0;
    for (set<Instruction *>::iterator dI = Deps.begin(), dE = Deps.end();
         dI != dE && count <= thresh; ++dI) {
      if (LoadInst::classof(*dI)) {
        ++count;
      }
    }
    return count <= thresh;
  }

 
