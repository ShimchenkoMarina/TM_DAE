#pragma once
#include "llvm/ADT/Statistic.h"
#include "llvm/Pass.h"
#include "WPA/WPAPass.h"
#include "WPA/Andersen.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstVisitor.h"
//For handeling getelements inbounds
#include "../../../../../llvm/lib/IR/ConstantsContext.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"

//#include "../../Utils/SkelUtils/CallingDAE.cpp" 
#include "../../Utils/SkelUtils/Replace.cpp"
//To annotate branches 
#include "../../Utils/SkelUtils/SBPAnnotator.cpp" 
//DAE functionality
#include "../../Utils/SkelUtils/helperDAE.cpp" 
//Remove prefetch
#include "../../Utils/RemoveRedundantPref/RemoveRedundantPref.cpp" 
//Simplify
#include "../../Utils/DCE/DCEutils.cpp" 

#include "ostream"
#include "fstream"
#include "iostream"
#include <vector>
#include <algorithm>
#include <map>
#include <queue>
#include <set>
#include <stack>

#define KERNEL_MARKING "__kernel__tm__"
#define FUNCTION_MARKING "TMFUNC_"
#define TX_MARKING "TXFUNC_"//TXFUNC_MAIN_TMFUNC means extracted TM region
#define LOOP_MARKING "LOOPFUNC_"//Extracted loop
#define MAIN_FUNCTION_MARKING "MAIN_TMFUNC_"//Means function contains TM regions
#define FUNCTION_MARKING_SIZE (7) 
#define TX_MARKING_SIZE (7) 
#define MAIN_FUNCTION_MARKING_SIZE (12)
#define CLONE_SUFFIX "_clone"
 
static cl::opt<bool> AllocaNotAllowed(
    "allocno",
    cl::desc("Treat alloca inst as stores to global"));

static cl::opt<bool> AccessNotAllowed(
    "clear",
    cl::desc("Run pass without 3d phase"));

static cl::opt<bool> Oracle(
    "oracle",
    cl::desc("Oracle version"));

static cl::opt<bool> OracleCount(
    "OracleCount",
    cl::desc("If we need to count loads and stores for Oracles"));

static cl::opt<bool> MUSTMAYPART(
    "MUSTMAYPART",
    cl::desc("0 - MUST, 1 - MustMayPart"));

static cl::opt<bool> TAP(
    "TAP",
    cl::desc("0 - Normal AP, 1 - Transactional Access Phases"));

static cl::opt<bool> DUPL(
    "DUPL",
    cl::desc("0 - Normal AP, 1 - AP is a duplicate of TX"));

static cl::opt<bool> INLINEINNER(
    "INLINEINNER",
    cl::desc("Now it is for inlining: false - not inline, true - inline"));

static cl::opt<bool> NOREMOVE(
    "NOREMOVE",
    cl::desc("remove unlisted or not: false - remove; true - do not remove"));

static cl::opt<int> RTS(
    "RTS",
    cl::desc("Reasonable transaction size. If it is not specified - full access phase instead. Goes together with HALFTM(just for simplicity. Example: -HALTM -RTS 5000. Bad example: -RTS 5000, it does nothing)"));

static cl::opt<float> TSP(
    "TSP",
    cl::desc("transaction size percent. If it is not specified - full access phase instead. Goes together with HALFTM(just for simplicity. Example: -HALTM -RTS 0.5. Bad example: -RTS 0.5, it does nothing)"));

static cl::opt<bool> JUSTINLINE(
    "JUSTINLINE",
    cl::desc("Only inline all functions: false - mode is not active; true - mode is active"));

static cl::opt<bool> JUSTINLINE_BEFORE(
    "JUSTINLINE_BEFORE",
    cl::desc("Tells if JUSTINLINE pass was run before: false - no; true - yes"));

static cl::opt<bool> HALFTM(
    "HALFTM",
    cl::desc("AFTER means that cutting happens after AP was created. 0 - full TM; 1 - half TM. Works together with RTS ot TSP. Otherwise AP is full."));

static cl::opt<bool> HALFTMBEFORE(
    "HALFTMBEFORE",
    cl::desc("BEFORE means that cutting happens during an inlining stage. 0 - full TM; 1 - half TM. Works together with RTS ot TSP. Otherwise AP is full."));

static cl::opt<bool> NODELETEUNUSED(
    "NODELETEUNUSED",
    cl::desc("0 - delete(default version); 1 - do not delete"));

static cl::opt<bool> SVFPREP(
    "SVFPREP",
    cl::desc("0 - noSVF are goind to be used for not inlined version; 1 - SVF is needed for not inlined version. Some preparations are required."));

static cl::opt<bool> SVFDESIGN(
    "SVFDESIGN",
    cl::desc("0 - TMDAE without SVF; 1 - TMDAE with SVF"));

static cl::opt<bool> INTERPROC(
    "INTERPROC",
    cl::desc("0 - no inter-procedural analysis; 1 - analysis present"));

static cl::opt<bool> FilterFP(
    "FilterFP",
    cl::desc("0 - no filter; 1 - struct pointers"));


//Just in case, because yada benchmark compiles forever
static cl::opt<bool> YADASPECIALFLAG(
    "YADASPECIALFLAG",
    cl::desc("0 - not yada benchmark; 1 - yada benchmark"));


/*static cl::opt<bool> OutsideTMMild(
    "outsideTMMild",
    cl::desc("Locate access phase outside TM if it is possible"));
static cl::opt<bool> IgnoreUnresolvedTM(
    "ignore",
    cl::desc("Locate access phase outside TM if it is possible"));*/

/*#define DEBUG_TYPE "tm_pass"
STATISTIC(TotalNUMLoads, "Total number of loads");
STATISTIC(TotalNUMPrefetchedLoads, "Total number of prefetched loads");
STATISTIC(TotalNUMLoadsInsideLoops, "Total number of loads inside loops");
STATISTIC(TotalNUMLoadsDependOnLoads, "Total number of loads that depend on loads");
STATISTIC(TotalNUMTXInsideLoops, "Total number of TX regions that are inside loops");
STATISTIC(TotalNUMTX, "Total number of TX");
STATISTIC(TotalNUMFunctionCalls, "Total number of functions calls");
*/
int TotalNUMLoads = 0;
int TotalNUMPrefetchedLoads = 0;
int TotalNUMLoadsInsideLoops = 0;
int TotalNUMLoadsDependOnLoads = 0;
int TotalNUMTXInsideLoops = 0;
int TotalNUMTX = 0;
int TotalNUMFunctionCalls = 0;
int TotalNUMPrefetchedLoadsTMDAE = 0;

//int RTS = 5000; // RTS stands for Reasonable Transaction Size

using namespace llvm;
using namespace std;
namespace{


	class TM_DAE_INTGR_pass: public ModulePass{

	friend class StatisticInfo;

	public:
		static char ID;
		TM_DAE_INTGR_pass(): ModulePass(ID){
		};
		~TM_DAE_INTGR_pass(){};
		
		virtual void getAnalysisUsage(AnalysisUsage& AU) const{
			AU.addRequiredID(LoopSimplifyID);
			AU.addRequiredID(BreakCriticalEdgesID);
			AU.addRequired<AAResultsWrapperPass>();
			AU.addRequired<DominatorTreeWrapperPass>();
			AU.addRequired<LoopInfoWrapperPass>();
			AU.addRequired<AssumptionCacheTracker>();
			//AU.addRequired<ScalarEvolutionWrapperPass>();
			AU.addRequired<TargetLibraryInfoWrapperPass>();
			AU.addRequired<TargetTransformInfoWrapperPass>();
			AU.addRequired<BranchProbabilityInfoWrapperPass>();
			//AU.addRequired<WPAPass>();
		}

		//bool runOnFunction(Function &F);
		virtual bool runOnModule(Module &M);

	private:
		//*****************************Data*************************************************************
		//LoopInfo *LI;
		//std::vector<LoopInfo*> LIV;
		std::vector<std::pair<Function*, Instruction *>> TMtoInstMap;
		std::vector<LoopInfoBase<BasicBlock, Loop> *> LIBV;
		std::vector<Loop *> LoopV;
		//std::vector<Loop *> LV;
		std::vector<GlobalVariable *> GVV;
		AliasAnalysis *AA;
		BranchProbabilityInfo *BPI;
		WPAPass *wpa;
		RemoveRedundantPref *RRP;
		AndersenWaveDiff* svfResults;

		int GlobalCount = 0;
		int NumTXinFunc = 0;
		std::vector<std::vector<BasicBlock *>> TXBBs;
		std::vector<BasicBlock *> TXBB;
		Instruction *FirstInst;
		std::vector<Instruction *> FirstInstV;
		BasicBlock * FirstInnerBB = nullptr;
		std::vector<BasicBlock * > FirstInnerBBs;
		void insertCompilerMarkers_TAP(Function *);
		void insertCompilerMarkers(Function *);
		void count_LOADS_STORES_PREF(vector<Function *> &, Function *, int*, int*, int*, bool);

		bool txDetected = false;
		bool txInnerDetected = false;
		bool do_it_again = false;
		bool stop = false;
		//if TX is not inside loop then depth is 1 by default
		//Otherwise depth should be changed accordingly
		int loop_depth = 0;
		enum MODE{START, END, InnerEND};
		std::vector<std::pair<const char *, int>> InstList;//For statistic colecting, one for tx region
		
		//First purpose:Handle situation when BB cals itself. Don't want to go in the infinite loop.
		//Second purpose: Make one for the whole program to check whether this TX was visited
		std::vector<BasicBlock*>  		  UsedBBs;
		//SmallVector<Instruction *, 16> PrefLoads;

		ValueToValueMapTy vmap;
		std::vector<Instruction* > inst_vect;
		std::vector<Instruction *> TX_inst;
		std::vector<Value *> PrefetchedAddresses;
		std::vector<Instruction *> LoadNotPrefetch;
		std::vector<Value *> FunctionArgs;

		enum GLOBALREASON {DIRECTGLOBAL, ALIASGLOBAL, NOTGLOBAL};
		//*****************************Data*************************************************************
		



		//*****************************Servant**********************************************************
		//this function is for current purpose
		//void countInst(Instruction &Inst);	
		void PrintTxStatistics();
		StringRef get_function_name(CallInst *ci);
		void LoadVisibleDependencies(Instruction *);
		bool isInstInsideLoop(Instruction *, bool);
		std::pair<GLOBALREASON, Instruction *> isLoadGlobal(Instruction *);
		bool isLoadDependLoad();
		AliasResult pointerAlias(Value *, Value *, const DataLayout&);
		bool isAddressPrefetched(Instruction *);
		void markLoop(Loop *);
		//bool collectDL(list<Instruction *> *, Instruction *);
		//void prefetchDL(Function *,list<Instruction *> *, Instruction *);
		Instruction * getFirstTMInst(Function &);//Works with global data TMtoInstMap
		//BasicBlock * getTargetBB(BasicBlock &);
		Instruction * insertCheckDeps(Function *, Instruction *);
		Instruction * followAccessDeps(Instruction *, Instruction *);
		void deleteEmptyAccessPhase(Function *);
		void AnnotateBranchesLoop(Loop *);
		//*****************************Servant**********************************************************
		
		

		//*****************************Core*************************************************************
		//This function goes through the BB and checks whether there is fakeCallBegin call there
		//Identifies the beginning of TX region
		bool isTargetBB(BasicBlock &BB, MODE mode);
		//These two functions just mark targeted functions and loops
		bool MarkEverything(Function &, bool);
		void parseCallGraph(BasicBlock &, bool, bool);	
		void ExtractSubLoops(Loop *loop, DominatorTree *DTI, LoopInfo *);

		//TODO: come up with more appropriate function name
		//Core optimization function
		bool printTxRegionInst(BasicBlock &BB, Instruction*);
		void prefetchGlobalLoads();
		void notAggressivePrefetching(Instruction *, std::pair<GLOBALREASON, Instruction *> *);
		//*****************************Core*************************************************************
	};

char TM_DAE_INTGR_pass::ID = 0;
static RegisterPass<TM_DAE_INTGR_pass> X("tm_dae_intgr_pass", "TM_DAE_INTGR_pass was successfuly registered", false, false);
}
