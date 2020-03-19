#include "llvm/Transforms/Utils/Local.h"

bool SimplifyCFGExclude(Function * F, TargetTransformInfo &TTI, unsigned bonusInstThreshold, vector<BasicBlock*> excludeList)
{
	bool modify = false; 
	Function::iterator bbI = F->begin(), bbE = F->end();
	while(bbI != bbE)
	{
		if (std::find(excludeList.begin(), excludeList.end(), &*bbI) == excludeList.end())
		{
			modify = SimplifyCFG(&*bbI, TTI, bonusInstThreshold);
		}else
		{ 
			modify = false;
		}
		if (modify)
		{
			bbI = F->begin();
		}else
		{
			bbI++;
		}	
	}
}

void simplifyCFG(Function *F, TargetTransformInfo &TTI)
{
	vector<BasicBlock*> excludeInCfg;
	excludeInCfg.push_back(&(F->getEntryBlock()));
	if (F->getEntryBlock().getTerminator()->getNumSuccessors() > 0)
	{
		excludeInCfg.push_back(F->getEntryBlock().getTerminator()->getSuccessor(0));
	}

	SimplifyCFGExclude(F, TTI, 0, excludeInCfg);
}
