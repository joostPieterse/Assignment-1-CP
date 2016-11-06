/*********************************************
Name: Chris Mens
Student number: 0770090
Email: c.m.mens@student.tue.nl

Name: Joost Pieterse
Student number: 0848231
Email: j.pieterse@student.tue.nl
 *********************************************/
using CP;

tuple Product {
	key int productId;
	string name;  
} 

tuple Demand {
	key string demandId;
	int productId;
	int quantity;
	int deliveryMin;
	int deliveryMax;
	float nonDeliveryVariableCost;
	int dueTime;
	float tardinessVariableCost;	 	
}

tuple Resource {
	key string resourceId;
	int resourceNr;
	string setupMatrix;
	int initialProductId;	
} 

tuple StorageTank {
	key string storageTankId;
	string name;
	int quantityMax;
	string setupMatrixId;
	int initialProductId;
}

tuple Step{
	key string stepId;
	int productId;
	string setupResourceId;
}
 tuple Precedence {
 	string predecessorId;
 	string successorId;
 	int delayMin;
 	int delayMax; 
 }

tuple Alternative {
	key string stepId;
	key int alternativeNumber;
	string resourceId;
	int fixedProcessingTime;
	float variableProcessingTime;
	float fixedProcessingCost;
	float variableProcessingCost;
}

tuple StorageProduction {
	key string prodStepId;
	key string storageTankId;
	string consStepId;
}

tuple setupMatrix {
	key string setupMatrixId;
	key int fromState;
	key int toState;
	int setupTime;
	int setupCost;
}

tuple Criterion {
	key string criterionId;
	float weight;
}
{Product} Products = ...;
{Demand} Demands = ...;
{Resource} Resources = ...;
{string} SetupResources = ...;
{StorageTank} StorageTanks = ...;
{Step} Steps = ...;
{Precedence} Precedences = ...;
{Alternative} Alternatives = ...;
{StorageProduction} StorageProductions = ...;
{setupMatrix} Setups = ...;
{Criterion} CriterionWeights = ...;


{int} productIds = {p.productId|p in Products};
float setupCostArray[Resources][productIds][productIds];
float setupTimeArray[Resources][productIds][productIds];

tuple DemandStep {
  Demand demand;
  Step step;
}
tuple DemandAlternative {
  Demand demand;
  Alternative alternative;
}

{DemandStep} DemSteps = {<d,s> | d in Demands, s in Steps: d.productId == s.productId};  

{DemandAlternative} DemandAlternatives = {<d,a> | d in Demands, a in Alternatives: d.productId==item(Steps, <a.stepId>).productId}; 
 
//interval for each demand (span of its steps)
dvar interval demands[d in Demands]
	optional(true)
	in 0..d.deliveryMax;

//interval for each relevant demand step combination (same product id)
dvar interval steps[<d,s> in DemSteps]
	optional(true);

//interval for each relevant demand alternative combination, only one is present per step
dvar interval alternatives[<d,a> in DemandAlternatives]
	optional(true)
	size   ftoi(round(a.fixedProcessingTime + a.variableProcessingTime * d.quantity));	
	
//interval for each time a setup resource is used
dvar interval setupResources[<d,s> in DemSteps]
	optional(true);	

//sequence giving the order in which resources are used
dvar sequence resourceUsage[r in Resources] in
	all(a in Alternatives, d in Demands:a.resourceId == r.resourceId && d.productId == item(Steps, <a.stepId>).productId) alternatives[<d,a>]
    types all(a in Alternatives, d in Demands:a.resourceId == r.resourceId && d.productId == item(Steps, <a.stepId>).productId) d.productId;

//interval indicating when a storage is being used
dvar interval storageResources[<d,s> in DemSteps][st in StorageTanks]
	optional(true);

//function that indicates the quantity in a storage tank at a certain time
cumulFunction storageUsageFunction[st in StorageTanks] = (sum(<d,s> in DemSteps, sp in StorageProductions:
	sp.prodStepId == s.stepId && sp.storageTankId == st.storageTankId) pulse(storageResources[<d,s>][st], d.quantity));


dexpr float NonDeliveryPerDemand[d in Demands] = (1-presenceOf(demands[d])) * d.quantity * d.nonDeliveryVariableCost;
dexpr float TotalNonDeliveryCost = sum(d in Demands) NonDeliveryPerDemand[d];

dexpr float processingCostPerStep[<d, s> in DemSteps] = sum(a in Alternatives:a.stepId == s.stepId)
	presenceOf(alternatives[<d,a>]) * (a.fixedProcessingCost + a.variableProcessingCost * d.quantity);
dexpr float TotalProcessingCost =  sum(d in Demands, s in Steps:d.productId == s.productId) processingCostPerStep[<d,s>];

dexpr float setupCostPerStep[<d, s> in DemSteps] =  sum(r in Resources:r.setupMatrix != "NULL") 
	sum(a in Alternatives:a.resourceId == r.resourceId && s.productId ==d.productId && a.stepId == s.stepId) 
	(typeOfPrev(resourceUsage[r], alternatives[<d,a>], r.initialProductId, -1)!=-1)*presenceOf(alternatives[<d,a>])*
	setupCostArray[r][typeOfPrev(resourceUsage[r], alternatives[<d,a>], (r.initialProductId>=0) * r.initialProductId, 0)][item(Steps, <a.stepId>).productId];
dexpr float TotalSetupCost = sum(d in Demands, s in Steps:d.productId == s.productId) setupCostPerStep[<d,s>];

dexpr float TardinessPerDemand[d in Demands] =  ((endOf(demands[d]) - d.dueTime)*(d.dueTime<endOf(demands[d])))*d.tardinessVariableCost;
dexpr float TotalTardinessCost = sum(d in Demands)TardinessPerDemand[d];

dexpr float WeightedTotalNonDeliveryCost = item(CriterionWeights,<"NonDeliveryCost">).weight * TotalNonDeliveryCost;
dexpr float WeightedTotalProcessingCost = item(CriterionWeights,  <"ProcessingCost">).weight * TotalProcessingCost;
dexpr float WeightedTotalSetupCost = item(CriterionWeights,  <"SetupCost">).weight * TotalSetupCost;
dexpr float WeightedTotalTardinessCost = item(CriterionWeights, <"TardinessCost">).weight * TotalTardinessCost;

execute{
	cp.param.Workers = 1;
	cp.param.TimeLimit = Opl.card(Demands);	
	
	//default
	cp.param.DefaultInferenceLevel = 5;
	
	//instance0:
	/*cp.param.DefaultInferenceLevel = 5;
	cp.param.RestartFailLimit = 70;
	var f = cp.factory;	
	cp.setSearchPhases(f.searchPhase(alternatives));*/
	
	//instance1:
	/*cp.param.DefaultInferenceLevel = 5;
	cp.param.RestartFailLimit = 70;
	var f = cp.factory;	
	cp.setSearchPhases(f.searchPhase(alternatives), f.searchPhase(steps));*/
	
	//instance2:
	/*cp.param.DefaultInferenceLevel = 4;
	cp.param.RestartFailLimit = 130;
	var f = cp.factory;	*/
	
	//instance3:
	/*cp.param.DefaultInferenceLevel = 5;
	cp.param.RestartFailLimit = 70;
	var f = cp.factory;	
	cp.setSearchPhases(f.searchPhase(alternatives));*/
	
	//instance 4:
	/*cp.param.DefaultInferenceLevel = 6;
	cp.param.RestartFailLimit = 70;
	var f = cp.factory;	
	cp.setSearchPhases(f.searchPhase(alternatives), f.searchPhase(steps));*/
		
	for(var r in Resources) {
       	for(var s in Setups) {
       		if(s.setupMatrixId == r.setupMatrix && r.setupMatrix != "NULL"){       	
       			setupCostArray[r][s.fromState][s.toState] = s.setupCost;  	
       			setupTimeArray[r][s.fromState][s.toState] = s.setupTime;
       		}       		
   		}				  
	}
}
tuple triplet {int loc1; int loc2; int value; };
{triplet} transitionTimes[r in Resources] = {<s.fromState, s.toState, s.setupTime>|s in Setups:s.setupMatrixId == r.setupMatrix };
{triplet} storageTransitions[st in StorageTanks] = {<s.fromState, s.toState, s.setupTime>|s in Setups:s.setupMatrixId == st.setupMatrixId };
//function that indicates the state of a tank at a certain time, while also taking setup times into account
stateFunction state[st in StorageTanks] with storageTransitions[st];

minimize WeightedTotalNonDeliveryCost + WeightedTotalTardinessCost + WeightedTotalProcessingCost + WeightedTotalSetupCost;

subject to{
	forall(d in Demands){
		//size of a demand interval corresponds to the size of all of its steps
		span(demands[d], all(s in Steps:s.productId==d.productId) steps[<d,s>]);
		forall(s in Steps:s.productId == d.productId){		
			//one alternative needs to be present if a step is present
			alternative(steps[<d,s>], all(a in Alternatives:a.stepId==s.stepId) alternatives[<d,a>]);	
			presenceOf(demands[d])==presenceOf(steps[<d,s>]);			
		}	
		forall(p in Precedences:item(Steps, <p.predecessorId>).productId==d.productId){
			//Each step should start within the delay period after the previous step	
			endBeforeStart(steps[<d,item(Steps, <p.predecessorId>)>], steps[<d,item(Steps, <p.successorId>)>], p.delayMin);						
			endOf(steps[<d,item(Steps, <p.predecessorId>)>], maxint) + p.delayMax >= startOf(steps[<d,item(Steps, <p.successorId>)>], -1000000);
		}	
		forall(r in Resources,a in Alternatives:d.productId == item(Steps, <a.stepId>).productId&&a.resourceId==r.resourceId && r.setupMatrix!="NULL"){
			//A setup resource is needed if there was a previous product id (so not -1) and the alternative is present
			//If both the time and the cost are 0, the setup resource is not needed
			//A setup resource usage ends when the setup is done (and the next step starts)
			(typeOfPrev(resourceUsage[r], alternatives[<d,a>], r.initialProductId, -1)!=-1 &&
				setupTimeArray[r][typeOfPrev(resourceUsage[r], alternatives[<d,a>], r.initialProductId)][d.productId]!=0) =>
				(endOf(setupResources[<d,item(Steps, <a.stepId>)>]) == startOf(alternatives[<d,a>]) && 
				sizeOf(setupResources[<d,item(Steps, <a.stepId>)>]) == 
				setupTimeArray[r][typeOfPrev(resourceUsage[r], alternatives[<d,a>], r.initialProductId)][d.productId]);						
		}	
		forall(sp in StorageProductions, s in Steps:item(Steps, <sp.prodStepId>).productId==d.productId && s.stepId == sp.prodStepId){
			//If there is time between steps, one storage resource is needed
			endOf(steps[<d,s>]) < startOf(steps[<d,item(Steps, <sp.consStepId>)>])=>
				(sum(sp in StorageProductions:sp.prodStepId == s.stepId) 
				(startOf(storageResources[<d,s>][item(StorageTanks, <sp.storageTankId>)]) == endOf(steps[<d,s>]) &&
				endOf(storageResources[<d,s>][item(StorageTanks, <sp.storageTankId>)]) == startOf(steps[<d,item(Steps, <sp.consStepId>)>]))==1);
			//After producing, at most 1 storage tank is used
			sum(st in StorageTanks) presenceOf(storageResources[<d,s>][st])==1;					
		}	
		//End of the demand needs to be after deliveryMin
		presenceOf(demands[d])=>(endOf(demands[d],maxint)>=d.deliveryMin);
	}
	forall(r in Resources){
		//Resource usage cannot overlap, taking transition times into account
		noOverlap(resourceUsage[r], transitionTimes[r]);
	}
	forall(sr in SetupResources){
		//setup resource usage cannot overlap
		noOverlap(all(s in Steps, d in Demands:s.setupResourceId==sr && d.productId==s.productId) setupResources[<d,s>]);									
	}	 
	forall(st in StorageTanks){
		//storage cannot exceed maximum quantity
		storageUsageFunction[st] <= st.quantityMax;	
		forall(s in Steps, sp in StorageProductions, d in Demands:d.productId == s.productId&&s.stepId == sp.prodStepId && st.storageTankId == sp.storageTankId){
			//The state (product id) of a storage resource must remain the same throughout the storage of a product
			alwaysEqual(state[st], storageResources[<d,s>][item(StorageTanks, <sp.storageTankId>)], s.productId, 0, 0);
		}	
	}
	
	//redundant constraints
	forall(d in Demands:d.tardinessVariableCost>0){
		presenceOf(demands[d])=>endOf(demands[d]) <= d.dueTime + (d.nonDeliveryVariableCost*d.quantity / d.tardinessVariableCost);
	}
}

tuple DemandAssignment {
  key string demandId;
  int startTime;       
  int endTime;
  float nonDeliveryCost;
  float tardinessCost;
};
 
{DemandAssignment} demandAssignments = {<d.demandId, startOf(demands[d]), endOf(demands[d]), NonDeliveryPerDemand[d], TardinessPerDemand[d]>|d in Demands};
 
tuple StepAssignment {
  key string demandId;
  key string stepId;   
  int startTime;       
  int endTime;
  string resourceId;
  float procCost;
  float setupCost;
  int startTimeSetup;
  int endTimeSetup;
  string setupResourceId;
};
 
{StepAssignment} stepAssignments = {<d.demandId, s.stepId, startOf(steps[<d,s>]), endOf(steps[<d,s>])
	, a.resourceId, processingCostPerStep[<d,s>], setupCostPerStep[<d,s>], startOf(setupResources[<d,s>]), endOf(setupResources[<d,s>])
	,s.setupResourceId>|s in Steps, d in Demands, a in Alternatives:d.productId==s.productId && s.stepId==a.stepId && presenceOf(alternatives[<d,a>])};
 
tuple StorageAssignment {
  key string demandId;
  key string prodStepId;   
  int startTime;       
  int endTime;
  int quantity;
  string storageTankId;
};
 
{StorageAssignment} storageAssignments = {<d.demandId, sp.prodStepId, startOf(storageResources[<d,s>][item(StorageTanks, <sp.storageTankId>)]), 
	endOf(storageResources[<d,s>][item(StorageTanks, <sp.storageTankId>)])
	, d.quantity, item(StorageTanks, <sp.storageTankId>).storageTankId>|<d,s> in DemSteps,sp in StorageProductions:
	sp.prodStepId == s.stepId && presenceOf(storageResources[<d,s>][item(StorageTanks, <sp.storageTankId>)]) };
 
 
execute {

    writeln("Total Non-Delivery Cost    : ", TotalNonDeliveryCost);
    writeln("Total Processing Cost      : ", TotalProcessingCost);
    writeln("Total Setup Cost           : ", TotalSetupCost);
    writeln("Total Tardiness Cost       : ", TotalTardinessCost);
    writeln();
    writeln("Weighted Non-Delivery Cost : ",WeightedTotalNonDeliveryCost);
    writeln("Weighted Processing Cost   : ", WeightedTotalProcessingCost);
    writeln("Weighted Setup Cost        : ", WeightedTotalSetupCost);
    writeln("Weighted Tardiness Cost    : ", WeightedTotalTardinessCost);
    writeln();
     
    for(var d in demandAssignments) {
        writeln(d.demandId, ": [",
                d.startTime, ",", d.endTime, "] ");
        writeln("   non-delivery cost: ", d.nonDeliveryCost,
                ", tardiness cost: " , d.tardinessCost);
    }
   
    writeln();
   
    for(var sa in stepAssignments) {
        writeln(sa.stepId, " of ", sa.demandId,
                ": [", sa.startTime, ",", sa.endTime, "] ",
                "on ", sa.resourceId);
        write("   processing cost: ", sa.procCost);
        if (sa.setupCost > 0)
          write(", setup cost: ", sa.setupCost);
        writeln();
        if (sa.startTimeSetup < sa.endTimeSetup)
            writeln("   setup step: [",
                    sa.startTimeSetup, ",", sa.endTimeSetup, "] ",
                    "on ", sa.setupResourceId);  
    }
    writeln();
 
    for(var sta in storageAssignments) {
      if (sta.startTime < sta.endTime) {
        writeln(sta.prodStepId, " of ", sta.demandId,
          " produces quantity ", sta.quantity,
            " in storage tank ", sta.storageTankId,
            " at time ", sta.startTime,
          " which is consumed at time ", sta.endTime); 
      }      
    }
}