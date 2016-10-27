/*********************************************
Name: Chris Mens
Student number:
Email:

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
int setupCostArray[Resources][productIds][productIds];
int setupTimeArray[Resources][productIds][productIds];

dvar interval demands[d in Demands]
	optional(true)
	in 0..d.deliveryMax;
	
dvar interval steps[s in Steps]
	optional(true);

dvar interval alternatives[a in Alternatives]
	optional(true)
	size   ftoi(round(a.fixedProcessingTime + a.variableProcessingTime * 
	sum(s in Steps:s.stepId==a.stepId) sum(d in Demands:d.productId==s.productId) d.quantity));	

dvar sequence resourceUsage[r in Resources] in
	all(a in Alternatives:a.resourceId == r.resourceId) alternatives[a]
	types all(a in Alternatives:a.resourceId == r.resourceId) sum(s in Steps:s.stepId == a.stepId) s.productId;
	
dexpr float TotalNonDeliveryCost = sum(d in Demands) (1-presenceOf(demands[d])) * d.quantity * d.nonDeliveryVariableCost;
dexpr float TotalProcessingCost = sum(a in Alternatives) presenceOf(alternatives[a]) * (a.fixedProcessingCost + 
a.variableProcessingCost * sum(s in Steps:s.stepId==a.stepId) sum(d in Demands:d.productId==s.productId) d.quantity);


dexpr float TotalSetupCost = 0;
dexpr float TotalTardinessCost = sum(d in Demands) ((endOf(demands[d]) - d.dueTime)*(d.dueTime<endOf(demands[d])));

dexpr float WeightedTotalNonDeliveryCost = item(CriterionWeights, ord(CriterionWeights, <"NonDeliveryCost">)).weight * TotalNonDeliveryCost;
dexpr float WeightedTotalProcessingCost = item(CriterionWeights, ord(CriterionWeights, <"ProcessingCost">)).weight * TotalProcessingCost;
dexpr float WeightedTotalSetupCost = item(CriterionWeights, ord(CriterionWeights, <"SetupCost">)).weight * TotalSetupCost;
dexpr float WeightedTotalTardinessCost = item(CriterionWeights, ord(CriterionWeights, <"TardinessCost">)).weight * TotalTardinessCost;

execute{
	cp.param.Workers = 1;
	//cp.param.TimeLimit = Opl.card(Demands);	
	for(var r in Resources) {
       	for(var s in Setups) {
       		if(s.setupMatrixId == r.setupMatrix && r.setupMatrix != "NULL"){       	
       		}       		
   		}				  
	}
}

minimize WeightedTotalNonDeliveryCost + WeightedTotalNonDeliveryCost + WeightedTotalTardinessCost;

subject to{
	forall(d in Demands){
		span(demands[d], all(s in Steps:s.productId==d.productId) steps[s]);
	}
	forall(s in Steps){
		alternative(steps[s], all(a in Alternatives:a.stepId==s.stepId) alternatives[a]);	
	}
	forall(p in Precedences){
		forall(s1 in Steps:s1.stepId==p.predecessorId){
			forall(s2 in Steps:s2.stepId==p.successorId){
				endOf(steps[s1], -1) + p.delayMin <= startOf(steps[s2], maxint);
				endOf(steps[s1], -1) + p.delayMax >= startOf(steps[s2], maxint);
			}				
		}
	}
	forall(r in Resources){
		noOverlap(all(a in Alternatives:a.resourceId==r.resourceId) alternatives[a]);
		forall(a1 in Alternatives:a1.resourceId==r.resourceId){					
			forall(a2 in Alternatives:a2.resourceId==r.resourceId && ord(Alternatives, a1) < ord(Alternatives, a2)){
				if(item(Steps, ord(Steps, <a1.stepId>)).productId != item(Steps, ord(Steps, <a2.stepId>)).productId){
					endOf(alternatives[a1], -1000) + setupTimeArray[r][item(Steps, ord(Steps, <a1.stepId>)).productId][item(Steps, ord(Steps, <a2.stepId>)).productId] <= startOf(alternatives[a2], 1000) ||	
					endOf(alternatives[a2], -1000) + setupTimeArray[r][item(Steps, ord(Steps, <a2.stepId>)).productId][item(Steps, ord(Steps, <a1.stepId>)).productId] <= startOf(alternatives[a1], 1000);		
				}	
			}		
		}
		/*forall(a in Alternatives:a.resourceId==r.resourceId){
			if(typeOfPrev(resourceUsage[r], alternatives[a], r.initialProductId, -1) != sum(s in Steps:s.stepId == a.stepId) s.productId
			&& typeOfPrev(resourceUsage[r], alternatives[a], r.initialProductId, -1) != -1){
				startOf(alternatives[a]) >= endOfPrev(resourceUsage[r], alternatives[a], -1, -1);
			}
		}*/
				
	}
}

tuple DemandAssignment {
  key string demandId; 
  int startTime;    	
  int endTime;
  float nonDeliveryCost;
  float tardinessCost;
};

//{DemandAssignment} demandAssignments = 0;

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

//{StepAssignment} stepAssignments = 0;

tuple StorageAssignment {
  key string demandId; 
  key string prodStepId;  	
  int startTime;    	
  int endTime;
  int quantity;
  string storageTankId;
};

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
     /*
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
  	}	*/   
} 


