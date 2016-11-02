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
float setupCostArray[Resources][productIds][productIds];

dvar interval demands[d in Demands]
	optional(true)
	in 0..d.deliveryMax;
	
dvar interval steps[d in Demands][s in Steps]
	optional(true);

dvar interval alternatives[d in Demands][a in Alternatives]
	optional(true)
	size   ftoi(round(a.fixedProcessingTime + a.variableProcessingTime * d.quantity));	
	
dvar interval setupResources[s in Steps][sr in SetupResources]
	optional(true);
	

dvar sequence resourceUsage[r in Resources] in
	all(a in Alternatives, d in Demands:a.resourceId == r.resourceId && d.productId == item(Steps, <a.stepId>).productId) alternatives[d][a]
    types all(a in Alternatives, d in Demands:a.resourceId == r.resourceId && d.productId == item(Steps, <a.stepId>).productId) d.productId;
	
dexpr float TotalNonDeliveryCost = sum(d in Demands) (1-presenceOf(demands[d])) * d.quantity * d.nonDeliveryVariableCost;
dexpr float TotalProcessingCost = sum (d in Demands) sum(a in Alternatives) presenceOf(alternatives[d][a]) * (a.fixedProcessingCost + 
a.variableProcessingCost * d.quantity);


dexpr float TotalSetupCost = sum(r in Resources:r.setupMatrix != "NULL") sum (d in Demands) sum(a in Alternatives:a.resourceId == r.resourceId) 
	(typeOfPrev(resourceUsage[r], alternatives[d][a], r.initialProductId, -1)!=-1)*
	setupCostArray[r][typeOfPrev(resourceUsage[r], alternatives[d][a], (r.initialProductId>=0) * r.initialProductId, 0)][item(Steps, <a.stepId>).productId];
dexpr float TotalTardinessCost = sum(d in Demands) ((endOf(demands[d]) - d.dueTime)*(d.dueTime<endOf(demands[d])))*d.tardinessVariableCost;

dexpr float WeightedTotalNonDeliveryCost = item(CriterionWeights,<"NonDeliveryCost">).weight * TotalNonDeliveryCost;
dexpr float WeightedTotalProcessingCost = item(CriterionWeights,  <"ProcessingCost">).weight * TotalProcessingCost;
dexpr float WeightedTotalSetupCost = item(CriterionWeights,  <"SetupCost">).weight * TotalSetupCost;
dexpr float WeightedTotalTardinessCost = item(CriterionWeights, <"TardinessCost">).weight * TotalTardinessCost;

execute{
	cp.param.Workers = 1;
	//cp.param.TimeLimit = Opl.card(Demands);	
	for(var r in Resources) {
       	for(var s in Setups) {
       		if(s.setupMatrixId == r.setupMatrix && r.setupMatrix != "NULL"){       	
       			setupCostArray[r][s.fromState][s.toState] = s.setupCost;
       		}       		
   		}				  
	}
}
tuple triplet {int loc1; int loc2; int value; };
{triplet} transitionTimes[r in Resources] = {<s.fromState, s.toState, s.setupTime>|s in Setups:s.setupMatrixId == r.setupMatrix };

minimize WeightedTotalNonDeliveryCost + WeightedTotalNonDeliveryCost + WeightedTotalTardinessCost;

subject to{
	forall(d in Demands){
		forall(p in Precedences){
			forall(s1 in Steps:s1.stepId==p.predecessorId && s1.productId == d.productId){
				forall(s2 in Steps:s2.stepId==p.successorId && s1.productId == d.productId){
					endOf(steps[d][s1], -1) + p.delayMin <= startOf(steps[d][s2], maxint);
					endOf(steps[d][s1], -1) + p.delayMax >= startOf(steps[d][s2], maxint);
				}				
			}
		}
		forall(a in Alternatives:d.productId == item(Steps, <a.stepId>).productId){
			presenceOf(alternatives[d][a]) => startOf(alternatives[d][a]) == startOf(steps[d][item(Steps, <a.stepId>)]) && 
			endOf(alternatives[d][a]) == endOf(steps[d][item(Steps, <a.stepId>)]);
		}
		span(demands[d], all(s in Steps:s.productId==d.productId) steps[d][s]);
		forall(s in Steps){
			alternative(steps[d][s], all(a in Alternatives:a.stepId==s.stepId) alternatives[d][a]);	
			presenceOf(demands[d])=>presenceOf(steps[d][s]);
		}
	}
	forall(r in Resources){
		noOverlap(resourceUsage[r], transitionTimes[r]);
		
			
	}
	forall(sr in SetupResources){
		noOverlap(all(s in Steps:s.setupResourceId==sr) setupResources[s][sr]);	
		forall(r in Resources){
			forall(d in Demands){
				forall(a in Alternatives:d.productId == item(Steps, <a.stepId>).productId&&a.resourceId==r.resourceId && r.setupMatrix!="NULL"){
					(typeOfPrev(resourceUsage[r], alternatives[d][a], r.initialProductId, -1)!=d.productId &&
					typeOfPrev(resourceUsage[r], alternatives[d][a], r.initialProductId, -1)!=-1 &&
					presenceOf(alternatives[d][a])) =>
					(endOf(setupResources[item(Steps, <a.stepId>)][sr]) == startOf(alternatives[d][a]) && 
					startOf(setupResources[item(Steps, <a.stepId>)][sr]) == endOf(setupResources[item(Steps, <a.stepId>)][sr]) - 
					item(Setups, <r.setupMatrix, typeOfPrev(resourceUsage[r], alternatives[d][a], 0), d.productId>).setupTime);			
				}
  			}
   		}  							
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


