/*********************************************
 * OPL 12.6.3.0 Model
 * Author: Chris
 * Creation Date: 13 okt. 2016 at 12:37:24
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
	float fixedProccesingCost;
	float variableProccessingCost;
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

int setupCostArray[Resources][Products][Products];


dvar interval demands[d in Demands]
	optional(true)
	in 0..d.deliveryMax;
	
dvar interval steps[s in Steps];

dvar interval alternatives[a in Alternatives]
	in 0..10
	size a.fixedProcessingTime + ftoi(a.variableProcessingTime);	//TODO: multiply by quantity
	

/*dexpr float TotalNonDeliveryCost = sum(d in Demands) presenceOf(demands[d]) * d.quantity * d.nonDeliveryVariableCost;
dexpr float TotalProcessingCost = sum(d in Demands) presenceOf(d) * 
(sum(s in Steps:s.productId==d.productId) );


dexpr float TotalSetupCost = 0;
dexpr float TotalTardinessCost = 0;

dexpr float WeightedTotalNonDeliveryCost = item(CriterionWeights, ord(CriterionWeights, <"NonDeliveryCost">)).weight * TotalNonDeliveryCost;
dexpr float WeightedTotalProcessingCost = item(CriterionWeights, ord(CriterionWeights, <"ProcessingCost">)).weight * TotalProcessingCost;
dexpr float WeightedTotalSetupCost = item(CriterionWeights, ord(CriterionWeights, <"SetupCost">)).weight * TotalSetupCost;
dexpr float WeightedTotalTardinessCost = item(CriterionWeights, ord(CriterionWeights, <"TardinessCost">)).weight * TotalTardinessCost;
*/
execute{
	cp.param.Workers = 1;
	cp.param.TimeLimit = Opl.card(Demands);	
	/*for(var r in Resources) {
       	for(var s in Setups) {
       		setupCostArray[r][<s.fromState>][<s.toState>] = s.setupCost;
   		}				  
	}*/
}

minimize 0;

subject to{
	forall(d in Demands){
		span(demands[d], all(s in Steps:s.productId==d.productId) steps[s]);
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
  	/*writeln("Total Non-Delivery Cost    : ", TotalNonDeliveryCost);
  	writeln("Total Processing Cost      : ", TotalProcessingCost);
  	writeln("Total Setup Cost           : ", TotalSetupCost);
  	writeln("Total Tardiness Cost       : ", TotalTardinessCost);
  	writeln();
  	writeln("Weighted Non-Delivery Cost : ",WeightedNonDeliveryCost);
  	writeln("Weighted Processing Cost   : ", WeightedProcessingCost);
  	writeln("Weighted Setup Cost        : ", WeightedSetupCost);
  	writeln("Weighted Tardiness Cost    : ", WeightedTardinessCost);
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
  	}	*/   
} 


