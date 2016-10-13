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
	key int demandId;
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

tuple StepPrototype{
	key string stepId;
	int productId;
	string setupResourceId;
}
 tuple Presedence {
 	string predecessorId;
 	string successorId;
 	int delayMin;
 	int delayMax; 
 }

tuple Alternative {
	key string stepId;
	int alternativeNumber;
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
{StepPrototype} StepPrototypes = ...;
{Presedence} Presedences = ...;
{Alternative} Alternatives = ...;
{StorageProduction} StorageProductions = ...;
{setupMatrix} setupMatrices = ...;
{Criterion} Criterions = ...;

{int} ProductIds = {0}; //TODO: 
int setupCostArray[Resources][ProductIds][ProductIds];

dvar interval demands[d in Demands]
	in 0..d.deliveryMax;

dvar interval step [d in Demands][s in StepPrototypes]
	in 0..d.deliveryMax
	size item(Alternatives, ord(Alternatives, <s.stepId>)).fixedProcessingTime + ftoi(item(Alternatives, ord(Alternatives, <s.stepId>)).variableProcessingTime * d.quantity); 



execute{
	cp.param.Workers = 1;
	cp.param.TimeLimit = Opl.card(Demands);	
	for(var r in Resources) {
       	for(var s in Setups) {
       		setupCostArray[r][s.fromProductId][s.toProductId] = 
  			s.setupCost;
   		}				  
	}
}

minimize 0;

subject to{



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
  	}	   
} 


