using CP;


tuple Character {
key string name;
string type;
} 

tuple Scene {
string name;
{string} characters;
}

{string} CharacterTypes=...;
{Character} Characters=...;
{string} LeadingCharacters=...;
int maxNrOfCharacters=...;
{Scene} Scenes = ...;
dvar int CharacterToActor[Characters] in 0..card(Characters)-1;
dexpr int nrOfActors = sum(actorNr in 0..card(Characters)-1) (count(CharacterToActor, actorNr)>0);
execute{
	cp.param.Workers = 1;
	//cp.param.TimeLimit = 5;	
}
minimize nrOfActors;
subject to{
	//Actors that play a leading character only play one character, so these can be assigned as different
	forall(lc in Characters:lc.name in LeadingCharacters){
		CharacterToActor[lc]==nrOfActors-ord(LeadingCharacters, lc.name)-1;	
	}
	//The actor number cannot be higher than the total number of actors minus the number of leading characters that are
	//already assigned
	forall(c in Characters:c.name not in LeadingCharacters){
		CharacterToActor[c]<nrOfActors-card(LeadingCharacters);	
	}
	//An actor plays a character of his own type
	forall(c1 in Characters:c1.name not in LeadingCharacters){
		forall(c2 in Characters:c2.name not in LeadingCharacters){
			if(c1.type!=c2.type){
				CharacterToActor[c1]!=CharacterToActor[c2];
			}		
		}
	}
	//An actor cannot play two different characters in 2 consecutive scenes
	forall(s1 in Scenes:ord(Scenes, s1) < card(Scenes)-1){
		forall(c1 in Characters:c1.name in s1.characters){
	
				forall(c2 in Characters:c2.name in next(Scenes, s1).characters){
					if(c1!=c2){				
						CharacterToActor[c1]!=CharacterToActor[c2];	
  					}				
				}			
 				
 		
		}
	}
	//An actor can only play one character per scene
	forall(s in Scenes){
		allDifferent(all(c1 in Characters:c1.name in s.characters) CharacterToActor[c1]);
	}
	//max nr of character per actor
	forall(actorNr in 0..card(Characters)-card(LeadingCharacters)){
		count(CharacterToActor, actorNr)<=maxNrOfCharacters;	
	}		
}

int nrOfActorsOfType[ct in CharacterTypes];
{Character} CharactersPlayedByActor[i in 0..nrOfActors-1];
execute {
  	writeln("Actors needed: ", nrOfActors);
  	for(var ct in CharacterTypes){
  		for(var actor=0; actor<nrOfActors; actor++){
  			for(var c in Characters){
  				if(CharacterToActor[c]==actor && c.type==ct){
  					nrOfActorsOfType[ct]++; 
  				  	break;
  				}
  			}  		
  		}  	  	
  	}
  	for(var ct in CharacterTypes) {
  		writeln(ct, " needed: ", nrOfActorsOfType[ct]);
   	}  	  
   	for(var c in Characters){   
   		CharactersPlayedByActor[CharacterToActor[c]].add(c);   	
   	}
  	for(var i=0; i<nrOfActors; i++) {  	
  	  	writeln("Actor ", i, " plays ", CharactersPlayedByActor[i]);
    }  	  
}  
