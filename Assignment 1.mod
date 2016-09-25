/*********************************************
 * OPL 12.6.3.0 Model
 * Author: s130604
 * Creation Date: 14 sep. 2016 at 14:56:15
 *********************************************/
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

dvar int CharactersPlayedByActor[Characters] in 0..card(Characters);
dexpr int nrOfActors=  sum(actorNr in 0..card(Characters)) (count(CharactersPlayedByActor, actorNr)>0);

execute{
	cp.param.Workers = 1;
	//cp.param.TimeLimit = 5;	
}
minimize nrOfActors;
subject to{
	//An actor plays a character of his own type
	forall(c1 in Characters){
		forall(c2 in Characters){
			if(c1.type!=c2.type){
				CharactersPlayedByActor[c1]!=CharactersPlayedByActor[c2];
			}		
		}
	}
	//An actor cannot play two different characters in 2 consecutive scenes
	forall(s1 in Scenes:ord(Scenes, s1) < card(Scenes)-1){
		forall(c1 in Characters:c1.name in s1.characters){
			forall(c2 in Characters:c2.name in next(Scenes, s1).characters){
				if(c1!=c2){				
					CharactersPlayedByActor[c1]!=CharactersPlayedByActor[c2];	
  				}				
			}			
		}
	}
	//An actor can only play one character per scene
	forall(s in Scenes){
		allDifferent(all(c1 in Characters:c1.name in s.characters) CharactersPlayedByActor[c1]);
	}
	//An actor that plays a leading character doesn't play any other characters
	forall(lc in Characters:lc.name in LeadingCharacters){
		forall(c in Characters:c!=lc){
			CharactersPlayedByActor[lc]!=CharactersPlayedByActor[c];
		}	
	}
	//max nr of character per actor
	forall(actorNr in 0..card(Characters)){
		count(CharactersPlayedByActor, actorNr)<=maxNrOfCharacters;	
	}		
}

/*
execute {
  	writeln("Actors needed: ", NrOfActorsNeeded);
  	
  	for(var ct in CharacterTypes) {
  		writeln(ct, " needed: ", nrOfActorsOfType[ct]);
   	}  	  
   			     	
  	for(var i=0; i<NrOfActorsNeeded; i++) {
  	  writeln("Actor ", i, " plays ", CharactersPlayedByActor[i]);
    }  	  
}  
*/