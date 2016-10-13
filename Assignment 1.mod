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

//The number of characters by type
int charactersOfType[t in CharacterTypes] = sum(c in Characters) (c.name not in LeadingCharacters && c.type==t);

//Minimum number of actors needed
int minimum = ftoi(sum(t in CharacterTypes)ceil((charactersOfType[t]/maxNrOfCharacters)) + card(LeadingCharacters));

dvar int CharactersPlayedByActor[Characters] in 0..card(Characters)-1;
dexpr int nrOfActors=  sum(actorNr in 0..card(Characters)-1) (count(CharactersPlayedByActor, actorNr)>0);

execute{
	cp.param.Workers = 1;
	cp.param.TimeLimit = 5;	
}

minimize nrOfActors;
subject to{
	//set minimum
	nrOfActors >= minimum;
	//Actors that play a leading character only play one character, so these can be assigned as different
	forall(lc in Characters:lc.name in LeadingCharacters){
		CharactersPlayedByActor[lc]==nrOfActors-ord(LeadingCharacters, lc.name)-1;	
	}	
	//The actor number cannot be higher than the total number of actors minus the number of leading characters that are
	//already assigned
	forall(c in Characters:c.name not in LeadingCharacters){
		CharactersPlayedByActor[c]<nrOfActors-card(LeadingCharacters);	
	}		
	//An actor plays a character of his own type
	forall(c1,c2 in Characters : ord(Characters,c1) < ord(Characters,c2)){
		if(c1.type!=c2.type){
			CharactersPlayedByActor[c1]!=CharactersPlayedByActor[c2];
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
	//max nr of character per actor
	forall(actorNr in 0..card(Characters)-card(LeadingCharacters)){
		count(CharactersPlayedByActor, actorNr)<=maxNrOfCharacters;	
	}		
}

int nrOfActorsOfType[ct in CharacterTypes];
{Character} ActorToCharacter[i in 0..nrOfActors-1];

execute {
  	writeln("Actors needed: ", nrOfActors);
  	for(var ct in CharacterTypes){
  		for(var actor=0; actor<nrOfActors; actor++){
  			for(var c in Characters){
  				if(CharactersPlayedByActor[c]==actor && c.type==ct){
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
   		ActorToCharacter[CharactersPlayedByActor[c]].add(c);   	
   	}
  	for(var i=0; i<nrOfActors; i++) {  	
  	  	writeln("Actor ", i, " plays ", ActorToCharacter[i]);
    }  	  
}  
