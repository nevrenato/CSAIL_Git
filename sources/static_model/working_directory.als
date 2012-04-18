open util/ordering[StateWD]

sig StateWD{}

abstract sig WDObject{

	wdparent: Dir lone -> StateWD,
	
  wdobjects: set StateWD

}

sig File, Dir extends WDObject{}

one sig Root extends Dir{}

pred inv[s:StateWD]{

	//objects from parent on a state s, belongs to that state
	wdparent.s  in wdobjects.s -> wdobjects.s

	//a Object cannot ascend from itself
	no ^(wdparent.s) & iden

	//all Objects desdends from a root
  //wdobjects.s in *(wdparent.s).(Root & wdobjects.s)
  wdobjects.s in ^(wdparent.s).(WDObject) + Root

}

fact{

	all s:StateWD | inv[s]

	// debug purposes
	//avoid objects not on the system
	WDObject in wdobjects.StateWD

}


run{
	#Dir > 3 
	#File > 3
} for 8 but 2 StateWD
