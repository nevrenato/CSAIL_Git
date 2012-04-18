open state

abstract sig WDObject{
	wdparent: Dir lone -> State,
  	wdobjects: set State
}

sig File, Dir extends WDObject{}

one sig Root extends Dir{}

pred inv[s:State]{
	//objects from parent on a state s, belongs to that state
	wdparent.s  in wdobjects.s -> wdobjects.s
	//a Object cannot ascend from itself
	no ^(wdparent.s) & iden
	//all Objects desdends from a root
  	//wdobjects.s in *(wdparent.s).(Root & wdobjects.s)
 	wdobjects.s in ^(wdparent.s).(WDObject) + Root
}

fact{
	all s:State | inv[s]
	// debug purposes
	//avoid objects not on the system
	WDObject in wdobjects.State
}


run{
} for 4 but 1 State
