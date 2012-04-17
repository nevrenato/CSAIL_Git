open util/ordering[StateWD]

sig StateWD{}
abstract sig WDObject{
	wdparent: Dir lone-> StateWD,
	wdobjects: set StateWD
}
sig File, Dir extends WDObject{}

one sig Root extends Dir{}

pred inv[s:StateWD]{
	//objects from parent on a state s, belongs to that state
	wdparent.s in wdobjects.s -> wdobjects.s
	//a Object cannot desdend from itself
	no ^(wdparent.s) & iden
	//all Objects desdends from a root
	wdobjects.s in *(wdparent.s).(Root & wdobjects.s)
}

fact{
	all s:StateWD | inv[s]
	//avoid objects not on the system
	WDObject in wdobjects.StateWD
}

run{
} for 3 but 1 StateWD
