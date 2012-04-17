sig State{}
abstract sig WDObject{
	parent: Dir lone-> State,
	wdobjects: set State
}
sig File, Dir extends WDObject{}

one sig Root extends Dir{}

pred inv[s:State]{
	//objects from parent on a state s, belongs to that state
	parent.s in wdobjects.s -> wdobjects.s
	//a WDObject cannot desdend from itself
	no ^(parent.s) & iden
	//all WDObjects desdends from a root
	wdobjects.s in *(parent.s).(Root & wdobjects.s)
}

fact{
	all s:State | inv[s]
	//avoid objects not on the system
	WDObject in wdobjects.State
}

run{
	//some s,s':State, f:File | rm[s,s',f]
} for 3 but exactly 2 State
