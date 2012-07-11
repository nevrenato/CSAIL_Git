open state
open sha

abstract sig WDObject{
	wdparent: Dir lone -> State,
  	wdobjects: set State
}

sig File extends WDObject{
	content: Sha lone-> State
}

sig Dir extends WDObject{}

one sig Root extends Dir{}

pred inv[s:State]{
	//if a file is in a state then the file has a content
	(wdobjects.s & File) in (content.s).(shas.s)

	//a Object cannot ascend from itself
	no ^(wdparent.s) & iden
	//all Objects desdends from a root
  	//wdobjects.s in *(wdparent.s).(Root & wdobjects.s)
 	wdobjects.s in ^(wdparent.s).(WDObject) + Root
	
	//referential integrity
	content.s in wdobjects.s -> shas.s
		//objects from parent on a state s, belongs to that state
	wdparent.s  in wdobjects.s -> wdobjects.s
}

fact{
	all s:State | inv[s]
	// debug purposes
	//avoid objects not on the system
	WDObject in wdobjects.State
}

pred rm[s,s':State, f:File]{
	f in wdobjects.s
	wdobjects.s' = wdobjects.s - f
//	wdparent.s' = wdparent.s
//	content.s' = content.s
}

run{
	some disj s,s':State, f:File | rm[s,s',f]
	//some f:File | no f.content
} for 4 but 2 State
