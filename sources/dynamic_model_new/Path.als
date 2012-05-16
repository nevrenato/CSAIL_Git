open Objects
open Name
open State

sig Path {
	pathparent : lone Path,
	name : Name
}

one sig Root extends Path{}

fact{
	//all paths except root have a perent and there are no cycles
	all p:Path - Root | some p.parent && p not in p.^parent
	//a path cannot have two direct descendants with the same name
	all p:Path, disj p1,p2:parent.p | p1.name != p2.name
	//root does not have a parent
	no Root.parent
}

sig File{
	path: Path,
	blob: Blob,
	index: set State
}


//associates paths with blob
fun pathcontents: State -> Path -> Blob{
	{s:State, p:Path, b:Blob | some f:index.s | f.path = p and f.blob = b}
}



fact {
	
}

run {
	some pathparent.pathparent
} for 3 but 1 State
