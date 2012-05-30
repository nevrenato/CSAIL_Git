open Objects
open Name

sig Path {
	pathparent : lone Path,
	name : Name
}

one sig Root extends Path{}

fact{
	//all paths except root have a perent and there are no cycles
	all p:Path - Root | some p.pathparent and p not in p.^pathparent
	//a path cannot have two direct descendants with the same name
	all p:Path, disj p1,p2:pathparent.p | p1.name != p2.name
	//root does not have a parent
	no Root.pathparent
}

sig File{
	path: Path,
	blob: Blob,
	index: set State
}

fact{
	all s:State, f:index.s{
		no (f.path).^pathparent & (index.s).path
		f.path not in Root
	}
	all s:State, disj f1,f2:index.s | f1.path != f2.path
}

run {
	#index.State > 1
}for 3 but 1 State
