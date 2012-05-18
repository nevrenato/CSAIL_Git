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
	all p:Path - Root | some p.pathparent && p not in p.^pathparent
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
	//the root is never a file
	no File.path & Root
	//only leaves are files
	no File.path & Path.pathparent
	//2 different files on the same index does not share a path
	all s:State, disj f1,f2:index.s | f1.path != f2.path
}

run {
	some File
}for 3 but 1 State


//associates paths with blob from index on a certain state
fun pathcontents: State -> Path -> Blob{
	{s:State, p:Path, b:Blob | some f:index.s | f.path = p and f.blob = b}
}

//it gives the paths that are on index
fun files : State -> Path {
	{s : State, p : Path | some p.(s.pathcontents) }
}
