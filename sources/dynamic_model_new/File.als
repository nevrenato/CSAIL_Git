open Objects
open Name
open State

sig Path {
	pathparent : lone Path,
	name : Name
}
sig File {
	index: set State,
	blob : Blob,
	pathname : Path
}

fact {
		// no cycles
		no ^pathparent & iden

		// pathname is injective
		pathname.~pathname in iden

		// two paths with the same parent can't have the same name
		all disj p,p' : Path | p.pathparent = p'.pathparent implies p.name != p'.name
	
		// The name of a file has to be always in a leaf
		no (Path.pathparent) & (File.pathname)
}

run{} for 3 but 1 State
