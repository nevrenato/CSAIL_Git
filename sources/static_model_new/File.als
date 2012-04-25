open Objects
open Name

sig Path {

	parent : lone Path,
	name : Name

}
sig File {

	blob : Blob,
	pathname : Path 

}

fact {
	
		// no cycles
		no ^parent & iden

		// pathname is injective
		pathname.~pathname in iden

		// two paths with the same parent can't have the same name
		all disj p,p' : Path | p.parent = p'.parent implies p.name != p'.name
	
		// The name of a file has to be always in a leaf
		no (Path.parent) & (File.pathname)
}

run {

} for 8
