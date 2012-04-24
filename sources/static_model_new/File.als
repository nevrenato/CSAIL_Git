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

		// two path's at the same level can't have the same name 
   	no (name.~name - iden) & (parent.~parent - iden)
		all disj p,p' : Path | no p.parent + p'.parent implies p.name != p'.name
	
		// The name of a file has to be always in a leaf
		no (Path.parent) & (File.pathname)
}

run {

} for 8
