open Objects
open Name


sig Path {
	pathparent : lone Path,
	name : Name
}
sig File {
	index: lone File,
	blob : Blob,
	pathname : Path
}

fact {
		//index is a correflexive
		index in iden	

		// no cycles
		no ^pathparent & iden

		// pathname is injective
		pathname.~pathname in iden

		// two paths with the same parent can't have the same name
		all disj p,p' : Path | p.pathparent = p'.pathparent implies p.name != p'.name
	
		// The name of a file has to be always in a leaf
		no (Path.pathparent) & (File.pathname)
}

run {
} for 3
