open Objects
open Name


sig Path {
	pathparent : lone Path,
	name : Name,
	blob:lone Blob,
	index: lone Path
}

fact {
		//index is a correflexive
		index in iden	

		//only leafs can have blobs
		no Path.pathparent & blob.Blob
		no Path.pathparent & index.Path
		
		Path - Path.pathparent = blob.Blob

		// no cycles
		no ^pathparent & iden

		// two paths with the same parent can't have the same name
		all disj p,p' : Path | p.pathparent = p'.pathparent implies p.name != p'.name
}

run {
	no Tree
	#pathparent > 1
	some p:Path | #pathparent.p > 1
} for 3
