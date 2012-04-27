open Objects
open Name
open State

sig Path {
	pathparent : lone Path,
	name : Name,
	blob:lone Blob,
	index: set State
}

fact {
		//only leafs can have blobs
		no Path.pathparent & blob.Blob
		
		all s:State{

			//only leafs can be on index
			no Path.pathparent & index.s

			//if a path is on index on a state s then the blob associated with the path is on state s
			(index.s).blob in objects.s
		}		

		//all leafs are files
		Path - Path.pathparent = blob.Blob
		
		// no cycles
		no ^pathparent & iden

		// two paths with the same parent can't have the same name
		all disj p,p' : Path | p.pathparent = p'.pathparent implies p.name != p'.name
}

run {
	some pathparent.pathparent
} for 3 but 1 State
