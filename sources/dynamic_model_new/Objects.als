open Name
open State 

abstract sig Object {
	objects: set State
}

sig Blob extends Object {}

sig Tree extends Object {
		contains : Name  -> (Tree+Blob) one -> State
}


fact {

	all s:State{
		let r = {x :Tree, y : Tree+Blob | some n : Name | x->n->y in contains.s} {
			// there shall be no cycles
			no ^r & iden

		 	// all trees must have at least one son (git restriction)
		  	all t : Tree | some t.r
		}

		// a tree must have one parent at most
		all t : Tree | lone (contains.s).t
		
		//referential integrity
		contains.s in objects.s -> Name -> objects.s
	}
}

run {

} for 3 but 1 State
