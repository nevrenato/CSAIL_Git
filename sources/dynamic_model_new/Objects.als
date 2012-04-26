open Name
open State 

abstract sig Object {
	objects: set State
}

sig Blob extends Object {}

sig Tree extends Object {
		contains : Name  -> one (Tree+Blob)
}


fact {

		let r = {x :Tree, y : Tree+Blob | some n : Name | x->n->y in contains} {
			// there shall be no cycles
			no ^r & iden

		 	// all trees must have at least one son (git restriction)
		  	all t : Tree | some t.r
		}

	all s:State{
		// a tree must have one parent at most
		all t : Tree | lone (contains).t
		
		//referential integrity
		contains in objects.s -> Name -> objects.s
	}
}

run {

} for 3 but exactly 1 State
