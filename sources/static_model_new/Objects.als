open Name


abstract sig Object {}
sig Blob extends Object {}

sig Tree extends Object {
		contains : Name -> one (Tree+Blob) 
}


fact {
	
		let r = {x :Tree, y : Tree+Blob | some n : Name | x->n->y in contains} {
			// there shall be no cycles
			no ^r & iden

		 	// all trees must have at least one son (git restriction)
		  	all t : Tree | some t.r
		}

		// a tree must have one parent at most
		all t : Tree | lone contains.t
}

run{}
