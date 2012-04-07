sig Sha{ }

// An object in git
abstract sig Object {
	namedBy : one Sha
}

// stores file data
sig Blob extends Object{}

// directory 
sig Tree extends Object {
	references : set (Tree+Blob)
}

// points to a single tree, marking it as what the project looked like
// at a certain point in time
sig Commit extends Object{
	points : one Tree
}

// way to mark a specific commit as special in some way
sig Tag extends Object{
	marks : one Commit
}

// a directory cannot reference itself
fact {
	no ^references & iden
}


fact{
	
	//two trees have the same name iff they have the same content
	// not pf :(
	all t,t':Tree | t.namedBy = t'.namedBy <=> t.references = t'.references
	//only Trees can share names
	 namedBy.~namedBy - (Tree->Tree) in iden
}

run { 
	// debug
	#Commit > 0 }  
