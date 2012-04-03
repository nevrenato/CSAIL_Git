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
	// pw 
	//all t : Tree | t not in t.^references

	// pf
 	^references & iden  = (none->none)

	// smart pf 
	no ^references & iden
}

// two objects cannot have same sha
fact {
	// pw 
	//all disjoint o,o' : Object | o.namedBy != o'.namedBy
	
	// pf 
	//(namedBy.~namedBy in iden)  

}

//two trees have the same name iff they have the same content
fact{fact{
	all t,t':Tree | t.namedBy = t'.namedBy <=> t.references = t'.references
	no Tree.namedBy & Commit.namedBy + Tree.namedBy & Blob.namedBy + Tree.namedBy & Tag.namedBy + Commit.namedBy &Tag.namedBy + Commit.namedBy & Blob.namedBy
	no (namedBy.~namedBy) & Commit -> Commit
	no (namedBy.~namedBy) & Tag -> Tag
}

run {}
