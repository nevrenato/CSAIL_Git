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
 	//^references & iden  = (none->none)

	// smart pf 
	no ^references & iden
}


fact{
	
	//two trees have the same name iff they have the same content
	// not pf :(
	all t,t':Tree | t.namedBy = t'.namedBy <=> t.references = t'.references

	//	no Tree.namedBy & Commit.namedBy + Tree.namedBy & Blob.namedBy + Tree.namedBy & Tag.namedBy + Commit.namedBy &Tag.namedBy + Commit.namedBy & Blob.namedBy 
	// Talvez mais bonito assim ?	
	  //  namedBy.~namedBy in (Tree->Tree)+(Blob->Blob)+(Commit->Commit)+(Tag->Tag)


	// Commits and Tags have always uniques sha's 
	//no (namedBy.~namedBy) & (Commit -> Commit)
	//no (namedBy.~namedBy) & (Tag -> Tag)
		// em cima estas a dizer que os commits e as tags nao podem ter sha !!!
	  //	namedBy.~namedBy & (Commit+Tag)->(Commit+Tag) in iden
		
		// even better
	  namedBy.~namedBy - (Tree->Tree) in iden
}

run { 
	// debug
	#Commit > 0 }  
