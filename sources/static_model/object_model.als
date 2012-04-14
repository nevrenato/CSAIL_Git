sig Sha{}

abstract sig Object {
	namedBy : Sha
}

sig Blob extends Object{}

sig Tree extends Object {
	references : set (Tree+Blob)
}

sig Commit extends Object{
   	points : Tree,
  	parent : set Commit
}

some sig RootCommit extends Commit{}

sig Tag extends Object{
	marks : Commit
}

sig branch{
	on: Commit
}

one sig head{
	current: branch
}

//general
fact{
	//only Trees can share names
	 namedBy.~namedBy - (Tree->Tree) in iden
}

//trees
fact {
	// a tree cannot reference itself
	no ^references & iden
	//two trees have the same name iff they have the same content (pag 11)
	all t,t':Tree | t.namedBy = t'.namedBy <=> t.references = t'.references
}

// Assumptions
fact {
	
	// A blob must have a parent
	Blob in Tree.references
 
	// A tree must have a parent or it is pointed by a commit
	Tree in Tree.references + Commit.points

	// There are no models with sha's alone
	Sha in Object.namedBy

	// A root tree can only be pointed by One commit
  	points.~points in iden

	// A tree can only have one parent
  	//references.(iden & (Tree->Tree)).~references  in iden
	all t:Tree | lone references.t

	// A non root tree cannot be pointed by a commit
  	no Commit.points & Tree.references
}


//commits
fact {	
	// A commit cannot be an ancestor of itself
  	no ^parent & iden
	//RootCommit don't have a parent
	no RootCommit.parent
	//All Commits descend from a RootCommit
	Commit - RootCommit in ^parent.RootCommit
}

run {} for 6
