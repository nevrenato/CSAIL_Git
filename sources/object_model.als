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
	points : one Tree,
  	parent : set Commit
}

sig RootCommit extends Commit{}


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

// Assumptions
fact {
	
	// A blob must have a parent
	Blob in Tree.references
 
	// A tree must have a parent tree unless it's root
	Tree in Tree.references + Commit.points

	// There are no models with sha's alone
	Sha in Object.namedBy

	// A root tree can only be pointed by One commit
  	points.~points in iden

	// A tree can only have one parent
  	references.(iden & (Tree->Tree)).~references  in iden 

	// A non root tree cannot be pointed by a commit
  	no Commit.points & Tree.references  
}

fact {	
	// A commit cannot be an ancestor of itself
  	no ^parent & iden
	//RootCommit don't have a parent
	no RootCommit.parent
	//All Commits descend from a RootCommit
	Commit - RootCommit in ^parent.RootCommit
}

run {

} for exactly 6 Object, 6 Sha
