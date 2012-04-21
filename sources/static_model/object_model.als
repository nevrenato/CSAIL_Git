sig Sha{
}

abstract sig Object {
	namedBy : Sha
}

sig Blob extends Object{
}

sig Tree extends Object {
	references : some (Tree+Blob)
}

sig Commit extends Object{
   	points : Tree,
  	parent : set Commit
}

sig RootCommit extends Commit{}

sig Tag extends Object{
	marks : Commit
}

//general
pred inv[]{

	//only Trees can share names
	namedBy.~namedBy - (Tree->Tree) in iden
}

//trees
pred invTrees[] {
	
	// a tree cannot reference itself
	no ^references & iden
	
 	//two trees have the same name iff they have the same content
	all t,t':Tree | t.namedBy = t'.namedBy <=> t.references = t'.references
}

// Assumptions
pred assumptions[] {

	 // A tree must have a parent or it is pointed by a commit
	 Tree in Tree.references + Commit.points
	
   // A tree can have at most one parent
   all t:Tree | lone references.t

	 //tags, always marks some commit
	 Tag in marks.Commit
	
   // A root tree can only be pointed by One commit
   points.~points in iden
	
	 // A tree cannot be simultaneously pointed from another tree and a commit
   no Commit.points & Tree.references
}

//commits
pred invCommits[]{	
	
	// A commit cannot be an ancestor of itself
	no ^parent & iden

	//RootCommits don't have a parent	
	no RootCommit.parent

	//All Commits descend from a RootCommit
	Commit in *parent.RootCommit
}

fact{
	inv[] && invTrees[] && assumptions[] && invCommits[]
	//everything on a state, belongs to that states
}


run {

} for 4
