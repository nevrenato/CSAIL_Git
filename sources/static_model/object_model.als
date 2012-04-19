sig Sha{
}

abstract sig Object {
	namedBy : Sha
}
sig Blob extends Object{
}
sig Tree extends Object {
	references : set (Tree+Blob)
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
	namedBy.~namedBy - Tree -> Tree in iden
}

//trees
pred invTrees[] {
	// a tree cannot reference itself
	no ^references & iden
	//two trees have the same name iff they have the same content (pag 11)
	all t,t':Tree | t.namedBy = t'.namedBy <=> t.references = t'.references
}

// Assumptions
pred assumptions[] {
	// A blob must have a parent - NO! - (gitComm pag 120) a blob sha may exist on index, so the blob must exist
	Blob in Tree.references 
	// A tree must have a parent or it is pointed by a commit
	Tree in Tree.references + Commit.points
	// A tree can have at most one parent
  	//references.(iden & (Tree->Tree)).~references  in iden
	all t:Tree | lone references.t
	// There are no models with sha's alone
	Sha in Object.namedBy
	//tags, always marks some commit
	Tag in marks.Commit
	// A root tree can only be pointed by One commit
  	points.~points in iden
	// A non root tree cannot be pointed by a commit
  	no Commit.points & Tree.references
}

//commits
pred invCommits[]{	
	// A commit cannot be an ancestor of itself
  	no ^parent & iden
	//RootCommit don't have a parent
	no RootCommit.parent
	//All Commits descend from a RootCommit
	Commit in *parent.(Commit & RootCommit)
}

fact{
	inv[] && invTrees[] && assumptions[] && invCommits[]
	//everything on a state, belongs to that states
}

run {
} for 4
