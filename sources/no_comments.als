sig Sha{ }

abstract sig Object {
	namedBy : one Sha
}

sig Blob extends Object{}

sig Tree extends Object {
	references : set (Tree+Blob)
}

sig Commit extends Object{
	points : one Tree,
  	parent : set Commit
}

sig Tag extends Object{
	marks : one Commit
}

fact {
	no ^references & iden
}

//namedBy
fact{
	all t,t':Tree | t.namedBy = t'.namedBy <=> t.references = t'.references
	namedBy.~namedBy - (Tree->Tree) in iden
}

// Assumptions
fact {
	Blob in Tree.references
	Tree in Tree.references + Commit.points
	Sha in Object.namedBy

  	points.~points in iden
  	references.(iden & (Tree->Tree)).~references  in iden
  	no Commit.points & Tree.references
}

fact {	
  	no ^parent & iden
}

run {} for exactly 6 Object, 6 Sha
