sig Sha{ }

abstract sig Object {
	namedBy : one Sha
}

sig Blob extends Object{}

sig Tree extends Object {
	references : set (Tree+Blob)
}

sig Commit extends Object{
	points : one Tree
}

sig Tag extends Object{
	marks : one Commit
}

fact {
	no ^references & iden
}

fact{

	all t,t':Tree | t.namedBy = t'.namedBy <=> t.references = t'.references
	namedBy.~namedBy - (Tree->Tree) in iden
}

run {}
