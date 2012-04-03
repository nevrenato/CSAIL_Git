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
 	^references & iden  = (none->none)
	no ^references & iden
}

fact {
	//all disjoint o,o' : Object | o.namedBy != o'.namedBy
	//(namedBy.~namedBy in iden)  
}

fact{
	all t,t':Tree | t.namedBy = t'.namedBy <=> t.references = t'.references
	namedBy in Object lone -> Sha
	no Tree.namedBy & Commit.namedBy + Tree.namedBy & Blob.namedBy + Tree.namedBy & Tag.namedBy + Commit.namedBy &Tag.namedBy + Commit.namedBy & Blob.namedBy
	no (namedBy.~namedBy) & Commit -> Commit
	no (namedBy.~namedBy) & Tag -> Tag
}

fact{

}

run {}
