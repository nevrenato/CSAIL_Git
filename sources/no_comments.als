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
	 
	// se gostares da outra versao podes tirar esta !
	no Tree.namedBy & Commit.namedBy + Tree.namedBy & Blob.namedBy + Tree.namedBy & Tag.namedBy + Commit.namedBy &Tag.namedBy + Commit.namedBy & Blob.namedBy
	
	//alternativa
	 //namedBy.~namedBy in (Tree->Tree)+(Blob->Blob)+(Commit->Commit)+(Tag->Tag)
	

  // se gostares da outra versao podes tirar esta !
	no (namedBy.~namedBy) & Commit -> Commit
	no (namedBy.~namedBy) & Tag -> Tag

	// alternativa
	//namedBy.~namedBy & (Commit+Tag)->(Commit+Tag) in iden

}

run {}
