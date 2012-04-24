open sha

abstract sig Object {
	namedBy : Sha
}

sig Blob extends Object{}

sig Tree extends Object {
	references :  Name->(Tree+Blob)
}

sig Commit extends Object{
   	points : Tree,
  	parent : set Commit
}

sig RootCommit extends Commit{}

sig Tag extends Object{
	marks : Commit
}
