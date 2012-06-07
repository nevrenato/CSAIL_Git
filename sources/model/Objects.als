open Name

-- This signature will represent the dynamic behaviour of git repository
-- The contents of the repository will be changed along the workflow
sig State {}

-- The representation of git objects, conceptually the belong
-- to a set of states
abstract sig Object {
	objects: set State
}

-- The representation of a file content (called blob on git) 
sig Blob extends Object {}

-- Equivalent to a folder on the filesystem. It's sons
-- can be blobs or other trees, each son is uniquely 
-- identified by a name
sig Tree extends Object {
		contains : Name  -> lone (Tree+Blob)
}

-- Just to aid in specification
fun contents: Tree -> Object -> Name{
	{t:Tree, o:Object, n:Name | t -> n-> o in contains}
}


-- The sharing nature of git, says that trees with the same 
-- content are represented as the same tree. There are no cycles
-- among them. And because git if file oriented, there cannot be
-- trees (folders) with no sons.
-- Note : Probably the two last restrictions can be passed to 
-- the Properties.als, in order to check consistency of git
fact {
		all t,t' : Tree | t.contains = t'.contains implies t=t'
		no ^(contents.Name) & iden 
}
