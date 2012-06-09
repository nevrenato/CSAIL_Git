open Objects
open Name

-- A path is used to represent a subset of full path of a file
-- E.g. the /a of /x/a or /a/x or /x/a/x etc...
sig Path {
	pathparent : lone Path,
	name : Name
}

-- The root folder of the repository
one sig Root extends Path{}

fact{
	--all paths except root have a perent and there are no cycles
	all p:Path - Root | some p.pathparent and p not in p.^pathparent
	
	--a path cannot have two direct descendants with the same name
	all p:Path, disj p1,p2:pathparent.p | p1.name != p2.name
	
	--root does not have a parent
	no Root.pathparent
}

-- This signature is not strictly necessary, is just used to get a nicer 
-- concept of the model, each file has a path and a content associated (blob).
-- A file can be on the index in some states of git workflow
sig File{
	path: Path,
	blob: Blob,
	index: set State
}


-- Paths representing folders can't be on index, and files can't be folders.
-- There cannot be files with same path in the same index
-- Note : Probably theses facts can be passed to the add predicate and/or to
-- Predicate.als in order to check consistency of git.
fact{
	all s:State, f:index.s{
		no (f.path).^pathparent & (index.s).path
		f.path not in Root
	}
	all s:State, disj f1,f2:index.s | f1.path != f2.path
}


run { 
			no Tree 
			#File = 2
			#File.path.*pathparent = 2
			#Path = 2
			#Blob = 1
			#Name = 2
			some index.State
}
