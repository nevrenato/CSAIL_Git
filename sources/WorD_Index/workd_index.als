open util/ordering[State]

-- Types of changes that can occur in the repo
abstract sig Type{}
one sig Mod,Add,Del extends Type {}

-- A file plus is associated changes
sig File {
	diff : some Type
}

-- The working directory, that sees all changes in the
-- tracked files, where the type Add cannot appear.
sig WorkingD {

	contents : set File
}

fact {

 not Add in (WorkingD.contents).diff
}



-- The index, where are all files modifications, to be included, including new ones
sig Index {

  toCommit : set File
}



-- Put this beast dynamic
sig State {

	workD : WorkingD,
  index : Index
}



-- git add operation
pred add [s,s' : State, f : File] {
  
	--debug (show only relevant cases)
  s != s' and s'.index.toCommit != s.index.toCommit

	-- git add only used for additions and modifications
	f.diff in (Add+Mod) 

  -- when we add a mod file, that change must already appear in the WorkD
  Mod in f.diff implies f in s.workD.contents   
  --(s'.index.toCommit).Mod in (s'.workD.contents).Mod
 
 s'.workD = s.workD
 s'.index.toCommit = s.index.toCommit + f 
}



run {

	some  s,s' : State, ch : File | add[s,s',ch]
	
  -- debug (removes garbage objs)
	WorkingD in State.workD
  Index in State.index
  File in WorkingD.contents + Index.toCommit

} for 6 but exactly 2 State
