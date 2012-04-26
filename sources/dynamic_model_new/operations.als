open Index
open File
open Object_Model

pred add[s,s' : State, f : File ] {
		s != s'
		f in (pathname.Path).s
		parent.s' = parent.s
		marks.s' = marks.s
		branches.s' = branches.s
		on.s' = on.s
		blob.s' = blob.s
		
		let r = {s'':s+s', c:Commit, c':Commit | c ->s'' -> c' in parent} {s'.r = s.r}
		let r = {s'':s+s', h:Head, c:Commit | h -> s'' -> c in current} {s'.r = s.r}
		let r = {s'':s+s', t:Tree, n:Name, o:Tree + Blob | t -> s'' -> n -> o in contains} {s'.r = s.r}
		let r = {s'':s+s', f:File, b:Blob |f -> s'' -> b in blob} {s'.r = s.r}
		let r = {s'':s+s', f:File, p:Path | f -> s'' -> p in pathname} {s'.r = s.r}
		s'.(Index.staged ) = s.(Index.staged) + f
}

pred rm[s,s' : State, f : File ] {
		s != s'
		f in s.(Index.staged)
		let r = {s'':s+s', c:Commit, c':Commit | c ->s'' -> c' in parent} {s'.r = s.r}
		let r = {s'':s+s', h:Head, c:Commit | h -> s'' -> c in current} {s'.r = s.r}
		let r = {s'':s+s', t:Tree, n:Name, o:Tree + Blob | t -> s'' -> n -> o in contains} {s'.r = s.r}
		let r = {s'':s+s', f:File, b:Blob |f -> s'' -> b in blob} {s'.r = s.r}
		let r = {s'':s+s', f:File, p:Path | f -> s'' -> p in pathname} {s'.r = s.r}
		s'.(Index.staged)  = s.(Index.staged) - f
}

pred commit[s,s' : State] {
		s != s'
		some s.(Index.staged)
		let r = {s'':s+s', t:Tree, n:Name, o:Tree + Blob | t -> s'' -> n -> o in contains} {s'.r = s.r}
		let r = {s'':s+s', f:File, b:Blob |f -> s'' -> b in blob} {s'.r = s.r}
		let r = {s'':s+s', f:File, p:Path | f -> s'' -> p in pathname} {s'.r = s.r}
		let r = {s'':s+s', i:Index, f:File| i -> s'' -> f in staged} {s'.r = s.r}
		some com:Commit{
			s.(Head.current) = s'.(com.parent)
			s'.(Head.current) = com
			let r = {c:Commit, c':Commit | c ->s -> c' in parent} {com not in ^r.RootCommit}
		}

}
run { 
	some s,s':State | commit[s,s']
} for 5 but exactly 2 State
