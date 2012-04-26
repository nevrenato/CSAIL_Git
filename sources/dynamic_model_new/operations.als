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

			some c : Commit  {
					
					// the parent of the new commit is the last commit
					s'.(c.parent) = s.(Head.pointsToLast)
					// the new commit cannot be in the last state
					no s.(c.parent) 
				 	// Head points to the new commit
					s'.(Head.pointsToLast) = c
			
					
					// The Hard part
					all f : s.(Index.staged) {

						let root = c.points, 
								fname = (s.(f.pathname)).name,
								fparents = (s.(f.pathname)).^parent,
								sons = 
								{t : Tree, t' : (Tree+Blob) | some n : Name | t->s'->n->t' in contains}  {
				
								
							// The object model of the new commit (s') can only have the blobs
							// that are staged in s
							(root.^sons) & Blob in s.((s.(Index.staged)).blob)
					

								one t : root.*sons {
														
											// relation name->blob in some tree									
											fname->s.(f.blob) in s'.(t.contains)
														
											// and for all parents of that file there must be a correspondent
											// tree										
											all fp : fparents |
												one t'',t' : root.*sons |
														some fp.parent implies s'->(fp.name->t'') in t'.contains   		
							  }
					   }
					}
			}
}

run { 
	some s,s':State | commit[s,s']
} for 5 but exactly 2 State
