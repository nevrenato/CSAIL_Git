open operations

assert commitMentalSanity{
	all s,s':State{
		commit[s,s'] => all o:(head.s').(marks.s').points.*(contents.Name) | o in Path.((head.s').(marks.s').abs) &&  (head.s').(marks.s').abs.o in (index.s).path.*pathparent
	}
}
