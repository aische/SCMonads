// 2011 Daniel van den Eijkel
// Monads for SuperCollider 

Monad {
	
	join {
		^(this >>= {|m| m})
	}	
	
	fmap {|f|
		this >>= {|a| this.class.return(f.(a)) }
	}
	
	>>= {|f|
		this.fmap(f).join;
	}
	
	* >>= {|f| ^(this.return(nil) >>= f) }

	/*
	do { |...fs|
		var m = this;
		var d = IdentityDictionary.new;	
		fs.do {|f| 
			if (f.def.argNames.notNil) {
				m = m >>= {|a| d.put(f.def.argNames[0], a); f.(a) }
			};
		}
		^m;
	}
	*/
}

Just {
	var <a;
	
	*new{|a|
		^super.new.init(a)
	}
	
	init {|aa|
		a = aa;
	}	
}



MaybeMonad {
	var <just;

	*new{|just|
		^super.new.init(just)
	}
	
	init {|justArg|
		just = justArg;
	}
	
	*return { |a|
		^this.new(Just(a));
	}
	
	*fail {
		^this.new(nil);
	}
		
	>>= { |f|
		if (just.isNil) {
			^this	
		}{
			^f.(just.a)	
		}
	}
	
	mplus {|m|
		if (just.isNil) {
			^m
		}{
			^this
		}		
	}
}

IdentityMonad : Monad {
	var a;
	
	*new{|a|
		^super.new.init(a)
	}
	
	init {|aa|
		a = aa;
	}
	
	*return {|a|
		^this.new(a)
	}
	
	fmap {|f|
		^this.class.new(f.(a))
	}
		
	>>= {|f|
		^f.(a)
	}
	
	run {
		^a
	}
}


StateMonad : Monad {
	var <func;
	
	*new{|func|
		^super.new.init(func)
	}
	
	init {|f|
		func = f;
	}
	
	*return {|a|
		^this.new{|state| [a, state]}
	}
	
	fmap {|f|
		^this.class.new{|state| 
			var a, s2;
			#a, s2 = func.(state);
			[f.(a), s2]
		}
	}
	
	>>= {|f|
		^this.class.new{|state|
			var a, state2;
			#a, state2 = func.(state);
			f.(a).func.(state2);
		}
	}
	
	*put {|state|
		^this.new{|st| [nil, state]}
	}
	
	*get {
		^this.new{|state| [state, state]}
	}
	
	run {|initialstate|
		^func.(initialstate)
	}
}

ListMonad : Monad {
	var list;
	
	*new{|list|
		^super.new.init(list)
	}
	
	init {|l|
		list = l;
	}
	
	*return {|a|
		^this.new([a])
	}

	fmap {|f|
		^this.class.new(list.collect(f))
	}
		
	>>= {|f|
		^this.class.new(list.collect((_.run) <> f).flatten)
	}

	run {
		^list
	}
}

CPSMonad : Monad {
	var <func;	// {|c| ... ; c.(a)}
	
	*return {|a|
		^this.new({|c| c.(a)})
	}

	*new{|func|
		^super.new.init(func);
	}
	
	init {|f|
		func = f;
	}

	fmap {|f|
		^this.class.new{|c| func.({|a| c.(f.(a))})} 
	}
	
	>>= {|f|
		^this.class.new({|c| func.({|a| f.(a).func.(c)})})
	}

	*callcc {|f|
		^this.new({|c| f.({|a| this.new({|c2| c.(a) }) }).func.(c) })
	}

	run {
		^func.({|a|a})
	}
}

StateMonadPlus : Monad {
	var <func;	// {|s| ... ; ([a,s] | nil)}, s is a list or array
	
	// monadic return / unit
	*return {|a|
		^this.new({|s| [a, s]})
	}
	
	// fail, causes backtracking if there are alternatives
	*fail {
		^this.new{}	
	}
	
	*new{|func|
		^super.new.init(func);
	}
	
	init {|f|
		func = f;
	}

	>>= {|f|
		^this.class.new({|s|
			var r1, a, s2, st;
			r1 = func.(s);
			if (r1.notNil) {
				#a, s2 = r1;
				st = f.(a);
				st.func.(s2)
			}
		})
	}

	fmap {|f|
		^this.class.new{|s| 
			var r, a, s2;
			r = func.(s);
			if (r.notNil) {
				#a, s2 = r;
				[f.(a), s2]
			}
		}
	}
	
	// operator for alternatives
	mplus { |st|
		^this.class.new({|s|
			var a, s2, r1;
			r1 = func.(s);
			if (r1.notNil) {
				r1
			}{
				st.func.(s)
			}
		})
	}
	
	run {|s|
		^func.(s)
	}
}

ParserMonad : StateMonadPlus {

	// get the next item from the input array, if there is such an item
	*item {
		^this.new{|s|
			if(s.size>0) {
				[s[0], s.drop(1)]
			}
		}
	}
	
	// fail parsing if func returns false
	*check {|func|
		^this.new{|s|
			if (func.()) {
				[nil, s]
			}
		}
	}
		
	// take next item. fail if check is false.
	*sat {|func|
		^(this.item >>= {|c| this.check(func.(c)) >>= this.return(c)});
	}
	
	*string {|str|
		if (str.size < 1) {
			^this.return([])
		}{
			^(
			this.sat(_==str[0]) >>= {|c|
			this.string(str.drop(1)) >>= {|cs|
			this.return([c]++cs) }}
			)
		}		
	}

	// 0 or more 
	many { 
		^(this >>= {|a| this.many >>= {|as| this.class.return([a] ++ as) }}) mplus: this.class.return([])
	}

	// 1 or more
	many1 { 
		^(this >>= {|a| this.many >>= {|as| this.class.return([a] ++ as) }})
	}

	// 0 or 1	
	maybe { |defaultValue|
		^(this mplus: this.class.return(defaultValue));
	}
}

RWSMonad : Monad {
	var <func;
	
	*new{|func|
		^super.new.init(func)
	}
	
	init {|f|
		func = f;
	}
	
	*return {|a|
		^this.new{|input, state| [a, state, []]}
	}
	
	fmap {|f|
		^this.class.new{|input, state| 
			var a, s2, o;
			#a, s2, o = func.(input, state);
			[f.(a), s2, o]
		}
	}
	
	>>= {|f|
		^this.class.new{|input, state|
			var a, state2, o2, b, state3, o3;
			#a, state2, o2 = func.(input, state);
			#b, state3, o3 = f.(a).func.(input, state2);
			[b, state3, o2 ++ o3]
		}
	}
	
	*read {
		^this.new{|input, state| [input, state, []]}
	}
	
	*write { |w|
		^this.new{|input, state| [nil, state, [w]]}
	}
	
	*put {|state|
		^this.new{|st| [nil, state, []]}
	}
	
	*get {
		^this.new{|input, state| [state, state, []]}
	}
	
	run {|input, initialstate|
		^func.(input, initialstate)
	}
}
