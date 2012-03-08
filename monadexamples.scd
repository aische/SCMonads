// 2011 Daniel van den Eijkel
// Monads for SuperCollider: Examples

(
	m = IdentityMonad;
	//m = ListMonad;
	//m = CPSMonad;
	//m = StateMonad;
	
	a = 
		m.return(1)   >>= {|x|
		m.return(2)   >>= {|y|
		m.return(x+y) }};
	
	a.run;
)


(
	m = ListMonad;
	
	a = 
		m.return(1)       >>= {|x|
		m.return(2)       >>= {|y|
		m.new([x+y, x-y]) >>= {|z|
		m.return(z*2)     }}};
	
	a.run;
)

(
	m = StateMonad;

	c = 
		m.get >>= {|x|
		m.put(x+1) >>= {
		m.return(x) }};

	a = 
		c >>= {|x|
		c >>= {|y|
		c >>= {|z|
		m.return([x,y,z]) }}};
	
	a.run(0);
)


(
	m = CPSMonad;

	f = {|n|
		if (n<1) {
			m.callcc{|break|
				c = break;	// store the continuation
				m.return(1)
			}
		}{
			f.(n-1) >>= {|r|
			(n*r).postln;
			m.return(n*r)
			}
		}
	};
	
	f.(3).run;
	
/*
	c.(1).run;
	c.(10).run;
	c.(7).run;
*/
)


( 
	m = ParserMonad;

	~space = 
		m.sat(_.isSpace).many;

	~number = 
		m.sat(_.isDecDigit).many1 >>= {|ds|
		~space >>= { 
		m.return(ds.join("").asFloat) }};

	~token = {|name|
		m.string(name) >>= {|n|
		~space >>= {
		m.return(n.join("")) }}};

	~exp0 = 
		~number mplus: 
		( 	
			~token.("(") >>= /*)*/{			
			~exp2       >>= {|e| /*(*/
			~token.(")") >>= {
			m.return(e) }}}
		);

	~exp1 = 	
		~exp0 >>= {|e1|
			(~token.("*") >>= { ~exp1 >>= {|e2| m.return(e1*e2) }})
			mplus:
			(~token.("/") >>= { ~exp1 >>= {|e2| m.return(e1/e2) }})
			mplus:
			m.return(e1)
		};
			
	~exp2 = 	
		~exp1 >>= {|e1|
			(~token.("+") >>= { ~exp2 >>= {|e2| m.return(e1+e2) }})
			mplus:
			(~token.("-") >>= { ~exp2 >>= {|e2| m.return(e1-e2) }})
			mplus:
			m.return(e1)
		};
			
	~exp2.run("2 +    3 *   7-(1)  ");

/*
	(~space >>= {~exp2}).run(" 1 +2  * 3     - 4 / 5 - 6");
*/
		
)


