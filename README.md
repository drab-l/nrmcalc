Calculate the given string as expression by calc function.

Supports user definable binary and unary operations.

Binary operation is defined as "left-operant @+alphanumeric "right-operand".
Unary operations is "[@+alphanumeric operand]".

The unary operation can omit "@+alphanumeric", in which case it is equivalent to @ only (alphanumeric is an empty string).
Binary and unary operations can be defined with set_custom1_cb and set_sqr_bra_cb function, where the first argument is "alphanumeric" string after @ and the second argument is the operation.


The syntax is follows.

		Syntax
		calc    : cmd
		          top_exp

		top_exp : asn_exp
		asn_exp : and_exp
		          var_exp [=,+=,-=,*=,/=,&=,^=,|=] asn_exp
		var_exp : [A-Za-z]...
		arg_var : $[1-9]
		and_exp : xor_exp
		          and_exp & xor_exp
		xor_exp : ior_exp
		          xor_exp ^ ior_exp
		ior_exp : eql_exp
		          ior_exp | eql_exp
		eql_exp : rel_exp
		          eql_exp [==,!=] rel_exp
		rel_exp : add_sub
		          rel_exp [<,>,<=,>=] add_sub
		add_sub : mul_div
		          add_sub [+,-] mul_div
		mul_div : custom1
		          mul_div [*,/] custom1
		par_exp : sqr_bra
		          (top_exp)
		sqr_bra : numeric
		          [[ ,@[[0-9A-Za-z]...]] top_exp]
		numeric : hexs
		          octs
		          digs
		          var_exp
		          arg_var

		custom1 : par_exp
		        : custom1 [@[ ,[0-9A-Za-z]...]] par_exp

		cmd     : @[0-9A-Za-z]... [ ,Args...]# if setted by set_cmd
		          @set_cmd[[0-9A-Za-z]...]=string
		          @str[top_exp]
		          @set_str[top_exp]=string
