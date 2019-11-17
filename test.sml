use "interpreter.sml";
val ast = ( APP( ( LAM( "zz" ,( APP( ( LAM( "zf" ,( APP( ( VAR( "zf" ) ),( VAR( "zz" ) ) ) ) ) ),( LAM( "y" ,( VAR( "zz" ) ) ) ) ) ) ) ),( LAM( "f" ,( LAM( "x" ,( VAR( "x" ) ) ) ) ) ) ) );
reducesTo ast