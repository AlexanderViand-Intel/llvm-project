; test that casted mallocs get converted to malloc of the right type
; RUN: llvm-upgrade < %s | llvm-as | opt -instcombine | llvm-dis | not grep bitcast

int* %test(uint %size) {
	%X = malloc long, uint %size
        %ret = bitcast long* %X to int*
	ret int* %ret
}
