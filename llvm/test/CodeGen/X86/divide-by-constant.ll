; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=i686-pc-linux-gnu | FileCheck %s --check-prefix=X86
; RUN: llc < %s -mtriple=x86_64-pc-linux-gnu | FileCheck %s --check-prefixes=X64,X64-FAST
; RUN: llc < %s -mtriple=x86_64-pc-linux-gnu -mattr=idivq-to-divl | FileCheck %s --check-prefixes=X64,X64-SLOW

define zeroext i16 @test1(i16 zeroext %x) nounwind {
; X86-LABEL: test1:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movzwl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    imull $63551, %eax, %eax # imm = 0xF83F
; X86-NEXT:    shrl $21, %eax
; X86-NEXT:    # kill: def $ax killed $ax killed $eax
; X86-NEXT:    retl
;
; X64-LABEL: test1:
; X64:       # %bb.0: # %entry
; X64-NEXT:    imull $63551, %edi, %eax # imm = 0xF83F
; X64-NEXT:    shrl $21, %eax
; X64-NEXT:    # kill: def $ax killed $ax killed $eax
; X64-NEXT:    retq
entry:
  %div = udiv i16 %x, 33
  ret i16 %div
}

define zeroext i16 @test2(i8 signext %x, i16 zeroext %c) nounwind readnone ssp noredzone {
; X86-LABEL: test2:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movzwl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    imull $43691, %eax, %eax # imm = 0xAAAB
; X86-NEXT:    shrl $17, %eax
; X86-NEXT:    # kill: def $ax killed $ax killed $eax
; X86-NEXT:    retl
;
; X64-LABEL: test2:
; X64:       # %bb.0: # %entry
; X64-NEXT:    imull $43691, %esi, %eax # imm = 0xAAAB
; X64-NEXT:    shrl $17, %eax
; X64-NEXT:    # kill: def $ax killed $ax killed $eax
; X64-NEXT:    retq
entry:
  %div = udiv i16 %c, 3
  ret i16 %div

}

define zeroext i8 @test3(i8 zeroext %x, i8 zeroext %c) nounwind readnone ssp noredzone {
; X86-LABEL: test3:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    imull $171, %eax, %eax
; X86-NEXT:    shrl $9, %eax
; X86-NEXT:    # kill: def $al killed $al killed $eax
; X86-NEXT:    retl
;
; X64-LABEL: test3:
; X64:       # %bb.0: # %entry
; X64-NEXT:    imull $171, %esi, %eax
; X64-NEXT:    shrl $9, %eax
; X64-NEXT:    # kill: def $al killed $al killed $eax
; X64-NEXT:    retq
entry:
  %div = udiv i8 %c, 3
  ret i8 %div
}

define signext i16 @test4(i16 signext %x) nounwind {
; X86-LABEL: test4:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movswl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    imull $1986, %eax, %eax # imm = 0x7C2
; X86-NEXT:    movl %eax, %ecx
; X86-NEXT:    shrl $31, %ecx
; X86-NEXT:    shrl $16, %eax
; X86-NEXT:    addl %ecx, %eax
; X86-NEXT:    # kill: def $ax killed $ax killed $eax
; X86-NEXT:    retl
;
; X64-LABEL: test4:
; X64:       # %bb.0: # %entry
; X64-NEXT:    imull $1986, %edi, %eax # imm = 0x7C2
; X64-NEXT:    movl %eax, %ecx
; X64-NEXT:    shrl $31, %ecx
; X64-NEXT:    shrl $16, %eax
; X64-NEXT:    addl %ecx, %eax
; X64-NEXT:    # kill: def $ax killed $ax killed $eax
; X64-NEXT:    retq
entry:
  %div = sdiv i16 %x, 33		; <i32> [#uses=1]
  ret i16 %div
}

define i32 @test5(i32 %A) nounwind {
; X86-LABEL: test5:
; X86:       # %bb.0:
; X86-NEXT:    movl $365384439, %eax # imm = 0x15C752F7
; X86-NEXT:    mull {{[0-9]+}}(%esp)
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    shrl $27, %eax
; X86-NEXT:    retl
;
; X64-LABEL: test5:
; X64:       # %bb.0:
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    imulq $365384439, %rax, %rax # imm = 0x15C752F7
; X64-NEXT:    shrq $59, %rax
; X64-NEXT:    # kill: def $eax killed $eax killed $rax
; X64-NEXT:    retq
  %tmp1 = udiv i32 %A, 1577682821         ; <i32> [#uses=1]
  ret i32 %tmp1
}

define signext i16 @test6(i16 signext %x) nounwind {
; X86-LABEL: test6:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movswl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    imull $26215, %eax, %eax # imm = 0x6667
; X86-NEXT:    movl %eax, %ecx
; X86-NEXT:    shrl $31, %ecx
; X86-NEXT:    sarl $18, %eax
; X86-NEXT:    addl %ecx, %eax
; X86-NEXT:    # kill: def $ax killed $ax killed $eax
; X86-NEXT:    retl
;
; X64-LABEL: test6:
; X64:       # %bb.0: # %entry
; X64-NEXT:    imull $26215, %edi, %eax # imm = 0x6667
; X64-NEXT:    movl %eax, %ecx
; X64-NEXT:    shrl $31, %ecx
; X64-NEXT:    sarl $18, %eax
; X64-NEXT:    addl %ecx, %eax
; X64-NEXT:    # kill: def $ax killed $ax killed $eax
; X64-NEXT:    retq
entry:
  %div = sdiv i16 %x, 10
  ret i16 %div
}

define i32 @test7(i32 %x) nounwind {
; X86-LABEL: test7:
; X86:       # %bb.0:
; X86-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    shrl $2, %eax
; X86-NEXT:    movl $613566757, %ecx # imm = 0x24924925
; X86-NEXT:    mull %ecx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    retl
;
; X64-LABEL: test7:
; X64:       # %bb.0:
; X64-NEXT:    # kill: def $edi killed $edi def $rdi
; X64-NEXT:    shrl $2, %edi
; X64-NEXT:    imulq $613566757, %rdi, %rax # imm = 0x24924925
; X64-NEXT:    shrq $32, %rax
; X64-NEXT:    # kill: def $eax killed $eax killed $rax
; X64-NEXT:    retq
  %div = udiv i32 %x, 28
  ret i32 %div
}

; PR13326
define i8 @test8(i8 %x) nounwind {
; X86-LABEL: test8:
; X86:       # %bb.0:
; X86-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    shrb %al
; X86-NEXT:    movzbl %al, %eax
; X86-NEXT:    imull $211, %eax, %eax
; X86-NEXT:    shrl $13, %eax
; X86-NEXT:    # kill: def $al killed $al killed $eax
; X86-NEXT:    retl
;
; X64-LABEL: test8:
; X64:       # %bb.0:
; X64-NEXT:    shrb %dil
; X64-NEXT:    movzbl %dil, %eax
; X64-NEXT:    imull $211, %eax, %eax
; X64-NEXT:    shrl $13, %eax
; X64-NEXT:    # kill: def $al killed $al killed $eax
; X64-NEXT:    retq
  %div = udiv i8 %x, 78
  ret i8 %div
}

define i8 @test9(i8 %x) nounwind {
; X86-LABEL: test9:
; X86:       # %bb.0:
; X86-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    shrb $2, %al
; X86-NEXT:    movzbl %al, %eax
; X86-NEXT:    imull $71, %eax, %eax
; X86-NEXT:    shrl $11, %eax
; X86-NEXT:    # kill: def $al killed $al killed $eax
; X86-NEXT:    retl
;
; X64-LABEL: test9:
; X64:       # %bb.0:
; X64-NEXT:    shrb $2, %dil
; X64-NEXT:    movzbl %dil, %eax
; X64-NEXT:    imull $71, %eax, %eax
; X64-NEXT:    shrl $11, %eax
; X64-NEXT:    # kill: def $al killed $al killed $eax
; X64-NEXT:    retq
  %div = udiv i8 %x, 116
  ret i8 %div
}

define i32 @testsize1(i32 %x) minsize nounwind {
; X86-LABEL: testsize1:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    pushl $32
; X86-NEXT:    popl %ecx
; X86-NEXT:    cltd
; X86-NEXT:    idivl %ecx
; X86-NEXT:    retl
;
; X64-LABEL: testsize1:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    pushq $32
; X64-NEXT:    popq %rcx
; X64-NEXT:    cltd
; X64-NEXT:    idivl %ecx
; X64-NEXT:    retq
entry:
  %div = sdiv i32 %x, 32
  ret i32 %div
}

define i32 @testsize2(i32 %x) minsize nounwind {
; X86-LABEL: testsize2:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    pushl $33
; X86-NEXT:    popl %ecx
; X86-NEXT:    cltd
; X86-NEXT:    idivl %ecx
; X86-NEXT:    retl
;
; X64-LABEL: testsize2:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    pushq $33
; X64-NEXT:    popq %rcx
; X64-NEXT:    cltd
; X64-NEXT:    idivl %ecx
; X64-NEXT:    retq
entry:
  %div = sdiv i32 %x, 33
  ret i32 %div
}

define i32 @testsize3(i32 %x) minsize nounwind {
; X86-LABEL: testsize3:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    shrl $5, %eax
; X86-NEXT:    retl
;
; X64-LABEL: testsize3:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    shrl $5, %eax
; X64-NEXT:    retq
entry:
  %div = udiv i32 %x, 32
  ret i32 %div
}

define i32 @testsize4(i32 %x) minsize nounwind {
; X86-LABEL: testsize4:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NEXT:    pushl $33
; X86-NEXT:    popl %ecx
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    divl %ecx
; X86-NEXT:    retl
;
; X64-LABEL: testsize4:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    pushq $33
; X64-NEXT:    popq %rcx
; X64-NEXT:    xorl %edx, %edx
; X64-NEXT:    divl %ecx
; X64-NEXT:    retq
entry:
  %div = udiv i32 %x, 33
  ret i32 %div
}

define i64 @PR23590(i64 %x) nounwind {
; X86-LABEL: PR23590:
; X86:       # %bb.0: # %entry
; X86-NEXT:    subl $12, %esp
; X86-NEXT:    pushl $0
; X86-NEXT:    pushl $12345 # imm = 0x3039
; X86-NEXT:    pushl {{[0-9]+}}(%esp)
; X86-NEXT:    pushl {{[0-9]+}}(%esp)
; X86-NEXT:    calll __umoddi3
; X86-NEXT:    addl $16, %esp
; X86-NEXT:    pushl $0
; X86-NEXT:    pushl $7
; X86-NEXT:    pushl %edx
; X86-NEXT:    pushl %eax
; X86-NEXT:    calll __udivdi3
; X86-NEXT:    addl $28, %esp
; X86-NEXT:    retl
;
; X64-FAST-LABEL: PR23590:
; X64-FAST:       # %bb.0: # %entry
; X64-FAST-NEXT:    movabsq $6120523590596543007, %rcx # imm = 0x54F077C718E7C21F
; X64-FAST-NEXT:    movq %rdi, %rax
; X64-FAST-NEXT:    mulq %rcx
; X64-FAST-NEXT:    shrq $12, %rdx
; X64-FAST-NEXT:    imulq $12345, %rdx, %rax # imm = 0x3039
; X64-FAST-NEXT:    subq %rax, %rdi
; X64-FAST-NEXT:    movabsq $2635249153387078803, %rcx # imm = 0x2492492492492493
; X64-FAST-NEXT:    movq %rdi, %rax
; X64-FAST-NEXT:    mulq %rcx
; X64-FAST-NEXT:    movq %rdx, %rax
; X64-FAST-NEXT:    retq
;
; X64-SLOW-LABEL: PR23590:
; X64-SLOW:       # %bb.0: # %entry
; X64-SLOW-NEXT:    movabsq $6120523590596543007, %rcx # imm = 0x54F077C718E7C21F
; X64-SLOW-NEXT:    movq %rdi, %rax
; X64-SLOW-NEXT:    mulq %rcx
; X64-SLOW-NEXT:    shrq $12, %rdx
; X64-SLOW-NEXT:    imulq $12345, %rdx, %rax # imm = 0x3039
; X64-SLOW-NEXT:    subq %rax, %rdi
; X64-SLOW-NEXT:    imulq $613566757, %rdi, %rax # imm = 0x24924925
; X64-SLOW-NEXT:    shrq $32, %rax
; X64-SLOW-NEXT:    retq
entry:
  %rem = urem i64 %x, 12345
  %div = udiv i64 %rem, 7
  ret i64 %div
}

define { i64, i32 } @PR38622(i64) nounwind {
; X86-LABEL: PR38622:
; X86:       # %bb.0:
; X86-NEXT:    pushl %ebp
; X86-NEXT:    pushl %ebx
; X86-NEXT:    pushl %edi
; X86-NEXT:    pushl %esi
; X86-NEXT:    subl $12, %esp
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ebx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ebp
; X86-NEXT:    pushl $0
; X86-NEXT:    pushl $-294967296 # imm = 0xEE6B2800
; X86-NEXT:    pushl %ebp
; X86-NEXT:    pushl %ebx
; X86-NEXT:    calll __udivdi3
; X86-NEXT:    addl $16, %esp
; X86-NEXT:    movl %eax, %esi
; X86-NEXT:    movl %edx, %edi
; X86-NEXT:    pushl $0
; X86-NEXT:    pushl $-294967296 # imm = 0xEE6B2800
; X86-NEXT:    pushl %ebp
; X86-NEXT:    pushl %ebx
; X86-NEXT:    calll __umoddi3
; X86-NEXT:    addl $16, %esp
; X86-NEXT:    movl %eax, %ecx
; X86-NEXT:    movl %esi, %eax
; X86-NEXT:    movl %edi, %edx
; X86-NEXT:    addl $12, %esp
; X86-NEXT:    popl %esi
; X86-NEXT:    popl %edi
; X86-NEXT:    popl %ebx
; X86-NEXT:    popl %ebp
; X86-NEXT:    retl
;
; X64-LABEL: PR38622:
; X64:       # %bb.0:
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    shrq $11, %rax
; X64-NEXT:    movabsq $4835703278458517, %rcx # imm = 0x112E0BE826D695
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $9, %rax
; X64-NEXT:    imull $-294967296, %eax, %ecx # imm = 0xEE6B2800
; X64-NEXT:    subl %ecx, %edi
; X64-NEXT:    movl %edi, %edx
; X64-NEXT:    retq
  %2 = udiv i64 %0, 4000000000
  %3 = urem i64 %0, 4000000000
  %4 = trunc i64 %3 to i32
  %5 = insertvalue { i64, i32 } undef, i64 %2, 0
  %6 = insertvalue { i64, i32 } %5, i32 %4, 1
  ret { i64, i32 } %6
}

define { i64, i32 } @PR38622_signed(i64) nounwind {
; X86-LABEL: PR38622_signed:
; X86:       # %bb.0:
; X86-NEXT:    pushl %ebp
; X86-NEXT:    pushl %ebx
; X86-NEXT:    pushl %edi
; X86-NEXT:    pushl %esi
; X86-NEXT:    subl $12, %esp
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ebx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ebp
; X86-NEXT:    pushl $0
; X86-NEXT:    pushl $-294967296 # imm = 0xEE6B2800
; X86-NEXT:    pushl %ebp
; X86-NEXT:    pushl %ebx
; X86-NEXT:    calll __divdi3
; X86-NEXT:    addl $16, %esp
; X86-NEXT:    movl %eax, %esi
; X86-NEXT:    movl %edx, %edi
; X86-NEXT:    pushl $0
; X86-NEXT:    pushl $-294967296 # imm = 0xEE6B2800
; X86-NEXT:    pushl %ebp
; X86-NEXT:    pushl %ebx
; X86-NEXT:    calll __moddi3
; X86-NEXT:    addl $16, %esp
; X86-NEXT:    movl %eax, %ecx
; X86-NEXT:    movl %esi, %eax
; X86-NEXT:    movl %edi, %edx
; X86-NEXT:    addl $12, %esp
; X86-NEXT:    popl %esi
; X86-NEXT:    popl %edi
; X86-NEXT:    popl %ebx
; X86-NEXT:    popl %ebp
; X86-NEXT:    retl
;
; X64-LABEL: PR38622_signed:
; X64:       # %bb.0:
; X64-NEXT:    movabsq $1237940039285380275, %rcx # imm = 0x112E0BE826D694B3
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    imulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $63, %rax
; X64-NEXT:    sarq $28, %rdx
; X64-NEXT:    addq %rdx, %rax
; X64-NEXT:    imull $-294967296, %eax, %ecx # imm = 0xEE6B2800
; X64-NEXT:    subl %ecx, %edi
; X64-NEXT:    movl %edi, %edx
; X64-NEXT:    retq
  %2 = sdiv i64 %0, 4000000000
  %3 = srem i64 %0, 4000000000
  %4 = trunc i64 %3 to i32
  %5 = insertvalue { i64, i32 } undef, i64 %2, 0
  %6 = insertvalue { i64, i32 } %5, i32 %4, 1
  ret { i64, i32 } %6
}

define i64 @urem_i64_3(i64 %x) nounwind {
; X86-LABEL: urem_i64_3:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    addl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    adcl $0, %ecx
; X86-NEXT:    movl $-1431655765, %edx # imm = 0xAAAAAAAB
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    shrl %edx
; X86-NEXT:    leal (%edx,%edx,2), %eax
; X86-NEXT:    subl %eax, %ecx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_3:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-6148914691236517205, %rcx # imm = 0xAAAAAAAAAAAAAAAB
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    shrq %rdx
; X64-NEXT:    leaq (%rdx,%rdx,2), %rax
; X64-NEXT:    subq %rax, %rdi
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 3
  ret i64 %rem
}

define i64 @urem_i64_5(i64 %x) nounwind {
; X86-LABEL: urem_i64_5:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    addl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    adcl $0, %ecx
; X86-NEXT:    movl $-858993459, %edx # imm = 0xCCCCCCCD
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    shrl $2, %edx
; X86-NEXT:    leal (%edx,%edx,4), %eax
; X86-NEXT:    subl %eax, %ecx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_5:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-3689348814741910323, %rcx # imm = 0xCCCCCCCCCCCCCCCD
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    shrq $2, %rdx
; X64-NEXT:    leaq (%rdx,%rdx,4), %rax
; X64-NEXT:    subq %rax, %rdi
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 5
  ret i64 %rem
}

define i64 @urem_i64_15(i64 %x) nounwind {
; X86-LABEL: urem_i64_15:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    addl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    adcl $0, %ecx
; X86-NEXT:    movl $-2004318071, %edx # imm = 0x88888889
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    shrl $3, %edx
; X86-NEXT:    leal (%edx,%edx,4), %eax
; X86-NEXT:    leal (%eax,%eax,2), %eax
; X86-NEXT:    subl %eax, %ecx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_15:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-8608480567731124087, %rcx # imm = 0x8888888888888889
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    shrq $3, %rdx
; X64-NEXT:    leaq (%rdx,%rdx,4), %rax
; X64-NEXT:    leaq (%rax,%rax,2), %rax
; X64-NEXT:    subq %rax, %rdi
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 15
  ret i64 %rem
}

define i64 @urem_i64_17(i64 %x) nounwind {
; X86-LABEL: urem_i64_17:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    addl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    adcl $0, %ecx
; X86-NEXT:    movl $-252645135, %edx # imm = 0xF0F0F0F1
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    andl $-16, %eax
; X86-NEXT:    shrl $4, %edx
; X86-NEXT:    addl %eax, %edx
; X86-NEXT:    subl %edx, %ecx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_17:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-1085102592571150095, %rcx # imm = 0xF0F0F0F0F0F0F0F1
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    andq $-16, %rax
; X64-NEXT:    shrq $4, %rdx
; X64-NEXT:    addq %rax, %rdx
; X64-NEXT:    subq %rdx, %rdi
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 17
  ret i64 %rem
}

define i64 @urem_i64_255(i64 %x) nounwind {
; X86-LABEL: urem_i64_255:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %esi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    addl %esi, %eax
; X86-NEXT:    adcl $0, %eax
; X86-NEXT:    movl $-2139062143, %edx # imm = 0x80808081
; X86-NEXT:    mull %edx
; X86-NEXT:    shrl $7, %edx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    shll $8, %eax
; X86-NEXT:    subl %eax, %edx
; X86-NEXT:    addl %esi, %ecx
; X86-NEXT:    adcl %edx, %ecx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_255:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-9187201950435737471, %rcx # imm = 0x8080808080808081
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    shrq $7, %rdx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shlq $8, %rax
; X64-NEXT:    subq %rax, %rdx
; X64-NEXT:    leaq (%rdx,%rdi), %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 255
  ret i64 %rem
}

define i64 @urem_i64_257(i64 %x) nounwind {
; X86-LABEL: urem_i64_257:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    addl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    adcl $0, %ecx
; X86-NEXT:    movl $-16711935, %edx # imm = 0xFF00FF01
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    andl $-256, %eax
; X86-NEXT:    shrl $8, %edx
; X86-NEXT:    addl %eax, %edx
; X86-NEXT:    subl %edx, %ecx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_257:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-71777214294589695, %rcx # imm = 0xFF00FF00FF00FF01
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    andq $-256, %rax
; X64-NEXT:    shrq $8, %rdx
; X64-NEXT:    addq %rax, %rdx
; X64-NEXT:    subq %rdx, %rdi
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 257
  ret i64 %rem
}

define i64 @urem_i64_65535(i64 %x) nounwind {
; X86-LABEL: urem_i64_65535:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %esi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    addl %esi, %eax
; X86-NEXT:    adcl $0, %eax
; X86-NEXT:    movl $-2147450879, %edx # imm = 0x80008001
; X86-NEXT:    mull %edx
; X86-NEXT:    shrl $15, %edx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    shll $16, %eax
; X86-NEXT:    subl %eax, %edx
; X86-NEXT:    addl %esi, %ecx
; X86-NEXT:    adcl %edx, %ecx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_65535:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-9223231297218904063, %rcx # imm = 0x8000800080008001
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    shrq $15, %rdx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shlq $16, %rax
; X64-NEXT:    subq %rax, %rdx
; X64-NEXT:    leaq (%rdx,%rdi), %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 65535
  ret i64 %rem
}

define i64 @urem_i64_65537(i64 %x) nounwind {
; X86-LABEL: urem_i64_65537:
; X86:       # %bb.0: # %entry
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    addl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    adcl $0, %ecx
; X86-NEXT:    movl $-65535, %edx # imm = 0xFFFF0001
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    shrl $16, %eax
; X86-NEXT:    shldl $16, %edx, %eax
; X86-NEXT:    subl %eax, %ecx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_65537:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-281470681808895, %rcx # imm = 0xFFFF0000FFFF0001
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    andq $-65536, %rax # imm = 0xFFFF0000
; X64-NEXT:    shrq $16, %rdx
; X64-NEXT:    addq %rax, %rdx
; X64-NEXT:    subq %rdx, %rdi
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 65537
  ret i64 %rem
}

define i64 @urem_i64_12(i64 %x) nounwind {
; X86-LABEL: urem_i64_12:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    shrl $2, %eax
; X86-NEXT:    shldl $30, %esi, %ecx
; X86-NEXT:    addl %eax, %ecx
; X86-NEXT:    adcl $0, %ecx
; X86-NEXT:    movl $-1431655765, %edx # imm = 0xAAAAAAAB
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    shrl %edx
; X86-NEXT:    leal (%edx,%edx,2), %eax
; X86-NEXT:    subl %eax, %ecx
; X86-NEXT:    andl $3, %esi
; X86-NEXT:    leal (%esi,%ecx,4), %eax
; X86-NEXT:    xorl %edx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_12:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-6148914691236517205, %rcx # imm = 0xAAAAAAAAAAAAAAAB
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    shrq %rdx
; X64-NEXT:    andq $-4, %rdx
; X64-NEXT:    leaq (%rdx,%rdx,2), %rax
; X64-NEXT:    subq %rax, %rdi
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 12
  ret i64 %rem
}

define i64 @udiv_i64_3(i64 %x) nounwind {
; X86-LABEL: udiv_i64_3:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %ebx
; X86-NEXT:    pushl %edi
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %edi
; X86-NEXT:    movl %ecx, %esi
; X86-NEXT:    addl %edi, %esi
; X86-NEXT:    adcl $0, %esi
; X86-NEXT:    movl $-1431655765, %ebx # imm = 0xAAAAAAAB
; X86-NEXT:    movl %esi, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    shrl %edx
; X86-NEXT:    leal (%edx,%edx,2), %eax
; X86-NEXT:    subl %eax, %esi
; X86-NEXT:    subl %esi, %ecx
; X86-NEXT:    sbbl $0, %edi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    imull $-1431655766, %ecx, %ecx # imm = 0xAAAAAAAA
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    imull $-1431655765, %edi, %ecx # imm = 0xAAAAAAAB
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    popl %edi
; X86-NEXT:    popl %ebx
; X86-NEXT:    retl
;
; X64-LABEL: udiv_i64_3:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    movabsq $-6148914691236517205, %rcx # imm = 0xAAAAAAAAAAAAAAAB
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq %rax
; X64-NEXT:    retq
entry:
  %rem = udiv i64 %x, 3
  ret i64 %rem
}

define i64 @udiv_i64_5(i64 %x) nounwind {
; X86-LABEL: udiv_i64_5:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %ebx
; X86-NEXT:    pushl %edi
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %edi
; X86-NEXT:    movl %ecx, %esi
; X86-NEXT:    addl %edi, %esi
; X86-NEXT:    adcl $0, %esi
; X86-NEXT:    movl $-858993459, %ebx # imm = 0xCCCCCCCD
; X86-NEXT:    movl %esi, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    shrl $2, %edx
; X86-NEXT:    leal (%edx,%edx,4), %eax
; X86-NEXT:    subl %eax, %esi
; X86-NEXT:    subl %esi, %ecx
; X86-NEXT:    sbbl $0, %edi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    imull $-858993460, %ecx, %ecx # imm = 0xCCCCCCCC
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    imull $-858993459, %edi, %ecx # imm = 0xCCCCCCCD
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    popl %edi
; X86-NEXT:    popl %ebx
; X86-NEXT:    retl
;
; X64-LABEL: udiv_i64_5:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    movabsq $-3689348814741910323, %rcx # imm = 0xCCCCCCCCCCCCCCCD
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $2, %rax
; X64-NEXT:    retq
entry:
  %rem = udiv i64 %x, 5
  ret i64 %rem
}

define i64 @udiv_i64_15(i64 %x) nounwind {
; X86-LABEL: udiv_i64_15:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %edi
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %edi
; X86-NEXT:    movl %ecx, %esi
; X86-NEXT:    addl %edi, %esi
; X86-NEXT:    adcl $0, %esi
; X86-NEXT:    movl $-2004318071, %edx # imm = 0x88888889
; X86-NEXT:    movl %esi, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    shrl $3, %edx
; X86-NEXT:    leal (%edx,%edx,4), %eax
; X86-NEXT:    leal (%eax,%eax,2), %eax
; X86-NEXT:    subl %eax, %esi
; X86-NEXT:    subl %esi, %ecx
; X86-NEXT:    sbbl $0, %edi
; X86-NEXT:    movl $-286331153, %edx # imm = 0xEEEEEEEF
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    imull $-286331154, %ecx, %ecx # imm = 0xEEEEEEEE
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    imull $-286331153, %edi, %ecx # imm = 0xEEEEEEEF
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    popl %edi
; X86-NEXT:    retl
;
; X64-LABEL: udiv_i64_15:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    movabsq $-8608480567731124087, %rcx # imm = 0x8888888888888889
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $3, %rax
; X64-NEXT:    retq
entry:
  %rem = udiv i64 %x, 15
  ret i64 %rem
}

define i64 @udiv_i64_17(i64 %x) nounwind {
; X86-LABEL: udiv_i64_17:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %ebx
; X86-NEXT:    pushl %edi
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %edi
; X86-NEXT:    movl %ecx, %esi
; X86-NEXT:    addl %edi, %esi
; X86-NEXT:    adcl $0, %esi
; X86-NEXT:    movl $-252645135, %ebx # imm = 0xF0F0F0F1
; X86-NEXT:    movl %esi, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    andl $-16, %eax
; X86-NEXT:    shrl $4, %edx
; X86-NEXT:    addl %eax, %edx
; X86-NEXT:    subl %edx, %esi
; X86-NEXT:    subl %esi, %ecx
; X86-NEXT:    sbbl $0, %edi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    imull $-252645136, %ecx, %ecx # imm = 0xF0F0F0F0
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    imull $-252645135, %edi, %ecx # imm = 0xF0F0F0F1
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    popl %edi
; X86-NEXT:    popl %ebx
; X86-NEXT:    retl
;
; X64-LABEL: udiv_i64_17:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    movabsq $-1085102592571150095, %rcx # imm = 0xF0F0F0F0F0F0F0F1
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $4, %rax
; X64-NEXT:    retq
entry:
  %rem = udiv i64 %x, 17
  ret i64 %rem
}

define i64 @udiv_i64_255(i64 %x) nounwind {
; X86-LABEL: udiv_i64_255:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %esi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    addl %esi, %eax
; X86-NEXT:    adcl $0, %eax
; X86-NEXT:    movl $-2139062143, %edx # imm = 0x80808081
; X86-NEXT:    mull %edx
; X86-NEXT:    shrl $7, %edx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    shll $8, %eax
; X86-NEXT:    subl %eax, %edx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    addl %esi, %eax
; X86-NEXT:    adcl %edx, %eax
; X86-NEXT:    subl %eax, %ecx
; X86-NEXT:    sbbl $0, %esi
; X86-NEXT:    movl $-16843009, %edx # imm = 0xFEFEFEFF
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    imull $-16843010, %ecx, %ecx # imm = 0xFEFEFEFE
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    imull $-16843009, %esi, %ecx # imm = 0xFEFEFEFF
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    retl
;
; X64-LABEL: udiv_i64_255:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    movabsq $-9187201950435737471, %rcx # imm = 0x8080808080808081
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $7, %rax
; X64-NEXT:    retq
entry:
  %rem = udiv i64 %x, 255
  ret i64 %rem
}

define i64 @udiv_i64_257(i64 %x) nounwind {
; X86-LABEL: udiv_i64_257:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %ebx
; X86-NEXT:    pushl %edi
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %edi
; X86-NEXT:    movl %ecx, %esi
; X86-NEXT:    addl %edi, %esi
; X86-NEXT:    adcl $0, %esi
; X86-NEXT:    movl $-16711935, %ebx # imm = 0xFF00FF01
; X86-NEXT:    movl %esi, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    andl $-256, %eax
; X86-NEXT:    shrl $8, %edx
; X86-NEXT:    addl %eax, %edx
; X86-NEXT:    subl %edx, %esi
; X86-NEXT:    subl %esi, %ecx
; X86-NEXT:    sbbl $0, %edi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    imull $-16711936, %ecx, %ecx # imm = 0xFF00FF00
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    imull $-16711935, %edi, %ecx # imm = 0xFF00FF01
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    popl %edi
; X86-NEXT:    popl %ebx
; X86-NEXT:    retl
;
; X64-LABEL: udiv_i64_257:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    movabsq $-71777214294589695, %rcx # imm = 0xFF00FF00FF00FF01
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $8, %rax
; X64-NEXT:    retq
entry:
  %rem = udiv i64 %x, 257
  ret i64 %rem
}

define i64 @udiv_i64_65535(i64 %x) nounwind {
; X86-LABEL: udiv_i64_65535:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %esi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    addl %esi, %eax
; X86-NEXT:    adcl $0, %eax
; X86-NEXT:    movl $-2147450879, %edx # imm = 0x80008001
; X86-NEXT:    mull %edx
; X86-NEXT:    shrl $15, %edx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    shll $16, %eax
; X86-NEXT:    subl %eax, %edx
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    addl %esi, %eax
; X86-NEXT:    adcl %edx, %eax
; X86-NEXT:    subl %eax, %ecx
; X86-NEXT:    sbbl $0, %esi
; X86-NEXT:    movl $-65537, %edx # imm = 0xFFFEFFFF
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %edx
; X86-NEXT:    imull $-65538, %ecx, %ecx # imm = 0xFFFEFFFE
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    movl %esi, %ecx
; X86-NEXT:    shll $16, %ecx
; X86-NEXT:    addl %esi, %ecx
; X86-NEXT:    subl %ecx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    retl
;
; X64-LABEL: udiv_i64_65535:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    movabsq $-9223231297218904063, %rcx # imm = 0x8000800080008001
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $15, %rax
; X64-NEXT:    retq
entry:
  %rem = udiv i64 %x, 65535
  ret i64 %rem
}

define i64 @udiv_i64_65537(i64 %x) nounwind {
; X86-LABEL: udiv_i64_65537:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %ebx
; X86-NEXT:    pushl %edi
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %edi
; X86-NEXT:    movl %ecx, %esi
; X86-NEXT:    addl %edi, %esi
; X86-NEXT:    adcl $0, %esi
; X86-NEXT:    movl $-65535, %ebx # imm = 0xFFFF0001
; X86-NEXT:    movl %esi, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    movl %edx, %eax
; X86-NEXT:    shrl $16, %eax
; X86-NEXT:    shldl $16, %edx, %eax
; X86-NEXT:    subl %eax, %esi
; X86-NEXT:    subl %esi, %ecx
; X86-NEXT:    sbbl $0, %edi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    shll $16, %ecx
; X86-NEXT:    subl %ecx, %edx
; X86-NEXT:    movl %edi, %ecx
; X86-NEXT:    shll $16, %ecx
; X86-NEXT:    subl %ecx, %edi
; X86-NEXT:    addl %edi, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    popl %edi
; X86-NEXT:    popl %ebx
; X86-NEXT:    retl
;
; X64-LABEL: udiv_i64_65537:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    movabsq $-281470681808895, %rcx # imm = 0xFFFF0000FFFF0001
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $16, %rax
; X64-NEXT:    retq
entry:
  %rem = udiv i64 %x, 65537
  ret i64 %rem
}

define i64 @udiv_i64_12(i64 %x) nounwind {
; X86-LABEL: udiv_i64_12:
; X86:       # %bb.0: # %entry
; X86-NEXT:    pushl %ebx
; X86-NEXT:    pushl %edi
; X86-NEXT:    pushl %esi
; X86-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NEXT:    movl {{[0-9]+}}(%esp), %edi
; X86-NEXT:    shrdl $2, %edi, %ecx
; X86-NEXT:    shrl $2, %edi
; X86-NEXT:    movl %ecx, %esi
; X86-NEXT:    addl %edi, %esi
; X86-NEXT:    adcl $0, %esi
; X86-NEXT:    movl $-1431655765, %ebx # imm = 0xAAAAAAAB
; X86-NEXT:    movl %esi, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    shrl %edx
; X86-NEXT:    leal (%edx,%edx,2), %eax
; X86-NEXT:    subl %eax, %esi
; X86-NEXT:    subl %esi, %ecx
; X86-NEXT:    sbbl $0, %edi
; X86-NEXT:    movl %ecx, %eax
; X86-NEXT:    mull %ebx
; X86-NEXT:    imull $-1431655766, %ecx, %ecx # imm = 0xAAAAAAAA
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    imull $-1431655765, %edi, %ecx # imm = 0xAAAAAAAB
; X86-NEXT:    addl %ecx, %edx
; X86-NEXT:    popl %esi
; X86-NEXT:    popl %edi
; X86-NEXT:    popl %ebx
; X86-NEXT:    retl
;
; X64-LABEL: udiv_i64_12:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    movabsq $-6148914691236517205, %rcx # imm = 0xAAAAAAAAAAAAAAAB
; X64-NEXT:    mulq %rcx
; X64-NEXT:    movq %rdx, %rax
; X64-NEXT:    shrq $3, %rax
; X64-NEXT:    retq
entry:
  %rem = udiv i64 %x, 12
  ret i64 %rem
}

; Make sure we don't inline expand for optsize.
define i64 @urem_i64_3_optsize(i64 %x) nounwind optsize {
; X86-LABEL: urem_i64_3_optsize:
; X86:       # %bb.0: # %entry
; X86-NEXT:    subl $12, %esp
; X86-NEXT:    pushl $0
; X86-NEXT:    pushl $3
; X86-NEXT:    pushl {{[0-9]+}}(%esp)
; X86-NEXT:    pushl {{[0-9]+}}(%esp)
; X86-NEXT:    calll __umoddi3
; X86-NEXT:    addl $28, %esp
; X86-NEXT:    retl
;
; X64-LABEL: urem_i64_3_optsize:
; X64:       # %bb.0: # %entry
; X64-NEXT:    movabsq $-6148914691236517205, %rcx # imm = 0xAAAAAAAAAAAAAAAB
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    mulq %rcx
; X64-NEXT:    shrq %rdx
; X64-NEXT:    leaq (%rdx,%rdx,2), %rax
; X64-NEXT:    subq %rax, %rdi
; X64-NEXT:    movq %rdi, %rax
; X64-NEXT:    retq
entry:
  %rem = urem i64 %x, 3
  ret i64 %rem
}

