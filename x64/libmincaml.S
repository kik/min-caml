#if defined(__CYGWIN__) || defined(__MACH__)
#define U(x) _##x
#else
#define U(x) x
#endif

#define ALIGNSTACK and $0xfffffffffffffff0, %rsp

.text
.globl min_caml_print_newline
min_caml_print_newline:
	push	%rbp
	mov	%rsp, %rbp
	ALIGNSTACK
	mov     $10, %edi
	call	U(putchar)
	mov	%rbp, %rsp
	pop	%rbp
	ret
.globl min_caml_print_int
min_caml_print_int:
	push	%rbp
	mov	%rsp, %rbp
	ALIGNSTACK
        mov     %rax, %rsi
	mov     $format_int, %rdi
        xor     %eax, %eax
	call	U(printf)
	mov	%rbp, %rsp
	pop	%rbp
	ret
.globl min_caml_print_byte
min_caml_print_byte:
	push	%rbp
	mov	%rsp, %rbp
	ALIGNSTACK
        mov     %rax, %rdi
	call	U(putchar)
	mov	%rbp, %rsp
	pop	%rbp
	ret
.globl min_caml_prerr_int
min_caml_prerr_int:
	push	%rbp
	mov	%rsp, %rbp
	ALIGNSTACK
        mov     %rax, %rdx
	mov     $format_int, %rsi
        mov     U(min_caml_stderr), %rdi
        xor     %eax, %eax
	call	U(fprintf)
	mov	%rbp, %rsp
	pop	%rbp
	ret
.globl min_caml_prerr_byte
min_caml_prerr_byte:
	push	%rbp
	mov	%rsp, %rbp
	ALIGNSTACK
        mov     %rax, %rsi
        mov     U(min_caml_stderr), %rdi
	call	U(fputc)
	mov	%rbp, %rsp
	pop	%rbp
	ret
.globl min_caml_prerr_float
min_caml_prerr_float:
	push	%rbp
	mov	%rsp, %rbp
	ALIGNSTACK
        mov     $format_float, %rsi
        mov     U(min_caml_stderr), %rdi
        mov     $1, %eax
	call	U(fprintf)
	mov	%rbp, %rsp
	pop	%rbp
	ret
.globl min_caml_read_int
min_caml_read_int:
        push    %rbp
        mov     %rsp, %rbp
        sub     $8, %rsp
        ALIGNSTACK
        lea     -8(%rsp), %rsi
        mov     $format_int, %rdi
        xor     %eax, %eax
        call    U(scanf)
        mov     -8(%rbp), %eax
        mov     %rbp, %rsp
        pop     %rbp
        ret
.globl min_caml_read_float
min_caml_read_float:
        push    %rbp
        mov     %rsp, %rbp
        sub     $8, %rsp
        ALIGNSTACK
        lea     -8(%rsp), %rsi
        mov     $format_float, %rdi
        xor     %eax, %eax
        call    U(scanf)
        movsd   -8(%rbp), %xmm0
        mov     %rbp, %rsp
        pop     %rbp
        ret
.globl min_caml_create_array
min_caml_create_array:
        mov     %rax, %rcx
        mov     min_caml_hp, %rax
        mov     %rcx, %rdx
        shl     $3, %rdx
        add     %rdx, min_caml_hp
create_array_loop:
        cmp     $0, %rcx
        jne     create_array_cont
create_array_exit:
        ret
create_array_cont:
        dec     %rcx
        mov     %rbx, (%rax,%rcx,8)
        jmp     create_array_loop
.globl min_caml_create_float_array
min_caml_create_float_array:
        mov     %rax, %rcx
        mov     min_caml_hp, %rax
        mov     %rcx, %rdx
        shl     $3, %rdx
        add     %rdx, min_caml_hp
create_float_array_loop:
        cmp     $0, %rcx
        jne     create_float_array_cont
create_float_array_exit:
        ret
create_float_array_cont:
        dec     %rcx
        movsd   %xmm0, (%rax,%rcx,8)
        jmp     create_float_array_loop
.globl min_caml_abs_float
min_caml_abs_float:
        push    %rbp
        mov     %rsp, %rbp
        ALIGNSTACK
        call    U(fabs)
        mov     %rbp, %rsp
        pop     %rbp
        ret
.globl min_caml_sqrt
min_caml_sqrt:
	sqrtsd	%xmm0, %xmm0
	ret
.globl min_caml_floor
min_caml_floor:
        push    %rbp
        mov     %rsp, %rbp
        ALIGNSTACK
        call    U(floor)
        mov     %rbp, %rsp
        pop     %rbp
        ret
.globl min_caml_int_of_float
min_caml_int_of_float:
.globl min_caml_truncate
min_caml_truncate:
	cvttsd2si	%xmm0, %rax
	ret
.globl min_caml_float_of_int
min_caml_float_of_int:
	cvtsi2sd	%rax, %xmm0
	ret
.globl min_caml_cos
min_caml_cos:
        push    %rbp
        mov     %rsp, %rbp
        ALIGNSTACK
        call    U(cos)
        mov     %rbp, %rsp
        pop     %rbp
        ret
.globl min_caml_sin
min_caml_sin:
        push    %rbp
        mov     %rsp, %rbp
        ALIGNSTACK
        call    U(sin)
        mov     %rbp, %rsp
        pop     %rbp
        ret
.globl min_caml_atan
min_caml_atan:
        push    %rbp
        mov     %rsp, %rbp
        ALIGNSTACK
        call    U(atan)
        mov     %rbp, %rsp
        pop     %rbp
        ret
.data
format_int:
	.asciz	"%d"
format_float:
	.asciz	"%lf"
.balign 8
float_0:
	.long	0x0
	.long	0x0
float_1:
	.long	0x0
	.long	0x3ff00000
.balign 16
.globl min_caml_fnegd
min_caml_fnegd:
	.long	0
	.long	0x80000000
	.long	0
	.long	0
.globl min_caml_hp
min_caml_hp:	
	.long	0x0
	.long	0x0
