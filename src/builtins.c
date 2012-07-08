/*
  implementations of some built-in functions and utilities
*/
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <setjmp.h>
#include <assert.h>
#include <sys/types.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#ifdef __WIN32__
#include <malloc.h>
#endif
#include <ctype.h>
#include <math.h>
#include "julia.h"
#include "builtin_proto.h"

// exceptions -----------------------------------------------------------------

void jl_error(const char *str)
{
    if (jl_errorexception_type == NULL) {
        JL_PRINTF(JL_STDERR, "%s", str);
        jl_exit(1);
    }
    jl_value_t *msg = jl_pchar_to_string((char*)str, strlen(str));
    JL_GC_PUSH(&msg);
    jl_raise(jl_new_struct(jl_errorexception_type, msg));
}

void jl_errorf(const char *fmt, ...)
{
    char buf[1024];
    va_list args;
    va_start(args, fmt);
    int nc = vsnprintf(buf, sizeof(buf), fmt, args);
    va_end(args);
    if (jl_errorexception_type == NULL) {
        JL_PRINTF(JL_STDERR, "%s", &buf);
        jl_exit(1);
    }
    jl_value_t *msg = jl_pchar_to_string(buf, nc);
    JL_GC_PUSH(&msg);
    jl_raise(jl_new_struct(jl_errorexception_type, msg));
}

void jl_too_few_args(const char *fname, int min)
{
    // TODO: ArgumentError
    jl_errorf("%s: too few arguments (expected %d)", fname, min);
}

void jl_too_many_args(const char *fname, int max)
{
    jl_errorf("%s: too many arguments (expected %d)", fname, max);
}

void jl_type_error_rt(const char *fname, const char *context,
                      jl_value_t *ty, jl_value_t *got)
{
    jl_value_t *ctxt=NULL;
    JL_GC_PUSH(&ctxt, &got);
    ctxt = jl_pchar_to_string((char*)context, strlen(context));
    jl_value_t *ex = jl_new_struct(jl_typeerror_type, jl_symbol(fname),
                                   ctxt, ty, got);
    jl_raise(ex);
}

void jl_type_error(const char *fname, jl_value_t *expected, jl_value_t *got)
{
    jl_type_error_rt(fname, "", expected, got);
}

JL_CALLABLE(jl_f_throw)
{
    JL_NARGS(throw, 1, 1);
    jl_raise(args[0]);
    return (jl_value_t*)jl_null;
}

void jl_enter_handler(jl_savestate_t *ss, jmp_buf *handlr)
{
    JL_SIGATOMIC_BEGIN();
    ss->eh_task = jl_current_task->state.eh_task;
    ss->eh_ctx = jl_current_task->state.eh_ctx;
    ss->bt = jl_current_task->state.bt;
    ss->ostream_obj = jl_current_task->state.ostream_obj;
    ss->prev = jl_current_task->state.prev;
#ifdef JL_GC_MARKSWEEP
    ss->gcstack = jl_pgcstack;
#endif

    jl_current_task->state.prev = ss;
    jl_current_task->state.eh_task = jl_current_task;
    jl_current_task->state.eh_ctx = handlr;
    jl_current_task->state.bt = 0;
    // TODO: this should really go after setjmp(). see comment in
    // ctx_switch in task.c.
    JL_SIGATOMIC_END();
}

void jl_pop_handler(int n)
{
    while (n > 0) {
        jl_eh_restore_state(jl_current_task->state.prev);
        n--;
    }
}

// primitives -----------------------------------------------------------------

int jl_egal(jl_value_t *a, jl_value_t *b)
{
    if (a == b)
        return 1;
    jl_value_t *ta = (jl_value_t*)jl_typeof(a);
    if (ta != (jl_value_t*)jl_typeof(b))
        return 0;
    if (jl_is_bits_type(ta)) {
        size_t nb = jl_bitstype_nbits(ta)/8;
        switch (nb) {
        case 1:
            return *(int8_t*)jl_bits_data(a) == *(int8_t*)jl_bits_data(b);
        case 2:
            return *(int16_t*)jl_bits_data(a) == *(int16_t*)jl_bits_data(b);
        case 4:
            return *(int32_t*)jl_bits_data(a) == *(int32_t*)jl_bits_data(b);
        case 8:
            return *(int64_t*)jl_bits_data(a) == *(int64_t*)jl_bits_data(b);
        default:
            return memcmp(jl_bits_data(a), jl_bits_data(b), nb)==0;
        }
    }
    if (jl_is_tuple(a)) {
        size_t l = jl_tuple_len(a);
        if (l != jl_tuple_len(b))
            return 0;
        for(size_t i=0; i < l; i++) {
            if (!jl_egal(jl_tupleref(a,i),jl_tupleref(b,i)))
                return 0;
        }
        return 1;
    }
    return 0;
}

JL_CALLABLE(jl_f_is)
{
    JL_NARGS(is, 2, 2);
    if (args[0] == args[1])
        return jl_true;
    return jl_egal(args[0],args[1]) ? jl_true : jl_false;
}

JL_CALLABLE(jl_f_no_function)
{
    jl_error("type cannot be constructed");
    return (jl_value_t*)jl_null;
}

JL_CALLABLE(jl_f_typeof)
{
    JL_NARGS(typeof, 1, 1);
    return jl_full_type(args[0]);
}

JL_CALLABLE(jl_f_subtype)
{
    JL_NARGS(subtype, 2, 2);
    if (!jl_is_typevar(args[0]))
        JL_TYPECHK(subtype, type, args[0]);
    if (!jl_is_typevar(args[1]))
        JL_TYPECHK(subtype, type, args[1]);
    return (jl_subtype(args[0],args[1],0) ? jl_true : jl_false);
}

JL_CALLABLE(jl_f_isa)
{
    JL_NARGS(isa, 2, 2);
    JL_TYPECHK(isa, type, args[1]);
    return (jl_subtype(args[0],args[1],1) ? jl_true : jl_false);
}

JL_CALLABLE(jl_f_typeassert)
{
    JL_NARGS(typeassert, 2, 2);
    JL_TYPECHK(typeassert, type, args[1]);
    if (!jl_subtype(args[0],args[1],1))
        jl_type_error("typeassert", args[1], args[0]);
    return args[0];
}

static jl_function_t *jl_append_any_func;

JL_CALLABLE(jl_f_apply)
{
    JL_NARGSV(apply, 1);
    JL_TYPECHK(apply, function, args[0]);
    if (nargs == 2 && jl_is_tuple(args[1])) {
        return jl_apply((jl_function_t*)args[0], &jl_tupleref(args[1],0),
                        jl_tuple_len(args[1]));
    }
    size_t n=0, i, j;
    for(i=1; i < nargs; i++) {
        if (jl_is_tuple(args[i])) {
            n += jl_tuple_len(args[i]);
        }
        else if (jl_typeis(args[i], jl_array_any_type)) {
            n += jl_array_len(args[i]);
        }
        else {
            if (jl_append_any_func == NULL) {
                jl_append_any_func =
                    (jl_function_t*)jl_get_global(jl_base_module,
                                                  jl_symbol("append_any"));
                if (jl_append_any_func == NULL) {
                    // error if append_any not available
                    JL_TYPECHK(apply, tuple, args[i]);
                }
            }
            goto fancy_apply;
        }
    }
    jl_value_t **newargs = alloca(n * sizeof(jl_value_t*));
    n = 0;
    for(i=1; i < nargs; i++) {
        if (jl_is_tuple(args[i])) {
            jl_tuple_t *t = (jl_tuple_t*)args[i];
            for(j=0; j < jl_tuple_len(t); j++)
                newargs[n++] = jl_tupleref(t, j);
        }
        else {
            size_t al = jl_array_len(args[i]);
            for(j=0; j < al; j++)
                newargs[n++] = jl_cellref(args[i], j);
        }
    }
    return jl_apply((jl_function_t*)args[0], newargs, n);

 fancy_apply: ;
    jl_value_t *argarr = jl_apply(jl_append_any_func, &args[1], nargs-1);
    JL_GC_PUSH(&argarr);
    assert(jl_typeis(argarr, jl_array_any_type));
    jl_value_t *result = jl_apply((jl_function_t*)args[0],
                                  jl_cell_data(argarr), jl_array_len(argarr));
    JL_GC_POP();
    return result;
}

// eval -----------------------------------------------------------------------

JL_CALLABLE(jl_f_top_eval)
{
    if (nargs != 2) {
        JL_NARGS(eval, 1, 1);
    }
    jl_expr_t *ex = (jl_expr_t*)args[nargs-1];
    if (jl_is_expr(ex) && (ex->head == export_sym ||
                           ex->head == import_sym ||
                           ex->head == importall_sym)) {
        jl_errorf("unsupported or misplaced expression %s", ex->head->name);
    }
    if (nargs == 1) {
        return jl_toplevel_eval((jl_value_t*)ex);
    }
    JL_TYPECHK(eval, module, args[0]);
    jl_module_t *m = (jl_module_t*)args[0];
    if (jl_is_symbol(args[1])) {
        return jl_eval_global_var(m, (jl_sym_t*)args[1]);
    }
    jl_value_t *v = NULL;
    jl_module_t *last_m = jl_current_module;
    JL_TRY {
        jl_current_module = m;
        v = jl_toplevel_eval((jl_value_t*)ex);
    }
    JL_CATCH {
        jl_current_module = last_m;
        jl_raise(jl_exception_in_transit);
    }
    return v;
}

JL_CALLABLE(jl_f_isbound)
{
    jl_module_t *m = jl_current_module;
    jl_sym_t *s=NULL;
    if (nargs == 1) {
        JL_TYPECHK(isbound, symbol, args[0]);
        s = (jl_sym_t*)args[0];
    }
    if (nargs != 2) {
        JL_NARGS(isbound, 1, 1);
    }
    else {
        JL_TYPECHK(isbound, module, args[0]);
        JL_TYPECHK(isbound, symbol, args[1]);
        m = (jl_module_t*)args[0];
        s = (jl_sym_t*)args[1];
    }
    assert(s);
    return jl_boundp(m, s) ? jl_true : jl_false;
}

// tuples ---------------------------------------------------------------------

JL_CALLABLE(jl_f_tuple)
{
    size_t i;
    if (nargs == 0) return (jl_value_t*)jl_null;
    jl_tuple_t *t = jl_alloc_tuple_uninit(nargs);
    for(i=0; i < nargs; i++) {
        jl_tupleset(t, i, args[i]);
    }
    return (jl_value_t*)t;
}

JL_CALLABLE(jl_f_tupleref)
{
    JL_NARGS(tupleref, 2, 2);
    JL_TYPECHK(tupleref, tuple, args[0]);
    JL_TYPECHK(tupleref, long, args[1]);
    jl_tuple_t *t = (jl_tuple_t*)args[0];
    size_t i = jl_unbox_long(args[1])-1;
    if (i >= jl_tuple_len(t))
        jl_error("tupleref: index out of range");
    return jl_tupleref(t, i);
}

JL_CALLABLE(jl_f_tuplelen)
{
    JL_NARGS(tuplelen, 1, 1);
    JL_TYPECHK(tuplelen, tuple, args[0]);
    return jl_box_long(jl_tuple_len(args[0]));
}

// composite types ------------------------------------------------------------

static size_t field_offset(jl_struct_type_t *t, jl_sym_t *fld, int err)
{
    jl_tuple_t *fn = t->names;
    size_t i;
    for(i=0; i < jl_tuple_len(fn); i++) {
        if (jl_tupleref(fn,i) == (jl_value_t*)fld) {
            return i;
        }
    }
    if (err)
        jl_errorf("type %s has no field %s", t->name->name->name, fld->name);
    return -1;
}

size_t jl_field_offset(jl_struct_type_t *t, jl_sym_t *fld)
{
    return field_offset(t, fld, 0);
}

static jl_value_t *nth_field(jl_value_t *v, size_t i)
{
    jl_value_t *fld = ((jl_value_t**)v)[1+i];
    if (fld == NULL)
        jl_raise(jl_undefref_exception);
    return fld;
}

JL_CALLABLE(jl_f_get_field)
{
    JL_NARGS(getfield, 2, 2);
    JL_TYPECHK(getfield, symbol, args[1]);
    jl_value_t *v = args[0];
    jl_value_t *vt = (jl_value_t*)jl_typeof(v);
    if (vt == (jl_value_t*)jl_module_type) {
        return jl_eval_global_var((jl_module_t*)v, (jl_sym_t*)args[1]);
    }
    if (!jl_is_struct_type(vt)) {
        jl_type_error("getfield", (jl_value_t*)jl_struct_kind, v);
    }
    size_t i = field_offset((jl_struct_type_t*)vt, (jl_sym_t*)args[1], 1);
    return nth_field(v, i);
}

JL_CALLABLE(jl_f_set_field)
{
    JL_NARGS(setfield, 3, 3);
    JL_TYPECHK(setfield, symbol, args[1]);
    jl_value_t *v = args[0];
    jl_value_t *vt = (jl_value_t*)jl_typeof(v);
    if (!jl_is_struct_type(vt))
        jl_type_error("setfield", (jl_value_t*)jl_struct_kind, v);
    jl_struct_type_t *st = (jl_struct_type_t*)vt;
    size_t i = field_offset(st, (jl_sym_t*)args[1], 1);
    jl_value_t *ft = jl_tupleref(st->types,i);
    if (!jl_subtype(args[2], ft, 1)) {
        jl_type_error("setfield", ft, args[2]);
    }
    ((jl_value_t**)v)[1+i] = args[2];
    return args[2];
}

JL_CALLABLE(jl_f_field_type)
{
    JL_NARGS(fieldtype, 2, 2);
    JL_TYPECHK(fieldtype, symbol, args[1]);
    jl_value_t *v = args[0];
    jl_value_t *vt = (jl_value_t*)jl_typeof(v);
    if (!jl_is_struct_type(vt))
        jl_type_error("fieldtype", (jl_value_t*)jl_struct_kind, v);
    jl_struct_type_t *st = (jl_struct_type_t*)vt;
    size_t i = field_offset(st, (jl_sym_t*)args[1], 1);
    return jl_tupleref(st->types, i);
}

// conversion -----------------------------------------------------------------

static jl_value_t *convert(jl_type_t *to, jl_value_t *x, jl_function_t *conv_f)
{
    jl_value_t *args[2];
    if (jl_subtype(x, (jl_value_t*)to, 1))
        return x;
    args[0] = (jl_value_t*)to; args[1] = x;
    return jl_apply(conv_f, args, 2);
}

JL_CALLABLE(jl_f_convert_tuple)
{
    jl_tuple_t *to = (jl_tuple_t*)args[0];
    jl_tuple_t *x = (jl_tuple_t*)args[1];
    if (to == jl_tuple_type)
        return (jl_value_t*)x;
    size_t i, cl=jl_tuple_len(x), pl=jl_tuple_len(to);
    jl_tuple_t *out = jl_alloc_tuple(cl);
    JL_GC_PUSH(&out);
    jl_value_t *ce, *pe=NULL;
    int pseq=0;
    jl_function_t *f = (jl_function_t*)args[2];
    for(i=0; i < cl; i++) {
        ce = jl_tupleref(x,i);
        if (pseq) {
        }
        else if (i < pl) {
            pe = jl_tupleref(to,i);
            if (jl_is_seq_type(pe)) {
                pe = jl_tparam0(pe);
                pseq = 1;
            }
        }
        else {
            out = NULL;
            break;
        }
        assert(pe != NULL);
        jl_tupleset(out, i, convert((jl_type_t*)pe, ce, f));
    }
    JL_GC_POP();
    if (out == NULL)
        jl_error("convert: invalid tuple conversion");
    return (jl_value_t*)out;
}

JL_CALLABLE(jl_f_convert_default)
{
    jl_type_t *to = (jl_type_t*)args[0];
    jl_value_t *x = args[1];
    if (!jl_subtype(x, (jl_value_t*)to, 1)) {
        jl_no_method_error((jl_function_t*)args[2], args, 2);
    }
    return x;
}

DLLEXPORT void *jl_symbol_name(jl_sym_t *s)
{
    return s->name;
}

//WARNING: THIS FUNCTION IS NEVER CALLED BUT INLINE BY CCALL
DLLEXPORT void *jl_array_ptr(jl_array_t *a)
{
    return a->data;
}

// printing -------------------------------------------------------------------

DLLEXPORT void jl_print_symbol(JL_STREAM *s, jl_sym_t *sym)
{
    JL_PUTS(sym->name,s);
}

// for bootstrap
DLLEXPORT void jl_print_int64(JL_STREAM *s, int64_t i)
{
    JL_PRINTF(s, "%lld", i);
}

DLLEXPORT int jl_strtod(char *str, double *out)
{
    char *p;
    errno = 0;
    *out = strtod(str, &p);
    if (p == str ||
        (errno==ERANGE && (*out==0 || *out==HUGE_VAL || *out==-HUGE_VAL)))
        return 1;
    while (*p != '\0') {
        if (!isspace(*p))
            return 1;
        p++;
    }
    return 0;
}

DLLEXPORT int jl_strtof(char *str, float *out)
{
    char *p;
    errno = 0;
    *out = strtof(str, &p);
    if (p == str ||
        (errno==ERANGE && (*out==0 || *out==HUGE_VALF || *out==-HUGE_VALF)))
        return 1;
    while (*p != '\0') {
        if (!isspace(*p))
            return 1;
        p++;
    }
    return 0;
}

// showing --------------------------------------------------------------------

jl_value_t *jl_stdout_obj()
{
    return jl_get_global(jl_base_module, jl_symbol("stdout_stream"));
}

jl_value_t *jl_stderr_obj()
{
    return jl_get_global(jl_base_module, jl_symbol("stderr_stream"));
}

static jl_function_t *jl_show_gf=NULL;

void jl_show(jl_value_t *stream, jl_value_t *v)
{
    if (jl_base_module) {
        if (jl_show_gf == NULL) {
            jl_show_gf = (jl_function_t*)jl_get_global(jl_base_module, jl_symbol("show"));
        }
        jl_value_t *args[2] = {stream,v};
        jl_apply(jl_show_gf, args, 2);
    }
}

// comma_one prints a comma for 1 element, e.g. "(x,)"
void jl_show_tuple(jl_value_t *st, jl_tuple_t *t, char opn, char cls, int comma_one)
{
    ios_t *s = (ios_t*)jl_iostr_data(st);
    JL_PUTC(opn, s);
    size_t i, n=jl_tuple_len(t);
    for(i=0; i < n; i++) {
        jl_show(st, jl_tupleref(t, i));
        if ((i < n-1) || (n==1 && comma_one))
            JL_PUTC(',', s);
    }
    JL_PUTC(cls, s);
}

static void show_function(JL_STREAM *s, jl_value_t *v)
{
    if (jl_is_gf(v)) {
        JL_PUTS(jl_gf_name(v)->name, s);
    }
    else {
        JL_PUTS("#<function>", s);
    }
}

static void show_type(jl_value_t *st, jl_value_t *t)
{
    ios_t *s = (ios_t*)jl_iostr_data(st);
    if (jl_is_union_type(t)) {
        if (t == (jl_value_t*)jl_bottom_type) {
            JL_WRITE(s, "None", 4);
        }
        else if (t == jl_top_type) {
            JL_WRITE(s, "Top", 3);
        }
        else {
            JL_WRITE(s, "Union", 5);
            jl_show_tuple(st, ((jl_uniontype_t*)t)->types, '(', ')', 0);
        }
    }
    else if (jl_is_seq_type(t)) {
        jl_show(st, jl_tparam0(t));
        JL_WRITE(s, "...", 3);
    }
    else if (jl_is_typector(t)) {
        jl_show(st, (jl_value_t*)((jl_typector_t*)t)->body);
    }
    else {
        assert(jl_is_some_tag_type(t));
        jl_tag_type_t *tt = (jl_tag_type_t*)t;
        JL_PUTS(tt->name->name->name, s);
        jl_tuple_t *p = tt->parameters;
        if (jl_tuple_len(p) > 0)
            jl_show_tuple(st, p, '{', '}', 0);
    }
}

DLLEXPORT void jl_show_any(jl_value_t *str, jl_value_t *v)
{
    ios_t *s = (ios_t*)jl_iostr_data(str);
    // fallback for printing some other builtin types
    if (jl_is_tuple(v)) {
        jl_show_tuple(str, (jl_tuple_t*)v, '(', ')', 1);
    }
    else if (jl_is_type(v)) {
        show_type(str, v);
    }
    else if (jl_is_func(v)) {
        show_function(s, v);
    }
    else if (jl_typeis(v,jl_intrinsic_type)) {
        JL_PRINTF(s, "#<intrinsic-function %d>", *(uint32_t*)jl_bits_data(v));
    }
    else {
        jl_value_t *t = (jl_value_t*)jl_typeof(v);
        if (jl_is_struct_type(t)) {
            jl_struct_type_t *st = (jl_struct_type_t*)t;
            JL_PUTS(st->name->name->name, s);
            JL_PUTC('(', s);
            size_t i;
            size_t n = jl_tuple_len(st->names);
            for(i=0; i < n; i++) {
                jl_show(str, nth_field(v, i));
                if (i < n-1)
                    JL_PUTC(',', s);
            }
            JL_PUTC(')', s);
        }
    }
}

// internal functions ---------------------------------------------------------

JL_CALLABLE(jl_trampoline)
{
    assert(jl_is_func(F));
    assert(((jl_function_t*)F)->linfo != NULL);
    /* // to run inference on all thunks. slows down loading files.
    if (F->linfo->inferred == jl_false) {
        if (!jl_in_inference) {
            jl_type_infer(F->linfo, jl_tuple_type, F->linfo);
        }
    }*/
    jl_compile((jl_function_t*)F);
    assert(((jl_function_t*)F)->fptr == &jl_trampoline);
    jl_generate_fptr((jl_function_t*)F);
    return jl_apply((jl_function_t*)F, args, nargs);
}

JL_CALLABLE(jl_f_instantiate_type)
{
    JL_NARGSV(instantiate_type, 1);
    if (!jl_is_some_tag_type(args[0]))
        JL_TYPECHK(instantiate_type, typector, args[0]);
    return jl_apply_type_(args[0], &args[1], nargs-1);
}

JL_CALLABLE(jl_f_new_type_constructor)
{
    JL_NARGS(new_type_constructor, 2, 2);
    JL_TYPECHK(new_type_constructor, tuple, args[0]);
    if (!jl_is_type(args[1]))
        jl_type_error("typealias", (jl_value_t*)jl_type_type, args[1]);
    jl_tuple_t *p = (jl_tuple_t*)args[0];
    return (jl_value_t*)jl_new_type_ctor(p, (jl_type_t*)args[1]);
}

JL_CALLABLE(jl_f_typevar)
{
    if (nargs < 1 || nargs > 3) {
        JL_NARGS(typevar, 1, 1);
    }
    JL_TYPECHK(typevar, symbol, args[0]);
    if (jl_boundp(jl_current_module, (jl_sym_t*)args[0]) &&
        jl_is_type(jl_get_global(jl_current_module, (jl_sym_t*)args[0]))) {
        ios_printf(ios_stderr, "Warning: type parameter name %s shadows an identifier\n", ((jl_sym_t*)args[0])->name);
    }
    jl_value_t *lb = (jl_value_t*)jl_bottom_type;
    jl_value_t *ub = (jl_value_t*)jl_any_type;
    int b = 0;
    if (args[nargs-1] == jl_true) {
        b = 1;
        nargs--;
    }
    if (nargs > 1) {
        JL_TYPECHK(typevar, type, args[1]);
        if (nargs > 2) {
            JL_TYPECHK(typevar, type, args[2]);
            lb = args[1];
            ub = args[2];
        }
        else {
            ub = args[1];
        }
    }
    jl_tvar_t *tv = jl_new_typevar((jl_sym_t*)args[0], lb, ub);
    tv->bound = b;
    return (jl_value_t*)tv;
}

JL_CALLABLE(jl_f_union)
{
    if (nargs == 0) return (jl_value_t*)jl_bottom_type;
    if (nargs == 1) return args[0];
    size_t i;
    jl_tuple_t *argt = jl_alloc_tuple_uninit(nargs);
    for(i=0; i < nargs; i++) {
        if (!jl_is_type(args[i]) && !jl_is_typevar(args[i])) {
            jl_error("invalid union type");
        }
        else {
            jl_tupleset(argt, i, args[i]);
        }
    }
    JL_GC_PUSH(&argt);
    jl_value_t *u = jl_type_union(argt);
    JL_GC_POP();
    return u;
}

// generic function reflection ------------------------------------------------

JL_CALLABLE(jl_f_methodexists)
{
    JL_NARGS(method_exists, 2, 2);
    JL_TYPECHK(method_exists, function, args[0]);
    if (!jl_is_gf(args[0]))
        jl_error("method_exists: not a generic function");
    JL_TYPECHK(method_exists, tuple, args[1]);
    jl_check_type_tuple((jl_tuple_t*)args[1], jl_gf_name(args[0]),
                        "method_exists");
    return jl_method_lookup_by_type(jl_gf_mtable(args[0]),
                                    (jl_tuple_t*)args[1], 0) != jl_bottom_func ?
        jl_true : jl_false;
}

JL_CALLABLE(jl_f_applicable)
{
    JL_NARGSV(applicable, 1);
    JL_TYPECHK(applicable, function, args[0]);
    if (!jl_is_gf(args[0]))
        jl_error("applicable: not a generic function");
    return jl_method_lookup(jl_gf_mtable(args[0]),
                            &args[1], nargs-1, 0) != jl_bottom_func ?
        jl_true : jl_false;
}

JL_CALLABLE(jl_f_invoke)
{
    JL_NARGSV(invoke, 2);
    JL_TYPECHK(invoke, function, args[0]);
    if (!jl_is_gf(args[0]))
        jl_error("invoke: not a generic function");
    JL_TYPECHK(invoke, tuple, args[1]);
    jl_check_type_tuple((jl_tuple_t*)args[1], jl_gf_name(args[0]), "invoke");
    if (!jl_tuple_subtype(&args[2], nargs-2, &jl_tupleref(args[1],0),
                          jl_tuple_len(args[1]), 1, 0))
        jl_error("invoke: argument type error");
    return jl_gf_invoke((jl_function_t*)args[0],
                        (jl_tuple_t*)args[1], &args[2], nargs-2);
}

// eq hash table --------------------------------------------------------------

#include "table.c"

// hashing --------------------------------------------------------------------

#ifdef __LP64__
#define bitmix(a,b) int64hash((a)^bswap_64(b))
#define hash64(a)   int64hash(a)
#else
#define bitmix(a,b) int64to32hash((((uint64_t)a)<<32)|((uint64_t)b))
#define hash64(a)   int64to32hash(a)
#endif

DLLEXPORT uptrint_t jl_uid(jl_value_t *v)
{
    if (jl_is_symbol(v))
        return ((jl_sym_t*)v)->hash;
    jl_value_t *tv = (jl_value_t*)jl_typeof(v);
    if (jl_is_struct_type(tv))
        return inthash((uptrint_t)v);
    if (jl_is_bits_type(tv)) {
        size_t nb = jl_bitstype_nbits(tv)/8;
        uptrint_t h = inthash((uptrint_t)tv);
        switch (nb) {
        case 1:
            return int32hash(*(int8_t*)jl_bits_data(v) ^ h);
        case 2:
            return int32hash(*(int16_t*)jl_bits_data(v) ^ h);
        case 4:
            return int32hash(*(int32_t*)jl_bits_data(v) ^ h);
        case 8:
            return hash64(*(int64_t*)jl_bits_data(v) ^ h);
        default:
#ifdef __LP64__
            return h ^ memhash((char*)jl_bits_data(v), nb);
#else
            return h ^ memhash32((char*)jl_bits_data(v), nb);
#endif
        }
    }
    assert(jl_is_tuple(v));
    uptrint_t h = 0;
    size_t l = jl_tuple_len(v);
    for(size_t i = 0; i < l; i++) {
        uptrint_t u = jl_uid(jl_tupleref(v,i));
        h = bitmix(h, u);
    }
    return h;
}

// init -----------------------------------------------------------------------

static void add_builtin(const char *name, jl_value_t *v)
{
    jl_set_const(jl_core_module, jl_symbol(name), v);
}

static void add_builtin_func(const char *name, jl_fptr_t f)
{
    add_builtin(name, (jl_value_t*)
                jl_new_closure(f, (jl_value_t*)jl_symbol(name), NULL));
}

void jl_init_primitives(void)
{
    add_builtin_func("is", jl_f_is);
    add_builtin_func("typeof", jl_f_typeof);
    add_builtin_func("subtype", jl_f_subtype);
    add_builtin_func("isa", jl_f_isa);
    add_builtin_func("typeassert", jl_f_typeassert);
    add_builtin_func("apply", jl_f_apply);
    add_builtin_func("throw", jl_f_throw);
    add_builtin_func("tuple", jl_f_tuple);
    add_builtin_func("Union", jl_f_union);
    add_builtin_func("method_exists", jl_f_methodexists);
    add_builtin_func("applicable", jl_f_applicable);
    add_builtin_func("invoke", jl_f_invoke);
    add_builtin_func("eval", jl_f_top_eval);
    add_builtin_func("isbound", jl_f_isbound);
    add_builtin_func("yieldto", jl_f_yieldto);
    
    // functions for internal use
    add_builtin_func("convert_default", jl_f_convert_default);
    add_builtin_func("convert_tuple", jl_f_convert_tuple);
    add_builtin_func("tupleref",  jl_f_tupleref);
    add_builtin_func("tuplelen",  jl_f_tuplelen);
    add_builtin_func("getfield",  jl_f_get_field);
    add_builtin_func("_setfield",  jl_f_set_field);
    add_builtin_func("fieldtype", jl_f_field_type);

    add_builtin_func("arraylen", jl_f_arraylen);
    add_builtin_func("arrayref", jl_f_arrayref);
    add_builtin_func("arrayset", jl_f_arrayset);
    add_builtin_func("arraysize", jl_f_arraysize);

    add_builtin_func("apply_type", jl_f_instantiate_type);
    add_builtin_func("typevar", jl_f_typevar);
    add_builtin_func("new_type_constructor", jl_f_new_type_constructor);

    // builtin types
    add_builtin("Any", (jl_value_t*)jl_any_type);
    add_builtin("None", (jl_value_t*)jl_bottom_type);
    add_builtin("Void", (jl_value_t*)jl_bottom_type);
    add_builtin("Top",  (jl_value_t*)jl_top_type);
    add_builtin("TypeVar", (jl_value_t*)jl_tvar_type);
    add_builtin("TypeName", (jl_value_t*)jl_typename_type);
    add_builtin("TypeConstructor", (jl_value_t*)jl_typector_type);
    add_builtin("Tuple", (jl_value_t*)jl_tuple_type);
    add_builtin("NTuple", (jl_value_t*)jl_ntuple_type);
    add_builtin("Type", (jl_value_t*)jl_type_type);
    add_builtin("...", (jl_value_t*)jl_seq_type);
    add_builtin("BitsKind", (jl_value_t*)jl_bits_kind);
    add_builtin("CompositeKind", (jl_value_t*)jl_struct_kind);
    add_builtin("AbstractKind", (jl_value_t*)jl_tag_kind);
    add_builtin("UnionKind", (jl_value_t*)jl_union_kind);
    // todo: this should only be visible to compiler components
    add_builtin("Undef", (jl_value_t*)jl_undef_type);

    add_builtin("Module", (jl_value_t*)jl_module_type);
    add_builtin("Method", (jl_value_t*)jl_method_type);
    add_builtin("MethodTable", (jl_value_t*)jl_methtable_type);
    add_builtin("Symbol", (jl_value_t*)jl_sym_type);
    add_builtin("IntrinsicFunction", (jl_value_t*)jl_intrinsic_type);
    add_builtin("Function", (jl_value_t*)jl_function_type);
    add_builtin("LambdaStaticData", (jl_value_t*)jl_lambda_info_type);
    add_builtin("Ptr", (jl_value_t*)jl_pointer_type);
    add_builtin("Box", (jl_value_t*)jl_box_type);
    add_builtin("Task", (jl_value_t*)jl_task_type);

    add_builtin("AbstractArray", (jl_value_t*)jl_abstractarray_type);
    add_builtin("Array", (jl_value_t*)jl_array_type);

    add_builtin("Expr", (jl_value_t*)jl_expr_type);
    add_builtin("LineNumberNode", (jl_value_t*)jl_linenumbernode_type);
    add_builtin("LabelNode", (jl_value_t*)jl_labelnode_type);
    add_builtin("GotoNode", (jl_value_t*)jl_gotonode_type);
    add_builtin("QuoteNode", (jl_value_t*)jl_quotenode_type);
    add_builtin("TopNode", (jl_value_t*)jl_topnode_type);

#ifdef __LP64__
    add_builtin("Int", (jl_value_t*)jl_int64_type);
#else
    add_builtin("Int", (jl_value_t*)jl_int32_type);
#endif

    add_builtin("ANY", jl_ANY_flag);
}
