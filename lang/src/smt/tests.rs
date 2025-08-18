use super::*;
use crate::{parse_str_cbpv, Sig};
use easy_smt::Response;

fn sig1() -> CheckedSig {
    let mut sig = CheckedSig::empty();
    sig.add_alias("B2", VType::tuple([VType::prop(), VType::prop()]));
    let t_u32 = sig.add_sort("u32");
    sig.add_alias("N2", VType::tuple([t_u32.clone(), t_u32.clone()]));

    sig.add_constant("zero", "u32");
    sig.add_relation("lt", ["u32", "u32"]);
    sig.add_relation("le", ["u32", "u32"]);

    sig.add_axiom("forall( |x:u32,y:u32| lt(x,y) == (le(x,y) && x != y))");
    sig.add_axiom("forall( |x:u32| le(zero,x))");
    sig.add_axiom("forall( |x:u32| !le(x,zero) || x == zero)");

    sig.add_op_fun("inc", "
|x_in:u32| |x_out:u32| lt(x_in,x_out)
");

    sig.add_op_fun("dec", "
|x_in:u32| |x_out:u32|
lt(x_out,x_in)
|| (x_in == x_out && x_in == zero)
");

    sig.add_sort("Set_u32");
    sig.add_constant("emptySet_u32", "Set_u32");
    sig.add_relation("member", ["u32", "Set_u32"]);

    sig.add_axiom("forall(|e:u32| !member(e,emptySet_u32))");

    sig.add_op_fun("insert", "
|e:u32,s1:Set_u32|
|s2:Set_u32|
forall(|e2:u32|
member(e2,s2) == (member(e2,s1) || e == e2))
");

    sig.add_op_fun("filter", "
|f:fn(u32) -> bool,s1:Set_u32|
|s2:Set_u32|
forall(|e:u32|
(!member(e,s2) || (member(e,s1) && f(e)))
&& (member(e,s2) || !(member(e,s1) && f(e))))
");

    sig.add_op_pred("all_pass", "
|f:fn(u32) -> bool,s1:Set_u32|
forall(|e:u32|
!member(e,s1) || f(e))
");

    sig.add_op_pred("test_pred1", "
|x:u32|
x == x
");

    sig.add_op_pred("test_pred2", "
|x:u32|
x != x
");

    sig.add_axiom("
forall(|s1:Set_u32, s2:Set_u32|
s1 == s2
|| exists(|e:u32| member(e,s1) != member(e,s2)))
");

    sig
}


pub fn sig_tuple_input() -> CheckedSig {
    let mut sig = sig1();

    sig.add_relation_t(
        "member_tuple",
        [VType::tuple([VType::ui("u32"), VType::ui("Set_u32")])]
    );

    sig.add_axiom("
forall(|e:u32, s:Set_u32|
member(e,s) == member_tuple((e,s)))
");


    sig.add_op_pred("all_pass_tuple", "
|tup:(fn(u32) -> bool,Set_u32)| {
    let (f,s1) = tup;
    forall(|e:u32| !member(e,s1) || f(e))
}
");

    sig.add_op_fun("filter_tuple", "
|tup:(fn(u32) -> bool,Set_u32)|
|s2:Set_u32|
{
    let (f,s1) = tup;

    forall(|e:u32|
    (!member(e,s2) || (member(e,s1) && f(e)))
    && (member(e,s2) || !(member(e,s1) && f(e))))
}
");

    sig.add_op_fun("dup", "
|x:u32|
|out:(u32,u32)|
{
    let (y,z) = out;
    x == y && x == z
}
");

    sig
}

pub fn assert_valid<T: ToString>(s: T) {
    assert_eq!(query_negative(s, &sig1()), Response::Unsat);
}
pub fn assert_invalid<T: ToString>(s: T) {
    assert_eq!(query_negative(s, &sig1()), Response::Sat);
}


pub fn assert_sat<T: ToString>(s: T) {
    assert_eq!(query(s, &sig1()), Response::Sat);
}

pub fn assert_unsat<T: ToString>(s: T) {
    assert_eq!(query(s, &sig1()), Response::Unsat);
}

pub fn query<T: ToString>(s: T, sig: &CheckedSig) -> Response {
    let c = parse_str_cbpv(&s.to_string()).unwrap();
    c.type_check_prop(sig.inner_sig());
    internal::check_sat_simple(&c, sig.inner_sig()).unwrap()
}

    #[test]
    fn smt_eq() {
        let c = parse_str_cbpv("true == false").unwrap();
        assert_eq!(
            internal::check_sat_simple(&c, &Sig::empty()).unwrap(),
            Response::Unsat,
        );
    }
    #[test]
    fn smt_neq() {
        let c = parse_str_cbpv("true != false").unwrap();
        assert_eq!(
            internal::check_sat_simple(&c, &Sig::empty()).unwrap(),
            Response::Sat,
        );
    }
    #[test]
    fn smt_neq2() {
        let c = parse_str_cbpv("true != true").unwrap();
        assert_eq!(
            internal::check_sat_simple(&c, &Sig::empty()).unwrap(),
            Response::Unsat,
        );
    }

    #[test]
    fn smt_forall() {
        let c = parse_str_cbpv("forall(|r:u32| r == r)").unwrap();
        let mut sig = Sig::empty();
        sig.add_sort("u32");
        assert_eq!(
            internal::check_sat_simple(&c, &sig).unwrap(),
            Response::Sat,
        );
    }

    #[test]
    fn smt_forall2() {
        let c = parse_str_cbpv("forall(|r1:u32| forall(|x:u32| r1 == x))").unwrap();
        let mut sig = Sig::empty();
        sig.add_sort("u32");
        assert_eq!(
            internal::check_sat_simple(&c, &sig).unwrap(),
            Response::Sat,
        )
    }

    #[test]
    fn smt_exists2() {
        let c = parse_str_cbpv("exists(|r1:u32| exists(|x:u32| r1 == x))").unwrap();
        let mut sig = Sig::empty();
        sig.add_sort("u32");
        assert_eq!(
            internal::check_sat_simple(&c, &sig).unwrap(),
            Response::Sat,
        )
    }

    #[test]
    fn smt_neq3() {
        let c = parse_str_cbpv("exists(|r:u32| r != r)").unwrap();
        let mut sig = Sig::empty();
        sig.add_sort("u32");
        assert_eq!(
            internal::check_sat_simple(&c, &sig).unwrap(),
            Response::Unsat,
        )
    }

    #[test]
    fn smt_foo_gt() {
        let c = parse_str_cbpv("forall(|r:u32| lt(r,r))").unwrap();
        let mut sig = Sig::empty();
        sig.add_sort("u32");
        sig.add_relation("lt", ["u32", "u32"]);
        assert_eq!(
            internal::check_sat_simple(&c, &sig).unwrap(),
            Response::Sat,
        )
    }

    #[test]
    fn smt_and1() { assert_sat("true && true"); }
    #[test]
    fn smt_and2() { assert_unsat("true && false"); }
    #[test]
    fn smt_and3() { assert_unsat("false && false"); }

    #[test]
    fn smt_and4() { assert_unsat("(forall(|r:u32| r == r)) && false"); }
    #[test]
    fn smt_and5() { assert_unsat("(true && false) && true"); }

    #[test]
    fn smt_or1() { assert_sat("true || true"); }
    #[test]
    fn smt_or2() { assert_sat("true || false"); }
    #[test]
    fn smt_or3() { assert_unsat("false || false"); }

    #[test]
    fn smt_not() { assert_unsat("!true"); }
    #[test]
    fn smt_not2() { assert_sat("!exists(|r:u32| r != r)"); }
    #[test]
    fn smt_not3() { assert_sat("!(exists(|r:u32| r != r))"); }
    #[test]
    fn smt_not4() { assert_sat("!(true && false)"); }

    #[test]
    fn smt_axiom1() { assert_valid("!(forall(|x:u32| lt(x,x))) || !(forall(|x1:u32| forall(|x2:u32| !lt(x1,x2) || !lt(x2,x1) || x1 == x2))) || (forall(|x1:u32| exists(|x2:u32| lt(x1,x2))))"); }
    #[test]
    fn smt_axiom2() { assert_valid("!(forall(|x:u32| lt(x,x))) || (forall(|x1:u32| exists(|x2:u32| lt(x1,x2))))"); }
    #[test]
    fn smt_axiom3() { assert_valid("forall(|x:u32| lt(x,x) || !(forall(|x:u32| lt(x,x))))"); }
    #[test]
    fn smt_axiom4() { assert_valid("(forall(|x:u32| lt(x,x))) || true"); }
    #[test]
    fn smt_axiom5() { assert_unsat("!(!(forall(|x:u32| lt(x,x))) || (forall(|x1:u32| exists(|x2:u32| lt(x1,x2)))))"); }
    #[test]
    fn smt_axiom6() { assert_sat("!(forall(|x:u32| lt(x,x))) || true"); }
    #[test]
    fn smt_axiom7() { assert_unsat("(forall(|x:u32| lt(x,x))) && (exists(|x1:u32| forall(|x2:u32| !lt(x1,x2))))"); }

    #[test]
    fn smt_not_quant() { assert_unsat("forall(|x:u32| lt(x,x))"); }
    #[test]
    fn smt_quant_not1() { assert_sat("forall(|x:u32| !lt(x,x))"); }
    #[test]
    fn smt_quant_not2() { assert_unsat("forall(|x:u32| !(x == x))"); }
    #[test]
    fn smt_3565() { assert_unsat("!forall(|x:u32| x == x)"); }

    #[test]
    fn smt_fun1() { assert_valid("forall(|x:u32| (|y:u32| y == y)(x))"); }
    #[test]
    fn smt_fun2() { assert_valid("forall(|x:u32| (|y:u32| exists(|z:u32| y == z))(x))"); }

    #[test]
    fn smt_block1() { assert_valid("{ true || false }"); }
    #[test]
    fn smt_let1() { assert_valid("{ let x = true; x || false }"); }

    #[test]
    fn smt_let2() { assert_valid("{
let f = |y:u32| exists(|z:u32| y == z);
forall(|x:u32| f(x))
}"); }

    #[test]
    fn smt_op1() { assert_valid("forall(|x:u32| lt(x,inc(x)))") }
    #[test]
    fn smt_op2() { assert_invalid("forall(|x:u32| lt(inc(x),inc(x)))") }
    #[test]
    fn smt_op3() { assert_invalid("forall(|x:u32| lt(inc(x),x))") }

    #[test]
    fn smt_hop1() { assert_valid("
forall(|x:u32|
forall(|s:Set_u32|
  !member(x,filter(|a:u32| a != x, s))))
"); }
    #[test]
    fn smt_hop2() { assert_invalid("
forall(|x:u32|
forall(|y:u32|
forall(|s:Set_u32|
  !member(y,filter(|a:u32| a != x, s)))))
"); }
    #[test]
    fn smt_hop3() { assert_valid("
forall(|x:u32|
forall(|s:Set_u32|
  filter(|a:u32| a != x, s)
  == filter(|a:u32| a != x, s)))
"); }
    #[test]
    fn smt_hop4() { assert_valid("
!(forall(|s1:Set_u32| forall(|s2:Set_u32|
    (s1 == s2) || (exists(|e:u32| member(e,s1) != member(e,s2))))))
||
forall(|x:u32|
forall(|s:Set_u32|
  filter(|a:u32| a != x, s)
  == filter(|a:u32| a != x, s)))
"); }
    #[test]
    fn smt_hop5() { assert_valid("
!(forall(|s1:Set_u32| forall(|s2:Set_u32|
    (s1 == s2) || (exists(|e:u32| member(e,s1) != member(e,s2))))))
||
forall(|x:u32|
forall(|s:Set_u32|
  !all_pass(|a:u32| a != x, s)
  || (filter(|a:u32| a != x, s) == s)))
"); }
    #[test]
    fn smt_hop6() { assert_valid("
forall(|x:u32|
forall(|s:Set_u32|
  all_pass(|a:u32| a != x, filter(|a:u32| a != x, s))))
"); }
    #[test]
    fn smt_hop7() { assert_invalid("
forall(|x:u32|
forall(|s:Set_u32|
  all_pass(|a:u32| a != x, s) || false))
"); }
    #[test]
    fn smt_hop8() { assert_valid("
!(forall(|s1:Set_u32| forall(|s2:Set_u32|
    (s1 == s2) || (exists(|e:u32| member(e,s1) != member(e,s2))))))
||
forall(|x:u32|
forall(|s:Set_u32|
  !(forall(|e:u32| !member(e,s) || e != x))
  || (filter(|a:u32| a != x, s) == s)))
"); }
    #[test]
    fn smt_hop9() { assert_valid("
forall(|x:u32|
forall(|s:Set_u32|
  !(all_pass(|a:u32| a != x, s))
  ||
  (forall(|e:u32| !member(e,s) || e != x))))
"); }
    #[test]
    fn smt_hop10() { assert_valid("
forall(|x:u32|
forall(|s:Set_u32|
  all_pass(|a:u32| a != x, s)
  ||
  (exists(|e:u32| member(e,s) && e == x))))
"); }
    #[test]
    fn smt_hop11() { assert_valid("
forall(|x:u32|
  test_pred1(x) || false)
"); }
    #[test]
    fn smt_hop12() { assert_invalid("
forall(|x:u32|
  test_pred2(x) || false)
"); }

    #[test]
    fn smt_multi_quant1() {assert_invalid("
forall(|x1:u32, x2:u32| x1 == x2)
"); }
    #[test]
    fn smt_multi_quant2() {assert_valid("
exists(|x1:u32, x2:u32| x1 == x2)
"); }

    #[test]
    fn smt_tuple_quant1() { assert_valid("
exists(|xs:(u32,u32)| xs == xs)
"); }
    #[test]
    fn smt_tuple_quant2() { assert_invalid("
exists(|xs:(u32,u32)| xs != xs)
"); }
    #[test]
    fn smt_tuple_quant3() { assert_invalid("
exists(|xs:(u32,u32,u32,u32)| xs != xs)
"); }
    #[test]
    fn smt_tuple_let1() { assert_valid("
exists(|xs:(u32,(u32,u32),u32,u32)| {
    let (x1,x2,x3,_) = xs;
    let (y1,_) = x2;
    y1 == x3
})
"); }
    #[test]
    fn smt_tuple_val1() { assert_invalid("
exists(|x:u32| (x,x) != (x,x))
"); }
    #[test]
    fn smt_tuple_val2() { assert_invalid("
exists(|x:(u32,u32)| (x,x) != (x,x))
"); }
    #[test]
    fn smt_tuple_val3() { assert_valid("
exists(|x:(u32,u32),y:u32| {
    let (x1,x2) = x;
    (x1,y) == (y,x2)
})
"); }

    #[test]
    fn smt_tuple_input1() { assert_valid_with(&sig_tuple_input(), "
forall(|e:u32, s:Set_u32|
!member(e,s) || member_tuple((e,s)))
"); }

    #[test]
    fn smt_tuple_input2() { assert_valid_with(&sig_tuple_input(), "
forall(|e:u32, s:Set_u32|
filter(|x:u32| x != e, s) ==
filter_tuple((|x:u32| x != e, s)))
"); }

    #[test]
    fn smt_tuple_input3() { assert_valid_with(&sig_tuple_input(), "
true
"); }

    #[test]
    fn smt_tuple_output1() { assert_valid_with(&sig_tuple_input(), "
forall(|e:u32|
dup(e) == (e,e))
"); }

    #[test]
    fn smt_ite1() { assert_invalid("
forall(|e:u32|
if lt(e,e) {
    e == e
} else {
    e != e
})
"); }

    #[test]
    fn smt_sort_cycle1() { assert_unknown_with(&sig1(), "
exists(|x:u32|
forall(|s:Set_u32|
member(x,s)))
"); }

    #[test]
    fn smt_const1() { assert_invalid("exists(|x:u32| member(x, emptySet_u32))") }

    #[test]
    fn smt_rec1() {
        let mut sig = sig1();
        sig.add_op_rec(
            "insert_to_zero",
            "
|e:u32| |s:Set_u32|
member(zero,s)
",
            "
|e:u32| {
    let s = if e == zero {
        emptySet_u32
    } else {
        insert_to_zero(dec(e))
    };
    insert(e,s)
}
",
        );
        assert_valid_with(&sig, "
member(zero, insert_to_zero(zero))
");
        assert_valid_with(&sig, "
forall(|e:u32|
member(zero, insert_to_zero(e)))
");
    }

    #[test]
    fn smt_direct_funs1() {
        println!("Starting...");
        CheckedSig::empty().assert_valid("
{
    let test = |x:bool,y:bool| implies(x,y) == (!x || y);
    test(true,true)
    &&
    test(true,false)
    &&
    test(false,true)
    &&
    test(false,false)
}
");
    }

    #[test]
    fn smt_type_alias1() {
        let mut sig = sig1();
        sig.add_relation("alias_test", ["N2", "N2"]);
        sig.add_axiom("
forall(|x:u32, y:u32, z:N2| {
    let (a,_) = z;
    !alias_test((x,y), z)
    || x == a
})
");

        sig.assert_valid("
forall(|x: u32, y: u32|
!alias_test((x,x), (y,y))
|| x == y)
");
    }

    #[test]
    fn smt_two_pred_ops1() {
        let mut sig = CheckedSig::empty();
        sig.add_sort("Planet");
        sig.add_constant("mercury", "Planet");
        sig.add_constant("venus", "Planet");

        sig.add_op_pred("fire", "
|p: Planet|
true");

        sig.add_op_pred("water", "
|p: Planet|
false");

        sig.assert_valid("fire(mercury) || water(venus) || true");
    }

    #[test]
    fn smt_bind_primative() {
        let sig = sig1();
        sig.assert_valid("
forall (|x:u32| {
let f = inc;
x != f(x)
})");
    }
