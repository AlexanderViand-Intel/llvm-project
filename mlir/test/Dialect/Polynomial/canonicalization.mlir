// RUN: mlir-opt -canonicalize %s | FileCheck %s
#ntt_poly = #polynomial.int_polynomial<-1 + x**8>
#ntt_ring = #polynomial.ring<coefficientType=i32, coefficientModulus=256, polynomialModulus=#ntt_poly>
// TODO: Update with actual expected representations
#representation = #polynomial.representation<representation="TEST">
#representation_ntt = #polynomial.representation<representation="TEST">
#root = #polynomial.primitive_root<value=31:i32, degree=8:index>
!poly_ty = !polynomial.polynomial<ring=#ntt_ring, representation=#representation>
!ntt_poly_ty = !polynomial.polynomial<ring=#ntt_ring, representation=#representation_ntt>

// CHECK-LABEL: @test_canonicalize_intt_after_ntt
// CHECK: (%[[P:.*]]: [[T:.*]]) -> [[T]]
func.func @test_canonicalize_intt_after_ntt(%p0 : !poly_ty) -> !poly_ty {
  // CHECK-NOT: polynomial.ntt
  // CHECK-NOT: polynomial.intt
  // CHECK: %[[RESULT:.+]] = polynomial.add %[[P]], %[[P]]  : [[T]]
  %t0 = polynomial.ntt %p0 {root=#root} : !poly_ty -> !ntt_poly_ty
  %p1 = polynomial.intt %t0 {root=#root} : !ntt_poly_ty -> !poly_ty
  %p2 = polynomial.add %p1, %p1 : !poly_ty
  // CHECK: return %[[RESULT]] : [[T]]
  return %p2 : !poly_ty
}

// CHECK-LABEL: @test_canonicalize_ntt_after_intt
// CHECK: (%[[X:.*]]: [[T:.*]]) -> [[T]]
func.func @test_canonicalize_ntt_after_intt(%t0 : !ntt_poly_ty) -> !ntt_poly_ty {
  // CHECK-NOT: polynomial.intt
  // CHECK-NOT: polynomial.ntt
  // CHECK: %[[RESULT:.+]] = polynomial.add %[[X]], %[[X]] : [[T]]
  %p0 = polynomial.intt %t0 {root=#root} : !ntt_poly_ty -> !poly_ty
  %t1 = polynomial.ntt %p0 {root=#root} : !poly_ty -> !ntt_poly_ty
  %t2 = polynomial.add %t1, %t1 : !ntt_poly_ty
  // CHECK: return %[[RESULT]] : [[T]]
  return %t2 : !ntt_poly_ty
}

#cycl_2048 = #polynomial.int_polynomial<1 + x**1024>
#ring = #polynomial.ring<coefficientType=i32, coefficientModulus=256:i32, polynomialModulus=#cycl_2048>
!sub_ty = !polynomial.polynomial<ring=#ring,representation=#representation>

// CHECK-LABEL: test_canonicalize_sub
// CHECK-SAME: (%[[p0:.*]]: [[T:.*]], %[[p1:.*]]: [[T]]) -> [[T]] {
func.func @test_canonicalize_sub(%poly0 : !sub_ty, %poly1 : !sub_ty) -> !sub_ty {
  %0 = polynomial.sub %poly0, %poly1  : !sub_ty
  // CHECK: %[[minus_one:.+]] = polynomial.constant -1 : i32
  // CHECK: %[[p1neg:.+]] = polynomial.mul_scalar %[[p1]], %[[minus_one]]
  // CHECK: [[ADD:%.+]] = polynomial.add %[[p0]], %[[p1neg]]
  return %0 : !sub_ty
}

// CHECK-LABEL: test_canonicalize_fold_add_through_ntt
// CHECK: polynomial.add
// CHECK-NOT: polynomial.ntt
// CHECK-NOT: polynomial.intt
func.func @test_canonicalize_fold_add_through_ntt(
    %poly0 : !poly_ty,
    %poly1 : !poly_ty) -> !poly_ty {
  %0 = polynomial.ntt %poly0 {root=#root} : !poly_ty -> !ntt_poly_ty
  %1 = polynomial.ntt %poly1 {root=#root} : !poly_ty -> !ntt_poly_ty
  %a_plus_b = polynomial.add %0, %1 : !ntt_poly_ty
  %out = polynomial.intt %a_plus_b {root=#root} : !ntt_poly_ty -> !poly_ty
  return %out : !poly_ty
}

// CHECK-LABEL: test_canonicalize_fold_add_through_intt
// CHECK: polynomial.add
// CHECK-NOT: polynomial.intt
// CHECK-NOT: polynomial.iintt
func.func @test_canonicalize_fold_add_through_intt(
    %tensor0 : !ntt_poly_ty,
    %tensor1 : !ntt_poly_ty) -> !ntt_poly_ty {
  %0 = polynomial.intt %tensor0 {root=#root} : !ntt_poly_ty -> !poly_ty
  %1 = polynomial.intt %tensor1 {root=#root} : !ntt_poly_ty -> !poly_ty
  %a_plus_b = polynomial.add %0, %1 : !poly_ty
  %out = polynomial.ntt %a_plus_b {root=#root} : !poly_ty -> !ntt_poly_ty
  return %out : !ntt_poly_ty
}

// CHECK-LABEL: test_canonicalize_fold_sub_through_ntt
// CHECK: polynomial.mul_scalar
// CHECK: polynomial.add
// CHECK-NOT: polynomial.ntt
// CHECK-NOT: polynomial.intt
func.func @test_canonicalize_fold_sub_through_ntt(
    %poly0 : !poly_ty,
    %poly1 : !poly_ty) -> !poly_ty {
  %0 = polynomial.ntt %poly0 {root=#root} : !poly_ty -> !ntt_poly_ty
  %1 = polynomial.ntt %poly1 {root=#root} : !poly_ty -> !ntt_poly_ty
  %a_plus_b = polynomial.sub %0, %1 : !ntt_poly_ty
  %out = polynomial.intt %a_plus_b {root=#root} : !ntt_poly_ty -> !poly_ty
  return %out : !poly_ty
}

// CHECK-LABEL: test_canonicalize_fold_sub_through_intt
// CHECK: polynomial.sub
// CHECK-NOT: polynomial.intt
// CHECK-NOT: polynomial.iintt
func.func @test_canonicalize_fold_sub_through_intt(
    %tensor0 : !ntt_poly_ty,
    %tensor1 : !ntt_poly_ty) -> !ntt_poly_ty {
  %0 = polynomial.intt %tensor0 {root=#root} : !ntt_poly_ty -> !poly_ty
  %1 = polynomial.intt %tensor1 {root=#root} : !ntt_poly_ty -> !poly_ty
  %a_plus_b = polynomial.sub %0, %1 : !poly_ty
  %out = polynomial.ntt %a_plus_b {root=#root} : !poly_ty -> !ntt_poly_ty
  return %out : !ntt_poly_ty
}


// CHECK-LABEL: test_canonicalize_do_not_fold_different_roots
// CHECK: polynomial.add
func.func @test_canonicalize_do_not_fold_different_roots(
    %poly0 : !poly_ty,
    %poly1 : !poly_ty) -> !poly_ty {
  %0 = polynomial.ntt %poly0 {root=#polynomial.primitive_root<value=31:i32, degree=8:index>} : !poly_ty -> !ntt_poly_ty
  %1 = polynomial.ntt %poly1 {root=#polynomial.primitive_root<value=33:i32, degree=8:index>} : !poly_ty -> !ntt_poly_ty
  %a_plus_b = polynomial.add %0, %1 : !ntt_poly_ty
  %out = polynomial.intt %a_plus_b {root=#root} : !ntt_poly_ty -> !poly_ty
  return %out : !poly_ty
}

