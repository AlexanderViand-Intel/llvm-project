//===- PolynomialTypes.td - Polynomial types ---------------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef POLYNOMIAL_TYPES
#define POLYNOMIAL_TYPES

include "mlir/Dialect/Polynomial/IR/PolynomialAttributes.td"
include "mlir/Dialect/Polynomial/IR/PolynomialDialect.td"

class Polynomial_Type<string name, string typeMnemonic>
    : TypeDef<Polynomial_Dialect, name> {
  let mnemonic = typeMnemonic;
}

def Polynomial_PolynomialType : Polynomial_Type<"Polynomial", "polynomial"> {
  let summary = "An element of a polynomial ring.";
  let description = [{
    A type for polynomials in a polynomial quotient ring.
  }];
  let parameters = (ins Polynomial_RingAttr:$ring);
  let assemblyFormat = "`<` struct(params) `>`";
}

def Polynomial_RNSType : Polynomial_Type<"RNS", "rns"> {
  let summary = "A residue number system representation of a polynomial";
  let description = [{
  }];

  let parameters = (ins ArrayRefParameter<"mlir::Type">:$basisTypes);
  let assemblyFormat = "`<` $basisTypes `>`";
  //TODO: Add verifiers
}

def PolynomialLike: TypesOrContainer<[Polynomial_PolynomialType,Polynomial_RNSType], "polynomial-like">;


#endif // POLYNOMIAL_TYPES
