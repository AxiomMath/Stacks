module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Sheaf-level graded algebras over a scheme

A quasi-coherent graded `𝒪_S`-algebra, in the sheaf-theoretic form of Situation 01NN: an
integer-indexed family of quasi-coherent `𝒪_S`-modules, an `𝒪_S`-bilinear multiplication
raising degrees additively, a global unit in degree `0`, associativity, commutativity and
unitality, and vanishing in negative degrees.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafBilinearMap`: an `𝒪_S`-bilinear map of
  `𝒪_S`-modules, recorded on the sections over each open together with its naturality.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`: the input of the bridge.

## Implementation notes

The homogeneous pieces are objects of `AlgebraicGeometry.Scheme.Modules`, i.e. sheaves of
modules over `S.ringCatSheaf` on the site of opens of `S`; this is the shape in which Mathlib
states quasi-coherence (`SheafOfModules.IsQuasicoherent`) and the shape in which this repository
states the localization property of the sections of a quasi-coherent module
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`). Sections are
written with the `Γ(M, U)` notation of `AlgebraicGeometry.Scheme.Modules.presheaf`, indexed by
an open of `S` rather than by an object of `(Opens S)ᵒᵖ`, and restriction is indexed by an
inclusion `U ≤ V` of opens rather than by a morphism of the opposite category.

The unit is recorded as a restriction-compatible family of local sections, `one` together with
`one_res`. That is exactly the unfolding of `PresheafOfModules.sections`, and it avoids naming
the `val` projection of a sheaf of modules through the type synonym
`AlgebraicGeometry.Scheme.Modules`, which is a `def` with its own category instance and so is
not transparent to instance search.

Associativity, unitality and commutativity are heterogeneous equalities: their two sides live in
the pieces of degrees that agree only propositionally, `(i + j) + k` against `i + (j + k)`,
`0 + i` against `i`, and `i + j` against `j + i`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)

## Not done here

Nothing is proved in this file; it fixes the input vocabulary of the bridge. Morphisms of
sheaf-level graded algebras, which Tag 0FQW also defines, are not needed by Situation 01NN and
are not introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

variable {S : Scheme.{u}}

/-- An `𝒪_S`-bilinear map of `𝒪_S`-modules, recorded on the sections over each open of `S`.
The last field is naturality: the map commutes with the restriction maps of the three modules.
-/
public structure SheafBilinearMap (M N P : S.Modules) where
  /-- The bilinear map on sections over an open. -/
  app (U : S.Opens) : Γ(M, U) →+ Γ(N, U) →+ Γ(P, U)
  /-- Linearity in the first variable. -/
  map_smul_left (U : S.Opens) (r : Γ(S, U)) (x : Γ(M, U)) (y : Γ(N, U)) :
    app U (r • x) y = r • app U x y
  /-- Linearity in the second variable. -/
  map_smul_right (U : S.Opens) (r : Γ(S, U)) (x : Γ(M, U)) (y : Γ(N, U)) :
    app U x (r • y) = r • app U x y
  /-- The bilinear map commutes with restriction. -/
  naturality {U V : S.Opens} (h : U ≤ V) (x : Γ(M, V)) (y : Γ(N, V)) :
    P.presheaf.map (homOfLE h).op (app V x y) =
      app U (M.presheaf.map (homOfLE h).op x) (N.presheaf.map (homOfLE h).op y)

/-- A commutative, nonnegatively graded, quasi-coherent graded `𝒪_S`-algebra, given as a family
of sheaves of modules with an `𝒪_S`-bilinear multiplication and a global unit.

This is the sheaf-level data of Situation 01NN. -/
@[stacks 01NN "the situation datum, on the sheaf-level bilinear-multiplication substrate"]
public structure SheafGradedAlgebra (S : Scheme.{u}) where
  /-- The homogeneous piece in each degree. -/
  piece : ℤ → S.Modules
  /-- Multiplication of homogeneous local sections. -/
  mul (i j : ℤ) : SheafBilinearMap (piece i) (piece j) (piece (i + j))
  /-- The unit, as a restriction-compatible family of local sections of degree `0`. -/
  one (U : S.Opens) : Γ(piece 0, U)
  /-- The unit is compatible with restriction. -/
  one_res {U V : S.Opens} (h : U ≤ V) :
    (piece 0).presheaf.map (homOfLE h).op (one V) = one U
  /-- Multiplication is associative. -/
  mul_assoc (i j k : ℤ) (U : S.Opens) (a : Γ(piece i, U)) (b : Γ(piece j, U))
      (c : Γ(piece k, U)) :
    HEq ((mul (i + j) k).app U ((mul i j).app U a b) c)
      ((mul i (j + k)).app U a ((mul j k).app U b c))
  /-- The unit is a left identity. -/
  one_mul (i : ℤ) (U : S.Opens) (a : Γ(piece i, U)) :
    HEq ((mul 0 i).app U (one U) a) a
  /-- The unit is a right identity. -/
  mul_one (i : ℤ) (U : S.Opens) (a : Γ(piece i, U)) :
    HEq ((mul i 0).app U a (one U)) a
  /-- Multiplication is commutative. -/
  mul_comm (i j : ℤ) (U : S.Opens) (a : Γ(piece i, U)) (b : Γ(piece j, U)) :
    HEq ((mul i j).app U a b) ((mul j i).app U b a)
  /-- Negative homogeneous pieces vanish. -/
  negative_isZero (n : ℤ) (hn : n < 0) : IsZero (piece n)
  /-- Every homogeneous piece is quasi-coherent. -/
  isQuasicoherent (n : ℤ) : (piece n).IsQuasicoherent

namespace SheafGradedAlgebra

attribute [instance] isQuasicoherent

end SheafGradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
