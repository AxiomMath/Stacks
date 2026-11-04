module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Basic

/-!
# From a sheaf of graded algebras on a scheme to the input of relative Proj

A sheaf of `ℤ`-graded algebras over the sheaf of rings of a scheme `S` is
`SheafOfModules.GradedAlgebra S.ringCatSheaf`: a family of sheaves of modules indexed by `ℤ`, an
`𝒪_S`-bilinear multiplication raising degrees additively, a global degree-`0` unit,
associativity and unitality. The input the relative Proj construction of this repository
consumes is `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra S`, which is the
same data written over `S.Opens` rather than over `(Opens S)ᵒᵖ`, together with three further
requirements: commutativity, vanishing in negative degrees, and quasi-coherence of every piece.

This file converts the first into the second. The data is carried across unchanged — the
multiplication of the result at an open `U` *is* the given multiplication at `op U` — and the
three extra requirements are the hypotheses.

## Main definitions

* `Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.IsCommutative`: commutativity of the
  multiplication of a sheaf of graded algebras, as a heterogeneous equality.
* `Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.VanishesInNegativeDegrees`: every local
  section of a negative-degree piece is zero.
* `Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra`: **the conversion.**

## Main results

* `Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.isZero_piece_of_neg`: a piece all of whose
  local sections vanish is a zero object of `S.Modules`.
* `toSheafGradedAlgebra_piece`, `toSheafGradedAlgebra_mul_app` and
  `toSheafGradedAlgebra_one`: the three equations pinning the conversion down. Each is `rfl`, so
  a statement about the converted algebra is a statement about the given one.

## Implementation notes

**Why the vanishing hypothesis is about sections and not about `IsZero`.** The field of
`SheafGradedAlgebra` asks for `CategoryTheory.Limits.IsZero (piece n)` in the category
`AlgebraicGeometry.Scheme.Modules S`, which is a `def` carrying its *own* `Category` instance
with its own `Hom`. A hypothesis phrased as `IsZero` in `SheafOfModules S.ringCatSheaf` is then
a proposition about a different instance, and transporting it means producing the comparison by
hand. Stating the hypothesis sectionwise avoids that: `isZero_piece_of_neg` builds the `IsZero`
of `S.Modules` directly from `CategoryTheory.Limits.IsZero.iff_id_eq_zero` and
`AlgebraicGeometry.Scheme.Modules.hom_ext`, which are the API of that category.

**The two spellings of a section.** `Γ(M, U)` is `(Scheme.Modules.presheaf M).obj (op U)`, an
object of `Ab`, while the graded-algebra structure speaks of `M.val.obj (op U)`, an object of
`ModuleCat Γ(S, U)`. These are *different objects of different categories* with the same carrier
type and the same additive structure, so the additive maps of the one are the additive maps of
the other and every field below is the given field at `op U` with no coercion written. The same
holds for the restriction maps, `Scheme.Modules.presheaf M |>.map f` against `M.val.map f`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)

## Not done here

No tag is claimed. The sheaf-level graded algebra data of Tag 01NN is already carried by
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, and the graded algebras of
Tag 0FQW by `SheafOfModules.GradedAlgebra`; this file asserts nothing that either does not.

Nothing is proved about morphisms *here*. `SheafGradedAlgebra` had none when this file was
written; it has them now, and
`Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebraHom` of
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.HomBridge` carries a
`SheafOfModules.GradedAlgebra.UnitalHom` across this bridge, with the same three fields read at
`op U`. The non-unital `SheafOfModules.GradedAlgebra.Hom` is still not carried across: every
consumer of `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom` needs the unit
law, which that structure lacks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

universe u

variable {S : Scheme.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)

/-- **Commutativity of a sheaf of graded algebras.** The two sides live in the pieces of the
degrees `i + j` and `j + i`, which agree only propositionally, so the equality is
heterogeneous. -/
public def IsCommutative : Prop :=
  ∀ (i j : ℤ) (U : (S.Opens)ᵒᵖ) (a : (A.piece i).val.obj U) (b : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U a b) ((A.mul j i).app U b a)

/-- **Concentration in nonnegative degrees**, stated on local sections. -/
public def VanishesInNegativeDegrees : Prop :=
  ∀ (n : ℤ), n < 0 → ∀ (U : (S.Opens)ᵒᵖ) (x : (A.piece n).val.obj U), x = 0

/-- A sheaf of modules all of whose local sections vanish is a zero object. -/
public theorem isZero_of_forall_eq_zero (M : S.Modules)
    (h : ∀ (U : S.Opens) (x : Γ(M, U)), x = 0) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact (h U x).trans (by rfl)

/-- A negative-degree piece of an algebra concentrated in nonnegative degrees is a zero object
of `S.Modules`. -/
public theorem isZero_piece_of_neg (hneg : VanishesInNegativeDegrees A) (n : ℤ) (hn : n < 0) :
    IsZero (A.piece n : S.Modules) :=
  isZero_of_forall_eq_zero _ fun U x => hneg n hn (op U) x

/-- **The conversion.** A commutative sheaf of graded algebras on a scheme, concentrated in
nonnegative degrees and with quasi-coherent homogeneous pieces, is sheaf-level graded algebra
data in the sense of Situation 01NN. -/
public def toSheafGradedAlgebra (hcomm : IsCommutative A)
    (hneg : VanishesInNegativeDegrees A)
    (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent) :
    SheafGradedAlgebra S where
  piece n := A.piece n
  mul i j :=
    { app U := (A.mul i j).app (op U)
      map_smul_left U r x y := (A.mul i j).map_smul_left (op U) r x y
      map_smul_right U r x y := (A.mul i j).map_smul_right (op U) r x y
      naturality h x y := (A.mul i j).naturality (homOfLE h).op x y }
  one U := A.one.eval (op U)
  one_res h := PresheafOfModules.sections_property A.one (homOfLE h).op
  mul_assoc i j k U a b c := A.mul_assoc i j k (op U) a b c
  one_mul i U a := A.one_mul i (op U) a
  mul_one i U a := A.mul_one i (op U) a
  mul_comm i j U a b := hcomm i j (op U) a b
  negative_isZero n hn := isZero_piece_of_neg A hneg n hn
  isQuasicoherent n := hqc n

variable (hcomm : IsCommutative A) (hneg : VanishesInNegativeDegrees A)
  (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent)

/-- The pieces are carried across unchanged. -/
public theorem toSheafGradedAlgebra_piece (n : ℤ) :
    (toSheafGradedAlgebra A hcomm hneg hqc).piece n = A.piece n := rfl

/-- The multiplication is carried across unchanged. -/
public theorem toSheafGradedAlgebra_mul_app (i j : ℤ) (U : S.Opens) :
    ((toSheafGradedAlgebra A hcomm hneg hqc).mul i j).app U = (A.mul i j).app (op U) := rfl

/-- The unit is carried across unchanged. -/
public theorem toSheafGradedAlgebra_one (U : S.Opens) :
    (toSheafGradedAlgebra A hcomm hneg hqc).one U = A.one.eval (op U) := rfl

end Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

end
