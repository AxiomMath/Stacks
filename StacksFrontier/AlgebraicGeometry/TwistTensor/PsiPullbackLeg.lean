module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaNonnegativeDegrees

/-!
# The second leg of Lemma 01O1's triangle, built from the homogeneous-section map of Tag 01NR

The characterising triangle of [Stacks, Tag 01O1] has two legs out of `f^*𝒜_{nd}`: the comparison
`θ` into `⨁_n ℒ^{⊗ n}` precomposed with the tag's own source `r^*(⨁_n 𝒪(nd))`, and the
quadruple's own `ψ`. The first of these needs a degreewise family

`v_n : f^*𝒜_{nd} ⟶ r^*𝒪(nd)`,

and the tag's `v` is the homogeneous-section map of [Stacks, Tag 01NR] — the field
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ` — pulled back along `r`. That field is
stated in the **direct-image** form

`ψ_n : 𝒜_n ⟶ (π_*𝒪(n))`, `π : Proj_S(𝒜) ⟶ S` the structure morphism,

so getting `v` out of it is a transposition followed by a base change, and this file does both.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTransposeNat`: **the adjoint transpose
  `π^*𝒜_n ⟶ 𝒪(n)` of the homogeneous-section map**, in a natural degree.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTranspose`: the same in every integer
  degree, the negative degrees filled in by the unique morphism out of a zero module.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiLeg`: **the transpose based-changed
  along a morphism `r : T ⟶ Proj_S(𝒜)` over `S`**, a family `f^*𝒜_m ⟶ r^*𝒪(m)`.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiLegVeronese`: `psiLeg` read in the
  `d`-divisible grading, which is **the second leg of Lemma 01O1's triangle**: a degreewise family
  `f^*𝒜_{nd} ⟶ (r^*(⨁_n 𝒪(nd)))_n`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.homEquiv_psiTransposeNat`: **the
  transpose is a transpose of `ψ` and of nothing else** — its image under the hom-set bijection of
  the adjunction `π^* ⊣ π_*` is the field `ψ` itself.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTransposeNat_eq`: the transpose
  written out as `π^*ψ_n` followed by the counit, the form a computation unfolds it to.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psi_eq_unit_comp` and
  `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psi_val_app`: **`ψ` recovered from the
  transpose**, as morphisms and on sections. The section form is what meets the chart description
  `TwistData.ψ_chart` and the multiplicativity `TwistData.ψ_mul`, both of which are statements
  about values of `ψ` on sections.

## Implementation notes

`psiTranspose` is defined by a pattern match on `Int`, not by a `dite` on `0 ≤ m` together with
`Int.toNat`. The point is that in the nonnegative branch the degree is literally `((n : ℕ) : ℤ)`,
which is the degree `ψ` is indexed by, so the branch needs no `eqToHom` on either side and
`psiTranspose_natCast` is `rfl`. The `Int.toNat` spelling forces a cast on the source and another
on the target, and then every consumer carries them.

The source of `psiTransposeNat` is spelled with `Stacks.RingedSpace.pullbackFunctor` of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom` rather than with Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback`, even though the transpose is taken for Mathlib's
adjunction. The two realizations of the inverse image are equal by `rfl`, and this is the
realization the homogeneous pieces of
`Stacks.AlgebraicGeometry.RelativeVeroneseTwists.pullbackTwistVeronese` are stated in, so
`psiLegVeronese` is `psiLeg` with no conversion at all.

The negative degrees carry no choice: the homogeneous pieces of a graded algebra of Situation
01NN vanish below degree zero (the field `negative_isZero`), the inverse image of a zero module is
zero, and a morphism out of a zero module is unique. So `psiTranspose` in a negative degree is
the only morphism available, and `v` is determined by `ψ` in every degree.

## What is NOT proved here

**Multiplicativity.** `psiLeg` is a degreewise family of morphisms of sheaves of modules and
nothing *in this file* says it is compatible with the multiplications.

For `psiTranspose` — the leg before its base change along `r` — this is no longer owed: the
sibling module `StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegMultiplicative` proves it, as
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTranspose_map_mul` on sections and
`TwistData.psiTranspose_mulSheaf` on the morphism-level multiplications, and assembles the leg into
a homomorphism of sheaves of graded algebras `TwistData.psiTransposeHom`. It does so by extending
`ψ` by zero to an integer-indexed family `TwistData.psiDirect`, matching the `ℕ`-indexed `HEq`
field `TwistData.ψ_mul` to a per-bidegree equation, and transposing with
`SheafOfModules.GradedAlgebra.transportHomBackward`.

The same for `psiLegVeronese` — that the leg remains multiplicative after base change along `r`
and after re-reading in the `d`-divisible grading — is not done here either, but it is no longer
owed: `StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegVeroneseMultiplicative` transports the
multiplicativity across both steps, as `TwistData.psiLegVeronese_mulSheaf`, and assembles the
homomorphism of graded algebras `TwistData.psiLegVeroneseHom` into
`Stacks.AlgebraicGeometry.RelativeVeroneseTwists.pullbackTwistVeronese`.

**The triangle.** Nothing here relates `psiLegVeronese` to a quadruple's own `ψ`, which is what
the commutativity of Lemma 01O1's triangle asserts. This file supplies the leg and not the
commutativity.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

namespace TwistData

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A)

/-! ### The adjoint transpose of the homogeneous-section map -/

/-- **The adjoint transpose `π^*𝒜_n ⟶ 𝒪(n)` of the homogeneous-section map of [Stacks, Tag
01NR]**, for `π : Proj_S(𝒜) ⟶ S` the structure morphism and `n` a natural degree.

The field `TwistData.ψ` is a morphism `𝒜_n ⟶ π_*𝒪(n)`; this is its image under the hom-set
bijection of the adjunction `π^* ⊣ π_*` of [Stacks, Tag 0096], in Mathlib as
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`. -/
def psiTransposeNat (n : ℕ) :
    (pullbackFunctor (ringedSpaceHom (relativeProj A).toBase)).obj (A.piece (n : ℤ)) ⟶
      D.algebra.piece (n : ℤ) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _ _).symm
    (D.ψ n)

/-- **The transpose is a transpose of `ψ`, and of nothing else**: its image under the hom-set
bijection of the adjunction `π^* ⊣ π_*` is the field `TwistData.ψ` itself. -/
theorem homEquiv_psiTransposeNat (n : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _ _
        (D.psiTransposeNat n) = D.ψ n :=
  Equiv.apply_symm_apply _ _

/-- **The transpose written out**: the inverse image of `ψ_n` followed by the counit of the
adjunction `π^* ⊣ π_*`. This is the form a computation with `psiTransposeNat` unfolds to. -/
theorem psiTransposeNat_eq (n : ℕ) :
    D.psiTransposeNat n =
      (Scheme.Modules.pullback (relativeProj A).toBase).map (D.ψ n) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).counit.app
          (D.algebra.piece (n : ℤ)) :=
  Adjunction.homEquiv_counit _ _ _ _

/-- **`ψ` is recovered from its transpose**: the unit of the adjunction `π^* ⊣ π_*` followed by
the direct image of the transpose. Together with `homEquiv_psiTransposeNat` this says the two
determine each other, in both directions. -/
theorem psi_eq_unit_comp (n : ℕ) :
    D.ψ n =
      (Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).unit.app
          (A.piece (n : ℤ)) ≫
        (Scheme.Modules.pushforward (relativeProj A).toBase).map (D.psiTransposeNat n) := by
  rw [← D.homEquiv_psiTransposeNat n]
  exact Adjunction.homEquiv_unit _ _ _ _

/-- **`ψ` on sections, through the transpose.** A section of `𝒜_n` over an open `U` of the base
is carried by `ψ_n` to the value of the transpose on the preimage of `U`, at the image of the
section under the unit.

This is the form that meets the chart description of `ψ`: the field `TwistData.ψ_chart` and the
field `TwistData.ψ_mul` are both statements about the values of `ψ` on sections, and the direct
image of a morphism acts on sections over `U` as the morphism itself over `π⁻¹U`
(`AlgebraicGeometry.Scheme.Modules.pushforward_map_app`), so no transport appears on the right. -/
theorem psi_val_app (n : ℕ) (U : S.Opens) (a : Γ(A.piece (n : ℤ), U)) :
    (D.ψ n).val.app (Opposite.op U) a =
      (D.psiTransposeNat n).val.app
        (Opposite.op ((relativeProj A).toBase ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).unit.app
          (A.piece (n : ℤ))).val.app (Opposite.op U) a) := by
  rw [psi_eq_unit_comp D n]
  rfl

/-- **The adjoint transpose of the homogeneous-section map in every integer degree.** In a
nonnegative degree this is `psiTransposeNat`; in a negative degree the homogeneous piece `𝒜_m`
vanishes, hence so does its inverse image, and this is the unique morphism out of it. -/
def psiTranspose : ∀ m : ℤ,
    (pullbackFunctor (ringedSpaceHom (relativeProj A).toBase)).obj (A.piece m) ⟶
      D.algebra.piece m
  | (n : ℕ) => D.psiTransposeNat n
  | .negSucc n =>
      (ProjRepresentsF1.isZero_pullback_obj (relativeProj A).toBase
        (A.negative_isZero _ (Int.negSucc_lt_zero n))).to_ _

/-- In a nonnegative degree `psiTranspose` is the transpose of `ψ` in that degree, on the nose. -/
@[simp] theorem psiTranspose_natCast (n : ℕ) :
    D.psiTranspose (n : ℤ) = D.psiTransposeNat n := rfl

/-- In a negative degree `psiTranspose` is the unique morphism out of a zero module, so it agrees
with every other morphism there. -/
theorem psiTranspose_eq_of_neg {m : ℤ} (hm : m < 0)
    (w : (pullbackFunctor (ringedSpaceHom (relativeProj A).toBase)).obj (A.piece m) ⟶
      D.algebra.piece m) :
    D.psiTranspose m = w :=
  (ProjRepresentsF1.isZero_pullback_obj (relativeProj A).toBase
    (A.negative_isZero m hm)).eq_of_src _ _

/-! ### The second leg of Lemma 01O1's triangle -/

variable {T : Scheme.{u}} {f : T ⟶ S} (r : T ⟶ (relativeProj A).scheme)

/-- **The transpose of the homogeneous-section map, base-changed along a morphism over `S`.** For
`r : T ⟶ Proj_S(𝒜)` with `r ≫ π = f`, the inverse image along `r` of `psiTranspose` is a morphism
`r^*π^*𝒜_m ⟶ r^*𝒪(m)`, and `r^*π^* = (r ≫ π)^* = f^*`; so this is a degreewise family

`f^*𝒜_m ⟶ r^*𝒪(m)`.

The two identifications are Mathlib's `AlgebraicGeometry.Scheme.Modules.pullbackCongr` and
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
def psiLeg (hr : r ≫ (relativeProj A).toBase = f) (m : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (A.piece m) ⟶
      (pullbackFunctor (ringedSpaceHom r)).obj (D.algebra.piece m) :=
  (Scheme.Modules.pullbackCongr hr).inv.app (A.piece m) ≫
    (Scheme.Modules.pullbackComp r (relativeProj A).toBase).inv.app (A.piece m) ≫
      (Scheme.Modules.pullback r).map (D.psiTranspose m)

/-- **The second leg of Lemma 01O1's triangle**: `psiLeg` read in the `d`-divisible grading, a
degreewise family

`v_n : f^*𝒜_{nd} ⟶ (r^*(⨁_n 𝒪(nd)))_n`

for the graded algebra of Situation 01NN and the tag's own source. Both vocabulary crossings are
`rfl` — the degree-`n` piece of
`Stacks.AlgebraicGeometry.RelativeVeroneseTwists.pullbackTwistVeronese` is the inverse image of
`𝒪(nd)` by `pullbackTwistVeronese_piece`, and the homogeneous pieces of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra` are those of `𝒜` — so this is
`psiLeg` itself in the degree `n * d`. -/
def psiLegVeronese (hr : r ≫ (relativeProj A).toBase = f) (d : ℤ) (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece (n * d)) ⟶
      (RelativeVeroneseTwists.pullbackTwistVeronese D d r).piece n :=
  D.psiLeg r hr (n * d)

/-- The second leg in the `d`-divisible grading is `psiLeg` in the degree `n * d`, on the nose. -/
theorem psiLegVeronese_eq (hr : r ≫ (relativeProj A).toBase = f) (d : ℤ) (n : ℤ) :
    D.psiLegVeronese r hr d n = D.psiLeg r hr (n * d) := rfl

end TwistData

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
