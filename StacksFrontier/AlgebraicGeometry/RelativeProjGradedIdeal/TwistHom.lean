module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.NonnegTruncation
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Kernel

/-!
# The homogeneous-section map of a relative Proj as one homomorphism of graded algebras

The twist data of a relative Proj carries its homogeneous-section map as an `ℕ`-indexed *family*
of morphisms of sheaves of modules,
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ n : 𝒜_n ⟶ p_*(𝒪(n))`, with the product
and unit laws stated separately on sections. **This file assembles that family into a single
`ℤ`-indexed homomorphism of sheaf-level graded algebras**
`ψ : 𝒜 ⟶ (p_*(⨁_d 𝒪(d)))_{≥0}`, which is the shape a kernel can be taken of.

Tags 0801 and 0803 need the kernel of such a homomorphism:
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.kernelGradedIdeal` is defined for a
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom` and for nothing weaker, so
while `ψ` is a family of morphisms rather than a homomorphism no graded ideal can be cut out by
it.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwists.twistTarget`: **the target**
  `(p_*(⨁_d 𝒪(d)))_{≥0}`, as sheaf-level graded algebra data on `S` in the sense of
  Situation 01NN.
* `…psiApp`: the degreewise morphism, `ψ_n` in a nonnegative degree and the zero morphism in a
  negative one.
* `…psiHom`: **`ψ` as a `SheafGradedAlgebraHom`.**

## Main results

* `…psiApp_ofNat`: the nonnegative components are the components of `TwistData.ψ`, on the nose.
* `…psiIdeal`, `…psiQuotient` and `…isClosedImmersion_psiAmbientHom`: the graded ideal `ker ψ`,
  the quotient `𝒜/ker ψ` and the closed immersion `Proj_S(𝒜/ker ψ) ⟶ Proj_S(𝒜)` now exist, with
  no hypothesis beyond `hqc` — every clause of `GradedQuotientPresentation` except `iso` is
  supplied by `StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Kernel.lean` once the
  homomorphism does.

## Implementation notes

**The negative components are forced.** `𝒜` is data of Situation 01NN, so `𝒜_n` is a zero object
for `n < 0`; the target is a nonnegative truncation, so its degree-`n` piece is a zero object
too. Both the product and the unit law in a negative degree therefore compare two sections of
zero modules, and the proof is `eq_zero_of_isZero` on each side — not a `HEq`, because the
degree-`i + j` piece of the target is the *same* object on both sides of `app_mul`.

**Why `eq_of_heq` appears in the nonnegative branch.** `TwistData.ψ_mul` states the product law
as a `HEq` carrying a transport along `Int.natCast_add`, because the section ring is graded by `ℕ`
while the pieces are indexed by `ℤ`. The two sides live in the pieces of `(↑p + ↑q : ℤ)` and
`(↑(p + q) : ℤ)`, which are *definitionally* equal — `Nat.cast` into `ℤ` is `Int.ofNat` and
`Int.add` reduces on that constructor — so the transport is the identity and the `HEq` is an
equality of terms of one type. This is the same observation the nonnegative truncation rests on.

**Quasi-coherence of the direct images is a hypothesis here, and is discharged elsewhere.** `p_*`
preserves quasi-coherence for a quasi-compact quasi-separated morphism (Tag 01LC), and the
structure morphism of a relative Proj is separated
(`Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase`); quasi-compactness of it is
the one hypothesis of Tag 0801. That chain is not run in this file, so `hqc` is taken as an
argument — but it **is** run, from quasi-compactness alone, by
`Stacks.AlgebraicGeometry.RelativeProjTwists.isQuasicoherent_pushforward_twist` in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/ClosedTwistAlgebra.lean`, which is what
every consumer of `psiHom` should pass. Nothing about `hqc` is owed.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)

## Not done here

No Stacks tag is claimed.

**This is not itself Tag 0801's homomorphism, but Tag 0801's homomorphism is now built from
it.** Tag 0801 takes the kernel of `𝒜 ⟶ ⨁_{d ≥ 0} p_*((i_*𝒪_Z)(d))` for a closed immersion
`i : Z ⟶ Proj_S(𝒜)`, and the `ψ` built here lands in `⨁_{d ≥ 0} p_*(𝒪(d))` — the twists
themselves, with no `Z` in sight. What separates the two is the graded algebra
`d ↦ (i_*𝒪_Z)(d)` on `Proj_S(𝒜)`, the degreewise quotient of `d ↦ 𝒪(d)` by the graded ideal
generated in degree `0` by the ideal sheaf of `Z`. **That quotient now exists**, as
`Stacks.AlgebraicGeometry.RelativeProjTwists.restrictedTwistAlgebra` in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/ClosedTwistAlgebra.lean`, with its
quotient homomorphism `…restrictionHom`; `psiHom` composed with the truncated direct image of
that homomorphism is `…psiClosedHom`, and `kernelGradedIdeal` of the composite is
`…closedVanishingIdeal`. The one hypothesis those still carry is quasi-coherence of the quotient
pieces, i.e. of `ℐ_Z · 𝒪(d)`; the `Not done here` section of that file records why, and what the
relative `iso` clause of Tag 0801 needs beyond it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.PushforwardGradedAlgebra
open Stacks.AlgebraicGeometry.NonnegTruncation
open scoped ZeroObject

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

universe u

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (D : TwistData A)
  (hqc : ∀ n : ℤ, (((Scheme.Modules.pushforward (relativeProj A).toBase).obj
    (D.algebra.piece n) : S.Modules)).IsQuasicoherent)

/-! ### The target of the homogeneous-section map -/

/-- **The target of the homogeneous-section map**: the direct image along `p` of the graded
algebra of twists, truncated to the nonnegative degrees, as data of Situation 01NN. -/
def twistTarget : SheafGradedAlgebra S :=
  pushforwardNonnegSheafGradedAlgebra (relativeProj A).toBase D.algebra D.mul_comm hqc

/-- In a nonnegative degree the target is the direct image of the corresponding twist. -/
theorem twistTarget_piece_ofNat (n : ℕ) :
    (twistTarget D hqc).piece (.ofNat n) =
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj (D.algebra.piece (.ofNat n)) :=
  rfl

/-- In a negative degree the target is a zero object. -/
theorem isZero_twistTarget_piece_negSucc (n : ℕ) :
    IsZero ((twistTarget D hqc).piece (.negSucc n)) :=
  isZero_piece_negSucc (pushforwardGradedAlgebra (relativeProj A).toBase D.algebra) n

/-! ### The homogeneous-section map in a single integer degree -/

/-- **The degree-`n` component of `ψ`**: the `n`-th component of `TwistData.ψ` when `n ≥ 0`, and
the zero morphism when `n < 0`, both source and target then being zero objects. -/
def psiApp : ∀ n : ℤ, A.piece n ⟶ (twistTarget D hqc).piece n
  | .ofNat n => D.ψ n
  | .negSucc _ => 0

/-- In a nonnegative degree `n`, `psiApp` is the `n`-th component of `TwistData.ψ`. -/
@[simp] theorem psiApp_ofNat (n : ℕ) : psiApp D hqc (.ofNat n) = D.ψ n := rfl

/-- In a negative degree, the component `psiApp` is the zero morphism. -/
@[simp] theorem psiApp_negSucc (n : ℕ) : psiApp D hqc (.negSucc n) = 0 := rfl

/-- A negative-degree component of `ψ` kills every local section, both sides being zero. -/
theorem psiApp_app_eq_zero_of_neg {i : ℤ} (hi : i < 0) (U : S.Opens)
    (a : Γ(A.piece i, U)) : (psiApp D hqc i).app U a = 0 := by
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hi
  simp [psiApp_negSucc]

/-- A local section of `𝒜` in a negative degree is zero: the piece is a zero object. -/
theorem eq_zero_of_neg {i : ℤ} (hi : i < 0) (U : S.Opens) (a : Γ(A.piece i, U)) : a = 0 :=
  eq_zero_of_isZero (A.negative_isZero i hi) (op U) a

/-! ### The homogeneous-section map as a homomorphism of graded algebras -/

/-- **The homogeneous-section map of a relative Proj as one homomorphism of sheaf-level graded
algebras** `𝒜 ⟶ (p_*(⨁_d 𝒪(d)))_{≥0}`, with components `psiApp`. -/
def psiHom : SheafGradedAlgebraHom A (twistTarget D hqc) where
  app := psiApp D hqc
  app_mul i j U a b := by
    rcases i with p | p
    · rcases j with q | q
      · exact eq_of_heq (D.ψ_mul U p q a b)
      · rw [eq_zero_of_neg (Int.negSucc_lt_zero q) U b]
        simp
    · rw [eq_zero_of_neg (Int.negSucc_lt_zero p) U a]
      simp
  app_one U := D.ψ_one U

/-- The degree-`n` component of `psiHom` is `psiApp D hqc n`. -/
@[simp] theorem psiHom_app (n : ℤ) : (psiHom D hqc).app n = psiApp D hqc n := rfl

/-! ### The kernel of `ψ` and the quotient by it -/

/-- **The graded ideal `ker ψ`** cut out by the homogeneous-section map, with quasi-coherent
pieces. -/
def psiIdeal : RelativeProjGradedIdeal.GradedIdeal A :=
  RelativeProjGradedIdeal.kernelGradedIdeal (psiHom D hqc)

/-- **The quotient `𝒜/ker ψ`**, as data of Situation 01NN. -/
def psiQuotient : SheafGradedAlgebra S :=
  RelativeProjGradedIdeal.quotByKernel (psiHom D hqc)

/-- **`Proj_S(𝒜/ker ψ) ⟶ Proj_S(𝒜)`.** -/
def psiAmbientHom :
    (relativeProj (psiQuotient D hqc)).scheme ⟶ (relativeProj A).scheme :=
  RelativeProjGradedIdeal.kernelAmbientHom (psiHom D hqc)

/-- **`Proj_S(𝒜/ker ψ)` is a closed subscheme of `Proj_S(𝒜)`.** -/
theorem isClosedImmersion_psiAmbientHom : IsClosedImmersion (psiAmbientHom D hqc) :=
  RelativeProjGradedIdeal.isClosedImmersion_kernelAmbientHom (psiHom D hqc)

/-- **The quotient homomorphism is degreewise surjective on the sections over the affine opens
of the base**. -/
theorem surjectiveOnAffineSections_psiQuotient :
    ProjBundleSurjection.SurjectiveOnAffineSections
      (RelativeProjGradedIdeal.quotMkKernel (psiHom D hqc)) :=
  RelativeProjGradedIdeal.surjectiveOnAffineSections_quotMkKernel (psiHom D hqc)

/-- **A homogeneous local section of `𝒜` dies in `𝒜/ker ψ` exactly when `ψ` kills it.** -/
theorem psiQuotient_app_eq_zero_iff (n : ℤ) (U : S.Opens) (a : Γ(A.piece n, U)) :
    ((RelativeProjGradedIdeal.quotMkKernel (psiHom D hqc)).app n).app U a = 0 ↔
      ((psiHom D hqc).app n).app U a = 0 :=
  RelativeProjGradedIdeal.quotMkKernel_app_eq_zero_iff (psiHom D hqc) n U a

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
