module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardSpecField
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceLeftExactness
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurvePicard
import StacksFrontier.AlgebraicGeometry.Blowup.Colength.InverseImageSections

/-!
# The contraction in the Picard sequence of an exceptional curve

Let `b : X ⟶ X'` contract an exceptional curve of the first kind `E ⊆ X`, presented by its ideal
sheaf `D` together with an isomorphism `e : 𝐏¹_k ≅ E` carrying the normal sheaf to `𝒪(-1)`. The
sequence

`0 ⟶ Pic(X') ⟶ Pic(X) ⟶ ℤ ⟶ 0`

has pullback along `b` for its first map and the degree on `E` for its second, split by
`n ↦ 𝒪_X(-nE)`. Pullback along `b` is injective, because the structure-sheaf comparison
`𝒪_{X'} ⟶ b_*𝒪_X` of a contraction is an isomorphism; and a class pulled back along `b` has
degree zero on `E`, because `E ⟶ X ⟶ X'` factors through the one-point subscheme that `b`
contracts `E` to.

The degree is the honest `ℤ`-valued one: `Pic(𝐏¹_k) = ℤ`, the identification carrying `m` to
`𝒪(m)`, so the degree map and the clauses computed from it need no parameter.

## Main definitions

* `AlgebraicGeometry.projectiveLinePicardAddEquiv` — the identification `ℤ ≃+ Pic(𝐏¹_k)`,
  `m ↦ 𝒪(m)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalDegree` — the degree of a Picard class on
  the exceptional curve.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.injective_schemePullbackClassHom_of_isContraction` —
  **left exactness:** pullback `Pic(X') ⟶ Pic(X)` along the contraction is injective.
* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalDegree_schemePullbackClassHom` — **a class
  pulled back along the contraction has degree zero on the exceptional curve.**
* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalDegree_negativeExceptionalMultiple`,
  `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalDegree_surjective`,
  `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalDegree_picardClass` and
  `AlgebraicGeometry.Scheme.IdealSheafData.negativeExceptionalMultipleHom_injective'` — the
  splitting, right exactness and the normalization `deg 𝒪_X(E) = -1`, with no hypothesis beyond
  the exceptional curve.

## What is not done

The converse inclusion at `Pic(X)` — that a class of degree zero on `E` is pulled back along
`b` — is not proved, and no declaration here states it. The source builds it from `b_*ℒ`: that
`b_*ℒ` is invertible with `b^*b_*ℒ ⟶ ℒ` an isomorphism is checked after flat base change to the
spectrum of the regular local ring at the contracted point, where every invertible module is a
multiple of `𝒪_X(E)`. That last input is the generation half of
[Stacks, Tag 0C5G](https://stacks.math.columbia.edu/tag/0C5G), which the library carries as the
hypothesis `hgen` of
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.picardGroupEquivInt`; it
needs a trivialization of an invertible module over `X ∖ E` to be read as a regular meromorphic
section of it on `X`, and nothing in the library does that.

## References

* [Stacks Project, Tag 0C5L](https://stacks.math.columbia.edu/tag/0C5L)
* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.RingedSpace (structureIsSheaf)

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry

/-- The identification `ℤ ≃+ Pic(𝐏¹_k)` carrying `m` to the class of the twist `𝒪(m)`, read in
the Picard group `Stacks.Picard.ofScheme`. -/
public def projectiveLinePicardAddEquiv (k : Type u) [Field k] :
    ℤ ≃+ Stacks.Picard.ofScheme (projectiveLineProj k) :=
  Stacks.PicardUFD.twistPicardAddEquiv k 1 Nat.one_pos

/-- The identification `ℤ ≃+ Pic(𝐏¹_k)` carries `m` to the class of `𝒪(m)`. -/
public theorem projectiveLinePicardAddEquiv_apply (k : Type u) [Field k] (m : ℤ) :
    projectiveLinePicardAddEquiv k m =
      Stacks.SheafOfModules.picardClass (projectiveLineProj k).presheaf
        (structureIsSheaf (projectiveLineProj k).toRingedSpace)
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)
        (Scheme.IdealSheafData.isInvertible_twistingSheaf_projectiveLine k m) :=
  rfl

namespace Scheme.IdealSheafData

variable {X X' : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  [Stacks.Divisors.IsEffectiveCartierDivisor D] (e : projectiveLineProj k ≅ D.subscheme)
  (b : X ⟶ X')

/-! ### The degree on the exceptional curve -/

/-- **The degree of a Picard class on the exceptional curve**: restrict to `E`, read the result
on `𝐏¹_k` through `e`, and convert to an integer through `Pic(𝐏¹_k) = ℤ`. -/
public abbrev exceptionalDegree : Stacks.Picard.ofScheme X →+ ℤ :=
  exceptionalDegreeHom D k e (projectiveLinePicardAddEquiv k)

/-- **Stacks Project, Tag 0C5L, the splitting.** The degree of `𝒪_X(-nE)` on the exceptional
curve is `n`, so the sequence of the tag is split by `n ↦ 𝒪_X(-nE)`. -/
@[stacks 0C5L "the splitting: the degree of O_X(-nE) on the exceptional curve is n"]
public theorem exceptionalDegree_negativeExceptionalMultiple
    (hE : D.IsExceptionalCurveOfFirstKind k e) (n : ℤ) :
    D.exceptionalDegree k e (negativeExceptionalMultipleHom D n) = n :=
  exceptionalDegreeHom_negativeExceptionalMultiple D k e (projectiveLinePicardAddEquiv k) hE
    (projectiveLinePicardAddEquiv_apply k (-1)) n

/-- **Stacks Project, Tag 0C5L, right exactness.** The degree map on the exceptional curve is
surjective onto `ℤ`, because `𝒪_X(-nE)` has degree `n`. -/
@[stacks 0C5L "right exactness: the degree map Pic(X) ⟶ Z on the exceptional curve is \
surjective, witnessed by the splitting n ↦ O_X(-nE)"]
public theorem exceptionalDegree_surjective (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Function.Surjective (D.exceptionalDegree k e) := fun n =>
  ⟨negativeExceptionalMultipleHom D n, exceptionalDegree_negativeExceptionalMultiple D k e hE n⟩

/-- **The degree of `𝒪_X(E)` on the exceptional curve is `-1`**, the source's reading of the
definition of an exceptional curve of the first kind. -/
@[stacks 0C5L "the normalization of the degree map: O_X(E) has degree -1 on the exceptional \
curve"]
public theorem exceptionalDegree_picardClass (hE : D.IsExceptionalCurveOfFirstKind k e) :
    D.exceptionalDegree k e (Stacks.Divisors.picardClass D) = -1 :=
  exceptionalDegreeHom_picardClass D k e (projectiveLinePicardAddEquiv k) hE
    (projectiveLinePicardAddEquiv_apply k (-1))

/-- **The splitting of the sequence is injective**, so `ℤ` is a direct summand of `Pic(X)`:
distinct multiples `𝒪_X(-nE)` have distinct degrees on the exceptional curve. -/
@[stacks 0C5L "the splitting n ↦ O_X(-nE) is injective, so Z is a direct summand of Pic(X)"]
public theorem negativeExceptionalMultipleHom_injective'
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Function.Injective (negativeExceptionalMultipleHom D) :=
  negativeExceptionalMultipleHom_injective D k e (projectiveLinePicardAddEquiv k) hE
    (projectiveLinePicardAddEquiv_apply k (-1))

/-! ### Pullback along the contraction -/

omit [Stacks.Divisors.IsEffectiveCartierDivisor D] in
/-- **Stacks Project, Tag 0C5L, left exactness.** Pullback of Picard classes along the
contraction of an exceptional curve of the first kind is injective: the structure-sheaf
comparison `𝒪_{X'} ⟶ b_*𝒪_X` of a contraction is an isomorphism, and pullback along a morphism
with that property is injective. -/
@[stacks 0C5L "left exactness: pullback Pic(X') ⟶ Pic(X) along the contraction of the \
exceptional curve is injective"]
public theorem injective_schemePullbackClassHom_of_isContraction
    (hb : IsContractionOfExceptionalCurve D b) :
    Function.Injective (Stacks.Picard.schemePullbackClassHom b) :=
  Stacks.Picard.injective_schemePullbackClass_of_isIso_c b hb.isIso_c

/-- The subscheme cut out by the reduced ideal sheaf of a closed point has exactly one point. -/
private theorem subsingleton_subscheme_vanishingIdeal {Z : Scheme.{u}} (z : Z)
    (hz : IsClosed ({z} : Set Z)) :
    Subsingleton (vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)).subscheme ∧
      Nonempty (vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)).subscheme := by
  set I := vanishingIdeal (⟨{z}, hz⟩ : Closeds Z) with hI
  have hrange : Set.range I.subschemeι.base = ({z} : Set Z) := by
    have h := I.range_subschemeι
    rw [h, hI]
    exact coe_support_vanishingIdeal _
  refine ⟨⟨fun a c => (IsClosedImmersion.isClosedEmbedding I.subschemeι).injective ?_⟩, ?_⟩
  · have ha : I.subschemeι.base a ∈ Set.range I.subschemeι.base := ⟨a, rfl⟩
    have hc : I.subschemeι.base c ∈ Set.range I.subschemeι.base := ⟨c, rfl⟩
    rw [hrange, Set.mem_singleton_iff] at ha hc
    rw [ha, hc]
  · have hz' : z ∈ Set.range I.subschemeι.base := by rw [hrange]; rfl
    exact ⟨hz'.choose⟩

/-- The degree on the subscheme cut out by an inverse-image ideal sheaf vanishes on classes
pulled back from the target, when the original subscheme has exactly one point. -/
private theorem exceptionalDegree_schemePullbackClassHom_aux {Y Y' : Scheme.{u}}
    (I : Y'.IdealSheafData) (f : Y ⟶ Y') (k : Type u) [Field k]
    [Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f)]
    (ε : projectiveLineProj k ≅ (I.comap f).subscheme)
    (hsub : Subsingleton I.subscheme) (hne : Nonempty I.subscheme)
    (L' : Stacks.Picard.ofScheme Y') :
    (I.comap f).exceptionalDegree k ε (Stacks.Picard.schemePullbackClassHom f L') = 0 := by
  have := hsub
  have := hne
  have h0 : ∀ {Z Z' : Scheme.{u}} (g : Z ⟶ Z'),
      Stacks.Picard.schemePullbackClass g (0 : Stacks.Picard.ofScheme Z') = 0 :=
    fun g => map_zero (Stacks.Picard.schemePullbackClassHom g)
  have hzero : Stacks.Picard.schemePullbackClass I.subschemeι L' = 0 :=
    Stacks.Picard.eq_zero_of_subsingleton _
  have key : exceptionalRestrictionHom (I.comap f) k ε
      (Stacks.Picard.schemePullbackClassHom f L') = 0 := by
    show Stacks.Picard.schemePullbackClass ε.hom
      (Stacks.Picard.schemePullbackClass (I.comap f).subschemeι
        (Stacks.Picard.schemePullbackClass f L')) = 0
    rw [Stacks.Picard.schemePullbackClass_comp (I.comap f).subschemeι f L',
      subschemeι_comap_comp I f, ← Stacks.Picard.schemePullbackClass_comp, hzero, h0, h0]
  have h := congrArg (projectiveLinePicardAddEquiv k).symm key
  rw [map_zero] at h
  exact h

/-- **Stacks Project, Tag 0C5L, the inclusion `im(b^*) ⊆ ker(deg)`.** A Picard class pulled back
along the contraction has degree zero on the exceptional curve: the curve maps into the
one-point subscheme it is contracted to, whose Picard group vanishes. -/
@[stacks 0C5L "exactness at Pic(X), the inclusion of the image of b^* in the kernel of the \
degree: a class pulled back along the contraction has degree zero on the exceptional curve"]
public theorem exceptionalDegree_schemePullbackClassHom
    (hb : IsContractionOfExceptionalCurve D b) (L' : Stacks.Picard.ofScheme X') :
    D.exceptionalDegree k e (Stacks.Picard.schemePullbackClassHom b L') = 0 := by
  obtain ⟨z, hz, -, -, hD, -, -⟩ := hb.exists_blowUp_iso
  subst hD
  obtain ⟨hsub, hne⟩ := subsingleton_subscheme_vanishingIdeal z hz
  exact exceptionalDegree_schemePullbackClassHom_aux _ b k e hsub hne L'

end Scheme.IdealSheafData

end AlgebraicGeometry

end
