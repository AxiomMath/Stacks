module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleDepthFourVanishing
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroSupport
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumPicardTorsion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The SGA2 injectivity of `Pic(U) → Pic(U₀)` in depth four

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪` a nonzerodivisor with `depth(A/fA) ≥ 3`.
Let `U`, resp. `U₀`, be the punctured spectrum of `A`, resp. of `A/fA`. Then

`Pic(U) → Pic(U₀)`

is injective. This is the conclusion of [Stacks, Tag 0FIX].

## Main results

* `Stacks.Algebraization.nonempty_linearEquiv_closedFibreSectionsModule`: the global sections of
  the closed-fibre member of an invertible coherent triple are `A/fA`.
* `Stacks.Algebraization.finite_closedFibreSectionsModule` and
  `Stacks.Algebraization.three_le_depth_closedFibreSectionsModule`: these sections form a finite
  `A`-module, of depth at least three when `depth(A/fA) ≥ 3`.
* `Stacks.Algebraization.eq_zero_of_schemePullbackClass_eq_zero_of_three_le_depth_quotient`: a
  class on `U` restricting to zero on `U₀` is zero.
* `Stacks.Algebraization.picRestrictionInjective_of_three_le_depth_quotient`: injectivity of
  `Pic(U) → Pic(U₀)`, with `depth(A/fA) ≥ 3` as the only hypothesis beyond `f` being a
  nonzerodivisor in `𝔪`.
* `Stacks.Algebraization.picRestrictionInjective_of_regularQuotient_of_depth`:
  [Stacks, Tag 0FIX], stated with the five hypotheses of the source.

## Implementation notes

`U` is `Stacks.Divisors.puncturedSpectrum A` and `U₀` is
`Stacks.Algebraization.puncturedClosedFibre A f`, which for `f ∈ 𝔪` is the punctured spectrum of
`A/fA`; the map on Picard groups is `Stacks.Picard.schemePullbackClass` of the restriction
`U₀ ⟶ U`, the spelling [Stacks, Tag 0F2G] and [Stacks, Tag 0F2A] are stated at.

## References

* [Stacks Project, Tag 0FIX](https://stacks.math.columbia.edu/tag/0FIX)
* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

open Stacks.RingedSpace (structureIsSheaf)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### The closed-fibre sections of an invertible coherent triple -/

/-- The global sections of the closed-fibre member of an invertible coherent triple are
`A/fA`. -/
theorem nonempty_linearEquiv_closedFibreSectionsModule (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀] :
    Nonempty ((closedFibreSectionsModule A f T : Type u) ≃ₗ[A] (A ⧸ Ideal.span {f})) := by
  have := isLocalRing_quotient_span (A := A) (f := f) hf
  have : Stacks.Ample.IsInvertibleModule (closedFibre A f) T.F₀ :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ T.F₀).2 ‹_›
  obtain ⟨e₀⟩ := nonempty_iso_unitModule_closedFibre hf T.F₀
  let : Module A ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj T.F₀) :=
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
      ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj T.F₀)).isModule
  let : IsScalarTower A (A ⧸ Ideal.span {f})
      ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj T.F₀) :=
    ⟨fun a b m => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let eB := ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).mapIso e₀ ≪≫
    (unitSpecSectionsEquiv (A ⧸ Ideal.span {f})).toModuleIso).toLinearEquiv
  exact ⟨eB.restrictScalars A⟩

/-- The global sections of the closed-fibre member of an invertible coherent triple form a finite
`A`-module. -/
theorem finite_closedFibreSectionsModule (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀] :
    Module.Finite A (closedFibreSectionsModule A f T : Type u) :=
  let e := (nonempty_linearEquiv_closedFibreSectionsModule A f hf T).some
  Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- If `depth(A/fA) ≥ 3` then the global sections of the closed-fibre member of an invertible
coherent triple have depth at least three over `A`. -/
theorem three_le_depth_closedFibreSectionsModule (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hb : 3 ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f})) :
    3 ≤ Module.depth A (maximalIdeal A) (closedFibreSectionsModule A f T : Type u) := by
  rwa [Module.depth_eq_depth_of_linearEquiv (maximalIdeal A)
    (nonempty_linearEquiv_closedFibreSectionsModule A f hf T).some]

/-! ### A class trivial on the punctured closed fibre is zero -/

/-- **A class on the punctured spectrum whose restriction to the punctured closed fibre is zero is
itself zero**, when `f` is a nonzerodivisor of `𝔪` with `depth(A/fA) ≥ 3`. -/
theorem eq_zero_of_schemePullbackClass_eq_zero_of_three_le_depth_quotient (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A)
    (hreg : IsRegular f) (hb : 3 ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f}))
    {x : Stacks.Picard.ofScheme (Stacks.Divisors.puncturedSpectrum A).toScheme}
    (h0 : Stacks.Picard.schemePullbackClass (puncturedClosedFibreRestriction A f) x = 0) :
    x = 0 := by
  have hdepth : 3 ≤ Module.depth A (maximalIdeal A) A :=
    three_le_depth_of_two_le_depth_quotient A f hf hreg.left
      (le_trans (by norm_num) hb)
  have htf : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme) :=
    isFTorsionFree_unitModule A hreg.left
  set L := (Stacks.Picard.picardRepresentative
    (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace x).obj
  have hLs : Stacks.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (structureIsSheaf (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L :=
    (Stacks.Picard.picardRepresentative
      (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace x).property
  have hclass : Stacks.SheafOfModules.picardClass
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (structureIsSheaf (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L hLs = x :=
    Stacks.Picard.classOf_picardRepresentative _ x
  have hLamp : Stacks.Ample.IsInvertibleModule
      (Stacks.Divisors.puncturedSpectrum A).toScheme L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).1 hLs
  have hpull : Stacks.SheafOfModules.picardClass (puncturedClosedFibre A f).toScheme.presheaf
      (structureIsSheaf (puncturedClosedFibre A f).toScheme.toRingedSpace)
      ((Stacks.RingedSpace.pullbackFunctor
        (puncturedClosedFibreRestriction A f).toLRSHom.toShHom).obj L)
      (Stacks.RingedSpace.modulePullback_isInvertible_of
        (puncturedClosedFibreRestriction A f).toLRSHom.toShHom L hLs) = 0 := by
    rwa [← Stacks.Picard.pullbackClass_classOf
      (puncturedClosedFibreRestriction A f).toLRSHom.toShHom L hLs, hclass]
  have htriv : Stacks.SheafOfModules.IsTrivial
      (puncturedClosedFibre A f).toScheme.presheaf
      (puncturedClosedFibre A f).toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (puncturedClosedFibreRestriction A f)).obj L) :=
    (Stacks.AlgebraicGeometry.PicardBaseChange.classOf_eq_zero_iff_nonempty_iso_unit _ _).1 hpull
  obtain ⟨e⟩ := htriv
  have e' : (Scheme.Modules.pullback (puncturedClosedFibreRestriction A f)).obj L ≅
      Stacks.Ample.unitModule (puncturedClosedFibre A f).toScheme := e
  set T := coherentTripleOfTrivialRestriction A f htf L e'
  have hT : IsInvertibleTriple T :=
    isInvertibleTriple_coherentTripleOfTrivialRestriction A f htf L e'
  have h1 := hT.invertible_F
  have h2 := hT.invertible_F₀
  have hchi : T.eulerCharacteristic = 0 :=
    eulerCharacteristic_eq_zero_of_three_le_depth_closedFibreSections A f hf hreg T hdepth
      (finite_closedFibreSectionsModule A f hf T)
      (three_le_depth_closedFibreSectionsModule A f hf T hb)
  have hFtriv := (CoherentTriple.eulerCharacteristic_eq_zero_iff_isTrivial A f hf hreg T
    hdepth).1 hchi
  rw [← hclass]
  exact (Stacks.AlgebraicGeometry.PicardBaseChange.classOf_eq_zero_iff_nonempty_iso_unit _
    hLs).2 hFtriv

/-! ### The injectivity -/

/-- **`Pic(U) → Pic(U₀)` is injective** for a nonzerodivisor `f ∈ 𝔪` with `depth(A/fA) ≥ 3`. -/
theorem picRestrictionInjective_of_three_le_depth_quotient (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (hb : 3 ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f})) :
    PicRestrictionInjective A f := by
  intro x y hxy
  have hsub : Stacks.Picard.schemePullbackClass (puncturedClosedFibreRestriction A f) (x - y)
      = 0 := by
    have h := (Stacks.Picard.schemePullbackClassHom
      (puncturedClosedFibreRestriction A f)).map_sub x y
    rw [Stacks.Picard.pullbackClassHom_apply, Stacks.Picard.pullbackClassHom_apply,
      Stacks.Picard.pullbackClassHom_apply] at h
    have hxy' : Stacks.Picard.pullbackClass
        (puncturedClosedFibreRestriction A f).toLRSHom.toShHom x =
      Stacks.Picard.pullbackClass
        (puncturedClosedFibreRestriction A f).toLRSHom.toShHom y := hxy
    change Stacks.Picard.pullbackClass
      (puncturedClosedFibreRestriction A f).toLRSHom.toShHom (x - y) = 0
    rw [h, hxy', sub_self]
  exact sub_eq_zero.1
    (eq_zero_of_schemePullbackClass_eq_zero_of_three_le_depth_quotient A f hf hreg hb hsub)

/-! ### Tag 0FIX -/

/-- [SGA2, Exposé XI, Lemma 3.16]. Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`. Assume
`A` is a quotient of a regular ring `R`, that `f` is a nonzerodivisor, and that (a)
`depth(A_𝔭) ≥ 2` for every prime `𝔭` with `dim(A/𝔭) = 1` and (b) `depth(A/fA) ≥ 3`. Let `U`,
resp. `U₀`, be the punctured spectrum of `A`, resp. `A/fA`. Then `Pic(U) → Pic(U₀)` is
injective. -/
@[stacks 0FIX "the SGA2 lemma: for a Noetherian local ring that is a quotient of a regular ring \
and a nonzerodivisor `f` of the maximal ideal with `depth(A/fA) ≥ 3`, the map `Pic(U) → Pic(U₀)` \
from the punctured spectrum of `A` to that of `A/fA` is injective. The five hypotheses of the \
source are all demanded. The Euler characteristic of the invertible coherent triple completing a \
module trivial on `U₀` is shown to vanish in this depth, which by [Stacks, Tag 0F28] trivialises \
the module; the finiteness of `H^2` of its sections that this needs is [Stacks, Tag 0BPY]. The \
source's footnote that hypothesis (a) follows from hypothesis (b) is \
`twoLeDepthLocalization_of_dim_eq_one`, and the dualizing complex of a quotient of a regular \
ring is `hasDualizingComplexOfRegularQuotient`.", sga "2 XI 3.16" "more general"]
theorem picRestrictionInjective_of_regularQuotient_of_depth (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (f : A) (hfm : f ∈ maximalIdeal A) (_R : Type u)
    [CommRing _R] [IsRegularRing _R] (_π : _R →+* A) (_hπ : Function.Surjective _π)
    (hf : IsRegular f)
    (_ha : ∀ p : Ideal A, ∀ _ : p.IsPrime, ringKrullDim (A ⧸ p) = 1 → TwoLeDepthLocalization A p)
    (hb : 3 ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f})) :
    PicRestrictionInjective A f :=
  picRestrictionInjective_of_three_le_depth_quotient A f hfm hf hb

end Stacks.Algebraization

end
