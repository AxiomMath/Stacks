module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Trace
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# `Rf_*` of the twists `𝒪(d)`, `-n-1 ≤ d ≤ -1`, on `ℙⁿ_S`, at any model of `D(𝒪)`

Let `S` be a scheme, `n = m + 1 ≥ 1` and `f : ℙⁿ_S ⟶ S` the structure morphism. For the
unbounded derived direct image `Stacks.Duality.derivedPushforward f`, at an arbitrary model of the
two derived categories:

* `Rf_*(𝒪(-n-1)[0]) ≅ 𝒪_S[-n]`, i.e. `Rf_*(𝒪(-n-1)[n]) ≅ 𝒪_S`: the higher direct images of
  `𝒪(-n-1)` vanish outside degree `n` and the trace identifies the degree-`n` one with `𝒪_S`;
* `Rf_*(𝒪(d)[0]) = 0` for `-n ≤ d ≤ -1`.

These are the two facts about `Rf_*` that the proof of [Stacks, Tag 0A9W] starts from.

## Main results

* `Stacks.Duality.nonempty_homology_derivedPushforward_iso_rightDerived` — at any model, the
  degree-`q` cohomology of `Rf_*(M[0])` is `R^q f_* M` (Mathlib's model-free derived functor), for
  any morphism of schemes and any module.
* `Stacks.Duality.ProjectiveSpace.isZero_derivedPushforward_twistOver` — `Rf_*(𝒪(d)[0]) = 0` for
  `-n ≤ d ≤ -1`.
* `Stacks.Duality.ProjectiveSpace.nonempty_derivedPushforward_dualizingTwist_iso` —
  `Rf_*(𝒪(-n-1)[0]) ≅ 𝒪_S[-n]`.
* `Stacks.Duality.ProjectiveSpace.nonempty_derivedPushforward_twistOver_zero_iso` —
  `Rf_*(𝒪[0]) ≅ 𝒪_S[0]`.

## References

* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe w u

namespace Stacks.Duality

section AnyMorphism

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- At any model, `Rf_*(M[0])` is the bounded below right derived functor of `f_*` at `M[0]`. -/
private theorem nonempty_derivedPushforward_single_iso (M : X.Modules) :
    Nonempty ((derivedPushforward.{w} f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M) ≅
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)).obj) := by
  have hE : ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M).obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor X.Modules 0).obj M).IsGE 0
    infer_instance
  exact Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f) (derivedPushforward.{w} f) (derivedPushforwardUnit.{w} f)
    (fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective.{w} f I hI)
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) 0 hE

/-- **The cohomology of `Rf_*(M[0])` is the higher direct image, at any model.** For a morphism
of schemes `f`, a module `M` and `q ≥ 0`, the degree-`q` cohomology sheaf of
`Stacks.Duality.derivedPushforward f` applied to `M[0]` is `R^q f_* M`, Mathlib's `ℕ`-indexed
right derived functor of the direct image — which is built from injective resolutions and so
does not depend on the chosen model. -/
theorem nonempty_homology_derivedPushforward_iso_rightDerived (M : X.Modules) (q : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor Y.Modules (q : ℤ)).obj
        ((derivedPushforward.{w} f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M)) ≅
      ((Scheme.Modules.pushforward f).rightDerived q).obj M) := by
  obtain ⟨e⟩ := nonempty_derivedPushforward_single_iso.{w} f M
  exact ⟨(DerivedCategory.homologyFunctor Y.Modules (q : ℤ)).mapIso e ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app M).symm⟩

/-- At any model, `Rf_*(M[0])` has no cohomology in negative degrees. -/
theorem isZero_homology_derivedPushforward_of_neg (M : X.Modules) (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules q).obj
        ((derivedPushforward.{w} f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M))) := by
  obtain ⟨e⟩ := nonempty_derivedPushforward_single_iso.{w} f M
  exact IsZero.of_iso
    (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj (Scheme.Modules.pushforward f) q hq M)
    ((DerivedCategory.homologyFunctor Y.Modules q).mapIso e)

end AnyMorphism

namespace ProjectiveSpace

section Standard

attribute [local instance 2000] HasDerivedCategory.standard

variable (m : ℕ) (S : Scheme.{u})

/-- `R^q f_* 𝒪(d)` for `ℙⁿ_S`, in Mathlib's model-free `ℕ`-indexing, vanishes when the bounded
below right derived functor at the standard model vanishes in degree `q`. -/
theorem isZero_rightDerived_of_isZero_rightDerivedPlus (d : ℤ) (q : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
      (q : ℤ)).obj (twistOver (m + 1) S d))) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerived
      q).obj (twistOver (m + 1) S d)) :=
  IsZero.of_iso h ((Stacks.DerivedIndexing.rightDerivedIso
    (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)) q).app _)

end Standard

section AnyModel

variable (m : ℕ) (S : Scheme.{u})
  [HasDerivedCategory.{w} (projectiveSpaceOver (m + 1) S).Modules]
  [HasDerivedCategory.{w} S.Modules]

/-- The structure morphism of `ℙⁿ_S`, `n = m + 1`. -/
abbrev structureMorphism : projectiveSpaceOver (m + 1) S ⟶ S := projectiveSpaceOver (m + 1) S ↘ S

/-- The degree-`q` cohomology of `Rf_*(𝒪(d)[0])` vanishes when `R^q f_* 𝒪(d)` does. -/
theorem isZero_homology_derivedPushforward_twistOver_of_isZero (d : ℤ) (q : ℤ)
    (h : ∀ k : ℕ, q = (k : ℤ) → IsZero (((Scheme.Modules.pushforward
      (structureMorphism m S)).rightDerived k).obj (twistOver (m + 1) S d))) :
    IsZero ((DerivedCategory.homologyFunctor S.Modules q).obj
      ((derivedPushforward.{w} (structureMorphism m S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistOver (m + 1) S d)))) := by
  rcases lt_or_ge q 0 with hq | hq
  · exact isZero_homology_derivedPushforward_of_neg _ _ q hq
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = (k : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg hq).symm⟩
    obtain ⟨e⟩ := nonempty_homology_derivedPushforward_iso_rightDerived.{w}
      (structureMorphism m S) (twistOver (m + 1) S d) k
    exact IsZero.of_iso (h k rfl) e

/-- **`Rf_*(𝒪(d)[0]) = 0` for `-n ≤ d ≤ -1`**, at any model: every higher direct image of such a
twist vanishes ([Stacks, Tag 01XW]). -/
theorem isZero_derivedPushforward_twistOver {d : ℤ} (hd₁ : -((m + 1 : ℕ) : ℤ) ≤ d)
    (hd₂ : d < 0) :
    IsZero ((derivedPushforward.{w} (structureMorphism m S)).obj
      ((DerivedCategory.singleFunctor _ 0).obj (twistOver (m + 1) S d))) :=
  Stacks.Cohomology.PushforwardRestriction.isZero_derived_of_homology_isZero _ fun q =>
    isZero_homology_derivedPushforward_twistOver_of_isZero m S d q fun k _ =>
      Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isZero_push_twistOver_of_acyclic
        m S k hd₁ hd₂

/-- Away from degree `n`, the cohomology of `Rf_*(𝒪(-n-1)[0])` vanishes. -/
theorem isZero_homology_derivedPushforward_dualizingTwist (q : ℤ)
    (hq : q ≠ ((m + 1 : ℕ) : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor S.Modules q).obj
      ((derivedPushforward.{w} (structureMorphism m S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (twistOver (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1))))) := by
  refine isZero_homology_derivedPushforward_twistOver_of_isZero m S _ q fun k hk => ?_
  subst hk
  refine isZero_rightDerived_of_isZero_rightDerivedPlus m S _ k ?_
  let := HasDerivedCategory.standard (projectiveSpaceOver (m + 1) S).Modules
  let := HasDerivedCategory.standard S.Modules
  by_cases hk0 : k = 0
  · subst hk0
    open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing in
    exact isZero_rightDerivedPlus_pushforward_twistOver_zero_of_neg (m + 1) (by omega) S _
      (by omega)
  · open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing in
    exact isZero_rightDerivedPlus_pushforward_twistOver_of_ne (m + 1) S _ (k : ℤ)
      (by exact_mod_cast hk0) hq

/-- A derived-category object with cohomology only in degree `n`, where it is `A`, is `A[-n]`. -/
private theorem nonempty_iso_singleFunctor_of_homology {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{w} C] (K : DerivedCategory C) (n : ℤ) (A : C)
    (h : ∀ i, i ≠ n → IsZero ((DerivedCategory.homologyFunctor C i).obj K))
    (t : (DerivedCategory.homologyFunctor C n).obj K ≅ A) :
    Nonempty (K ≅ (DerivedCategory.singleFunctor C n).obj A) := by
  have : K.IsGE n := (DerivedCategory.isGE_iff K _).2 fun i hi => h i (by omega)
  have : K.IsLE n := (DerivedCategory.isLE_iff K _).2 fun i hi => h i (by omega)
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor C _).mapIso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor C n).mapIso e.symm ≪≫ t)⟩

/-- **`Rf_*(𝒪(-n-1)[0]) ≅ 𝒪_S[-n]`**, at any model: the higher direct images of `𝒪(-n-1)`
vanish outside degree `n`, and the trace of
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.trace` identifies the degree-`n` one
with `𝒪_S`. -/
theorem nonempty_derivedPushforward_dualizingTwist_iso :
    Nonempty ((derivedPushforward.{w} (structureMorphism m S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (twistOver (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1))) ≅
      (DerivedCategory.singleFunctor S.Modules ((m + 1 : ℕ) : ℤ)).obj
        (SheafOfModules.unit S.ringCatSheaf)) := by
  obtain ⟨t⟩ := nonempty_homology_derivedPushforward_iso_rightDerived.{w}
    (structureMorphism m S) (twistOver (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1)) (m + 1)
  exact nonempty_iso_singleFunctor_of_homology _ _ _
    (fun i hi => isZero_homology_derivedPushforward_dualizingTwist m S i hi)
    (t ≪≫ Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.trace m S)

/-- Away from degree `0`, the cohomology of `Rf_*(𝒪[0])` vanishes. -/
theorem isZero_homology_derivedPushforward_twistOver_zero (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor S.Modules q).obj
      ((derivedPushforward.{w} (structureMorphism m S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistOver (m + 1) S 0)))) := by
  refine isZero_homology_derivedPushforward_twistOver_of_isZero m S _ q fun k hk => ?_
  subst hk
  refine isZero_rightDerived_of_isZero_rightDerivedPlus m S _ k ?_
  let := HasDerivedCategory.standard (projectiveSpaceOver (m + 1) S).Modules
  let := HasDerivedCategory.standard S.Modules
  by_cases hkn : (k : ℤ) = ((m + 1 : ℕ) : ℤ)
  · rw [hkn]
    open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage in
    exact isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt m S (by omega)
  · open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing in
    exact isZero_rightDerivedPlus_pushforward_twistOver_of_ne (m + 1) S _ (k : ℤ)
      (by exact_mod_cast hq) hkn

/-- **`Rf_*(𝒪_{ℙⁿ_S}(0)[0]) ≅ 𝒪_S[0]`**, at any model: the higher direct images of the structure
sheaf of projective space vanish and its direct image is `𝒪_S`
(`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.pushZeroTwistIso`). -/
theorem nonempty_derivedPushforward_twistOver_zero_iso :
    Nonempty ((derivedPushforward.{w} (structureMorphism m S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistOver (m + 1) S 0)) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj (SheafOfModules.unit S.ringCatSheaf)) := by
  obtain ⟨t⟩ := nonempty_homology_derivedPushforward_iso_rightDerived.{w}
    (structureMorphism m S) (twistOver (m + 1) S 0) 0
  exact nonempty_iso_singleFunctor_of_homology _ _ _
    (fun i hi => isZero_homology_derivedPushforward_twistOver_zero m S i hi)
    (t ≪≫ Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.pushZeroTwistIso m S)

end AnyModel

end ProjectiveSpace

end Stacks.Duality

end
