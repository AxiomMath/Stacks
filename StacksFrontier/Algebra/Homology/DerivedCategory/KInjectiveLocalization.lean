module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Right derived functors on a Grothendieck abelian category, tested on K-injectives

Let `C` be a Grothendieck abelian category. Every cochain complex in `C` admits a
quasi-isomorphism into a K-injective complex, so the pointwise criterion of Stacks 070K,
`Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective`,
applies to every functor out of `K(C)`. This file records the three consequences
that the derived-functor developments throughout the project use, each a statement about
`D(C)` that is *checked on K-injective complexes only*:

* the comparison map of a right derived functor is invertible at a K-injective complex;
* a morphism of functors on `D(C)` invertible at the K-injective complexes is invertible;
* a comparison map invertible at the K-injective complexes exhibits its target as a right
  derived functor.

They are stated for an arbitrary target category `H`, not just for a derived category, which is
what lets them be used for the homology functors and for derived sections alike.

## Main results

* `Stacks.Cohomology.Localization.enoughKInjectives`: every cochain complex in a Grothendieck
  abelian category receives a quasi-isomorphism from a K-injective complex.
* `Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`: the derived-functor unit is
  invertible at a K-injective complex.
* `Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives`: a natural transformation of
  functors on the derived category is invertible as soon as it is invertible at the images of
  the K-injective complexes.
* `Stacks.Cohomology.Localization.rightDerived_of_kInjectives`: the criterion for a
  transformation to exhibit a right derived functor, tested on K-injective complexes.

## References

* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v wG vH uH wD

namespace Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{wG} C]

/-- Every cochain complex in a Grothendieck abelian category admits a quasi-isomorphism into a
K-injective complex: the functorial resolution of Stacks 079P, forgetting functoriality. -/
lemma enoughKInjectives (K : CochainComplex C ℤ) :
    ∃ (I : CochainComplex C ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion C).app K, inferInstance, inferInstance⟩

variable [HasDerivedCategory.{wD} C] {H : Type uH} [Category.{vH} H]

/-- The unit of a right derived functor is invertible at a K-injective complex. -/
lemma derivedUnit_isIsoOnKInjective
    (F : HomotopyCategory C (.up ℤ) ⥤ H) (RF : DerivedCategory C ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ))]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso (α.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v, vH, wD,
    u, uH, max u v}
    F enoughKInjectives).2 DerivedCategory.Qh RF α I inferInstance

/-- A natural transformation between functors on the derived category is an isomorphism as soon
as it is one at the image of every K-injective complex. -/
lemma natTrans_isIso_of_kInjectives {F G : DerivedCategory C ⥤ H} (τ : F ⟶ G)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (τ.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj I)))) : IsIso τ := by
  suffices ∀ K, IsIso (τ.app K) from NatIso.isIso_of_isIso_app τ
  intro K
  rw [← NatTrans.isIso_app_iff_of_iso τ (DerivedCategory.Qh.objObjPreimageIso K)]
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective (DerivedCategory.Qh.objPreimage K)
  rw [← hL]
  obtain ⟨I, q, hI, hq⟩ := enoughKInjectives L
  have hqi : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map q)) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  rw [NatTrans.isIso_app_iff_of_iso τ (asIso (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient C (.up ℤ)).map q)))]
  exact h I

/-- A comparison map which is invertible at every K-injective complex exhibits its target as a
right derived functor. -/
lemma rightDerived_of_kInjectives
    (F : HomotopyCategory C (.up ℤ) ⥤ H) (RF : DerivedCategory C ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (α.app ((HomotopyCategory.quotient C (.up ℤ)).obj I))) :
    RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ)) := by
  let _ :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v, vH,
      wD, u, uH, max u v}
    F enoughKInjectives).1
  let R := F.totalRightDerived DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  let β := F.totalRightDerivedUnit DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  rw [Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc R β]
  refine natTrans_isIso_of_kInjectives _ fun I _ => ?_
  have := derivedUnit_isIsoOnKInjective F R β I
  exact (isIso_comp_left_iff (β.app _) _).mp
    (R.rightDerived_fac_app β (HomotopyCategory.quasiIso C (.up ℤ)) RF α _ ▸ h I)


end Stacks.Cohomology.Localization
