module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNatIsoGlue
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SingleRightDerivedUnitComposition

/-!
# The unit `Φ(-)[0] ⟶ RΦ((-)[0])` is natural in the functor being derived

For an additive functor `Φ : 𝒜 ⥤ ℬ` between abelian categories with `𝒜` having enough injectives,
`Stacks.Cohomology.singleRightDerivedUnit` is the canonical transformation `Φ(-)[0] ⟶ RΦ((-)[0])`.
This file proves that it is natural in the functor being derived.

## Main results

All in the namespace `Stacks.Cohomology`.

* `singleRightDerivedUnit_natIso_hom_app`, `singleRightDerivedUnit_natIso_inv_app` — **the
  naturality**: for an isomorphism `e : Φ ≅ Φ'` of additive functors, `e` placed in degree zero
  followed by the unit of `RΦ'` is the unit of `RΦ` followed by the invariance comparison
  `CategoryTheory.Functor.rightDerivedFunctorPlusNatIso e`, and likewise for the inverses.
* `singleRightDerivedUnit_fac_app` — the same for an arbitrary natural transformation `τ`, with
  the derived transformation and its characterising factorization taken as arguments.  Both
  isomorphism forms are instances of it.
* `mapSingleFunctorCompQhIso_hom_app_natTrans`,
  `mapSingleFunctorCompQhIso_inv_app_natTrans` — the identification of `Φ(M[0])` with `(ΦM)[0]`
  is natural in `Φ`, in `D⁺(ℬ)`.
* `singleMapPlusHom_natTrans` and `singleMapHomologicalComplex_hom_app_natTrans` — the same in
  the bounded below homotopy category and on complexes.

## Implementation notes

The characterising factorization is an argument rather than a hypothesis on a named
construction, so that the two isomorphism forms — whose factorizations are
`CategoryTheory.Functor.rightDerivedFunctorPlusNatIso_hom_fac_app` and `…_inv_fac_app` — are
both instances and the computation is done once.  The accompanying `hσ` identifies the action on
`K⁺(𝒜)` that the factorization mentions with the degreewise action of `τ`; for both forms it
holds by `rfl`.

## References

* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M), when the composition comparison
  is an isomorphism
* [Stacks, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8), the unit at a single complex
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Stacks.Cohomology.ModulePushforwardComparison

universe v v₁ w w₁ u u₁

namespace Stacks.Cohomology

-- Everything below mentions `Functor.rightDerivedFunctorPlus`, so the cheap instance that gets
-- pointwise right derivability from `EnoughInjectives` is given precedence over the one that would
-- embark on proving termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The identification of `Φ(M[0])` with `(ΦM)[0]` is natural in `Φ` -/

section Complexes

variable {A : Type*} {B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (Φ Φ' : A ⥤ B) [Φ.Additive] [Φ'.Additive] (τ : Φ ⟶ Φ')

/-- **`HomologicalComplex.singleMapHomologicalComplex` is natural in the functor.**  The
identification of `Φ(M[j])` with `(ΦM)[j]`, followed by `τ` placed in degree `j`, is `τ` applied
termwise to `M[j]` followed by the identification for `Φ'`. -/
lemma singleMapHomologicalComplex_hom_app_natTrans {I : Type*} (c : ComplexShape I)
    [DecidableEq I] (j : I) (M : A) :
    (singleMapHomologicalComplex Φ c j).hom.app M ≫
        (HomologicalComplex.single B c j).map (τ.app M) =
      (NatTrans.mapHomologicalComplex τ c).app
          ((HomologicalComplex.single A c j).obj M) ≫
        (singleMapHomologicalComplex Φ' c j).hom.app M := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  by_cases h : i = j
  · subst h
    simp [single_map_f_self]
  · exact (isZero_single_obj_X c j (Φ'.obj M) i h).eq_of_tgt _ _

/-- **`Stacks.Cohomology.ModulePushforwardComparison.singleMapPlusHom` is natural in the functor**,
in the bounded below homotopy category: `singleMapPlusHom Φ M` followed by `τ` placed in degree
zero is the action of `τ` on `M[0]` followed by `singleMapPlusHom Φ' M`. -/
lemma singleMapPlusHom_natTrans (M : A) :
    singleMapPlusHom Φ M ≫ (HomotopyCategory.Plus.singleFunctor B 0).map (τ.app M) =
      (Functor.mapHomotopyCategoryPlusNatTrans τ).app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj M) ≫ singleMapPlusHom Φ' M := by
  refine (HomotopyCategory.Plus.ι B).map_injective ?_
  have h1 (Ψ : A ⥤ B) [Ψ.Additive] : (HomotopyCategory.Plus.ι B).map (singleMapPlusHom Ψ M) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((singleMapHomologicalComplex Ψ (ComplexShape.up ℤ) 0).hom.app M) :=
    (ι_map_singleMapPlusHom Ψ M).trans (mapHomotopyCategorySingleFunctor_hom_app Ψ M)
  have := congrArg (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
    (singleMapHomologicalComplex_hom_app_natTrans Φ Φ' τ (ComplexShape.up ℤ) 0 M)
  rw [Functor.map_comp, Functor.map_comp] at this ⊢
  rw [h1, h1]
  exact this

end Complexes

/-! ### The coherence in `D⁺(ℬ)` -/

section Coherence

variable {A : Type u} {B : Type u₁} [Category.{v} A] [Category.{v₁} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w₁} B]
  (Φ Φ' : A ⥤ B) [Φ.Additive] [Φ'.Additive] (τ : Φ ⟶ Φ')

/-- **`CategoryTheory.Functor.mapSingleFunctorCompQhIso` is natural in the functor.**  The
identification of the image in `D⁺(ℬ)` of `Φ` applied termwise to `M[0]` with `(ΦM)[0]`, followed
by `τ` placed in degree zero, is the degreewise action of `τ` followed by the identification for
`Φ'`. -/
lemma mapSingleFunctorCompQhIso_hom_app_natTrans (M : A) :
    (Functor.mapSingleFunctorCompQhIso Φ).hom.app M ≫
        (DerivedCategory.Plus.singleFunctor B 0).map (τ.app M) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatTrans τ).app
            ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≫
        (Functor.mapSingleFunctorCompQhIso Φ').hom.app M := by
  refine (cancel_mono ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.app
    (Φ'.obj M))).1 ?_
  have hnat : (DerivedCategory.Plus.singleFunctor B 0).map (τ.app M) ≫
      (Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.app (Φ'.obj M) =
      (Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.app (Φ.obj M) ≫
        DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.singleFunctor B 0).map (τ.app M)) :=
    (Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.naturality (τ.app M)
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine (CategoryTheory.whisker_eq _ hnat).trans ?_
  refine Eq.trans ?_ (CategoryTheory.whisker_eq _
    (mapSingleFunctorCompQhIso_hom_app_comp Φ' M)).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (CategoryTheory.eq_whisker (mapSingleFunctorCompQhIso_hom_app_comp Φ M) _).trans ?_
  exact ((DerivedCategory.Plus.Qh.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Plus.Qh.map (singleMapPlusHom_natTrans Φ Φ' τ M)).trans
      (DerivedCategory.Plus.Qh.map_comp _ _)))

/-- The coherence `mapSingleFunctorCompQhIso_hom_app_natTrans` of
`CategoryTheory.Functor.mapSingleFunctorCompQhIso` with a transformation of the functor, in inverse
form. -/
lemma mapSingleFunctorCompQhIso_inv_app_natTrans (M : A) :
    (DerivedCategory.Plus.singleFunctor B 0).map (τ.app M) ≫
        ((Functor.mapSingleFunctorCompQhIso Φ').app M).inv =
      ((Functor.mapSingleFunctorCompQhIso Φ).app M).inv ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatTrans τ).app
            ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) :=
  (CommSq.horiz_inv (f := (Functor.mapSingleFunctorCompQhIso Φ).app M)
    (i := (Functor.mapSingleFunctorCompQhIso Φ').app M)
    ⟨mapSingleFunctorCompQhIso_hom_app_natTrans Φ Φ' τ M⟩).w.symm

end Coherence

/-! ### The naturality of the unit in the functor -/

section Unit

variable {A : Type u} {B : Type u₁} [Category.{v} A] [Category.{v₁} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w₁} B]
  [EnoughInjectives A] (Φ Φ' : A ⥤ B) [Φ.Additive] [Φ'.Additive]

/-- **The unit `Φ(-)[0] ⟶ RΦ((-)[0])` is natural in the functor being derived.**  Let
`τ : Φ ⟶ Φ'` be a transformation of additive functors and let `ρ : RΦ ⟶ RΦ'` be a transformation
of their bounded below right derived functors satisfying the factorization `hρ` that
characterises the derived transformation induced by `τ`, with `σ` the action of `τ` on `K⁺(𝒜)`.
Then `τ` placed in degree zero, followed by the unit of `RΦ'`, is the unit of `RΦ` followed by
`ρ`. -/
lemma singleRightDerivedUnit_fac_app (τ : Φ ⟶ Φ')
    (σ : Φ.mapHomotopyCategoryPlus ⟶ Φ'.mapHomotopyCategoryPlus)
    (ρ : Φ.rightDerivedFunctorPlus ⟶ Φ'.rightDerivedFunctorPlus)
    (hσ : σ = Functor.mapHomotopyCategoryPlusNatTrans τ)
    (hρ : ∀ K : HomotopyCategory.Plus A,
      Φ.rightDerivedFunctorPlusUnith.app K ≫ ρ.app (DerivedCategory.Plus.Qh.obj K) =
        DerivedCategory.Plus.Qh.map (σ.app K) ≫
          Φ'.rightDerivedFunctorPlusUnith.app K)
    (M : A) :
    (DerivedCategory.Plus.singleFunctor B 0).map (τ.app M) ≫
        (singleRightDerivedUnit Φ').app M =
      (singleRightDerivedUnit Φ).app M ≫
        ρ.app ((DerivedCategory.Plus.singleFunctor A 0).obj M) := by
  subst hσ
  have hρM := hρ ((HomotopyCategory.Plus.singleFunctor A 0).obj M)
  have hnatρ : Φ.rightDerivedFunctorPlus.map
        ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M) ≫
      ρ.app ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      ρ.app (DerivedCategory.Plus.Qh.obj
          ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≫
        Φ'.rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M) :=
    ρ.naturality ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M)
  rw [singleRightDerivedUnit_app, singleRightDerivedUnit_app, Category.assoc, Category.assoc,
    hnatρ, ← Category.assoc (Φ.rightDerivedFunctorPlusUnith.app _), hρM, Category.assoc,
    ← Category.assoc ((Functor.mapSingleFunctorCompQhIso Φ).app M).inv]
  exact (Category.assoc _ _ _).symm.trans
    (CategoryTheory.eq_whisker (mapSingleFunctorCompQhIso_inv_app_natTrans Φ Φ' τ M) _)

/-- **The unit is natural in the functor, for an isomorphism of functors**: `e` placed in degree
zero, followed by the unit of `RΦ'`, is the unit of `RΦ` followed by the invariance comparison
`CategoryTheory.Functor.rightDerivedFunctorPlusNatIso e`. -/
theorem singleRightDerivedUnit_natIso_hom_app (e : Φ ≅ Φ') (M : A) :
    (DerivedCategory.Plus.singleFunctor B 0).map (e.hom.app M) ≫
        (singleRightDerivedUnit Φ').app M =
      (singleRightDerivedUnit Φ).app M ≫
        (Functor.rightDerivedFunctorPlusNatIso e).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) :=
  singleRightDerivedUnit_fac_app Φ Φ' e.hom
    (Functor.mapHomotopyCategoryPlusNatIso e).hom
    (Functor.rightDerivedFunctorPlusNatIso e).hom rfl
    (fun K ↦ Functor.rightDerivedFunctorPlusNatIso_hom_fac_app e K) M

/-- The inverse form of `singleRightDerivedUnit_natIso_hom_app`. -/
theorem singleRightDerivedUnit_natIso_inv_app (e : Φ ≅ Φ') (M : A) :
    (DerivedCategory.Plus.singleFunctor B 0).map (e.inv.app M) ≫
        (singleRightDerivedUnit Φ).app M =
      (singleRightDerivedUnit Φ').app M ≫
        (Functor.rightDerivedFunctorPlusNatIso e).inv.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) :=
  singleRightDerivedUnit_fac_app Φ' Φ e.inv
    (Functor.mapHomotopyCategoryPlusNatIso e).inv
    (Functor.rightDerivedFunctorPlusNatIso e).inv rfl
    (fun K ↦ Functor.rightDerivedFunctorPlusNatIso_inv_fac_app e K) M

end Unit

end Stacks.Cohomology

end
