module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Recognizing right-derived functors on K-injective complexes

In a Grothendieck abelian category every cochain complex has a K-injective resolution, so a
functor on the homotopy category is determined on the derived category by its values on
K-injective complexes. This module records the three consequences used whenever a derived
functor has to be computed: the unit of a right-derived functor is an isomorphism at a
K-injective complex, a natural transformation of functors on the derived category is an
isomorphism as soon as it is one at every K-injective complex, and a candidate unit which is
an isomorphism at every K-injective complex exhibits its target as the right-derived functor.

## Main results

* `Stacks.Injectives.exists_kInjective_resolution_of_grothendieck`: existence of K-injective
  resolutions, in the form in which the Mathlib criterion consumes it.
* `Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective`.
* `Stacks.Injectives.isIso_natTrans_of_kInjective`.
* `Stacks.Injectives.rightDerived_of_kInjective_units`.
* `Stacks.Injectives.isIso_complexUnit_app`: the same statement for
  `Stacks.Injectives.complexUnit`, the unit read on cochain complexes.

## Implementation notes

Existence of K-injective resolutions is the functorial resolution of
`Stacks.Injectives.kInjectiveResolutionFunctor` evaluated at the complex; only its existence
is used here, and phrasing it as an existential statement is what the Mathlib criterion
`Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective` needs.

`isIso_natTrans_of_kInjective` reduces an arbitrary object of the derived category to a
K-injective complex in two steps: the localization functor is essentially surjective and the
homotopy-category quotient is surjective on objects, so the object is isomorphic to the image
of a cochain complex, and that complex maps quasi-isomorphically to a K-injective one.

A right-derived functor between derived categories is presented by a unit on the homotopy
category of the source, while its consumers work with cochain complexes;
`Stacks.Injectives.complexUnit` transports that unit across
`DerivedCategory.quotientCompQhIso`, and `Stacks.Injectives.complexUnit_app`
records its three factors, which is what lets equalities of composites involving it be proved
in term mode.

`rightDerived_of_kInjective_units` compares the candidate with the total right-derived functor
through `CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc`; both units
are isomorphisms at a K-injective complex, hence so is the comparison, and the previous lemma
upgrades that to an isomorphism of natural transformations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u vH uH vD uD w wD wE

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w, v, u} C]

/-- Every cochain complex in a Grothendieck abelian category admits a K-injective
resolution. -/
theorem exists_kInjective_resolution_of_grothendieck (K : CochainComplex C ℤ) :
    ∃ (I : CochainComplex C ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q :=
  ⟨(kInjectiveResolutionFunctor C).obj K, (kInjectiveResolutionInclusion C).app K,
    inferInstance, inferInstance⟩

variable [HasDerivedCategory.{wD} C] {H : Type uH} [Category.{vH} H]

/-- The unit of a right-derived functor is an isomorphism at a K-injective complex. -/
theorem rightDerivedUnit_isIso_at_kInjective
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H) (RF : DerivedCategory C ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    F (exists_kInjective_resolution_of_grothendieck (C := C))).2 _ RF α I inferInstance

/-- A natural transformation of functors on the derived category is an isomorphism as soon as
it is an isomorphism at every K-injective complex. -/
theorem isIso_natTrans_of_kInjective {F G : DerivedCategory C ⥤ H} (τ : F ⟶ G)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (τ.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)))) : IsIso τ := by
  suffices ∀ K, IsIso (τ.app K) from NatIso.isIso_of_isIso_app τ
  intro K
  rw [← NatTrans.isIso_app_iff_of_iso τ (DerivedCategory.Qh.objObjPreimageIso K)]
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective
    (DerivedCategory.Qh.objPreimage K)
  rw [← hL]
  obtain ⟨I, q, hI, hq⟩ := exists_kInjective_resolution_of_grothendieck (C := C) L
  have hqi : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map q)) := by
    apply Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  rw [NatTrans.isIso_app_iff_of_iso τ (asIso (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map q)))]
  exact h I

/-- A candidate unit which is an isomorphism at every K-injective complex exhibits its target
as the right-derived functor. -/
theorem rightDerived_of_kInjective_units
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H)
    [F.HasRightDerivedFunctor (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (RF : DerivedCategory C ⥤ H) (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I))) :
    RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  let R := F.totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  let β := F.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  rw [Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc R β
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) RF α]
  apply isIso_natTrans_of_kInjective
  intro I _
  have := rightDerivedUnit_isIso_at_kInjective F R β I
  exact (isIso_comp_left_iff (β.app _) _).mp
    (R.rightDerived_fac_app β (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) RF α
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) ▸ h I)

/-! ### The unit of a right-derived functor, read on cochain complexes -/

section ComplexUnit

variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wE} D]

/-- The comparison map of a right derived functor, read on the homotopy category of cochain
complexes rather than on the homotopy category itself. -/
noncomputable def homotopyUnit (F : C ⥤ D) [F.Additive]
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (HomotopyCategory.quotient D (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ RF where
  app K := α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  naturality _ _ f := α.naturality ((HomotopyCategory.quotient _ _).map f)

/-- The comparison map of a right derived functor, transported to the localization of the
cochain complexes. -/
noncomputable def complexUnit (F : C ⥤ D) [F.Additive]
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
  Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso D).inv ≫
    homotopyUnit F RF α ≫ Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).hom RF

omit [IsGrothendieckAbelian.{w, v, u} C] in
/-- The three factors of `complexUnit`, spelled out.  Stating this once is what lets the
compatibility lemmas of its consumers be proved in term mode: the composite mixes
`DerivedCategory.Q.obj K` with `DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)`,
which are definitionally but not syntactically equal. -/
lemma complexUnit_app (F : C ⥤ D) [F.Additive]
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) (K : CochainComplex C ℤ) :
    (complexUnit F RF α).app K =
      (DerivedCategory.quotientCompQhIso D).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
          RF.map ((DerivedCategory.quotientCompQhIso C).hom.app K) :=
  rfl

variable (F : C ⥤ D) [F.Additive] (RF : DerivedCategory C ⥤ DerivedCategory D)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- The complex-level comparison map is invertible at a K-injective complex. -/
lemma isIso_complexUnit_app (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((complexUnit F RF α).app I) := by
  have := rightDerivedUnit_isIso_at_kInjective _ RF α I
  rw [complexUnit_app]
  exact IsIso.comp_isIso' ((DerivedCategory.quotientCompQhIso D).symm.app _).isIso_hom
    (IsIso.comp_isIso' this
      (RF.mapIso ((DerivedCategory.quotientCompQhIso C).app I)).isIso_hom)

end ComplexUnit

end Stacks.Injectives

end
