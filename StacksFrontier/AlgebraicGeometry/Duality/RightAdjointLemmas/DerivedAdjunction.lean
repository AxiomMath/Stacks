module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Deriving an adjunction whose left adjoint is exact

Let `G : B ⥤ A` and `F : A ⥤ B` be additive functors between abelian categories with `G ⊣ F`
and `G` exact, and suppose every cochain complex in `A` admits a quasi-isomorphism into a
K-injective complex. Then the functor `G.mapDerivedCategory : D(B) ⥤ D(A)` induced by `G` is
left adjoint to *any* total right derived functor `RF : D(A) ⥤ D(B)` of `F`, by an adjunction
whose unit and counit are the ones induced by those of `G ⊣ F` together with the two
derived-functor comparison maps.

## Main definitions

* `Stacks.DerivedFunctor.derivedAdjunction` is the derived adjunction
  `G.mapDerivedCategory ⊣ RF`.

## Main results

* `Stacks.DerivedFunctor.exists_quasiIso_isKInjective`: a Grothendieck abelian category has
  enough K-injective complexes.
* `Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective`: enough
  K-injectives makes every right derived functor pointwise, which is [Stacks, Tag 070K].
* `Stacks.DerivedFunctor.isRightDerivedFunctor_comp_mapDerivedCategory`: a right derived functor
  followed by the functor induced by an exact functor is again a right derived functor.
* `Stacks.DerivedFunctor.derivedAdjunction_unit_app` and
  `Stacks.DerivedFunctor.derivedAdjunction_counit_app`: the unit and counit of the derived
  adjunction are induced by those of the given adjunction and the comparison maps.

## References

* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.DerivedFunctor

/-! ### Colimits over a diagram whose index category has a terminal object -/

/-- If `L.map` is bijective on morphisms into `I` and `e : L.obj I ≅ Y`, then
`CostructuredArrow.mk e.hom` is a terminal object of the category of costructured arrows
`CostructuredArrow L Y`. -/
noncomputable def terminalCostructuredArrowOfBijective {C D : Type*}
    [Category C] [Category D] (L : C ⥤ D) (Y : D) (I : C) (e : L.obj I ≅ Y)
    (h : ∀ X : C, Function.Bijective (L.map : (X ⟶ I) → (L.obj X ⟶ L.obj I))) :
    IsTerminal (CostructuredArrow.mk e.hom) :=
  IsTerminal.ofUniqueHom
    (fun c ↦ CostructuredArrow.homMk ((h c.left).surjective (c.hom ≫ e.inv)).choose (by
      simp [((h c.left).surjective (c.hom ≫ e.inv)).choose_spec]))
    (fun c m ↦ by
      ext
      refine (h c.left).injective ?_
      apply (cancel_mono e.hom).1
      simpa [((h c.left).surjective (c.hom ≫ e.inv)).choose_spec] using CostructuredArrow.w m)

/-- A cocone over a diagram with terminal index is a colimit as soon as its leg at that index
is an isomorphism. -/
noncomputable def isColimitOfIsoTerminal {J C : Type*} [Category J] [Category C]
    {t : J} (ht : IsTerminal t) (F : J ⥤ C) (c : Cocone F) [IsIso (c.ι.app t)] : IsColimit c :=
  IsColimit.ofIsoColimit (colimitOfDiagramTerminal ht F)
    (Cocone.ext (asIso (c.ι.app t)) fun j ↦ by
      dsimp
      rw [← c.w (ht.from j)])

/-- Every functor preserves a colimit over a diagram whose index category has a terminal
object. -/
theorem preservesColimitOfTerminal {J C D : Type*}
    [Category J] [Category C] [Category D] {t : J}
    (ht : IsTerminal t) (F : J ⥤ C) (H : C ⥤ D) : PreservesColimit F H where
  preserves := fun {c} hc ↦ ⟨by
    have := hc.isIso_ι_app_of_isTerminal t ht
    have : IsIso ((H.mapCocone c).ι.app t) := inferInstanceAs (IsIso (H.map (c.ι.app t)))
    exact isColimitOfIsoTerminal ht (F ⋙ H) (H.mapCocone c)⟩

/-! ### Absoluteness of a right derived functor computed by K-injective resolutions -/

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w} B]

/-- A K-injective resolution of a complex representing `Y` gives a terminal object of the index
category of the colimit computing a pointwise left Kan extension along `DerivedCategory.Qh`
at `Y`. -/
private theorem exists_isTerminal_costructuredArrow
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q)
    (Y : DerivedCategory A) :
    Nonempty (Σ t : CostructuredArrow DerivedCategory.Qh Y, IsTerminal t) := by
  obtain ⟨I, q, hI, hq⟩ := hA (DerivedCategory.Qh.objPreimage Y).as
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map q)) :=
    Localization.inverts _ _ _ ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq)
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ Y :=
    (asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map q))).symm ≪≫
      DerivedCategory.Qh.objObjPreimageIso Y
  exact ⟨⟨CostructuredArrow.mk e.hom,
    terminalCostructuredArrowOfBijective DerivedCategory.Qh Y _ e
      (fun Z => CochainComplex.IsKInjective.Qh_map_bijective Z I)⟩⟩

/-- **Stacks 079P.** In a Grothendieck abelian category every cochain complex admits a
quasi-isomorphism into a K-injective complex, namely the inclusion into its chosen functorial
K-injective resolution. -/
theorem exists_quasiIso_isKInjective {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] (K : CochainComplex A ℤ) :
    ∃ (I : CochainComplex A ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor A).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion A).app K, inferInstance, inferInstance⟩

omit [HasDerivedCategory.{w} A] in
/-- **Stacks 070K.** A functor out of the unbounded homotopy category of an abelian category in
which every complex admits a quasi-isomorphism into a K-injective complex has a pointwise total
right derived functor along the quasi-isomorphisms. -/
theorem hasPointwiseRightDerivedFunctor_of_exists_isKInjective
    {H : Type u₃} [Category.{v₃} H] (Φ : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q) :
    Φ.HasPointwiseRightDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  (Φ.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v₁,
    v₃, v₃, u₁, u₃, u₃} hA).1

/-- **A right derived functor computed by K-injective resolutions is absolute.** If every
cochain complex in `A` admits a quasi-isomorphism into a K-injective complex, then composing a
right derived functor of `F : A ⥤ B` with the functor induced on derived categories by an exact
functor `G : B ⥤ A` again gives a right derived functor. -/
theorem isRightDerivedFunctor_comp_mapDerivedCategory (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q) :
    (RF ⋙ G.mapDerivedCategory).IsRightDerivedFunctor
      (whiskerRight β G.mapDerivedCategory ≫
        (Functor.associator DerivedCategory.Qh RF G.mapDerivedCategory).hom)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have hpoint : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
    hasPointwiseRightDerivedFunctor_of_exists_isKInjective _ hA
  have hpres : G.mapDerivedCategory.PreservesPointwiseLeftKanExtension
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      DerivedCategory.Qh := fun Y => by
    obtain ⟨t, ht⟩ := (exists_isTerminal_costructuredArrow hA Y).some
    have : PreservesColimit (CostructuredArrow.proj DerivedCategory.Qh Y ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
        G.mapDerivedCategory := preservesColimitOfTerminal ht _ _
    infer_instance
  have : HasPointwiseLeftKanExtension DerivedCategory.Qh
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor _
      DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  have : RF.IsLeftKanExtension β :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension RF β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  exact ⟨Functor.PreservesLeftKanExtension.preserves RF β⟩

/-! ### The derived adjunction -/

/-- The functor induced on derived categories by an exact functor is its own left derived
functor, every quasi-isomorphism already being inverted. -/
theorem isLeftDerivedFunctor_mapDerivedCategory (G : B ⥤ A) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ G.mapDerivedCategoryFactorsh

/-- The functor induced on the homotopy categories by an exact functor, followed by the
localization, inverts the quasi-isomorphisms. -/
private theorem isInvertedBy_mapHomotopyCategory_comp_qh (G : B ⥤ A) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).IsInvertedBy
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
  rw [MorphismProperty.IsInvertedBy.iff_of_iso _ G.mapDerivedCategoryFactorsh.symm]
  exact MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh (Localization.inverts _ _) _

/-- The functor induced by an exact functor, followed by any functor on derived categories, is a
left derived functor of the corresponding composite. -/
theorem isLeftDerivedFunctor_mapDerivedCategory_comp (G : B ⥤ A) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (RF : DerivedCategory A ⥤ DerivedCategory B) :
    (G.mapDerivedCategory ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh G.mapDerivedCategory RF).inv ≫
        whiskerRight G.mapDerivedCategoryFactorsh.hom RF)
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) := by
  have := isLeftDerivedFunctor_mapDerivedCategory G
  refine (Functor.isLeftDerivedFunctor_iff_of_inverts _ _
    (MorphismProperty.IsInvertedBy.of_comp _ _
      (isInvertedBy_mapHomotopyCategory_comp_qh G) RF)).2 ?_
  infer_instance

section Adjunction

variable {F : A ⥤ B} [F.Additive] {G : B ⥤ A} [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : G ⊣ F)
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
    I.IsKInjective ∧ QuasiIso q)

include hA

/-- **Stacks 09T5 for derived categories of abelian categories.** Let `G ⊣ F` be an adjunction
of additive functors between abelian categories with `G` exact, and let `RF` be a total right
derived functor of `F` with comparison map `β`. If every cochain complex in the source of `F`
admits a quasi-isomorphism into a K-injective complex, then the functor induced on derived
categories by `G` is left adjoint to `RF`. -/
noncomputable def derivedAdjunction : G.mapDerivedCategory ⊣ RF :=
  have := isLeftDerivedFunctor_mapDerivedCategory G
  have := isLeftDerivedFunctor_mapDerivedCategory_comp G RF
  have := isRightDerivedFunctor_comp_mapDerivedCategory F RF β G hA
  (Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G.mapDerivedCategoryFactorsh.hom β

/-- The unit of the derived adjunction is the one induced by the unit of the given adjunction
and the two derived-functor comparison maps. -/
theorem derivedAdjunction_unit_app (M : HomotopyCategory B (ComplexShape.up ℤ)) :
    (derivedAdjunction adj RF β hA).unit.app (DerivedCategory.Qh.obj M) ≫
        RF.map (G.mapDerivedCategoryFactorsh.hom.app M) =
      DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app M) ≫
        β.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  have := isLeftDerivedFunctor_mapDerivedCategory G
  have := isLeftDerivedFunctor_mapDerivedCategory_comp G RF
  have := isRightDerivedFunctor_comp_mapDerivedCategory F RF β G hA
  (Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) G.mapDerivedCategoryFactorsh.hom β M

/-- The counit of the derived adjunction is the one induced by the counit of the given
adjunction and the two derived-functor comparison maps. -/
theorem derivedAdjunction_counit_app (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    G.mapDerivedCategory.map (β.app K) ≫
        (derivedAdjunction adj RF β hA).counit.app (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).counit.app K) :=
  have := isLeftDerivedFunctor_mapDerivedCategory G
  have := isLeftDerivedFunctor_mapDerivedCategory_comp G RF
  have := isRightDerivedFunctor_comp_mapDerivedCategory F RF β G hA
  (Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G.mapDerivedCategoryFactorsh.hom β K

end Adjunction

end Stacks.DerivedFunctor

end
