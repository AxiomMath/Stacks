module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic

/-!
# Global sections along an isomorphism of schemes

Let `c : T ⟶ Z` be an isomorphism of schemes. This file proves that the restriction maps

`Γ(Z, M) ⟶ Γ(T, c⁻¹M)` and `RΓ(Z, M) ⟶ RΓ(T, c⁻¹M)`

on abelian sheaves of the small étale sites, and on their unbounded derived categories, are
isomorphisms: `Stacks.EtaleCohomology.isIso_smallEtaleGlobalSectionsRestrictionAb` and
`Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction`.

The two maps are `Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb` and
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction`, and the second is the
descent of the first along the unit of the derivation of global sections.

## Main definitions

* `Stacks.DerivedFunctor.mapHomotopyCategoryCompositeIdIso` and
  `Stacks.DerivedFunctor.mapDerivedCategoryCompositeIdIso` — for exact functors composing to the
  identity, the identification of the composite of the actions on homotopy categories, resp. on
  unbounded derived categories, with the localization functor.

## Main results

* `Stacks.Sites.isIso_sectionsPullbackComparison` — the comparison map on sections of an
  inverse-image adjunction is an isomorphism as soon as the unit of the adjunction and the
  morphism along which sections are restricted are.
* `Stacks.DerivedFunctor.isEquivalence_mapHomotopyCategory` and
  `Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory` — an exact equivalence of abelian
  categories acts as an equivalence on homotopy categories of cochain complexes and on unbounded
  derived categories.
* `Stacks.DerivedFunctor.isLeftKanExtension_comp_of_equivalence` — a left Kan extension along a
  localization functor remains one after transport along an equivalence of the categories of
  complexes, an equivalence of the localizations, and an isomorphism of the functor being
  extended.
* `Stacks.EtaleCohomology.isEquivalence_smallEtalePullbackAb_of_isIso` — inverse image of
  abelian étale sheaves along an isomorphism of schemes is an equivalence.
* `Stacks.EtaleCohomology.isIso_smallEtaleGlobalSectionsRestrictionAb` — restriction of global
  sections along an isomorphism of schemes is an isomorphism.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction` — restriction of
  unbounded derived global sections along an isomorphism of schemes is an isomorphism.

## References

* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Sites

section

variable {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
  (A : Type*) [Category A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] {P : Sheaf J A ⥤ Sheaf K A}

/-- The comparison map on sections attached to a continuous functor of sites and an
inverse-image/direct-image adjunction is an isomorphism as soon as the unit of the adjunction is
one and the morphism `g` along which sections are restricted is one. -/
theorem isIso_sectionsPullbackComparison (adj : P ⊣ G.sheafPushforwardContinuous A J K)
    {U : C} {V : D} (g : V ⟶ G.obj U) (hunit : IsIso adj.unit) (hg : IsIso g) :
    IsIso (sectionsPullbackComparison G A J K adj g) := by
  have := hunit
  have := hg
  have happ : ∀ F, IsIso ((sectionsPullbackComparison G A J K adj g).app F) := by
    intro F
    rw [sectionsPullbackComparison_app]
    have h1 : IsIso ((sheafToPresheaf J A).map (adj.unit.app F)) := inferInstance
    have h2 : IsIso ((adj.unit.app F).hom) := h1
    have h3 : IsIso ((adj.unit.app F).hom.app (op U)) := by infer_instance
    have h4 : IsIso ((P.obj F).obj.map g.op) := by infer_instance
    exact IsIso.comp_isIso' h3 h4
  exact NatIso.isIso_of_isIso_app _

end

end Stacks.Sites

namespace Stacks.DerivedFunctor

/-! ### An exact equivalence acts as an equivalence on complexes up to homotopy and quasi-iso -/

/-- The action on homotopy categories of an isomorphism of additive functors is an
isomorphism. -/
instance isIso_natTrans_mapHomotopyCategory {V W : Type*} [Category* V] [Preadditive V]
    [Category* W] [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive] (τ : F ⟶ G) [IsIso τ]
    {ι : Type*} (c : ComplexShape ι) : IsIso (NatTrans.mapHomotopyCategory τ c) := by
  refine ⟨NatTrans.mapHomotopyCategory (inv τ) c, ?_, ?_⟩ <;>
    rw [← NatTrans.mapHomotopyCategory_comp] <;> simp

section Equivalences

variable {B C : Type*} [Category* B] [Abelian B] [Category* C] [Abelian C]

/-- For additive functors `F` and `G` whose composite is isomorphic to the identity, the action
of `G` on homotopy categories identifies the quotient functor precomposed with the action of `F`
on cochain complexes with the quotient functor itself. -/
def mapHomotopyCategoryCompositeIdIso (F : B ⥤ C) (G : C ⥤ B) [F.Additive] [G.Additive]
    (e : F ⋙ G ≅ 𝟭 B) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙
      G.mapHomotopyCategory (ComplexShape.up ℤ) ≅
    HomotopyCategory.quotient B (ComplexShape.up ℤ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)) _ ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ _) _ ≪≫
      Functor.leftUnitor _

/-- The action of an additive functor on homotopy categories lifts its action on cochain
complexes through the quotient functor. -/
instance liftingMapHomotopyCategory (F : B ⥤ C) [F.Additive] :
    Localization.Lifting (HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (F.mapHomotopyCategory (ComplexShape.up ℤ)) :=
  ⟨F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)⟩

/-- An additive equivalence of abelian categories acts as an equivalence on the homotopy
categories of cochain complexes. -/
theorem isEquivalence_mapHomotopyCategory (F : B ⥤ C) [F.Additive] [F.IsEquivalence] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ)).IsEquivalence := by
  let G := F.asEquivalence.inverse
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  exact Localization.isEquivalence
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (HomotopyCategory.quotient C (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ))
    _ (F.mapHomotopyCategory (ComplexShape.up ℤ))
    _ (G.mapHomotopyCategory (ComplexShape.up ℤ))
    (mapHomotopyCategoryCompositeIdIso F G F.asEquivalence.unitIso.symm)
    (mapHomotopyCategoryCompositeIdIso G F F.asEquivalence.counitIso)

variable [HasDerivedCategory B] [HasDerivedCategory C]

/-- For exact functors `F` and `G` whose composite is isomorphic to the identity, the action of
`G` on unbounded derived categories identifies the localization functor precomposed with the
action of `F` on cochain complexes with the localization functor itself. -/
def mapDerivedCategoryCompositeIdIso (F : B ⥤ C) (G : C ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ⋙ G ≅ 𝟭 B) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
      G.mapDerivedCategory ≅ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)) _ ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ _) _ ≪≫
      Functor.leftUnitor _

/-- An exact equivalence of abelian categories acts as an equivalence on unbounded derived
categories. -/
theorem isEquivalence_mapDerivedCategory (F : B ⥤ C) [F.Additive] [F.IsEquivalence]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.IsEquivalence := by
  let G := F.asEquivalence.inverse
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have : PreservesFiniteLimits G := inferInstance
  have : PreservesFiniteColimits G := inferInstance
  exact Localization.isEquivalence DerivedCategory.Q
    (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    _ F.mapDerivedCategory _ G.mapDerivedCategory
    (mapDerivedCategoryCompositeIdIso F G F.asEquivalence.unitIso.symm)
    (mapDerivedCategoryCompositeIdIso G F F.asEquivalence.counitIso)

end Equivalences

section

variable {A₁ : Type*} [Category* A₁] [Abelian A₁] [HasDerivedCategory A₁]
  {A₂ : Type*} [Category* A₂] [Abelian A₂] [HasDerivedCategory A₂]
  {A₃ : Type*} [Category* A₃] [Abelian A₃] [HasDerivedCategory A₃]

/-- The degreewise action on homotopy categories of an isomorphism `F ≅ G ⋙ H` of additive
functors is an isomorphism. -/
instance isIso_mapHomotopyCategoryOfComp (F : A₁ ⥤ A₃) [F.Additive] (G : A₁ ⥤ A₂) [G.Additive]
    (H : A₂ ⥤ A₃) [H.Additive] (τ : F ⟶ G ⋙ H) [IsIso τ] :
    IsIso (mapHomotopyCategoryOfComp F G H τ) := by
  unfold mapHomotopyCategoryOfComp
  infer_instance

end

/-! ### Transporting a left Kan extension along equivalences -/

section Transport

variable {C C' D D' H : Type*} [Category* C] [Category* C'] [Category* D]
  [Category* D'] [Category* H]

/-- **Transport of a left Kan extension along equivalences.** Let `Φ : C ⥤ C'` and `G : D ⥤ D'`
be equivalences and let `e : L ⋙ G ≅ Φ ⋙ L'` compare two functors `L : C ⥤ D` and `L' : C' ⥤ D'`
through them. If `RF` is a left Kan extension of `Ft` along `L'`, and `Fz ≅ Φ ⋙ Ft`, then
`G ⋙ RF` is a left Kan extension of `Fz` along `L`, for the transformation obtained by
transporting the unit; any transformation equal to that one is a left Kan extension unit as well.
-/
theorem isLeftKanExtension_comp_of_equivalence
    {Φ : C ⥤ C'} [Φ.IsEquivalence] {L : C ⥤ D} {L' : C' ⥤ D'} {G : D ⥤ D'}
    [G.IsEquivalence] (e : L ⋙ G ≅ Φ ⋙ L') {Ft : C' ⥤ H} {Fz : C ⥤ H} {RF : D' ⥤ H}
    (αt : Ft ⟶ L' ⋙ RF) [RF.IsLeftKanExtension αt] (eF : Fz ≅ Φ ⋙ Ft)
    (β : Fz ⟶ L ⋙ (G ⋙ RF))
    (hβ : (eF.hom ≫ Functor.whiskerLeft Φ αt ≫ (Functor.associator Φ L' RF).inv) ≫
        Functor.whiskerRight e.inv RF ≫ (Functor.associator L G RF).hom = β) :
    (G ⋙ RF).IsLeftKanExtension β := by
  subst hβ
  have h1 : RF.IsLeftKanExtension
      (Functor.whiskerLeft Φ αt ≫ (Functor.associator Φ L' RF).inv) :=
    (Functor.isLeftKanExtension_iff_precomp RF Φ αt).mp ‹_›
  have h2 : RF.IsLeftKanExtension
      (eF.hom ≫ (Functor.whiskerLeft Φ αt ≫ (Functor.associator Φ L' RF).inv)) :=
    (Functor.isLeftKanExtension_iff_of_iso₂ _ _ eF.symm (Iso.refl RF) (by simp)).mp h1
  exact (Functor.isLeftKanExtension_iff_postcomp₁ G e _).mp h2

end Transport

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

/-! ### Inverse image along an isomorphism of schemes -/

section Underived

variable {T Z : Scheme.{u}} (c : T ⟶ Z) [IsIso c]

/-- Base change along an isomorphism of schemes exhibits the small étale site of the target as a
dense subsite of the small étale site of the source. -/
theorem isDenseSubsite_smallEtaleBaseChange_of_isIso :
    (smallEtaleBaseChange c).IsDenseSubsite (smallEtaleTopology Z) (smallEtaleTopology T) :=
  have := AlgebraicGeometry.universalHomeomorphism_of_isIso c
  isDenseSubsite_of_universalHomeomorphism c

/-- Direct image of abelian sheaves along an isomorphism of schemes is an equivalence of the
small étale topoi. -/
theorem isEquivalence_smallEtalePushforwardAb_of_isIso :
    (smallEtalePushforwardAb c).IsEquivalence :=
  have := isDenseSubsite_smallEtaleBaseChange_of_isIso c
  inferInstanceAs
    ((smallEtaleBaseChange c).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology Z) (smallEtaleTopology T)).IsEquivalence

/-- Inverse image of abelian sheaves along an isomorphism of schemes is an equivalence of the
small étale topoi. -/
theorem isEquivalence_smallEtalePullbackAb_of_isIso :
    (smallEtalePullbackAb c).IsEquivalence := by
  have h := isEquivalence_smallEtalePushforwardAb_of_isIso c
  have e : smallEtalePullbackAb c ≅ (smallEtalePushforwardAb c).inv :=
    Adjunction.leftAdjointUniq (smallEtaleAdjunctionAb c)
      (smallEtalePushforwardAb c).asEquivalence.symm.toAdjunction
  exact Functor.isEquivalence_of_iso e.symm

/-- The unit of the inverse-image/direct-image adjunction along an isomorphism of schemes is an
isomorphism. -/
instance isIso_smallEtaleAdjunctionAb_unit_of_isIso :
    IsIso (smallEtaleAdjunctionAb c).unit :=
  have := isEquivalence_smallEtalePullbackAb_of_isIso c
  have : (smallEtalePullbackAb c).Full := inferInstance
  have : (smallEtalePullbackAb c).Faithful := inferInstance
  inferInstance

omit [IsIso c] in
/-- The morphism of small étale sites of `T` from the identity object to the base change along an
isomorphism `c : T ⟶ Z` of the identity object of `Z` is an isomorphism. -/
theorem isIso_smallEtaleBaseChangeLift_mkId :
    IsIso (smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 Z)) c (Category.comp_id c)) := by
  have h2 : IsIso (((smallEtaleBaseChange c).obj (Scheme.Etale.mk (𝟙 Z))).hom) := by
    change IsIso (pullback.snd (𝟙 Z) c)
    infer_instance
  have ht2 : IsTerminal ((smallEtaleBaseChange c).obj (Scheme.Etale.mk (𝟙 Z))) :=
    isTerminalOfIsIsoHom _
  have ht1 : IsTerminal (Scheme.Etale.mk (𝟙 T)) := isTerminalEtaleMkId T
  have he : smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 Z)) c (Category.comp_id c) =
      (ht1.uniqueUpToIso ht2).hom := ht2.hom_ext _ _
  rw [he]
  infer_instance

/-- Restriction of sections over the identity object of the small étale site of `Z` to global
sections of the inverse image along an isomorphism `c : T ⟶ Z` is an isomorphism. -/
theorem isIso_smallEtaleSectionsPullbackAb_mkId :
    IsIso (smallEtaleSectionsPullbackAb c (Scheme.Etale.mk (𝟙 Z)) c (Category.comp_id c)) := by
  have h1 := isIso_smallEtaleBaseChangeLift_mkId c
  have h2 := Stacks.Sites.isIso_sectionsPullbackComparison (smallEtaleBaseChange c) Ab.{u + 1}
    (smallEtaleTopology Z) (smallEtaleTopology T) (smallEtaleAdjunctionAb c)
    (smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 Z)) c (Category.comp_id c))
    (isIso_smallEtaleAdjunctionAb_unit_of_isIso c) h1
  have h3 : IsIso (Functor.whiskerLeft (smallEtalePullbackAb c)
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
        (isTerminalEtaleMkId T)).inv) := by infer_instance
  unfold smallEtaleSectionsPullbackAb
  exact IsIso.comp_isIso' h2 h3

/-- **Restriction of global sections along an isomorphism of schemes is an isomorphism.** For an
isomorphism `c : T ⟶ Z` of schemes the canonical map `Γ(Z, M) ⟶ Γ(T, c⁻¹M)` on abelian sheaves of
the small étale sites is an isomorphism, naturally in `M`. -/
instance isIso_smallEtaleGlobalSectionsRestrictionAb :
    IsIso (smallEtaleGlobalSectionsRestrictionAb c) := by
  have h2 := isIso_smallEtaleSectionsPullbackAb_mkId c
  unfold smallEtaleGlobalSectionsRestrictionAb
  exact IsIso.comp_isIso' inferInstance h2

end Underived

/-! ### Derived global sections along an isomorphism of schemes -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {T Z : Scheme.{u}} (c : T ⟶ Z) [IsIso c]
  [((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]

omit [((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ))] in
/-- For an isomorphism `c : T ⟶ Z` of schemes, the unbounded derived global sections on `T` of
the unbounded derived inverse image along `c` are a right derived functor of degreewise global
sections on `Z`, for the comparison that
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction` is descended from. -/
theorem isRightDerivedFunctor_smallEtaleDerivedPullbackAb_comp :
    (smallEtaleDerivedPullbackAb c ⋙ smallEtaleDerivedGlobalSections T).IsRightDerivedFunctor
      (Stacks.DerivedFunctor.exactDerivedDescUnit
        (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) (smallEtalePullbackAb c)
        (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) (smallEtaleDerivedGlobalSections T)
        (smallEtaleDerivedGlobalSectionsUnit T) (smallEtaleGlobalSectionsRestrictionAb c))
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) := by
  have hΦ : (smallEtalePullbackAb c).IsEquivalence :=
    isEquivalence_smallEtalePullbackAb_of_isIso c
  have hΦh : ((smallEtalePullbackAb c).mapHomotopyCategory
      (ComplexShape.up ℤ)).IsEquivalence :=
    Stacks.DerivedFunctor.isEquivalence_mapHomotopyCategory _
  have hRΦ : (smallEtalePullbackAb c).mapDerivedCategory.IsEquivalence :=
    Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory _
  have hm : IsIso (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
      (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) (smallEtalePullbackAb c)
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
      (smallEtaleGlobalSectionsRestrictionAb c)) := inferInstance
  have hT : (smallEtaleDerivedGlobalSections T).IsLeftKanExtension
      (smallEtaleDerivedGlobalSectionsUnit T) := by
    rw [← Functor.isRightDerivedFunctor_iff_isLeftKanExtension
      (W := HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]
    infer_instance
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  refine Stacks.DerivedFunctor.isLeftKanExtension_comp_of_equivalence
    (smallEtalePullbackAb c).mapDerivedCategoryFactorsh
    (smallEtaleDerivedGlobalSectionsUnit T)
    (Functor.isoWhiskerRight (asIso (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
        (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) (smallEtalePullbackAb c)
        (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
        (smallEtaleGlobalSectionsRestrictionAb c))) DerivedCategory.Qh ≪≫
      Functor.associator _ _ _) _ ?_
  simp [Stacks.DerivedFunctor.exactDerivedDescUnit]

/-- **Restriction of unbounded derived global sections along an isomorphism of schemes is an
isomorphism.** For an isomorphism `c : T ⟶ Z` of schemes the canonical map
`RΓ(Z, M) ⟶ RΓ(T, c⁻¹M)` on unbounded derived categories of abelian sheaves of the small étale
sites is an isomorphism, naturally in `M`. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction :
    IsIso (smallEtaleDerivedGlobalSectionsRestriction c) :=
  have := isRightDerivedFunctor_smallEtaleDerivedPullbackAb_comp c
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (smallEtaleDerivedGlobalSections Z) (smallEtaleDerivedGlobalSectionsUnit Z)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) _ _).mp this

end Derived

end Stacks.EtaleCohomology

end
