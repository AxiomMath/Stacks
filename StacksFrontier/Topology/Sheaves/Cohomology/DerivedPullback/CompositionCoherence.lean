module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DerivedPullbackUnitLawsOfRingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeCompositionOnRingedTopoi
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphismGeneral

/-!
# Coherence of the composition isomorphisms of derived pullback, at any model

For morphisms of ringed spaces, the composition isomorphisms
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` of Stacks 0D5S satisfy the
cocycle identity. With the unit isomorphism
`Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIsoGeneral`, they also satisfy both
unit laws. These hold for every choice of models of the derived categories involved.

## Main results

* `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical_hom_assoc`: the cocycle
  identity.
* `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical_hom_id_comp` and
  `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical_hom_comp_id`: the unit laws.

## Implementation notes

Each identity is transported from the corresponding degreewise identity through the universal
property of the left derived functor on its target, which needs no resolution. The cocycle
transport is `Stacks.Cohomology.DerivedBaseChangeComposition.leftDerived_comparison_assoc`. The
unit transports are `leftDerived_comparison_id_comp` and `leftDerived_comparison_comp_id` below.
The degreewise identities are `CategoryTheory.Adjunction.leftAdjointCompIso_assoc` and its unit
companions, applied to the pushforward isomorphisms, whose components are identities.

The statements at `HasDerivedCategory.standard` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity` are read
off from these, after identifying the unit isomorphism used there with
`Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIsoGeneral`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

namespace Stacks.DerivedPullback.Composition

universe w₁ w₂ w₃ w₄ u

noncomputable section

/-! ### Unit laws for left derived functors -/

section Abstract

variable {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
  {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {F₀₁ : C₀ ⥤ C₁} {L₀₁ : D₀ ⥤ D₁}
  (α₀₁ : Q₀ ⋙ L₀₁ ⟶ F₀₁ ⋙ Q₁)

/-- **The left unit law, transported through the universal property of a left derived
functor.** If a comparison `L₀₁ ⋙ L₁₁ ⟶ L₀₁` is induced by a degreewise one which is the
whiskering of a unit `I₁ ⟶ 𝟭`, and `ι : L₁₁ ⟶ 𝟭` is induced by that unit, then the comparison
is the whiskering of `ι`. -/
theorem leftDerived_comparison_id_comp (W : MorphismProperty C₀) [Q₀.IsLocalization W]
    [L₀₁.IsLeftDerivedFunctor α₀₁ W] {I₁ : C₁ ⥤ C₁} {L₁₁ : D₁ ⥤ D₁}
    (α₁₁ : Q₁ ⋙ L₁₁ ⟶ I₁ ⋙ Q₁) (c : F₀₁ ⋙ I₁ ⟶ F₀₁) (d : L₀₁ ⋙ L₁₁ ⟶ L₀₁)
    (fac : ∀ M, d.app (Q₀.obj M) ≫ α₀₁.app M =
      L₁₁.map (α₀₁.app M) ≫ α₁₁.app (F₀₁.obj M) ≫ Q₁.map (c.app M))
    (ι : L₁₁ ⟶ 𝟭 D₁) (p : I₁ ⟶ 𝟭 C₁) (hι : ∀ N, ι.app (Q₁.obj N) = α₁₁.app N ≫ Q₁.map (p.app N))
    (hc : ∀ M, c.app M = p.app (F₀₁.obj M)) :
    d = Functor.whiskerLeft L₀₁ ι ≫ (Functor.rightUnitor L₀₁).hom := by
  apply L₀₁.leftDerived_ext α₀₁ W
  ext M
  have h := ι.naturality (α₀₁.app M)
  dsimp at h ⊢
  rw [fac, Category.comp_id, ← h, hι, hc]

/-- **The right unit law, transported through the universal property of a left derived
functor**, the counterpart of `leftDerived_comparison_id_comp` for a unit on the source. -/
theorem leftDerived_comparison_comp_id (W : MorphismProperty C₀) [Q₀.IsLocalization W]
    [L₀₁.IsLeftDerivedFunctor α₀₁ W] {I₀ : C₀ ⥤ C₀} {L₀₀ : D₀ ⥤ D₀}
    (α₀₀ : Q₀ ⋙ L₀₀ ⟶ I₀ ⋙ Q₀) (c : I₀ ⋙ F₀₁ ⟶ F₀₁) (d : L₀₀ ⋙ L₀₁ ⟶ L₀₁)
    (fac : ∀ M, d.app (Q₀.obj M) ≫ α₀₁.app M =
      L₀₁.map (α₀₀.app M) ≫ α₀₁.app (I₀.obj M) ≫ Q₁.map (c.app M))
    (ι : L₀₀ ⟶ 𝟭 D₀) (p : I₀ ⟶ 𝟭 C₀) (hι : ∀ N, ι.app (Q₀.obj N) = α₀₀.app N ≫ Q₀.map (p.app N))
    (hc : ∀ M, c.app M = F₀₁.map (p.app M)) :
    d = Functor.whiskerRight ι L₀₁ ≫ (Functor.leftUnitor L₀₁).hom := by
  apply L₀₁.leftDerived_ext α₀₁ W
  ext M
  have h := α₀₁.naturality (p.app M)
  dsimp at h ⊢
  rw [fac, Category.comp_id, hι, Functor.map_comp, Category.assoc, h, hc]

end Abstract

/-! ### Unit isomorphisms on homotopy categories -/

section HomotopyUnit

open Stacks.Cohomology.DerivedPullbackAlongIso

variable {ι : Type*} {V : Type*} [Category* V] [Preadditive V] {V' : Type*} [Category* V']
  [Preadditive V'] (c : ComplexShape ι)

/-- The unit isomorphism `(𝟭 V).mapHomotopyCategory ≅ 𝟭` at an object is the class of the
degreewise unit isomorphism. -/
theorem mapHomotopyCategoryIdIso_hom_app (V : Type*) [Category* V] [Preadditive V]
    (K : HomologicalComplex V c) :
    (mapHomotopyCategoryIdIso V c).hom.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient V c).map ((Functor.mapHomologicalComplexIdIso V c).hom.app K) := by
  have h : ((𝟭 V).mapHomotopyCategoryFactors c ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso V c)
        (HomotopyCategory.quotient V c) ≪≫
      (HomotopyCategory.quotient V c).leftUnitor ≪≫
        (HomotopyCategory.quotient V c).rightUnitor.symm).hom.app K =
      (HomotopyCategory.quotient V c).map ((Functor.mapHomologicalComplexIdIso V c).hom.app K) := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.symm_hom,
      Functor.rightUnitor_inv_app, Category.comp_id]
    dsimp only [Functor.mapHomotopyCategoryFactors]
    rw [Quotient.lift.isLift_hom]
    exact (Category.id_comp _).trans (Category.comp_id _)
  exact h

/-- On homotopy categories, the compositor of `G` with a unit `I ≅ 𝟭` whiskered on the left is
the unit at the image of `G`. -/
theorem mapHomotopyCategoryCompIso_whiskerLeft_hom_app (G : V ⥤ V') {I : V' ⥤ V'} [G.Additive]
    [I.Additive] (e : I ≅ 𝟭 V') (M : HomotopyCategory V c) :
    (Functor.mapHomotopyCategoryCompIso (Functor.isoWhiskerLeft G e ≪≫ Functor.rightUnitor G)
        c).hom.app M =
      (mapHomotopyCategoryIso e c ≪≫ mapHomotopyCategoryIdIso V' c).hom.app
        ((G.mapHomotopyCategory c).obj M) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  show (HomotopyCategory.quotient V' c).map
      ((Functor.mapHomologicalComplexCompIso (Functor.isoWhiskerLeft G e ≪≫ Functor.rightUnitor G)
        c).hom.app M) =
    (HomotopyCategory.quotient V' c).map
      ((NatTrans.mapHomologicalComplex e.hom c).app ((G.mapHomologicalComplex c).obj M)) ≫
      (mapHomotopyCategoryIdIso V' c).hom.app
        ((HomotopyCategory.quotient V' c).obj ((G.mapHomologicalComplex c).obj M))
  rw [mapHomotopyCategoryIdIso_hom_app, ← Functor.map_comp]
  congr 1

/-- On homotopy categories, the compositor of a unit `I ≅ 𝟭` whiskered on the right with `G` is
the image under `G` of the unit. -/
theorem mapHomotopyCategoryCompIso_whiskerRight_hom_app (G : V ⥤ V') {I : V ⥤ V} [G.Additive]
    [I.Additive] (e : I ≅ 𝟭 V) (M : HomotopyCategory V c) :
    (Functor.mapHomotopyCategoryCompIso (Functor.isoWhiskerRight e G ≪≫ Functor.leftUnitor G)
        c).hom.app M =
      (G.mapHomotopyCategory c).map
        ((mapHomotopyCategoryIso e c ≪≫ mapHomotopyCategoryIdIso V c).hom.app M) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  show (HomotopyCategory.quotient V' c).map
      ((Functor.mapHomologicalComplexCompIso (Functor.isoWhiskerRight e G ≪≫ Functor.leftUnitor G)
        c).hom.app M) =
    (G.mapHomotopyCategory c).map
      ((HomotopyCategory.quotient V c).map ((NatTrans.mapHomologicalComplex e.hom c).app M) ≫
        (mapHomotopyCategoryIdIso V c).hom.app ((HomotopyCategory.quotient V c).obj M))
  rw [mapHomotopyCategoryIdIso_hom_app, ← Functor.map_comp, Functor.mapHomotopyCategory_map]
  congr 1
  ext n
  simp

end HomotopyUnit

/-! ### Degreewise coherence -/

section Degreewise

variable {X Y Z W : RingedSpace.{u, u}}

/-- The cocycle identity for the pullback-composition isomorphism of sheaves of modules. -/
theorem modulePullbackComp_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Functor.isoWhiskerLeft (modulePullback h) (modulePullbackComp f g) ≪≫
        modulePullbackComp (f ≫ g) h =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (modulePullbackComp g h) (modulePullback f) ≪≫
          modulePullbackComp f (g ≫ h) :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (by ext; rfl)

/-- The cocycle identity for the pullback-composition isomorphism on homotopy categories. -/
theorem pullbackOnHomotopyCompIso_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Functor.whiskerLeft ((modulePullback h).mapHomotopyCategory (ComplexShape.up ℤ))
          (pullbackOnHomotopyCompIso f g).hom ≫
        (pullbackOnHomotopyCompIso (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (pullbackOnHomotopyCompIso g h).hom
          ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)) ≫
        (pullbackOnHomotopyCompIso f (g ≫ h)).hom :=
  Stacks.Cohomology.DerivedBaseChangeComposition.mapHomotopyCategoryCompIso_assoc _ _ _ _
    (congrArg Iso.hom (modulePullbackComp_assoc f g h)) (ComplexShape.up ℤ)

end Degreewise

/-! ### The cocycle identity at any model -/

section Assoc

variable {X Y Z W : RingedSpace.{u, u}}
  [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
  [HasDerivedCategory.{w₃} (ModuleSheaves Z)] [HasDerivedCategory.{w₄} (ModuleSheaves W)]

/-- The composition isomorphism of Stacks 0D5S at a complex, followed by the comparison for
`L(f ≫ g)^*`: the comparison for `Lg^*`, then the one for `Lf^*`, then the degreewise
compositor, at any model of the three derived categories. -/
theorem derivedPullbackCompIsoCanonical_hom_app_Qh_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ)) :
    (derivedPullbackCompIsoCanonical f g).hom.app (DerivedCategory.Qh.obj K) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
          (f ≫ g)).app K =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g).app K) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
          (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f g).hom.app K) :=
  (Functor.leftDerived_fac_app
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f ≫ g))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (f ≫ g))
      (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (derivedPullbackCompCounit f g
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g)) K).trans
    (derivedPullbackCompCounit_app f g
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g) K)

/-- **The cocycle identity of Stacks 0D5S at any model.** For three composable morphisms of
ringed spaces the two identifications of `Lh^* ⋙ Lg^* ⋙ Lf^*` with `L(f ≫ g ≫ h)^*` agree. -/
theorem derivedPullbackCompIsoCanonical_hom_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Functor.whiskerLeft (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h)
          (derivedPullbackCompIsoCanonical f g).hom ≫
        (derivedPullbackCompIsoCanonical (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedPullbackCompIsoCanonical g h).hom
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ≫
        (derivedPullbackCompIsoCanonical f (g ≫ h)).hom :=
  Stacks.Cohomology.DerivedBaseChangeComposition.leftDerived_comparison_assoc
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison h)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (g ≫ h))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (f ≫ g))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (f ≫ g ≫ h))
    (HomotopyCategory.quasiIso (ModuleSheaves W) (ComplexShape.up ℤ))
    (pullbackOnHomotopyCompIso g h).hom (pullbackOnHomotopyCompIso f g).hom
    (pullbackOnHomotopyCompIso (f ≫ g) h).hom (pullbackOnHomotopyCompIso f (g ≫ h)).hom
    (derivedPullbackCompIsoCanonical g h).hom (derivedPullbackCompIsoCanonical f g).hom
    (derivedPullbackCompIsoCanonical (f ≫ g) h).hom (derivedPullbackCompIsoCanonical f (g ≫ h)).hom
    (derivedPullbackCompIsoCanonical_hom_app_Qh_comp g h)
    (derivedPullbackCompIsoCanonical_hom_app_Qh_comp f g)
    (derivedPullbackCompIsoCanonical_hom_app_Qh_comp (f ≫ g) h)
    (derivedPullbackCompIsoCanonical_hom_app_Qh_comp f (g ≫ h))
    (pullbackOnHomotopyCompIso_assoc f g h)

end Assoc

/-! ### The unit laws at any model -/

section Unit

open Stacks.Cohomology.DerivedPullbackAlongIso

variable {X Y Z : RingedSpace.{u, u}}

/-- The unit isomorphism `L(𝟙 Y)^* ≅ 𝟭` at a complex: the comparison for `L(𝟙 Y)^*`, followed by
the degreewise unit isomorphism. -/
theorem derivedPullbackIdIso_hom_app_Qh (Y : RingedSpace.{u, u})
    [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
    (N : HomotopyCategory (ModuleSheaves Y) (ComplexShape.up ℤ)) :
    (derivedPullbackIdIsoGeneral Y).hom.app (DerivedCategory.Qh.obj N) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (𝟙 Y)).app N ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryIso (modulePullbackId Y) (ComplexShape.up ℤ) ≪≫
          mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)).hom.app N) := by
  have : (𝟭 (DerivedCategory (ModuleSheaves Y))).IsLeftDerivedFunctor
      (pullbackOnHomotopyIdIsoGeneral Y).hom
      (HomotopyCategory.quasiIso (ModuleSheaves Y) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ (pullbackOnHomotopyIdIsoGeneral Y)
  have h := Functor.leftDerivedNatTrans_app
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (𝟙 Y))
    (𝟭 (DerivedCategory (ModuleSheaves Y)))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (𝟙 Y))
    (pullbackOnHomotopyIdIsoGeneral Y).hom
    (HomotopyCategory.quasiIso (ModuleSheaves Y) (ComplexShape.up ℤ)) (𝟙 _) N
  rw [← cancel_mono ((pullbackOnHomotopyIdIsoGeneral Y).hom.app N)]
  refine h.trans ?_
  simp [pullbackOnHomotopyIdIsoGeneral]

variable [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
  [HasDerivedCategory.{w₃} (ModuleSheaves Z)]

/-- **The left unit law of Stacks 0D5S at any model**: identifying `Lg^* ⋙ L(𝟙 Y)^*` with
`L(𝟙 Y ≫ g)^* = Lg^*` is the unit isomorphism of `L(𝟙 Y)^*` whiskered by `Lg^*`. -/
theorem derivedPullbackCompIsoCanonical_hom_id_comp (g : Y ⟶ Z) :
    (derivedPullbackCompIsoCanonical (𝟙 Y) g).hom =
      Functor.whiskerLeft (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
          (derivedPullbackIdIsoGeneral Y).hom ≫
        (Functor.rightUnitor _).hom :=
  leftDerived_comparison_id_comp
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g)
    (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (𝟙 Y))
    (pullbackOnHomotopyCompIso (𝟙 Y) g).hom (derivedPullbackCompIsoCanonical (𝟙 Y) g).hom
    (derivedPullbackCompIsoCanonical_hom_app_Qh_comp (𝟙 Y) g) (derivedPullbackIdIsoGeneral Y).hom
    (mapHomotopyCategoryIso (modulePullbackId Y) (ComplexShape.up ℤ) ≪≫
      mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)).hom
    (derivedPullbackIdIso_hom_app_Qh Y) (fun M => by
      dsimp only [pullbackOnHomotopyCompIso]
      rw [modulePullbackComp_id_comp]
      exact mapHomotopyCategoryCompIso_whiskerLeft_hom_app _ _ _ M)

/-- **The right unit law of Stacks 0D5S at any model**: identifying `L(𝟙 Y)^* ⋙ Lf^*` with
`L(f ≫ 𝟙 Y)^* = Lf^*` is `Lf^*` of the unit isomorphism of `L(𝟙 Y)^*`. -/
theorem derivedPullbackCompIsoCanonical_hom_comp_id (f : X ⟶ Y) :
    (derivedPullbackCompIsoCanonical f (𝟙 Y)).hom =
      Functor.whiskerRight (derivedPullbackIdIsoGeneral Y).hom
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ≫
        (Functor.leftUnitor _).hom :=
  leftDerived_comparison_comp_id
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
    (HomotopyCategory.quasiIso (ModuleSheaves Y) (ComplexShape.up ℤ))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (𝟙 Y))
    (pullbackOnHomotopyCompIso f (𝟙 Y)).hom (derivedPullbackCompIsoCanonical f (𝟙 Y)).hom
    (derivedPullbackCompIsoCanonical_hom_app_Qh_comp f (𝟙 Y)) (derivedPullbackIdIsoGeneral Y).hom
    (mapHomotopyCategoryIso (modulePullbackId Y) (ComplexShape.up ℤ) ≪≫
      mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)).hom
    (derivedPullbackIdIso_hom_app_Qh Y) (fun M => by
      dsimp only [pullbackOnHomotopyCompIso]
      rw [modulePullbackComp_comp_id]
      exact mapHomotopyCategoryCompIso_whiskerRight_hom_app _ _ _ M)

end Unit

end

end Stacks.DerivedPullback.Composition
