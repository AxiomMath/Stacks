module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCompositeSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingleComp
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# The pullback map on cohomology along a composite

Let `G' : X'' ⟶ X'` and `G : X' ⟶ X` be morphisms of ringed spaces. The pullback map
`pullbackHgroup` of [Stacks, Tag 01F9], built from the canonical comparisons of
[Stacks, Tag 01F8] and [Stacks, Tag 01EZ], is functorial: for a `G`-map `φ : ℳ ⟶ G_*ℳ'` and a
`G'`-map `φ' : ℳ' ⟶ G'_*ℳ''`, the pullback map of the `(G' ≫ G)`-map `φ ≫ G_*φ'` is the pullback
map of `φ` followed by that of `φ'`.

## Main results

* `Stacks.DeRham.GysinCohomologyBaseChange.lerayComparisonAb_comp`: the Leray comparison in
  `D(Ab)` is compatible with the composition isomorphism `RG'_* ⋙ RG_* ≅ R(G' ≫ G)_*` of
  [Stacks, Tag 0D5T].
* `Stacks.DeRham.GysinCohomologyBaseChange.singleToDerivedPushforward_comp`: so is the
  comparison of [Stacks, Tag 01F8].
* `Stacks.DeRham.GysinCohomologyBaseChange.lerayComparisonAb_id_app`,
  `Stacks.DeRham.GysinCohomologyBaseChange.singleToDerivedPushforward_id_app`: both comparisons
  along the identity are the unit isomorphism `R(𝟙 X)_* ≅ 𝟭`.
* `Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup_canonical_comp`: **the pullback map
  along a composite is the composite of the pullback maps.**
* `Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup_canonical_id`,
  `Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup_canonical_of_eq_id`: **the pullback map
  along the identity is the map induced on cohomology.**

## Implementation notes

The pullback map is built in the standard model of the derived category, as is the composition
isomorphism of derived pushforwards; the file opens the scope `Stacks.StandardDerivedModel`.
Both comparisons out of a right derived functor are pinned down by its universal property
(`rightDerived_ext`), and the remaining identities are checked degreewise. The longer chases are
carried out by small lemmas at variables: run directly on the ringed-space functors, a single
rewrite exhausts the heartbeat budget on an `isDefEq` check between two spellings of the same
object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.CohomologicalGysin
open scoped Stacks.StandardDerivedModel

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

variable {X X' X'' : RingedSpace.{u, u}} (G' : X'' ⟶ X') (G : X' ⟶ X)

/-- The equation characterizing the Leray comparison in `D(Ab)`, pointwise: its composite with
the unit of `RΓ(X', -)` is the Leray unit. -/
@[reassoc]
theorem lerayComparisonAb_fac_app (K : HomotopyCategory (RModules X') (ComplexShape.up ℤ)) :
    (derivedGlobalSectionsUnit X').app K ≫ (lerayComparisonAb G).app (DerivedCategory.Qh.obj K) =
      (lerayUnitAb G).app K :=
  (derivedGlobalSections X').rightDerived_fac_app (derivedGlobalSectionsUnit X')
    (HomotopyCategory.quasiIso (RModules X') (ComplexShape.up ℤ)) _ (lerayUnitAb G) K

/-- The Leray unit in `D(Ab)`, pointwise. -/
theorem lerayUnitAb_app (K : HomotopyCategory (RModules X') (ComplexShape.up ℤ)) :
    (lerayUnitAb G).app K =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso G)
          (ComplexShape.up ℤ)).inv.app K) ≫
        (derivedGlobalSectionsUnit X).app
          (((modulePushforward G).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (derivedGlobalSections X).map ((derivedPushforwardUnit G).app K) := by
  simp only [lerayUnitAb, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]

/-- The algebra of `lerayComparisonAb_comp`, at variables. -/
private lemma leray_comp_chase {C : Type*} [Category* C] {A P Q R S T P' Q' R' P'' : C}
    (a₁ : A ⟶ P) (u₁ : P ⟶ Q) (rm : Q ⟶ R) (rη : R ⟶ S) (rr : S ⟶ T) (a₂ : A ⟶ P')
    (u₂ : P' ⟶ Q') (re : Q' ⟶ R') (lc : R' ⟶ T) (lc₀ : Q' ⟶ S) (lu : P' ⟶ S)
    (c₀ : P' ⟶ P'') (u₃ : P'' ⟶ R) (gm : P ⟶ P'')
    (f₁ : re ≫ lc = lc₀ ≫ rr) (f₂ : u₂ ≫ lc₀ = lu) (f₃ : lu = c₀ ≫ u₃ ≫ rη)
    (f₄ : u₁ ≫ rm = gm ≫ u₃) (f₅ : a₁ ≫ gm = a₂ ≫ c₀) :
    a₁ ≫ u₁ ≫ rm ≫ rη ≫ rr = a₂ ≫ u₂ ≫ re ≫ lc := by
  rw [f₁, reassoc_of% f₂, f₃, reassoc_of% f₄, reassoc_of% f₅]
  simp only [Category.assoc]

/-- **The Leray comparison in `D(Ab)` along a composite.** For `G' : X'' ⟶ X'` and `G : X' ⟶ X`,
the Leray comparison for `G' ≫ G` followed by the composition isomorphism
`R(G' ≫ G)_* ≅ RG'_* ⋙ RG_*` is the Leray comparison for `G'` followed by that for `G`. -/
theorem lerayComparisonAb_comp :
    lerayComparisonAb (G' ≫ G) ≫
        Functor.whiskerRight (derivedPushforwardCompIso G' G).inv (derivedGlobalSections X) =
      lerayComparisonAb G' ≫
        Functor.whiskerLeft (derivedPushforward G') (lerayComparisonAb G) := by
  apply (derivedGlobalSections X'').rightDerived_ext (derivedGlobalSectionsUnit X'')
    (HomotopyCategory.quasiIso (RModules X'') (ComplexShape.up ℤ))
  ext K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← Category.assoc, lerayComparisonAb_fac_app, ← Category.assoc, lerayComparisonAb_fac_app,
    lerayUnitAb_app, lerayUnitAb_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp (derivedGlobalSections X),
    Stacks.Cohomology.DerivedSectionsLeray.derivedPushforwardUnit_comp_derivedPushforwardCompIso_inv
      G' G K,
    Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit_app]
  have hnat : (derivedGlobalSections X').map ((derivedPushforwardUnit G').app K) ≫
        (lerayComparisonAb G).app ((derivedPushforward G').obj (DerivedCategory.Qh.obj K)) =
      (lerayComparisonAb G).app (DerivedCategory.Qh.obj
          (((modulePushforward G').mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        (derivedGlobalSections X).map
          ((derivedPushforward G).map ((derivedPushforwardUnit G').app K)) :=
    (lerayComparisonAb G).naturality ((derivedPushforwardUnit G').app K)
  have hf := lerayComparisonAb_fac_app G
    (((modulePushforward G').mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have hu := (derivedGlobalSectionsUnit X).naturality
    ((Functor.mapHomotopyCategoryCompIso (modulePushforwardComp G' G)
      (ComplexShape.up ℤ)).inv.app K)
  dsimp only [Functor.comp_map] at hu
  simp only [Functor.map_comp]
  exact leray_comp_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnat hf (lerayUnitAb_app G _) hu.symm
    (by simp only [← Functor.map_comp]; rfl)

/-! ### The comparison of [Stacks, Tag 01F8] along a composite -/

/-- The comparison `(G_*ℳ')[a] ⟶ RG_*(ℳ'[a])` of [Stacks, Tag 01F8], pointwise. -/
theorem singleToDerivedPushforward_app (a : ℤ) (M' : RModules X') :
    (singleToDerivedPushforward G a).app M' =
      (DerivedCategory.singleFunctorIsoCompQh (RModules X) a).hom.app
          ((modulePushforward G).obj M') ≫
        DerivedCategory.Qh.map (((modulePushforward G).mapHomotopyCategorySingleFunctor a).inv.app
          M') ≫
        (derivedPushforwardUnit G).app ((HomotopyCategory.singleFunctor (RModules X') a).obj M') ≫
        (derivedPushforward G).map ((DerivedCategory.singleFunctorIsoCompQh (RModules X') a).inv.app
          M') := by
  simp [singleToDerivedPushforward]

/-- The identity of cochain complexes behind `singleToDerivedPushforward_comp`: the comparison of
`(-)[a]` with `(G' ≫ G)_*`, followed by the composition isomorphism of the direct images, is the
comparison for `G` at `G'_*ℳ''` followed by `G_*` of the comparison for `G'`. -/
theorem singleMapHomologicalComplex_modulePushforwardComp (a : ℤ) (M'' : RModules X'') :
    (HomologicalComplex.singleMapHomologicalComplex (modulePushforward (G' ≫ G))
        (ComplexShape.up ℤ) a).inv.app M'' ≫
      (NatTrans.mapHomologicalComplex (modulePushforwardComp G' G).inv (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj M'') =
    (HomologicalComplex.single _ (ComplexShape.up ℤ) a).map
        ((modulePushforwardComp G' G).inv.app M'') ≫
      (HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
        (ComplexShape.up ℤ) a).inv.app ((modulePushforward G').obj M'') ≫
      ((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G')
          (ComplexShape.up ℤ) a).inv.app M'') := by
  have hN := HomologicalComplex.singleMapHomologicalComplex_natTrans (ComplexShape.up ℤ)
    (modulePushforwardComp G' G).inv a M''
  have hC := HomologicalComplex.singleMapHomologicalComplex_comp (c := ComplexShape.up ℤ)
    (modulePushforward G') (modulePushforward G) a M''
  have hI : (HomologicalComplex.singleMapHomologicalComplex
      (modulePushforward G' ⋙ modulePushforward G) (ComplexShape.up ℤ) a).app M'' =
      ((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G')
            (ComplexShape.up ℤ) a).app M'') ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
          (ComplexShape.up ℤ) a).app ((modulePushforward G').obj M'') :=
    Iso.ext hC.symm
  have hC' := congrArg Iso.inv hI
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hC'
  rw [← hC', ← cancel_mono ((HomologicalComplex.singleMapHomologicalComplex
    (modulePushforward G' ⋙ modulePushforward G) (ComplexShape.up ℤ) a).hom.app M''),
    Category.assoc, hN, Iso.inv_hom_id_app_assoc, Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

/-- The identity of the homotopy category behind `singleToDerivedPushforward_comp`. -/
theorem mapHomotopyCategorySingleFunctor_modulePushforwardComp (a : ℤ) (M'' : RModules X'') :
    ((modulePushforward (G' ≫ G)).mapHomotopyCategorySingleFunctor a).inv.app M'' ≫
      (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp G' G) (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.singleFunctor _ a).obj M'') =
    (HomotopyCategory.singleFunctor _ a).map ((modulePushforwardComp G' G).inv.app M'') ≫
      ((modulePushforward G).mapHomotopyCategorySingleFunctor a).inv.app
        ((modulePushforward G').obj M'') ≫
      ((modulePushforward G).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((modulePushforward G').mapHomotopyCategorySingleFunctor a).inv.app M'') := by
  have h1 : (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp G' G)
      (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.singleFunctor _ a).obj M'') =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (modulePushforwardComp G' G).inv (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj M'')) := rfl
  have h2 : (HomotopyCategory.singleFunctor _ a).map ((modulePushforwardComp G' G).inv.app M'') =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).map
          ((modulePushforwardComp G' G).inv.app M'')) := rfl
  have h3 : ((modulePushforward G).mapHomotopyCategory (ComplexShape.up ℤ)).map
      (((modulePushforward G').mapHomotopyCategorySingleFunctor a).inv.app M'') =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G')
            (ComplexShape.up ℤ) a).inv.app M'')) := by
    rw [Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app_degree]
    exact Functor.mapHomotopyCategory_map _ _
  rw [h1, h2, h3, Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app_degree,
    Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app_degree]
  refine ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    (((congrArg (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (singleMapHomologicalComplex_modulePushforwardComp G' G a M''))).trans
      (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).trans ?_))
  exact congrArg (_ ≫ ·) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _)

/-- **The comparison of [Stacks, Tag 01F8] along a composite.** For `G' : X'' ⟶ X'` and
`G : X' ⟶ X`, the comparison `((G' ≫ G)_*ℳ'')[a] ⟶ R(G' ≫ G)_*(ℳ''[a])` is the comparison for
`G` at `G'_*ℳ''`, then `RG_*` of the comparison for `G'`, then the composition isomorphism
`RG_* RG'_* ≅ R(G' ≫ G)_*` of [Stacks, Tag 0D5T]. -/
theorem singleToDerivedPushforward_comp (a : ℤ) (M'' : RModules X'') :
    (singleToDerivedPushforward (G' ≫ G) a).app M'' =
      (DerivedCategory.singleFunctor _ a).map ((modulePushforwardComp G' G).inv.app M'') ≫
        (singleToDerivedPushforward G a).app ((modulePushforward G').obj M'') ≫
        (derivedPushforward G).map ((singleToDerivedPushforward G' a).app M'') ≫
        (derivedPushforwardCompIso G' G).hom.app ((DerivedCategory.singleFunctor _ a).obj M'') := by
  open Stacks.Cohomology.DerivedPushforwardComposition in
  have hU := derivedPushforwardCompUnit_comp_derivedPushforwardCompIso
    G' G ((HomotopyCategory.singleFunctor _ a).obj M'')
  rw [Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit_app] at hU
  simp only [Category.assoc] at hU
  have hH := mapHomotopyCategorySingleFunctor_modulePushforwardComp G' G a M''
  simp only [singleToDerivedPushforward_app]
  exact Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.singleComparison_comp_of_unit_comp
    (DerivedCategory.singleFunctorIsoCompQh _ a)
    (DerivedCategory.singleFunctorIsoCompQh _ a) (DerivedCategory.singleFunctorIsoCompQh _ a)
    ((modulePushforward G').mapHomotopyCategorySingleFunctor a)
    ((modulePushforward G).mapHomotopyCategorySingleFunctor a)
    ((modulePushforward (G' ≫ G)).mapHomotopyCategorySingleFunctor a)
    (derivedPushforwardUnit G') (derivedPushforwardUnit G) (derivedPushforwardUnit (G' ≫ G))
    (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp G' G) (ComplexShape.up ℤ))
    (derivedPushforwardCompIso G' G) M'' ((modulePushforwardComp G' G).inv.app M'') hU hH

/-! ### The pullback map along a composite -/

/-- The Leray identification of the canonical comparison is the inverse of the Leray comparison,
pointwise. -/
private lemma canonical_leray_hom_app [IsIso (lerayComparisonAb G)]
    (K : DerivedCategory (RModules X')) :
    (CohomologyPullbackComparison.canonical G).leray.hom.app K =
      inv ((lerayComparisonAb G).app K) := by
  rw [← NatIso.isIso_inv_app]
  rfl

/-- The Leray identification of the canonical comparisons along a composite: `RΓ(X, -)` of the
composition isomorphism of derived pushforwards followed by the identification for `G' ≫ G` is
the identification for `G` followed by that for `G'`. -/
theorem canonical_leray_comp (K : DerivedCategory (RModules X'')) :
    (derivedGlobalSections X).map ((derivedPushforwardCompIso G' G).hom.app K) ≫
        (CohomologyPullbackComparison.canonical (G' ≫ G)).leray.hom.app K =
      (CohomologyPullbackComparison.canonical G).leray.hom.app ((derivedPushforward G').obj K) ≫
        (CohomologyPullbackComparison.canonical G').leray.hom.app K := by
  have := isIso_lerayComparisonAb G
  have := isIso_lerayComparisonAb G'
  have := isIso_lerayComparisonAb (G' ≫ G)
  have h := congrArg (fun τ => τ.app K) (lerayComparisonAb_comp G' G)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  rw [canonical_leray_hom_app, canonical_leray_hom_app, canonical_leray_hom_app,
    ← cancel_epi ((lerayComparisonAb G').app K ≫
      (lerayComparisonAb G).app ((derivedPushforward G').obj K))]
  conv_rhs => rw [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id]
  rw [← h, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, IsIso.hom_inv_id]

/-- The algebra of `derivedPushforwardMap_canonical_comp`, at variables. -/
private lemma derivedMap_comp_chase {D D' : Type*} [Category* D] [Category* D'] (R : D' ⥤ D)
    {S₀ S₁ S₂ P : D} {T₁ T₂ T₃ : D'} (sΦ : S₀ ⟶ S₂) (smi : S₂ ⟶ S₂) (sφ : S₀ ⟶ S₁)
    (sGφ' : S₁ ⟶ S₂) (uG : S₁ ⟶ R.obj T₁) (uG₂ : S₂ ⟶ R.obj T₂) (sφ' : T₁ ⟶ T₂)
    (uG' : T₂ ⟶ T₃) (ρ : R.obj T₃ ⟶ P) (uGG : S₂ ⟶ P)
    (hs : uGG = smi ≫ uG₂ ≫ R.map uG' ≫ ρ) (hΦ : sΦ ≫ smi = sφ ≫ sGφ')
    (hn : sGφ' ≫ uG₂ = uG ≫ R.map sφ') :
    sΦ ≫ uGG = (sφ ≫ uG) ≫ R.map (sφ' ≫ uG') ≫ ρ := by
  rw [hs, reassoc_of% hΦ, reassoc_of% hn, R.map_comp]
  simp only [Category.assoc]

/-- **The derived `G`-map of a composite.** The morphism `ℳ[a] ⟶ R(G' ≫ G)_*(ℳ''[a])` of
[Stacks, Tag 01F8] attached to the `(G' ≫ G)`-map `φ ≫ G_*φ'` is the one attached to `φ`,
followed by `RG_*` of the one attached to `φ'` and the composition isomorphism. -/
theorem derivedPushforwardMap_canonical_comp (a : ℤ) {M : RModules X} {M' : RModules X'}
    {M'' : RModules X''} (φ : M ⟶ (modulePushforward G).obj M')
    (φ' : M' ⟶ (modulePushforward G').obj M'') :
    derivedPushforwardMap (CohomologyPullbackComparison.canonical (G' ≫ G)) a
        (φ ≫ (modulePushforward G).map φ' ≫ (modulePushforwardComp G' G).hom.app M'') =
      derivedPushforwardMap (CohomologyPullbackComparison.canonical G) a φ ≫
        (derivedPushforward G).map
          (derivedPushforwardMap (CohomologyPullbackComparison.canonical G') a φ') ≫
        (derivedPushforwardCompIso G' G).hom.app ((DerivedCategory.singleFunctor _ a).obj M'') := by
  have hs := singleToDerivedPushforward_comp G' G a M''
  have hn := (singleToDerivedPushforward G a).naturality φ'
  dsimp only [Functor.comp_map] at hn
  have hΦ : (DerivedCategory.singleFunctor _ a).map
        (φ ≫ (modulePushforward G).map φ' ≫ (modulePushforwardComp G' G).hom.app M'') ≫
      (DerivedCategory.singleFunctor _ a).map ((modulePushforwardComp G' G).inv.app M'') =
      (DerivedCategory.singleFunctor _ a).map φ ≫
        (DerivedCategory.singleFunctor _ a).map ((modulePushforward G).map φ') := by
    rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc,
      Iso.hom_inv_id_app]
    exact congrArg _ (congrArg (φ ≫ ·) (Category.comp_id _))
  change (DerivedCategory.singleFunctor _ a).map
        (φ ≫ (modulePushforward G).map φ' ≫ (modulePushforwardComp G' G).hom.app M'') ≫
      (singleToDerivedPushforward (G' ≫ G) a).app M'' =
    ((DerivedCategory.singleFunctor _ a).map φ ≫ (singleToDerivedPushforward G a).app M') ≫
      (derivedPushforward G).map ((DerivedCategory.singleFunctor _ a).map φ' ≫
        (singleToDerivedPushforward G' a).app M'') ≫
      (derivedPushforwardCompIso G' G).hom.app ((DerivedCategory.singleFunctor _ a).obj M'')
  exact derivedMap_comp_chase (derivedPushforward G) _ _ _ _ _ _ _ _ _ _ hs hΦ hn

/-- The algebra of `pullbackHgroup_canonical_comp` on derived global sections, at variables. -/
private lemma sections_comp_chase {E : Type*} [Category* E] {A B C D' F F' T : E}
    (gφ : A ⟶ B) (gr : B ⟶ C) (gρ : C ⟶ D') (lGG : D' ⟶ T) (lG₁ : C ⟶ F) (lG' : F ⟶ T)
    (lG : B ⟶ F') (g' : F' ⟶ F) (h₁ : gρ ≫ lGG = lG₁ ≫ lG') (h₂ : gr ≫ lG₁ = lG ≫ g') :
    gφ ≫ gr ≫ gρ ≫ lGG = (gφ ≫ lG) ≫ g' ≫ lG' := by
  rw [h₁, reassoc_of% h₂]
  simp only [Category.assoc]

/-- **The pullback map on cohomology along a composite is the composite of the pullback maps**
([Stacks, Tag 01F9] is functorial). For `G' : X'' ⟶ X'`, `G : X' ⟶ X`, a `G`-map
`φ : ℳ ⟶ G_*ℳ'` and a `G'`-map `φ' : ℳ' ⟶ G'_*ℳ''`, the pullback map of the `(G' ≫ G)`-map
`φ ≫ G_*φ'` is that of `φ` followed by that of `φ'`, for the canonical comparisons. -/
theorem pullbackHgroup_canonical_comp (a m : ℤ) (n : ℕ) (hn : m - a = n) {M : RModules X}
    {M' : RModules X'} {M'' : RModules X''} (φ : M ⟶ (modulePushforward G).obj M')
    (φ' : M' ⟶ (modulePushforward G').obj M'') :
    pullbackHgroup (CohomologyPullbackComparison.canonical (G' ≫ G)) a m n hn
        (φ ≫ (modulePushforward G).map φ' ≫ (modulePushforwardComp G' G).hom.app M'') =
      pullbackHgroup (CohomologyPullbackComparison.canonical G) a m n hn φ ≫
        pullbackHgroup (CohomologyPullbackComparison.canonical G') a m n hn φ' := by
  have hK : (derivedGlobalSections X).map (derivedPushforwardMap
        (CohomologyPullbackComparison.canonical (G' ≫ G)) a
          (φ ≫ (modulePushforward G).map φ' ≫ (modulePushforwardComp G' G).hom.app M'')) ≫
        (CohomologyPullbackComparison.canonical (G' ≫ G)).leray.hom.app
          ((DerivedCategory.singleFunctor _ a).obj M'') =
      ((derivedGlobalSections X).map
          (derivedPushforwardMap (CohomologyPullbackComparison.canonical G) a φ) ≫
        (CohomologyPullbackComparison.canonical G).leray.hom.app
          ((DerivedCategory.singleFunctor _ a).obj M')) ≫
      ((derivedGlobalSections X').map
          (derivedPushforwardMap (CohomologyPullbackComparison.canonical G') a φ') ≫
        (CohomologyPullbackComparison.canonical G').leray.hom.app
          ((DerivedCategory.singleFunctor _ a).obj M'')) := by
    rw [derivedPushforwardMap_canonical_comp, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc]
    exact sections_comp_chase _ _ _ _ _ _ _ _ (canonical_leray_comp G' G _)
      ((CohomologyPullbackComparison.canonical G).leray.hom.naturality
        (derivedPushforwardMap (CohomologyPullbackComparison.canonical G') a φ'))
  simp only [pullbackHgroup, Category.assoc, Iso.hom_inv_id_assoc]
  rw [hK, Functor.map_comp, Category.assoc]

/-! ### The pullback map along the identity -/

/-- A morphism equal to the identity is absorbed, at variables. -/
private lemma id_comp_chase {C : Type*} [Category* C] {A B : C} (x : A ⟶ A) (y : A ⟶ B)
    (hx : x = 𝟙 A) : x ≫ y = y := by
  rw [hx, Category.id_comp]

open Stacks.Cohomology.DerivedPushforwardAssociativity in
/-- The comparison `(𝟙 X)_* ⟶ R(𝟙 X)_*` followed by the unit isomorphism `R(𝟙 X)_* ≅ 𝟭` is the
localization of the unit isomorphism `(𝟙 X)_* ≅ 𝟭` on the homotopy category. -/
theorem derivedPushforwardUnit_id_comp_idIso_hom
    (K : HomotopyCategory (RModules X) (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit (𝟙 X)).app K ≫
        (derivedPushforwardIdIso X).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((modulePushforwardIdHomotopy X).hom.app K) := by
  have hId := derivedPushforwardIdIso_inv_app X K
  have hη : (derivedPushforwardUnit (𝟙 X)).app K ≫
      (derivedPushforwardIdIso X).hom.app (DerivedCategory.Qh.obj K) =
        (pushforwardIdToDerived X).inv.app K := by
    rw [← cancel_epi ((pushforwardIdToDerived X).hom.app K), ← Category.assoc, ← hId,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app]
    rfl
  rw [hη, ← cancel_epi ((pushforwardIdToDerived X).hom.app K), Iso.hom_inv_id_app,
    pushforwardIdToDerived_hom_app, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  rfl

open Stacks.Cohomology.DerivedPushforwardAssociativity in
/-- **The Leray comparison in `D(Ab)` along the identity** is `RΓ(X, -)` of the unit isomorphism
`R(𝟙 X)_* ≅ 𝟭`, pointwise. -/
theorem lerayComparisonAb_id_app (L : DerivedCategory (RModules X)) :
    (lerayComparisonAb (𝟙 X)).app L ≫
        (derivedGlobalSections X).map ((derivedPushforwardIdIso X).hom.app L) = 𝟙 _ := by
  have key : lerayComparisonAb (𝟙 X) ≫
      Functor.whiskerRight (derivedPushforwardIdIso X).hom (derivedGlobalSections X) =
        (Functor.leftUnitor _).inv := by
    apply (derivedGlobalSections X).rightDerived_ext (derivedGlobalSectionsUnit X)
      (HomotopyCategory.quasiIso (RModules X) (ComplexShape.up ℤ))
    ext K
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_inv_app]
    rw [← Category.assoc, lerayComparisonAb_fac_app, lerayUnitAb_app, Category.assoc,
      Category.assoc, ← Functor.map_comp, derivedPushforwardUnit_id_comp_idIso_hom]
    have hu := (derivedGlobalSectionsUnit X).naturality ((modulePushforwardIdHomotopy X).hom.app K)
    dsimp only [Functor.comp_map] at hu
    rw [← hu, ← Category.assoc, ← Functor.map_comp]
    dsimp only [Functor.id_obj, Functor.comp_obj]
    rw [Category.comp_id]
    refine id_comp_chase _ _ ?_
    rw [← CategoryTheory.Functor.map_id]
    rfl
  have := congrArg (fun τ => τ.app L) key
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at this
  exact this

/-- The algebra of `singleToDerivedPushforward_id_app`, at variables. -/
private lemma single_id_chase {D H : Type*} [Category* D] [Category* H] (Qh : H ⥤ D)
    (R : D ⥤ D) {A B : D} {P P' P'' : H} (sh : A ⟶ Qh.obj P) (ms : P ⟶ P')
    (u : Qh.obj P' ⟶ R.obj (Qh.obj P''))
    (si : Qh.obj P'' ⟶ B) (idh : R.obj (Qh.obj P'') ⟶ Qh.obj P'') (idB : R.obj B ⟶ B)
    (mp : P' ⟶ P'') (hn : R.map si ≫ idB = idh ≫ si) (hu : u ≫ idh = Qh.map mp)
    (sε : A ⟶ B) (hh : sh ≫ Qh.map (ms ≫ mp) ≫ si = sε) :
    sh ≫ Qh.map ms ≫ u ≫ R.map si ≫ idB = sε := by
  rw [hn, reassoc_of% hu, ← hh, Functor.map_comp, Category.assoc]

open Stacks.Cohomology.DerivedPushforwardAssociativity in
/-- The identity of the homotopy category behind `singleToDerivedPushforward_id_app`. -/
theorem mapHomotopyCategorySingleFunctor_modulePushforwardId (a : ℤ) (M' : RModules X) :
    ((modulePushforward (𝟙 X)).mapHomotopyCategorySingleFunctor a).inv.app M' ≫
        ((modulePushforwardIdHomotopy X).hom.app ((HomotopyCategory.singleFunctor _ a).obj M') :
          _ ⟶ (HomotopyCategory.singleFunctor _ a).obj M') =
      (HomotopyCategory.singleFunctor _ a).map
        ((modulePushforwardId X).hom.app M' : (modulePushforward (𝟙 X)).obj M' ⟶ M') := by
  rw [Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app_degree]
  have h1 : (modulePushforwardIdHomotopy X).hom.app ((HomotopyCategory.singleFunctor _ a).obj M') =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (modulePushforwardId X).hom (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj M')) := by
    simp only [modulePushforwardIdHomotopy, Iso.trans_hom, NatTrans.comp_app,
      natIsoMapHomotopyCategory, mapHomotopyCategoryIdIso]
    rfl
  have h2 : (HomotopyCategory.singleFunctor _ a).map ((modulePushforwardId X).hom.app M') =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).map
          ((modulePushforwardId X).hom.app M')) := rfl
  rw [h1, h2]
  refine ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm.trans ?_
  refine quotient_map_congr ?_
  ext i : 1
  by_cases hi : i = a
  · subst hi
    rw [HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [NatTrans.mapHomologicalComplex_app_f, Category.assoc]
    rw [NatTrans.naturality]
    rfl
  · exact ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a
      ((modulePushforward (𝟙 X)).obj M') i hi).eq_of_src _ _)

/-- **The comparison of [Stacks, Tag 01F8] along the identity** is the unit isomorphism
`(𝟙 X)_* ≅ 𝟭` placed in degree `a`, read through `R(𝟙 X)_* ≅ 𝟭`. -/
theorem singleToDerivedPushforward_id_app (a : ℤ) (M' : RModules X) :
    (singleToDerivedPushforward (𝟙 X) a).app M' ≫
        (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso X).hom.app
          ((DerivedCategory.singleFunctor _ a).obj M') =
      (DerivedCategory.singleFunctor _ a).map ((modulePushforwardId X).hom.app M') := by
  rw [singleToDerivedPushforward_app]
  simp only [Category.assoc]
  have hσ := (DerivedCategory.singleFunctorIsoCompQh (RModules X) a).hom.naturality
    ((modulePushforwardId X).hom.app M')
  dsimp only [Functor.comp_map] at hσ
  refine single_id_chase DerivedCategory.Qh _ _ _ _ _ _ _ _
    ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso X).hom.naturality
      ((DerivedCategory.singleFunctorIsoCompQh (RModules X) a).inv.app M'))
    (derivedPushforwardUnit_id_comp_idIso_hom _) _ ?_
  rw [mapHomotopyCategorySingleFunctor_modulePushforwardId, ← reassoc_of% hσ, Iso.hom_inv_id_app,
    Category.comp_id]

/-- Moving an isomorphism across an equation, at variables. -/
private lemma iso_inv_chase {C : Type*} [Category* C] {A B P Q : C} (i : A ≅ P) (x : A ⟶ B)
    (j : B ⟶ Q) (y : P ⟶ Q) (h : x ≫ j = i.hom ≫ y) : i.inv ≫ x ≫ j = y := by
  rw [h, Iso.inv_hom_id_assoc]

/-- The Leray identification of the canonical comparison along the identity is `RΓ(X, -)` of the
unit isomorphism `R(𝟙 X)_* ≅ 𝟭`. -/
theorem canonical_leray_id_app (L : DerivedCategory (RModules X)) :
    (CohomologyPullbackComparison.canonical (𝟙 X)).leray.hom.app L =
      (derivedGlobalSections X).map
        ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso X).hom.app
          L) := by
  have := isIso_lerayComparisonAb (𝟙 X)
  rw [canonical_leray_hom_app]
  exact IsIso.inv_eq_of_hom_inv_id (lerayComparisonAb_id_app L)

/-- **The pullback map on cohomology along the identity** is the map induced on cohomology by the
`𝟙`-map `φ : ℳ ⟶ (𝟙 X)_*ℳ' = ℳ'`, for the canonical comparisons. -/
theorem pullbackHgroup_canonical_id (a m : ℤ) (n : ℕ) (hn : m - a = n) {M M' : RModules X}
    (φ : M ⟶ (modulePushforward (𝟙 X)).obj M') :
    pullbackHgroup (CohomologyPullbackComparison.canonical (𝟙 X)) a m n hn φ =
      (Hfunctor (structureSheafRing X) ⊤ n).map (φ ≫ (modulePushforwardId X).hom.app M') := by
  have hD : (derivedGlobalSections X).map
        (derivedPushforwardMap (CohomologyPullbackComparison.canonical (𝟙 X)) a φ) ≫
      (CohomologyPullbackComparison.canonical (𝟙 X)).leray.hom.app
        ((DerivedCategory.singleFunctor _ a).obj M') =
      (derivedGlobalSections X).map ((DerivedCategory.singleFunctor _ a).map
        (φ ≫ (modulePushforwardId X).hom.app M')) := by
    rw [canonical_leray_id_app, ← Functor.map_comp]
    congr 1
    simp only [derivedPushforwardMap, CohomologyPullbackComparison.canonical]
    rw [Category.assoc, singleToDerivedPushforward_id_app, ← Functor.map_comp]
  have hnat := cohomologyDerivedSingleIso_hom_naturality X
    (φ ≫ (modulePushforwardId X).hom.app M' : M ⟶ M') a m n hn
  unfold pullbackHgroup
  rw [hD]
  exact iso_inv_chase _ _ _ _ hnat

/-- **The pullback map along a morphism equal to the identity**: for `G : X ⟶ X` with `G = 𝟙 X`,
the pullback map of a `G`-map `ψ : ℳ ⟶ G_*ℳ'` is the map induced on cohomology by `ψ`, read
through `G_*ℳ' = ℳ'`. -/
theorem pullbackHgroup_canonical_of_eq_id {G : X ⟶ X} (hG : G = 𝟙 X) (a m : ℤ) (n : ℕ)
    (hn : m - a = n) {M M' : RModules X} (ψ : M ⟶ (modulePushforward G).obj M') :
    pullbackHgroup (CohomologyPullbackComparison.canonical G) a m n hn ψ =
      (Hfunctor (structureSheafRing X) ⊤ n).map
        (ψ ≫ eqToHom (congrArg (fun g : X ⟶ X => (modulePushforward g).obj M') hG) ≫
          (modulePushforwardId X).hom.app M') := by
  subst hG
  rw [pullbackHgroup_canonical_id, eqToHom_refl, Category.id_comp]

end Stacks.DeRham.GysinCohomologyBaseChange

end
