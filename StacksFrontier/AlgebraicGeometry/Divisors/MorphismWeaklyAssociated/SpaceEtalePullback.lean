module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# Weakly associated points and étale pullback

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` and let `G` be an
`𝒪_Y`-module. A point of `X` is weakly associated to `f^*G` exactly when its image is weakly
associated to `G`: this is Stacks 0CUU, for the notion of a weakly associated point of
`AlgebraicGeometry.Space.IsWeaklyAssociatedPoint`.

## Main definitions

* `Stacks.moduleStalkLargeCongr`: isomorphic sheaves of modules have isomorphic stalks at a
  point of a site.
* `AlgebraicGeometry.Space.etaleStalkRingIso` and
  `AlgebraicGeometry.Space.etaleModuleStalkLargeAddEquiv`: an étale morphism changes neither the
  stalk of the structure sheaf nor the stalk of a module at a geometric point, the second
  semilinearly over the first.
* `AlgebraicGeometry.Space.geometricFiberPostcomp`: postcomposition with an étale morphism, read
  on the lifts of a geometric point into the étale charts.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_modulePullback_iff`: **Stacks 0CUU**, the
  equivalence for the pullback of modules along an étale morphism.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_etaleModulePullback_iff`: the same for étale
  restriction of sections, which is that pullback by Stacks 03LW.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_congr`: weak association is invariant under an
  isomorphism of modules.
* `AlgebraicGeometry.Space.initial_geometricFiberPostcomp`: postcomposition with an étale
  morphism is initial on the lifts of a geometric point into the étale charts.
* `Stacks.semilinear_of_semilinear_moduleStalkLargeGerm`: an additive map out of the stalk of a
  sheaf of modules which is semilinear on germs is semilinear.

## References

* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m v w t

namespace Stacks

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

/-! ### The stalk of a sheaf of modules as the stalk of its lifted sections -/

/-- The stalk of a sheaf of modules at a point of a site, identified with the stalk of its
lifted sections as a presheaf of abelian groups: the former is the colimit of the latter's
diagram over a small final model of the neighbourhoods of the point. -/
noncomputable def moduleStalkLargeAddEquivPresheafFiber
    (F : SheafOfModules.{m} (commRingSheafToRingSheaf O)) :
    moduleStalkLarge.{m} p O F ≃+
      (p.presheafFiber (A := AddCommGrpCat.{max w m})).obj (liftedSectionPresheaf.{m} O F) :=
  (moduleStalkLargeFinalIso.{m} p O F).addCommGroupIsoToAddEquiv

/-- The identification of the stalk with the stalk of the lifted sections sends the germ of a
section to its image in the colimit over the neighbourhoods of the point. -/
theorem moduleStalkLargeAddEquivPresheafFiber_germ
    (F : SheafOfModules.{m} (commRingSheafToRingSheaf O)) (U : C) (x : p.fiber.obj U)
    (s : F.val.obj (op U)) :
    moduleStalkLargeAddEquivPresheafFiber p O F (moduleStalkLargeGerm p O F U x s) =
      p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F) (ULift.up s) := by
  rw [moduleStalkLargeGerm_apply]
  exact ConcreteCategory.congr_hom (moduleStalkLargeFinalIso.{m} p O F).inv_hom_id _

/-- The inverse identification sends the image of a section in the colimit over the
neighbourhoods of the point to its germ. -/
theorem moduleStalkLargeAddEquivPresheafFiber_symm_toPresheafFiber
    (F : SheafOfModules.{m} (commRingSheafToRingSheaf O)) (U : C) (x : p.fiber.obj U)
    (s : F.val.obj (op U)) :
    (moduleStalkLargeAddEquivPresheafFiber p O F).symm
        (p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F) (ULift.up s)) =
      moduleStalkLargeGerm p O F U x s :=
  (moduleStalkLargeAddEquivPresheafFiber p O F).symm_apply_eq.mpr
    (moduleStalkLargeAddEquivPresheafFiber_germ p O F U x s).symm

/-- An element of the stalk of the structure sheaf and an element of the stalk of a sheaf of
modules are germs of sections over one common neighbourhood of the point. -/
theorem exists_moduleStalkLargeGerm_representatives
    (F : SheafOfModules.{m} (commRingSheafToRingSheaf O))
    (r : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj) (z : moduleStalkLarge.{m} p O F) :
    ∃ (U : C) (x : p.fiber.obj U) (a : (commRingSheafToRingSheaf O).obj.obj (op U))
      (s : F.val.obj (op U)),
      p.toPresheafFiber U x O.obj a = r ∧ moduleStalkLargeGerm p O F U x s = z := by
  obtain ⟨U₁, x₁, a₀, ha₀⟩ := p.toPresheafFiber_jointly_surjective (P := O.obj) r
  obtain ⟨U₂, x₂, s₀, hs₀⟩ := moduleStalkLargeGerm_jointly_surjective p O F z
  obtain ⟨V, η, g₁, g₂, hg₁, hg₂⟩ := exists_common_neighborhood₂ p
    (fun _ : Unit => U₁) (fun _ : Unit => U₂) (fun _ => x₁) (fun _ => x₂)
  refine ⟨V, η, O.obj.map (g₁ ()).op a₀, (F.val.map (g₂ ()).op).hom s₀, ?_, ?_⟩
  · rwa [p.toPresheafFiber_w_apply, hg₁ ()]
  · rwa [moduleStalkLargeGerm_w, hg₂ ()]

/-- An additive map out of the stalk of a sheaf of modules which is semilinear on germs is
semilinear. -/
theorem semilinear_of_semilinear_moduleStalkLargeGerm
    (F : SheafOfModules.{m} (commRingSheafToRingSheaf O))
    {R' : Type*} [Ring R'] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (e : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj →+* R')
    (φ : moduleStalkLarge.{m} p O F →+ M')
    (h : ∀ (U : C) (x : p.fiber.obj U)
      (a : (commRingSheafToRingSheaf O).obj.obj (op U)) (s : F.val.obj (op U)),
      φ (p.toPresheafFiber U x O.obj a • moduleStalkLargeGerm p O F U x s) =
        e (p.toPresheafFiber U x O.obj a) • φ (moduleStalkLargeGerm p O F U x s))
    (r : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (z : moduleStalkLarge.{m} p O F) :
    φ (r • z) = e r • φ z := by
  obtain ⟨U, x, a, s, ha, hs⟩ := exists_moduleStalkLargeGerm_representatives p O F r z
  subst ha hs
  exact h U x a s

/-! ### Isomorphic sheaves of modules have isomorphic stalks -/

variable {F₁ F₂ : SheafOfModules.{m} (commRingSheafToRingSheaf O)}

/-- The lifted sections of an isomorphism of sheaves of modules, as an isomorphism of presheaves
of abelian groups. -/
noncomputable def liftedSectionPresheafCongr (α : F₁ ≅ F₂) :
    liftedSectionPresheaf.{m} O F₁ ≅ liftedSectionPresheaf.{m} O F₂ :=
  Functor.isoWhiskerRight ((PresheafOfModules.toPresheaf _).mapIso
    ((SheafOfModules.forget _).mapIso α)) AddCommGrpCat.uliftFunctor.{w}

/-- The stalk at a point of the site of the lifted sections of an isomorphism of sheaves of
modules. -/
noncomputable def presheafFiberCongrAddEquiv (α : F₁ ≅ F₂) :
    (p.presheafFiber (A := AddCommGrpCat.{max w m})).obj (liftedSectionPresheaf.{m} O F₁) ≃+
      (p.presheafFiber (A := AddCommGrpCat.{max w m})).obj (liftedSectionPresheaf.{m} O F₂) :=
  ((p.presheafFiber (A := AddCommGrpCat.{max w m})).mapIso
    (liftedSectionPresheafCongr.{m} O α)).addCommGroupIsoToAddEquiv

omit [LocallySmall.{w} C] in
/-- The stalk of an isomorphism of sheaves of modules carries the image of a section to the
image of its value under the isomorphism. -/
theorem presheafFiberCongrAddEquiv_toPresheafFiber (α : F₁ ≅ F₂) (U : C) (x : p.fiber.obj U)
    (s : F₁.val.obj (op U)) :
    presheafFiberCongrAddEquiv p O α
        (p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F₁) (ULift.up s)) =
      p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F₂)
        (ULift.up ((α.hom.val.app (op U)).hom s)) :=
  p.toPresheafFiber_naturality_apply (liftedSectionPresheafCongr.{m} O α).hom U x (ULift.up s)

/-- The stalks at a point of a site of isomorphic sheaves of modules are isomorphic as additive
groups. -/
noncomputable def moduleStalkLargeCongr (α : F₁ ≅ F₂) :
    moduleStalkLarge.{m} p O F₁ ≃+ moduleStalkLarge.{m} p O F₂ :=
  (moduleStalkLargeAddEquivPresheafFiber p O F₁).trans
    ((presheafFiberCongrAddEquiv p O α).trans
      (moduleStalkLargeAddEquivPresheafFiber p O F₂).symm)

/-- The comparison of the stalks of isomorphic sheaves of modules carries the germ of a section
to the germ of its value under the isomorphism. -/
theorem moduleStalkLargeCongr_germ (α : F₁ ≅ F₂) (U : C) (x : p.fiber.obj U)
    (s : F₁.val.obj (op U)) :
    moduleStalkLargeCongr p O α (moduleStalkLargeGerm p O F₁ U x s) =
      moduleStalkLargeGerm p O F₂ U x ((α.hom.val.app (op U)).hom s) := by
  rw [moduleStalkLargeCongr, AddEquiv.trans_apply, AddEquiv.trans_apply,
    moduleStalkLargeAddEquivPresheafFiber_germ, presheafFiberCongrAddEquiv_toPresheafFiber,
    moduleStalkLargeAddEquivPresheafFiber_symm_toPresheafFiber]

/-- The comparison of the stalks of isomorphic sheaves of modules is linear over the stalk of
the sheaf of rings. -/
theorem moduleStalkLargeCongr_smul (α : F₁ ≅ F₂)
    (r : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (z : moduleStalkLarge.{m} p O F₁) :
    moduleStalkLargeCongr p O α (r • z) = r • moduleStalkLargeCongr p O α z := by
  obtain ⟨U, x, a, s, ha, hs⟩ := exists_moduleStalkLargeGerm_representatives p O F₁ r z
  subst ha hs
  rw [← moduleStalkLargeGerm_smul, moduleStalkLargeCongr_germ, moduleStalkLargeCongr_germ,
    (α.hom.val.app (op U)).hom.map_smul, moduleStalkLargeGerm_smul]

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The stalk of the structure sheaf of an algebraic space at the point of its small étale site
determined by a geometric point is a local ring. -/
instance isLocalRing_presheafFiber_structureSheaf (X : AlgebraicSpaces B S hS)
    (xbar : GeometricPoint B S hS X.1) :
    IsLocalRing (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber
      (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O.obj) :=
  isLocalRing_presheafFiber_structurePresheaf B S hS X.1 xbar X.2

/-- The sections of an `𝒪_Z`-module as a presheaf of abelian groups, raised to the universe in
which the stalk `Stacks.moduleStalkLarge` at a point of the small étale site is formed. -/
noncomputable abbrev liftedModuleSections (Z : AlgebraicSpaces B S hS)
    (F : Modules.{u, m} B S hS Z.1 Z.2) :
    (SmallEtale B S hS Z.1)ᵒᵖ ⥤ AddCommGrpCat.{max u m} :=
  F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u}

variable {X Y : AlgebraicSpaces B S hS}

/-! ### An étale morphism does not change the stalks -/

section Etale

variable (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (xbar : GeometricPoint B S hS X.1)

/-- Postcomposition with an étale morphism `f : X ⟶ Y` of algebraic spaces, read on the lifts of
a geometric point `x̄` of `X` into the étale charts: a lift of `x̄` into a chart of `X` is a lift
of the image of `x̄` into the composite chart of `Y`. -/
noncomputable def geometricFiberPostcomp :
    (etaleSitePoint B S hS X.1 xbar X.2).fiber.Elements ⥤
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).fiber.Elements where
  obj e := Functor.elementsMk _ ((smallEtalePostcomp B S hS f hf).obj e.obj)
    ⟨e.val.1, congrArg _ e.val.2⟩
  map {e e'} g := Functor.Elements.homMk ((smallEtalePostcomp B S hS f hf).map g.hom)
    (Subtype.ext (congrArg Subtype.val g.map_val :
      (((geometricFiber B S hS X.1 xbar).map g.hom) e.val).1 = (e'.val).1))
  map_id e := Functor.Elements.hom_ext ((smallEtalePostcomp B S hS f hf).map_id e.obj)
  map_comp g h :=
    Functor.Elements.hom_ext ((smallEtalePostcomp B S hS f hf).map_comp g.hom h.hom)

/-- Reading a small étale neighbourhood of a geometric point as a lift of that point into a
chart commutes with postcomposition along an étale morphism, on the nose. -/
theorem neighborhoodToFiberElements_comp_geometricFiberPostcomp :
    neighborhoodToFiberElements B S hS X.1 xbar ⋙ geometricFiberPostcomp B S hS f hf xbar =
      SmallEtaleNeighborhood.postcomp B S hS f hf xbar ⋙
        neighborhoodToFiberElements B S hS Y.1 (geometricPointMap f.hom xbar) :=
  rfl

/-- Postcomposition with an étale morphism is initial on the lifts of a geometric point. -/
instance initial_geometricFiberPostcomp : (geometricFiberPostcomp B S hS f hf xbar).Initial := by
  have h₁ : (neighborhoodToFiberElements B S hS X.1 xbar).IsEquivalence :=
    (neighborhoodFiberElementsEquiv B S hS X.1 xbar).isEquivalence_functor
  have h₂ : (neighborhoodToFiberElements B S hS Y.1
      (geometricPointMap f.hom xbar)).IsEquivalence :=
    (neighborhoodFiberElementsEquiv B S hS Y.1
      (geometricPointMap f.hom xbar)).isEquivalence_functor
  have h₃ := SmallEtaleNeighborhood.initial_postcomp B S hS f hf xbar
  have h₄ : (neighborhoodToFiberElements B S hS X.1 xbar ⋙
      geometricFiberPostcomp B S hS f hf xbar).Initial := by
    rw [neighborhoodToFiberElements_comp_geometricFiberPostcomp]
    exact Functor.initial_comp_equivalence
      (SmallEtaleNeighborhood.postcomp B S hS f hf xbar)
      (neighborhoodToFiberElements B S hS Y.1 (geometricPointMap f.hom xbar))
  exact Functor.initial_of_equivalence_comp (neighborhoodToFiberElements B S hS X.1 xbar) _

/-- The diagram of sections of the structure sheaf over the lifts of `x̄` into the étale charts
of `X` is the corresponding diagram for `Y`, read through postcomposition. -/
theorem geometricFiberPostcomp_op_comp_structureSheaf :
    (geometricFiberPostcomp B S hS f hf xbar).op ⋙
        ((CategoryOfElements.π
            (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).fiber).op ⋙
          (smallEtaleRingedTopos B S hS Y).O.obj) =
      (CategoryOfElements.π (etaleSitePoint B S hS X.1 xbar X.2).fiber).op ⋙
        (smallEtaleRingedTopos B S hS X).O.obj :=
  rfl

/-- **Stacks 04KF, first equality, at the point of the site.** An étale morphism of algebraic
spaces does not change the stalk of the structure sheaf at a geometric point. -/
noncomputable def etaleStalkRingIso :
    ((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj ≅
      ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).presheafFiber
        (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O.obj :=
  ((etaleSitePoint B S hS X.1 xbar X.2).isColimitPresheafFiberCocone
      (smallEtaleRingedTopos B S hS X).O.obj).coconePointUniqueUpToIso
    ((Functor.Final.isColimitWhiskerEquiv (geometricFiberPostcomp B S hS f hf xbar).op
        ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).presheafFiberCocone
          (smallEtaleRingedTopos B S hS Y).O.obj)).symm
      ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).isColimitPresheafFiberCocone
        (smallEtaleRingedTopos B S hS Y).O.obj))

/-- The comparison of the stalks of the structure sheaf carries the germ of a section over an
étale chart of `X` to its germ over the composite chart of `Y`. -/
theorem etaleStalkRingIso_toPresheafFiber
    (e : (etaleSitePoint B S hS X.1 xbar X.2).fiber.Elements) :
    (etaleSitePoint B S hS X.1 xbar X.2).toPresheafFiber e.1 e.2
          (smallEtaleRingedTopos B S hS X).O.obj ≫ (etaleStalkRingIso B S hS f hf xbar).hom =
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).toPresheafFiber
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).1
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).2
        (smallEtaleRingedTopos B S hS Y).O.obj :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (op e)

variable (G : Modules.{u, m} B S hS Y.1 Y.2)

/-- The diagram of lifted sections of a module over the lifts of `x̄` into the étale charts of
`X` is the diagram of lifted sections of `G` over the lifts of the image point, read through
postcomposition: the two agree on the nose, so this is the identity. -/
noncomputable def liftedSectionDiagramIso :
    (CategoryOfElements.π (etaleSitePoint B S hS X.1 xbar X.2).fiber).op ⋙
        liftedModuleSections B S hS X ((etaleModulePullback B S hS f hf).obj G) ≅
      (geometricFiberPostcomp B S hS f hf xbar).op ⋙
        ((CategoryOfElements.π
            (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).fiber).op ⋙
          liftedModuleSections B S hS Y G) :=
  Iso.refl _

/-- The components of `AlgebraicGeometry.Space.liftedSectionDiagramIso` are identities. -/
theorem liftedSectionDiagramIso_hom_app
    (e : ((etaleSitePoint B S hS X.1 xbar X.2).fiber.Elements)ᵒᵖ) :
    (liftedSectionDiagramIso B S hS f hf xbar G).hom.app e = 𝟙 _ :=
  rfl

/-- An étale morphism of algebraic spaces does not change the stalk of the lifted sections of a
module at a geometric point: the stalk of the étale restriction of `G` at `x̄` is the stalk of
`G` at the image of `x̄`. -/
noncomputable def etaleLiftedSectionStalkIso :
    ((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := AddCommGrpCat.{max u m})).obj
        (liftedModuleSections B S hS X ((etaleModulePullback B S hS f hf).obj G)) ≅
      ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).presheafFiber
          (A := AddCommGrpCat.{max u m})).obj
        (liftedModuleSections B S hS Y G) :=
  HasColimit.isoOfNatIso (liftedSectionDiagramIso B S hS f hf xbar G) ≪≫
    Functor.Final.colimitIso (geometricFiberPostcomp B S hS f hf xbar).op
      ((CategoryOfElements.π
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).fiber).op ⋙
        liftedModuleSections B S hS Y G)

/-- The comparison of the stalks of the lifted sections carries the image of a section over an
étale chart of `X` to its image over the composite chart of `Y`. -/
theorem etaleLiftedSectionStalkIso_toPresheafFiber
    (e : (etaleSitePoint B S hS X.1 xbar X.2).fiber.Elements) :
    (etaleSitePoint B S hS X.1 xbar X.2).toPresheafFiber e.1 e.2
          (liftedModuleSections B S hS X ((etaleModulePullback B S hS f hf).obj G)) ≫
        (etaleLiftedSectionStalkIso B S hS f hf xbar G).hom =
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).toPresheafFiber
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).1
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).2
        (liftedModuleSections B S hS Y G) := by
  show colimit.ι ((CategoryOfElements.π (etaleSitePoint B S hS X.1 xbar X.2).fiber).op ⋙
        liftedModuleSections B S hS X ((etaleModulePullback B S hS f hf).obj G)) (op e) ≫
      ((HasColimit.isoOfNatIso (liftedSectionDiagramIso B S hS f hf xbar G)).hom ≫
        (Functor.Final.colimitIso (geometricFiberPostcomp B S hS f hf xbar).op
          ((CategoryOfElements.π
              (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).fiber).op ⋙
            liftedModuleSections B S hS Y G)).hom) =
    colimit.ι ((CategoryOfElements.π
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).fiber).op ⋙
      liftedModuleSections B S hS Y G)
      (op ((geometricFiberPostcomp B S hS f hf xbar).obj e))
  rw [← Category.assoc, HasColimit.isoOfNatIso_ι_hom, liftedSectionDiagramIso_hom_app]
  refine Eq.trans (congrArg (fun g => g ≫ (Functor.Final.colimitIso
      (geometricFiberPostcomp B S hS f hf xbar).op
      ((CategoryOfElements.π
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).fiber).op ⋙
        liftedModuleSections B S hS Y G)).hom) (Category.id_comp _)) ?_
  exact Functor.Final.ι_colimitIso_hom (geometricFiberPostcomp B S hS f hf xbar).op
    ((CategoryOfElements.π
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).fiber).op ⋙
      liftedModuleSections B S hS Y G) (op e)

/-- An étale morphism of algebraic spaces does not change the stalk of a module at a geometric
point: the stalk of the étale restriction of `G` at `x̄` is the stalk of `G` at the image of
`x̄`, as an additive group. -/
noncomputable def etaleModuleStalkLargeAddEquiv :
    Stacks.moduleStalkLarge.{m} (etaleSitePoint B S hS X.1 xbar X.2)
        (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G) ≃+
      Stacks.moduleStalkLarge.{m} (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2)
        (smallEtaleRingedTopos B S hS Y).O G :=
  (Stacks.moduleStalkLargeAddEquivPresheafFiber (etaleSitePoint B S hS X.1 xbar X.2)
      (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G)).trans
    (((etaleLiftedSectionStalkIso B S hS f hf xbar G).addCommGroupIsoToAddEquiv).trans
      (Stacks.moduleStalkLargeAddEquivPresheafFiber
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2)
        (smallEtaleRingedTopos B S hS Y).O G).symm)

/-- The comparison of the stalks of a module along an étale morphism, read through the
identification of each stalk with the stalk of the lifted sections. -/
theorem etaleModuleStalkLargeAddEquiv_apply
    (z : Stacks.moduleStalkLarge.{m} (etaleSitePoint B S hS X.1 xbar X.2)
      (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G)) :
    etaleModuleStalkLargeAddEquiv B S hS f hf xbar G z =
      (Stacks.moduleStalkLargeAddEquivPresheafFiber
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2)
          (smallEtaleRingedTopos B S hS Y).O G).symm
        ((etaleLiftedSectionStalkIso B S hS f hf xbar G).addCommGroupIsoToAddEquiv
          (Stacks.moduleStalkLargeAddEquivPresheafFiber (etaleSitePoint B S hS X.1 xbar X.2)
            (smallEtaleRingedTopos B S hS X).O
            ((etaleModulePullback B S hS f hf).obj G) z)) :=
  rfl

/-- The comparison of the stalks of the lifted sections, read on the image of a section. -/
theorem etaleLiftedSectionStalkIso_toPresheafFiber_apply
    (e : (etaleSitePoint B S hS X.1 xbar X.2).fiber.Elements)
    (s : ((etaleModulePullback B S hS f hf).obj G).val.obj (op e.1)) :
    (etaleLiftedSectionStalkIso B S hS f hf xbar G).hom
        ((etaleSitePoint B S hS X.1 xbar X.2).toPresheafFiber e.1 e.2
          (liftedModuleSections B S hS X ((etaleModulePullback B S hS f hf).obj G))
          (ULift.up s)) =
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).toPresheafFiber
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).1
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).2
        (liftedModuleSections B S hS Y G) (ULift.up s) :=
  (CategoryTheory.comp_apply
      ((etaleSitePoint B S hS X.1 xbar X.2).toPresheafFiber e.1 e.2
        (liftedModuleSections B S hS X ((etaleModulePullback B S hS f hf).obj G)))
      (etaleLiftedSectionStalkIso B S hS f hf xbar G).hom (ULift.up s)).symm.trans
    (ConcreteCategory.congr_hom
      (etaleLiftedSectionStalkIso_toPresheafFiber B S hS f hf xbar G e) (ULift.up s))

/-- The comparison of the stalks of a module along an étale morphism carries the germ of a
section over an étale chart of `X` to its germ over the composite chart of `Y`. -/
theorem etaleModuleStalkLargeAddEquiv_germ
    (e : (etaleSitePoint B S hS X.1 xbar X.2).fiber.Elements)
    (s : ((etaleModulePullback B S hS f hf).obj G).val.obj (op e.1)) :
    etaleModuleStalkLargeAddEquiv B S hS f hf xbar G
        (Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 xbar X.2)
          (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G)
          e.1 e.2 s) =
      Stacks.moduleStalkLargeGerm
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2)
        (smallEtaleRingedTopos B S hS Y).O G
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).1
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).2 s :=
  (etaleModuleStalkLargeAddEquiv_apply B S hS f hf xbar G _).trans
    ((congrArg (Stacks.moduleStalkLargeAddEquivPresheafFiber
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2)
          (smallEtaleRingedTopos B S hS Y).O G).symm
        ((congrArg (etaleLiftedSectionStalkIso B S hS f hf xbar G).hom.hom
            (Stacks.moduleStalkLargeAddEquivPresheafFiber_germ
              (etaleSitePoint B S hS X.1 xbar X.2) (smallEtaleRingedTopos B S hS X).O
              ((etaleModulePullback B S hS f hf).obj G) e.1 e.2 s)).trans
          (etaleLiftedSectionStalkIso_toPresheafFiber_apply B S hS f hf xbar G e s))).trans
      (Stacks.moduleStalkLargeAddEquivPresheafFiber_symm_toPresheafFiber
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2)
        (smallEtaleRingedTopos B S hS Y).O G
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).1
        ((geometricFiberPostcomp B S hS f hf xbar).obj e).2 s))

/-- Semilinearity of the comparison of module stalks, checked on a germ. -/
private theorem etaleModuleStalkLargeAddEquiv_smul_germ
    (e : (etaleSitePoint B S hS X.1 xbar X.2).fiber.Elements)
    (a : (Stacks.commRingSheafToRingSheaf
      (smallEtaleRingedTopos B S hS X).O).obj.obj (op e.1))
    (s : ((etaleModulePullback B S hS f hf).obj G).val.obj (op e.1)) :
    etaleModuleStalkLargeAddEquiv B S hS f hf xbar G
        ((etaleSitePoint B S hS X.1 xbar X.2).toPresheafFiber e.1 e.2
            (smallEtaleRingedTopos B S hS X).O.obj a •
          Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 xbar X.2)
            (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G)
            e.1 e.2 s) =
      (etaleStalkRingIso B S hS f hf xbar).commRingCatIsoToRingEquiv
          ((etaleSitePoint B S hS X.1 xbar X.2).toPresheafFiber e.1 e.2
            (smallEtaleRingedTopos B S hS X).O.obj a) •
        etaleModuleStalkLargeAddEquiv B S hS f hf xbar G
          (Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 xbar X.2)
            (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G)
            e.1 e.2 s) := by
  have hX := Stacks.moduleStalkLargeGerm_smul (etaleSitePoint B S hS X.1 xbar X.2)
    (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G) e.1 e.2 a s
  have hY := Stacks.moduleStalkLargeGerm_smul
    (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2)
    (smallEtaleRingedTopos B S hS Y).O G
    ((geometricFiberPostcomp B S hS f hf xbar).obj e).1
    ((geometricFiberPostcomp B S hS f hf xbar).obj e).2 a s
  refine (congrArg (etaleModuleStalkLargeAddEquiv B S hS f hf xbar G) hX.symm).trans
    (((etaleModuleStalkLargeAddEquiv_germ B S hS f hf xbar G e _).trans hY).trans ?_)
  congr 1
  · exact (ConcreteCategory.congr_hom (etaleStalkRingIso_toPresheafFiber B S hS f hf xbar e) a).symm
  · exact (etaleModuleStalkLargeAddEquiv_germ B S hS f hf xbar G e s).symm

/-- The comparison of the stalks of a module along an étale morphism is semilinear over the
comparison of the stalks of the structure sheaf. -/
theorem etaleModuleStalkLargeAddEquiv_smul
    (r : ((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X).O.obj)
    (z : Stacks.moduleStalkLarge.{m} (etaleSitePoint B S hS X.1 xbar X.2)
      (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G)) :
    etaleModuleStalkLargeAddEquiv B S hS f hf xbar G (r • z) =
      (etaleStalkRingIso B S hS f hf xbar).commRingCatIsoToRingEquiv r •
        etaleModuleStalkLargeAddEquiv B S hS f hf xbar G z :=
  Stacks.semilinear_of_semilinear_moduleStalkLargeGerm (etaleSitePoint B S hS X.1 xbar X.2)
    (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G)
    (etaleStalkRingIso B S hS f hf xbar).commRingCatIsoToRingEquiv.toRingHom
    (etaleModuleStalkLargeAddEquiv B S hS f hf xbar G).toAddMonoidHom
    (fun U x a s => etaleModuleStalkLargeAddEquiv_smul_germ B S hS f hf xbar G
      (Functor.elementsMk _ U x) a s) r z

end Etale

/-! ### Stacks 0CUU -/

/-- Weak association to a module is invariant under an isomorphism of modules. -/
theorem isWeaklyAssociatedPoint_congr {F F' : Modules.{u, m} B S hS X.1 X.2} (α : F ≅ F')
    (x : points B S hS X.1) :
    IsWeaklyAssociatedPoint B S hS X F x ↔ IsWeaklyAssociatedPoint B S hS X F' x := by
  rw [isWeaklyAssociatedPoint_iff_moduleStalkLarge,
    isWeaklyAssociatedPoint_iff_moduleStalkLarge]
  refine exists_congr fun xbar => and_congr_right fun _ => ?_
  exact isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv
    (RingEquiv.refl _)
    (Stacks.moduleStalkLargeCongr (etaleSitePoint B S hS X.1 xbar X.2)
      (smallEtaleRingedTopos B S hS X).O α)
    (Stacks.moduleStalkLargeCongr_smul (etaleSitePoint B S hS X.1 xbar X.2)
      (smallEtaleRingedTopos B S hS X).O α)

/-- **Stacks 0CUU**, for étale restriction of sections. A point of `X` is weakly associated to
the étale restriction of an `𝒪_Y`-module `G` exactly when its image is weakly associated
to `G`. -/
theorem isWeaklyAssociatedPoint_etaleModulePullback_iff (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (G : Modules.{u, m} B S hS Y.1 Y.2)
    (x : points B S hS X.1) :
    IsWeaklyAssociatedPoint B S hS X ((etaleModulePullback B S hS f hf).obj G) x ↔
      IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X.1 f.hom x) := by
  rw [isWeaklyAssociatedPoint_iff_moduleStalkLarge,
    isWeaklyAssociatedPoint_iff_moduleStalkLarge]
  have key : ∀ xbar : GeometricPoint B S hS X.1,
      IsWeaklyAssociatedPrime
          (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
            (smallEtaleRingedTopos B S hS X).O.obj)
          (Stacks.moduleStalkLarge.{m} (etaleSitePoint B S hS X.1 xbar X.2)
            (smallEtaleRingedTopos B S hS X).O ((etaleModulePullback B S hS f hf).obj G))
          (IsLocalRing.maximalIdeal _) ↔
        IsWeaklyAssociatedPrime
          (((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2).presheafFiber
            (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O.obj)
          (Stacks.moduleStalkLarge.{m}
            (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom xbar) Y.2)
            (smallEtaleRingedTopos B S hS Y).O G)
          (IsLocalRing.maximalIdeal _) := fun xbar =>
    isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv
      (etaleStalkRingIso B S hS f hf xbar).commRingCatIsoToRingEquiv
      (etaleModuleStalkLargeAddEquiv B S hS f hf xbar G)
      (etaleModuleStalkLargeAddEquiv_smul B S hS f hf xbar G)
  constructor
  · rintro ⟨xbar, hxbar, h⟩
    exact ⟨geometricPointMap f.hom xbar, by rw [← hxbar]; rfl, (key xbar).1 h⟩
  · rintro ⟨ybar, hybar, h⟩
    obtain ⟨xbar, hxbar, himg⟩ := exists_geometricPoint_lift_of_isEtale B S hS X.2 Y.2
      f.hom hf ybar x hybar.symm
    exact ⟨xbar, hxbar, (key xbar).2
      ((Subtype.ext himg : geometricPointMap f.hom xbar = ybar) ▸ h)⟩

/-- **Weak association along an étale pullback.** Let `f : X ⟶ Y` be an étale morphism of
algebraic spaces over a scheme `S`, let `G` be an `𝒪_Y`-module and let `x` be a point of `X` with
image `y`. Then `x` is weakly associated to `f^*G` if and only if `y` is weakly associated to
`G`. -/
@[stacks 0CUU]
theorem isWeaklyAssociatedPoint_modulePullback_iff (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (x : points B S hS X.1) :
    IsWeaklyAssociatedPoint B S hS X ((modulePullback B S hS f).obj G) x ↔
      IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X.1 f.hom x) :=
  (isWeaklyAssociatedPoint_congr B S hS
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).app G) x).trans
    (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS f hf G x)

/-- **The weakly associated points of an algebraic space étale over another are the inverse
image of those of the target.** A point `x` of `X` is a weakly associated point of `X` if and
only if its image under the étale morphism `f : X ⟶ Y` is a weakly associated point of `Y`. -/
theorem mem_weaklyAssociatedPointsOfSpace_iff_of_isEtale (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (x : points B S hS X.1) :
    x ∈ weaklyAssociatedPointsOfSpace B S hS X ↔
      pointsMap B S hS X.1 f.hom x ∈ weaklyAssociatedPointsOfSpace B S hS Y :=
  (isWeaklyAssociatedPoint_congr B S hS (modulePullbackUnitIso B S hS f).symm x).trans
    (isWeaklyAssociatedPoint_modulePullback_iff B S hS f hf
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) x)

/-- **The weakly associated points of an algebraic space étale over another, as an equality of
sets of points.** The set-level form of
`AlgebraicGeometry.Space.mem_weaklyAssociatedPointsOfSpace_iff_of_isEtale`. -/
theorem weaklyAssociatedPointsOfSpace_eq_preimage_of_isEtale (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    weaklyAssociatedPointsOfSpace B S hS X =
      pointsMap B S hS X.1 f.hom ⁻¹' weaklyAssociatedPointsOfSpace B S hS Y :=
  Set.ext fun x => mem_weaklyAssociatedPointsOfSpace_iff_of_isEtale B S hS f hf x

end AlgebraicGeometry.Space

end
