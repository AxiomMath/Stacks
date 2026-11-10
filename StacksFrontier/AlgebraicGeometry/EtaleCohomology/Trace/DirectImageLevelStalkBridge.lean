module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveSpecializationInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicIntegralDirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.FibreStalk

/-!
# The stalk of a direct image, level by level, on the two small étale sites

Let `f : X ⟶ Y` be a morphism of the big étale site, `F` an ℓ-adic sheaf on `Y`, `F'` one on `X`
and `χ : f⁻¹F → F'` a morphism. At level `n` the adjunct of `χₙ` is a map `Fₙ → f_* F'ₙ` of
sheaves of `ℤ/ℓⁿ⁺¹`-modules on the bounded small étale site of `Y`; its stalk at a geometric point
`s̄` is `Stacks.EtaleCohomology.levelAdjunctStalkMap`. Reading `F'ₙ` as a sheaf of
`ℤ_ℓ`-modules and the direct image on Mathlib's small étale site
(`Stacks.EtaleCohomology.etaleModuleDirectImage`), the target becomes the stalk at `s̄` of
`f_*(F'ₙ)` there (`Stacks.EtaleCohomology.directImageStalkBridge`), and the composite is
`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap`. This file records how that composite behaves:

* on germs (`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap_germ`);
* with respect to the transition maps
  (`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap_transition`);
* with respect to morphisms on `X` and on `Y`
  (`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap_comp`,
  `Stacks.EtaleCohomology.levelAdjunctPadicStalkMap_inverseImageMap_comp`);
* with respect to endomorphisms of `s̄`, e.g. the geometric Frobenius
  (`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap_stalkEnd`).

These are the facts needed to compare the stalk at a missing point `ȳ` of a curve of an ℓ-adic
sheaf `G` with the stalks of `j_*` of the levels of a lisse sheaf on the complement, in the
specialization step of Laumon's degeneration argument
(`Stacks.EtaleCohomology.CurveSpecializationMapInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.directImageStalkBridge`
* `Stacks.EtaleCohomology.levelAdjunctStalkMap`
* `Stacks.EtaleCohomology.levelAdjunctPadicStalkMap`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.SmallEtale.LAdicSheaf

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

section Bridge

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.1)
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The stalk of a direct image on the two small étale sites.** For `f : X ⟶ Y` in the big
étale site and a geometric point `s̄` of `Y`, the stalk at `s̄` of the direct image on the bounded
small étale site is the stalk at `s̄` of the direct image on Mathlib's small étale site, naturally
in the sheaf of `ℤ_ℓ`-modules on `X`: the composite of the comparison of stalk functors
`AlgebraicGeometry.sheafEquivCompSheafFiberIso` and of direct images
`AlgebraicGeometry.SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso`. -/
public def directImageStalkBridge :
    B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ]) ⋙
        etaleModuleStalkFunctor.{u, u + 1, 0} B Y ℤ_[ℓ] s ≅
      (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor ⋙
        etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f) ⋙
          (Scheme.pointSmallEtale s.hom).sheafFiber :=
  Functor.isoWhiskerLeft _ (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B Y ℤ_[ℓ] s).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B f _) _ ≪≫
    Functor.associator _ _ _

/-- The comparison of stalks of direct images, componentwise. -/
public theorem directImageStalkBridge_hom_app
    (F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} ℤ_[ℓ])) :
    (directImageStalkBridge f s ℓ).hom.app F =
      (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B Y ℤ_[ℓ] s).inv.app
          ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj F) ≫
        (Scheme.pointSmallEtale s.hom).sheafFiber.map
          ((SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B f _).hom.app F) := by
  simp [directImageStalkBridge]

/-- **The comparison of stalks of direct images commutes with the endomorphisms of the geometric
point**: the map of Tag 04FN on the bounded site corresponds to the map of stalk functors of
Mathlib's points. -/
public theorem directImageStalkBridge_hom_app_pointHom (a : GeometricPoint.Hom s s)
    (F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} ℤ_[ℓ])) :
    (directImageStalkBridge f s ℓ).hom.app F ≫
        (GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom Y.1 a)).app
          ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).obj
            ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj F)) =
      (geometricPointStalkMap B Y.1 Y.2 a (ModuleCat.{u + 1} ℤ_[ℓ])).app
          ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj F).obj ≫
        (directImageStalkBridge f s ℓ).hom.app F := by
  let P := (B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj F
  let T := GrothendieckTopology.Point.Hom.sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])
    (smallEtalePointHom Y.1 a)
  let L := (SmallEtale.sheafEquiv B Y.1 Y.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor
  let BC := (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B f
    (ModuleCat.{u + 1} ℤ_[ℓ])).hom.app F
  have h : (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B Y ℤ_[ℓ] s).inv.app P ≫ T.app (L.obj P) =
      (geometricPointStalkMap B Y.1 Y.2 a (ModuleCat.{u + 1} ℤ_[ℓ])).app P.obj ≫
        (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B Y ℤ_[ℓ] s).inv.app P :=
    NatTrans.congr_app (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B Y ℤ_[ℓ] a) P
  have hn : (Scheme.pointSmallEtale s.hom).sheafFiber.map BC ≫
      T.app ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).obj
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj F)) =
      T.app (L.obj P) ≫ (Scheme.pointSmallEtale s.hom).sheafFiber.map BC :=
    T.naturality BC
  rw [directImageStalkBridge_hom_app, Category.assoc]
  change _ ≫ (Scheme.pointSmallEtale s.hom).sheafFiber.map BC ≫ _ = _
  rw [hn, ← Category.assoc, h, Category.assoc]

end Bridge

section Germs

variable {B : BigEtaleSite.{u}} (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **Additive maps out of an étale stalk agreeing on germs are equal.** -/
public theorem etaleStalk_addMonoidHom_ext {R : Type} [Ring R]
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{u + 1} R) {M : Type (u + 1)} [AddCommGroup M]
    {g₁ g₂ : (etaleStalk B S hS s P : ModuleCat.{u + 1} R) →+ M}
    (h : ∀ (j : (geometricPointFiber B S hS s).Elementsᵒᵖ)
      (x : P.obj ((Functor.Elements.π (geometricPointFiber B S hS s)).op.obj j)),
      g₁ ((colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ P) j).hom x) =
        g₂ ((colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ P) j).hom x)) :
    g₁ = g₂ := by
  have hc := (isColimitOfPreserves (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
    (colimit.isColimit ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ P)))
  exact congrArg AddCommGrpCat.Hom.hom (hc.hom_ext (W := AddCommGrpCat.of M)
    (f := AddCommGrpCat.ofHom g₁) (f' := AddCommGrpCat.ofHom g₂) fun j => by
      ext x
      exact h j x)

/-- Additive maps out of an étale stalk agreeing on germs agree on every element. -/
private theorem etaleStalk_addMonoidHom_apply_eq {R : Type} [Ring R]
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{u + 1} R) {M : Type (u + 1)} [AddCommGroup M]
    {g₁ g₂ : (etaleStalk B S hS s P : ModuleCat.{u + 1} R) →+ M}
    (h : ∀ (j : (geometricPointFiber B S hS s).Elementsᵒᵖ)
      (x : P.obj ((Functor.Elements.π (geometricPointFiber B S hS s)).op.obj j)),
      g₁ ((colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ P) j).hom x) =
        g₂ ((colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ P) j).hom x))
    (w : (etaleStalk B S hS s P : ModuleCat.{u + 1} R)) : g₁ w = g₂ w :=
  DFunLike.congr_fun (etaleStalk_addMonoidHom_ext S hS s P h) w

end Germs

section Level

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.1) {ℓ : ℕ}
  [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- **The stalk at `s̄` of the adjunct `Fₙ → f_* F'ₙ` of `χₙ : f⁻¹ Fₙ → F'ₙ`**, for a morphism
`χ : f⁻¹ F → F'` of ℓ-adic sheaves. For `χ = 𝟙` it is the stalk of the unit,
`Stacks.EtaleCohomology.levelUnitStalkMap` (`Stacks.EtaleCohomology.levelAdjunctStalkMap_id`). -/
public def levelAdjunctStalkMap (F : LAdicSheaf.{u, u + 1} B Y ℓ) (F' : LAdicSheaf.{u, u + 1} B X ℓ)
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (n : ℕ) :
    finiteLevelStalk B Y ℓ F s n ⟶
      etaleStalk B Y.1 Y.2 s ((levelPushforward f n).obj (F'.level n)).obj :=
  colim.map (Functor.whiskerLeft ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op)
    (((levelAdjunction f n).homEquiv _ _) (χ.app n)).hom)

/-- For `χ = 𝟙` the stalk of the adjunct is the stalk of the unit. -/
public theorem levelAdjunctStalkMap_id (F : LAdicSheaf.{u, u + 1} B Y ℓ) (n : ℕ) :
    levelAdjunctStalkMap f s F _ (𝟙 _) n = levelUnitStalkMap f F s n := by
  change colim.map (Functor.whiskerLeft _
    (((levelAdjunction f n).homEquiv _ _) (𝟙 ((levelPullback f n).obj (F.level n)))).hom) = _
  rw [Adjunction.homEquiv_id]
  rfl

/-- **The stalk at `s̄` of `Fₙ → f_* F'ₙ`, landing in the stalk of the direct image on Mathlib's
small étale site of the level `F'ₙ` read as a sheaf of `ℤ_ℓ`-modules**:
`Stacks.EtaleCohomology.levelAdjunctStalkMap` followed by the commutation of the stalk with
restriction of scalars and `Stacks.EtaleCohomology.directImageStalkBridge`. -/
public def levelAdjunctPadicStalkMap (F : LAdicSheaf.{u, u + 1} B Y ℓ)
    (F' : LAdicSheaf.{u, u + 1} B X ℓ)
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (n : ℕ) :
    (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1))).obj
        (finiteLevelStalk B Y ℓ F s n) ⟶
      (Scheme.pointSmallEtale s.hom).sheafFiber.obj
        ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).obj
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
            (LAdicSheaf.padicLevel B X ℓ F' n))) :=
  (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1))).map
      (levelAdjunctStalkMap f s F F' χ n) ≫
    (preservesColimitIso (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1)))
      ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
        ((levelPushforward f n).obj (F'.level n)).obj)).hom ≫
    (directImageStalkBridge f s ℓ).hom.app (LAdicSheaf.padicLevel B X ℓ F' n)

/-- **The composite on germs**: the germ of a section `x` goes to the image under
`Stacks.EtaleCohomology.directImageStalkBridge` of the germ of the image of `x` by the adjunct. -/
public theorem levelAdjunctPadicStalkMap_germ (F : LAdicSheaf.{u, u + 1} B Y ℓ)
    (F' : LAdicSheaf.{u, u + 1} B X ℓ)
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (n : ℕ)
    (j : (geometricPointFiber B Y.1 Y.2 s).Elementsᵒᵖ)
    (x : (F.level n).obj.obj ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op.obj j)) :
    (levelAdjunctPadicStalkMap f s F F' χ n).hom
        ((colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
          (F.level n).obj) j).hom x) =
      ((directImageStalkBridge f s ℓ).hom.app (LAdicSheaf.padicLevel B X ℓ F' n)).hom
        ((colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
          ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj
            (LAdicSheaf.padicLevel B X ℓ F' n)).obj) j).hom
          (((((levelAdjunction f n).homEquiv _ _) (χ.app n)).hom.app
            ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op.obj j)).hom x)) := by
  have h1 := ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft
    ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op)
    (((levelAdjunction f n).homEquiv _ _) (χ.app n)).hom) j) x
  have h2 := ConcreteCategory.congr_hom (ι_preservesColimitIso_hom
    (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1)))
    ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
      ((levelPushforward f n).obj (F'.level n)).obj) j)
    (((((levelAdjunction f n).homEquiv _ _) (χ.app n)).hom.app
      ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op.obj j)).hom x)
  change ((directImageStalkBridge f s ℓ).hom.app (LAdicSheaf.padicLevel B X ℓ F' n)).hom
    ((preservesColimitIso
      (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1)))
      ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
        ((levelPushforward f n).obj (F'.level n)).obj)).hom.hom
      ((levelAdjunctStalkMap f s F F' χ n).hom ((colimit.ι
        ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙ (F.level n).obj) j).hom
          x))) = _
  refine congrArg _ ?_
  exact (congrArg (preservesColimitIso (ModuleCat.restrictScalars.{u + 1}
    (PadicInt.toZModPow (p := ℓ) (n + 1))) ((Functor.Elements.π
      (geometricPointFiber B Y.1 Y.2 s)).op ⋙
        ((levelPushforward f n).obj (F'.level n)).obj)).hom.hom h1).trans h2

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.obj] [AlgebraicGeometry.IsNoetherian Y.obj] in
/-- **The comparison of stalks of direct images is natural, on germs.** -/
public theorem directImageStalkBridge_germ_naturality
    {F₁ F₂ : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} ℤ_[ℓ])} (g : F₁ ⟶ F₂)
    (j : (geometricPointFiber B Y.1 Y.2 s).Elementsᵒᵖ)
    (y : ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj F₁).obj.obj
      ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op.obj j)) :
    ((Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).map
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map g))).hom
        (((directImageStalkBridge f s ℓ).hom.app F₁).hom
          ((colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
            ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj F₁).obj) j).hom y)) =
      ((directImageStalkBridge f s ℓ).hom.app F₂).hom
        ((colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
            ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj F₂).obj) j).hom
          ((((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).map g).hom.app
            ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op.obj j)).hom y)) := by
  have h := ConcreteCategory.congr_hom ((directImageStalkBridge f s ℓ).hom.naturality g)
    ((colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
      ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj F₁).obj) j).hom y)
  have h2 := ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft
    ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op)
      ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).map g).hom) j) y
  exact h.symm.trans (congrArg ((directImageStalkBridge f s ℓ).hom.app F₂).hom h2)

/-- **The transition maps on germs.** -/
public theorem stalkTransition_germ (F : LAdicSheaf.{u, u + 1} B Y ℓ) (n : ℕ)
    (j : (geometricPointFiber B Y.1 Y.2 s).Elementsᵒᵖ)
    (x : (F.level (n + 1)).obj.obj
      ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op.obj j)) :
    LAdicSheaf.stalkTransition B Y ℓ F s n
        ((colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
          (F.level (n + 1)).obj) j).hom x) =
      (colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
          (F.level n).obj) j).hom
        (((F.transition n).hom.app
          ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op.obj j)).hom x) := by
  have h1 := ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft
    ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op) (F.transition n).hom) j) x
  have h2 := ConcreteCategory.congr_hom (ι_preservesColimitIso_inv
    (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
    ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙ (F.level n).obj) j)
    (((F.transition n).hom.app
      ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op.obj j)).hom x)
  exact (congrArg (preservesColimitIso (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
    ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
      (F.level n).obj)).inv.hom h1).trans h2

/-- **The adjuncts commute with the transition maps**, as maps of sheaves `F_{n+1} → f_* F'ₙ`. -/
public theorem levelAdjunct_transition (F : LAdicSheaf.{u, u + 1} B Y ℓ)
    (F' : LAdicSheaf.{u, u + 1} B X ℓ)
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (n : ℕ) :
    ((levelAdjunction f (n + 1)).homEquiv _ _) (χ.app (n + 1)) ≫
        (levelPushforward f (n + 1)).map (F'.transition n) =
      F.transition n ≫ (levelRestrict Y n).map (((levelAdjunction f n).homEquiv _ _) (χ.app n)) ≫
        (levelPushforwardRestrictIso f n).inv.app _ := by
  have hχ : χ.app (n + 1) ≫ F'.transition n =
      inverseImageTransition f F n ≫ (levelRestrict X n).map (χ.app n) := χ.naturality n
  have e1 : ((levelAdjunction f (n + 1)).homEquiv _ _) (χ.app (n + 1)) ≫
      (levelPushforward f (n + 1)).map (F'.transition n) =
      ((levelAdjunction f (n + 1)).homEquiv _ _) (χ.app (n + 1) ≫ F'.transition n) :=
    (Adjunction.homEquiv_naturality_right _ _ _).symm
  have e3 : ((levelAdjunction f (n + 1)).homEquiv _ _)
      (inverseImageTransition f F n ≫ (levelRestrict X n).map (χ.app n)) =
      ((levelAdjunction f (n + 1)).homEquiv _ _) (inverseImageTransition f F n) ≫
        (levelPushforward f (n + 1)).map ((levelRestrict X n).map (χ.app n)) :=
    Adjunction.homEquiv_naturality_right _ _ _
  have e4 : ((levelAdjunction f (n + 1)).homEquiv _ _) (inverseImageTransition f F n) =
      F.transition n ≫ (levelRestrict Y n).map ((levelAdjunction f n).unit.app (F.level n)) ≫
        (levelPushforwardRestrictIso f n).inv.app _ :=
    Equiv.apply_symm_apply _ _
  have e2 : ((levelAdjunction f (n + 1)).homEquiv _ _) (χ.app (n + 1) ≫ F'.transition n) =
      ((levelAdjunction f (n + 1)).homEquiv _ _)
        (inverseImageTransition f F n ≫ (levelRestrict X n).map (χ.app n)) :=
    congrArg (⇑((levelAdjunction f (n + 1)).homEquiv _ _)) hχ
  refine e1.trans (e2.trans (e3.trans ?_))
  rw [e4]
  rfl

/-- **`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap` commutes with the transition maps.** -/
public theorem levelAdjunctPadicStalkMap_transition (F : LAdicSheaf.{u, u + 1} B Y ℓ)
    (F' : LAdicSheaf.{u, u + 1} B X ℓ)
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (n : ℕ)
    (w : finiteLevelStalk B Y ℓ F s (n + 1)) :
    (levelAdjunctPadicStalkMap f s F F' χ n).hom (LAdicSheaf.stalkTransition B Y ℓ F s n w) =
      ((Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).map
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
            (LAdicSheaf.padicTransition B X ℓ F' n)))).hom
        ((levelAdjunctPadicStalkMap f s F F' χ (n + 1)).hom w) := by
  let P₀ := levelAdjunctPadicStalkMap f s F F' χ n
  let P₁ := levelAdjunctPadicStalkMap f s F F' χ (n + 1)
  let T := (Scheme.pointSmallEtale s.hom).sheafFiber.map
    ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).map
      ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicTransition B X ℓ F' n)))
  refine etaleStalk_addMonoidHom_apply_eq Y.1 Y.2 s (F.level (n + 1)).obj
    (g₁ := P₀.hom.toAddMonoidHom.comp (LAdicSheaf.stalkTransition B Y ℓ F s n).toAddMonoidHom)
    (g₂ := T.hom.toAddMonoidHom.comp P₁.hom.toAddMonoidHom) (fun j x => ?_) w
  have hsec := (congrArg (fun g => (g.hom.app _).hom x)
    (levelAdjunct_transition f F F' χ n)).symm
  change P₀.hom (LAdicSheaf.stalkTransition B Y ℓ F s n _) = T.hom (P₁.hom _)
  rw [stalkTransition_germ]
  refine (levelAdjunctPadicStalkMap_germ f s F F' χ n j _).trans ?_
  rw [levelAdjunctPadicStalkMap_germ f s F F' χ (n + 1) j]
  erw [hsec]
  exact (directImageStalkBridge_germ_naturality f s (LAdicSheaf.padicTransition B X ℓ F' n) j
    _).symm

/-- **`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap` is natural in the target.** -/
public theorem levelAdjunctPadicStalkMap_comp (F : LAdicSheaf.{u, u + 1} B Y ℓ)
    {F' F'' : LAdicSheaf.{u, u + 1} B X ℓ}
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (θ : F' ⟶ F'') (n : ℕ)
    (w : finiteLevelStalk B Y ℓ F s n) :
    (levelAdjunctPadicStalkMap f s F F'' (χ ≫ θ) n).hom w =
      ((Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).map
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
            (LAdicSheaf.padicLevelMap θ n)))).hom
        ((levelAdjunctPadicStalkMap f s F F' χ n).hom w) := by
  let P₀ := levelAdjunctPadicStalkMap f s F F'' (χ ≫ θ) n
  let P₁ := levelAdjunctPadicStalkMap f s F F' χ n
  let T := (Scheme.pointSmallEtale s.hom).sheafFiber.map
    ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).map
      ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicLevelMap θ n)))
  refine etaleStalk_addMonoidHom_apply_eq Y.1 Y.2 s (F.level n).obj
    (g₁ := P₀.hom.toAddMonoidHom) (g₂ := T.hom.toAddMonoidHom.comp P₁.hom.toAddMonoidHom)
    (fun j x => ?_) w
  have e : ((levelAdjunction f n).homEquiv _ _) ((χ ≫ θ).app n) =
      ((levelAdjunction f n).homEquiv _ _) (χ.app n) ≫ (levelPushforward f n).map (θ.app n) :=
    Adjunction.homEquiv_naturality_right _ _ _
  have hsec := congrArg (fun g => (g.hom.app _).hom x) e
  change P₀.hom _ = T.hom (P₁.hom _)
  rw [levelAdjunctPadicStalkMap_germ, levelAdjunctPadicStalkMap_germ, hsec]
  exact (directImageStalkBridge_germ_naturality f s (LAdicSheaf.padicLevelMap θ n) j _).symm

/-- **`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap` is natural in the source.** -/
public theorem levelAdjunctPadicStalkMap_inverseImageMap_comp {F₁ F : LAdicSheaf.{u, u + 1} B Y ℓ}
    {F' : LAdicSheaf.{u, u + 1} B X ℓ} (ζ : F₁ ⟶ F)
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (n : ℕ)
    (w : finiteLevelStalk B Y ℓ F₁ s n) :
    (levelAdjunctPadicStalkMap f s F₁ F'
        (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap f ζ ≫ χ) n).hom w =
      (levelAdjunctPadicStalkMap f s F F' χ n).hom ((finiteLevelStalkMap ζ s n).hom w) := by
  let P₀ := levelAdjunctPadicStalkMap f s F₁ F'
    (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap f ζ ≫ χ) n
  let P₁ := levelAdjunctPadicStalkMap f s F F' χ n
  refine etaleStalk_addMonoidHom_apply_eq Y.1 Y.2 s (F₁.level n).obj
    (g₁ := P₀.hom.toAddMonoidHom)
    (g₂ := P₁.hom.toAddMonoidHom.comp (finiteLevelStalkMap ζ s n).hom.toAddMonoidHom)
    (fun j x => ?_) w
  have hm := ConcreteCategory.congr_hom (ι_finiteLevelStalkMap ζ s n j) x
  have e : ((levelAdjunction f n).homEquiv _ _)
      ((AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap f ζ ≫ χ).app n) =
      ζ.app n ≫ ((levelAdjunction f n).homEquiv _ _) (χ.app n) :=
    Adjunction.homEquiv_naturality_left _ _ _
  have hsec := congrArg (fun g => (g.hom.app _).hom x) e
  change P₀.hom _ = P₁.hom ((finiteLevelStalkMap ζ s n).hom _)
  rw [levelAdjunctPadicStalkMap_germ f s F₁ F' _ n j]
  erw [hsec]
  exact (levelAdjunctPadicStalkMap_germ f s F F' χ n j _).symm.trans (congrArg P₁.hom hm.symm)

/-- **`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap` commutes with the endomorphisms of the
geometric point**, e.g. the geometric Frobenius: the action of Tag 04FN on the stalk of `Fₙ`
goes to the action of the corresponding endomorphism of Mathlib's point. -/
public theorem levelAdjunctPadicStalkMap_stalkEnd (F : LAdicSheaf.{u, u + 1} B Y ℓ)
    (F' : LAdicSheaf.{u, u + 1} B X ℓ)
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (n : ℕ)
    (a : GeometricPoint.Hom s s) (w : finiteLevelStalk B Y ℓ F s n) :
    (levelAdjunctPadicStalkMap f s F F' χ n).hom ((finiteLevelStalkEnd B Y ℓ F a n).hom w) =
      ((GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom Y.1 a)).app
        ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).obj
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
            (LAdicSheaf.padicLevel B X ℓ F' n)))).hom
        ((levelAdjunctPadicStalkMap f s F F' χ n).hom w) := by
  let P₁ := levelAdjunctPadicStalkMap f s F F' χ n
  let T := (GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom Y.1 a)).app
    ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f)).obj
      ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
        (LAdicSheaf.padicLevel B X ℓ F' n)))
  let Br := (directImageStalkBridge f s ℓ).hom.app (LAdicSheaf.padicLevel B X ℓ F' n)
  refine etaleStalk_addMonoidHom_apply_eq Y.1 Y.2 s (F.level n).obj
    (g₁ := P₁.hom.toAddMonoidHom.comp (finiteLevelStalkEnd B Y ℓ F a n).hom.toAddMonoidHom)
    (g₂ := T.hom.toAddMonoidHom.comp P₁.hom.toAddMonoidHom) (fun j x => ?_) w
  have hpre := ConcreteCategory.congr_hom (colimit.ι_pre
    ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙ (F.level n).obj)
    (neighborhoodFunctor B Y.1 Y.2 a).op j) x
  have hpre' := ConcreteCategory.congr_hom (colimit.ι_pre
    ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
      ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj
        (LAdicSheaf.padicLevel B X ℓ F' n)).obj)
    (neighborhoodFunctor B Y.1 Y.2 a).op j)
    ((((levelAdjunction f n).homEquiv _ _) (χ.app n)).hom.app _ |>.hom x)
  have hb := ConcreteCategory.congr_hom (directImageStalkBridge_hom_app_pointHom f s ℓ a
    (LAdicSheaf.padicLevel B X ℓ F' n))
    ((colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
      ((B.smallPushforward f (ModuleCat.{u + 1} ℤ_[ℓ])).obj
        (LAdicSheaf.padicLevel B X ℓ F' n)).obj) j).hom
      ((((levelAdjunction f n).homEquiv _ _) (χ.app n)).hom.app _ |>.hom x))
  exact (congrArg P₁.hom hpre).trans
    ((levelAdjunctPadicStalkMap_germ f s F F' χ n
      ((neighborhoodFunctor B Y.1 Y.2 a).op.obj j) x).trans
    ((congrArg Br.hom hpre').symm.trans
    (hb.symm.trans (congrArg T.hom (levelAdjunctPadicStalkMap_germ f s F F' χ n j x).symm))))

/-- Multiplication by `k` on an ℓ-adic sheaf acts on the level stalks by multiplication by
`k`. -/
public theorem finiteLevelStalkMap_nsmul_id_apply (F : LAdicSheaf.{u, u + 1} B Y ℓ) (n k : ℕ)
    (w : finiteLevelStalk B Y ℓ F s n) :
    (finiteLevelStalkMap (k • 𝟙 F) s n).hom w = k • w := by
  induction k with
  | zero =>
    rw [zero_nsmul, finiteLevelStalkMap_zero, zero_nsmul]
    rfl
  | succ k ih =>
    rw [succ_nsmul, finiteLevelStalkMap_add, ModuleCat.hom_add, LinearMap.add_apply, ih,
      finiteLevelStalkMap_id, ModuleCat.hom_id, LinearMap.id_apply, succ_nsmul]

/-- **`Stacks.EtaleCohomology.levelAdjunctPadicStalkMap` of `k • χ` is `k` times that of `χ`.** -/
public theorem levelAdjunctPadicStalkMap_nsmul (F : LAdicSheaf.{u, u + 1} B Y ℓ)
    (F' : LAdicSheaf.{u, u + 1} B X ℓ)
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (n k : ℕ)
    (w : finiteLevelStalk B Y ℓ F s n) :
    (levelAdjunctPadicStalkMap f s F F' (k • χ) n).hom w =
      k • (levelAdjunctPadicStalkMap f s F F' χ n).hom w := by
  have e0 : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap f (k • 𝟙 F) = k • 𝟙 _ := by
    change (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageFunctor f).map (k • 𝟙 F) = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have e : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap f (k • 𝟙 F) ≫ χ = k • χ := by
    rw [e0, Preadditive.nsmul_comp, Category.id_comp]
  rw [← e, levelAdjunctPadicStalkMap_inverseImageMap_comp, finiteLevelStalkMap_nsmul_id_apply]
  exact map_nsmul (levelAdjunctPadicStalkMap f s F F' χ n).hom k w

/-- **The kernel of `Stacks.EtaleCohomology.levelAdjunctPadicStalkMap` is that of
`Stacks.EtaleCohomology.levelAdjunctStalkMap`**: the remaining steps are isomorphisms. -/
public theorem levelAdjunctStalkMap_eq_zero_of_padic (F : LAdicSheaf.{u, u + 1} B Y ℓ)
    (F' : LAdicSheaf.{u, u + 1} B X ℓ)
    (χ : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F ⟶ F') (n : ℕ)
    (w : finiteLevelStalk B Y ℓ F s n) (h : (levelAdjunctPadicStalkMap f s F F' χ n).hom w = 0) :
    (levelAdjunctStalkMap f s F F' χ n).hom w = 0 := by
  have i2 := ((directImageStalkBridge f s ℓ).app
    (LAdicSheaf.padicLevel B X ℓ F' n)).toLinearEquiv.injective
  have i1 := (preservesColimitIso
    (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1)))
      ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
        ((levelPushforward f n).obj (F'.level n)).obj)).toLinearEquiv.injective
  exact i1 ((i2 (h.trans (map_zero _).symm)).trans (map_zero _).symm)

end Level

end Stacks.EtaleCohomology

end
