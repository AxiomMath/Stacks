module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardModulesTransportMonoidal
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.DenseSubsiteMorphism

/-!
# A morphism of algebraic spaces on the equi-universe models

Let `g : X ⟶ Y` be a morphism of algebraic spaces. The small étale ringed topoi of `X` and `Y`
have their sites one universe above their morphisms; the equi-universe models
`AlgebraicGeometry.Space.smallEtaleModelRingedSite` do not. This file attaches to `g` a
morphism of ringed topoi `g_m` between the two models, together with the commutative square

```
  model(X) --g_m--> model(Y)
     |                 |
    π_X               π_Y
     v                 v
   X_étale ---g---> Y_étale
```

in the sense of Stacks 04IC (the two composites are 2-isomorphic), where `π` is the morphism
`AlgebraicGeometry.Space.smallEtaleModelRingedToposHom` whose derived pullback is the derived
equivalence with the model.

The morphism `g_m` is `ρ_Y ∘ g ∘ π_X`, for `ρ_Y : Y_étale ⟶ model(Y)` the morphism of ringed
topoi of the functor of the model equivalence, a dense subsite inclusion, with the identity as
structure map (the structure sheaf of the model is the direct image of that of `Y` along it).
The 2-isomorphism `π_Y ∘ ρ_Y ≅ id` is the counit of the model equivalence.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleModelInverseRingedToposHom`: `ρ_Y`.
* `AlgebraicGeometry.Space.smallEtaleModelPullbackRingedToposHom`: `g_m`.
* `AlgebraicGeometry.Space.smallEtaleModelPullbackSquarePushforwardIso`: the 2-isomorphism of
  the square, on direct images of sheaves of sets.

## Main results

* `AlgebraicGeometry.Space.smallEtaleModelPullbackSquare_fSharpRing`: the 2-isomorphism carries
  the structure map of one composite to that of the other.

## References

* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of ringed sites from the small étale site of `X` to its model**: the functor
of the model equivalence, a dense subsite inclusion, with the identity as structure map, the
structure sheaf of the model being the direct image of that of `X` along it. -/
def smallEtaleModelInverseRingedSiteHom (X : AlgebraicSpaces B S hS) :
    RingedSite.HomGeneral (smallEtaleRingedSite B S hS X.1 X.2)
      (smallEtaleModelRingedSite B S hS X.1 X.2) :=
  letI : ∀ x, HasInitial
      (StructuredArrow x (smallEtaleModelEquivalence B S hS X.1).functor.op) :=
    isRightAdjoint_iff_hasInitial_structuredArrow.1 inferInstance
  letI : ∀ x, HasLimitsOfShape
      (StructuredArrow x (smallEtaleModelEquivalence B S hS X.1).functor.op) (Type u) :=
    fun _ => ⟨fun _ => inferInstance⟩
  let h : IsMorphismOfSites.{u} (smallEtaleModelEquivalence B S hS X.1).functor
      (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1) :=
    IsMorphismOfSites.ofIsDenseSubsite _
  { u := (smallEtaleModelEquivalence B S hS X.1).functor
    isMorphismOfSites := h
    fsharp := 𝟙 _ }

/-- **`ρ_X`: the morphism of ringed topoi from the small étale site of `X` to its model.** -/
abbrev smallEtaleModelInverseRingedToposHom (X : AlgebraicSpaces B S hS) :
    RingedToposHom (smallEtaleRingedTopos B S hS X)
      (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos :=
  (smallEtaleModelInverseRingedSiteHom B S hS X).toRingedToposHom

variable {B S hS}

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- The composite `g ∘ π_X` from the model of `X` to the small étale ringed topos of `Y`. -/
abbrev smallEtaleModelCompRingedToposHom {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    RingedToposHom (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos
      (smallEtaleRingedTopos B S hS Y) :=
  RingedToposHom.comp (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
    (Y := smallEtaleRingedTopos B S hS X) (Z := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS g) (smallEtaleModelRingedToposHom B S hS X)

/-- **A morphism of algebraic spaces on the equi-universe models**, `g_m = ρ_Y ∘ g ∘ π_X`. -/
abbrev smallEtaleModelPullbackRingedToposHom {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    RingedToposHom (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos
      (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos :=
  RingedToposHom.comp (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
    (Y := smallEtaleRingedTopos B S hS Y)
    (Z := (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos)
    (smallEtaleModelInverseRingedToposHom B S hS Y) (smallEtaleModelCompRingedToposHom g)

/-- The composite `π_Y ∘ g_m` from the model of `X` to the small étale ringed topos of `Y`. -/
abbrev smallEtaleModelPullbackCompRingedToposHom {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    RingedToposHom (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos
      (smallEtaleRingedTopos B S hS Y) :=
  RingedToposHom.comp (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
    (Y := (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos)
    (Z := smallEtaleRingedTopos B S hS Y)
    (smallEtaleModelRingedToposHom B S hS Y) (smallEtaleModelPullbackRingedToposHom g)

/-- The direct image along `π_Y ∘ ρ_Y` is the identity: it is the direct image along the
composite of the two functors of the model equivalence, which the counit identifies with the
identity. -/
def smallEtaleModelInversePushforwardIso (Y : AlgebraicSpaces B S hS) :
    (smallEtaleModelEquivalence B S hS Y.1).functor.sheafPushforwardContinuous (Type u)
        (smallEtaleModelTopology B S hS Y.1) (SmallEtale.topology B S hS Y.1) ⋙
      (smallEtaleModelEquivalence B S hS Y.1).inverse.sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (smallEtaleModelTopology B S hS Y.1) ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :=
  letI := Functor.isContinuous_comp (smallEtaleModelEquivalence B S hS Y.1).inverse
    (smallEtaleModelEquivalence B S hS Y.1).functor (SmallEtale.topology B S hS Y.1)
    (smallEtaleModelTopology B S hS Y.1) (SmallEtale.topology B S hS Y.1)
  Functor.sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫
    Functor.sheafPushforwardContinuousId' (smallEtaleModelEquivalence B S hS Y.1).counitIso _ _

/-- **The 2-isomorphism of the square**, on direct images of sheaves of sets:
`(π_Y ∘ g_m)_* = π_{Y*} ρ_{Y*} g_* π_{X*} ≅ g_* π_{X*}`. -/
def smallEtaleModelPullbackSquarePushforwardIso {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    (smallEtaleModelPullbackCompRingedToposHom g).toToposHom.pushforward ≅
      (smallEtaleModelCompRingedToposHom g).toToposHom.pushforward :=
  Functor.associator (smallEtaleModelCompRingedToposHom g).toToposHom.pushforward
      ((smallEtaleModelEquivalence B S hS Y.1).functor.sheafPushforwardContinuous (Type u)
        (smallEtaleModelTopology B S hS Y.1) (SmallEtale.topology B S hS Y.1))
      ((smallEtaleModelEquivalence B S hS Y.1).inverse.sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (smallEtaleModelTopology B S hS Y.1)) ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleModelInversePushforwardIso Y) ≪≫ Functor.rightUnitor _

open Stacks.Sheaves.ToposPullback in
/-- **The 2-isomorphism of the square carries the structure map of `π_Y ∘ g_m` to that of
`g ∘ π_X`.** On underlying sheaves of sets both structure maps factor through that of `g ∘ π_X`;
what is left is that the structure maps of `π_Y` and `ρ_Y` compose, under the counit of the
model equivalence, to the identity. -/
theorem smallEtaleModelPullbackSquare_fSharpRing {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    (smallEtaleModelPullbackCompRingedToposHom g).fSharpRing ≫
        pullbackRingSheafMapOfNatTrans
          (Φ := (smallEtaleModelPullbackCompRingedToposHom g).toToposHom.pushforward)
          (Φ' := (smallEtaleModelCompRingedToposHom g).toToposHom.pushforward)
          (smallEtaleRingedTopos B S hS Y).J
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.O)
          (smallEtaleModelPullbackSquarePushforwardIso g).hom =
      (smallEtaleModelCompRingedToposHom g).fSharpRing := by
  refine (sheafCompose (smallEtaleRingedTopos B S hS Y).J (forget RingCat.{u})).map_injective ?_
  refine (Functor.map_comp _ _ _).trans ?_
  refine (congrArg (fun n => (sheafCompose (smallEtaleRingedTopos B S hS Y).J
    (forget RingCat.{u})).map (smallEtaleModelPullbackCompRingedToposHom g).fSharpRing ≫ n)
    (ringSheafMap_pullbackRingSheafMapOfNatTrans _ _ _)).trans ?_
  have h₁ := RingedToposHom.comp_fSharpRing_underlying (smallEtaleModelRingedToposHom B S hS Y)
    (smallEtaleModelPullbackRingedToposHom g)
  have h₂ := RingedToposHom.comp_fSharpRing_underlying
    (smallEtaleModelInverseRingedToposHom B S hS Y)
    (smallEtaleModelCompRingedToposHom g)
  refine (congrArg (fun x => x ≫ (smallEtaleModelPullbackSquarePushforwardIso g).hom.app
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.O).ringSheaf) h₁).trans ?_
  refine (congrArg (fun y => (sheafCompose (smallEtaleRingedTopos B S hS Y).J
      (forget RingCat.{u})).map (smallEtaleModelRingedToposHom B S hS Y).fSharpRing ≫
      (smallEtaleModelRingedToposHom B S hS Y).toToposHom.pushforward.map y ≫
      (smallEtaleModelPullbackSquarePushforwardIso g).hom.app
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.O).ringSheaf) h₂).trans ?_
  refine Sheaf.hom_ext_sections fun U s => ?_
  have hO : ((sheafCompose (smallEtaleRingedTopos B S hS Y).J (forget RingCat.{u})).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).obj.map
        ((smallEtaleModelEquivalence B S hS Y.1).counitInv.app U.unop).op
      (((sheafCompose (smallEtaleRingedTopos B S hS Y).J (forget RingCat.{u})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).obj.map
        ((smallEtaleModelEquivalence B S hS Y.1).counit.app U.unop).op s) = s :=
    ConcreteCategory.congr_hom ((((sheafCompose (smallEtaleRingedTopos B S hS Y).J
        (forget RingCat.{u})).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).obj.mapIso
        ((smallEtaleModelEquivalence B S hS Y.1).counitIso.app U.unop).op).hom_inv_id) s
  have hn := NatTrans.naturality_apply ((sheafCompose (smallEtaleRingedTopos B S hS Y).J
    (forget RingCat.{u})).map (smallEtaleModelCompRingedToposHom g).fSharpRing).hom
    ((smallEtaleModelEquivalence B S hS Y.1).counitInv.app U.unop).op
    (((sheafCompose (smallEtaleRingedTopos B S hS Y).J (forget RingCat.{u})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).obj.map
        ((smallEtaleModelEquivalence B S hS Y.1).counit.app U.unop).op s)
  rw [hO] at hn
  exact hn.symm

/-- **The square of comparisons around `g_m`, for abstract data.** Given the 0D6D compositors
`cmp₁ : P_Y ⋙ G ≅ L₁`, `cmp₂ : L_g ⋙ P_X ≅ L₂`, a transport `tr : L₁ ≅ L₂`, comparisons `α`
satisfying the composition laws `h₁`, `h₃` and the transport law `h₂`, and identifications
`p : P ≅ e`, the composite `c : e_Y ⋙ G ≅ L_g ⋙ e_X` carries the comparison of `G` read
through `p_Y` to the comparison of `L_g` read through `p_X`. -/
theorem tensorComparison_square_of_laws {DY DX MY MX : Type*} [Category DY] [Category DX]
    [Category MY] [Category MX] {TY : DY × DY ⥤ DY} {TX : DX × DX ⥤ DX}
    {TmY : MY × MY ⥤ MY} {TmX : MX × MX ⥤ MX} {PY eY : DY ⥤ MY} {PX eX : DX ⥤ MX}
    (pY : PY ≅ eY) (pX : PX ≅ eX) {Lg : DY ⥤ DX} {G : MY ⥤ MX} {L₁ L₂ : DY ⥤ MX}
    (cmp₁ : PY ⋙ G ≅ L₁) (tr : L₁ ≅ L₂) (cmp₂ : Lg ⋙ PX ≅ L₂)
    (αPY : TY ⋙ PY ⟶ PY.prod PY ⋙ TmY) (αPX : TX ⋙ PX ⟶ PX.prod PX ⋙ TmX)
    (αG : TmY ⋙ G ⟶ G.prod G ⋙ TmX) (αg : TY ⋙ Lg ⟶ Lg.prod Lg ⋙ TX)
    (α₁ : TY ⋙ L₁ ⟶ L₁.prod L₁ ⋙ TmX) (α₂ : TY ⋙ L₂ ⟶ L₂.prod L₂ ⋙ TmX)
    (h₁ : Functor.whiskerLeft TY cmp₁.hom ≫ α₁ =
      Functor.whiskerRight αPY G ≫ Functor.whiskerLeft (PY.prod PY) αG ≫
        Functor.whiskerRight (NatTrans.prod cmp₁.hom cmp₁.hom) TmX)
    (h₂ : Functor.whiskerLeft TY tr.hom ≫ α₂ =
      α₁ ≫ Functor.whiskerRight (NatTrans.prod tr.hom tr.hom) TmX)
    (h₃ : Functor.whiskerLeft TY cmp₂.hom ≫ α₂ =
      Functor.whiskerRight αg PX ≫ Functor.whiskerLeft (Lg.prod Lg) αPX ≫
        Functor.whiskerRight (NatTrans.prod cmp₂.hom cmp₂.hom) TmX)
    (A B : DY) :
    G.map (pY.inv.app (TY.obj (A, B)) ≫ αPY.app (A, B) ≫
          TmY.map (pY.hom.app A ×ₘ pY.hom.app B)) ≫
        αG.app (eY.obj A, eY.obj B) ≫
        TmX.map ((Functor.isoWhiskerRight pY.symm G ≪≫ cmp₁ ≪≫ tr ≪≫ cmp₂.symm ≪≫
            Functor.isoWhiskerLeft Lg pX).hom.app A ×ₘ
          (Functor.isoWhiskerRight pY.symm G ≪≫ cmp₁ ≪≫ tr ≪≫ cmp₂.symm ≪≫
            Functor.isoWhiskerLeft Lg pX).hom.app B) =
      (Functor.isoWhiskerRight pY.symm G ≪≫ cmp₁ ≪≫ tr ≪≫ cmp₂.symm ≪≫
          Functor.isoWhiskerLeft Lg pX).hom.app (TY.obj (A, B)) ≫
        eX.map (αg.app (A, B)) ≫
        (pX.inv.app (TX.obj (Lg.obj A, Lg.obj B)) ≫ αPX.app (Lg.obj A, Lg.obj B) ≫
          TmX.map (pX.hom.app (Lg.obj A) ×ₘ pX.hom.app (Lg.obj B))) := by
  have e₁ : cmp₁.hom.app (TY.obj (A, B)) ≫ α₁.app (A, B) =
      G.map (αPY.app (A, B)) ≫ αG.app (PY.obj A, PY.obj B) ≫
        TmX.map (cmp₁.hom.app A ×ₘ cmp₁.hom.app B) := NatTrans.congr_app h₁ (A, B)
  have e₂ : tr.hom.app (TY.obj (A, B)) ≫ α₂.app (A, B) =
      α₁.app (A, B) ≫ TmX.map (tr.hom.app A ×ₘ tr.hom.app B) := NatTrans.congr_app h₂ (A, B)
  have e₃ : cmp₂.hom.app (TY.obj (A, B)) ≫ α₂.app (A, B) =
      PX.map (αg.app (A, B)) ≫ αPX.app (Lg.obj A, Lg.obj B) ≫
        TmX.map (cmp₂.hom.app A ×ₘ cmp₂.hom.app B) := NatTrans.congr_app h₃ (A, B)
  have e₁' : G.map (αPY.app (A, B)) ≫ αG.app (PY.obj A, PY.obj B) =
      cmp₁.hom.app (TY.obj (A, B)) ≫ α₁.app (A, B) ≫
        TmX.map (cmp₁.inv.app A ×ₘ cmp₁.inv.app B) := by
    rw [reassoc_of% e₁, ← TmX.map_comp, prod_comp]
    simp
  have e₂' : α₁.app (A, B) = tr.hom.app (TY.obj (A, B)) ≫ α₂.app (A, B) ≫
      TmX.map (tr.inv.app A ×ₘ tr.inv.app B) := by
    rw [reassoc_of% e₂, ← TmX.map_comp, prod_comp]
    simp
  have e₃' : α₂.app (A, B) = cmp₂.inv.app (TY.obj (A, B)) ≫ PX.map (αg.app (A, B)) ≫
      αPX.app (Lg.obj A, Lg.obj B) ≫ TmX.map (cmp₂.hom.app A ×ₘ cmp₂.hom.app B) := by
    rw [← e₃]
    simp
  have nG := αG.naturality (pY.hom.app A ×ₘ pY.hom.app B)
  have npX := pX.inv.naturality (αg.app (A, B))
  simp only [Functor.comp_obj, Functor.prod_obj, Functor.comp_map,
    Functor.prod_map] at nG npX
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% nG, reassoc_of% e₁', e₂', e₃', reassoc_of% npX]
  simp only [Category.assoc, ← TmX.map_comp, prod_comp]
  simp

section Derived

open Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy
  hasMapBifunctor_sheafTensor_smallEtaleModel

/-- The derived pullback along `g ∘ π_X` exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_smallEtaleModelCompPullbackOnHomotopy
    {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    (pullbackOnHomotopy (smallEtaleModelCompRingedToposHom g)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := smallEtaleRingedTopos B S hS Y)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleModelCompRingedToposHom g)

/-- The derived pullback along `π_Y ∘ g_m` exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_smallEtaleModelPullbackCompPullbackOnHomotopy
    {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    (pullbackOnHomotopy (smallEtaleModelPullbackCompRingedToposHom g)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := smallEtaleRingedTopos B S hS Y)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleModelPullbackCompRingedToposHom g)

/-- The derived pullback along `g_m` exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_smallEtaleModelPullbackPullbackOnHomotopy
    {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    (pullbackOnHomotopy (smallEtaleModelPullbackRingedToposHom g)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
    (Y := (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos)
    (smallEtaleModelPullbackRingedToposHom g)

/-- The pullbacks of modules along the two composites of the square agree, by the 2-isomorphism of
the square. -/
def smallEtaleModelPullbackSquarePullbackModulesIso {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    (smallEtaleModelPullbackCompRingedToposHom g).toModulesHom.pullbackModules ≅
      (smallEtaleModelCompRingedToposHom g).toModulesHom.pullbackModules :=
  RingedToposHom.pullbackModulesIsoOfNatIso (smallEtaleModelPullbackCompRingedToposHom g)
    (smallEtaleModelCompRingedToposHom g) (smallEtaleModelPullbackSquarePushforwardIso g)
    (smallEtaleModelPullbackSquare_fSharpRing g)

/-- The derived pullbacks along the two composites of the square agree, by the 2-isomorphism of
the square. -/
def smallEtaleModelPullbackSquareTransport {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    derivedPullback (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleModelPullbackCompRingedToposHom g) ≅
      derivedPullback (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleModelCompRingedToposHom g) :=
  derivedPullbackIsoOfPullbackModulesIso
    (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
    (Y := smallEtaleRingedTopos B S hS Y) (φ := smallEtaleModelPullbackCompRingedToposHom g)
    (ψ := smallEtaleModelCompRingedToposHom g) (smallEtaleModelPullbackSquarePullbackModulesIso g)

/-- **The derived pullback along `g_m` is `Lg^*` read on the models**: `e_Y ⋙ Lg_m^* ≅ Lg^* ⋙ e_X`,
through `e ≅ Lπ^*`, the compositors of Stacks 0D6D and the 2-isomorphism of the square. -/
def smallEtaleModelDerivedPullbackSquareIso {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) :
    (smallEtaleModelDerivedEquivalence B S hS Y).functor ⋙
        derivedPullback (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
          (Y := (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos)
          (smallEtaleModelPullbackRingedToposHom g) ≅
      smallEtaleDerivedModulePullback B S hS g ⋙
        (smallEtaleModelDerivedEquivalence B S hS X).functor :=
  Functor.isoWhiskerRight (smallEtaleModelDerivedPullbackIso B S hS Y).symm _ ≪≫
    derivedPullbackCompIso (smallEtaleModelPullbackRingedToposHom g)
      (smallEtaleModelRingedToposHom B S hS Y) ≪≫
    smallEtaleModelPullbackSquareTransport g ≪≫
    (derivedPullbackCompIso (smallEtaleModelRingedToposHom B S hS X)
      (smallEtaleRingedToposHom B S hS g)).symm ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleModelDerivedPullbackIso B S hS X)

/-- The identification of the derived tensor product of `X` with that of its model, written out:
the inverse of `e ≅ Lπ^*`, the comparison of Stacks 07A4 along `π`, and `e ≅ Lπ^*` in each
factor. -/
theorem smallEtaleModelDerivedTensorIso_hom_app (X : AlgebraicSpaces B S hS)
    (A A' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleModelDerivedTensorIso B S hS X).hom.app (A, A') =
      (smallEtaleModelDerivedPullbackIso B S hS X).inv.app
          ((Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X)).obj (A, A')) ≫
        (derivedPullbackTensorIso (smallEtaleModelRingedToposHom B S hS X)
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct _)
          (smallEtaleDerivedTensorProduct B S hS X)).hom.app (A, A') ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2))).map
          ((smallEtaleModelDerivedPullbackIso B S hS X).hom.app A ×ₘ
            (smallEtaleModelDerivedPullbackIso B S hS X).hom.app A') := by
  simp [smallEtaleModelDerivedTensorIso]

/-- The square of `smallEtaleModelPullbackIso_tensor`, with the identifications of the derived
tensor products written out. -/
theorem smallEtaleModelPullbackIso_tensor_aux {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (A A' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    type_of% (tensorComparison_square_of_laws (smallEtaleModelDerivedPullbackIso B S hS Y)
    (smallEtaleModelDerivedPullbackIso B S hS X) _ (smallEtaleModelPullbackSquareTransport g) _
    _ _ _ _ _ _
    (derivedPullbackTensorIso_comp (smallEtaleModelPullbackRingedToposHom g)
      (smallEtaleModelRingedToposHom B S hS Y) (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos.toRingedSite)
      (smallEtaleDerivedTensorProduct B S hS Y))
    (derivedPullbackTensorIso_pullbackModulesIsoOfNatIso
      (smallEtaleModelPullbackCompRingedToposHom g) (smallEtaleModelCompRingedToposHom g)
      (smallEtaleModelPullbackSquarePushforwardIso g) (smallEtaleModelPullbackSquare_fSharpRing g)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)
      (smallEtaleDerivedTensorProduct B S hS Y))
    (derivedPullbackTensorIso_comp (smallEtaleModelRingedToposHom B S hS X)
      (smallEtaleRingedToposHom B S hS g) (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)
      (smallEtaleDerivedTensorProduct B S hS X)
      (smallEtaleDerivedTensorProduct B S hS Y)) A A') :=
  tensorComparison_square_of_laws (smallEtaleModelDerivedPullbackIso B S hS Y)
    (smallEtaleModelDerivedPullbackIso B S hS X) _ (smallEtaleModelPullbackSquareTransport g) _
    _ _ _ _ _ _
    (derivedPullbackTensorIso_comp (smallEtaleModelPullbackRingedToposHom g)
      (smallEtaleModelRingedToposHom B S hS Y) (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos.toRingedSite)
      (smallEtaleDerivedTensorProduct B S hS Y))
    (derivedPullbackTensorIso_pullbackModulesIsoOfNatIso
      (smallEtaleModelPullbackCompRingedToposHom g) (smallEtaleModelCompRingedToposHom g)
      (smallEtaleModelPullbackSquarePushforwardIso g) (smallEtaleModelPullbackSquare_fSharpRing g)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)
      (smallEtaleDerivedTensorProduct B S hS Y))
    (derivedPullbackTensorIso_comp (smallEtaleModelRingedToposHom B S hS X)
      (smallEtaleRingedToposHom B S hS g) (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)
      (smallEtaleDerivedTensorProduct B S hS X)
      (smallEtaleDerivedTensorProduct B S hS Y)) A A'

/-- **Stacks 07A4 for `g_m` is Stacks 07A4 for `g` read on the models**: across
`smallEtaleModelDerivedPullbackSquareIso` and the identifications `smallEtaleModelDerivedTensorIso`
of the derived tensor products with those of the models, the comparison of Stacks 07A4 along
`g_m` is the one along `g`. -/
theorem smallEtaleModelDerivedPullbackSquareIso_tensor {X Y : AlgebraicSpaces B S hS}
    (g : X ⟶ Y)
    (A A' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (derivedPullback (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
          (Y := (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos)
          (smallEtaleModelPullbackRingedToposHom g)).map
          ((smallEtaleModelDerivedTensorIso B S hS Y).hom.app (A, A')) ≫
        (derivedPullbackTensorIso (smallEtaleModelPullbackRingedToposHom g)
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.toRingedSite)
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            (smallEtaleModelRingedSite B S hS Y.1 Y.2).toRingedTopos.toRingedSite)).hom.app
          ((smallEtaleModelDerivedEquivalence B S hS Y).functor.obj A,
            (smallEtaleModelDerivedEquivalence B S hS Y).functor.obj A') ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2))).map
          ((smallEtaleModelDerivedPullbackSquareIso g).hom.app A ×ₘ
            (smallEtaleModelDerivedPullbackSquareIso g).hom.app A') =
      (smallEtaleModelDerivedPullbackSquareIso g).hom.app
          ((Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y)).obj (A, A')) ≫
        (smallEtaleModelDerivedEquivalence B S hS X).functor.map
          ((smallEtaleDerivedPullbackTensorIso g).hom.app (A, A')) ≫
        (smallEtaleModelDerivedTensorIso B S hS X).hom.app
          ((smallEtaleDerivedModulePullback B S hS g).obj A,
            (smallEtaleDerivedModulePullback B S hS g).obj A') :=
  smallEtaleModelPullbackIso_tensor_aux g A A'

end Derived

end AlgebraicGeometry.Space

end
