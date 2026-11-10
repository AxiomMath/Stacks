module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.RingTheory.IsTensorProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePushforwardRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving

/-!
# The small étale direct image along an affine morphism

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site whose underlying morphism of
schemes `r` is affine, and let `ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` be the morphism of small
étale ringed sites of Stacks 070R (2).  This file proves

`(ε_a)_* (𝓕^a) ≅ (r_* 𝓕)^a`

for a quasi-coherent `𝒪_X`-module `𝓕`, and the consequence that `(ε_a)_*` preserves
quasi-coherence on the site — Stacks 02KG (1) read on the small étale sites of two schemes, the
form in which Stacks 07U8 cites it, and the input the affine case of Stacks 0CU9 needs.

## The route

Everything rests on **the cartesian condition**: a sheaf of modules on the small étale site of
`S` is *cartesian between affine objects* when, for a morphism `T ⟶ T'` of objects with affine
underlying schemes, the base-change comparison `Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective.
Quasi-coherence on the site implies it, by Stacks 03DX (2) in the form
`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite`; and the
counit argument of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleCounit.lean` uses
quasi-coherence of its argument for nothing else, so it runs over the cartesian condition alone.
That is what makes the circle break: quasi-coherence of `(ε_a)_* 𝓜` is what is being proved,
while its cartesian condition is a consequence of the cartesian condition for `𝓜` upstairs.

The cartesian condition for a pushforward is a purely algebraic statement about one square of
rings, and it is proved here at that generality, for the pushforward of presheaves of modules
along an arbitrary functor and comparison of presheaves of commutative rings
(`Stacks.PresheafOfModules.bijective_restrictionBaseChange_pushforward`): if `M` is cartesian
over `F f` and the square of rings `R_D X → R_D Y`, `R_C (F X) → R_C (F Y)` is a pushout, then
`F_* M` is cartesian over `f`.  The module statement is
`Algebra.IsPushout.cancelBaseChange`, `(R_C (F Y)) ⊗_{R_C (F X)} M ≅ (R_D Y) ⊗_{R_D X} M`, and
the two comparisons are identified on the pure tensors `1 ⊗ m`, where both are the restriction
map of `M`.

Geometrically the square of rings is the square of global functions of

```
  X ×_Y T  ⟶ X ×_Y T'
     |            |
     T      ⟶     T'
```

which is a fibre-product square of affine schemes — the base change of an affine morphism along
an affine object is affine — so `AlgebraicGeometry.isPushout_appTop_of_isPullback` applies.

With the counit at `(ε_a)_* 𝓜` an isomorphism, `(ε_a)_* 𝓜` is the associated module of its
restriction to the small Zariski site of `Y`; that restriction is quasi-coherent by
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule_pushforward`, which is the
Zariski case of Stacks 02KG read through the square of direct images, and the associated module
of a quasi-coherent module is quasi-coherent on the site by Stacks 03DV (2).  Taking `𝓜 = 𝓕^a`
and identifying the restriction with `r_* 𝓕` through the unit of the adjunction of `X_étale`
(an isomorphism at a quasi-coherent module, Stacks 0GN7) gives the comparison itself.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsCartesianOnAffines`: the cartesian condition between affine
  objects of the small étale site, as a proposition.
* `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`: **`(ε_a)_*(𝓕^a) ≅ (r_*𝓕)^a`**.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_pushforward`: the pushforward of a
  cartesian presheaf of modules is cartesian, over a pushout square of rings.
* `AlgebraicGeometry.SmallEtale.isPullback_toScheme_smallEtaleBaseChange` and
  `AlgebraicGeometry.SmallEtale.isAffine_toScheme_smallEtaleBaseChange`: the fibre-product square
  of a base change on small étale sites, and affineness of its corners.
* `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_pushforward` and
  `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_pushforward`: the small étale direct image
  along an affine morphism of a quasi-coherent module is cartesian between affine objects.
* `AlgebraicGeometry.SmallEtale.isIso_counit_of_isCartesianOnAffines`: the counit of the
  associated-module adjunction is an isomorphism at a sheaf of modules which is cartesian between
  affine objects and whose Zariski restriction is quasi-coherent.  This is
  `AlgebraicGeometry.SmallEtale.isIso_counit` with its quasi-coherence hypothesis weakened.
* `AlgebraicGeometry.SmallEtale.isIso_counit_pushforward`: the counit is an isomorphism at the
  small étale direct image along an affine morphism.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward`: **the small étale direct
  image along an affine morphism preserves quasi-coherence on the site.**

## Implementation notes

`AlgebraicGeometry.SmallEtale.bijective_counit_val_app_of_isAffine_of_isCartesianOnAffines`,
`AlgebraicGeometry.SmallEtale.bijective_counit_val_app_openSubObj_of_isCartesianOnAffines` and
`AlgebraicGeometry.SmallEtale.isIso_counit_of_isCartesianOnAffines` are the three statements of
`SmallEtaleCounit.lean` that mention quasi-coherence of `𝒢` on the site, restated over
`AlgebraicGeometry.SmallEtale.IsCartesianOnAffines` instead; the proofs are unchanged.
`AlgebraicGeometry.SmallEtale.isCartesianOnAffines_of_isQuasicoherentOnSite` records that the new
hypothesis is weaker, so no statement of that file is strengthened by being restated.

The affineness instances of the fibre-product square have to be supplied at the spellings the
elaborator reduces `Γ(·, ⊤)` to, which are not the ones
`AlgebraicGeometry.SmallEtale.toScheme` presents; the `haveI`s before
`AlgebraicGeometry.isPushout_appTop_of_isPullback` in
`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_pushforward` are that transport and
nothing more.

**No `@[stacks]` attribute is placed.**  Stacks 02KG is a statement about the Zariski site of a
scheme and is registered on
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom` and
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`; what is
proved here is the form in which Stacks 07U8 cites it on the small étale site, which the source
does not state as a result of its own.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 0CU9](https://stacks.math.columbia.edu/tag/0CU9)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v₁ v₂ u₁ u₂ r m

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  {RD : Cᵒᵖ ⥤ CommRingCat.{r}} {RC : Dᵒᵖ ⥤ CommRingCat.{r}}

/-- A comparison of presheaves of commutative rings along `F`, read on the underlying presheaves
of not necessarily commutative rings; this is the form over which the pushforward of presheaves
of modules is taken. -/
abbrev ringMap (ψ : RD ⟶ F.op ⋙ RC) :
    (RD ⋙ forget₂ CommRingCat RingCat.{r}) ⟶
      F.op ⋙ (RC ⋙ forget₂ CommRingCat RingCat.{r}) :=
  Functor.whiskerRight ψ (forget₂ CommRingCat RingCat.{r})

/-- **The pushforward of a cartesian presheaf of modules is cartesian**, as soon as the square of
rings `R_D X → R_D Y`, `R_C (F X) → R_C (F Y)` is a pushout. -/
theorem bijective_restrictionBaseChange_pushforward
    (ψ : RD ⟶ F.op ⋙ RC)
    (M : PresheafOfModules.{max m r} (RC ⋙ forget₂ CommRingCat RingCat.{r}))
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (hpo : IsPushout (ψ.app X) (RD.map f) (RC.map (F.op.map f)) (ψ.app Y))
    (hM : Function.Bijective (restrictionBaseChange (R := RC) M (F.op.map f))) :
    Function.Bijective (restrictionBaseChange (R := RD)
      ((PresheafOfModules.pushforward (ringMap ψ)).obj M) f) := by
  let : Algebra (RD.obj X) (RD.obj Y) := (RD.map f).hom.toAlgebra
  let : Algebra (RD.obj X) (RC.obj (F.op.obj X)) := (ψ.app X).hom.toAlgebra
  let : Algebra (RC.obj (F.op.obj X)) (RC.obj (F.op.obj Y)) :=
    (RC.map (F.op.map f)).hom.toAlgebra
  let : Algebra (RD.obj Y) (RC.obj (F.op.obj Y)) := (ψ.app Y).hom.toAlgebra
  let : Algebra (RD.obj X) (RC.obj (F.op.obj Y)) :=
    (ψ.app X ≫ RC.map (F.op.map f)).hom.toAlgebra
  have : IsScalarTower (RD.obj X) (RC.obj (F.op.obj X)) (RC.obj (F.op.obj Y)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (RD.obj X) (RD.obj Y) (RC.obj (F.op.obj Y)) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      congrArg (fun g : RD.obj X ⟶ RC.obj (F.op.obj Y) => g.hom x) (ψ.naturality f).symm
  have : Algebra.IsPushout (RD.obj X) (RD.obj Y) (RC.obj (F.op.obj X))
      (RC.obj (F.op.obj Y)) :=
    (CommRingCat.isPushout_iff_isPushout.1 hpo).symm
  let : Module (RD.obj X) (M.obj (F.op.obj X)) := inferInstanceAs
    (Module (RD.obj X) (((PresheafOfModules.pushforward (ringMap ψ)).obj M).obj X))
  let : Module (RC.obj (F.op.obj X)) (M.obj (F.op.obj Y)) := inferInstanceAs
    (Module (RC.obj (F.op.obj X))
      ((ModuleCat.restrictScalars (RC.map (F.op.map f)).hom).obj (M.obj (F.op.obj Y))))
  have : IsScalarTower (RD.obj X) (RC.obj (F.op.obj X)) (M.obj (F.op.obj X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (RC.obj (F.op.obj X)) (RC.obj (F.op.obj Y)) (M.obj (F.op.obj Y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : M.obj (F.op.obj X) →ₗ[RC.obj (F.op.obj X)] M.obj (F.op.obj Y) :=
    { toFun := fun x => (M.map (F.op.map f)).hom x
      map_add' := fun x y => map_add (M.map (F.op.map f)).hom x y
      map_smul' := fun c x => (M.map (F.op.map f)).hom.map_smul c x }
  have hbc : IsBaseChange (RC.obj (F.op.obj Y)) g :=
    IsBaseChange.of_equiv
      (LinearEquiv.ofBijective (restrictionBaseChange (R := RC) M (F.op.map f)).hom hM)
      fun x => restrictionBaseChange_one_tmul M (F.op.map f) x
  let e := Algebra.IsPushout.cancelBaseChange (RD.obj X) (RD.obj Y)
    (RC.obj (F.op.obj X)) (RC.obj (F.op.obj Y)) (M.obj (F.op.obj X))
  have key : ∀ x, (restrictionBaseChange (R := RD)
        ((PresheafOfModules.pushforward (ringMap ψ)).obj M) f) x = hbc.equiv (e.symm x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s mm =>
      refine Eq.trans (restrictionBaseChange_tmul (R := RD)
        ((PresheafOfModules.pushforward (ringMap ψ)).obj M) f s mm) ?_
      refine Eq.symm (Eq.trans (congrArg hbc.equiv
        (Algebra.IsPushout.cancelBaseChange_symm_tmul (RD.obj X) (RD.obj Y)
          (RC.obj (F.op.obj X)) (RC.obj (F.op.obj Y)) (M.obj (F.op.obj X)) s mm)) ?_)
      exact hbc.equiv_tmul _ mm
    | add x y hx hy =>
      refine Eq.trans (map_add _ x y) (Eq.trans (congrArg₂ (· + ·) hx hy) ?_)
      exact Eq.symm ((congrArg _ (map_add _ x y)).trans (map_add _ _ _))
  rw [show ⇑(restrictionBaseChange (R := RD)
        ((PresheafOfModules.pushforward (ringMap ψ)).obj M) f) = ⇑hbc.equiv ∘ ⇑e.symm from
    funext key]
  exact hbc.equiv.bijective.comp e.symm.bijective

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

universe u


section Counit

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being cartesian between affine objects of the small étale site of `S`, as a proposition.
This is the conclusion of
`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite`, which is
all that the counit argument of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleCounit.lean` uses
quasi-coherence on the site for. -/
def IsCartesianOnAffines (G : SheafOfModules.{u} (structureSheaf B S hS)) : Prop :=
  ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
    AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') →
        Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
          (R := commStructurePresheaf B S hS) G.val g.op)

/-- A quasi-coherent sheaf of modules on the small étale site is cartesian between affine
objects; this is `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_\
isQuasicoherentOnSite` read as `AlgebraicGeometry.SmallEtale.IsCartesianOnAffines`. -/
theorem isCartesianOnAffines_of_isQuasicoherentOnSite
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    IsCartesianOnAffines B S hS G :=
  fun g hT hT' => bijective_restrictionBaseChange_of_isQuasicoherentOnSite B S hS G hG hT hT' g

/-- **The counit is bijective on sections over an affine object lying over an affine open**, for a
sheaf of modules which is merely cartesian between affine objects.

This is `AlgebraicGeometry.SmallEtale.bijective_counit_val_app_of_isAffine` with its
quasi-coherence hypothesis on `𝒢` weakened to the cartesian condition it is used through: the
base-change square of `Stacks.PresheafOfModules.restrictionBaseChange_naturality` along a
morphism `T ⟶ V` has three bijective sides, the third being the counit over `V`. -/
theorem bijective_counit_val_app_of_isAffine_of_isCartesianOnAffines
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : IsCartesianOnAffines B S hS G)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    {T : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V)))
    (g : T ⟶ (opensToSmallEtale B S hS).obj V) :
    Function.Bijective
      (((associatedModuleAdjunction B S hS).counit.app G).val.app (op T)) := by
  classical
  set θ := (associatedModuleAdjunction B S hS).counit.app G
  have hqa : ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)
      ).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _ h
  have hA' := bijective_restrictionBaseChange_of_isQuasicoherentOnSite B S hS
    ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)) hqa hT hV g
  have hVi : IsIso (θ.val.app (op ((opensToSmallEtale B S hS).obj V))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_counit_val_app_opensObj B S hS G h V)
  have hE : Function.Bijective ((ModuleCat.extendScalars
      ((commStructurePresheaf B S hS).map g.op).hom).map
      (θ.val.app (op ((opensToSmallEtale B S hS).obj V)))) :=
    ConcreteCategory.bijective_of_isIso
      (f := ((ModuleCat.extendScalars ((commStructurePresheaf B S hS).map g.op).hom).mapIso
        (@asIso _ _ _ _ _ hVi)).hom)
  have hsq := Stacks.PresheafOfModules.restrictionBaseChange_naturality
    (R := commStructurePresheaf B S hS) θ.val g.op
  have hpt : ∀ x, Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf B S hS) G.val g.op
        ((ModuleCat.extendScalars ((commStructurePresheaf B S hS).map g.op).hom).map
          (θ.val.app (op ((opensToSmallEtale B S hS).obj V))) x) =
      θ.val.app (op T) (Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf B S hS)
        ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)).val g.op x) :=
    fun x => ConcreteCategory.congr_hom hsq x
  have hcomp : Function.Bijective (fun x => θ.val.app (op T)
      (Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf B S hS)
        ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)).val g.op x)) := by
    refine (funext hpt : _ = _) ▸ ?_
    exact (hG g hT hV).comp hE
  exact (hA'.of_comp_iff _).1 hcomp

/-- **The counit is bijective on sections over an affine open of an object lying over an affine
open of `S`**, for a sheaf of modules which is merely cartesian between affine objects. -/
theorem bijective_counit_val_app_openSubObj_of_isCartesianOnAffines
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : IsCartesianOnAffines B S hS G)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    (T : SmallEtale B S hS) {V : T.obj.left.obj.Opens} (hV : IsAffineOpen V)
    {U : S.Opens} (hU : IsAffineOpen U) (hVU : V ≤ T.obj.hom.hom ⁻¹ᵁ U) :
    Function.Bijective (((associatedModuleAdjunction B S hS).counit.app G).val.app
      (op (openSubObj B S hS T V))) :=
  bijective_counit_val_app_of_isAffine_of_isCartesianOnAffines B S hS G hG h
    (T := openSubObj B S hS T V) hV (V := U) hU (openSubHomOver B S hS T hVU)

/-- **The counit is an isomorphism** whenever `𝒢` is cartesian between affine objects of the
small étale site and its restriction to the small Zariski site is quasi-coherent.

This is `AlgebraicGeometry.SmallEtale.isIso_counit` with its quasi-coherence hypothesis on `𝒢`
weakened to that cartesian condition, which is the only consequence of quasi-coherence the
argument uses.  The counit is bijective over the affine opens lying over affine opens of `S`,
which cover every object, so it is locally bijective; both source and target are sheaves. -/
theorem isIso_counit_of_isCartesianOnAffines
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : IsCartesianOnAffines B S hS G)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G)) :
    IsIso ((associatedModuleAdjunction B S hS).counit.app G) := by
  set θ := (associatedModuleAdjunction B S hS).counit.app G
  have hbij : ∀ (T : SmallEtale B S hS) (i : (affineSubordinateCover B S hS T).I₀),
      Function.Bijective (((sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).map
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).map θ)).app
        (op ((affineSubordinateCover B S hS T).X i))) := fun T i =>
    bijective_counit_val_app_openSubObj_of_isCartesianOnAffines B S hS G hG h T
      i.down.1.2 i.down.2.1.2 i.down.2.2
  have hinj : Sheaf.IsLocallyInjective
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).map θ) := by
    rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff]
    refine ⟨fun {T} x y hxy => ?_⟩
    refine (topology B S hS).superset_covering ?_
      (mem_topology_sieve₀_affineSubordinateCover B S hS T.unop)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    refine (hbij T.unop i).1 ?_
    have hn := fun z => ConcreteCategory.congr_hom
      (((sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).map
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).map θ)).naturality
        ((affineSubordinateCover B S hS T.unop).f i).op) z
    exact (hn x).trans ((congrArg _ hxy).trans (hn y).symm)
  have hsurj : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).map θ) := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    refine ⟨fun {T} s => ?_⟩
    refine (topology B S hS).superset_covering ?_
      (mem_topology_sieve₀_affineSubordinateCover B S hS T)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact (hbij T i).2 _
  exact (isIso_iff_of_reflects_iso θ (SheafOfModules.toSheaf (structureSheaf B S hS))).1
    ((Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hinj, hsurj⟩)

end Counit

section BaseChange

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The base change along `a` of an affine object of the small étale site of `Y` is affine, the
morphism of schemes underlying `a` being affine. -/
theorem isAffine_toScheme_smallEtaleBaseChange [IsAffineHom (schemeHom B a)]
    (T : SmallEtale B Y.obj Y.property)
    (hT : AlgebraicGeometry.IsAffine ((toScheme B Y.obj Y.property).obj T)) :
    AlgebraicGeometry.IsAffine
      ((toScheme B X.obj X.property).obj ((smallEtaleBaseChange B a).obj T)) := by
  have : AlgebraicGeometry.IsAffine (B.inclusion.obj T.obj.left) := hT
  exact AlgebraicGeometry.IsAffine.of_isPullback
    ((IsPullback.of_hasPullback T.obj.hom a).map B.inclusion)

/-- **The square of rings of global functions of a base change on small étale sites is a
pushout.**  For a morphism `f : T ⟶ T'` of affine objects of the small étale site of `Y`, the
square of fibre products
```
  X ×_Y T  ⟶ X ×_Y T'
     |            |
     T      ⟶     T'
```
is cartesian with all four corners affine, so the rings of global functions form a pushout. -/
theorem isPullback_toScheme_smallEtaleBaseChange
    {T T' : SmallEtale B Y.obj Y.property} (f : T ⟶ T') :
    IsPullback
      ((toScheme B X.obj X.property).map ((smallEtaleBaseChange B a).map f))
      (show (toScheme B X.obj X.property).obj ((smallEtaleBaseChange B a).obj T) ⟶
          (toScheme B Y.obj Y.property).obj T from
        B.inclusion.map (pullback.fst T.obj.hom a))
      (show (toScheme B X.obj X.property).obj ((smallEtaleBaseChange B a).obj T') ⟶
          (toScheme B Y.obj Y.property).obj T' from
        B.inclusion.map (pullback.fst T'.obj.hom a))
      ((toScheme B Y.obj Y.property).map f) :=
  (CategoryTheory.baseChange_square (C := B.Scheme)
    ((inclusion B Y.obj Y.property).map f).left T'.obj.hom T.obj.hom a
    (Over.w ((inclusion B Y.obj Y.property).map f))).map B.inclusion

/-- **The small étale direct image along an affine morphism of a quasi-coherent module is
cartesian between affine objects.** -/
theorem bijective_restrictionBaseChange_pushforward [IsAffineHom (schemeHom B a)]
    (𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓜 : 𝓜.IsQuasicoherentOnSite)
    {T T' : SmallEtale B Y.obj Y.property} (f : T ⟶ T')
    (hT : AlgebraicGeometry.IsAffine ((toScheme B Y.obj Y.property).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B Y.obj Y.property).obj T')) :
    Function.Bijective (restrictionBaseChange (R := commStructurePresheaf B Y.obj Y.property)
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj 𝓜).val f.op) := by
  have hεT := isAffine_toScheme_smallEtaleBaseChange B a T hT
  have hεT' := isAffine_toScheme_smallEtaleBaseChange B a T' hT'
  refine Stacks.PresheafOfModules.bijective_restrictionBaseChange_pushforward
    (structureSharp B a).hom 𝓜.val f.op ?_
    (bijective_restrictionBaseChange_of_isQuasicoherentOnSite B X.obj X.property 𝓜 h𝓜
      hεT hεT' ((smallEtaleBaseChange B a).map f))
  have : AlgebraicGeometry.IsAffine
      (unop ((toScheme B Y.obj Y.property).op.obj (op T))) := hT
  have : AlgebraicGeometry.IsAffine
      (unop ((toScheme B Y.obj Y.property).op.obj (op T'))) := hT'
  have : AlgebraicGeometry.IsAffine
      (((𝟭 (Over Y)).obj ((inclusion B Y.obj Y.property).obj T)).left.obj) := hT
  have : AlgebraicGeometry.IsAffine
      (((𝟭 (Over Y)).obj ((inclusion B Y.obj Y.property).obj T')).left.obj) := hT'
  have : AlgebraicGeometry.IsAffine
      (((Over.map a).obj ((Over.pullback a).obj
        ((inclusion B Y.obj Y.property).obj T'))).left.obj) := hεT'
  exact AlgebraicGeometry.isPushout_appTop_of_isPullback
    (isPullback_toScheme_smallEtaleBaseChange B a f)

/-! ### The comparison with the associated module of the Zariski direct image -/

/-- **The small étale direct image along an affine morphism is cartesian between affine
objects**, read as `AlgebraicGeometry.SmallEtale.IsCartesianOnAffines`. -/
theorem isCartesianOnAffines_pushforward [IsAffineHom (schemeHom B a)]
    (𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓜 : 𝓜.IsQuasicoherentOnSite) :
    IsCartesianOnAffines B Y.obj Y.property
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj 𝓜) :=
  fun f hT hT' => bijective_restrictionBaseChange_pushforward B a 𝓜 h𝓜 f hT hT'

/-- **The counit of the associated-module adjunction of `Y_étale` is an isomorphism at the small
étale direct image along an affine morphism of a quasi-coherent module.**

The two inputs are `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_pushforward`, which comes
from Stacks 03DX (2) upstairs together with the pushout of rings of global functions of a base
change of affines, and
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule_pushforward`, which is the Zariski
case of Stacks 02KG read through the square of direct images. -/
theorem isIso_counit_pushforward [IsAffineHom (schemeHom B a)]
    (𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓜 : 𝓜.IsQuasicoherentOnSite) :
    IsIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj 𝓜)) :=
  isIso_counit_of_isCartesianOnAffines B Y.obj Y.property _
    (isCartesianOnAffines_pushforward B a 𝓜 h𝓜)
    (isQuasicoherent_restrictModule_pushforward B a 𝓜 h𝓜)

/-- **The small étale direct image along an affine morphism of a quasi-coherent module is
quasi-coherent on the site.**  This is Stacks 02KG (1) read on the small étale sites of two
schemes: the direct image along the morphism of ringed sites `ε_a` of Stacks 070R (2) preserves
quasi-coherence as soon as the underlying morphism of schemes is affine.

The counit of the associated-module adjunction of `Y_étale` is an isomorphism there by
`AlgebraicGeometry.SmallEtale.isIso_counit_pushforward`, so the direct image is the associated
module of its restriction to the small Zariski site, which is quasi-coherent; and the associated
module of a quasi-coherent module is quasi-coherent on the site by Stacks 03DV (2).

No `@[stacks]` attribute is placed.  Stacks 02KG is a statement about the Zariski site of a
scheme and is registered on
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom` and
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`; this is
the form in which Stacks 07U8 cites it on the small étale site, which the source does not state
separately. -/
theorem isQuasicoherentOnSite_pushforward [IsAffineHom (schemeHom B a)]
    (𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓜 : 𝓜.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
      𝓜).IsQuasicoherentOnSite := by
  have := isIso_counit_pushforward B a 𝓜 h𝓜
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (asIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj 𝓜)))
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B Y.obj Y.property _
      (isQuasicoherent_restrictModule_pushforward B a 𝓜 h𝓜))

/-- **The direct image along `ε_a` of the associated module is the associated module of the
direct image**, for an affine morphism of schemes and a quasi-coherent `𝒪_X`-module:

`(ε_a)_* (𝓕^a) ≅ (r_* 𝓕)^a`.

The isomorphism is the inverse of the counit of the associated-module adjunction of `Y_étale` at
the direct image — an isomorphism by
`AlgebraicGeometry.SmallEtale.isIso_counit_pushforward` — followed by the associated module of
the identification of the restriction to the small Zariski site of that direct image with
`r_* 𝓕`, which is
`AlgebraicGeometry.SmallEtale.restrictModulePushforwardObjIso` together with the unit of the
adjunction of `X_étale`, an isomorphism at the quasi-coherent `𝓕` by Stacks 0GN7. -/
def pushforwardAssociatedModuleIso [IsAffineHom (schemeHom B a)]
    (𝓕 : X.obj.Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := X.obj.ringCatSheaf) 𝓕) :
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B X.obj X.property).obj 𝓕) ≅
      (associatedModule B Y.obj Y.property).obj
        ((Scheme.Modules.pushforward (schemeHom B a)).obj 𝓕) :=
  haveI h𝓜 : ((associatedModule B X.obj X.property).obj 𝓕).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B X.obj X.property 𝓕 h𝓕
  haveI : IsIso ((associatedModuleAdjunction B X.obj X.property).unit.app 𝓕) :=
    unitIsoOnQuasicoherent B X.obj X.property ⟨𝓕, h𝓕⟩
  haveI := isIso_counit_pushforward B a _ h𝓜
  (asIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B X.obj X.property).obj 𝓕)))).symm ≪≫
    (associatedModule B Y.obj Y.property).mapIso
      (restrictModulePushforwardObjIso B a ((associatedModule B X.obj X.property).obj 𝓕) ≪≫
        (Scheme.Modules.pushforward (schemeHom B a)).mapIso
          (asIso ((associatedModuleAdjunction B X.obj X.property).unit.app 𝓕)).symm)

end BaseChange

end AlgebraicGeometry.SmallEtale

end
