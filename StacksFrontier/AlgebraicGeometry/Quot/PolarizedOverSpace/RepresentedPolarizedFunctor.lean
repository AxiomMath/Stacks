module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedComparison
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.SchemeOverIntegersForget
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence

/-!
# Towards the comparison `RepresentedPolarized ⥤ Polarized` as a functor over the site

The comparison `AlgebraicGeometry.PolarizedOverSpace.toPolarizedMap` restricts the comparison of
modules of a morphism of `RepresentedPolarized` to the Zariski site. This file collects what its
functor laws need.

* Its identity law follows from its composition law: an idempotent endomorphism of a polarized
  family lying over identities is the identity
  (`AlgebraicGeometry.PolarizedFamily.eq_id_of_comp_self`).
* Its composition law, proved in
  `StacksFrontier/AlgebraicGeometry/Quot/PolarizedOverSpace/RepresentedPolarizedTheta.lean`, is fed
  with the naturality and the composition law of
  `AlgebraicGeometry.Space.representedZariskiModulePullbackIso`, once the comparisons of
  `arrowModules` are identified with those of Stacks 03LU at the represented morphisms
  (`AlgebraicGeometry.PolarizedOverSpace.arrowModules_mapComp_inv_app`,
  `AlgebraicGeometry.PolarizedOverSpace.arrowModules_map_map`,
  `AlgebraicGeometry.PolarizedOverSpace.fiber_comp`).

## Implementation notes

A term built from the projections of a pseudofunctor and a term headed by
`AlgebraicGeometry.Space.modulePullback` or `AlgebraicGeometry.Space.modulePullbackCompIso` are
compared, by elaboration and by the kernel alike, by unfolding the latter first, which is
unaffordable. The two are therefore made irreducible for elaboration below, identifications are
stated at the level of whole functors and isomorphisms (where both sides have the same shape) and
transported to components with `CategoryTheory.Functor.congr_hom`, and no component of a comparison
is ever identified by `rfl`.

The morphisms of arrows in the comparisons are typed through the quiver of the category of arrows
(`CategoryTheory.CategoryStruct.toQuiver`) rather than through Mathlib's separate quiver instance
on `CategoryTheory.Arrow`: the bases of morphisms of a Grothendieck construction are typed through
the former, and a comparison stated through the latter differs from its instances at such bases
inside the arguments of `AlgebraicGeometry.Space.representedModulePullbackCompIso`, which the
kernel then unfolds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A pseudofunctor out of a locally discrete bicategory sends every invertible `2`-morphism to a
transport. -/
theorem _root_.CategoryTheory.map₂Iso_inv_toNatTrans_app_of_locallyDiscrete {C : Type*}
    [Category C] (G : Pseudofunctor (LocallyDiscrete C) Cat) {a b : LocallyDiscrete C}
    {φ ψ : a ⟶ b} (e : φ ≅ ψ) (M : G.obj a) :
    (G.map₂Iso e).inv.toNatTrans.app M =
      eqToHom (congrArg (fun k => (G.map k).toFunctor.obj M)
        (obj_ext_of_isDiscrete e.hom).symm) := by
  obtain rfl := obj_ext_of_isDiscrete e.hom
  obtain rfl : e = Iso.refl φ := Subsingleton.elim _ _
  simp
  rfl

/-- The composition comparison of a composite of pseudofunctors, at an object. -/
theorem _root_.CategoryTheory.comp_mapComp_inv_app_of_locallyDiscrete {C D : Type*} [Category C]
    [Category D] (F : Pseudofunctor (LocallyDiscrete C) (LocallyDiscrete D))
    (G : Pseudofunctor (LocallyDiscrete D) Cat) {a b c : LocallyDiscrete C} (φ : a ⟶ b)
    (ψ : b ⟶ c) (M : G.obj (F.obj a)) :
    ((F.comp G).mapComp φ ψ).inv.toNatTrans.app M =
      (G.mapComp (F.map φ) (F.map ψ)).inv.toNatTrans.app M ≫
        (G.map₂Iso (F.mapComp φ ψ)).inv.toNatTrans.app M :=
  rfl

/-- The inverse of the `2`-isomorphism of `Cat` attached to the inverse of a natural
isomorphism. -/
theorem _root_.CategoryTheory.Cat.Hom.isoMk_symm_inv_toNatTrans.{v₀, u₀} {C D : Type u₀}
    [Category.{v₀} C] [Category.{v₀} D] {F G : C ⥤ D} (e : F ≅ G) :
    (Cat.Hom.isoMk (F := G) (G := F) e.symm).inv.toNatTrans = e.hom :=
  rfl

/-- Two transports between the same objects agree. -/
theorem _root_.CategoryTheory.comp_eqToHom_eq {C : Type*} [Category C] {X Y Z : C} (e : X ⟶ Y)
    (p q : Y = Z) : e ≫ eqToHom p = e ≫ eqToHom q :=
  rfl

/-- Transports along equalities of objects with themselves cancel. -/
theorem _root_.CategoryTheory.eqToHom_self_comp_comp_eqToHom_self {C : Type*} [Category C] {X Y : C}
    (p : X = X) (e : X ⟶ Y) (q : Y = Y) : eqToHom p ≫ e ≫ eqToHom q = e := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

namespace PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- **An idempotent endomorphism of a polarized family lying over identities is the identity.**
Comparing `e ≫ e = e` with `𝟙 ≫ e = e` on the comparisons of polarizations and cancelling `e`
shows that its comparison is the canonical identification of the pullback along an identity. -/
theorem eq_id_of_comp_self {P : PolarizedFamily B} (e : P ⟶ P) (hb : e.baseMap = 𝟙 _)
    (ht : e.totalMap = 𝟙 _) (he : e ≫ e = e) : e = 𝟙 P := by
  have h2 : e ≫ e = 𝟙 P ≫ e := he.trans (Category.id_comp e).symm
  obtain ⟨b, t, cart, φ⟩ := e
  dsimp only at hb ht
  subst hb ht
  injection h2 with _ _ h3
  have h4 := congrArg Iso.hom h3
  change ((Scheme.Modules.pullbackComp (𝟙 P.total) (𝟙 P.total)).symm.app P.lineBundle ≪≫
      (Scheme.Modules.pullback (𝟙 P.total)).mapIso φ ≪≫ φ).hom =
    ((Scheme.Modules.pullbackComp (𝟙 P.total) (𝟙 P.total)).symm.app P.lineBundle ≪≫
      (Scheme.Modules.pullback (𝟙 P.total)).mapIso φ ≪≫
        (Scheme.Modules.pullbackId P.total).app P.lineBundle).hom at h4
  simp only [Iso.trans_hom, Iso.cancel_iso_hom_left] at h4
  have h5 : φ = (Scheme.Modules.pullbackId P.total).app P.lineBundle := Iso.ext h4
  subst h5
  rfl

end PolarizedFamily

namespace PolarizedOverSpace

variable (B : BigFppfSite.{u})

-- Elaboration is made to unfold the pseudofunctors rather than the inverse images.
attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso

/-- The composition comparison of `arrowModules` is that of the pseudofunctor of modules on
algebraic spaces at the represented morphisms, followed by a transport. -/
theorem arrowModules_mapComp_inv_app_eq {X Y Z : Arrow (Site B)}
    (f : @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver X Y)
    (g : @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver Y Z)
    (M : (arrowModules B).obj ⟨Opposite.op Z⟩) :
    ((arrowModules B).mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app M =
      ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp
        ((arrowSpace B).op.toPseudofunctor.map g.op.toLoc)
        ((arrowSpace B).op.toPseudofunctor.map f.op.toLoc)).inv.toNatTrans.app M ≫
      eqToHom (congrArg
        (fun k => ((Space.modulesPseudofunctor B integerBase (hZ B)).map k).toFunctor.obj M)
        (obj_ext_of_isDiscrete
          (((arrowSpace B).op.toPseudofunctor).mapComp g.op.toLoc f.op.toLoc).hom).symm) := by
  refine (_root_.CategoryTheory.comp_mapComp_inv_app_of_locallyDiscrete
    ((arrowSpace B).op.toPseudofunctor) (Space.modulesPseudofunctor B integerBase (hZ B))
    g.op.toLoc f.op.toLoc M).trans ?_
  exact congrArg (fun x => _ ≫ x)
    (_root_.CategoryTheory.map₂Iso_inv_toNatTrans_app_of_locallyDiscrete
      (Space.modulesPseudofunctor B integerBase (hZ B))
      (((arrowSpace B).op.toPseudofunctor).mapComp g.op.toLoc f.op.toLoc) M)

/-- The composition comparison of the pseudofunctor of modules at represented morphisms. -/
theorem modulesPseudofunctor_mapComp_inv_app_arrowSpace {X Y Z : Arrow (Site B)}
    (f : @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver X Y)
    (g : @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver Y Z)
    (M : (arrowModules B).obj ⟨Opposite.op Z⟩) :
      ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp
        ((arrowSpace B).op.toPseudofunctor.map g.op.toLoc)
        ((arrowSpace B).op.toPseudofunctor.map f.op.toLoc)).inv.toNatTrans.app M =
      (Space.modulePullbackCompIso B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) f.left)
        (Space.representedSpaceMap B integerBase (hZ B) g.left)).hom.app M := by
  have h3 : (Space.modulesPseudofunctor B integerBase (hZ B)).mapComp
      ((arrowSpace B).op.toPseudofunctor.map g.op.toLoc)
      ((arrowSpace B).op.toPseudofunctor.map f.op.toLoc) =
      Cat.Hom.isoMk (Space.modulePullbackCompIso B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) f.left)
        (Space.representedSpaceMap B integerBase (hZ B) g.left)).symm :=
    Space.modulesPseudofunctor_mapComp B integerBase (hZ B)
      (Space.representedSpaceMap B integerBase (hZ B) f.left)
      (Space.representedSpaceMap B integerBase (hZ B) g.left)
  refine (congrArg (fun e => NatTrans.app (Cat.Hom₂.toNatTrans (Iso.inv e)) M) h3).trans ?_
  exact congrArg (fun x => NatTrans.app x M)
    (_root_.CategoryTheory.Cat.Hom.isoMk_symm_inv_toNatTrans
      (Space.modulePullbackCompIso B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) f.left)
        (Space.representedSpaceMap B integerBase (hZ B) g.left)))

/-- `AlgebraicGeometry.Space.representedModulePullbackCompIso` at a module: the comparison of
Stacks 03LU followed by a transport. -/
theorem representedModulePullbackCompIso_hom_app_eq {X Y Z : Arrow (Site B)}
    (f : @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver X Y)
    (g : @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver Y Z)
    (M : Space.Modules B integerBase (hZ B) (yoneda.obj Z.left) (isAlgebraicSpace_yoneda _ _ _ _)) :
    (Space.representedModulePullbackCompIso B integerBase (hZ B) f.left g.left).hom.app M =
      (Space.modulePullbackCompIso B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) f.left)
        (Space.representedSpaceMap B integerBase (hZ B) g.left)).hom.app M ≫
      eqToHom (Functor.congr_obj (congrArg (Space.modulePullback B integerBase (hZ B))
        (Space.representedSpaceMap_comp B integerBase (hZ B) f.left g.left)) M) :=
  (NatTrans.comp_app _ _ M).trans (congrArg (fun x => _ ≫ x) (eqToHom_app (congrArg
    (Space.modulePullback B integerBase (hZ B))
      (Space.representedSpaceMap_comp B integerBase (hZ B) f.left g.left)) M))

/-- The total space of an arrow of the site maps by the represented morphism. -/
theorem arrowSpace_map {X Y : Arrow (Site B)} (f : X ⟶ Y) :
    (arrowSpace B).map f = Space.representedSpaceMap B integerBase (hZ B) f.left :=
  rfl

/-- The composition comparison of the pseudofunctor of modules on the arrows of the site is the
comparison of inverse images of Stacks 03LU at the represented morphisms. -/
theorem arrowModules_mapComp_inv_app {X Y Z : Arrow (Site B)}
    (f : @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver X Y)
    (g : @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver Y Z)
    (M : (arrowModules B).obj ⟨Opposite.op Z⟩) :
    ((arrowModules B).mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app M =
      (Space.representedModulePullbackCompIso B integerBase (hZ B) f.left g.left).hom.app M := by
  refine (arrowModules_mapComp_inv_app_eq B f g M).trans ?_
  refine (congrArg (fun x => x ≫ _)
    (modulesPseudofunctor_mapComp_inv_app_arrowSpace B f g M)).trans ?_
  exact (_root_.CategoryTheory.comp_eqToHom_eq _ _ _).trans
    (representedModulePullbackCompIso_hom_app_eq B f g M).symm

/-- The inverse image of `arrowModules` along a morphism of arrows is the inverse image along the
represented morphism of total spaces. -/
theorem arrowModules_map_toFunctor {X Y : Arrow (Site B)} (a : X ⟶ Y) :
    ((arrowModules B).map a.op.toLoc).toFunctor =
      Space.modulePullback B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) a.left) :=
  rfl

/-- Morphism form of `arrowModules_map_toFunctor`. -/
theorem arrowModules_map_map {X Y : Arrow (Site B)} (a : X ⟶ Y)
    {M N : (arrowModules B).obj ⟨Opposite.op Y⟩} (x : M ⟶ N) :
    ((arrowModules B).map a.op.toLoc).toFunctor.map x =
      (Space.modulePullback B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) a.left)).map x :=
  (Functor.congr_hom (arrowModules_map_toFunctor B a) x).trans
    (_root_.CategoryTheory.eqToHom_self_comp_comp_eqToHom_self _ _ _)

section CompLaw

variable {B} {X Y Z : RepresentedPolarized B}

/-- The comparison of modules of a morphism of `RepresentedPolarized` is invertible. -/
theorem isIso_fiber (f : X ⟶ Y) : IsIso f.hom.hom.fiber := f.property.2

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The comparison of modules of a composite. -/
theorem fiber_comp : (f ≫ g).hom.hom.fiber = f.hom.hom.fiber ≫
    ((arrowModules B).map f.hom.hom.base.op.toLoc).toFunctor.map g.hom.hom.fiber ≫
      ((arrowModules B).mapComp g.hom.hom.base.op.toLoc f.hom.hom.base.op.toLoc).inv.toNatTrans.app
        Z.obj.obj.fiber :=
  Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber f.hom.hom g.hom.hom

end CompLaw

end PolarizedOverSpace

end AlgebraicGeometry

end
