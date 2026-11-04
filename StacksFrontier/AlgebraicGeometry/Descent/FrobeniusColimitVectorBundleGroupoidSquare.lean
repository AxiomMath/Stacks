module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoid
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundlesCube
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidStack
public import
  StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackPseudofunctor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsoWideMap

/-!
# The comparison functor of a square for the category fibred in groupoids of Stacks Tag 0EXE

For a commutative square of the big h category over `S`, the comparison functor
`𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` of the pseudofunctor in groupoids
`AlgebraicGeometry.frobeniusVectorBundleGroupoidPseudofunctor` lives on the *groupoids* of finite
locally free `colim_F 𝒪`-modules and their isomorphisms, whereas the comparison functor of Stacks
Tags 0EXC and 0EXD, `AlgebraicGeometry.frobeniusColimitVectorBundlesComparison`, lives on the full
*categories* of those modules, at the underlying square of schemes.  This file proves that the
first is an equivalence as soon as the second is.

## Main definitions

* `AlgebraicGeometry.frobeniusVectorBundleGroupoidInclusion`: the inclusion of the groupoid fibre
  over `U` into the category of finite locally free `colim_F 𝒪_U`-modules.

## Main results

* `AlgebraicGeometry.isCoreInclusion_frobeniusVectorBundleGroupoidInclusion`: that inclusion
  presents the groupoid fibre as the core of the category.
* `AlgebraicGeometry.pseudofunctorSquareIso_frobeniusVectorBundleGroupoid_hom_app_hom_iso_hom`:
  the structural isomorphism of the groupoid comparison functor has, as underlying morphism of
  sheaves of modules, the square comparison `AlgebraicGeometry.frobeniusColimitPullbackSquareIso`
  of the underlying square of schemes.
* `AlgebraicGeometry.isEquivalence_pseudofunctorSquareComparison_frobeniusVectorBundleGroupoid`:
  **the comparison functor of the pseudofunctor in groupoids at a commutative square of the site
  is an equivalence as soon as the comparison functor of the categories of finite locally free
  modules at the underlying square of schemes is.**
* `isEquivalence_twoFibreProductComparison_frobeniusVectorBundleGroupoidFibration`: **the same
  for the comparison functor of Stacks 0EX9 of the structure functor of Stacks Tag 0EXE**, at a
  cartesian square of the site.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius

namespace AlgebraicGeometry

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-- **The inclusion of the groupoid fibre of Stacks Tag 0EXE over `U` into the category of finite
locally free `colim_F 𝒪_U`-modules.** -/
def frobeniusVectorBundleGroupoidInclusion (U : BigHOver B S hS) :
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op U⟩ ⥤
      frobeniusColimitVectorBundles ((BigHOver.toScheme B S hS).obj U) p
        (isInCharacteristic_bigHOver B S hS p hpS U) where
  obj M := ⟨M.obj.of, M.property⟩
  map g := ObjectProperty.homMk g.hom.iso.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The groupoid fibre of Stacks Tag 0EXE is the core of the category of finite locally free
modules.** -/
theorem isCoreInclusion_frobeniusVectorBundleGroupoidInclusion (U : BigHOver B S hS) :
    (frobeniusVectorBundleGroupoidInclusion B S hS p hpS U).IsCoreInclusion where
  faithful := ⟨fun {_ _} _ _ h ↦
    ObjectProperty.hom_ext _ (Core.hom_ext (congrArg (fun k ↦ k.hom) h))⟩
  isIso_map {_ _} g :=
    ⟨ObjectProperty.homMk g.hom.iso.inv,
      ObjectProperty.hom_ext _ g.hom.iso.hom_inv_id,
      ObjectProperty.hom_ext _ g.hom.iso.inv_hom_id⟩
  exists_map_eq {_ _} e :=
    ⟨ObjectProperty.homMk (Core.isoMk ((ObjectProperty.ι _).mapIso e)).hom, rfl⟩
  essSurj := ⟨fun N ↦ ⟨⟨⟨N.obj⟩, N.property⟩, ⟨Iso.refl _⟩⟩⟩

/-! ### The composition constraints of the three pseudofunctors -/

section MapComp

variable {B S hS p}

/-- The composition constraint of the maximal-subgroupoid pseudofunctor has the composition
constraint of the pseudofunctor of all modules as underlying morphism. -/
lemma frobeniusColimitModuleCorePseudofunctor_mapComp'_hom_app_iso_hom
    {a b c : LocallyDiscrete (BigHOver B S hS)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (n : a ⟶ c)
    (h : f ≫ g = n) (X : (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).obj a) :
    (((frobeniusColimitModuleCorePseudofunctor B S hS p hpS).mapComp' f g n h).hom.toNatTrans.app
      X).iso.hom =
      ((frobeniusColimitModulePseudofunctor B S hS p hpS).mapComp' f g n h).hom.toNatTrans.app
        X.of := by
  subst h
  rfl

/-- The inverse of the composition constraint of the maximal-subgroupoid pseudofunctor has the
inverse of the composition constraint of the pseudofunctor of all modules as underlying
morphism. -/
lemma frobeniusColimitModuleCorePseudofunctor_mapComp'_inv_app_iso_hom
    {a b c : LocallyDiscrete (BigHOver B S hS)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (n : a ⟶ c)
    (h : f ≫ g = n) (X : (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).obj a) :
    (((frobeniusColimitModuleCorePseudofunctor B S hS p hpS).mapComp' f g n h).inv.toNatTrans.app
      X).iso.hom =
      ((frobeniusColimitModulePseudofunctor B S hS p hpS).mapComp' f g n h).inv.toNatTrans.app
        X.of := by
  subst h
  rfl

/-- The composition constraint of the pseudofunctor of all modules is the inverse of the
composition comparison of the transition functors of the underlying morphisms of schemes. -/
lemma frobeniusColimitModulePseudofunctor_mapComp_hom_app
    {U V W : BigHOver B S hS} (f : V ⟶ U) (g : W ⟶ V)
    (N : (frobeniusColimitModulePseudofunctor B S hS p hpS).obj ⟨op U⟩) :
    ((frobeniusColimitModulePseudofunctor B S hS p hpS).mapComp f.op.toLoc
      g.op.toLoc).hom.toNatTrans.app N =
      (frobeniusColimitPullbackComp p ((BigHOver.toScheme B S hS).map g)
        ((BigHOver.toScheme B S hS).map f)
        (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U)).inv.app N :=
  rfl

/-- The inverse of the composition constraint of the pseudofunctor of all modules is the
composition comparison of the transition functors of the underlying morphisms of schemes. -/
lemma frobeniusColimitModulePseudofunctor_mapComp_inv_app
    {U V W : BigHOver B S hS} (f : V ⟶ U) (g : W ⟶ V)
    (N : (frobeniusColimitModulePseudofunctor B S hS p hpS).obj ⟨op U⟩) :
    ((frobeniusColimitModulePseudofunctor B S hS p hpS).mapComp f.op.toLoc
      g.op.toLoc).inv.toNatTrans.app N =
      (frobeniusColimitPullbackComp p ((BigHOver.toScheme B S hS).map g)
        ((BigHOver.toScheme B S hS).map f)
        (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U)).hom.app N :=
  rfl

/-- The composition constraint of the pseudofunctor in groupoids has the composition constraint
of the maximal-subgroupoid pseudofunctor as underlying morphism. -/
lemma frobeniusVectorBundleGroupoidPseudofunctor_mapComp'_hom_app_hom
    {a b c : LocallyDiscrete (BigHOver B S hS)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (n : a ⟶ c)
    (h : f ≫ g = n) (X : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj a) :
    (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp' f g n h).hom.toNatTrans.app
      X).hom =
      ((frobeniusColimitModuleCorePseudofunctor B S hS p hpS).mapComp' f g n h).hom.toNatTrans.app
        X.obj := by
  subst h
  rfl

/-- The inverse of the composition constraint of the pseudofunctor in groupoids has the inverse of
the composition constraint of the maximal-subgroupoid pseudofunctor as underlying morphism. -/
lemma frobeniusVectorBundleGroupoidPseudofunctor_mapComp'_inv_app_hom
    {a b c : LocallyDiscrete (BigHOver B S hS)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (n : a ⟶ c)
    (h : f ≫ g = n) (X : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj a) :
    (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp' f g n h).inv.toNatTrans.app
      X).hom =
      ((frobeniusColimitModuleCorePseudofunctor B S hS p hpS).mapComp' f g n h).inv.toNatTrans.app
        X.obj := by
  subst h
  rfl

/-- The inverse of the composition constraint of the pseudofunctor in groupoids, on underlying
morphisms of sheaves of modules. -/
lemma frobeniusVectorBundleGroupoidPseudofunctor_mapComp_inv_app_hom_iso_hom
    {U V W : BigHOver B S hS} (f : V ⟶ U) (g : W ⟶ V)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op U⟩) :
    (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp f.op.toLoc
      g.op.toLoc).inv.toNatTrans.app M).hom.iso.hom =
      (frobeniusColimitPullbackComp p ((BigHOver.toScheme B S hS).map g)
        ((BigHOver.toScheme B S hS).map f)
        (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U)).hom.app M.obj.of := by
  rw [← Pseudofunctor.mapComp'_eq_mapComp,
    frobeniusVectorBundleGroupoidPseudofunctor_mapComp'_inv_app_hom,
    frobeniusColimitModuleCorePseudofunctor_mapComp'_inv_app_iso_hom,
    Pseudofunctor.mapComp'_eq_mapComp]
  exact frobeniusColimitModulePseudofunctor_mapComp_inv_app hpS f g M.obj.of

/-- The composition constraint of the pseudofunctor in groupoids, on underlying morphisms of
sheaves of modules. -/
lemma frobeniusVectorBundleGroupoidPseudofunctor_mapComp_hom_app_hom_iso_hom
    {U V W : BigHOver B S hS} (f : V ⟶ U) (g : W ⟶ V)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op U⟩) :
    (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp f.op.toLoc
      g.op.toLoc).hom.toNatTrans.app M).hom.iso.hom =
      (frobeniusColimitPullbackComp p ((BigHOver.toScheme B S hS).map g)
        ((BigHOver.toScheme B S hS).map f)
        (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U)).inv.app M.obj.of := by
  rw [← Pseudofunctor.mapComp'_eq_mapComp,
    frobeniusVectorBundleGroupoidPseudofunctor_mapComp'_hom_app_hom,
    frobeniusColimitModuleCorePseudofunctor_mapComp'_hom_app_iso_hom,
    Pseudofunctor.mapComp'_eq_mapComp]
  exact frobeniusColimitModulePseudofunctor_mapComp_hom_app hpS f g M.obj.of

/-- The triangle comparison of the underlying triangle of schemes at a literal composite of the
site is the composition comparison. -/
private lemma frobeniusColimitPullbackTriangleIso_map_comp
    {U V W : BigHOver B S hS} (f : V ⟶ U) (g : W ⟶ V) :
    frobeniusColimitPullbackTriangleIso p ((BigHOver.toScheme B S hS).map g)
        ((BigHOver.toScheme B S hS).map f) ((BigHOver.toScheme B S hS).map (g ≫ f))
        (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U)
        (((BigHOver.toScheme B S hS).map_comp g f).symm.trans
          (congrArg (BigHOver.toScheme B S hS).map rfl)) =
      frobeniusColimitPullbackComp p ((BigHOver.toScheme B S hS).map g)
        ((BigHOver.toScheme B S hS).map f) (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U) :=
  frobeniusColimitPullbackTriangleIso_rfl p _ _ _ _ _

/-- The composition constraint of the pseudofunctor in groupoids at a commuting triangle of the
site, on underlying morphisms of sheaves of modules: the inverse of the triangle comparison of
the underlying triangle of schemes. -/
lemma frobeniusVectorBundleGroupoidPseudofunctor_mapComp'_hom_app_hom_iso_hom
    {U V W : BigHOver B S hS} (f : V ⟶ U) (g : W ⟶ V) (n : W ⟶ U) (h : g ≫ f = n)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op U⟩) :
    (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp' f.op.toLoc g.op.toLoc
      n.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app M).hom.iso.hom =
      (frobeniusColimitPullbackTriangleIso p ((BigHOver.toScheme B S hS).map g)
        ((BigHOver.toScheme B S hS).map f) ((BigHOver.toScheme B S hS).map n)
        (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U)
        (((BigHOver.toScheme B S hS).map_comp g f).symm.trans
          (congrArg (BigHOver.toScheme B S hS).map h))).inv.app M.obj.of := by
  subst h
  rw [show (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp' f.op.toLoc g.op.toLoc
      (g ≫ f).op.toLoc (by rfl) =
      (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp' f.op.toLoc g.op.toLoc
        _ rfl from rfl, Pseudofunctor.mapComp'_eq_mapComp,
    frobeniusVectorBundleGroupoidPseudofunctor_mapComp_hom_app_hom_iso_hom,
    frobeniusColimitPullbackTriangleIso_map_comp hpS]

/-- The inverse of the composition constraint of the pseudofunctor in groupoids at a commuting
triangle of the site, on underlying morphisms of sheaves of modules: the triangle comparison of
the underlying triangle of schemes. -/
lemma frobeniusVectorBundleGroupoidPseudofunctor_mapComp'_inv_app_hom_iso_hom
    {U V W : BigHOver B S hS} (f : V ⟶ U) (g : W ⟶ V) (n : W ⟶ U) (h : g ≫ f = n)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op U⟩) :
    (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp' f.op.toLoc g.op.toLoc
      n.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app M).hom.iso.hom =
      (frobeniusColimitPullbackTriangleIso p ((BigHOver.toScheme B S hS).map g)
        ((BigHOver.toScheme B S hS).map f) ((BigHOver.toScheme B S hS).map n)
        (isInCharacteristic_bigHOver B S hS p hpS W)
        (isInCharacteristic_bigHOver B S hS p hpS V)
        (isInCharacteristic_bigHOver B S hS p hpS U)
        (((BigHOver.toScheme B S hS).map_comp g f).symm.trans
          (congrArg (BigHOver.toScheme B S hS).map h))).hom.app M.obj.of := by
  subst h
  rw [show (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp' f.op.toLoc g.op.toLoc
      (g ≫ f).op.toLoc (by rfl) =
      (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp' f.op.toLoc g.op.toLoc
        _ rfl from rfl, Pseudofunctor.mapComp'_eq_mapComp,
    frobeniusVectorBundleGroupoidPseudofunctor_mapComp_inv_app_hom_iso_hom,
    frobeniusColimitPullbackTriangleIso_map_comp hpS]

/-- The structural isomorphism of the groupoid comparison functor, split into its two
composition constraints, on underlying morphisms. -/
lemma pseudofunctorSquareIso_frobeniusVectorBundleGroupoid_hom_app_split
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op X⟩) :
    ((BigHOver.pseudofunctorSquareIso
      (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).hom.app M).hom.iso.hom =
      (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp z.op.toLoc
        e.op.toLoc).inv.toNatTrans.app M).hom.iso.hom ≫
      (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp' b.op.toLoc
        d.op.toLoc (e ≫ z).op.toLoc (by rw [hw]; rfl)).hom.toNatTrans.app M).hom.iso.hom :=
  rfl

/-- **The structural isomorphism of the groupoid comparison functor at a commutative square of the
site has, as underlying morphism of sheaves of modules, the comparison of the two composite
extensions of scalars around the underlying square of schemes.** -/
theorem pseudofunctorSquareIso_frobeniusVectorBundleGroupoid_hom_app_hom_iso_hom
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (hw' : (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map b =
      (BigHOver.toScheme B S hS).map e ≫ (BigHOver.toScheme B S hS).map z)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op X⟩) :
    ((BigHOver.pseudofunctorSquareIso (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS)
        b z d e hw).hom.app M).hom.iso.hom =
      (frobeniusColimitPullbackSquareIso p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').hom.app M.obj.of := by
  have hT := frobeniusColimitPullbackSquareIso_hom_app_comp_triangleIso p
    ((BigHOver.toScheme B S hS).map d) ((BigHOver.toScheme B S hS).map b)
    ((BigHOver.toScheme B S hS).map e) ((BigHOver.toScheme B S hS).map z)
    (isInCharacteristic_bigHOver B S hS p hpS E) (isInCharacteristic_bigHOver B S hS p hpS X')
    (isInCharacteristic_bigHOver B S hS p hpS Z) (isInCharacteristic_bigHOver B S hS p hpS X) hw'
    ((BigHOver.toScheme B S hS).map (e ≫ z))
    (((BigHOver.toScheme B S hS).map_comp d b).symm.trans
      (congrArg (BigHOver.toScheme B S hS).map hw.symm)) M.obj.of
  rw [pseudofunctorSquareIso_frobeniusVectorBundleGroupoid_hom_app_split hpS,
    frobeniusVectorBundleGroupoidPseudofunctor_mapComp_inv_app_hom_iso_hom,
    frobeniusVectorBundleGroupoidPseudofunctor_mapComp'_hom_app_hom_iso_hom hpS b d (e ≫ z)
      hw.symm M]
  have hA : (frobeniusColimitPullbackComp p ((BigHOver.toScheme B S hS).map e)
      ((BigHOver.toScheme B S hS).map z) (isInCharacteristic_bigHOver B S hS p hpS E)
      (isInCharacteristic_bigHOver B S hS p hpS Z)
      (isInCharacteristic_bigHOver B S hS p hpS X)).hom.app M.obj.of =
      (frobeniusColimitPullbackTriangleIso p ((BigHOver.toScheme B S hS).map e)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map (e ≫ z))
        (isInCharacteristic_bigHOver B S hS p hpS E) (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS X)
        (((BigHOver.toScheme B S hS).map_comp e z).symm.trans rfl)).hom.app M.obj.of := by
    rw [frobeniusColimitPullbackTriangleIso_map_comp hpS]
  exact (congrArg (· ≫ _) (hA.trans hT.symm)).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.hom_inv_id_app _ _)).trans (Category.comp_id _)))

end MapComp

variable {B S hS p} in
/-- The inclusion of the two-fibre product of the groupoid fibres of Stacks Tag 0EXE into the
two-fibre product of the categories of finite locally free modules, over a commutative square of
the site: the functor induced (Stacks 02XA) by the three inclusions, with identity fillers. -/
def frobeniusVectorBundleGroupoidTwoFibreProductInclusion {X' Z E : BigHOver B S hS}
    (d : E ⟶ X') (e : E ⟶ Z) :
    CategoricalPullback
        ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map e.op.toLoc).toFunctor
        ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map d.op.toLoc).toFunctor ⥤
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map e)
          (isInCharacteristic_bigHOver B S hS p hpS E)
          (isInCharacteristic_bigHOver B S hS p hpS Z))
        (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map d)
          (isInCharacteristic_bigHOver B S hS p hpS E)
          (isInCharacteristic_bigHOver B S hS p hpS X')) :=
  CategoricalPullback.map
    ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map e.op.toLoc).toFunctor
    ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map d.op.toLoc).toFunctor
    (frobeniusVectorBundleGroupoidInclusion B S hS p hpS Z)
    (frobeniusVectorBundleGroupoidInclusion B S hS p hpS X')
    (frobeniusVectorBundleGroupoidInclusion B S hS p hpS E)
    (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map e)
      (isInCharacteristic_bigHOver B S hS p hpS E) (isInCharacteristic_bigHOver B S hS p hpS Z))
    (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map d)
      (isInCharacteristic_bigHOver B S hS p hpS E) (isInCharacteristic_bigHOver B S hS p hpS X'))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

variable {B S hS p} in
/-- The first component of the image of an object `M` of the groupoid fibre over `X` under the
groupoid square comparison functor, included into the two-fibre product of categories, is the first
component of the image of `M` under the comparison functor of the categories. -/
lemma frobeniusVectorBundleGroupoid_squareComparison_obj_fst
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (hw' : (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map b =
      (BigHOver.toScheme B S hS).map e ≫ (BigHOver.toScheme B S hS).map z)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op X⟩) :
    ((frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).obj
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).obj M)).fst =
      ((frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M)).fst :=
  (show ((frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).obj
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).obj M)).fst =
      (frobeniusVectorBundleGroupoidInclusion B S hS p hpS Z).obj
        (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map z.op.toLoc).toFunctor.obj
          M)
    from rfl).trans
  ((show (frobeniusVectorBundleGroupoidInclusion B S hS p hpS Z).obj
        (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map z.op.toLoc).toFunctor.obj
          M) =
      (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map z)
        (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS X)).obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M) from rfl).trans
   (show (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map z)
        (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS X)).obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M) =
      ((frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M)).fst from rfl))

variable {B S hS p} in
/-- The second component of the image of an object `M` of the groupoid fibre over `X` under the
groupoid square comparison functor, included into the two-fibre product of categories, is the
second component of the image of `M` under the comparison functor of the categories. -/
lemma frobeniusVectorBundleGroupoid_squareComparison_obj_snd
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (hw' : (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map b =
      (BigHOver.toScheme B S hS).map e ≫ (BigHOver.toScheme B S hS).map z)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op X⟩) :
    ((frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).obj
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).obj M)).snd =
      ((frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M)).snd :=
  (show ((frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).obj
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).obj M)).snd =
      (frobeniusVectorBundleGroupoidInclusion B S hS p hpS X').obj
        (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map b.op.toLoc).toFunctor.obj
          M)
    from rfl).trans
  ((show (frobeniusVectorBundleGroupoidInclusion B S hS p hpS X').obj
        (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map b.op.toLoc).toFunctor.obj
          M) =
      (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map b)
        (isInCharacteristic_bigHOver B S hS p hpS X')
        (isInCharacteristic_bigHOver B S hS p hpS X)).obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M) from rfl).trans
   (show (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map b)
        (isInCharacteristic_bigHOver B S hS p hpS X')
        (isInCharacteristic_bigHOver B S hS p hpS X)).obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M) =
      ((frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M)).snd from rfl))

variable {B S hS p} in
/-- The first component of the structural isomorphism: the image of a module of the groupoid
fibre under the two composites around the square. -/
lemma frobeniusVectorBundleGroupoid_squareComparison_iso_hom_hom
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (_hw' : (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map b =
      (BigHOver.toScheme B S hS).map e ≫ (BigHOver.toScheme B S hS).map z)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op X⟩) :
    ((frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).obj
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).obj
            M)).iso.hom.hom =
      ((BigHOver.pseudofunctorSquareIso (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS)
        b z d e hw).hom.app M).hom.iso.hom := by
  simp only [frobeniusVectorBundleGroupoidTwoFibreProductInclusion,
    CategoricalPullback.map_obj_iso_hom, ObjectProperty.FullSubcategory.comp_hom]
  rfl

variable {B S hS p} in
/-- The structural isomorphisms of the two comparison functors agree, as an isomorphism in the
two-fibre product of the categories of finite locally free modules. -/
def frobeniusVectorBundleGroupoidSquareComparisonObjIso
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (hw' : (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map b =
      (BigHOver.toScheme B S hS).map e ≫ (BigHOver.toScheme B S hS).map z)
    (M : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op X⟩) :
    (frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).obj
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).obj M) ≅
      (frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M) :=
  CategoricalPullback.mkIso
    (Iso.refl ((frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map z)
        (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS X)).obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M)))
    (Iso.refl ((frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map b)
        (isInCharacteristic_bigHOver B S hS p hpS X')
        (isInCharacteristic_bigHOver B S hS p hpS X)).obj
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M)))
    (by
      apply ObjectProperty.hom_ext
      have key := (frobeniusVectorBundleGroupoid_squareComparison_iso_hom_hom hpS b z d e hw hw'
        M).trans ((pseudofunctorSquareIso_frobeniusVectorBundleGroupoid_hom_app_hom_iso_hom hpS
        b z d e hw hw' M).trans (frobeniusColimitVectorBundlesSquareIso_hom_app_hom p _ _ _ _ _ _ _
          _ hw' ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).obj M)).symm)
      refine ((congrArg (· ≫ _) (congrArg InducedCategory.Hom.hom
        (CategoryTheory.Functor.map_id _ _))).trans (Category.id_comp _)).trans ?_
      refine Eq.trans ?_ ((congrArg (_ ≫ ·) (congrArg InducedCategory.Hom.hom
        (CategoryTheory.Functor.map_id _ _))).trans (Category.comp_id _)).symm
      exact key.symm)

variable {B S hS p} in
/-- The naturality of `AlgebraicGeometry.frobeniusVectorBundleGroupoidSquareComparisonObjIso`, in
the first component. -/
lemma frobeniusVectorBundleGroupoidSquareComparison_map_fst
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (hw' : (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map b =
      (BigHOver.toScheme B S hS).map e ≫ (BigHOver.toScheme B S hS).map z)
    {M N : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op X⟩} (g : M ⟶ N) :
    ((frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).map
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).map g)).fst ≫
      (frobeniusVectorBundleGroupoidSquareComparisonObjIso hpS b z d e hw hw' N).hom.fst =
    (frobeniusVectorBundleGroupoidSquareComparisonObjIso hpS b z d e hw hw' M).hom.fst ≫
      ((frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').map
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).map g)).fst := by
  have h₁ : ((frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).map
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).map g)).fst =
      (frobeniusVectorBundleGroupoidInclusion B S hS p hpS Z).map
        (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map z.op.toLoc).toFunctor.map
          g) := rfl
  have h₂ : (frobeniusVectorBundleGroupoidInclusion B S hS p hpS Z).map
        (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map z.op.toLoc).toFunctor.map
          g) =
      (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map z)
        (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS X)).map
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).map g) := rfl
  have h₃ : (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map z)
        (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS X)).map
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).map g) =
      ((frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').map
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).map g)).fst := rfl
  have hM : (frobeniusVectorBundleGroupoidSquareComparisonObjIso hpS b z d e hw hw' M).hom.fst =
      𝟙 _ := rfl
  have hN : (frobeniusVectorBundleGroupoidSquareComparisonObjIso hpS b z d e hw hw' N).hom.fst =
      𝟙 _ := rfl
  rw [hM, hN]
  exact (Category.comp_id _).trans ((h₁.trans (h₂.trans h₃)).trans (Category.id_comp _).symm)

variable {B S hS p} in
/-- The naturality of `AlgebraicGeometry.frobeniusVectorBundleGroupoidSquareComparisonObjIso`, in
the second component. -/
lemma frobeniusVectorBundleGroupoidSquareComparison_map_snd
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (hw' : (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map b =
      (BigHOver.toScheme B S hS).map e ≫ (BigHOver.toScheme B S hS).map z)
    {M N : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨op X⟩} (g : M ⟶ N) :
    ((frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).map
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).map g)).snd ≫
      (frobeniusVectorBundleGroupoidSquareComparisonObjIso hpS b z d e hw hw' N).hom.snd =
    (frobeniusVectorBundleGroupoidSquareComparisonObjIso hpS b z d e hw hw' M).hom.snd ≫
      ((frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').map
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).map g)).snd := by
  have h₁ : ((frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).map
        ((BigHOver.pseudofunctorSquareComparison
          (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).map g)).snd =
      (frobeniusVectorBundleGroupoidInclusion B S hS p hpS X').map
        (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map b.op.toLoc).toFunctor.map
          g) := rfl
  have h₂ : (frobeniusVectorBundleGroupoidInclusion B S hS p hpS X').map
        (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map b.op.toLoc).toFunctor.map
          g) =
      (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map b)
        (isInCharacteristic_bigHOver B S hS p hpS X')
        (isInCharacteristic_bigHOver B S hS p hpS X)).map
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).map g) := rfl
  have h₃ : (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map b)
        (isInCharacteristic_bigHOver B S hS p hpS X')
        (isInCharacteristic_bigHOver B S hS p hpS X)).map
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).map g) =
      ((frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').map
          ((frobeniusVectorBundleGroupoidInclusion B S hS p hpS X).map g)).snd := rfl
  have hM : (frobeniusVectorBundleGroupoidSquareComparisonObjIso hpS b z d e hw hw' M).hom.snd =
      𝟙 _ := rfl
  have hN : (frobeniusVectorBundleGroupoidSquareComparisonObjIso hpS b z d e hw hw' N).hom.snd =
      𝟙 _ := rfl
  rw [hM, hN]
  exact (Category.comp_id _).trans ((h₁.trans (h₂.trans h₃)).trans (Category.id_comp _).symm)

variable {B S hS p} in
/-- **The comparison functor of the pseudofunctor in groupoids of Stacks Tag 0EXE at a commutative
square of the site is an equivalence as soon as the comparison functor of the categories of finite
locally free `colim_F 𝒪`-modules at the underlying square of schemes is.** -/
theorem isEquivalence_pseudofunctorSquareComparison_frobeniusVectorBundleGroupoid
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b)
    (hw' : (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map b =
      (BigHOver.toScheme B S hS).map e ≫ (BigHOver.toScheme B S hS).map z)
    (h : (frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').IsEquivalence) :
    (BigHOver.pseudofunctorSquareComparison
      (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hw).IsEquivalence := by
  have := (isCoreInclusion_frobeniusVectorBundleGroupoidInclusion B S hS p hpS E).faithful
  have hv : (frobeniusVectorBundleGroupoidTwoFibreProductInclusion hpS d e).IsIsoWide :=
    CategoricalPullback.isIsoWide_map
      (isCoreInclusion_frobeniusVectorBundleGroupoidInclusion B S hS p hpS Z).toIsIsoWide
      (isCoreInclusion_frobeniusVectorBundleGroupoidInclusion B S hS p hpS X').toIsIsoWide
  exact Functor.isEquivalence_of_isCoreInclusion
    (E := frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw')
    (isCoreInclusion_frobeniusVectorBundleGroupoidInclusion B S hS p hpS X) hv
    (NatIso.ofComponents (frobeniusVectorBundleGroupoidSquareComparisonObjIso hpS b z d e hw hw')
      (fun {_ _} g ↦ CategoricalPullback.hom_ext
        (frobeniusVectorBundleGroupoidSquareComparison_map_fst hpS b z d e hw hw' g)
        (frobeniusVectorBundleGroupoidSquareComparison_map_snd hpS b z d e hw hw' g)))

variable {B S hS p} in
/-- **The comparison functor `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` of Stacks Tag 0EX9 for the category fibred
in groupoids of Stacks Tag 0EXE, at a cartesian square of the site, is an equivalence as soon as
the comparison functor of the categories of finite locally free `colim_F 𝒪`-modules at the
underlying square of schemes is.** -/
theorem isEquivalence_twoFibreProductComparison_frobeniusVectorBundleGroupoidFibration
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hsq : IsPullback e d z b)
    (hw' : (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map b =
      (BigHOver.toScheme B S hS).map e ≫ (BigHOver.toScheme B S hS).map z)
    (h : (frobeniusColimitVectorBundlesComparison p ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map d)
        ((BigHOver.toScheme B S hS).map e) (isInCharacteristic_bigHOver B S hS p hpS X)
        (isInCharacteristic_bigHOver B S hS p hpS X') (isInCharacteristic_bigHOver B S hS p hpS Z)
        (isInCharacteristic_bigHOver B S hS p hpS E) hw').IsEquivalence) :
    (BigHOver.twoFibreProductComparison B S hS (frobeniusVectorBundleGroupoidFibration B S hS p hpS)
      b z d e hsq).IsEquivalence :=
  (BigHOver.isEquivalence_twoFibreProductComparison_forget_iff
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) b z d e hsq).2
    (isEquivalence_pseudofunctorSquareComparison_frobeniusVectorBundleGroupoid hpS b z d e hsq.w
      hw' h)

end AlgebraicGeometry

end
