module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Geometry.RingedSpace.OpenImmersion
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors

/-!
# Restricting a derived direct image to an open subspace

For a Cartesian square of ringed spaces
```
U ----g---> V
|           |
i           j
|           |
v           v
X ----f---> Y
```
whose vertical arrows `i` and `j` are open immersions, restriction of a derived direct image is
naturally isomorphic to the derived direct image of the restriction: `(Rf_*E)|_V ≅ Rg_*(E|_U)`.
This is Stacks 08FE.

The proof is the one in the source. Both composites `Rf_* ∘ Rj^*` and `Rg_* ∘ Ri^*` are right
derived functors of the corresponding composites on homotopy categories, because pullback along
an open immersion is exact and carries K-injective complexes to K-injective complexes; the
underived comparison `(f_*I)|_V ≅ g_*(I|_U)` is then an isomorphism of functors on homotopy
categories, and the universal property of right derived functors transports it.

## Main definitions

* `Stacks.Cohomology.pushforwardRestrictMap`: the canonical base-change map, the adjoint
  transpose under `j^* ⊣ j_*` of the unit map `f_*M ⟶ f_*i_*i^*M` followed by the canonical
  identification `f_*i_* ≅ j_*g_*`.
* `Stacks.Cohomology.pushforwardRestrictHomotopyMap`: the same map on homotopy categories.
* `Stacks.Cohomology.pushforwardRestrictHomotopyIso`: the underived comparison, an isomorphism
  once `i` and `j` are open immersions in a Cartesian square.
* `Stacks.Cohomology.derivedPushforwardRestrictIso`: the natural isomorphism of Stacks 08FE
  comparing the two composites of derived functors around the square.
* `Stacks.Cohomology.openImmersionRestrictionData`: restriction of sheaves of modules along an
  open immersion of ringed spaces, together with its adjunction to the pushforward.
* `Stacks.Cohomology.openInclusionSiteRestriction`: restriction of sheaves of modules to an open
  subspace, presented as a sheaf pushforward along the image functor on opens, and
  `Stacks.Cohomology.openInclusionSiteRestrictionAdjunction`,
  `Stacks.Cohomology.openInclusionModulePullbackIso` its adjunction and its identification with
  module pullback.
* `Stacks.PullbackPseudofunctor.modulePullbackIdIso`, imported: pullback along an identity is
  the identity functor.
* `Stacks.Cohomology.openImmersionRangeIso`: the restriction of a ringed space along an open
  immersion is the open subspace cut out by the image of that immersion.

## Main results

* `Stacks.Cohomology.derivedPushforwardRestrictIso_isCanonical`: the isomorphism of Stacks 08FE
  is the canonical one — on a K-injective representative it is induced by the fixed adjunction
  mate `pushforwardRestrictHomotopyMap` and by the four specified derived-functor units.
* `Stacks.Cohomology.pushforwardRestrictHomotopyIso_hom`: the underived comparison is that same
  fixed adjunction mate.
* `Stacks.Cohomology.derivedRestrictionUnit_isIso`: pullback along an open immersion is exact,
  so the unit of any chosen right derived functor of it is an isomorphism; the chosen derived
  pullback is therefore ordinary restriction on derived categories.
* `Stacks.Cohomology.openImmersionModulePullback_preservesHomology` and
  `.openImmersionModulePullback_preservesKInjective`: the two exactness inputs.
* `Stacks.Cohomology.pushforwardRestrictMap_isIso`: the base-change map is an isomorphism for a
  Cartesian square with open-immersion verticals.

## Implementation notes

An open subspace square is expressed invariantly as a pullback square of ringed spaces. Each
derived functor is supplied together with its canonical unit and its
`Functor.IsRightDerivedFunctor` universal property; in particular, restriction is represented by
the right derived functor of pullback along the open immersion, and its exactness canonically
identifies this with ordinary restriction on the derived category. The conclusion is an
isomorphism of functors, retaining naturality in `E` rather than merely asserting an objectwise
isomorphism.

The underived comparison is fixed, not chosen up to an automorphism; the normalization is
recorded by `pushforwardRestrictHomotopyIso_hom` before
`derivedPushforwardRestrictIso_isCanonical` characterizes the derived comparison on K-injective
representatives.

The additive facts `RingedSpaceModuleAdjunction.modulePullback_additive` and
`RingedSpaceModuleAdjunction.modulePushforward_additive`, needed to form the functors on
homotopy categories appearing in the statement, are already global instances and are not
restated here.

Everything is stated at *free* `HasDerivedCategory` instances rather than at
`HasDerivedCategory.standard`: nothing here mentions a coproduct or an object that exists only at
one model, so each statement specialises both to the standard model and to the locally small model
of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which is the model at which the
compact-generation inputs of [Stacks, Tag 09IS] have content.

`openImmersionModulePullback_preservesKInjective` factors the open immersion through the inclusion
of its image and is phrased for a morphism out of an unconstrained ringed space: instance search
for `(modulePullback q).Additive` succeeds for a variable `q` and fails for the concrete inclusion
term, whose source is a definition rather than a variable.

## References

* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology

universe u

-- Sections of a sheaf pushforward along a continuous functor of sites are, on the nose,
-- sections over the image object; the restriction-along-an-open-immersion arguments below
-- compose maps whose endpoints are written on the two sides of that identification, so the
-- definition has to reduce at implicit transparency for those composites to elaborate.
attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

/-- The canonical base-change map for a commutative square of ringed spaces. It is the
adjoint transpose under `j^* ⊣ j_*` of the unit map `f_* M → f_* i_* i^* M`, followed
by the canonical identification `f_* i_* ≅ j_* g_*`. -/
noncomputable def pushforwardRestrictMap
    {X Y U V : RingedSpace.{u, u}}
    (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    (w : i ≫ f = g ≫ j) :
    modulePushforward f ⋙ modulePullback j ⟶ modulePullback i ⋙ modulePushforward g :=
  let e : modulePushforward i ⋙ modulePushforward f ≅
      modulePushforward g ⋙ modulePushforward j :=
    (pushforwardComp i f).symm ≪≫
      eqToIso (congrArg pushforward w) ≪≫ pushforwardComp g j
  ((modulePullbackPushforwardAdjunction j).whiskerRight
    (SheafOfModules.{u} (structureSheafRing X))).homEquiv _ _ |>.symm <|
      (Functor.leftUnitor (modulePushforward f)).inv ≫
        Functor.whiskerRight (modulePullbackPushforwardAdjunction i).unit
          (modulePushforward f) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (modulePullback i) e.hom ≫
        (Functor.associator _ _ _).inv

/-- The canonical base-change map applied termwise and passed to homotopy categories. -/
noncomputable def pushforwardRestrictHomotopyMap
    {X Y U V : RingedSpace.{u, u}}
    (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    (w : i ≫ f = g ≫ j) :
    (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePullback j).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePushforward f ⋙ modulePullback j)) (ComplexShape.up ℤ)).hom ≫
    (pushforwardRestrictMap f i j g w).mapHomotopyCategory (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePullback i ⋙ modulePushforward g)) (ComplexShape.up ℤ)).inv

/-- Restriction of sheaves of modules to an open subspace, presented as the sheaf pushforward
along the image functor on opens of the open embedding. -/
noncomputable def openInclusionSiteRestriction (X : RingedSpace.{u, u})
    (U : Opens (X : TopCat)) :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)) := by
  let j := X.ofRestrict U.isOpenEmbedding
  let h : Topology.IsOpenEmbedding j.hom.base :=
    (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open
  let F := h.functor
  let : F.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := h.functor_isContinuous
  exact SheafOfModules.pushforward (F := F) (𝟙 _)

/-- Restriction to an open subspace is left adjoint to the pushforward along the open
inclusion. -/
noncomputable def openInclusionSiteRestrictionAdjunction (X : RingedSpace.{u, u})
    (U : Opens (X : TopCat)) :
    openInclusionSiteRestriction X U ⊣ modulePushforward (X.ofRestrict U.isOpenEmbedding) := by
  let j := X.ofRestrict U.isOpenEmbedding
  let h : Topology.IsOpenEmbedding j.hom.base :=
    (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open
  let F := h.functor
  let G := Opens.map j.hom.base
  let adj : F ⊣ G := h.isOpenMap.adjunction
  let : F.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := h.functor_isContinuous
  let : G.IsContinuous
      (Opens.grothendieckTopology (X : TopCat))
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat)) := inferInstance
  let R := structureSheafRing X
  let S := structureSheafRing (X.restrict U.isOpenEmbedding)
  let φ : S ⟶ (F.sheafPushforwardContinuous RingCat _ _).obj R := 𝟙 _
  let ψ : R ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj S := structureSheafHom j
  have h1 : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext V x
    rfl
  have h2 : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj := by
    ext V x
    change (R.obj.map (adj.counit.app (F.obj V.unop)).op ≫
      R.obj.map (F.map (adj.unit.app V.unop)).op) x = x
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components V.unop]
    exact CategoryTheory.Functor.map_id_apply R.obj (Opposite.op (F.obj V.unop)) x
  change SheafOfModules.pushforward φ ⊣ SheafOfModules.pushforward ψ
  exact SheafOfModules.pushforwardPushforwardAdj adj φ ψ h1 h2

/-- Restriction to an open subspace is the pullback of sheaves of modules along the open
inclusion: both are left adjoint to the pushforward. -/
noncomputable def openInclusionModulePullbackIso (X : RingedSpace.{u, u})
    (U : Opens (X : TopCat)) :
    openInclusionSiteRestriction X U ≅
      modulePullback (X.ofRestrict U.isOpenEmbedding) :=
  Adjunction.leftAdjointUniq (openInclusionSiteRestrictionAdjunction X U)
    (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding))

/-- A functor isomorphic to a homology-preserving functor preserves homology. -/
private theorem preservesHomology_of_iso {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] {F G : C ⥤ D} (e : F ≅ G)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [F.PreservesHomology] :
    G.PreservesHomology := by
  refine { preservesKernels := fun A B f => ?_, preservesCokernels := fun A B f => ?_ }
  · have := ‹F.PreservesHomology›.preservesKernels f
    exact preservesLimit_of_natIso (parallelPair f 0) e
  · have := ‹F.PreservesHomology›.preservesCokernels f
    exact preservesColimit_of_natIso (parallelPair f 0) e

/-- Pullback along the inclusion of an open subspace preserves homology: it agrees with
restriction, which is exact. -/
theorem openInclusionModulePullback_preservesHomology (X : RingedSpace.{u, u})
    (U : Opens (X : TopCat)) :
    (modulePullback (X.ofRestrict U.isOpenEmbedding)).PreservesHomology := by
  let F := openInclusionSiteRestriction X U
  let G := modulePullback (X.ofRestrict U.isOpenEmbedding)
  let e : F ≅ G := openInclusionModulePullbackIso X U
  let : F.Additive := by
    show (HigherDirectImage.moduleRestriction X U).Additive
    infer_instance
  have hF : F.PreservesHomology := by
    show (ExtensionByZeroModules.jStar U (structureSheafRing X)).PreservesHomology
    let : PreservesLimits (ExtensionByZeroModules.jStar U (structureSheafRing X)) :=
      (ExtensionByZeroModules.jShriekAdjunction U
        (structureSheafRing X)).rightAdjoint_preservesLimits
    let : PreservesColimits (ExtensionByZeroModules.jStar U (structureSheafRing X)) :=
      (ExtensionByZeroModules.jStarAdjunction U
        (structureSheafRing X)).leftAdjoint_preservesColimits
    infer_instance
  let : G.PreservesZeroMorphisms := by dsimp [G]; infer_instance
  exact preservesHomology_of_iso e

/-- Pullback along the inclusion of an open subspace carries K-injective complexes to
K-injective complexes. -/
theorem openInclusionModulePullback_preservesKInjective (X : RingedSpace.{u, u})
    (U : Opens (X : TopCat))
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((modulePullback (X.ofRestrict U.isOpenEmbedding)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let : (openInclusionSiteRestriction X U).Additive := by
    show (HigherDirectImage.moduleRestriction X U).Additive
    infer_instance
  have hF : CochainComplex.IsKInjective
      (((openInclusionSiteRestriction X U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
    show CochainComplex.IsKInjective
      (((ExtensionByZeroModules.jStar U (structureSheafRing X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)
    infer_instance
  exact CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex (openInclusionModulePullbackIso X U)
      (ComplexShape.up ℤ)).app I)

/-- The image of the top open under the functor of an open embedding is its range. -/
private theorem coe_functor_obj_top {X Y : TopCat} {f : X ⟶ Y} (h : Topology.IsOpenEmbedding f) :
    (h.isOpenMap.functor.obj ⊤ : Set Y) = Set.range f := by
  rw [IsOpenMap.coe_functor_obj]
  simp

/-- The restriction of a ringed space along an open immersion is isomorphic to the open
subspace cut out by the image of that immersion. -/
noncomputable def openImmersionRangeIso
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    X.restrict ((inferInstance : SheafedSpace.IsOpenImmersion i).base_open) ≅
      openSubspace X
      ((inferInstance : SheafedSpace.IsOpenImmersion i).base_open.functor.obj ⊤) := by
  let h : Topology.IsOpenEmbedding i.hom.base :=
    (show SheafedSpace.IsOpenImmersion i from inferInstance).base_open
  let W : Opens (X : TopCat) := h.functor.obj ⊤
  let a := X.ofRestrict W.isOpenEmbedding
  let b := X.ofRestrict h
  let fb := SheafedSpace.forgetToPresheafedSpace.map b
  let fa := SheafedSpace.forgetToPresheafedSpace.map a
  have hb : PresheafedSpace.IsOpenImmersion fb := by
    simpa [fb] using (SheafedSpace.IsOpenImmersion.forgetMapIsOpenImmersion b)
  have ha : PresheafedSpace.IsOpenImmersion fa := by
    simpa [fa] using (SheafedSpace.IsOpenImmersion.forgetMapIsOpenImmersion a)
  have hW : (W : Set (X : TopCat)) = Set.range i.hom.base := by
    change (h.isOpenMap.functor.obj ⊤ : Set (X : TopCat)) = _
    rw [IsOpenMap.coe_functor_obj]
    simp
  have hr : Set.range fb.base = Set.range fa.base := by
    change Set.range i.hom.base = Set.range (W.inclusion')
    exact hW.symm.trans (Opens.set_range_inclusion' W).symm
  exact SheafedSpace.isoMk
    (@AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq
      CommRingCat inferInstance _ _ _ fb hb fa ha hr)

/-- The identification `openImmersionRangeIso` is compatible with the two inclusions into the
ambient ringed space. -/
theorem openImmersionRangeIso_comp
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    (openImmersionRangeIso i).hom ≫
        X.ofRestrict
          ((inferInstance : SheafedSpace.IsOpenImmersion i).base_open.functor.obj
            ⊤).isOpenEmbedding =
      X.ofRestrict ((inferInstance : SheafedSpace.IsOpenImmersion i).base_open) := by
  let h : Topology.IsOpenEmbedding i.hom.base :=
    (show SheafedSpace.IsOpenImmersion i from inferInstance).base_open
  let W : Opens (X : TopCat) := h.functor.obj ⊤
  let a := X.ofRestrict W.isOpenEmbedding
  let b := X.ofRestrict h
  let fb := SheafedSpace.forgetToPresheafedSpace.map b
  let fa := SheafedSpace.forgetToPresheafedSpace.map a
  have hb : PresheafedSpace.IsOpenImmersion fb := by
    simpa [fb] using (SheafedSpace.IsOpenImmersion.forgetMapIsOpenImmersion b)
  have ha : PresheafedSpace.IsOpenImmersion fa := by
    simpa [fa] using (SheafedSpace.IsOpenImmersion.forgetMapIsOpenImmersion a)
  have hW : (W : Set (X : TopCat)) = Set.range i.hom.base := coe_functor_obj_top h
  have hr : Set.range fb.base = Set.range fa.base := by
    show Set.range i.hom.base = Set.range (W.inclusion')
    exact hW.symm.trans (Opens.set_range_inclusion' W).symm
  let e := @AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    CommRingCat inferInstance _ _ _ fb hb fa ha hr
  show (SheafedSpace.isoMk e).hom ≫ a = b
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  show PresheafedSpace.IsOpenImmersion.lift fa fb (le_of_eq hr) ≫ fa = fb
  exact PresheafedSpace.IsOpenImmersion.lift_fac fa fb (le_of_eq hr)

/-- Restricting to the image of an open immersion `i` and including it back recovers `i`. -/
private theorem isoRestrict_trans_openImmersionRangeIso_hom_comp
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    ((SheafedSpace.IsOpenImmersion.isoRestrict i).trans (openImmersionRangeIso i)).hom ≫
      X.ofRestrict
        ((inferInstance : SheafedSpace.IsOpenImmersion i).base_open.functor.obj
          ⊤).isOpenEmbedding = i := by
  rw [Iso.trans_hom]
  erw [Category.assoc, openImmersionRangeIso_comp]
  exact SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict i

/-- In a Cartesian square of ringed spaces whose verticals are open immersions, the image of the
left vertical is the inverse image of the image of the right vertical. -/
theorem openImmersion_range_eq_preimage
    {X Y U V : RingedSpace.{u, u}}
    (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (h : IsPullback i g f j) :
    Set.range i.hom.base = f.hom.base ⁻¹' Set.range j.hom.base := by
  let hi : Topology.IsOpenEmbedding i.hom.base :=
    (show SheafedSpace.IsOpenImmersion i from inferInstance).base_open
  let hj : Topology.IsOpenEmbedding j.hom.base :=
    (show SheafedSpace.IsOpenImmersion j from inferInstance).base_open
  let Z : Opens (Y : TopCat) := hj.isOpenMap.functor.obj ⊤
  let W : Opens (X : TopCat) := hi.isOpenMap.functor.obj ⊤
  have hZ : (Z : Set (Y : TopCat)) = Set.range j.hom.base := coe_functor_obj_top hj
  have hW : (W : Set (X : TopCat)) = Set.range i.hom.base := coe_functor_obj_top hi
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    show f.hom.base (i.hom.base u) ∈ Set.range j.hom.base
    refine ⟨g.hom.base u, ?_⟩
    simpa using (congrArg (fun q : U ⟶ Y => q.hom.base u) h.w).symm
  · intro hx
    rw [← hW]
    rcases hx with ⟨y, hy⟩
    have hyZ : f.hom.base x ∈ Z := by
      show f.hom.base x ∈ (Z : Set (Y : TopCat))
      rw [hZ]
      exact ⟨y, hy⟩
    let k : openSubspace X ((Opens.map f.hom.base).obj Z) ⟶ X :=
      X.ofRestrict ((Opens.map f.hom.base).obj Z).isOpenEmbedding
    let m := HigherDirectImage.restrictedMorphism f Z
    let e := (SheafedSpace.IsOpenImmersion.isoRestrict j).trans
      (openImmersionRangeIso j)
    let j₀ : openSubspace Y Z ⟶ Y := Y.ofRestrict Z.isOpenEmbedding
    have he : e.hom ≫ j₀ = j := isoRestrict_trans_openImmersionRangeIso_hom_comp j
    have he' : e.inv ≫ j = j₀ := (Iso.inv_comp_eq e).2 he.symm
    let n : openSubspace X ((Opens.map f.hom.base).obj Z) ⟶ V := m ≫ e.inv
    have hmn : k ≫ f = n ≫ j := by
      show k ≫ f = m ≫ e.inv ≫ j
      exact (HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion f Z).trans
        (congrArg (fun t => m ≫ t) he').symm
    let c : PullbackCone f j := PullbackCone.mk k n hmn
    let l := h.isLimit.lift c
    have hl : l ≫ i = k := h.isLimit.fac c WalkingCospan.left
    let z : openSubspace X ((Opens.map f.hom.base).obj Z) := ⟨x, hyZ⟩
    exact ⟨l.hom.base z, trivial, congrArg (fun q => q.hom.base z) hl⟩

/-- Pullback of sheaves of modules along an isomorphism of ringed spaces is an equivalence. -/
theorem modulePullbackIso_isEquivalence
    {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    (modulePullback e.hom).IsEquivalence := by
  let η : 𝟭 (SheafOfModules.{u} (structureSheafRing Y)) ≅
      modulePullback e.hom ⋙ modulePullback e.inv :=
    (Stacks.PullbackPseudofunctor.modulePullbackIdIso Y).symm ≪≫
      (eqToIso (congrArg modulePullback e.inv_hom_id)).symm ≪≫
      pullbackComp e.inv e.hom
  let ε : modulePullback e.inv ⋙ modulePullback e.hom ≅
      𝟭 (SheafOfModules.{u} (structureSheafRing X)) :=
    (pullbackComp e.hom e.inv).symm ≪≫
      eqToIso (congrArg modulePullback e.hom_inv_id) ≪≫
        Stacks.PullbackPseudofunctor.modulePullbackIdIso X
  exact Functor.IsEquivalence.mk' (modulePullback e.inv) η ε

/-- Pullback of sheaves of modules along an isomorphism of ringed spaces preserves homology. -/
theorem modulePullbackIso_preservesHomology
    {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    (modulePullback e.hom).PreservesHomology := by
  let F := modulePullback e.hom
  let : F.IsEquivalence := modulePullbackIso_isEquivalence e
  let : PreservesLimits F := F.asEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  let : PreservesColimits F :=
    (modulePullbackPushforwardAdjunction e.hom).leftAdjoint_preservesColimits
  let : F.PreservesZeroMorphisms := by dsimp [F]; infer_instance
  exact { preservesKernels := fun _ => inferInstance, preservesCokernels := fun _ => inferInstance }

/-- Pullback of sheaves of modules along an isomorphism of ringed spaces carries K-injective
complexes to K-injective complexes. -/
theorem modulePullbackIso_preservesKInjective
    {X Y : RingedSpace.{u, u}} (e : X ≅ Y)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((modulePullback e.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let F := modulePullback e.hom
  let : F.IsEquivalence := modulePullbackIso_isEquivalence e
  let v := F.asEquivalence.symm.functor
  let : v.IsEquivalence := inferInstance
  let : v.IsRightAdjoint := inferInstance
  let : v.IsLeftAdjoint := inferInstance
  let : v.Additive := Functor.additive_of_preserves_binary_products v
  let : v.PreservesZeroMorphisms := inferInstance
  let : PreservesFiniteLimits v := by
    let : PreservesLimits v := (Adjunction.ofIsRightAdjoint v).rightAdjoint_preservesLimits
    infer_instance
  let : PreservesFiniteColimits v := by
    let : PreservesColimits v := (Adjunction.ofIsLeftAdjoint v).leftAdjoint_preservesColimits
    infer_instance
  let : v.PreservesHomology :=
    { preservesKernels := fun _ => inferInstance, preservesCokernels := fun _ => inferInstance }
  let adj : v ⊣ F := F.asEquivalence.symm.toAdjunction
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact F v adj I

/-- Pullback of sheaves of modules along an open immersion of ringed spaces preserves
homology. -/
theorem openImmersionModulePullback_preservesHomology
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    (modulePullback i).PreservesHomology := by
  let W : Opens (X : TopCat) :=
    (inferInstance : SheafedSpace.IsOpenImmersion i).base_open.functor.obj ⊤
  let k : openSubspace X W ⟶ X := X.ofRestrict W.isOpenEmbedding
  let ei := (SheafedSpace.IsOpenImmersion.isoRestrict i).trans (openImmersionRangeIso i)
  have he : ei.hom ≫ k = i := isoRestrict_trans_openImmersionRangeIso_hom_comp i
  let F := modulePullback k ⋙ modulePullback ei.hom
  let G := modulePullback i
  let eF : G ≅ F :=
    (eqToIso (congrArg modulePullback he)).symm ≪≫ pullbackComp ei.hom k
  let : (modulePullback ei.hom).PreservesHomology := modulePullbackIso_preservesHomology ei
  let : (modulePullback ei.hom).PreservesZeroMorphisms := by infer_instance
  let : (modulePullback k).PreservesHomology := by
    show (modulePullback (X.ofRestrict W.isOpenEmbedding)).PreservesHomology
    exact openInclusionModulePullback_preservesHomology X W
  let : (modulePullback k).PreservesZeroMorphisms := by infer_instance
  let : F.PreservesZeroMorphisms := by dsimp [F]; infer_instance
  have hF : F.PreservesHomology := by
    refine { preservesKernels := ?_, preservesCokernels := ?_ }
    · intro A B f
      let : PreservesLimit (parallelPair f 0) (modulePullback k) :=
        (openInclusionModulePullback_preservesHomology X W).preservesKernels f
      let d : parallelPair f 0 ⋙ modulePullback k ≅
          parallelPair ((modulePullback k).map f) 0 :=
        parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      let : PreservesLimit (parallelPair ((modulePullback k).map f) 0)
          (modulePullback ei.hom) :=
        (modulePullbackIso_preservesHomology ei).preservesKernels
          ((modulePullback k).map f)
      let : PreservesLimit ((parallelPair f 0) ⋙ modulePullback k)
          (modulePullback ei.hom) :=
        preservesLimit_of_iso_diagram (modulePullback ei.hom) d.symm
      infer_instance
    · intro A B f
      let : PreservesColimit (parallelPair f 0) (modulePullback k) :=
        (openInclusionModulePullback_preservesHomology X W).preservesCokernels f
      let d : parallelPair f 0 ⋙ modulePullback k ≅
          parallelPair ((modulePullback k).map f) 0 :=
        parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      let : PreservesColimit (parallelPair ((modulePullback k).map f) 0)
          (modulePullback ei.hom) :=
        (modulePullbackIso_preservesHomology ei).preservesCokernels
          ((modulePullback k).map f)
      let : PreservesColimit ((parallelPair f 0) ⋙ modulePullback k)
          (modulePullback ei.hom) :=
        preservesColimit_of_iso_diagram (modulePullback ei.hom) d.symm
      infer_instance
  let : G.PreservesZeroMorphisms := by dsimp [G]; infer_instance
  exact preservesHomology_of_iso eF.symm

/-- Pullback of sheaves of modules along an open immersion of ringed spaces carries K-injective
complexes to K-injective complexes. -/
theorem openImmersionModulePullback_preservesKInjective
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((modulePullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let W : Opens (X : TopCat) :=
    (inferInstance : SheafedSpace.IsOpenImmersion i).base_open.functor.obj ⊤
  let k : openSubspace X W ⟶ X := X.ofRestrict W.isOpenEmbedding
  let ei := (SheafedSpace.IsOpenImmersion.isoRestrict i).trans (openImmersionRangeIso i)
  have he : ei.hom ≫ k = i := isoRestrict_trans_openImmersionRangeIso_hom_comp i
  let F := modulePullback k ⋙ modulePullback ei.hom
  let G := modulePullback i
  let eF : G ≅ F :=
    (eqToIso (congrArg modulePullback he)).symm ≪≫ pullbackComp ei.hom k
  have hF : CochainComplex.IsKInjective
      (((F).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
    show CochainComplex.IsKInjective
      (((modulePullback ei.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePullback k).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    let : CochainComplex.IsKInjective
        (((modulePullback k).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
      show CochainComplex.IsKInjective
        (((modulePullback (X.ofRestrict W.isOpenEmbedding)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
      exact openInclusionModulePullback_preservesKInjective X W I
    exact modulePullbackIso_preservesKInjective ei
      (((modulePullback k).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  exact CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex eF (ComplexShape.up ℤ)).symm.app I)

/-- The unit of a chosen right derived functor of an exact functor is an isomorphism. -/
theorem chosenRightDerivedUnit_isIso_of_preservesHomology
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor alpha (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    IsIso alpha := by
  let : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
  let : PreservesFiniteColimits F := Functor.preservesFiniteColimits_of_preservesHomology F
  let e := F.mapDerivedCategoryFactorsh
  have hstd : F.mapDerivedCategory.IsRightDerivedFunctor e.inv
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ F.mapDerivedCategory e
  let e' := Functor.rightDerivedUnique R F.mapDerivedCategory alpha e.inv
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  have h : alpha ≫ Functor.whiskerLeft DerivedCategory.Qh e'.hom = e.inv := by
    simp [e', Functor.rightDerivedNatIso, Functor.rightDerivedNatTrans]
  have : IsIso (alpha ≫ Functor.whiskerLeft DerivedCategory.Qh e'.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right alpha (Functor.whiskerLeft DerivedCategory.Qh e'.hom)

/-- Pullback along an open immersion is exact, so the unit of any chosen right derived
functor of pullback is an isomorphism.  Thus the chosen derived pullback is ordinary
restriction on derived categories. -/
theorem derivedRestrictionUnit_isIso
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing U))]
    (Ri : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing U)))
    (alpha : (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri)
    [Ri.IsRightDerivedFunctor alpha
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))] :
    IsIso alpha := by
  let : (modulePullback i).PreservesHomology :=
    openImmersionModulePullback_preservesHomology i
  exact chosenRightDerivedUnit_isIso_of_preservesHomology
    (modulePullback i) Ri alpha

/-- Restriction of sheaves of modules along an open immersion of ringed spaces, together with
its adjunction to the pushforward. The functor is a sheaf pushforward along the image functor
on opens, whose structure map is invertible precisely because `i` is an open immersion. -/
noncomputable def openImmersionRestrictionData
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [hi : SheafedSpace.IsOpenImmersion i] :
    Σ F : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing U),
      F ⊣ modulePushforward i := by
  let a := hi.base_open.isOpenMap.adjunction
  let F := hi.base_open.functor
  let G := Opens.map i.hom.base
  let : F.IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) := hi.base_open.functor_isContinuous
  let S := structureSheafRing U
  let R := structureSheafRing X
  let ψ := structureSheafHom i
  let ρ : (F.sheafPushforwardContinuous RingCat _ _).obj R ⟶ S :=
    ⟨Functor.whiskerLeft F.op ψ.hom ≫ Functor.whiskerRight (NatTrans.op a.unit) S.obj⟩
  have : IsIso ρ := by
    have : Mono i.hom.base := (TopCat.mono_iff_injective _).2 hi.base_open.injective
    have : F.Full := inferInstance
    have : F.Faithful := inferInstance
    have : IsIso a.unit := inferInstance
    have : IsIso ((sheafToPresheaf _ _).map ρ) := by
      apply (NatTrans.isIso_iff_isIso_app _).2
      intro W
      change IsIso (ψ.hom.app (Opposite.op (F.obj W.unop)) ≫
        S.obj.map (a.unit.app W.unop).op)
      have hψ : IsIso (ψ.hom.app (Opposite.op (F.obj W.unop))) := by
        change IsIso ((forget₂ CommRingCat RingCat).map
          (i.hom.c.app (Opposite.op (F.obj W.unop))))
        have := hi.c_iso W.unop
        infer_instance
      have hmap : IsIso (S.obj.map (a.unit.app W.unop).op) :=
        S.obj.map_isIso (a.unit.app W.unop).op
      exact IsIso.comp_isIso' hψ hmap
    exact isIso_of_reflects_iso ρ (sheafToPresheaf _ _)
  let φ := inv ρ
  refine ⟨SheafOfModules.pushforward φ,
    SheafOfModules.pushforwardPushforwardAdj a φ ψ ?_ ?_⟩
  · ext W : 2
    have hρ : IsIso ρ.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map ρ))
    have hρW : IsIso (ρ.hom.app (G.op.obj W)) := inferInstance
    have hcancel : φ.hom.app (G.op.obj W) ≫ ρ.hom.app (G.op.obj W) = 𝟙 _ := by
      have h1 : φ.hom.app (G.op.obj W) = inv (ρ.hom.app (G.op.obj W)) := by
        simp [φ, ObjectProperty.hom_inv, NatIso.isIso_inv_app]
      rw [h1, IsIso.inv_hom_id]
    have hn := ψ.hom.naturality (a.counit.app W.unop).op
    change R.obj.map (a.counit.app W.unop).op ≫
      ψ.hom.app (Opposite.op (F.obj (G.obj W.unop))) =
      ψ.hom.app W ≫ S.obj.map (G.map (a.counit.app W.unop)).op at hn
    have hmain : R.obj.map (a.counit.app W.unop).op ≫ ρ.hom.app (G.op.obj W) =
        ψ.hom.app W := by
      change R.obj.map (a.counit.app W.unop).op ≫
        ψ.hom.app (Opposite.op (F.obj (G.obj W.unop))) ≫
        S.obj.map (a.unit.app (G.obj W.unop)).op = ψ.hom.app W
      rw [← Category.assoc, hn, Category.assoc, ← S.obj.map_comp,
        ← op_comp, a.right_triangle_components]
      exact (congrArg (fun t => ψ.hom.app W ≫ t)
        (S.obj.map_id (Opposite.op (G.obj W.unop)))).trans (Category.comp_id _)
    apply (cancel_mono (ρ.hom.app (G.op.obj W))).1
    change R.obj.map (a.counit.app W.unop).op ≫ ρ.hom.app (G.op.obj W) =
      ψ.hom.app W ≫ φ.hom.app (G.op.obj W) ≫ ρ.hom.app (G.op.obj W)
    rw [hcancel]
    exact hmain.trans (Category.comp_id _).symm
  · change (inv ρ).hom ≫ ρ.hom = 𝟙 _
    simp

/-- The counit of the restriction adjunction along an open immersion is an isomorphism. -/
theorem openImmersionRestriction_counit_isIso
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [hi : SheafedSpace.IsOpenImmersion i]
    (M : SheafOfModules.{u} (structureSheafRing U)) :
    IsIso ((openImmersionRestrictionData i).2.counit.app M) := by
  have : Mono i.hom.base := (TopCat.mono_iff_injective _).2 hi.base_open.injective
  have : IsIso hi.base_open.isOpenMap.adjunction.unit := inferInstance
  let T := SheafOfModules.forget (structureSheafRing U) ⋙ PresheafOfModules.toPresheaf _
  have : IsIso (T.map ((openImmersionRestrictionData i).2.counit.app M)) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro W
    show IsIso (M.val.presheaf.map
      (hi.base_open.isOpenMap.adjunction.unit.app W.unop).op)
    infer_instance
  exact isIso_of_reflects_iso _ T

/-- The counit of `i^* ⊣ i_*` is an isomorphism for an open immersion `i`. -/
theorem openImmersionPullback_counit_isIso
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i]
    (M : SheafOfModules.{u} (structureSheafRing U)) :
    IsIso ((modulePullbackPushforwardAdjunction i).counit.app M) := by
  let a := (openImmersionRestrictionData i).2
  let b := modulePullbackPushforwardAdjunction i
  have : IsIso (a.counit.app M) := openImmersionRestriction_counit_isIso i M
  have h := Adjunction.leftAdjointUniq_hom_app_counit a b M
  have : IsIso ((Adjunction.leftAdjointUniq a b).hom.app _ ≫ b.counit.app M) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left ((Adjunction.leftAdjointUniq a b).hom.app _) (b.counit.app M)

/-- Over an open contained in the image of an open immersion `i`, the unit of `i^* ⊣ i_*` is an
isomorphism on sections. -/
theorem openImmersion_unit_app_isIso
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [hi : SheafedSpace.IsOpenImmersion i]
    (M : SheafOfModules.{u} (structureSheafRing X)) (W : Opens X)
    (hW : (W : Set X) ⊆ Set.range i.hom.base) :
    IsIso (((modulePullbackPushforwardAdjunction i).unit.app M).val.app (Opposite.op W)) := by
  let a := hi.base_open.isOpenMap.adjunction
  have : IsIso (a.counit.app W) := by
    refine ⟨⟨homOfLE fun x hx => ?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    obtain ⟨z, rfl⟩ := hW hx
    exact ⟨z, hx, rfl⟩
  let a₁ := (openImmersionRestrictionData i).2
  let a₂ := modulePullbackPushforwardAdjunction i
  have : IsIso ((a₁.unit.app M).val.app (Opposite.op W)) := by
    let T := forget₂ (ModuleCat ((structureSheafRing X).obj.obj (Opposite.op W))) AddCommGrpCat
    have : IsIso (T.map ((a₁.unit.app M).val.app (Opposite.op W))) := by
      show IsIso (M.val.presheaf.map (a.counit.app W).op)
      infer_instance
    exact isIso_of_reflects_iso _ T
  have h := Adjunction.unit_leftAdjointUniq_hom_app a₁ a₂ M
  rw [← h]
  show IsIso ((SheafOfModules.evaluation _ (Opposite.op W)).map
    (a₁.unit.app M ≫ (modulePushforward i).map
      ((Adjunction.leftAdjointUniq a₁ a₂).hom.app M)))
  rw [Functor.map_comp]
  have : IsIso ((SheafOfModules.evaluation _ (Opposite.op W)).map (a₁.unit.app M)) :=
    ‹IsIso ((a₁.unit.app M).val.app (Opposite.op W))›
  infer_instance

/-- A map of sheaves of modules whose sections over every open in the image of an open
immersion `i` are isomorphisms becomes an isomorphism after pullback along `i`. -/
theorem openImmersionPullback_map_isIso
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [hi : SheafedSpace.IsOpenImmersion i]
    {M N : SheafOfModules.{u} (structureSheafRing X)} (t : M ⟶ N)
    (ht : ∀ W : Opens U, IsIso (t.val.app (Opposite.op (hi.base_open.functor.obj W)))) :
    IsIso ((modulePullback i).map t) := by
  let F := (openImmersionRestrictionData i).1
  have : IsIso (F.map t) := by
    let T := SheafOfModules.forget (structureSheafRing U) ⋙ PresheafOfModules.toPresheaf _
    have : IsIso (T.map (F.map t)) := by
      apply (NatTrans.isIso_iff_isIso_app _).2
      intro W
      have := ht W.unop
      show IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
        (t.val.app (Opposite.op (hi.base_open.functor.obj W.unop))))
      infer_instance
    exact isIso_of_reflects_iso _ T
  let e := Adjunction.leftAdjointUniq (openImmersionRestrictionData i).2
    (modulePullbackPushforwardAdjunction i)
  have he : (modulePullback i).map t = e.inv.app M ≫ F.map t ≫ e.hom.app N := by
    simp
  rw [he]
  infer_instance

/-- For a Cartesian square whose verticals are open immersions, the canonical base-change map
is an isomorphism. -/
theorem pushforwardRestrictMap_isIso
    {X Y U V : RingedSpace.{u, u}}
    (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    [SheafedSpace.IsOpenImmersion i] [hj : SheafedSpace.IsOpenImmersion j]
    (h : IsPullback i g f j) : IsIso (pushforwardRestrictMap f i j g h.w) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun M => ?_
  let e : modulePushforward i ⋙ modulePushforward f ≅
      modulePushforward g ⋙ modulePushforward j :=
    (pushforwardComp i f).symm ≪≫
      eqToIso (congrArg pushforward h.w) ≪≫ pushforwardComp g j
  let t := (modulePushforward f).map ((modulePullbackPushforwardAdjunction i).unit.app M)
  have : IsIso ((modulePullback j).map t) := by
    apply openImmersionPullback_map_isIso j t
    intro W
    have hu := openImmersion_unit_app_isIso i M
      ((Opens.map f.hom.base).obj (hj.base_open.functor.obj W)) (by
        rw [openImmersion_range_eq_preimage f i j g h]
        rintro x ⟨z, hz, he⟩
        exact ⟨z, he⟩)
    show IsIso ((ModuleCat.restrictScalars
      ((structureSheafHom f).hom.app (Opposite.op (hj.base_open.functor.obj W))).hom).map
      (((modulePullbackPushforwardAdjunction i).unit.app M).val.app
        (Opposite.op ((Opens.map f.hom.base).obj (hj.base_open.functor.obj W)))))
    exact @Functor.map_isIso _ _ _ _ _ _
      (ModuleCat.restrictScalars
        ((structureSheafHom f).hom.app (Opposite.op (hj.base_open.functor.obj W))).hom)
      (((modulePullbackPushforwardAdjunction i).unit.app M).val.app
        (Opposite.op ((Opens.map f.hom.base).obj (hj.base_open.functor.obj W)))) hu
  have := openImmersionPullback_counit_isIso j
    ((modulePushforward g).obj ((modulePullback i).obj M))
  have he : (pushforwardRestrictMap f i j g h.w).app M =
      (modulePullback j).map t ≫
      (modulePullback j).map (e.hom.app ((modulePullback i).obj M)) ≫
      (modulePullbackPushforwardAdjunction j).counit.app
        ((modulePushforward g).obj ((modulePullback i).obj M)) := by
    dsimp only [pushforwardRestrictMap]
    rw [Adjunction.homEquiv_symm_apply]
    show (modulePullback j).map
      (𝟙 _ ≫ t ≫ 𝟙 _ ≫ e.hom.app ((modulePullback i).obj M) ≫ 𝟙 _) ≫
      (𝟙 _ ≫ (modulePullbackPushforwardAdjunction j).counit.app
        ((modulePushforward g).obj ((modulePullback i).obj M)) ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [he]
  infer_instance

/-- A natural transformation out of a derived category is an isomorphism as soon as it is an
isomorphism at every K-injective complex, provided K-injective resolutions exist. -/
theorem isIso_of_isIso_on_kInjectives
    {A H : Type*} [Category A] [Category H] [Abelian A] [HasDerivedCategory A]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    {R S : DerivedCategory A ⥤ H} (τ : R ⟶ S)
    (hτ : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (τ.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)))) :
    IsIso τ := by
  have := Localization.essSurj DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  refine (NatTrans.isIso_iff_isIso_app _).2 fun E => ?_
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Qh E
  apply (τ.isIso_app_iff_of_iso e).1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, t, hI, ht⟩ := hA K
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map t)) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff t).2 ht)
  exact (τ.isIso_app_iff_of_iso (asIso
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map t)))).2 (hτ I hI)

/-- A functor on the derived category with a transformation that is an isomorphism at every
K-injective complex is a right derived functor. -/
theorem isRightDerivedFunctor_of_isIso_on_kInjectives
    {A H : Type*} [Category A] [Category H] [Abelian A] [HasDerivedCategory A]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (R : DerivedCategory A ⥤ H) (α : F ⟶ DerivedCategory.Qh ⋙ R)
    (hα : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient _ _).obj I))) :
    R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have h := F.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective hA
  have := h.1
  let R₀ := F.totalRightDerived DerivedCategory.Qh W
  let α₀ := F.totalRightDerivedUnit DerivedCategory.Qh W
  apply (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc R₀ α₀ W R α).2
  apply isIso_of_isIso_on_kInjectives hA
  intro I hI
  have := h.2 DerivedCategory.Qh R₀ α₀ I hI
  have := hα I hI
  have he := Functor.rightDerived_fac_app R₀ α₀ W R α
    ((HomotopyCategory.quotient _ _).obj I)
  have : IsIso (α₀.app ((HomotopyCategory.quotient _ _).obj I) ≫
      (Functor.rightDerivedDesc R₀ α₀ W R α).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (α₀.app ((HomotopyCategory.quotient _ _).obj I)) _

/-- The composite of two right derived functors is a right derived functor of the composite,
provided the second unit is an isomorphism at the image of every K-injective complex. -/
theorem composite_isRightDerivedFunctor
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (RG : DerivedCategory B ⥤ DerivedCategory C)
    (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hG : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj I)))) :
    (RF ⋙ RG).IsRightDerivedFunctor
      (Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) αG ≫
        Functor.whiskerRight αF RG)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  apply isRightDerivedFunctor_of_isIso_on_kInjectives hA
  intro I hI
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hA).2
      DerivedCategory.Qh RF αF I hI
  have := hG I hI
  show IsIso (αG.app _ ≫ RG.map (αF.app _))
  infer_instance

/-- Every complex of sheaves of modules on a ringed space has a K-injective resolution.  This is
`Stacks.Injectives.exists_kInjective_resolution_of_grothendieck` at the Grothendieck abelian
category of sheaves of modules; the content is not re-proved here. -/
theorem sheaf_exists_kInjective_resolution (X : RingedSpace.{u, u})
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f :=
  Stacks.Injectives.exists_kInjective_resolution_of_grothendieck K

/-- For a Cartesian square whose vertical maps are open immersions, restriction commutes
with pushforward already on homotopy categories.  This is the comparison
`(f_* I)|_V ≅ g_*(I|_U)` used in the proof of Stacks 08FE. -/
noncomputable def pushforwardRestrictHomotopyIso
    {X Y U V : RingedSpace.{u, u}}
    (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (h : IsPullback i g f j) :
    (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePullback j).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ) := by
  have : IsIso (pushforwardRestrictMap f i j g h.w) := pushforwardRestrictMap_isIso f i j g h
  let e : (modulePushforward f ⋙ modulePullback j).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (modulePullback i ⋙ modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ) :=
    { hom := (pushforwardRestrictMap f i j g h.w).mapHomotopyCategory (ComplexShape.up ℤ)
      inv := (inv (pushforwardRestrictMap f i j g h.w)).mapHomotopyCategory (ComplexShape.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
  exact (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (modulePushforward f ⋙ modulePullback j)) (ComplexShape.up ℤ)) ≪≫ e ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePullback i ⋙ modulePushforward g)) (ComplexShape.up ℤ)).symm

/-- **Stacks 08FE.** In a Cartesian square of ringed spaces
```
U ----g---> V
|           |
i           j
|           |
v           v
X ----f---> Y
```
in which `i` and `j` are open immersions, restricting the derived direct image along `j` is
naturally isomorphic to taking the derived direct image along `g` after restriction along `i`.

The four functors are arbitrary choices of right derived functors equipped with their canonical
units; hence the result applies in particular to the standard choices of `Rf_*`, `Rg_*`, and the
exact restriction functors. -/
@[stacks 08FE]
noncomputable def derivedPushforwardRestrictIso
    {X Y U V : RingedSpace.{u, u}}
    (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (h : IsPullback i g f j)
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing Y))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing U))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing V))]
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (Rg : DerivedCategory (SheafOfModules.{u} (structureSheafRing U)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing V)))
    (Ri : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing U)))
    (Rj : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing V)))
    (αf : (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    (αg : (modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    (αi : (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri)
    (αj : (modulePullback j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Ri.IsRightDerivedFunctor αi
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))] :
    Rf ⋙ Rj ≅ Ri ⋙ Rg := by
  let F := (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)
  let G := (modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)
  let I := (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ)
  let J := (modulePullback j).mapHomotopyCategory (ComplexShape.up ℤ)
  let βf : (F ⋙ J) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ (Rf ⋙ Rj) :=
    Functor.whiskerLeft F αj ≫ Functor.whiskerRight αf Rj
  let βg : (I ⋙ G) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ (Ri ⋙ Rg) :=
    Functor.whiskerLeft I αg ≫ Functor.whiskerRight αi Rg
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)
  have : (Rf ⋙ Rj).IsRightDerivedFunctor βf W := by
    apply composite_isRightDerivedFunctor
      (DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)
      (modulePushforward f) (modulePullback j) Rf Rj αf αj
    intro K hK
    have := derivedRestrictionUnit_isIso j Rj αj
    infer_instance
  have : (Ri ⋙ Rg).IsRightDerivedFunctor βg W := by
    apply composite_isRightDerivedFunctor
      (DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)
      (modulePullback i) (modulePushforward g) Ri Rg αi αg
    intro K hK
    have hKi := openImmersionModulePullback_preservesKInjective i K
    exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (G ⋙ DerivedCategory.Qh) (DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective U)).2
        DerivedCategory.Qh Rg αg
        (((modulePullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) hKi
  exact Functor.rightDerivedNatIso (Rf ⋙ Rj) (Ri ⋙ Rg) βf βg W
    (Functor.isoWhiskerRight (pushforwardRestrictHomotopyIso f i j g h) DerivedCategory.Qh)

/-- The underived isomorphism is induced by the canonical adjunction mate, using the
specified units and canonical pushforward-composition maps, rather than an arbitrary
natural isomorphism between the same functors. -/
theorem pushforwardRestrictHomotopyIso_hom
    {X Y U V : RingedSpace.{u, u}}
    (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (h : IsPullback i g f j) :
    (pushforwardRestrictHomotopyIso f i j g h).hom =
      pushforwardRestrictHomotopyMap f i j g h.w :=
  rfl

/-- The isomorphism `derivedPushforwardRestrictIso` is the canonical one: on a
K-injective representative it is induced by the fixed adjunction mate
`pushforwardRestrictHomotopyMap` and by the four specified derived-functor units. -/
@[stacks 08FE "canonicality"]
theorem derivedPushforwardRestrictIso_isCanonical
    {X Y U V : RingedSpace.{u, u}}
    (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (h : IsPullback i g f j)
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing Y))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing U))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing V))]
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (Rg : DerivedCategory (SheafOfModules.{u} (structureSheafRing U)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing V)))
    (Ri : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing U)))
    (Rj : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing V)))
    (alpha_f : (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    (alpha_g : (modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    (alpha_i : (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri)
    (alpha_j : (modulePullback j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rf.IsRightDerivedFunctor alpha_f
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor alpha_g
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Ri.IsRightDerivedFunctor alpha_i
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Rj.IsRightDerivedFunctor alpha_j
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (_hI : I.IsKInjective) :
    alpha_j.app (((modulePushforward f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj I)) ≫
        Rj.map (alpha_f.app ((HomotopyCategory.quotient _ _).obj I)) ≫
        (derivedPushforwardRestrictIso f i j g h Rf Rg Ri Rj
          alpha_f alpha_g alpha_i alpha_j).hom.app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) =
      DerivedCategory.Qh.map
          ((pushforwardRestrictHomotopyMap f i j g h.w).app
            ((HomotopyCategory.quotient _ _).obj I)) ≫
        alpha_g.app (((modulePullback i).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj I)) ≫
        Rg.map (alpha_i.app ((HomotopyCategory.quotient _ _).obj I)) := by
  have : (Rf ⋙ Rj).IsRightDerivedFunctor
      (Functor.whiskerLeft
        ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)) alpha_j ≫
        Functor.whiskerRight alpha_f Rj)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
    apply composite_isRightDerivedFunctor
      (DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)
      (modulePushforward f) (modulePullback j) Rf Rj alpha_f alpha_j
    intro K hK
    have := derivedRestrictionUnit_isIso j Rj alpha_j
    infer_instance
  dsimp only [derivedPushforwardRestrictIso]
  simp only [Functor.rightDerivedNatIso_hom, Functor.isoWhiskerRight_hom]
  rw [← pushforwardRestrictHomotopyIso_hom f i j g h]
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Category.assoc] using
    (Functor.rightDerivedNatTrans_app (Rf ⋙ Rj) (Ri ⋙ Rg)
      (Functor.whiskerLeft
        ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)) alpha_j ≫
        Functor.whiskerRight alpha_f Rj)
      (Functor.whiskerLeft
        ((modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ)) alpha_g ≫
        Functor.whiskerRight alpha_i Rg)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (Functor.whiskerRight (pushforwardRestrictHomotopyIso f i j g h).hom DerivedCategory.Qh)
      ((HomotopyCategory.quotient _ _).obj I))

end Stacks.Cohomology

end
