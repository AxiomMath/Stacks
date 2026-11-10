module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkBaseChangeMate
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeDerivedStalks
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Stalks
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.IndependenceUniverseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Tor-independent base change of algebraic spaces and the derived pullback

Let `S` be a scheme and let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over `S` with `g` and `f` Tor independent.  Stacks
0DKD says:

1. if `E ∈ D(𝒪_X)` has Tor amplitude in `[a, b]` as a complex of `f⁻¹𝒪_Y`-modules, then
   `L(g')^*E` has Tor amplitude in `[a, b]` as a complex of `f'⁻¹𝒪_{Y'}`-modules;
2. if `𝒢` is an `𝒪_X`-module flat over `Y`, then `L(g')^*𝒢 = (g')^*𝒢`.

## Main results

* `hasTorAmplitude_derivedScalarRestriction_smallEtaleDerivedModulePullback`, in the namespace
  `AlgebraicGeometry.Space`: **Stacks 0DKD (1)**.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedModulePullbackComparison_of_isFlatOver`:
  **Stacks 0DKD (2)**: the canonical comparison `L(g')^*𝒢 ⟶ (g')^*𝒢` is an isomorphism.
* `isIso_smallEtaleDerivedModulePullbackComparison_of_forall_isFlatOverAtGeometricPoint`, in the
  same namespace: the same for any `𝒪_X`-module whose geometric stalks are flat over the étale
  local rings of `Y`, the form in which part (2) is proved.

## Implementation notes

The proof is the source's: Tor amplitude and flatness are read at the geometric points of `X'`
(Stacks 0DJJ and 04K5).  `E` has cohomology in degrees at most `b`, so it is represented by a
bounded above complex `P` of flat `𝒪_X`-modules, which computes `L(g')^*` (Stacks 06YY) and has
K-flat stalk complexes.  At a geometric point `x̄'` of `X'` over `x̄` the stalk of `(g')^*P` is
`P_{x̄} ⊗ 𝒪_{X', x̄'}` (Stacks 05V5), the stalk of `f⁻¹𝒪_Y` is `𝒪_{Y, ȳ}`, and the ring-level
statements for the Tor-independent square of stalk rings — Stacks 0661 and 066L — finish the
argument.  Those ring-level statements need the stalk rings of the four corners in one
universe, so the square of rings is the square of stalks of the structure sheaves at the points
of the small étale sites, in the universe of the schemes; the Tor independence of Stacks 08IP
and the cartesian flatness `AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat` are stated
for the étale local rings of Stacks 04KG, one universe up, and are transported along
`AlgebraicGeometry.Space.pointStalkRingEquiv`.

Tor amplitude over `f⁻¹𝒪_Y` is measured against an arbitrary derived tensor product datum on the
ringed site `(X_étale, f⁻¹𝒪_Y)`, as everywhere in this development; by Stacks 08G1 it does not
depend on the datum.  Flatness over `Y` is Stacks 05VV, which the source defines for
quasi-coherent modules; the geometric-point statement needs no quasi-coherence.

## References

* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 066L](https://stacks.math.columbia.edu/tag/066L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose

/- The base's `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeDerivedStalks`,
imported for `AlgebraicGeometry.Space.scalarRestrictionStalkIso`, brings the global instance
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` into scope; it gives `Abelian` for these
categories of modules at a universe join that is never the one used here, so it is switched off
as in that file. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [LocallySmall.{u} C] (O : Sheaf J CommRingCat.{u})
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A morphism of complexes of sheaves of modules is a quasi-isomorphism as soon as its stalk
complexes at the members of a conservative family of points are. -/
theorem quasiIso_of_forall_sheafModuleFiberOfCommRing {I : Type*} (p : I → J.Point.{u})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    {K L : CochainComplex (SheafOfModules.{u} (commRingSheafToRingSheaf O)) ℤ} (φ : K ⟶ L)
    (h : ∀ i, QuasiIso (((sheafModuleFiberOfCommRing (p i) O).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  refine ⟨fun n => ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  refine isIso_of_isIso_sheafModuleFiber _ hp _ (fun Φ => ?_)
  obtain ⟨i, hi⟩ := (ObjectProperty.ofObj_iff _ Φ.obj).1 Φ.property
  rw [← hi]
  refine isIso_of_isIso_restrictScalars_map (commRingSheafFiberIso (p i) O).inv.hom _ ?_
  let F := sheafModuleFiberOfCommRing (p i) O
  let ψ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) n).map φ
  have hleft : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map ψ)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 ((h i).quasiIsoAt n)
  have hnat := ShortComplex.mapHomologyIso_hom_naturality ψ F
  have hc : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map ψ) ≫
      (ShortComplex.mapHomologyIso _ F).hom) := inferInstance
  rw [hnat] at hc
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (ShortComplex.mapHomologyIso _ F).hom _ _ hc

end Stacks

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section RelativeStalk

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- The stalk of `f⁻¹𝒪_Y` at the point of the small étale site of `X` given by `x̄`. -/
abbrev relativeStalkRing : CommRingCat.{u} :=
  Stacks.ringFiber (etaleSitePoint B S hS X.1 x X.2) (inverseImageRingedSite B S hS f).O.obj

/-- The stalk at `x̄` of the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
abbrev relativeStalkMap :
    relativeStalkRing f x →+*
      Stacks.ringFiber (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O.obj :=
  Stacks.SitePointBaseChange.stalkRingHom (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom
    (etaleSitePoint B S hS X.1 x X.2)

/-- The stalk of `f⁻¹𝒪_Y` at `x̄` is the étale local ring of `Y` at `f ∘ x̄`. -/
def relativeStalkRingEquiv :
    relativeStalkRing f x ≃+* etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x) :=
  ((smallEtaleInverseImageFiberRingIso B S hS f x).app
      (smallEtaleRingedTopos B S hS Y).O).symm.commRingCatIsoToRingEquiv.trans
    (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x))

/-- Read on the étale local rings, the stalk of `f⁻¹𝒪_Y ⟶ 𝒪_X` at `x̄` is the canonical
homomorphism of Stacks 04NG. -/
theorem pointStalkRingEquiv_relativeStalkMap (r : relativeStalkRing f x) :
    pointStalkRingEquiv B S hS X x (relativeStalkMap f x r) =
      etaleLocalRingMap X.2 f.hom x (relativeStalkRingEquiv f x r) := by
  rw [← stalkStructureMapAsEtaleLocalRingMap_eq]
  let e := (smallEtaleInverseImageFiberRingIso B S hS f x).app (smallEtaleRingedTopos B S hS Y).O
  change _ = pointStalkRingEquiv B S hS X x ((stalkStructureMap B S hS f x).hom
    ((pointStalkRingEquiv B S hS Y _).symm (pointStalkRingEquiv B S hS Y _ (e.inv.hom r))))
  have h1 : (pointStalkRingEquiv B S hS Y _).symm
      (pointStalkRingEquiv B S hS Y _ (e.inv.hom r)) = e.inv.hom r :=
    RingEquiv.symm_apply_apply _ _
  refine congrArg (pointStalkRingEquiv B S hS X x) ?_
  refine Eq.trans ?_ (congrArg (stalkStructureMap B S hS f x).hom h1).symm
  have h2 : e.inv ≫ stalkStructureMap B S hS f x =
      ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage :=
    e.inv_hom_id_assoc _
  exact (congrArg (fun φ => φ.hom r) h2).symm

end RelativeStalk

section Square

variable {X' X Y' Y : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) (x' : GeometricPoint B S hS X'.1)

include hpb in
/-- The two images in `Y` of a geometric point of the upper-left corner agree. -/
theorem geometricPointMap_eq_of_isPullback :
    geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
  congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hpb.w

/-- The homomorphism `(f⁻¹𝒪_Y)_{x̄} ⟶ (f'⁻¹𝒪_{Y'})_{x̄'}` of the bottom row of the square of
stalk rings at `x̄'`: the canonical homomorphism `𝒪_{Y, ȳ} ⟶ 𝒪_{Y', ȳ'}` of Stacks 04NG,
read through `relativeStalkRingEquiv`.  Only the commutativity `w` of the square is used. -/
def relativeBaseStalkMap (w : g' ≫ f = f' ≫ g) :
    relativeStalkRing f (geometricPointMap g'.hom x') →+* relativeStalkRing f' x' :=
  (relativeStalkRingEquiv f' x').symm.toRingHom.comp
    (((eqToHom (congrArg (etaleLocalRing B S hS Y.1)
        (congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') w)) ≫
      CommRingCat.ofHom (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).comp
      (relativeStalkRingEquiv f (geometricPointMap g'.hom x')).toRingHom)

/-- Read through `relativeStalkRingEquiv`, `relativeBaseStalkMap` is the canonical homomorphism
`𝒪_{Y, ȳ} ⟶ 𝒪_{Y', ȳ'}` of étale local rings. -/
theorem relativeStalkRingEquiv_relativeBaseStalkMap (w : g' ≫ f = f' ≫ g)
    (r : relativeStalkRing f (geometricPointMap g'.hom x')) :
    relativeStalkRingEquiv f' x' (relativeBaseStalkMap g' f' f g x' w r) =
      (eqToHom (congrArg (etaleLocalRing B S hS Y.1)
        (congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') w)) ≫
      CommRingCat.ofHom (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom
        (relativeStalkRingEquiv f (geometricPointMap g'.hom x') r) :=
  RingEquiv.apply_symm_apply _ _

/-- **Stacks 08IP at the stalks of the small étale sites.** -/
theorem torIndependent_relativeStalk (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom) :
    letI := (relativeStalkMap f (geometricPointMap g'.hom x')).toAlgebra
    letI := (relativeBaseStalkMap g' f' f g x' hpb.w).toAlgebra
    RingTheory.TorIndependence.TorIndependent (relativeStalkRing f (geometricPointMap g'.hom x'))
      (Stacks.ringFiber (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O.obj)
      (relativeStalkRing f' x') := by
  let := (relativeStalkMap f (geometricPointMap g'.hom x')).toAlgebra
  let := (relativeBaseStalkMap g' f' f g x' hpb.w).toAlgebra
  have hti := torIndependent_etaleLocalRing f g htor (geometricPointMap g'.hom x')
    (geometricPointMap f'.hom x') (geometricPointMap_eq_of_isPullback g' f' f g hpb x')
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1)
        (geometricPointMap_eq_of_isPullback g' f' f g hpb x')) ≫
      CommRingCat.ofHom (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
  exact (RingTheory.TorIndependence.torIndependent_congr_universe.{u, u + 1}
    (relativeStalkRingEquiv f (geometricPointMap g'.hom x'))
    (pointStalkRingEquiv B S hS X (geometricPointMap g'.hom x'))
    (relativeStalkRingEquiv f' x')
    (pointStalkRingEquiv_relativeStalkMap f (geometricPointMap g'.hom x'))
    (relativeStalkRingEquiv_relativeBaseStalkMap g' f' f g x' hpb.w)).1 hti

/-- **The cartesian input to Stacks 0DKD at the stalks of the small étale sites.** The stalk
of `𝒪_{X'}` at `x̄'` is flat over `(𝒪_X)_{x̄} ⊗_{(f⁻¹𝒪_Y)_{x̄}} (f'⁻¹𝒪_{Y'})_{x̄'}` through a ring
map restricting to the stalk pullback map of `g'` and to the stalk of `f'⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}`. -/
theorem exists_flat_relativeStalk_tensor :
    letI := (relativeStalkMap f (geometricPointMap g'.hom x')).toAlgebra
    letI := (relativeBaseStalkMap g' f' f g x' hpb.w).toAlgebra
    ∃ φ : Stacks.ringFiber (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
          (smallEtaleRingedTopos B S hS X).O.obj ⊗[relativeStalkRing f
            (geometricPointMap g'.hom x')]
          relativeStalkRing f' x' →+*
        Stacks.ringFiber (etaleSitePoint B S hS X'.1 x' X'.2)
          (smallEtaleRingedTopos B S hS X').O.obj,
      φ.comp Algebra.TensorProduct.includeLeftRingHom =
          smallEtaleStalkPullbackRingMap B S hS g' x' ∧
        φ.comp Algebra.TensorProduct.includeRight.toRingHom = relativeStalkMap f' x' ∧
        φ.Flat := by
  let := (relativeStalkMap f (geometricPointMap g'.hom x')).toAlgebra
  let := (relativeBaseStalkMap g' f' f g x' hpb.w).toAlgebra
  have h := geometricPointMap_eq_of_isPullback g' f' f g hpb x'
  obtain ⟨φ, hleft, hright, hflat⟩ := cartesian_etaleStalk_tensor_flat B S hS g' f' f g hpb x'
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫
      CommRingCat.ofHom (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
  let eA := pointStalkRingEquiv B S hS X (geometricPointMap g'.hom x')
  let eR := relativeStalkRingEquiv f (geometricPointMap g'.hom x')
  let eB := relativeStalkRingEquiv f' x'
  let eC := pointStalkRingEquiv B S hS X' x'
  let eT := tensorRingCongr eR eA eB (pointStalkRingEquiv_relativeStalkMap f _)
    (relativeStalkRingEquiv_relativeBaseStalkMap g' f' f g x' hpb.w)
  refine ⟨eC.symm.toRingHom.comp (φ.comp eT.toRingHom), ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => eC.injective ?_
    have := RingHom.congr_fun hleft (eA a)
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, RingEquiv.apply_symm_apply]
    refine Eq.trans ?_ (this.trans ?_)
    · refine congrArg φ ?_
      exact (show eT (a ⊗ₜ 1) = eA a ⊗ₜ eB 1 from rfl).trans (by rw [map_one]; rfl)
    · exact (RingHom.congr_fun
        (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS g' x')
        a).symm
  · refine RingHom.ext fun b => eC.injective ?_
    have := RingHom.congr_fun hright (eB b)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply] at this
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    refine Eq.trans ?_ (this.trans ?_)
    · refine congrArg φ ?_
      exact (show eT (1 ⊗ₜ b) = eA 1 ⊗ₜ eB b from rfl).trans (by rw [map_one]; rfl)
    · exact (pointStalkRingEquiv_relativeStalkMap f' x' b).symm
  · exact (RingHom.Flat.comp_iff_of_bijective_left eC.symm.bijective).2
      ((RingHom.Flat.comp_iff_of_bijective_right eT.bijective).2 hflat)

end Square

section ModuleStalks

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- The stalk complex at `x̄` of a complex of `𝒪_X`-modules, over `(𝒪_X)_{x̄}`. -/
abbrev stalkComplex (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    CochainComplex (ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O.obj)) ℤ :=
  ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The stalk complex at `x̄` of a complex read over `f⁻¹𝒪_Y` is the restriction of scalars of
its stalk complex along the stalk of `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
def scalarRestrictionRelativeStalkComplexIso
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    haveI := Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (inverseImageRingedSite B S hS f).O
    ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.restrictScalars (relativeStalkMap f x)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (stalkComplex x K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (scalarRestrictionStalkIso _ _ _ f x).app (K.X i))
    (fun i j _ => by
      simp only [Functor.mapHomologicalComplex_obj_d, Iso.app_hom]
      exact ((scalarRestrictionStalkIso _ _ _ f x).hom.naturality (K.d i j)).symm)

/-- The derived stalk at `x̄` of a complex read over `f⁻¹𝒪_Y` is the restriction of scalars of
its stalk complex along the stalk of `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
def derivedRelativeStalkIso (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    (Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).obj
        ((derivedScalarRestriction B S hS f).obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (relativeStalkMap f x)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (stalkComplex x K)) :=
  (Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
      (inverseImageRingedSite B S hS f).O).mapIso
      ((derivedScalarRestrictionFactors B S hS f).app K) ≪≫
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (inverseImageRingedSite B S hS f).O).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (scalarRestrictionRelativeStalkComplexIso f x K)

end ModuleStalks

section PullbackStalks

variable {X' X : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (x' : GeometricPoint B S hS X'.1)

/-- The pullback of modules from which the derived pullback of Stacks 06YY is built is the
pullback of modules `AlgebraicGeometry.Space.modulePullback` of Stacks 03LU. -/
theorem pullbackModules_smallEtaleRingedToposHom :
    (smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules = modulePullback B S hS g' :=
  RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom
    (smallEtaleRingedToposHom B S hS g')

/-- **Stacks 05V5 at a geometric point**, for the pullback of modules the derived pullback is
built from. -/
def pullbackStalkFunctorIso :
    (smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules ⋙
        Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
          (smallEtaleRingedTopos B S hS X').O ≅
      Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
          (smallEtaleRingedTopos B S hS X).O ⋙
        ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS g' x') :=
  eqToIso (congrArg (· ⋙ _) (pullbackModules_smallEtaleRingedToposHom g')) ≪≫
    modulePullbackFiberIso B S hS g' x'

/-- **Stacks 05V5 for complexes, at a geometric point**, naturally in the complex. -/
def pullbackStalkComplexNatIso :
    haveI := Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
      (smallEtaleRingedTopos B S hS X').O
    haveI := Stacks.instAdditiveSheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
      (smallEtaleRingedTopos B S hS X).O
    (smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
          (smallEtaleRingedTopos B S hS X').O).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
          (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars
          (smallEtaleStalkPullbackRingMap B S hS g' x')).mapHomologicalComplex
            (ComplexShape.up ℤ) :=
  haveI := Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
    (smallEtaleRingedTopos B S hS X').O
  haveI := Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2) (smallEtaleRingedTopos B S hS X).O
  Functor.mapHomologicalComplexCompIso (pullbackStalkFunctorIso g' x') _ ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O ⋙
      ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS g' x'))) _).symm

/-- **Stacks 05V5 for complexes, at a geometric point.** The stalk complex at `x̄'` of the
degreewise pullback of a complex along `g'` is the extension of scalars of its stalk complex at
`g' ∘ x̄'`. -/
def pullbackStalkComplexIso (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    stalkComplex x'
        (((smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS g' x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (stalkComplex (geometricPointMap g'.hom x') K) :=
  (pullbackStalkComplexNatIso g' x').app K

end PullbackStalks

section Resolutions

variable {X : AlgebraicSpaces B S hS}

/-- Every complex of `𝒪_X`-modules with cohomology in degrees at most `b` is quasi-isomorphic
to a complex of flat `𝒪_X`-modules vanishing above `b`. -/
theorem exists_flat_resolution
    (M : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) (b : ℤ)
    (hM : M.IsStrictlyLE b) :
    ∃ (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
      (q : P ⟶ M), QuasiIso q ∧
      P.IsStrictlyLE b ∧
      ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (smallEtaleRingedTopos B S hS X).O) (P.X i) := by
  let Pflat : ObjectProperty (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
    fun G => AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS X).O) G
  let _ : Pflat.ContainsZero :=
    ⟨⟨kernel (𝟙 (_root_.SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))),
      isZero_kernel_of_mono _,
      Stacks.SheafOfModules.DerivedTensorProduct.isFlat_kernel_id_unit
        (Y := smallEtaleRingedSite B S hS X.1 X.2)⟩⟩
  have hcover : ∀ G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X),
      ∃ (G' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (_ : Pflat G')
        (f : G' ⟶ G), Epi f := by
    intro G
    obtain ⟨G', f, hG', hf⟩ :=
      Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat (smallEtaleRingedTopos B S hS X).O G
    exact ⟨G', hG', f, hf⟩
  obtain ⟨P, q, -, hq, hPflat, hPLE⟩ := (CochainComplex.exists_quasiIso_prop Pflat hcover b).1 M
  exact ⟨P, q, hq, hPLE, hPflat⟩

end Resolutions

section Bounded

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` reflects vanishing of cohomology above a
degree: it does not change the underlying sheaves of abelian groups. -/
theorem isLE_of_isLE_derivedScalarRestriction
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (b : ℤ)
    (h : ((derivedScalarRestriction B S hS f).obj E).IsLE b) : E.IsLE b := by
  rw [DerivedCategory.isLE_iff] at h ⊢
  intro i hi
  have hz := (h i hi).of_iso
    (((scalarRestriction B S hS f).mapDerivedCategoryHomologyIso i).app E).symm
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  apply (scalarRestriction B S hS f).map_injective
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]

/-- **The stalk of a module flat over `Y` at `x̄` is flat over the stalk of `f⁻¹𝒪_Y`.** The
geometric stalk `F_{x̄}` flat over `𝒪_{Y, ȳ}` (Stacks 05VU (2)) is the stalk of `F` at the point
of the small étale site, read over `(f⁻¹𝒪_Y)_{x̄}`. -/
theorem flat_relativeStalk_of_isFlatOverAtGeometricPoint (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsFlatOverAtGeometricPoint B S hS f G x) :
    Module.Flat (relativeStalkRing f x)
      ((ModuleCat.restrictScalars (relativeStalkMap f x)).obj
        (Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O G)) := by
  let N := geometricModuleStalk B S hS X x G
  let Ret := etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x)
  let eR := relativeStalkRingEquiv f x
  let γ := etaleLocalRingMap X.2 f.hom x
  let instRet : Module Ret N := Module.compHom N γ
  have hN : Module.Flat Ret N := hG
  let : Algebra (relativeStalkRing f x) Ret := eR.toRingHom.toAlgebra
  let instR : Module (relativeStalkRing f x) N := Module.compHom N (γ.comp eR.toRingHom)
  have : IsScalarTower (relativeStalkRing f x) Ret N :=
    ⟨fun r s n => by
      change (γ (eR r * s)) • n = (γ (eR r)) • ((γ s) • n)
      rw [map_mul, mul_smul]⟩
  have : Module.Flat (relativeStalkRing f x) Ret :=
    RingHom.Flat.of_bijective (f := eR.toRingHom) eR.bijective
  have : Module.Flat (relativeStalkRing f x) N := Module.Flat.trans _ Ret N
  let L := Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O G
  let ε := geometricModuleStalkAddEquiv B S hS X x G
  let e : Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O G
      ≃+ N := L.symm.toAddEquiv.trans ε
  have he : ∀ (r : relativeStalkRing f x)
      (m : Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O G),
      e (relativeStalkMap f x r • m) = γ (eR r) • e m := fun r m =>
    ((congrArg ε (L.symm.map_smul (relativeStalkMap f x r) m)).trans
      (geometricModuleStalkAddEquiv_smul B S hS X x G (relativeStalkMap f x r) (L.symm m))).trans
      (congrArg (· • ε (L.symm m)) (pointStalkRingEquiv_relativeStalkMap f x r))
  let δ : ((ModuleCat.restrictScalars (relativeStalkMap f x)).obj
      (Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O G))
        ≃ₗ[relativeStalkRing f x] N :=
    AddEquiv.toLinearEquiv e he
  exact Module.Flat.of_linearEquiv δ

/-- **Quasi-isomorphisms of complexes of `𝒪_X`-modules are detected at the geometric points**
(Stacks 04K5): the stalk functors are exact and jointly conservative. -/
theorem quasiIso_of_forall_stalkComplex {K L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ}
    (φ : K ⟶ L)
    (h : ∀ x : GeometricPoint B S hS X.1,
      QuasiIso (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ :=
  Stacks.quasiIso_of_forall_sheafModuleFiberOfCommRing (smallEtaleRingedTopos B S hS X).O
    (fun x : GeometricPoint B S hS X.1 => etaleSitePoint B S hS X.1 x X.2)
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2) φ h

end Bounded

section Main

open Stacks.SheafOfModules.DerivedTensorProduct StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude (hasTorAmplitudeCanonical_of_iso)

variable {X' X Y' Y : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g)

/-- The stalk complex of a bounded above complex of flat modules is K-flat. -/
theorem kFlat_stalkComplex (x : GeometricPoint B S hS X.1)
    (P : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (b : ℤ) (hP : P.IsStrictlyLE b)
    (hflat : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS X).O) (P.X i)) :
    (stalkComplex x P).KFlat := by
  have : (stalkComplex x P).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O).map_isZero (P.isZero_of_isStrictlyLE b i hi)
  have : ∀ n, Module.Flat (Stacks.ringFiber (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O.obj) ((stalkComplex x P).X n) := fun n =>
    Stacks.isFlatModuleStalk_of_isFlat_freeUniverse (smallEtaleRingedTopos B S hS X).O (P.X n)
      (etaleSitePoint B S hS X.1 x X.2) (hflat n)
  exact CochainComplex.KFlat.kFlat_of_flat.{u, u} (stalkComplex x P) b

/-- A flat `A ⊗[R] R'`-algebra structure on `C` compatible with `A → C` and `R' → C` gives a
pushout `T` of `A ← R → R'` with `C` a flat `T`-algebra and the scalar towers over `T`. -/
private theorem exists_flat_pushout_algebra {R A R' C : Type u} [CommRing R] [CommRing A]
    [CommRing R'] [CommRing C] [Algebra R A] [Algebra R R'] [Algebra A C] [Algebra R' C]
    (φ : A ⊗[R] R' →+* C)
    (hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap A C)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap R' C)
    (hflat : φ.Flat) {P : Prop}
    (h : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra A T] [Algebra R' T]
      [IsScalarTower R A T] [IsScalarTower R R' T] [Algebra.IsPushout R A R' T] [Algebra T C]
      [IsScalarTower A T C] [IsScalarTower R' T C] [Module.Flat T C], P) : P := by
  let : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R R' (A ⊗[R] R') := Algebra.TensorProduct.right_isScalarTower
  let : Algebra.IsPushout R A R' (A ⊗[R] R') := TensorProduct.isPushout
  let : Algebra (A ⊗[R] R') C := φ.toAlgebra
  let : IsScalarTower A (A ⊗[R] R') C := IsScalarTower.of_algebraMap_eq' hleft.symm
  let : IsScalarTower R' (A ⊗[R] R') C := IsScalarTower.of_algebraMap_eq' hright.symm
  let : Module.Flat (A ⊗[R] R') C := hflat
  exact h (A ⊗[R] R')

include hpb in
/-- **Stacks 0DKD (1) at a geometric point of the upper-left corner**, for the stalk complex of
a K-flat complex. -/
theorem hasTorAmplitudeCanonical_relativeStalk_pullback
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom) (x' : GeometricPoint B S hS X'.1)
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hK : (stalkComplex (geometricPointMap g'.hom x') K).KFlat) (a b : ℤ)
    (hamp : HasTorAmplitudeCanonical (relativeStalkRing f (geometricPointMap g'.hom x'))
      ((ModuleCat.restrictScalars
          (relativeStalkMap f (geometricPointMap g'.hom x'))).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (stalkComplex (geometricPointMap g'.hom x') K))) a b) :
    HasTorAmplitudeCanonical (relativeStalkRing f' x')
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (relativeStalkMap f' x')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars
              (smallEtaleStalkPullbackRingMap B S hS g' x')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (stalkComplex (geometricPointMap g'.hom x') K)))) a b := by
  let := (relativeStalkMap f (geometricPointMap g'.hom x')).toAlgebra
  let := (relativeBaseStalkMap g' f' f g x' hpb.w).toAlgebra
  obtain ⟨φ, hleft, hright, hflat⟩ := exists_flat_relativeStalk_tensor g' f' f g hpb x'
  let : Algebra _ _ := (smallEtaleStalkPullbackRingMap B S hS g' x').toAlgebra
  let : Algebra _ _ := (relativeStalkMap f' x').toAlgebra
  refine exists_flat_pushout_algebra φ hleft hright hflat ?_
  intro T
  intros
  exact
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_torIndependent_flatBaseChange
    (T := T) (torIndependent_relativeStalk g' f' f g hpb x' htor) _ hK a b hamp

include hpb in
/-- **Stacks 0DKD (1).** Let `X' → X`, `Y' → Y` be a cartesian square of algebraic spaces over
`S` with `X` and `Y'` Tor independent over `Y`. If `E ∈ D(𝒪_X)` has Tor amplitude in `[a, b]`
as a complex of `f⁻¹𝒪_Y`-modules, then `L(g')^*E` has Tor amplitude in `[a, b]` as a complex
of `f'⁻¹𝒪_{Y'}`-modules. -/
@[stacks 0DKD "part (1)"]
theorem hasTorAmplitude_derivedScalarRestriction_smallEtaleDerivedModulePullback
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (T : Stacks.SheafOfModules.DerivedTensorProduct (inverseImageRingedSite B S hS f))
    (T' : Stacks.SheafOfModules.DerivedTensorProduct (inverseImageRingedSite B S hS f'))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a b : ℤ)
    (hE : HasTorAmplitude T ((derivedScalarRestriction B S hS f).obj E) a b) :
    HasTorAmplitude T' ((derivedScalarRestriction B S hS f').obj
      ((smallEtaleDerivedModulePullback B S hS g').obj E)) a b := by
  have : E.IsLE b := isLE_of_isLE_derivedScalarRestriction f E b (isLE_of_hasTorAmplitude T _ hE)
  obtain ⟨M, hM, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E b
  obtain ⟨P, q, hq, hPLE, hPflat⟩ := exists_flat_resolution M b hM
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  let eP : DerivedCategory.Q.obj P ≅ E := asIso (DerivedCategory.Q.map q) ≪≫ eM.symm
  refine hasTorAmplitude_of_forall_derivedModuleFiber_family T' _ a b
    (fun x' : GeometricPoint B S hS X'.1 => etaleSitePoint B S hS X'.1 x' X'.2)
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X'.1 X'.2) (fun x' => ?_)
  let x := geometricPointMap g'.hom x'
  have hx := hasTorAmplitudeCanonical_derivedModuleFiber T _ a b hE
    (etaleSitePoint B S hS X.1 x X.2)
  have hx' := hasTorAmplitudeCanonical_of_iso
    ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).mapIso
        ((derivedScalarRestriction B S hS f).mapIso eP.symm) ≪≫
      derivedRelativeStalkIso f x P ≪≫
      ((ModuleCat.restrictScalars (relativeStalkMap f x)).mapDerivedCategoryFactors.app
        (stalkComplex x P)).symm) a b hx
  have hup := hasTorAmplitudeCanonical_relativeStalk_pullback g' f' f g hpb htor x' P
    (kFlat_stalkComplex x P b hPLE hPflat) a b hx'
  exact hasTorAmplitudeCanonical_of_iso
    (DerivedCategory.Q.mapIso
        (((ModuleCat.restrictScalars (relativeStalkMap f' x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso (pullbackStalkComplexIso g' x' P)).symm ≪≫
      (derivedRelativeStalkIso f' x' _).symm ≪≫
      (Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
        (inverseImageRingedSite B S hS f').O).mapIso
        ((derivedScalarRestriction B S hS f').mapIso
          ((@nonempty_smallEtaleDerivedModulePullback_obj_Q_iso B S hS X' X g' P b hPLE
            hPflat).some.symm ≪≫
            (smallEtaleDerivedModulePullback B S hS g').mapIso eP))) a b hup

include hpb in
/-- **Stacks 0DKD (2) at a geometric point of the upper-left corner.** Extension of scalars
along the stalk pullback map of `g'` carries a K-flat resolution of a module flat over the stalk
of `f⁻¹𝒪_Y` to a resolution. -/
theorem quasiIso_extendScalars_relativeStalk
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom) (x' : GeometricPoint B S hS X'.1)
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hK : (stalkComplex (geometricPointMap g'.hom x') K).KFlat)
    (M : ModuleCat.{u} (Stacks.ringFiber
      (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
      (smallEtaleRingedTopos B S hS X).O.obj))
    (hM : Module.Flat (relativeStalkRing f (geometricPointMap g'.hom x'))
      ((ModuleCat.restrictScalars (relativeStalkMap f (geometricPointMap g'.hom x'))).obj M))
    (q : stalkComplex (geometricPointMap g'.hom x') K ⟶
      (CochainComplex.singleFunctor _ 0).obj M) [QuasiIso q] :
    QuasiIso (((ModuleCat.extendScalars
        (smallEtaleStalkPullbackRingMap B S hS g' x')).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  let := (relativeStalkMap f (geometricPointMap g'.hom x')).toAlgebra
  let := (relativeBaseStalkMap g' f' f g x' hpb.w).toAlgebra
  obtain ⟨φ, hleft, hright, hflat⟩ := exists_flat_relativeStalk_tensor g' f' f g hpb x'
  let : Algebra _ _ := (smallEtaleStalkPullbackRingMap B S hS g' x').toAlgebra
  let : Algebra _ _ := (relativeStalkMap f' x').toAlgebra
  refine exists_flat_pushout_algebra φ hleft hright hflat ?_
  intro T
  intros
  exact RingTheory.TorIndependence.quasiIso_extendScalars_of_flat_of_flat (T := T)
    (torIndependent_relativeStalk g' f' f g hpb x' htor) _ hK M hM q

/-- Invertibility of the derived-pullback comparison propagates along a quasi-isomorphism whose
degreewise pullback is again a quasi-isomorphism. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_of_quasiIso
    {K L : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ}
    (q : K ⟶ L) (hq : QuasiIso q)
    (hpq : QuasiIso
      (((smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).map q))
    (hcK : IsIso ((smallEtaleDerivedModulePullbackComparison B S hS g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) := by
  let qh := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q
  have hq₀ : IsIso (DerivedCategory.Qh.map qh) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) q).mpr
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).mpr hq)
  have hq₂ : IsIso ((smallEtaleModulePullbackOnHomotopy B S hS g').map qh) := by
    change IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      (((smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).map q))
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _).mpr
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hpq)
  have hq₁ : IsIso ((smallEtaleDerivedModulePullback B S hS g').map (DerivedCategory.Qh.map qh)) :=
    Functor.map_isIso _ _
  have hn := (smallEtaleDerivedModulePullbackComparison B S hS g').naturality qh
  have hcomp : IsIso ((smallEtaleDerivedModulePullback B S hS g').map (DerivedCategory.Qh.map qh) ≫
      (smallEtaleDerivedModulePullbackComparison B S hS g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) := by
    have h' : IsIso ((smallEtaleDerivedModulePullbackComparison B S hS g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        (smallEtaleModulePullbackOnHomotopy B S hS g').map qh) := IsIso.comp_isIso' hcK hq₂
    rwa [← hn] at h'
  exact IsIso.of_isIso_comp_left
    ((smallEtaleDerivedModulePullback B S hS g').map (DerivedCategory.Qh.map qh)) _

include hpb in
/-- **Stacks 0DKD (2), at the geometric points.** For a cartesian square of algebraic spaces
with `X` and `Y'` Tor independent over `Y`, and an `𝒪_X`-module `𝒢` whose geometric stalks are
flat over the étale local rings of `Y` (Stacks 05VU (2)), the canonical comparison
`L(g')^*𝒢 ⟶ (g')^*𝒢` is an isomorphism. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_of_forall_isFlatOverAtGeometricPoint
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hG : ∀ x, IsFlatOverAtGeometricPoint B S hS f G x) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj G))) := by
  obtain ⟨P, q, hq, hPLE, hPflat⟩ := exists_flat_resolution ((CochainComplex.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj G) 0 inferInstance
  have hPK := @smallEtaleModuleKFlat_of_isStrictlyLE B S hS X P 0 hPLE hPflat
  refine isIso_smallEtaleDerivedModulePullbackComparison_of_quasiIso g' q hq ?_
    (isIso_smallEtaleDerivedModulePullbackComparison_app B S hS g' _ hPK)
  refine quasiIso_of_forall_stalkComplex _ (fun x' => ?_)
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoOfNatIso (pullbackStalkComplexNatIso g' x')
    (Arrow.mk q))).2 ?_
  let x := geometricPointMap g'.hom x'
  let F := Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O
  have : F.Additive := Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O
  have : PreservesFiniteLimits F := Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O
  have : PreservesFiniteColimits F := Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O
  let E := ModuleCat.extendScalars.{u, u, u} (smallEtaleStalkPullbackRingMap B S hS g' x')
  let s := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app G
  let qL := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ s.hom
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology q F
  have : QuasiIso qL := inferInstanceAs (QuasiIso (_ ≫ _))
  have hring : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map qL) :=
    quasiIso_extendScalars_relativeStalk g' f' f g hpb htor x' P
      (kFlat_stalkComplex x P 0 hPLE hPflat) (F.obj G)
      (flat_relativeStalk_of_isFlatOverAtGeometricPoint f x G (hG x)) qL
  have : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map s.hom) := inferInstance
  have hc : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫
      (E.mapHomologicalComplex (ComplexShape.up ℤ)).map s.hom) := by
    rwa [← Functor.map_comp]
  exact (quasiIso_iff_comp_right _ _).1 hc

include hpb in
/-- **Stacks 0DKD (2).** For a cartesian square of algebraic spaces with `X` and `Y'` Tor
independent over `Y`, and a quasi-coherent `𝒪_X`-module `𝒢` flat over `Y` (Stacks 05VV), the
canonical comparison `L(g')^*𝒢 ⟶ (g')^*𝒢` is an isomorphism. -/
@[stacks 0DKD "part (2)"]
theorem isIso_smallEtaleDerivedModulePullbackComparison_of_isFlatOver
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    [G.IsQuasicoherentOnSite] (hG : IsFlatOver B S hS X.2 f.hom G) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj G))) :=
  isIso_smallEtaleDerivedModulePullbackComparison_of_forall_isFlatOverAtGeometricPoint g' f' f g
    hpb htor G ((isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f G).1 hG)

end Main

end AlgebraicGeometry.Space
