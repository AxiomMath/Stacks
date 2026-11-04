module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutGlueSectionsChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutChartAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealMeet
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType

/-!
# The unit and the counit of the gluing of modules over a Milnor cube of chart rings

For a commuting square `U ⟶ V ⟶ V'`, `U ⟶ U' ⟶ V'` of representable morphisms and an étale chart
`W` of `V'` whose base changes `W_V`, `W_{U'}` and `W_U` are affine, suppose the rings of functions
on `W`, `W_V`, `W_{U'}` and `W_U`, with their restriction maps, sit in a cube of rings over a
fibre product `B' = B ×_A A'` with `A' ⟶ A` surjective, the three faces through `B' ⟶ Γ(W)` being
pushouts (`Stacks.Pushout.IsMilnorCube`).  Then on the sections over `W`:

* the unit `M ⟶ (glue ∘ restrict)(M)` of the gluing adjunction is bijective for a quasi-coherent
  module `M` on `V'` whose sections over `W` are flat over `B'`;
* the two components of the counit `(restrict ∘ glue)(T) ⟶ T` are bijective over `W_V` and
  `W_{U'}` for a triple `T` of quasi-coherent modules, once the glued module is quasi-coherent;
* the sections of the glued module of a triple of quasi-coherent modules whose components are
  flat over `B` and `A'` are flat over `B'`.

These are the module statements of Stacks 07RW over the cube
(`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/ThickeningPushoutChartAlgebra.lean`), read through
the description of the sections of the glued module as compatible pairs
(`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/ThickeningPushoutGlueSections.lean`) and the base
change description of the sections of an inverse image over affine charts (Stacks 083K).

## Main definitions

* `AlgebraicGeometry.Space.PushoutModules.glueGamma`: the comparison of the two base changes to
  `W_U` of the two components of a triple of quasi-coherent modules, through the triple's
  isomorphism.

## Main results

* `AlgebraicGeometry.Space.PushoutModules.bijective_squareUnit_app_of_isMilnorCube`
* `AlgebraicGeometry.Space.PushoutModules.bijective_squareCounit_target_app_of_isMilnorCube`
* `AlgebraicGeometry.Space.PushoutModules.bijective_squareCounit_ambient_app_of_isMilnorCube`
* `AlgebraicGeometry.Space.PushoutModules.flat_glue_sections_of_isMilnorCube`

## References

* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
* [Stacks Project, Tag 07RW](https://stacks.math.columbia.edu/tag/07RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Space.PushoutModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U V U' V' : AlgebraicSpaces B S hS} (t : U ⟶ V) (v : V ⟶ V') (a : U ⟶ U') (u' : U' ⟶ V')
    (h : a ≫ u' = t ≫ v)
    (ht : yoneda.relativelyRepresentable t.hom) (hv : yoneda.relativelyRepresentable v.hom)
    (ha : yoneda.relativelyRepresentable a.hom) (hu' : yoneda.relativelyRepresentable u'.hom)
    (htv : yoneda.relativelyRepresentable (t ≫ v).hom)
    (hau : yoneda.relativelyRepresentable (a ≫ u').hom)
    (W : SmallEtale B S hS V'.1)

/-- The pullback of functions from `W_V` to `W_U`. -/
abbrev cubeTargetRestrict :
    chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W) →+*
      chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W) :=
  chartDiagramRestrict B S hS t (targetDiagram t v ht hv htv W)

/-- The pullback of functions from `W_{U'}` to `W_U`. -/
abbrev cubeAmbientRestrict :
    chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W) →+*
      chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W) :=
  chartDiagramRestrict B S hS a (ambientDiagram t v a u' h ha hu' htv hau W)

variable (T : SquareTriple t a) (hG : T.target.IsQuasicoherentOnSite)
    (hF : T.ambient.IsQuasicoherentOnSite)
    (hWV : IsAffine (chartScheme ((smallBaseChange B S hS v hv).obj W)))
    (hWU' : IsAffine (chartScheme ((smallBaseChange B S hS u' hu').obj W)))
    (hWU : IsAffine (chartScheme ((smallBaseChange B S hS (t ≫ v) htv).obj W)))

/-- The isomorphism of a triple, on the sections over `W_U`. -/
def glueComparisonIso :
    ModuleCat.of (chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W))
        (((modulePullback B S hS t).obj T.target).val.obj
          (op ((smallBaseChange B S hS (t ≫ v) htv).obj W))) ≅
      ModuleCat.of (chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W))
        (((modulePullback B S hS a).obj T.ambient).val.obj
          (op ((smallBaseChange B S hS (t ≫ v) htv).obj W))) :=
  (LinearEquiv.ofBijective (T.comparison.hom.val.app
      (op ((smallBaseChange B S hS (t ≫ v) htv).obj W))).hom
    (Function.bijective_iff_has_inverse.2 ⟨(T.comparison.inv.val.app
        (op ((smallBaseChange B S hS (t ≫ v) htv).obj W))).hom,
      fun y => sheafOfModules_iso_hom_inv_apply T.comparison _ y,
      fun y => sheafOfModules_iso_inv_hom_apply T.comparison _ y⟩)).toModuleIso

include hG hWU hWV in
/-- For `G` quasi-coherent and `W_U`, `W_V` affine, the base change map from the sections of `G`
over `W_V` to the sections of `t^*G` over `W_U` is bijective. -/
theorem bijective_targetBaseChange :
    letI := chartDiagramAlgebra B S hS t (targetDiagram t v ht hv htv W)
    Function.Bijective (modulePullbackChartBaseChange B S hS t T.target
      (targetDiagram t v ht hv htv W)) :=
  bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS t T.target hG _ hWU hWV

include hF hWU hWU' in
/-- For `F` quasi-coherent and `W_U`, `W_{U'}` affine, the base change map from the sections of `F`
over `W_{U'}` to the sections of `a^*F` over `W_U` is bijective. -/
theorem bijective_ambientBaseChange :
    letI := chartDiagramAlgebra B S hS a (ambientDiagram t v a u' h ha hu' htv hau W)
    Function.Bijective (modulePullbackChartBaseChange B S hS a T.ambient
      (ambientDiagram t v a u' h ha hu' htv hau W)) :=
  bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS a T.ambient hF _ hWU
    hWU'

/-- **The comparison of the two base changes to `W_U`** of the two components of a triple of
quasi-coherent modules, through the triple's isomorphism. -/
def glueGamma :
    (ModuleCat.extendScalars (cubeTargetRestrict t v ht hv htv W)).obj
        (ModuleCat.of _ (T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W)))) ≅
      (ModuleCat.extendScalars (cubeAmbientRestrict t v a u' h ha hu' htv hau W)).obj
        (ModuleCat.of _ (T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W)))) :=
  chartBaseChangeIso B S hS t T.target (targetDiagram t v ht hv htv W)
      (bijective_targetBaseChange t v a ht hv htv W T hG hWV hWU) ≪≫
    glueComparisonIso t v a htv W T ≪≫
    (chartBaseChangeIso B S hS a T.ambient (ambientDiagram t v a u' h ha hu' htv hau W)
      (bijective_ambientBaseChange t v a u' h ha hu' htv hau W T hF hWU' hWU)).symm

/-- **The comparison of the two base changes on the elements `1 ⊗ x`**: it carries `1 ⊗ x` to
`1 ⊗ y` exactly when the triple's isomorphism carries the chart section of `x` over `W_U` to the
chart section of `y`. -/
theorem glueGamma_hom_one_tmul_eq_iff
    (x : T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W)))
    (y : T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W))) :
    (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU).hom
        ((1 : chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W)) ⊗ₜ[
          chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W),
          cubeTargetRestrict t v ht hv htv W] x) =
      (1 : chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W)) ⊗ₜ[
          chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W),
          cubeAmbientRestrict t v a u' h ha hu' htv hau W] y ↔
      T.comparison.hom.val.app _
          (modulePullbackChartSection B S hS t T.target (targetDiagram t v ht hv htv W) x) =
        modulePullbackChartSection B S hS a T.ambient
          (ambientDiagram t v a u' h ha hu' htv hau W) y := by
  set bt := chartBaseChangeIso B S hS t T.target (targetDiagram t v ht hv htv W)
      (bijective_targetBaseChange t v a ht hv htv W T hG hWV hWU) with hbt
  set ba := chartBaseChangeIso B S hS a T.ambient (ambientDiagram t v a u' h ha hu' htv hau W)
      (bijective_ambientBaseChange t v a u' h ha hu' htv hau W T hF hWU' hWU) with hba
  have e1 : (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU).hom
      ((1 : chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W)) ⊗ₜ[
          chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W),
          cubeTargetRestrict t v ht hv htv W] x) =
      ba.inv (T.comparison.hom.val.app _
        (modulePullbackChartSection B S hS t T.target (targetDiagram t v ht hv htv W) x)) := by
    change ba.inv ((glueComparisonIso t v a htv W T).hom (bt.hom _)) = _
    exact congrArg (fun z => ba.inv ((glueComparisonIso t v a htv W T).hom z))
      (chartBaseChangeIso_hom_one_tmul B S hS t T.target (targetDiagram t v ht hv htv W)
        (bijective_targetBaseChange t v a ht hv htv W T hG hWV hWU) x)
  have e2 : (1 : chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W)) ⊗ₜ[
          chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W),
          cubeAmbientRestrict t v a u' h ha hu' htv hau W] y =
      ba.inv (modulePullbackChartSection B S hS a T.ambient
          (ambientDiagram t v a u' h ha hu' htv hau W) y) :=
    (Iso.hom_inv_id_apply ba _).symm.trans (congrArg ba.inv
      (chartBaseChangeIso_hom_one_tmul B S hS a T.ambient
        (ambientDiagram t v a u' h ha hu' htv hau W)
        (bijective_ambientBaseChange t v a u' h ha hu' htv hau W T hF hWU' hWU) y))
  rw [e1, e2]
  refine ⟨fun hq => ?_, fun hq => congrArg ba.inv hq⟩
  have := congrArg ba.hom hq
  rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this

/-! ### The two coordinates are semilinear -/

/-- The first coordinate of a sum of sections of the glued module is the sum of their first
coordinates. -/
theorem gluePr₁_add (p q : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) :
    gluePr₁ t v a u' h hv T W (p + q) =
      gluePr₁ t v a u' h hv T W p + gluePr₁ t v a u' h hv T W q :=
  (congrArg (chartModProj B S hS v hv T.target W)
    (map_add ((TripleGluing.glueFst (qV := modulePushforward B S hS v)
      (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
      (compTransport a u' (t ≫ v) h) T).val.app (op W)).hom p q)).trans
    (chartModProj_add B S hS v hv T.target W _ _)

/-- The second coordinate of a sum of sections of the glued module is the sum of their second
coordinates. -/
theorem gluePr₂_add (p q : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) :
    gluePr₂ t v a u' h hu' T W (p + q) =
      gluePr₂ t v a u' h hu' T W p + gluePr₂ t v a u' h hu' T W q :=
  (congrArg (chartModProj B S hS u' hu' T.ambient W)
    (map_add ((TripleGluing.glueSnd (qV := modulePushforward B S hS v)
      (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
      (compTransport a u' (t ≫ v) h) T).val.app (op W)).hom p q)).trans
    (chartModProj_add B S hS u' hu' T.ambient W _ _)

/-- The first coordinate of `d • p` is the restriction of `d` to `W_V` acting on the first
coordinate of `p`. -/
theorem gluePr₁_smul (d : chartRing B S hS V'.1 V'.2 W)
    (p : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) :
    gluePr₁ t v a u' h hv T W (d • p) =
      baseChangeChartRestrict B S hS v hv W d • gluePr₁ t v a u' h hv T W p :=
  (congrArg (chartModProj B S hS v hv T.target W)
    (map_smul ((TripleGluing.glueFst (qV := modulePushforward B S hS v)
      (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
      (compTransport a u' (t ≫ v) h) T).val.app (op W)).hom d p)).trans
    (chartModProj_smul B S hS v hv T.target W d _)

/-- The second coordinate of `d • p` is the restriction of `d` to `W_{U'}` acting on the second
coordinate of `p`. -/
theorem gluePr₂_smul (d : chartRing B S hS V'.1 V'.2 W)
    (p : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) :
    gluePr₂ t v a u' h hu' T W (d • p) =
      baseChangeChartRestrict B S hS u' hu' W d • gluePr₂ t v a u' h hu' T W p :=
  (congrArg (chartModProj B S hS u' hu' T.ambient W)
    (map_smul ((TripleGluing.glueSnd (qV := modulePushforward B S hS v)
      (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
      (compTransport a u' (t ≫ v) h) T).val.app (op W)).hom d p)).trans
    (chartModProj_smul B S hS u' hu' T.ambient W d _)

/-- The two coordinates of a section of the glued module have equal images under `glueGamma`. -/
private theorem glueGamma_one_tmul_gluePr (p : ((TripleGluing.glueFunctor
    (qV := modulePushforward B S hS v) (qA := modulePushforward B S hS u')
    (modulePullbackAdjunction B S hS t) (modulePullbackAdjunction B S hS a)
    (modulePushforwardCompIso B S hS t v) (compTransport a u' (t ≫ v) h)).obj T).val.obj
    (op W)) :
    (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU).hom
        ((1 : chartRing B S hS U.1 U.2 _) ⊗ₜ[_,cubeTargetRestrict t v ht hv htv W]
          gluePr₁ t v a u' h hv T W p) =
      (1 : chartRing B S hS U.1 U.2 _) ⊗ₜ[_,cubeAmbientRestrict t v a u' h ha hu' htv hau W]
        gluePr₂ t v a u' h hu' T W p :=
  (glueGamma_hom_one_tmul_eq_iff t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU _ _).2
    (glue_sections_compat t v a u' h ht hv ha hu' htv hau T W p)

/-- Two sections over `W_V` and `W_{U'}` matched by `glueGamma` come from a section of the glued
module. -/
private theorem glue_exists_of_glueGamma
    (x : T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W)))
    (y : T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W)))
    (hxy : (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU).hom
        ((1 : chartRing B S hS U.1 U.2 _) ⊗ₜ[_,cubeTargetRestrict t v ht hv htv W] x) =
      (1 : chartRing B S hS U.1 U.2 _) ⊗ₜ[_,cubeAmbientRestrict t v a u' h ha hu' htv hau W] y) :
    ∃ p : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
      (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
      (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W),
      gluePr₁ t v a u' h hv T W p = x ∧ gluePr₂ t v a u' h hu' T W p = y :=
  glue_sections_exists t v a u' h ht hv ha hu' htv hau T W x y
    ((glueGamma_hom_one_tmul_eq_iff t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU x y).1
      hxy)

/-! ### The module statements of Stacks 07RW over a cube, for the glued module -/

section Cube

variable {B' B₀ A' A₀ : Type u} [CommRing B'] [CommRing B₀] [CommRing A'] [CommRing A₀]
    {bB : B' →+* B₀} {bA' : B' →+* A'} {tB : B₀ →+* A₀} {tA' : A' →+* A₀}
    {σ : B' →+* chartRing B S hS V'.1 V'.2 W}
    {σB : B₀ →+* chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W)}
    {σA' : A' →+* chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W)}
    {σA : A₀ →+* chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W)}
    (hcube : Stacks.Pushout.IsMilnorCube bB bA' tB tA' σ σB σA' σA
      (baseChangeChartRestrict B S hS v hv W) (baseChangeChartRestrict B S hS u' hu' W)
      (cubeTargetRestrict t v ht hv htv W) (cubeAmbientRestrict t v a u' h ha hu' htv hau W))

include hcube hG hF hWV hWU' hWU in
/-- **The unit of Stacks 07RW for the glued module of a triple over a cube**: a map into the
sections of the glued module over `W` out of a module flat over `B'`, which sends `m` to the pair
of its two base changes, is bijective. -/
theorem bijective_glue_of_isMilnorCube (N : ModuleCat.{u} (chartRing B S hS V'.1 V'.2 W))
    (hN : @Module.Flat B' N _ _ (Module.compHom N σ))
    (aff₁ : (ModuleCat.extendScalars (baseChangeChartRestrict B S hS v hv W)).obj N ≅
      ModuleCat.of _ (T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W))))
    (aff₂ : (ModuleCat.extendScalars (baseChangeChartRestrict B S hS u' hu' W)).obj N ≅
      ModuleCat.of _ (T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W))))
    (μ : N →ₗ[chartRing B S hS V'.1 V'.2 W] ((TripleGluing.glueFunctor
      (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W))
    (hμ₁ : ∀ m, gluePr₁ t v a u' h hv T W (μ m) = aff₁.hom ((1 : chartRing B S hS V.1 V.2
      ((smallBaseChange B S hS v hv).obj W))
        ⊗ₜ[chartRing B S hS V'.1 V'.2 W,baseChangeChartRestrict B S hS v hv W] m))
    (hμ₂ : ∀ m, gluePr₂ t v a u' h hu' T W (μ m) = aff₂.hom ((1 : chartRing B S hS U'.1 U'.2
      ((smallBaseChange B S hS u' hu').obj W))
        ⊗ₜ[chartRing B S hS V'.1 V'.2 W,baseChangeChartRestrict B S hS u' hu' W] m)) :
    Function.Bijective μ :=
  Stacks.Pushout.cube_unit_bijective hcube _ _
    (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (gluePr₁ t v a u' h hv T W) (gluePr₂ t v a u' h hu' T W)
    (gluePr₁_add t v a u' h hv W T) (gluePr₁_smul t v a u' h hv W T)
    (gluePr₂_add t v a u' h hu' W T) (gluePr₂_smul t v a u' h hu' W T)
    (glueGamma_one_tmul_gluePr t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (glue_sections_ext t v a u' h hv hu' T W)
    (glue_exists_of_glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    N hN aff₁ aff₂ μ hμ₁ hμ₂

include hcube hG hF hWV hWU' hWU in
/-- **The first component of the counit of Stacks 07RW for the glued module over a cube**: a map
out of the base change of the sections of the glued module to `W_V` into the sections of the
first component of the triple, sending `1 ⊗ p` to the first coordinate of `p`, is bijective. -/
theorem bijective_glue_counit_fst_of_isMilnorCube
    (Q : ModuleCat.{u} (chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W)))
    (aff : (ModuleCat.extendScalars (baseChangeChartRestrict B S hS v hv W)).obj
      (ModuleCat.of _ (((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W))) ≅ Q)
    (c : Q ⟶ ModuleCat.of _ (T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W))))
    (hc : ∀ p, c (aff.hom ((1 : chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W))
      ⊗ₜ[chartRing B S hS V'.1 V'.2 W,baseChangeChartRestrict B S hS v hv W] p)) =
        gluePr₁ t v a u' h hv T W p) :
    Function.Bijective c :=
  Stacks.Pushout.cube_counit_fst_bijective hcube _ _
    (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (gluePr₁ t v a u' h hv T W) (gluePr₂ t v a u' h hu' T W)
    (gluePr₁_add t v a u' h hv W T) (gluePr₁_smul t v a u' h hv W T)
    (gluePr₂_add t v a u' h hu' W T) (gluePr₂_smul t v a u' h hu' W T)
    (glueGamma_one_tmul_gluePr t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (glue_sections_ext t v a u' h hv hu' T W)
    (glue_exists_of_glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    Q aff c hc

include hcube hG hF hWV hWU' hWU in
/-- **The second component of the counit of Stacks 07RW for the glued module over a cube.** -/
theorem bijective_glue_counit_snd_of_isMilnorCube
    (Q : ModuleCat.{u} (chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W)))
    (aff : (ModuleCat.extendScalars (baseChangeChartRestrict B S hS u' hu' W)).obj
      (ModuleCat.of _ (((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W))) ≅ Q)
    (c : Q ⟶ ModuleCat.of _ (T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W))))
    (hc : ∀ p, c (aff.hom ((1 : chartRing B S hS U'.1 U'.2
      ((smallBaseChange B S hS u' hu').obj W))
        ⊗ₜ[chartRing B S hS V'.1 V'.2 W,baseChangeChartRestrict B S hS u' hu' W] p)) =
          gluePr₂ t v a u' h hu' T W p) :
    Function.Bijective c :=
  Stacks.Pushout.cube_counit_snd_bijective hcube _ _
    (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (gluePr₁ t v a u' h hv T W) (gluePr₂ t v a u' h hu' T W)
    (gluePr₁_add t v a u' h hv W T) (gluePr₁_smul t v a u' h hv W T)
    (gluePr₂_add t v a u' h hu' W T) (gluePr₂_smul t v a u' h hu' W T)
    (glueGamma_one_tmul_gluePr t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (glue_sections_ext t v a u' h hv hu' T W)
    (glue_exists_of_glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    Q aff c hc

include hcube hG hF hWV hWU' hWU in
/-- **The sections of the glued module of a triple of relatively flat modules over a cube are
flat over the base of the cube** (Stacks 07RW). -/
theorem flat_glue_of_isMilnorCube
    (hGflat : @Module.Flat B₀ (T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W))) _ _
      (Module.compHom _ σB))
    (hFflat : @Module.Flat A' (T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W))) _ _
      (Module.compHom _ σA')) :
    @Module.Flat B' (((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) _ _ (Module.compHom _ σ) :=
  Stacks.Pushout.cube_flat hcube _ _
    (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (gluePr₁ t v a u' h hv T W) (gluePr₂ t v a u' h hu' T W)
    (gluePr₁_add t v a u' h hv W T) (gluePr₁_smul t v a u' h hv W T)
    (gluePr₂_add t v a u' h hu' W T) (gluePr₂_smul t v a u' h hu' W T)
    (glueGamma_one_tmul_gluePr t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (glue_sections_ext t v a u' h hv hu' T W)
    (glue_exists_of_glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    hGflat hFflat

include hcube hG hF hWV hWU' hWU in
/-- **The sections of the glued module of a triple of modules with finite sections over a cube
are finite** (Stacks 08IH, through Stacks 07RW). -/
theorem finite_glue_of_isMilnorCube
    (hGfin : Module.Finite (chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W))
      (T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W))))
    (hFfin : Module.Finite (chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W))
      (T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W)))) :
    Module.Finite (chartRing B S hS V'.1 V'.2 W) (((TripleGluing.glueFunctor
      (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) :=
  have := hGfin
  have := hFfin
  Stacks.Pushout.cube_finite hcube _ _
    (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (gluePr₁ t v a u' h hv T W) (gluePr₂ t v a u' h hu' T W)
    (gluePr₁_add t v a u' h hv W T) (gluePr₁_smul t v a u' h hv W T)
    (gluePr₂_add t v a u' h hu' W T) (gluePr₂_smul t v a u' h hu' W T)
    (glueGamma_one_tmul_gluePr t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (glue_sections_ext t v a u' h hv hu' T W)
    (glue_exists_of_glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)

include hcube hG hF hWV hWU' hWU in
/-- **The sections of the glued module of a triple of relatively flat modules with finitely
presented sections over a cube whose ring map `B' ⟶ 𝒪(W)` is of finite presentation are finitely
presented** (Stacks 08KP, through Stacks 07RW). -/
theorem finitePresentation_glue_of_isMilnorCube
    (hGfp : Module.FinitePresentation
      (chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W))
      (T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W))))
    (hFfp : Module.FinitePresentation
      (chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W))
      (T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W))))
    (hGflat : @Module.Flat B₀ (T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W))) _ _
      (Module.compHom _ σB))
    (hFflat : @Module.Flat A' (T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W))) _ _
      (Module.compHom _ σA'))
    (hσ : σ.FinitePresentation) :
    Module.FinitePresentation (chartRing B S hS V'.1 V'.2 W)
      (((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) :=
  have := hGfp
  have := hFfp
  Stacks.Pushout.cube_finitePresentation hcube _ _
    (glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (gluePr₁ t v a u' h hv T W) (gluePr₂ t v a u' h hu' T W)
    (gluePr₁_add t v a u' h hv W T) (gluePr₁_smul t v a u' h hv W T)
    (gluePr₂_add t v a u' h hu' W T) (gluePr₂_smul t v a u' h hu' W T)
    (glueGamma_one_tmul_gluePr t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    (glue_sections_ext t v a u' h hv hu' T W)
    (glue_exists_of_glueGamma t v a u' h ht hv ha hu' htv hau W T hG hF hWV hWU' hWU)
    hGflat hFflat hσ

end Cube

/-! ### The unit and the counit of the gluing adjunction over a cube -/

section Adjunction

omit hG hF in
include hWV hWU' hWU in
/-- **The unit of the gluing adjunction is bijective over a chart carrying a Milnor cube**, for a
quasi-coherent module whose sections over the chart are flat over the base of the cube. -/
theorem bijective_squareUnit_app_of_isMilnorCube (M : Modules.{u, u} B S hS V'.1 V'.2)
    (hM : M.IsQuasicoherentOnSite) (hW : IsAffine (chartScheme W))
    {B' B₀ A' A₀ : Type u} [CommRing B'] [CommRing B₀] [CommRing A'] [CommRing A₀]
    {bB : B' →+* B₀} {bA' : B' →+* A'} {tB : B₀ →+* A₀} {tA' : A' →+* A₀}
    {σ : B' →+* chartRing B S hS V'.1 V'.2 W}
    {σB : B₀ →+* chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W)}
    {σA' : A' →+* chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W)}
    {σA : A₀ →+* chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W)}
    (hcube : Stacks.Pushout.IsMilnorCube bB bA' tB tA' σ σB σA' σA
      (baseChangeChartRestrict B S hS v hv W) (baseChangeChartRestrict B S hS u' hu' W)
      (cubeTargetRestrict t v ht hv htv W) (cubeAmbientRestrict t v a u' h ha hu' htv hau W))
    (hflat : @Module.Flat B' (M.val.obj (op W)) _ _ (Module.compHom _ σ)) :
    Function.Bijective (((TripleGluing.adjunction (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v)
        (compTransport_eq_rightComparison t v a u' h)).unit.app M).val.app (op W)) := by
  have hb₁ : let := chartDiagramAlgebra B S hS v (baseChangeChartDiagram B S hS v hv W)
      Function.Bijective (modulePullbackChartBaseChange B S hS v M
        (baseChangeChartDiagram B S hS v hv W)) :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS v M hM _ hWV hW
  have hb₂ : let := chartDiagramAlgebra B S hS u' (baseChangeChartDiagram B S hS u' hu' W)
      Function.Bijective (modulePullbackChartBaseChange B S hS u' M
        (baseChangeChartDiagram B S hS u' hu' W)) :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS u' M hM _ hWU' hW
  refine bijective_glue_of_isMilnorCube t v a u' h ht hv ha hu' htv hau W
    ((TripleGluing.restrictFunctor (squareOverlap t v a u' h)).obj M)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS v M hM)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS u' M hM)
    hWV hWU' hWU hcube (ModuleCat.of _ (M.val.obj (op W))) hflat
    (baseChangeChartIso B S hS v hv M W hb₁)
    (baseChangeChartIso B S hS u' hu' M W hb₂)
    (((TripleGluing.adjunction (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v)
        (compTransport_eq_rightComparison t v a u' h)).unit.app M).val.app (op W)).hom (fun m => ?_)
          (fun m => ?_)
  · have e := sheafOfModules_comp_eq_apply
      ((TripleGluing.adjunction_unit_app_fst (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v) (compTransport_eq_rightComparison t v a u' h) M).trans
        (Category.comp_id _).symm) (op W) m
    have e2 := chartModProj_modulePullbackAdjunction_unit B S hS v hv M W m
    have e3 := baseChangeChartIso_hom_one_tmul B S hS v hv M W hb₁ m
    exact ((congrArg (chartModProj B S hS v hv ((modulePullback B S hS v).obj M) W) e).trans
      e2).trans e3.symm
  · have e := sheafOfModules_comp_eq_apply
      ((TripleGluing.adjunction_unit_app_snd (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v) (compTransport_eq_rightComparison t v a u' h) M).trans
        (Category.comp_id _).symm) (op W) m
    have e2 := chartModProj_modulePullbackAdjunction_unit B S hS u' hu' M W m
    have e3 := baseChangeChartIso_hom_one_tmul B S hS u' hu' M W hb₂ m
    exact ((congrArg (chartModProj B S hS u' hu' ((modulePullback B S hS u').obj M) W) e).trans
      e2).trans e3.symm

include hG hF hWV hWU' hWU in
/-- **The first component of the counit of the gluing adjunction is bijective over `W_V`** when
`W` carries a Milnor cube and the glued module is quasi-coherent. -/
theorem bijective_squareCounit_target_app_of_isMilnorCube
    (hglue : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).IsQuasicoherentOnSite) (hW : IsAffine (chartScheme W))
    {B' B₀ A' A₀ : Type u} [CommRing B'] [CommRing B₀] [CommRing A'] [CommRing A₀]
    {bB : B' →+* B₀} {bA' : B' →+* A'} {tB : B₀ →+* A₀} {tA' : A' →+* A₀}
    {σ : B' →+* chartRing B S hS V'.1 V'.2 W}
    {σB : B₀ →+* chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W)}
    {σA' : A' →+* chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W)}
    {σA : A₀ →+* chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W)}
    (hcube : Stacks.Pushout.IsMilnorCube bB bA' tB tA' σ σB σA' σA
      (baseChangeChartRestrict B S hS v hv W) (baseChangeChartRestrict B S hS u' hu' W)
      (cubeTargetRestrict t v ht hv htv W) (cubeAmbientRestrict t v a u' h ha hu' htv hau W)) :
    Function.Bijective ((((TripleGluing.adjunction (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v)
        (compTransport_eq_rightComparison t v a u' h)).counit.app T).target).val.app
      (op ((smallBaseChange B S hS v hv).obj W))) := by
  have hb : let := chartDiagramAlgebra B S hS v (baseChangeChartDiagram B S hS v hv W)
      Function.Bijective (modulePullbackChartBaseChange B S hS v ((TripleGluing.glueFunctor
        (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T)
        (baseChangeChartDiagram B S hS v hv W)) :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS v _ hglue _ hWV hW
  refine bijective_glue_counit_fst_of_isMilnorCube t v a u' h ht hv ha hu' htv hau W T hG hF
    hWV hWU' hWU hcube _
    (baseChangeChartIso B S hS v hv ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T) W hb)
    (ModuleCat.ofHom ((((TripleGluing.adjunction (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v)
        (compTransport_eq_rightComparison t v a u' h)).counit.app T).target).val.app
      (op ((smallBaseChange B S hS v hv).obj W))).hom) (fun p => ?_)
  have e := congrArg (fun m' => m'.val.app _
      (modulePullbackChartSection B S hS v ((TripleGluing.glueFunctor
        (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T) (baseChangeChartDiagram B S hS v hv W) p))
    (TripleGluing.adjunction_counit_app_target (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v) (compTransport_eq_rightComparison t v a u' h) T)
  refine (congrArg (ModuleCat.ofHom ((((TripleGluing.adjunction (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v)
        (compTransport_eq_rightComparison t v a u' h)).counit.app T).target).val.app
      (op ((smallBaseChange B S hS v hv).obj W))).hom)
      (baseChangeChartIso_hom_one_tmul B S hS v hv ((TripleGluing.glueFunctor
        (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T) W hb p)).trans ?_
  refine e.trans ?_
  refine (congrArg (((modulePullbackAdjunction B S hS v).counit.app T.target).val.app _)
    (modulePullbackChartSection_map B S hS v _ (TripleGluing.glueFst
      (qV := modulePushforward B S hS v)
        (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
        (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
        (compTransport a u' (t ≫ v) h) T) (baseChangeChartDiagram B S hS v hv W) p)).trans
    ?_
  exact modulePullbackAdjunction_counit_chartSection B S hS v hv T.target W _

include hG hF hWV hWU' hWU in
/-- **The second component of the counit of the gluing adjunction is bijective over `W_{U'}`**
when `W` carries a Milnor cube and the glued module is quasi-coherent. -/
theorem bijective_squareCounit_ambient_app_of_isMilnorCube
    (hglue : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).IsQuasicoherentOnSite) (hW : IsAffine (chartScheme W))
    {B' B₀ A' A₀ : Type u} [CommRing B'] [CommRing B₀] [CommRing A'] [CommRing A₀]
    {bB : B' →+* B₀} {bA' : B' →+* A'} {tB : B₀ →+* A₀} {tA' : A' →+* A₀}
    {σ : B' →+* chartRing B S hS V'.1 V'.2 W}
    {σB : B₀ →+* chartRing B S hS V.1 V.2 ((smallBaseChange B S hS v hv).obj W)}
    {σA' : A' →+* chartRing B S hS U'.1 U'.2 ((smallBaseChange B S hS u' hu').obj W)}
    {σA : A₀ →+* chartRing B S hS U.1 U.2 ((smallBaseChange B S hS (t ≫ v) htv).obj W)}
    (hcube : Stacks.Pushout.IsMilnorCube bB bA' tB tA' σ σB σA' σA
      (baseChangeChartRestrict B S hS v hv W) (baseChangeChartRestrict B S hS u' hu' W)
      (cubeTargetRestrict t v ht hv htv W) (cubeAmbientRestrict t v a u' h ha hu' htv hau W)) :
    Function.Bijective ((((TripleGluing.adjunction (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v)
        (compTransport_eq_rightComparison t v a u' h)).counit.app T).ambient).val.app
      (op ((smallBaseChange B S hS u' hu').obj W))) := by
  have hb : let := chartDiagramAlgebra B S hS u' (baseChangeChartDiagram B S hS u' hu' W)
      Function.Bijective (modulePullbackChartBaseChange B S hS u' ((TripleGluing.glueFunctor
        (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T)
        (baseChangeChartDiagram B S hS u' hu' W)) :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS u' _ hglue _ hWU' hW
  refine bijective_glue_counit_snd_of_isMilnorCube t v a u' h ht hv ha hu' htv hau W T hG hF
    hWV hWU' hWU hcube _
    (baseChangeChartIso B S hS u' hu' ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T) W hb)
    (ModuleCat.ofHom ((((TripleGluing.adjunction (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v)
        (compTransport_eq_rightComparison t v a u' h)).counit.app T).ambient).val.app
      (op ((smallBaseChange B S hS u' hu').obj W))).hom) (fun p => ?_)
  have e := congrArg (fun m' => m'.val.app _
      (modulePullbackChartSection B S hS u' ((TripleGluing.glueFunctor
        (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T) (baseChangeChartDiagram B S hS u' hu' W)
        p))
    (TripleGluing.adjunction_counit_app_ambient (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v) (compTransport_eq_rightComparison t v a u' h) T)
  refine (congrArg (ModuleCat.ofHom ((((TripleGluing.adjunction (modulePullbackAdjunction B S hS v)
      (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)
      (modulePushforwardCompIso B S hS t v)
        (compTransport_eq_rightComparison t v a u' h)).counit.app T).ambient).val.app
      (op ((smallBaseChange B S hS u' hu').obj W))).hom)
      (baseChangeChartIso_hom_one_tmul B S hS u' hu' ((TripleGluing.glueFunctor
        (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T) W hb p)).trans ?_
  refine e.trans ?_
  refine (congrArg (((modulePullbackAdjunction B S hS u').counit.app T.ambient).val.app _)
    (modulePullbackChartSection_map B S hS u' _ (TripleGluing.glueSnd
      (qV := modulePushforward B S hS v)
        (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
        (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
        (compTransport a u' (t ≫ v) h) T) (baseChangeChartDiagram B S hS u' hu' W)
      p)).trans ?_
  exact modulePullbackAdjunction_counit_chartSection B S hS u' hu' T.ambient W _

end Adjunction

/-! ### Quasi-coherence of the glued module -/

omit hWV hWU' hWU in
include hG hF in
/-- **The glued module of a triple of quasi-coherent modules is quasi-coherent**, for affine
`v`, `u'` and `U ⟶ V'`: it is a fibre product of direct images of quasi-coherent modules along
affine morphisms (Stacks 03M1 and Stacks 01BF). -/
theorem isQuasicoherentOnSite_glue (hvaff : IsAffineHom B S hS v.hom)
    (hu'aff : IsAffineHom B S hS u'.hom) (htvaff : IsAffineHom B S hS (t ≫ v).hom) :
    ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isPullback B S hS V'.1 V'.2
    (TripleGluing.isPullback_glue (qV := modulePushforward B S hS v)
      (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
      (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
      (compTransport a u' (t ≫ v) h) T)
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom' v
      hvaff hG)
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom' u'
      hu'aff hF)
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom'
      (t ≫ v) htvaff
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a T.ambient hF))

/-! ### The composite restrictions to `W_U` -/

section Restrict

/-- The ring maps on global sections induced by `k₁` and `k₂` compose to the one induced by
`k₁ ≫ k₂`. -/
theorem appTop_hom_comp {A₁ A₂ A₃ : BigFppfOver B S hS} (k₁ : A₁ ⟶ A₂) (k₂ : A₂ ⟶ A₃) :
    ((BigFppfOver.toScheme B S hS).map k₁).appTop.hom.comp
        ((BigFppfOver.toScheme B S hS).map k₂).appTop.hom =
      ((BigFppfOver.toScheme B S hS).map (k₁ ≫ k₂)).appTop.hom := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]

/-- The base change of a chart along equal morphisms, followed by the cartesian projection. -/
theorem toOver_map_eqToHom_smallBaseChange_snd {k k' : U ⟶ V'} (e : k = k')
    (hk : yoneda.relativelyRepresentable k.hom) (hk' : yoneda.relativelyRepresentable k'.hom) :
    (SmallEtale.toOver B S hS U.1).map (eqToHom (smallBaseChange_obj_congr e hk hk' W)) ≫
        hk'.snd W.1.hom = hk.snd W.1.hom := by
  subst e
  obtain rfl : hk = hk' := rfl
  rw [eqToHom_refl]
  exact (congrArg (· ≫ hk.snd W.1.hom) ((SmallEtale.toOver B S hS U.1).map_id _)).trans
    (Category.id_comp _)

/-- The chart projection of `W_U` to `W` through `W_V`. -/
theorem targetDiagram_g_comp :
    (targetDiagram t v ht hv htv W).g ≫ hv.snd W.1.hom = htv.snd W.1.hom := by
  change ((SmallEtale.toOver B S hS U.1).map
      (chartBaseChangeCompComparison B S hS t v ht hv htv W) ≫
      ht.snd ((smallBaseChange B S hS v hv).obj W).1.hom) ≫ hv.snd W.1.hom = htv.snd W.1.hom
  exact (Category.assoc _ _ _).trans
    (toOver_map_chartBaseChangeCompComparison_comp_snd B S hS t v ht hv htv W)

/-- The chart projection of `W_U` to `W` through `W_{U'}`. -/
theorem ambientDiagram_g_comp :
    (ambientDiagram t v a u' h ha hu' htv hau W).g ≫ hu'.snd W.1.hom = htv.snd W.1.hom := by
  change ((SmallEtale.toOver B S hS U.1).map
      (eqToHom (smallBaseChange_obj_congr h.symm htv hau W) ≫
        chartBaseChangeCompComparison B S hS a u' ha hu' hau W) ≫
      ha.snd ((smallBaseChange B S hS u' hu').obj W).1.hom) ≫ hu'.snd W.1.hom = htv.snd W.1.hom
  have e1 := toOver_map_chartBaseChangeCompComparison_comp_snd B S hS a u' ha hu' hau W
  have e2 := toOver_map_eqToHom_smallBaseChange_snd W h.symm htv hau
  exact (Category.assoc _ _ _).trans ((congrArg (· ≫ (ha.snd ((smallBaseChange B S hS u' hu').obj
    W).1.hom ≫ hu'.snd W.1.hom)) ((SmallEtale.toOver B S hS U.1).map_comp _ _)).trans
    ((Category.assoc _ _ _).trans ((congrArg _ e1).trans e2)))

/-- The restriction from `W` to `W_U` through `W_V` is the restriction along the base change. -/
theorem cubeTargetRestrict_comp :
    (cubeTargetRestrict t v ht hv htv W).comp (baseChangeChartRestrict B S hS v hv W) =
      baseChangeChartRestrict B S hS (t ≫ v) htv W := by
  change ((BigFppfOver.toScheme B S hS).map (targetDiagram t v ht hv htv W).g).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map (hv.snd W.1.hom)).appTop.hom =
    ((BigFppfOver.toScheme B S hS).map (htv.snd W.1.hom)).appTop.hom
  exact (appTop_hom_comp _ _).trans (congrArg (fun k => ((BigFppfOver.toScheme B S hS).map
    k).appTop.hom) (targetDiagram_g_comp t v ht hv htv W))

/-- The restriction from `W` to `W_U` through `W_{U'}` is the restriction along the base
change. -/
theorem cubeAmbientRestrict_comp :
    (cubeAmbientRestrict t v a u' h ha hu' htv hau W).comp
        (baseChangeChartRestrict B S hS u' hu' W) =
      baseChangeChartRestrict B S hS (t ≫ v) htv W := by
  change ((BigFppfOver.toScheme B S hS).map
      (ambientDiagram t v a u' h ha hu' htv hau W).g).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map (hu'.snd W.1.hom)).appTop.hom =
    ((BigFppfOver.toScheme B S hS).map (htv.snd W.1.hom)).appTop.hom
  exact (appTop_hom_comp _ _).trans (congrArg (fun k => ((BigFppfOver.toScheme B S hS).map
    k).appTop.hom) (ambientDiagram_g_comp t v a u' h ha hu' htv hau W))

end Restrict

end AlgebraicGeometry.Space.PushoutModules

end
