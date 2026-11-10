module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurj
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackPointSections

/-!
# The module of sections along points is cartesian

The presheaf of modules `(T, a) ↦ Γ(T, a^*𝒢)` on the affine points of the pointwise quotient
`[U/_pR]` of a groupoid in algebraic spaces, attached to a quasi-coherent module `(𝒢, α)` on the
groupoid (`AlgebraicGeometry.Stack.pointModuleSheaf`), has all its base change maps
`Γ(T, a^*𝒢) ⊗_{Γ(T)} Γ(T') ⟶ Γ(T', a'^*𝒢)` isomorphisms: this is condition (1) of Stacks 0H0E,
which makes it the restriction of a quasi-coherent module on `[U/_pR]`, as the proof of
Stacks 06WT requires. The restriction map along `(h, r)` is the chart section along `h`, which is
a base change by Stacks 083K since `a^*𝒢` is quasi-coherent and the charts are affine, followed by
the transition along `r`, which is an isomorphism because `α` is (Stacks 077W).

## Main results

* `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_pointPresheaf`: the base change maps are
  isomorphisms.
* `AlgebraicGeometry.Stack.isIso_canonicalMap_pointModuleSheaf`: the same, in the form of
  condition (1) of `AlgebraicGeometry.Stack.AffineCategory.tfae_isQuasicoherent`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe u

/-- A function out of a base change computed on pure tensors by `ρ` is `ρ.liftBaseChange`. -/
theorem Stacks.liftBaseChange_apply_eq_of_tmul {R S N N' : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module S N'] [Module R N']
    [IsScalarTower R S N'] (ρ : N →ₗ[R] N') (e : TensorProduct R S N → N')
    (hadd : ∀ z w, e (z + w) = e z + e w)
    (htmul : ∀ (b : S) (m : N), e (TensorProduct.tmul R b m) = b • ρ m) (z : TensorProduct R S N) :
    ρ.liftBaseChange S z = e z := by
  induction z using TensorProduct.inductionOn with
  | tmul b m => rw [LinearMap.liftBaseChange_tmul, htmul]
  | add z w hz hw => rw [map_add, hz, hw, hadd]

/-- **A morphism out of an extension of scalars is bijective when the base change comparison of
its restriction is.** -/
theorem Stacks.bijective_of_bijective_liftBaseChange_extendScalars {A Rv N N' : Type u}
    [CommRing A] [CommRing Rv] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module Rv N']
    (φ : A →+* Rv) (e : (ModuleCat.extendScalars φ).obj (ModuleCat.of A N) ⟶ ModuleCat.of Rv N') :
    letI := φ.toAlgebra
    letI := Module.compHom N' φ
    haveI : IsScalarTower A Rv N' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    ∀ ρ : N →ₗ[A] N', (∀ m : N, e ((1 : Rv) ⊗ₜ[A,φ] m) = ρ m) →
      Function.Bijective (ρ.liftBaseChange Rv) → Function.Bijective e := by
  let _ := φ.toAlgebra
  let _ := Module.compHom N' φ
  have _ : IsScalarTower A Rv N' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  intro ρ hρ hbij
  have key := Stacks.liftBaseChange_apply_eq_of_tmul ρ (fun z : TensorProduct A Rv N => e z)
    (fun z w => map_add _ z w) (fun b m => by
      have hb : TensorProduct.tmul A b m = b • TensorProduct.tmul A (1 : Rv) m := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hms : (ConcreteCategory.hom e) (b • TensorProduct.tmul A (1 : Rv) m) =
          b • (ConcreteCategory.hom e) (TensorProduct.tmul A (1 : Rv) m) :=
        map_smul (ConcreteCategory.hom e) b _
      rw [hb, hms]
      exact congrArg (b • ·) (hρ m))
  have hfun : (ρ.liftBaseChange Rv : TensorProduct A Rv N → N') =
      (fun z : TensorProduct A Rv N => e z) := funext key
  exact (hfun ▸ hbij : Function.Bijective fun z : TensorProduct A Rv N => e z)

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- The restriction along a chart diagram as a linear map over the target chart. -/
def chartRestrictLinear {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Space.Modules.{u, u} C S hS Y.1 Y.2) (P : Space.Modules.{u, u} C S hS X.1 X.2)
    (φ : (Space.modulePullback C S hS f).obj N ⟶ P) (d : Space.ChartDiagram C S hS X.1 Y.1 f.hom) :
    letI := Module.compHom (P.val.obj (op d.U)) (Space.chartDiagramRestrict C S hS f d)
    N.val.obj (op d.V) →ₗ[Space.chartRing C S hS Y.1 Y.2 d.V] P.val.obj (op d.U) :=
  letI := Module.compHom (P.val.obj (op d.U)) (Space.chartDiagramRestrict C S hS f d)
  { toFun := chartRestrict f N P φ d
    map_add' := chartRestrict_add f N P φ d
    map_smul' := chartRestrict_smul f N P φ d }

/-- The linear map `chartRestrictLinear f N P φ d` evaluates to `chartRestrict f N P φ d`. -/
theorem chartRestrictLinear_apply {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Space.Modules.{u, u} C S hS Y.1 Y.2) (P : Space.Modules.{u, u} C S hS X.1 X.2)
    (φ : (Space.modulePullback C S hS f).obj N ⟶ P) (d : Space.ChartDiagram C S hS X.1 Y.1 f.hom)
    (m : N.val.obj (op d.V)) : chartRestrictLinear f N P φ d m = chartRestrict f N P φ d m :=
  rfl

/-- **The restriction through an isomorphism along a diagram of affine charts is a base change
of the sections of a quasi-coherent module.** -/
theorem bijective_liftBaseChange_chartRestrictLinear {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Space.Modules.{u, u} C S hS Y.1 Y.2) (P : Space.Modules.{u, u} C S hS X.1 X.2)
    (φ : (Space.modulePullback C S hS f).obj N ⟶ P) (hφ : IsIso φ)
    (d : Space.ChartDiagram C S hS X.1 Y.1 f.hom) (hN : N.IsQuasicoherentOnSite)
    (haU : IsAffine ((Space.SmallEtale.toOver C S hS X.1 ⋙ BigFppfOver.toScheme C S hS).obj d.U))
    (haV : IsAffine ((Space.SmallEtale.toOver C S hS Y.1 ⋙ BigFppfOver.toScheme C S hS).obj d.V)) :
    letI := Space.chartDiagramAlgebra C S hS f d
    letI := Module.compHom (P.val.obj (op d.U)) (Space.chartDiagramRestrict C S hS f d)
    haveI : IsScalarTower (Space.chartRing C S hS Y.1 Y.2 d.V) (Space.chartRing C S hS X.1 X.2 d.U)
        (P.val.obj (op d.U)) := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    Function.Bijective ((chartRestrictLinear f N P φ d).liftBaseChange
      (Space.chartRing C S hS X.1 X.2 d.U)) := by
  let := Space.chartDiagramAlgebra C S hS f d
  let := Module.compHom (P.val.obj (op d.U)) (Space.chartDiagramRestrict C S hS f d)
  have : IsScalarTower (Space.chartRing C S hS Y.1 Y.2 d.V) (Space.chartRing C S hS X.1 X.2 d.U)
      (P.val.obj (op d.U)) := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hb := Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite C S hS f N hN
    d haU haV
  have hφb := SheafOfModules.bijective_val_app_of_isIso φ hφ (op d.U)
  refine Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_liftBaseChange_of_bijective
    (chartRestrictLinear f N P φ d)
    (fun z => φ.val.app (op d.U) (Space.modulePullbackChartBaseChange C S hS f N d z))
    (fun z w => by rw [map_add, map_add]) (fun b m => ?_) (hφb.comp hb)
  change φ.val.app (op d.U) (Space.modulePullbackChartBaseChange C S hS f N d
    (TensorProduct.tmul _ b m)) = b • chartRestrict f N P φ d m
  rw [Space.modulePullbackChartBaseChange_tmul, map_smul]
  rfl

variable {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

/-- The presheaf `pointPresheaf` over the commutative structure presheaf of the affine points. -/
def pointCommPresheaf : PresheafOfModules.{u} (((AffineCategory.toScheme C S hS
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p).op ⋙ Scheme.Γ) ⋙
      forget₂ CommRingCat RingCat) :=
  pointPresheaf G M

/-- **The module `(T, a) ↦ Γ(T, a^*𝒢)` is cartesian**: all its base change maps
`Γ(T, a^*𝒢) ⊗_{Γ(T)} Γ(T') ⟶ Γ(T', a'^*𝒢)` are isomorphisms. -/
theorem isIso_restrictionBaseChange_pointPresheaf {x y : (AffineCategory C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)ᵒᵖ}
    (f : x ⟶ y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (AffineCategory.toScheme C S hS (presheafOfGroupoids
        (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p).op ⋙ Scheme.Γ)
      (pointCommPresheaf G M) f) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  have hN := Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite C S hS
    (pointMap G x.unop.obj) M.F.obj M.F.property
  have hiso : IsIso (pointwiseTransition G M f.unop.hom) :=
    Space.isIso_pointTransition M (baseMap f.unop.hom.base) (pointMap G x.unop.obj)
      (arrowMap G f.unop.hom) (arrowMap_source G f.unop.hom) (arrowMap_target G f.unop.hom)
  have hb := bijective_liftBaseChange_chartRestrictLinear (baseMap f.unop.hom.base)
    ((Space.modulePullback C S hS (pointMap G x.unop.obj)).obj M.F.obj)
    ((Space.modulePullback C S hS (pointMap G y.unop.obj)).obj M.F.obj)
    (pointwiseTransition G M f.unop.hom) hiso (Space.selfChartDiagram C S hS f.unop.hom.base) hN
    y.unop.property x.unop.property
  refine Stacks.bijective_of_bijective_liftBaseChange_extendScalars
    (A := ((AffineCategory.toScheme C S hS (presheafOfGroupoids
        (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p).op ⋙ Scheme.Γ).obj x)
    (Rv := ((AffineCategory.toScheme C S hS (presheafOfGroupoids
        (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p).op ⋙ Scheme.Γ).obj y)
    (N := (pointCommPresheaf G M).obj x) (N' := (pointCommPresheaf G M).obj y) _ _
    (chartRestrictLinear (baseMap f.unop.hom.base)
      ((Space.modulePullback C S hS (pointMap G x.unop.obj)).obj M.F.obj)
      ((Space.modulePullback C S hS (pointMap G y.unop.obj)).obj M.F.obj)
      (pointwiseTransition G M f.unop.hom) (Space.selfChartDiagram C S hS f.unop.hom.base))
    (fun m => ?_) hb
  refine (Stacks.PresheafOfModules.restrictionBaseChange_one_tmul
    (pointCommPresheaf G M) f m).trans ?_
  refine (Stacks.PresheafOfModules.mkOfSemilinear_map_apply (fun x => pointModule G M x.unop)
    (fun f => affinePointSemilinear G M f) (affinePointSemilinear_id G M)
    (fun f g s => affinePointSemilinear_comp G M f g s) f m).trans ?_
  refine (affinePointSemilinear_apply G M f m).trans ?_
  exact (chartRestrictLinear_apply (baseMap f.unop.hom.base)
      ((Space.modulePullback C S hS (pointMap G x.unop.obj)).obj M.F.obj)
      ((Space.modulePullback C S hS (pointMap G y.unop.obj)).obj M.F.obj)
      (pointwiseTransition G M f.unop.hom) (Space.selfChartDiagram C S hS f.unop.hom.base) m).symm

/-- **Condition (1) of Stacks 0H0E for `(T, a) ↦ Γ(T, a^*𝒢)`.** -/
theorem isIso_canonicalMap_pointModuleSheaf {x x' : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p} (f : x ⟶ x') :
    IsIso (Stacks.SheafOfModules.canonicalMap (AffineCategory.siteKindRingedSite C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (isFiberedInGroupoids_presheafOfGroupoids _) .fppf).chaotic (pointModuleSheaf G M) f) :=
  isIso_restrictionBaseChange_pointPresheaf G M f.op

end AlgebraicGeometry.Stack

end
