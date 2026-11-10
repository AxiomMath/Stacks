module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesChartDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem

/-!
# The prescribed module of the extension problem at a chart is `𝒪_X ⊗_A I`

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart, and let
`Spec A ⊂ Spec A'` be a square-zero closed immersion with ideal `I`, an `A`-module. The extension
problem of [Stacks, Section 08V3] attached to `X → Spec A ⊂ Spec A'`
(`AlgebraicGeometry.Space.FlatThickeningDeformation.problem`) has prescribed module
`f^*𝒞_{Spec A/Spec A'}`, the conormal module pulled back along `f : X → Spec A`. This file
identifies it with `𝒪_X ⊗_A I` ([Stacks, Tag 0D3F]), on the small étale site of `X` and on its
`Type u` model, where it is the module `AlgebraicGeometry.Space.modelTensorFunctor` of the
base-ring datum `chartBaseRingHom x hx`, whose `Ext` groups are the functors `T¹`, `T²` of
Remark 0D1P.

The conormal module of `Spec A ⊂ Spec A'` is `𝒪_{Spec A} ⊗_{Γ(Spec A')} I`
(`AlgebraicGeometry.Space.conormalModuleRangeIso`), `𝒪 ⊗ −` commutes with pullback
(`AlgebraicGeometry.Space.baseRingTensorModulePullbackCompIso`), and `I`, a module over
`Γ(Spec A')` through the surjection `Γ(Spec A') → A`, is a module over `A`
(`AlgebraicGeometry.Space.baseRingTensorModuleRestrictScalarsIso`).

## Main definitions

* `AlgebraicGeometry.Space.ProperFlatLift.chartPulledBackConormalIso`: `f^*𝒞 ≅ 𝒪_X ⊗_A N` on the
  small étale site, for an `A`-module `N` identified with `I`.
* `AlgebraicGeometry.Space.ProperFlatLift.chartModelConormalIso`: the same on the model.
* `AlgebraicGeometry.Space.ProperFlatLift.thickeningModelConormalIso`: for a square-zero
  thickening `D` of Situation 07YX, `f^*𝒞 ≅ 𝒪_X ⊗_A D.kernel` on the model.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  {T' : BigFppfOver B S hS} (i : algebraOver A B S hS toS hA ⟶ T')
  (hi : IsSquareZeroClosedImmersion B S hS i)

/-- The special map of `x` along `i` is its structure morphism followed by the identification of
`Spec A` with the closed subspace `Spec A ⊆ T'`. -/
theorem specialMap_eq_chartStructureMap_comp :
    specialMap i hi x hx = chartStructureMap x hx ≫ (rangeSpaceIso B S hS i hi.1).hom :=
  (Category.assoc _ _ _).symm

/-- Pullback of functions along `i : Spec A ⟶ T'`, read through `Γ(Spec A) ≅ A`: the ring map
`Γ(T', 𝒪_{T'}) → A`. -/
def chartThickeningRingHom : baseRing B S hS T' →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map i).op).hom

include hi in
/-- `Γ(T', 𝒪_{T'}) → A` is surjective for affine `T'`, `i` being a closed immersion. -/
theorem surjective_chartThickeningRingHom
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) :
    Function.Surjective (chartThickeningRingHom i) := by
  have := hi.1
  have := hT'
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).2.comp
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((BigFppfOver.toScheme B S hS).map i)).2

/-- The base-ring datum of `X → Spec A → T'` is `chartBaseRingHom x hx` precomposed with
`Γ(T', 𝒪_{T'}) → A`. -/
theorem baseRingHomOfMap_chartStructureMap_comp :
    baseRingHomOfMap (chartStructureMap x hx ≫ schemeSpaceMap i) =
      (chartBaseRingHom x hx).comp (chartThickeningRingHom i) := by
  refine (baseRingHomOfMap_comp B S hS (chartStructureMap x hx) i).trans ?_
  refine RingHom.ext fun r => congrArg (baseRingHomOfMap (chartStructureMap x hx))
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map i).op).hom r)).symm

/-- The first half of `chartPulledBackConormalIso`: `f^*𝒞 ≅ 𝒪_X ⊗_{Γ(T')} I`, the base ring acting
through `X → Spec A → T'`. -/
def chartPulledBackConormalIdealIso (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) :
    FlatThickeningDeformation.pulledBackConormal (Z := baseSubspace i hi) (specialMap i hi x hx) ≅
      (baseRingTensorModule B S hS x.obj.obj.left
          (baseRingHomOfMap (chartStructureMap x hx ≫ schemeSpaceMap i))).obj
        (ModuleCat.of (baseRing B S hS T')
          (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS i hi.1))) :=
  ((modulePullbackCompIsoOfEq B S hS (chartStructureMap x hx)
      (rangeSpaceIso B S hS i hi.1).hom (specialMap_eq_chartStructureMap_comp x hx i hi).symm).app
        (conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS i hi.1))).symm ≪≫
    (modulePullback B S hS (chartStructureMap x hx)).mapIso
      (conormalModuleRangeIso B S hS i hi.1 hT') ≪≫
    (baseRingTensorModulePullbackCompIso B S hS (chartStructureMap x hx) (schemeSpaceMap i)).app _

/-- **The prescribed module `f^*𝒞_{Spec A/T'}` of the extension problem of `x` along `i` is
`𝒪_X ⊗_A N`**, on the small étale site of `X`, for an `A`-module `N` whose restriction to
`Γ(T', 𝒪_{T'})` is the ideal `I` of `Spec A ⊆ T'`. -/
def chartPulledBackConormalIso (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (N : ModuleCat.{u} A)
    (e : (ModuleCat.restrictScalars.{u} (chartThickeningRingHom i)).obj N ≅
      ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS i hi.1))) :
    FlatThickeningDeformation.pulledBackConormal (Z := baseSubspace i hi) (specialMap i hi x hx) ≅
      (baseRingTensorModule B S hS x.obj.obj.left (chartBaseRingHom x hx)).obj N :=
  chartPulledBackConormalIdealIso x hx i hi hT' ≪≫
    (baseRingTensorModule B S hS x.obj.obj.left _).mapIso e.symm ≪≫
    eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS x.obj.obj.left φ).obj
      ((ModuleCat.restrictScalars.{u} (chartThickeningRingHom i)).obj N))
      (baseRingHomOfMap_chartStructureMap_comp x hx i)) ≪≫
    (baseRingTensorModuleRestrictScalarsIso B S hS _ _ _
      (surjective_chartThickeningRingHom i hi hT')).app N

section Counit

variable (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
  (φ : R →+* modelGlobalFunctions B S hS X)

/-- **The counit of the Comparison Lemma at `𝒪_X ⊗_R M`**: the restriction to the model of the
base-ring tensor module of `X` is the base-ring tensor module of the model. -/
def modelBaseRingTensorCounitIso (M : ModuleCat.{u} R) :
    (Deformation.AlgebraExtension.moduleRes (smallEtaleModelTopology B S hS X.1)
        (smallEtaleModelEquiv B S hS X).inverse (smallEtaleRingedTopos B S hS X).O).obj
        ((baseRingTensorModule B S hS X φ).obj M) ≅
      (modelTensorFunctor φ).obj M :=
  (smallEtaleModelModulesEquiv B S hS X).counitIso.app _

end Counit

/-- `chartPulledBackConormalIso` restricted to the `Type u` model of the small étale site. -/
def chartModelPulledBackConormalIso (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (N : ModuleCat.{u} A)
    (e : (ModuleCat.restrictScalars.{u} (chartThickeningRingHom i)).obj N ≅
      ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS i hi.1))) :
    (Deformation.AlgebraExtension.moduleRes (smallEtaleModelTopology B S hS x.obj.obj.left.1)
        (smallEtaleModelEquiv B S hS x.obj.obj.left).inverse
        (smallEtaleRingedTopos B S hS x.obj.obj.left).O).obj
        (FlatThickeningDeformation.pulledBackConormal (Z := baseSubspace i hi)
          (specialMap i hi x hx)) ≅
      (Deformation.AlgebraExtension.moduleRes (smallEtaleModelTopology B S hS x.obj.obj.left.1)
        (smallEtaleModelEquiv B S hS x.obj.obj.left).inverse
        (smallEtaleRingedTopos B S hS x.obj.obj.left).O).obj
        ((baseRingTensorModule B S hS x.obj.obj.left (chartBaseRingHom x hx)).obj N) :=
  (Deformation.AlgebraExtension.moduleRes (smallEtaleModelTopology B S hS x.obj.obj.left.1)
        (smallEtaleModelEquiv B S hS x.obj.obj.left).inverse
        (smallEtaleRingedTopos B S hS x.obj.obj.left).O).mapIso
      (chartPulledBackConormalIso x hx i hi hT' N e)

/-- **The prescribed module of the extension problem of `x` along `i` is `𝒪_X ⊗_A N` on the
model**: `chartPulledBackConormalIso` restricted to the `Type u` model of the small étale site
(`chartModelPulledBackConormalIso`), followed by the counit of the Comparison Lemma
(`modelBaseRingTensorCounitIso`), where `𝒪_X ⊗_A N` is
`modelTensorFunctor (chartBaseRingHom x hx)`. -/
def chartModelConormalIso (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (N : ModuleCat.{u} A)
    (e : (ModuleCat.restrictScalars.{u} (chartThickeningRingHom i)).obj N ≅
      ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS i hi.1))) :
    (Deformation.AlgebraExtension.moduleRes (smallEtaleModelTopology B S hS x.obj.obj.left.1)
        (smallEtaleModelEquiv B S hS x.obj.obj.left).inverse
        (smallEtaleRingedTopos B S hS x.obj.obj.left).O).obj
        (FlatThickeningDeformation.pulledBackConormal (Z := baseSubspace i hi)
          (specialMap i hi x hx)) ≅
      (modelTensorFunctor (chartBaseRingHom x hx)).obj N :=
  chartModelPulledBackConormalIso x hx i hi hT' N e ≪≫
    modelBaseRingTensorCounitIso x.obj.obj.left (chartBaseRingHom x hx) N

/-- `chartModelConormalIso` is, by definition, the restricted `chartPulledBackConormalIso`
followed by the counit of the Comparison Lemma. -/
theorem chartModelConormalIso_hom (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (N : ModuleCat.{u} A)
    (e : (ModuleCat.restrictScalars.{u} (chartThickeningRingHom i)).obj N ≅
      ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS i hi.1))) :
    (chartModelConormalIso x hx i hi hT' N e).hom =
      (chartModelPulledBackConormalIso x hx i hi hT' N e).hom ≫
        (modelBaseRingTensorCounitIso x.obj.obj.left (chartBaseRingHom x hx) N).hom :=
  rfl

/-! ### A square-zero thickening of Situation 07YX -/

section Thickening

variable {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')

/-- The ring map `Γ(Spec A') → A` of `Spec A ⊂ Spec A'` is `q` read through `Γ(Spec A') ≅ A'`. -/
theorem chartThickeningRingHom_arrow :
    chartThickeningRingHom D.arrow =
      D.q.comp (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom D.q)
  refine RingHom.ext fun r => ?_
  have hr := ConcreteCategory.congr_hom h r
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Scheme.Γ.map (B.inclusion.map D.arrow.left).op).hom r) = _
  rw [D.arrow_spec]
  exact hr

/-- An element of `Γ(Spec A')` lies in the ideal of `Spec A ⊂ Spec A'` iff `Γ(Spec A') → A` kills
it. -/
private theorem mem_closedSubspaceBaseIdeal_arrow_iff (r : baseRing B S hS (Over.mk D.toS')) :
    r ∈ closedSubspaceBaseIdeal B S hS
      (rangeSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D).1) ↔
      chartThickeningRingHom D.arrow r = 0 := by
  rw [closedSubspaceBaseIdeal_rangeSubspace B S hS D.arrow _, RingHom.mem_ker]
  exact ((ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1.eq_iff' (map_zero _)).symm

/-- The ideal of `Spec A ⊂ Spec A'` in `Γ(Spec A')` is carried into `Ker(q)` by `Γ(Spec A') ≅ A'`.
-/
theorem ΓSpecIso_hom_mem_ker (r : baseRing B S hS (Over.mk D.toS'))
    (hr : r ∈ closedSubspaceBaseIdeal B S hS
      (rangeSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D).1)) :
    (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom r ∈ RingHom.ker D.q :=
  RingHom.mem_ker.2 <| (RingHom.congr_fun (chartThickeningRingHom_arrow D) r).symm.trans
    ((mem_closedSubspaceBaseIdeal_arrow_iff D r).1 hr)

/-- `Γ(Spec A') ≅ A'` carries `Ker(q)` back into the ideal of `Spec A ⊂ Spec A'`. -/
theorem ΓSpecIso_inv_mem_closedSubspaceBaseIdeal (k : RingHom.ker D.q) :
    (Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom k.1 ∈ closedSubspaceBaseIdeal B S hS
      (rangeSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D).1) :=
  (mem_closedSubspaceBaseIdeal_arrow_iff D _).2 <|
    (RingHom.congr_fun (chartThickeningRingHom_arrow D) _).trans
      ((congrArg D.q (ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso (CommRingCat.of A')).inv_hom_id k.1)).trans (RingHom.mem_ker.1 k.2))

/-- `Γ(Spec A') ≅ A'` is compatible with the action of `Γ(Spec A')` on `Ker(q)` through `q`. -/
theorem thickeningKernel_smul_aux (r : Γ(Spec (CommRingCat.of A'), ⊤)) (k : RingHom.ker D.q) :
    letI := Stacks.Smooth.kerModule D.squareZeroSurjection.1 D.squareZeroSurjection.2
    (Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom
        ((D.q ((Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom r) • k : RingHom.ker D.q) : A') =
      r * (Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom k.1 := by
  let := Stacks.Smooth.kerModule D.squareZeroSurjection.1 D.squareZeroSurjection.2
  rw [Stacks.Smooth.kerModule_smul, Submodule.coe_smul, smul_eq_mul, map_mul]
  exact congrArg (· * _) (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso (CommRingCat.of A')).hom_inv_id r)

/-- The linear equivalence underlying `thickeningKernelIdealIso`. -/
def thickeningKernelIdealLinearEquiv :
    (ModuleCat.restrictScalars.{u} (chartThickeningRingHom D.arrow)).obj D.kernel ≃ₗ[
        baseRing B S hS (Over.mk D.toS')]
      closedSubspaceBaseIdeal B S hS
        (rangeSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D).1) :=
  letI := Stacks.Smooth.kerModule D.squareZeroSurjection.1 D.squareZeroSurjection.2
  { toFun := fun k => ⟨(Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom
        (show RingHom.ker D.q from k).1, ΓSpecIso_inv_mem_closedSubspaceBaseIdeal D _⟩
    invFun := fun r => (show RingHom.ker D.q from
        ⟨(Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom r.1, ΓSpecIso_hom_mem_ker D r.1 r.2⟩)
    map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
    map_smul' := fun r k => Subtype.ext
      (((congrArg (fun a : A => ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom
          ((a • (show RingHom.ker D.q from k) : RingHom.ker D.q) : A')))
          (RingHom.congr_fun (chartThickeningRingHom_arrow D) r)).trans
        (thickeningKernel_smul_aux D r _)))
    left_inv := fun k => Subtype.ext (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (CommRingCat.of A')).inv_hom_id (show RingHom.ker D.q from k).1)
    right_inv := fun r => Subtype.ext (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (CommRingCat.of A')).hom_inv_id r.1) }

/-- **The kernel of a square-zero thickening is the ideal of `Spec A ⊂ Spec A'`**: restricted to
`Γ(Spec A')` along `Γ(Spec A') → A`, the `A`-module `Ker(q)` is the ideal of `Spec A` in
`Γ(Spec A')`, through `Γ(Spec A') ≅ A'`. -/
def thickeningKernelIdealIso :
    (ModuleCat.restrictScalars.{u} (chartThickeningRingHom D.arrow)).obj D.kernel ≅
      ModuleCat.of (baseRing B S hS (Over.mk D.toS'))
        (closedSubspaceBaseIdeal B S hS
          (rangeSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D).1)) :=
  (thickeningKernelIdealLinearEquiv D).toModuleIso

/-- **(G2) The prescribed module of the extension problem of a square-zero thickening of
Situation 07YX is `𝒪_X ⊗_A I`**: for `x = (X → Spec A)` and a square-zero thickening
`Spec A ⊂ Spec A'` with ideal `I = Ker(A' → A)`, the module `f^*𝒞_{Spec A/Spec A'}` of the
extension problem of [Stacks, Section 08V3], restricted to the model of the small étale site of
`X`, is `modelTensorFunctor (chartBaseRingHom x hx)` applied to `I`. -/
def thickeningModelConormalIso :
    (Deformation.AlgebraExtension.moduleRes (smallEtaleModelTopology B S hS x.obj.obj.left.1)
        (smallEtaleModelEquiv B S hS x.obj.obj.left).inverse
        (smallEtaleRingedTopos B S hS x.obj.obj.left).O).obj
        (FlatThickeningDeformation.pulledBackConormal (Z := baseSubspace D.arrow
          (isSquareZeroClosedImmersion_arrow D))
          (specialMap D.arrow (isSquareZeroClosedImmersion_arrow D) x hx)) ≅
      (modelTensorFunctor (chartBaseRingHom x hx)).obj D.kernel :=
  chartModelConormalIso x hx D.arrow (isSquareZeroClosedImmersion_arrow D)
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of A')))) D.kernel (thickeningKernelIdealIso D)

end Thickening

end AlgebraicGeometry.Space.ProperFlatLift

end
