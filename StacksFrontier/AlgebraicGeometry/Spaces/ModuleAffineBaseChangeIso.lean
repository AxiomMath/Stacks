module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties

/-!
# Affine base change of a quasi-coherent module, as an isomorphism

Let

```
X' --g'--> X
|f'         |f
v           v
Y' --g-->  Y
```

be a cartesian square of algebraic spaces over a scheme `S` of a big fppf site `B`, with `f`
affine and `g` arbitrary. For every quasi-coherent `𝒪_X`-module `F` the base change map
`g^*f_*F ⟶ f'_*(g')^*F` is an isomorphism; this is the base change clause of Stacks 07U8,
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isAffineHom` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleAffineBaseChange.lean`. This file packages it as an
isomorphism and evaluates it at the structure sheaf, and records the bijectivity of the counit on
the sections over a base-changed chart for a representable `f`.

## Main results

* `AlgebraicGeometry.Space.moduleAffineBaseChangeIso`: the base change map as an isomorphism,
  and `AlgebraicGeometry.Space.modulePullbackPushforwardUnitIso`: its value at the structure
  sheaf, `g^*(f_*𝒪_X) ≅ f'_*𝒪_{X'}`.
* `AlgebraicGeometry.Space.isIso_moduleBaseChangeApp_of_isAffineHom`: the same invertibility in
  the spelling `AlgebraicGeometry.Space.moduleBaseChangeApp`.
* `AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_smallBaseChangeDiagram`: for a
  representable `f` the sections of `f_*F` over an étale chart `V` project bijectively to the
  sections of `F` over the base-changed chart `V ×_Y X`.
* `LinearMap.bijective_baseChange_of_bijective`, `LinearMap.bijective_liftBaseChange_of_bijective`:
  base change of a bijective linear map is bijective.

The quasi-coherence assertion of Stacks 07U8 is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional`,
in `StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageQuasicoherentUnconditional.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace LinearMap

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
  {N P : Type*} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
  {M' P' : Type*} [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M']
  [AddCommGroup P'] [Module A' P']

/-- The base change of a bijective linear map is bijective. -/
theorem bijective_baseChange_of_bijective (i : N →ₗ[A] P) (hi : Function.Bijective i) :
    Function.Bijective (i.baseChange A') :=
  ((LinearEquiv.ofBijective i hi).baseChange A A' N P).bijective

/-- **Base change of a bijection, compared with an injection.**  Let `i : N → P` be a bijection of
`A`-modules, `i' : M' → P'` an injection of `A'`-modules and `θP : A' ⊗_A P → P'` a bijection.
Then an `A`-linear map `μ : N → M'` with `i' ∘ μ = θP ∘ (1 ⊗ i)` has a bijective `A'`-linear
extension `A' ⊗_A N → M'`.  No flatness is needed: this is the case of
`LinearMap.bijective_liftBaseChange_of_equalizer` with a trivial equalizer. -/
theorem bijective_liftBaseChange_of_bijective (i : N →ₗ[A] P) (hi : Function.Bijective i)
    (i' : M' →ₗ[A'] P') (hi' : Function.Injective i') (θP : A' ⊗[A] P →ₗ[A'] P')
    (hθP : Function.Bijective θP) (μ : N →ₗ[A] M') (hμ : ∀ n, i' (μ n) = θP (1 ⊗ₜ i n)) :
    Function.Bijective (μ.liftBaseChange A') := by
  have hcomp : ∀ z, i' (μ.liftBaseChange A' z) = θP (i.baseChange A' z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r n =>
      rw [liftBaseChange_tmul, baseChange_tmul, map_smul, hμ, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hiA := bijective_baseChange_of_bijective (A' := A') i hi
  refine ⟨fun x y hxy => hiA.1 (hθP.1 ?_), fun m => ?_⟩
  · rw [← hcomp, ← hcomp, hxy]
  · obtain ⟨z, hz⟩ := hθP.2 (i' m)
    obtain ⟨w, rfl⟩ := hiA.2 z
    exact ⟨w, hi' ((hcomp w).trans hz)⟩

end LinearMap

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- The base-changed chart `V ×_Y X` of an étale chart `V` of `Y` along a representable `f`, as
a chart diagram over `f`. -/
abbrev smallBaseChangeDiagram (f : X ⟶ Y) (hrep : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS Y.1) : ChartDiagram B S hS X.1 Y.1 f.hom :=
  ⟨(smallBaseChange B S hS f hrep).obj V, V, hrep.snd V.1.hom, hrep.w V.1.hom⟩

/-- The cartesian form of the base-changed chart diagram is the comparison isomorphism of the two
base changes. -/
theorem chartLift_smallBaseChangeDiagram (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    (smallBaseChangeComparisonIso B S hS f hrep V).hom =
      chartLift B S hS f (smallBaseChangeDiagram f hrep V) :=
  chartLift_eq B S hS f (smallBaseChangeDiagram f hrep V) _
    (smallBaseChangeComparisonIso_hom_projection B S hS f hrep V)

/-- The cartesian form of the base-changed chart diagram is surjective. -/
theorem isSurjective_chartLift_smallBaseChangeDiagram (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map
      (chartLift B S hS f (smallBaseChangeDiagram f hrep V))).hom := by
  rw [← chartLift_smallBaseChangeDiagram f hrep V]
  let e := (SpacesEtale.toSpaces B S hS X).mapIso (smallBaseChangeComparisonIso B S hS f hrep V)
  intro y
  refine ⟨pointsMap B S hS _ e.inv.hom y, ?_⟩
  rw [← pointsMap_comp_apply]
  have h : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg (fun q => q.hom) e.inv_hom_id
  change pointsMap B S hS _ (e.inv.hom ≫ e.hom.hom) y = y
  rw [h, pointsMap_id, id_eq]

/-- **The sections of `f_*F` over an étale chart `V` are the sections of `F` over the
base-changed chart `V ×_Y X`, for a representable `f`**: the projection to that chart is
bijective. -/
theorem bijective_modulePushforwardCounitApp_smallBaseChangeDiagram (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) :
    Function.Bijective
      (modulePushforwardCounitApp B S hS f F (smallBaseChangeDiagram f hrep V)) := by
  have hc := isSurjective_chartLift_smallBaseChangeDiagram f hrep V
  refine ⟨injective_modulePushforwardCounitApp f F _ hc, fun p => ?_⟩
  let W := (smallBaseChange B S hS f hrep).obj V
  have hmono : Mono (chartLift B S hS f (smallBaseChangeDiagram f hrep V)) := by
    rw [← chartLift_smallBaseChangeDiagram f hrep V]
    infer_instance
  have hR : IsPullback ((comparisonFunctor B S hS X).map (𝟙 W))
      ((comparisonFunctor B S hS X).map (𝟙 W))
      (chartLift B S hS f (smallBaseChangeDiagram f hrep V))
      (chartLift B S hS f (smallBaseChangeDiagram f hrep V)) := by
    rw [(comparisonFunctor B S hS X).map_id]
    exact IsKernelPair.id_of_mono _
  have hk : IsSurjective B S hS
      ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map (𝟙 W))).hom := by
    rw [(comparisonFunctor B S hS X).map_id, (SpacesEtale.toSpaces B S hS X).map_id]
    exact isSurjective_id B S hS _
  exact exists_modulePushforwardCounitApp_eq f F _ hc (𝟙 W) (𝟙 W) hR (𝟙 W) hk p rfl

/-- The base change map of a cartesian square with `f` affine at a quasi-coherent module, in the
spelling `AlgebraicGeometry.Space.moduleBaseChangeApp` whose type applies the inverse and direct
images one after the other, is an isomorphism. -/
theorem isIso_moduleBaseChangeApp_of_isAffineHom (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    IsIso (moduleBaseChangeApp f f' sq.w F) :=
  isIso_moduleBaseChangeMap_app_of_isAffineHom sq hf F hF

/-- **Affine base change at a quasi-coherent module, as an isomorphism**: the base change map
`g^*f_*F ⟶ f'_*(g')^*F` of a cartesian square with `f` affine, made invertible by
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isAffineHom`. -/
def moduleAffineBaseChangeIso (sq : IsPullback g' f' f g) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    (modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F) ≅
      (modulePushforward B S hS f').obj ((modulePullback B S hS g').obj F) :=
  @asIso _ _ _ _ (moduleBaseChangeApp f f' sq.w F)
    (isIso_moduleBaseChangeApp_of_isAffineHom sq hf F hF)

/-- The forward map of `AlgebraicGeometry.Space.moduleAffineBaseChangeIso` is the base change
map. -/
theorem moduleAffineBaseChangeIso_hom (sq : IsPullback g' f' f g) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    (moduleAffineBaseChangeIso sq hf F hF).hom = moduleBaseChangeApp f f' sq.w F :=
  @asIso_hom _ _ _ _ _ (isIso_moduleBaseChangeApp_of_isAffineHom sq hf F hF)

/-- **Affine base change of the structure sheaf.**  For a cartesian square with `f` affine and
`g` arbitrary, `g^*(f_*𝒪_X) ≅ f'_*𝒪_{X'}`: the base change map at `𝒪_X`, followed by the direct
image along `f'` of the identification `(g')^*𝒪_X ≅ 𝒪_{X'}` of Stacks 03LU. -/
def modulePullbackPushforwardUnitIso (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) :
    (modulePullback B S hS g).obj ((modulePushforward B S hS f).obj
        (SheafOfModules.unit (structureRingSheaf B S hS X))) ≅
      (modulePushforward B S hS f').obj (SheafOfModules.unit (structureRingSheaf B S hS X')) :=
  moduleAffineBaseChangeIso sq hf _ (SheafOfModules.isQuasicoherentOnSite_unit _) ≪≫
    (modulePushforward B S hS f').mapIso (modulePullbackUnitIso B S hS g')

/-- The forward map of `AlgebraicGeometry.Space.modulePullbackPushforwardUnitIso` is the base
change map at `𝒪_X` followed by the direct image of `(g')^*𝒪_X ≅ 𝒪_{X'}`. -/
theorem modulePullbackPushforwardUnitIso_hom (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) :
    (modulePullbackPushforwardUnitIso sq hf).hom =
      moduleBaseChangeApp f f' sq.w (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
        (modulePushforward B S hS f').map (modulePullbackUnitIso B S hS g').hom :=
  congrArg (· ≫ (modulePushforward B S hS f').map (modulePullbackUnitIso B S hS g').hom)
    (moduleAffineBaseChangeIso_hom sq hf _ (SheafOfModules.isQuasicoherentOnSite_unit _))

end AlgebraicGeometry.Space
