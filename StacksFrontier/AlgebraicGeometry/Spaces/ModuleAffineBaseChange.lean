module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase

/-!
# Affine base change for the direct image of a quasi-coherent module

Let

```
X' --g'--> X
|f'         |f
v           v
Y' --g-->  Y
```

be a cartesian square of algebraic spaces over a scheme `S` of a big fppf site `B`, with `f`
affine.  For every quasi-coherent `𝒪_X`-module `F` the base change map
`g^*f_*F ⟶ f'_*(g')^*F` of `AlgebraicGeometry.Space.moduleBaseChangeMap` is an isomorphism.
This is the base change clause of Stacks 07U8, the algebraic-space form of affine base change
(Stacks 02KG, part (2), for schemes).  No hypothesis is placed on `g`.

## Main results

* `AlgebraicGeometry.Space.exists_affine_chart_isIso_chartLift`: for an affine `f` and an affine
  étale scheme chart `V` of `Y`, the algebraic space `V ×_Y X` is itself an affine étale scheme
  chart of `X`.
* `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isAffineHom`: the statement above.
* `AlgebraicGeometry.Space.nonempty_modulePullbackModulePushforwardIso_of_isAffineHom`: the
  resulting isomorphism `g^*f_*F ≅ f'_*(g')^*F`.

## Proof

Invertibility is checked on the sections over the source charts `U'` of the affine chart
diagrams `U' ⟶ V` over `g` (`AlgebraicGeometry.Space.isIso_of_bijective_affineChartDiagram`),
exactly as for flat base change in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFlatBaseChangeQuasicoherent.lean`.  The difference
is that `f` being affine, `V ×_Y X` is represented by an affine scheme `W`, which is an étale
scheme chart of `X`; so the sections of `f_*F` over `V` *are* the sections of `F` over `W`,
with no equalizer to preserve.  Base changing `W` along `U' ⟶ V` gives an affine chart of `X'`
over which the sections of `(g')^*F` are `𝒪(U') ⊗_{𝒪(V)} F(W)`, and the sections of `f'_*(g')^*F`
over `U'` inject into them.  This identifies `(g^*f_*F)(U') = 𝒪(U') ⊗_{𝒪(V)} (f_*F)(V)` with
`(f'_*(g')^*F)(U')` without any flatness.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace LinearMap

/-- **Base change of a module identified with a second module through a bijection.**  Let
`i : N → P` be a bijective `A`-linear map, `i' : M' → P'` an injective `A'`-linear map and
`θP : A' ⊗_A P → P'` a bijective `A'`-linear map.  Then an `A`-linear map `μ : N → M'` with
`i' ∘ μ = θP ∘ (1 ⊗ i)` has a bijective `A'`-linear extension `A' ⊗_A N → M'`.  No flatness of
`A'` over `A` is needed. -/
theorem bijective_liftBaseChange_of_bijective_of_injective {A A' : Type*} [CommRing A]
    [CommRing A'] [Algebra A A'] {N P : Type*} [AddCommGroup N] [Module A N] [AddCommGroup P]
    [Module A P] {M' P' : Type*} [AddCommGroup M'] [Module A' M'] [Module A M']
    [IsScalarTower A A' M'] [AddCommGroup P'] [Module A' P']
    (i : N →ₗ[A] P) (hi : Function.Bijective i) (i' : M' →ₗ[A'] P')
    (hi' : Function.Injective i') (θP : A' ⊗[A] P →ₗ[A'] P') (hθP : Function.Bijective θP)
    (μ : N →ₗ[A] M') (hμ : ∀ n, i' (μ n) = θP (1 ⊗ₜ i n)) :
    Function.Bijective (μ.liftBaseChange A') := by
  have hcomp : ∀ z, i' (μ.liftBaseChange A' z) = θP (i.baseChange A' z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r n =>
      rw [liftBaseChange_tmul, baseChange_tmul, map_smul, hμ, ← map_smul, smul_tmul',
        smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hiA : Function.Bijective (i.baseChange A') :=
    ((LinearEquiv.ofBijective i hi).baseChange A A' N P).bijective
  refine ⟨fun x y hxy => hiA.1 (hθP.1 (by rw [← hcomp, ← hcomp, hxy])), fun m => ?_⟩
  obtain ⟨z, hz⟩ := hθP.2 (i' m)
  obtain ⟨w, rfl⟩ := hiA.2 z
  exact ⟨w, hi' ((hcomp w).trans hz)⟩

end LinearMap

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Chart

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **For an affine morphism `f : X ⟶ Y` and an affine étale scheme chart `V` of `Y`, the
algebraic space `V ×_Y X` is an affine étale scheme chart of `X`.**  There is an étale scheme
chart `W` of `X` with affine underlying scheme and a morphism `W ⟶ V` over `f` whose cartesian
form `W ⟶ V ×_Y X` is an isomorphism. -/
theorem exists_affine_chart_isIso_chartLift (hf : IsAffineHom B S hS f.hom)
    (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V)) :
    ∃ (W : SmallEtale B S hS X.1)
      (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
      (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom),
      IsAffine (chartScheme W) ∧ IsIso (chartLift B S hS f ⟨W, V, b, hb⟩) := by
  obtain ⟨W₀, p, q, hpq⟩ := hf ⟨V.1.left, hV⟩ V.1.hom
  have P1 := AlgebraicSpaces.isPullback_hom B S hS (isPullback_chartBaseChangeInclusion B S hS f V)
  let p₀ := (hpq.isoIsPullback _ _ P1).hom
  let W : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (p₀ ≫ (chartBaseChangeInclusion B S hS f V).hom),
      presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS (isEtale_of_isIso B S hS p₀)
        (isEtale_chartBaseChangeInclusion B S hS f V))⟩
  let b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V :=
    yoneda.preimage (show yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W) ⟶
      yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V) from
        p₀ ≫ (chartBaseChangeProjection B S hS f V).hom)
  have hyb : yoneda.map b = p₀ ≫ (chartBaseChangeProjection B S hS f V).hom :=
    yoneda.map_preimage _
  have hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom := by
    rw [hyb]
    exact (Category.assoc _ _ _).trans ((congrArg (p₀ ≫ ·) P1.w).trans
      (Category.assoc _ _ _).symm)
  let c₀ : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS f V :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk p₀) rfl)
  refine ⟨W, b, hb, W₀.property, ?_⟩
  rw [← chartLift_eq B S hS f ⟨W, V, b, hb⟩ c₀ (ObjectProperty.hom_ext _ hyb.symm)]
  let F := SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _
  have : IsIso (F.map c₀) := inferInstanceAs (IsIso p₀)
  exact isIso_of_reflects_iso c₀ F

/-- **If the cartesian lift of a chart diagram is an isomorphism, it is surjective.** -/
private theorem isSurjective_chartLift_of_isIso (e : ChartDiagram B S hS X.1 Y.1 f.hom)
    [IsIso (chartLift B S hS f e)] :
    IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map (chartLift B S hS f e)).hom :=
  isSurjective_of_isIso B S hS ((SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _).map
    (chartLift B S hS f e))

/-- **The sections of `f_*F` over `V` are those of `F` over a chart `U` with `U ≅ V ×_Y X`.** -/
theorem bijective_modulePushforwardCounitApp_of_isIso_chartLift
    (F : Modules.{u, u} B S hS X.1 X.2) (e : ChartDiagram B S hS X.1 Y.1 f.hom)
    [IsIso (chartLift B S hS f e)] :
    Function.Bijective (modulePushforwardCounitApp B S hS f F e) := by
  have hsurj := isSurjective_chartLift_of_isIso f e
  have hpb : IsPullback ((comparisonFunctor B S hS X).map (𝟙 e.U))
      ((comparisonFunctor B S hS X).map (𝟙 e.U)) (chartLift B S hS f e) (chartLift B S hS f e) := by
    rw [CategoryTheory.Functor.map_id]
    exact IsKernelPair.id_of_mono _
  have hk : IsSurjective B S hS
      ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map (𝟙 e.U))).hom := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact isSurjective_of_isIso B S hS (𝟙 _)
  exact ⟨injective_modulePushforwardCounitApp f F e hsurj, fun p =>
    exists_modulePushforwardCounitApp_eq f F e hsurj (𝟙 e.U) (𝟙 e.U) hpb (𝟙 e.U) hk p rfl⟩

end Chart

section Main

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- **Affine base change on the sections over an affine chart diagram.** -/
theorem bijective_moduleBaseChangeMap_app_val_app_of_isAffineHom (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (d : ChartDiagram B S hS Y'.1 Y.1 g.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V)) :
    Function.Bijective (((moduleBaseChangeMap f g f' g' sq.w).app F).val.app (op d.U)).hom := by
  obtain ⟨W, b, hb, hWa, hiso⟩ := exists_affine_chart_isIso_chartLift f hf d.V hV
  let e : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨W, d.V, b, hb⟩
  let e' := chartBaseChangeAlongDiagram sq d.g d.comm b hb
  let T := chartBaseChangeAlong sq d.g d.comm b hb
  let N := (modulePushforward B S hS f).obj F
  let F' := (modulePullback B S hS g').obj F
  let M := (modulePushforward B S hS f').obj F'
  have hN : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f
      (isQuasiCompact_of_isAffineHom' B S hS f.hom X.2 Y.2 hf)
      (isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isAffineHom B S hS f.hom X.2 Y.2 hf))
      F hF
  let iAA' := chartDiagramAlgebra B S hS g d
  let mP : Module (chartRing B S hS Y.1 Y.2 d.V) (F.val.obj (op W)) :=
    Module.compHom _ (chartDiagramRestrict B S hS f e)
  let mP' : Module (chartRing B S hS Y'.1 Y'.2 d.U) (F'.val.obj (op T)) :=
    Module.compHom _ (chartDiagramRestrict B S hS f' e')
  let mM : Module (chartRing B S hS Y.1 Y.2 d.V) (M.val.obj (op d.U)) :=
    Module.compHom _ (algebraMap (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U))
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (M.val.obj (op d.U)) := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨θP, hθP, hθPt⟩ := exists_bijective_liftBaseChange_unitSection sq F hF d hU hV b hb hWa
  let iL : N.val.obj (op d.V) →ₗ[chartRing B S hS Y.1 Y.2 d.V] F.val.obj (op W) :=
    ⟨⟨modulePushforwardCounitApp B S hS f F e, modulePushforwardCounitApp_add B S hS f F e⟩,
      modulePushforwardCounitApp_smul B S hS f F e⟩
  let iL' : M.val.obj (op d.U) →ₗ[chartRing B S hS Y'.1 Y'.2 d.U] F'.val.obj (op T) :=
    ⟨⟨modulePushforwardCounitApp B S hS f' F' e', modulePushforwardCounitApp_add B S hS f' F' e'⟩,
      modulePushforwardCounitApp_smul B S hS f' F' e'⟩
  let β : ((modulePullback B S hS g).obj N).val.obj (op d.U) ⟶ M.val.obj (op d.U) :=
    ((moduleBaseChangeMap f g f' g' sq.w).app F).val.app (op d.U)
  let μ : N.val.obj (op d.V) →ₗ[chartRing B S hS Y.1 Y.2 d.V] M.val.obj (op d.U) :=
    { toFun := fun n => β.hom (modulePullbackChartSection B S hS g N d n)
      map_add' := fun x y => by rw [modulePullbackChartSection_add, map_add]
      map_smul' := fun r x => by
        rw [modulePullbackChartSection_smul, map_smul]
        rfl }
  have hi' : Function.Injective iL' := injective_modulePushforwardCounitApp f' F' e'
    (isSurjective_chartLift_chartBaseChangeAlongDiagram sq d.g d.comm b hb
      (isSurjective_chartLift_of_isIso f e))
  exact LinearMap.bijective_of_comp_liftBaseChange (A' := chartRing B S hS Y'.1 Y'.2 d.U)
    (modulePullbackChartBaseChange B S hS g N d) β.hom μ
    (fun n => congrArg β.hom ((modulePullbackChartBaseChange_tmul B S hS g N d 1 n).trans
      (one_smul _ _)))
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS g N hN d hU hV)
    (LinearMap.bijective_liftBaseChange_of_bijective_of_injective
      (A' := chartRing B S hS Y'.1 Y'.2 d.U) iL
      (bijective_modulePushforwardCounitApp_of_isIso_chartLift f F e) iL' hi' θP hθP μ fun n =>
        (modulePushforwardCounitApp_moduleBaseChangeMap_chartSection sq F d b hb n).trans
          ((one_smul _ _).symm.trans (hθPt 1 (iL n)).symm))

/-- **Affine base change for the direct image of a quasi-coherent module** (the base change
clause of Stacks 07U8; Stacks 02KG for schemes).  For a cartesian square of algebraic spaces
whose right morphism `f` is affine, the base change map `g^*f_*F ⟶ f'_*(g')^*F` is an
isomorphism at every quasi-coherent `𝒪_X`-module `F`.  The bottom morphism `g` is
arbitrary. -/
@[stacks 07U8 "base change: g^*f_*F = f'_*(g')^*F for f affine and F quasi-coherent"]
theorem isIso_moduleBaseChangeMap_app_of_isAffineHom (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((moduleBaseChangeMap f g f' g' sq.w).app F) :=
  isIso_of_bijective_affineChartDiagram B S hS g _ fun d hU hV =>
    bijective_moduleBaseChangeMap_app_val_app_of_isAffineHom sq hf F hF d hU hV

/-- **Affine base change, as an isomorphism** (the base change clause of Stacks 07U8): for a
cartesian square whose right morphism `f` is affine and a quasi-coherent `𝒪_X`-module `F`,
`g^*f_*F ≅ f'_*(g')^*F`, by the base change map of
`AlgebraicGeometry.Space.moduleBaseChangeMap`. -/
theorem nonempty_modulePullbackModulePushforwardIso_of_isAffineHom (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    Nonempty ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F) ≅
      (modulePushforward B S hS f').obj ((modulePullback B S hS g').obj F)) :=
  have := isIso_moduleBaseChangeMap_app_of_isAffineHom sq hf F hF
  ⟨asIso ((moduleBaseChangeMap f g f' g' sq.w).app F)⟩

end Main

end AlgebraicGeometry.Space

end
