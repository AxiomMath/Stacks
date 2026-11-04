module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModule
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorMono

/-!
# `𝒪_X ⊗_R -` along a morphism `f : X ⟶ Spec(R)`, and its exactness for flat `f`

Let `X` be an algebraic space over a scheme `S` and let `f : X ⟶ T` be a morphism to an object
`T` of the big fppf site, viewed as an algebraic space; write `R = Γ(T, 𝒪_T)`.  This file
constructs the base-ring datum `R →+* Γ(X, 𝒪_X)` of `f`, so that
`AlgebraicGeometry.Space.baseRingTensorModule` applied to it is the module `𝒪_X ⊗_R M` of
Stacks 0D3F, and proves that for flat `f` and affine `T` the functor `M ↦ 𝒪_X ⊗_R M` carries
injections of `R`-modules to monomorphisms of `𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.Space.chartToBaseOfMap`: the morphism `U ⟶ T` induced by `f` on an étale chart
  `U` of `X`.
* `AlgebraicGeometry.Space.globalFunctionsOfMap`: the ring map `Γ(T, 𝒪_T) →+* Γ(X, 𝒪_X)`
  pulling a function back to every étale chart.
* `AlgebraicGeometry.Space.baseRingHomOfMap`: the same, read on the model of the small étale
  site, the base-ring datum of `AlgebraicGeometry.Space.baseRingTensorModule`.

## Main results

* `AlgebraicGeometry.Space.flat_chartToBaseOfMap`: for flat `f`, every chart morphism `U ⟶ T` is a
  flat morphism of schemes.
* `AlgebraicGeometry.Space.exists_ofArrows_mem_modelTopology_flat`: on the model, every object is
  covered by objects whose ring of sections is flat over `R`.
* `AlgebraicGeometry.Space.mono_baseRingTensorModule_map`: for flat `f` and affine `T`,
  `𝒪_X ⊗_R -` carries injections to monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (T : BigFppfOver B S hS)

/-- The ring `R = Γ(T, 𝒪_T)` of global regular functions of an object of the site. -/
abbrev baseRing : Type u := Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))

variable {B S hS T}

/-- The morphism of the site from the scheme underlying an étale chart of `X` to `T` induced by a
morphism `f : X ⟶ T` of algebraic spaces. -/
def chartToBaseOfMap (f : X ⟶ schemeSpace T) (U : SmallEtale B S hS X.1) : U.obj.left ⟶ T :=
  yoneda.preimage (U.obj.hom ≫ f.hom)

/-- The image of `chartToBaseOfMap f U` under the Yoneda embedding is the composite of the chart
`U ⟶ X` with `f`. -/
theorem yoneda_map_chartToBaseOfMap (f : X ⟶ schemeSpace T) (U : SmallEtale B S hS X.1) :
    yoneda.map (chartToBaseOfMap f U) = U.obj.hom ≫ f.hom :=
  yoneda.map_preimage _

/-- The morphisms `chartToBaseOfMap f U` are compatible with morphisms `U ⟶ V` of étale charts
of `X`. -/
theorem chartToBaseOfMap_naturality (f : X ⟶ schemeSpace T) {U V : SmallEtale B S hS X.1}
    (m : U ⟶ V) : m.hom.left ≫ chartToBaseOfMap f V = chartToBaseOfMap f U := by
  apply yoneda.map_injective
  rw [yoneda.map_comp, yoneda_map_chartToBaseOfMap, yoneda_map_chartToBaseOfMap]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f.hom) (CostructuredArrow.w m.hom))

/-- **The global functions of `T` pulled back along `f : X ⟶ T`**: a regular function on `T`
gives, on every étale chart `U` of `X`, its pullback along `U ⟶ T`. -/
def globalFunctionsOfMap (f : X ⟶ schemeSpace T) :
    baseRing B S hS T →+* GlobalFunctionRing (structureSheaf B S hS X.1 X.2) where
  toFun r := ⟨fun U => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (chartToBaseOfMap f U.unop)).op).hom r, fun {U V} m => by
    change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m.unop.hom.left).op).hom
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (chartToBaseOfMap f U.unop)).op).hom r) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Γ.map_comp, ← op_comp, ← Functor.map_comp,
      chartToBaseOfMap_naturality]⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

/-- The base-ring datum of `𝒪_X ⊗_R -` on the model of the small étale site attached to a
morphism `f : X ⟶ T`, with `R = Γ(T, 𝒪_T)`. -/
def baseRingHomOfMap (f : X ⟶ schemeSpace T) :
    baseRing B S hS T →+* modelGlobalFunctions B S hS X :=
  (modelGlobalFunctionsHom B S hS X).comp (globalFunctionsOfMap f)

/-- For a flat morphism `f : X ⟶ T` of algebraic spaces, the morphism of schemes from every
étale chart of `X` to `T` is flat. -/
theorem flat_chartToBaseOfMap (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (U : SmallEtale B S hS X.1) :
    Flat ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f U)) :=
  hflat U.obj.left T U.obj.hom (yoneda.map (𝟙 T)) (chartToBaseOfMap f U) U.property
    (presheaf_yoneda_map_id_etale B S hS T)
    (by rw [yoneda.map_id]; exact (Category.comp_id _).trans (yoneda_map_chartToBaseOfMap f U))

/-- **Over an affine `T`, the sections of `𝒪_X` over every affine étale chart of `X` are flat
over `Γ(T, 𝒪_T)` when `f : X ⟶ T` is flat**, for the algebra structure given by `f`. -/
theorem flat_appTop_chartToBaseOfMap (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (U : SmallEtale B S hS X.1)
    (hU : IsAffineChart B S hS X.1 U) :
    ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f U)).appTop.hom.Flat :=
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left) := hU
  (HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 (flat_chartToBaseOfMap f hflat U)

/-- A morphism into `e.inverse.obj W` is recovered from its transpose along an equivalence. -/
private theorem unit_app_comp_inverse_map_functor_map_comp_counit {C D : Type*} [Category C]
    [Category D] (e : C ≌ D) {U : C} {W : D} (f : U ⟶ e.inverse.obj W) :
    e.unit.app U ≫ e.inverse.map (e.functor.map f ≫ e.counit.app W) = f := by
  rw [Functor.map_comp, ← Equivalence.unitInv_app_inverse, Equivalence.inv_fun_map]
  simp

/-- On the model of the small étale site, every object is covered by objects over which the
structure sheaf is flat over `Γ(T, 𝒪_T)`, when `f : X ⟶ T` is flat and `T` is affine: the
images of the affine étale charts of `X`. -/
theorem exists_ofArrows_mem_modelTopology_flat (f : X ⟶ schemeSpace T)
    (hflat : IsFlat B S hS f.hom) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (W : SmallModel.{u} (SmallEtale B S hS X.1)) :
    ∃ (I : Type u) (Vi : I → SmallModel.{u} (SmallEtale B S hS X.1)) (g : ∀ i, Vi i ⟶ W),
      Sieve.ofArrows Vi g ∈ smallEtaleModelTopology B S hS X.1 W ∧
        ∀ i, letI := baseRingSectionAlgebra (baseRingHomOfMap f) (op (Vi i))
          Module.Flat (baseRing B S hS T)
            ((smallEtaleModelStructureSheaf B S hS X).obj.obj (op (Vi i))) := by
  let e := smallEtaleModelEquiv B S hS X
  obtain ⟨I, Ui, fi, hcov, haff⟩ := hasEnoughObjects_isAffineChart B S hS X.1 (e.inverse.obj W)
  refine ⟨I, fun i => e.functor.obj (Ui i), fun i => e.functor.map (fi i) ≫ e.counit.app W,
    ?_, fun i => ?_⟩
  · rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hcov
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact ⟨_, e.functor.map (fi i) ≫ e.counit.app W, e.unit.app (Ui i),
      Sieve.ofArrows_mk _ _ i, (unit_app_comp_inverse_map_functor_map_comp_counit e (fi i)).symm⟩
  · have hV : IsAffineChart B S hS X.1 (e.inverse.obj (e.functor.obj (Ui i))) := by
      have : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
          ((𝟭 _).obj (Ui i))) := haff i
      exact IsAffine.of_isIso ((SmallEtale.toOver B S hS X.1 ⋙
        BigFppfOver.toScheme B S hS).map (e.unitInv.app (Ui i)))
    exact flat_appTop_chartToBaseOfMap f hflat hT _ hV

/-- **Stacks 0D3F, the first row: for flat `f : X ⟶ Spec(R)`, `𝒪_X ⊗_R -` carries injections
of `R`-modules to monomorphisms of `𝒪_X`-modules.** -/
theorem mono_baseRingTensorModule_map (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {M M' : ModuleCat.{u} (baseRing B S hS T)} (g : M ⟶ M') (hg : Function.Injective g) :
    Mono ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).map g) := by
  have h : Mono ((baseRingTensorFunctor.{u, u, u, u, u} (baseRingHomOfMap f)).map g) :=
    mono_baseRingTensorFunctor_map (baseRingHomOfMap f)
      (exists_ofArrows_mem_modelTopology_flat f hflat hT) g hg
  have := Functor.preservesMonomorphisms_of_adjunction
    (smallEtaleModelModulesEquiv B S hS X).toAdjunction
  exact @Functor.map_mono _ _ _ _ (smallEtaleModelModulesEquiv B S hS X).inverse _ _ _ _ h

end AlgebraicGeometry.Space

end
