module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import StacksFrontier.Algebra.Module.Adequate.InjectiveTangentSurjective
public import StacksFrontier.Algebra.Module.Adequate.TangentEqualizerCounterexample

/-!
# An injective module-valued functor whose tangent functor is not right exact

**Stacks erratum.**  [Stacks, Tag 06ZA] asserts that for an
injective object `I` of the category of module-valued functors on `Alg_A`, every `A`-algebra
`B` and every short exact sequence `0 → N₁ → N → N₂ → 0` of `B`-modules, the sequence of
tangent modules `TI(B, N₁) → TI(B, N) → TI(B, N₂) → 0` is exact.  **This file refutes that
assertion**: it builds a ring, an injective module-valued functor over it and a short exact
sequence for which the tangent sequence is not exact at its middle term `TI(B, N)`.

## The counterexample

Let `k` be a field, `C = k[ε]/(ε²)` and `J = Hom_k(C, k)`, an injective `C`-module.  Put

`I(D) = ∏_{α : D →ₐ[k] C} J`,

with `D` acting on the `α`-component through `α`.  Evaluation at `C` followed by `k`-duality
is left adjoint to `I`, and a monomorphism of module-valued functors is injective at every
algebra, so `I` is an *injective* object of the category of module-valued functors.  For
finite-dimensional `V` the tangent module is

`TI(k, V) = {h : V^* → J | h 0 = 0}`.

Apply this to `0 → k → k² → k → 0`, the inclusion of the first coordinate followed by the
projection to the second.  The two tangent maps are `g ↦ ((a, b) ↦ g a)` and
`h ↦ (b ↦ h (0, b))`.  Choose `0 ≠ j ∈ J` and let `h` be the function with `h (1, 0) = j` and
`h = 0` elsewhere.  Then `h` is killed by the second map, but it is not in the image of the
first, because every element of that image takes equal values at `(1, 0)` and `(1, 1)`.  So
the tangent sequence is **not exact in the middle**.

The formalization takes `k = ℚ`; nothing in the argument depends on the field, and `ℚ` is the
field over which the square-zero vocabulary of
`StacksFrontier/Algebra/Module/Adequate/TangentEqualizerCounterexample.lean` is already set up.
There `0 ≠ j ∈ J` is the augmentation `ℚ[ε] → ℚ`, and the two algebra maps that the image of
the first tangent map cannot separate are that file's `hom₁ ≠ hom₂`.

## What survives, and the companion refutation

Exactness at `TI(B, N₂)` is true, and is
`AdequateFunctor.epi_tangentFunctorAt_map_of_injective` in
`StacksFrontier/Algebra/Module/Adequate/InjectiveTangentSurjective.lean`; this file checks it
against the counterexample itself in
`AdequateFunctor.epi_tangentFunctorAt_map_coinducedDualNum`.  The *proof step* of Tag 06ZA —
that the free module-valued functor preserves the square-zero equalizer — is refuted
separately in
`StacksFrontier/Algebra/Module/Adequate/TangentEqualizerCounterexample.lean`; the present file
refutes the conclusion itself.

## Main definitions

* `AdequateFunctor.coinduced`: the module-valued functor coinduced from a `k`-algebra `D`.
* `AdequateFunctor.coinducedDualNum`: the instance of it at `D = ℚ[ε]`.
* `AdequateFunctor.indicatorAtHom₁`: the element of the middle tangent module that witnesses
  the failure of exactness.

## Main results

* `AdequateFunctor.coinduced_app_apply`: a morphism into the coinduced functor is determined
  by a single `k`-linear functional on the value of its source at `D`.
* `AdequateFunctor.injective_coinduced`: the coinduced functor is an injective object.
* `AdequateFunctor.not_hasRightExactTangentFunctor_coinducedDualNum`: the tangent functor of
  the injective functor coinduced from `ℚ[ε]` is not right exact in the module variable.
* `AdequateFunctor.not_forall_hasRightExactTangentFunctor_of_injective`: **Tag 06ZA is false
  as stated**, the negation of the source's assertion.
* `AdequateFunctor.not_forall_exact_map_tangentFunctorAt_of_injective`: the negation of the
  middle exactness asserted by Tag 06ZA.
* `AdequateFunctor.epi_tangentFunctorAt_map_coinducedDualNum`: the counterexample does
  satisfy the corrected form of Tag 06ZA.

## References

* [Stacks Project, Tag 06Z4](https://stacks.math.columbia.edu/tag/06Z4)
* [Stacks Project, Tag 06ZA](https://stacks.math.columbia.edu/tag/06ZA)
* [Stacks Project, Tag 06ZF](https://stacks.math.columbia.edu/tag/06ZF)
-/

@[expose] public section

namespace AdequateFunctor

open CategoryTheory

universe u v

section Value

variable (k : Type u) [Field k] (D : Type v) [CommRing D] [Algebra k D]

/-- The functions on the `k`-algebra maps `C → D` with values in the `k`-dual of `D`. -/
def coinducedValue (C : Type v) [CommRing C] [Algebra k C] : Type max u v :=
  (C →ₐ[k] D) → (D →ₗ[k] k)

variable {k D}

/-- The coinduced values form an additive group under pointwise addition. -/
instance (C : Type v) [CommRing C] [Algebra k C] : AddCommGroup (coinducedValue k D C) :=
  inferInstanceAs (AddCommGroup ((C →ₐ[k] D) → (D →ₗ[k] k)))

/-- A scalar `c` acts on the component at `φ : C → D` through multiplication by `φ c`. -/
instance (C : Type v) [CommRing C] [Algebra k C] : Module C (coinducedValue k D C) where
  smul c ψ := fun φ => (ψ φ).comp (LinearMap.mulLeft k (φ c))
  one_smul ψ := funext fun φ => LinearMap.ext fun d => by
    change ψ φ (φ 1 * d) = ψ φ d
    rw [map_one φ, one_mul]
  mul_smul c₁ c₂ ψ := funext fun φ => LinearMap.ext fun d => by
    change ψ φ (φ (c₁ * c₂) * d) = ψ φ (φ c₂ * (φ c₁ * d))
    rw [map_mul φ, mul_assoc, mul_left_comm]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul c₁ c₂ ψ := funext fun φ => LinearMap.ext fun d => by
    change ψ φ (φ (c₁ + c₂) * d) = ψ φ (φ c₁ * d) + ψ φ (φ c₂ * d)
    rw [map_add φ, add_mul, map_add (ψ φ)]
  zero_smul ψ := funext fun φ => LinearMap.ext fun d => by
    change ψ φ (φ 0 * d) = 0
    rw [map_zero φ, zero_mul, map_zero (ψ φ)]

/-- The scalar `c : C` acts by multiplying the argument of the component at `φ` by `φ c`. -/
lemma coinducedValue_smul_apply {C : Type v} [CommRing C] [Algebra k C]
    (c : C) (ψ : coinducedValue k D C) (φ : C →ₐ[k] D) (d : D) :
    (c • ψ) φ d = ψ φ (φ c * d) := rfl

/-- Precomposition with an algebra map, as a semilinear map of coinduced values. -/
noncomputable def coinducedRestriction {B C : CommAlgCat.{v} k} (f : B ⟶ C) :
    ModuleCat.of B (coinducedValue k D B) ⟶
      (ModuleCat.restrictScalars f.hom.toRingHom).obj
        (ModuleCat.of C (coinducedValue k D C)) := by
  refine ModuleCat.ofHom
    (X := ModuleCat.of B (coinducedValue k D B))
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj
      (ModuleCat.of C (coinducedValue k D C)))
    { toFun := fun ψ φ => ψ (φ.comp f.hom)
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }
  intro b ψ
  rfl

end Value

section Coinduced

variable (k : Type u) [Field k] (D : Type v) [CommRing D] [Algebra k D]

/-- The module-valued functor coinduced from the `k`-algebra `D`: it sends a `k`-algebra `C`
to the `k`-dual-valued functions on `Mor_k(C, D)`. -/
noncomputable def coinduced :
    PresheafOfModules.{max u v} (algebraStructurePresheaf.{v} k) where
  obj X := ModuleCat.of X.unop.unop (coinducedValue k D X.unop.unop)
  map {_ _} f := coinducedRestriction f.unop.unop
  map_id _ := by ext ψ; rfl
  map_comp _ _ := by ext ψ; rfl

/-- The object of the index category of module-valued functors at the algebra `D`. -/
abbrev coinducedBase : ((CommAlgCat.{v} k)ᵒᵖ)ᵒᵖ :=
  Opposite.op (Opposite.op (CommAlgCat.of k D))

variable {k D}

/-- The coinduced functor sends an algebra map `f` to precomposition with `f`. -/
@[simp]
lemma coinduced_moduleValueMap_apply {B C : Type v} [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] (f : B →ₐ[k] C)
    (ψ : moduleValue k (coinduced k D) B) (φ : C →ₐ[k] D) :
    moduleValueMap k (coinduced k D) f ψ φ = ψ (φ.comp f) := rfl

/-- A morphism of module-valued functors commutes with `d • moduleValueMap φ` for `d : D`. -/
private lemma app_smul_moduleValueMap
    {F G : PresheafOfModules.{max u v} (algebraStructurePresheaf.{v} k)}
    (f : F ⟶ G) {C : Type v} [CommRing C] [Algebra k C]
    (x : moduleValue k F C) (φ : C →ₐ[k] D) (d : D) :
    f.app (coinducedBase k D) (d • moduleValueMap k F φ x) =
      d • moduleValueMap k G φ (f.app (Opposite.op (Opposite.op (CommAlgCat.of k C))) x) := by
  rw [(f.app (coinducedBase k D)).hom.map_smul d]
  exact congrArg (d • ·) (PresheafOfModules.naturality_apply f (CommAlgCat.ofHom φ).op.op x)

/-- A morphism into the coinduced functor is determined by the `k`-linear functional
`z ↦ g(z)(id)(1)` on the value of its source at `D`. -/
lemma coinduced_app_apply
    {F : PresheafOfModules.{max u v} (algebraStructurePresheaf.{v} k)}
    (g : F ⟶ coinduced k D) {C : Type v} [CommRing C] [Algebra k C]
    (x : moduleValue k F C) (φ : C →ₐ[k] D) (d : D) :
    g.app (Opposite.op (Opposite.op (CommAlgCat.of k C))) x φ d =
      g.app (coinducedBase k D) (d • moduleValueMap k F φ x) (AlgHom.id k D) 1 := by
  rw [app_smul_moduleValueMap]
  exact congrArg
    (fun z : D => g.app (Opposite.op (Opposite.op (CommAlgCat.of k C))) x φ z) (mul_one d).symm

end Coinduced

section Injective

variable {k : Type u} [Field k] {D : Type v} [CommRing D] [Algebra k D]

/-- The value of a module-valued functor at `D`, viewed as a `k`-module by restriction of
scalars along `algebraMap k D`. -/
local instance baseKModule
    (F : PresheafOfModules.{max u v} (algebraStructurePresheaf.{v} k)) :
    Module k (moduleValue k F D) :=
  Module.compHom _ (algebraMap k D)

/-- The `k`-linear functional `z ↦ g(z)(id)(1)` attached to a morphism into the coinduced
functor. -/
noncomputable def coinducedFunctional
    {F : PresheafOfModules.{max u v} (algebraStructurePresheaf.{v} k)}
    (g : F ⟶ coinduced k D) : moduleValue k F D →ₗ[k] k where
  toFun z := g.app (coinducedBase k D) z (AlgHom.id k D) 1
  map_add' _ _ := by rw [map_add]; rfl
  map_smul' q z := by
    have h := (g.app (coinducedBase k D)).hom.map_smul (algebraMap k D q) z
    change g.app (coinducedBase k D) (algebraMap k D q • z) (AlgHom.id k D) 1 = _
    rw [h]
    have h2 : ((algebraMap k D q • g.app (coinducedBase k D) z) (AlgHom.id k D)) 1 =
        g.app (coinducedBase k D) z (AlgHom.id k D) (algebraMap k D q * 1) := rfl
    rw [h2, mul_one, Algebra.algebraMap_eq_smul_one,
      (g.app (coinducedBase k D) z (AlgHom.id k D)).map_smul q 1]
    rfl

/-- The value at `D` of a morphism of module-valued functors, as a `k`-linear map. -/
noncomputable def baseMap
    {F G : PresheafOfModules.{max u v} (algebraStructurePresheaf.{v} k)} (f : F ⟶ G) :
    moduleValue k F D →ₗ[k] moduleValue k G D where
  toFun z := f.app (coinducedBase k D) z
  map_add' := map_add _
  map_smul' q z := (f.app (coinducedBase k D)).hom.map_smul (algebraMap k D q) z

/-- The morphism into the coinduced functor determined by a `k`-linear functional on the
value at `D`: it sends `y` over `C` to `φ ↦ (d ↦ μ (d • φ(y)))`. -/
noncomputable def coinducedLift
    {G : PresheafOfModules.{max u v} (algebraStructurePresheaf.{v} k)}
    (mu : moduleValue k G D →ₗ[k] k) : G ⟶ coinduced k D where
  app X := ModuleCat.ofHom
    (X := G.obj X) (Y := (coinduced k D).obj X)
    { toFun := fun y φ =>
        { toFun := fun d => mu (d • moduleValueMap k G φ y)
          map_add' := fun _ _ => by rw [add_smul, map_add]
          map_smul' := fun q d => by
            change mu ((q • d) • moduleValueMap k G φ y) = q * mu (d • _)
            rw [Algebra.smul_def, mul_smul]
            exact mu.map_smul q _ }
      map_add' := fun y y' => funext fun φ => LinearMap.ext fun d => by
        change mu (d • moduleValueMap k G φ (y + y')) = _
        rw [map_add, smul_add, map_add]
        rfl
      map_smul' := fun c y => funext fun φ => LinearMap.ext fun d => by
        change mu (d • moduleValueMap k G φ (c • y)) =
          mu ((φ c * d) • moduleValueMap k G φ y)
        rw [(moduleValueMap k G φ).map_smulₛₗ, smul_smul, mul_comm]
        rfl }
  naturality u := by
    ext y
    refine funext fun φ => LinearMap.ext fun d => ?_
    change mu (d • moduleValueMap k G φ (moduleValueMap k G u.unop.unop.hom y)) =
      mu (d • moduleValueMap k G (φ.comp u.unop.unop.hom) y)
    rw [moduleValueMap_comp]

/-- The module-valued functor coinduced from a `k`-algebra is an injective object: a morphism
into it is one `k`-linear functional on the value at `D`, and such a functional extends along
any injection of `k`-vector spaces. -/
theorem injective_coinduced (k : Type u) [Field k] (D : Type v) [CommRing D] [Algebra k D] :
    Injective (coinduced k D) where
  factors {F G} g f _ := by
    have hinj : Function.Injective (baseMap (D := D) f) :=
      PresheafOfModules.injective_of_mono f _
    obtain ⟨mu, hmu⟩ := ((coinducedFunctional g).comp
      (LinearEquiv.ofInjective (baseMap (D := D) f) hinj).symm.toLinearMap).exists_extend
    have hmuf : ∀ z, mu (baseMap (D := D) f z) = coinducedFunctional g z := by
      intro z
      have h1 := LinearMap.congr_fun hmu
        (LinearEquiv.ofInjective (baseMap (D := D) f) hinj z)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
      exact h1
    refine ⟨coinducedLift mu, PresheafOfModules.hom_ext fun X => ?_⟩
    ext y
    refine funext fun φ => LinearMap.ext fun d => ?_
    change mu (d • moduleValueMap k G φ (f.app X y)) = g.app X y φ d
    rw [← app_smul_moduleValueMap f y φ d]
    exact (hmuf _).trans (coinduced_app_apply g y φ d).symm

end Injective

section NotRightExact

open TangentEqualizer

/-- The dual numbers `ℚ[ε]`, the algebra the counterexample coinduces from. -/
abbrev dualNum : Type := (squareZeroAlgebra ℚ pairOne : CommAlgCat.{0} ℚ)

/-- The injective module-valued functor coinduced from the dual numbers. -/
noncomputable abbrev coinducedDualNum :
    PresheafOfModules.{0} (algebraStructurePresheaf.{0} ℚ) :=
  coinduced ℚ dualNum

/-- The augmentation `ℚ[ε] → ℚ`, a nonzero `ℚ`-linear functional on the dual numbers.  This
is the `0 ≠ j ∈ J` of the counterexample. -/
noncomputable abbrev dualNumFst : dualNum →ₗ[ℚ] ℚ :=
  (squareZeroAugmentation ℚ pairOne).toLinearMap

/-- The witness: the functional `dualNumFst` placed at the single algebra map `hom₁`, and
zero at every other `ℚ[N] → ℚ[ε]`.  This is the function `h` of the counterexample, with
`h (1, 0) = j` and `h = 0` elsewhere. -/
noncomputable def indicatorAtHom₁ : extensionValue ℚ coinducedDualNum pairN :=
  haveI : DecidableEq ((squareZeroAlgebra ℚ pairN : CommAlgCat.{0} ℚ) →ₐ[ℚ] dualNum) :=
    Classical.decEq _
  fun β => if β = hom₁ then dualNumFst else 0

/-- The function `indicatorAtHom₁` takes the value `dualNumFst` at `hom₁`. -/
lemma indicatorAtHom₁_hom₁ : indicatorAtHom₁ hom₁ = dualNumFst := by
  classical
  change (if hom₁ = hom₁ then dualNumFst else 0) = dualNumFst
  simp

/-- The function `indicatorAtHom₁` vanishes at every algebra map other than `hom₁`. -/
lemma indicatorAtHom₁_of_ne
    {β : (squareZeroAlgebra ℚ pairN : CommAlgCat.{0} ℚ) →ₐ[ℚ] dualNum} (h : β ≠ hom₁) :
    indicatorAtHom₁ β = 0 := by
  classical
  change (if β = hom₁ then dualNumFst else 0) = 0
  simp [h]

/-- `hom₁` does not kill `N`, so it does not factor through the augmentation `ℚ[N] → ℚ`. -/
lemma hom₁_ne_comp_augmentation (φ : ℚ →ₐ[ℚ] dualNum) :
    φ.comp (squareZeroAugmentation ℚ pairN) ≠ hom₁ := by
  intro h
  have h1 : TrivSqZeroExt.snd (φ (0 : ℚ)) = (1 : ℚ) :=
    congrArg
      (fun l : (squareZeroAlgebra ℚ pairN : CommAlgCat.{0} ℚ) →ₐ[ℚ] dualNum =>
        TrivSqZeroExt.snd (l ((0 : ℚ), ((1 : ℚ), (0 : ℚ))))) h
  rw [map_zero] at h1
  exact zero_ne_one (show (0 : ℚ) = 1 from h1)

/-- The function `indicatorAtHom₁` lies in the tangent kernel at `pairN`. -/
lemma indicatorAtHom₁_mem : indicatorAtHom₁ ∈ tangentKernel ℚ coinducedDualNum pairN := by
  refine funext fun φ => ?_
  change indicatorAtHom₁ (φ.comp (squareZeroAugmentation ℚ pairN)) = 0
  exact indicatorAtHom₁_of_ne (hom₁_ne_comp_augmentation φ)

/-- The short exact sequence `0 → ℚ → ℚ × ℚ → ℚ → 0` of `ℚ`-modules. -/
noncomputable abbrev coordinateSeq : ShortComplex (ModuleCat.{0} ℚ) :=
  ShortComplex.moduleCatMk (LinearMap.inl ℚ ℚ ℚ) (LinearMap.snd ℚ ℚ ℚ) (by ext; simp)

/-- The sequence `0 → ℚ → ℚ × ℚ → ℚ → 0` of `coordinateSeq` is short exact. -/
lemma coordinateSeq_shortExact : coordinateSeq.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change x.2 = 0 at hx
    exact ⟨x.1, Prod.ext rfl hx.symm⟩
  · rw [ModuleCat.mono_iff_injective]
    change Function.Injective (LinearMap.inl ℚ ℚ ℚ)
    exact LinearMap.inl_injective
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (LinearMap.snd ℚ ℚ ℚ)
    exact fun y => ⟨(0, y), rfl⟩

/-- **The tangent functor of an injective module-valued functor need not be right exact.
Stacks erratum.**
For the injective functor coinduced from `ℚ[ε]` and the short exact sequence
`0 → ℚ → ℚ² → ℚ → 0` of `ℚ`-modules, the indicator function of the first coordinate
functional is killed by the map to `T(ℚ, ℚ)` and is not in the image of `T(ℚ, ℚ)`: the two
algebra maps `hom₁ ≠ hom₂` of Tag 06ZA's equalizer agree on `ℚ[ℚ]`.  This is the
counterexample described in the module documentation, at `k = ℚ`. -/
theorem not_hasRightExactTangentFunctor_coinducedDualNum :
    ¬ HasRightExactTangentFunctor ℚ coinducedDualNum := by
  intro hT
  have h := (hT ℚ coordinateSeq coordinateSeq_shortExact).1
  have h' := (ShortComplex.ab_exact_iff_function_exact
    (coordinateSeq.map (tangentFunctorAt ℚ coinducedDualNum ℚ))).mp h
  change Function.Exact
      ((tangentFunctor ℚ coinducedDualNum).map (ofLinearUp (LinearMap.inl ℚ ℚ ℚ)))
      ((tangentFunctor ℚ coinducedDualNum).map (ofLinearDown (LinearMap.snd ℚ ℚ ℚ))) at h'
  set χ : tangentModule ℚ coinducedDualNum pairN := ⟨indicatorAtHom₁, indicatorAtHom₁_mem⟩
    with hχ
  have hzero :
      (tangentFunctor ℚ coinducedDualNum).map (ofLinearDown (LinearMap.snd ℚ ℚ ℚ)) χ = 0 := by
    apply Subtype.ext
    rw [(tangentFunctor ℚ coinducedDualNum).map_coe]
    refine funext fun γ => ?_
    change indicatorAtHom₁ (γ.comp quotHom) = 0
    exact indicatorAtHom₁_of_ne fun hc => hom₁_notMem_range_comp_quot ⟨γ, hc⟩
  obtain ⟨ψ, hψ⟩ := (h' χ).mp hzero
  have hcoe := congrArg
    (fun t : tangentModule ℚ coinducedDualNum pairN =>
      (t : extensionValue ℚ coinducedDualNum pairN)) hψ
  rw [(tangentFunctor ℚ coinducedDualNum).map_coe] at hcoe
  have e1 := congrFun hcoe hom₁
  have e2 := congrFun hcoe hom₂
  change ψ.val (hom₁.comp inclHom) = indicatorAtHom₁ hom₁ at e1
  change ψ.val (hom₂.comp inclHom) = indicatorAtHom₁ hom₂ at e2
  rw [indicatorAtHom₁_hom₁, hom₁_comp_incl_eq] at e1
  rw [indicatorAtHom₁_of_ne (Ne.symm hom₁_ne_hom₂)] at e2
  have hd : (dualNumFst : dualNum →ₗ[ℚ] ℚ) = 0 := e1.symm.trans e2
  exact one_ne_zero
    (show (1 : ℚ) = 0 from congrArg (fun l : dualNum →ₗ[ℚ] ℚ => l 1) hd)

/-- **Tag 06ZA is false as stated.  Stacks erratum.**
The source asserts that for every ring `A`, every injective object `I` of the category of
module-valued functors on `Alg_A`, every `A`-algebra `B` and every short exact sequence of
`B`-modules, the tangent sequence `TI(B, N₁) → TI(B, N) → TI(B, N₂) → 0` is exact.  This is
the negation of that assertion: there is a ring `A` and an injective object `I` for which
some short exact sequence of modules over some `A`-algebra `B` is not carried by `TI(B, -)`
to a right exact sequence.

The witness is `AdequateFunctor.coinducedDualNum`, the functor `I(D) = ∏_{α : D →ₐ C} J` for
`C = ℚ[ε]/(ε²)` and `J = Hom_ℚ(C, ℚ)`, injective by
`AdequateFunctor.injective_coinduced`, together with `0 → ℚ → ℚ² → ℚ → 0`; exactness fails at
the middle term by `AdequateFunctor.not_hasRightExactTangentFunctor_coinducedDualNum`.  The
corrected statement, surjectivity at `TI(B, N₂)`, is
`AdequateFunctor.epi_tangentFunctorAt_map_of_injective`. -/
theorem not_forall_hasRightExactTangentFunctor_of_injective :
    ¬ ∀ (A : Type) [CommRing A]
        (I : PresheafOfModules.{0} (algebraStructurePresheaf.{0} A)),
        Injective I → HasRightExactTangentFunctor A I := fun h =>
  not_hasRightExactTangentFunctor_coinducedDualNum
    (h ℚ coinducedDualNum (injective_coinduced ℚ dualNum))

/-- **Exactness at `TI(B, N)` in Tag 06ZA is false.  Stacks erratum.**
The source asserts that for every ring `A`, every injective object `I` of the category of
module-valued functors on `Alg_A`, every `A`-algebra `B` and every short exact sequence
`0 → N₁ → N → N₂ → 0` of `B`-modules, the sequence `TI(B, N₁) → TI(B, N) → TI(B, N₂) → 0` is
exact.  This is the negation of its exactness at the middle term `TI(B, N)`.

The witness is the one of
`AdequateFunctor.not_forall_hasRightExactTangentFunctor_of_injective`: the injective functor
`AdequateFunctor.coinducedDualNum` and `0 → ℚ → ℚ² → ℚ → 0`.  Since the other conjunct,
exactness at `TI(B, N₂)`, does hold for every injective functor
(`AdequateFunctor.epi_tangentFunctorAt_map_of_injective`), middle exactness is exactly the
part that fails.  The corrected statement is
`AdequateFunctor.map_comp_eq_zero_and_epi_tangentFunctorAt_map_of_injective`. -/
@[stacks 06ZA "Stacks erratum: the negation of the exactness at `TI(B,N)` asserted by the \
source, witnessed by the injective functor coinduced from `ℚ[ε]` and the sequence \
`0 → ℚ → ℚ² → ℚ → 0`.  The corrected statement is \
`AdequateFunctor.map_comp_eq_zero_and_epi_tangentFunctorAt_map_of_injective`."]
theorem not_forall_exact_map_tangentFunctorAt_of_injective :
    ¬ ∀ (A : Type) [CommRing A]
        (I : PresheafOfModules.{0} (algebraStructurePresheaf.{0} A)), Injective I →
        ∀ (B : Type) [CommRing B] [Algebra A B] (S : ShortComplex (ModuleCat.{0} B)),
          S.ShortExact → (S.map (tangentFunctorAt A I B)).Exact := fun h =>
  not_forall_hasRightExactTangentFunctor_of_injective fun A _ I hI B _ _ S hS =>
    have : Injective I := hI
    ⟨h A I hI B S hS, epi_tangentFunctorAt_map_of_injective A I B S hS⟩

/-- The counterexample satisfies the corrected form of Tag 06ZA: for the injective functor
coinduced from `ℚ[ε]`, every short exact sequence of modules does give a surjection onto the
last tangent module, even though by
`AdequateFunctor.not_hasRightExactTangentFunctor_coinducedDualNum` the tangent sequence is
not exact at its middle term. -/
theorem epi_tangentFunctorAt_map_coinducedDualNum (B : Type) [CommRing B] [Algebra ℚ B]
    (S : ShortComplex (ModuleCat.{0} B)) (hS : S.ShortExact) :
    Epi ((tangentFunctorAt ℚ coinducedDualNum B).map S.g) :=
  have : Injective coinducedDualNum := injective_coinduced ℚ dualNum
  epi_tangentFunctorAt_map_of_injective ℚ coinducedDualNum B S hS

end NotRightExact

end AdequateFunctor
