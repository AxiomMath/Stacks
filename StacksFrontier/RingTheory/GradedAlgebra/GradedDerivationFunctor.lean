module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.WeightedPresentation

/-!
# Degree-preserving derivations with values in `P ⊗ V`, as a functor of `V`

Let `P` be a graded algebra over a field `k`. For a `k`-vector space `V`, the trivial first-order
deformation of `P` over the square-zero extension `k[V] = k ⊕ V` is `k[V] ⊗_k P`, and an
automorphism of it over `k[V]` which preserves the grading and reduces to the identity of `P`
is `1 ⊗ x ↦ 1 ⊗ x + D x` for a degree-preserving `k`-derivation `D : P → P ⊗_k V`. This is the
infinitesimal-automorphism half of the proof of Stacks 0DVZ, for an arbitrary test module `V`
rather than only for the dual numbers.

The finite-dimensionality criterion of Stacks 06IH needs the derivations not at a single `V`
but as an additive `k`-linear functor on finitely generated `k`-modules, together with a natural
injection of the automorphisms into it. This file supplies both, in pure commutative algebra.

## Main definitions

* `GradedAlgebra.gradedDerivations`: the `k`-derivations `D : P → P ⊗[k] V` sending each graded
  piece `P_d` into the image of `P_d ⊗[k] V`.
* `GradedAlgebra.gradedDerivationFunctor`: `V ↦ gradedDerivations grading V` as a functor
  `FGModuleCat k ⥤ ModuleCat k`, with its `Functor.Additive` and `Functor.Linear k` instances.
* `GradedAlgebra.trivSqZeroExtTensorFst`, `GradedAlgebra.trivSqZeroExtTensorSnd`: the two
  coordinates `k[V] ⊗ P → P` and `k[V] ⊗ P → P ⊗ V` of the decomposition
  `k[V] ⊗ P = P ⊕ (P ⊗ V)`.
* `GradedAlgebra.trivSqZeroExtTensorReduction`: the reduction `k[V] ⊗ P → k ⊗ P`.
* `GradedAlgebra.trivSqZeroExtTensorMap`: the map `k[V] ⊗ P → k[W] ⊗ P` induced by `V → W`.
* `GradedAlgebra.derivationOfAlgHom`: the derivation `x ↦ σ (1 ⊗ x) - 1 ⊗ x` attached to an
  automorphism `σ` of the trivial deformation reducing to the identity.

## Main results

* `GradedAlgebra.finiteDimensional_gradedDerivationFunctor_obj`: for `P` of finite type with
  finite-dimensional graded pieces, every value of the functor is finite-dimensional.
* `GradedAlgebra.derivationOfAlgHom_injective`: `σ` is determined by its derivation.
* `GradedAlgebra.derivationOfAlgHom_naturality`: the derivation is natural in `V`.
* `GradedAlgebra.derivationOfAlgHom_id`: the identity has derivation zero.
* `GradedAlgebra.trivSqZeroExtTensorSnd_mul`, `GradedAlgebra.trivSqZeroExtTensor_ext`: the
  second coordinate satisfies the Leibniz rule, and the two coordinates determine an element.

## Implementation notes

`P ⊗[k] V` is a `P`-module through the left factor, and the pushforward along `f : V → W` is
the `P`-linear map `TensorProduct.AlgebraTensorModule.lTensor P P f`, whose underlying function
is `LinearMap.lTensor P f`.

The kernel of the reduction `k[V] ⊗ P → k ⊗ P` is identified with `P ⊗ V` through the second
coordinate `trivSqZeroExtTensorSnd : r ⊗ p ↦ p ⊗ r.snd`, which vanishes on `1 ⊗ P`. Hence the
derivation attached to `σ` is `x ↦ trivSqZeroExtTensorSnd (σ (1 ⊗ x))`, with no subtraction:
this is `σ (1 ⊗ x) - 1 ⊗ x` read in `P ⊗ V`.

The hypotheses on `σ` are asked only on the generators `1 ⊗ x` of `k[V] ⊗ P` over `k[V]`:
`σ (1 ⊗ x)` lies in the degree-`d` part `k[V] ⊗ P_d` when `x ∈ P_d`, and reduces to `1 ⊗ x`.
For a `k[V]`-algebra map these are equivalent to `σ` preserving every degree-`d` part and to
`reduction ∘ σ = reduction`, and they are weaker as stated.

The opposite scalar action `Module kᵐᵒᵖ V` needed for the ring structure of `TrivSqZeroExt k V`
is not a global instance in Mathlib; it is taken as an instance argument, together with
`IsCentralScalar k V`, so that any of the local instances of the project can be supplied.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

namespace GradedAlgebra

universe w

variable {k : Type w} [Field k] {P : Type w} [CommRing P] [Algebra k P]
  (grading : ℕ → Submodule k P)

/-! ### Degree-preserving derivations -/

section Derivations

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- **Degree-preserving derivations with values in `P ⊗ V`.** The `k`-derivations
`D : P → P ⊗[k] V` sending each graded piece `P_d` into the image of `P_d ⊗[k] V`. -/
def gradedDerivations : Submodule k (Derivation k P (P ⊗[k] V)) where
  carrier := {D | ∀ d x, x ∈ grading d →
    D x ∈ LinearMap.range (TensorProduct.map (grading d).subtype (LinearMap.id : V →ₗ[k] V))}
  zero_mem' := by
    intro d x _
    rw [Derivation.zero_apply]
    exact Submodule.zero_mem _
  add_mem' := by
    intro D E hD hE d x hx
    rw [Derivation.add_apply]
    exact Submodule.add_mem _ (hD d x hx) (hE d x hx)
  smul_mem' := by
    intro r D hD d x hx
    rw [Derivation.smul_apply]
    exact Submodule.smul_mem _ r (hD d x hx)

variable {V} {W : Type w} [AddCommGroup W] [Module k W]

/-- Tensoring with `f : V → W` maps the image of `P_d ⊗ V` into the image of `P_d ⊗ W`. -/
theorem lTensor_mem_range_map_subtype (f : V →ₗ[k] W) (d : ℕ) {y : P ⊗[k] V}
    (hy : y ∈ LinearMap.range (TensorProduct.map (grading d).subtype (LinearMap.id : V →ₗ[k] V))) :
    f.lTensor P y ∈
      LinearMap.range (TensorProduct.map (grading d).subtype (LinearMap.id : W →ₗ[k] W)) := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨f.lTensor _ z, by simp⟩

/-- **Pushforward of degree-preserving derivations** along `f : V → W`: composition with the
`P`-linear map `P ⊗ V → P ⊗ W`. -/
def gradedDerivationsMap (f : V →ₗ[k] W) :
    gradedDerivations grading V →ₗ[k] gradedDerivations grading W where
  toFun D := ⟨(AlgebraTensorModule.lTensor P P f).compDer D.1,
    fun d x hx => lTensor_mem_range_map_subtype grading f d (D.2 d x hx)⟩
  map_add' D E := by
    ext x
    simp
  map_smul' r D := by
    ext x
    simp

/-- The pushforward of `D` along `f` sends `x` to `(P ⊗ f) (D x)`. -/
@[simp]
theorem gradedDerivationsMap_apply (f : V →ₗ[k] W) (D : gradedDerivations grading V) (x : P) :
    (gradedDerivationsMap grading f D).1 x = f.lTensor P (D.1 x) := rfl

end Derivations

/-- **The functor of degree-preserving derivations**,
`V ↦ {D : P → P ⊗[k] V degree-preserving k-derivation}`, on finitely generated `k`-modules, with
pushforward along `f : V → W` given by composition with `P ⊗ f`. -/
def gradedDerivationFunctor : FGModuleCat.{w} k ⥤ ModuleCat.{w} k where
  obj V := ModuleCat.of k (gradedDerivations grading V)
  map f := ModuleCat.ofHom (gradedDerivationsMap grading f.hom.hom)
  map_id V := by
    ext D x
    simp
  map_comp f g := by
    ext D x
    simp [LinearMap.lTensor_comp_apply]

/-- The functor of degree-preserving derivations is additive. -/
instance : (gradedDerivationFunctor grading).Additive where
  map_add := by
    intro V V' f g
    refine ModuleCat.hom_ext (LinearMap.ext fun D => Subtype.ext (Derivation.ext fun x => ?_))
    change (f + g).hom.hom.lTensor P (D.1 x) =
      f.hom.hom.lTensor P (D.1 x) + g.hom.hom.lTensor P (D.1 x)
    rw [show (f + g).hom = f.hom + g.hom from ModuleCat.hom_ext rfl, ModuleCat.hom_add,
      LinearMap.lTensor_add, LinearMap.add_apply]

/-- The functor of degree-preserving derivations is `k`-linear. -/
instance : (gradedDerivationFunctor grading).Linear k where
  map_smul := by
    intro V V' f r
    refine ModuleCat.hom_ext (LinearMap.ext fun D => Subtype.ext (Derivation.ext fun x => ?_))
    change (r • f).hom.hom.lTensor P (D.1 x) = r • f.hom.hom.lTensor P (D.1 x)
    rw [show (r • f).hom = r • f.hom from ModuleCat.hom_ext rfl, ModuleCat.hom_smul,
      LinearMap.lTensor_smul, LinearMap.smul_apply]

/-- **Finite-dimensionality of the degree-preserving derivations.** For a graded algebra of
finite type over a field with finite-dimensional graded pieces, every value of
`gradedDerivationFunctor` is finite-dimensional: a derivation is determined by its values on
finitely many homogeneous algebra generators `v i ∈ P_{d i}`, and those values lie in the
finite-dimensional images of `P_{d i} ⊗ V`. -/
theorem finiteDimensional_gradedDerivationFunctor_obj [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)] [Algebra.FiniteType k P] (V : FGModuleCat.{w} k) :
    FiniteDimensional k ((gradedDerivationFunctor grading).obj V) := by
  change FiniteDimensional k (gradedDerivations grading V)
  obtain ⟨n, v, d, v_mem, hgen⟩ := exists_fin_homogeneous_adjoin_eq_top grading
  let E : gradedDerivations grading V →ₗ[k] ((i : Fin n) →
      LinearMap.range (TensorProduct.map (grading (d i)).subtype (LinearMap.id : V →ₗ[k] V))) :=
    { toFun := fun D i => ⟨D.1 (v i), D.2 (d i) (v i) (v_mem i)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine FiniteDimensional.of_injective E fun D F h => Subtype.ext <|
    Derivation.ext_of_adjoin_eq_top (D1 := D.1) (D2 := F.1) (Set.range v) hgen ?_
  rintro x ⟨i, rfl⟩
  exact congrArg Subtype.val (congrFun h i)

/-! ### The trivial first-order deformation `k[V] ⊗ P` -/

section TrivialDeformation

variable (V : Type w) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

variable (k P) in
/-- **The reduction of the trivial deformation**, `k[V] ⊗ P → k ⊗ P`, induced by the
augmentation `k[V] → k`. -/
def trivSqZeroExtTensorReduction : TrivSqZeroExt k V ⊗[k] P →ₐ[k] k ⊗[k] P :=
  Algebra.TensorProduct.map (TrivSqZeroExt.fstHom k k V) (AlgHom.id k P)

/-- The reduction sends `r ⊗ p` to `r.fst ⊗ p`. -/
@[simp]
theorem trivSqZeroExtTensorReduction_tmul (r : TrivSqZeroExt k V) (p : P) :
    trivSqZeroExtTensorReduction k P V (r ⊗ₜ p) = r.fst ⊗ₜ p := rfl

variable (k P) in
/-- **The first coordinate of the trivial deformation**, `k[V] ⊗ P → P`, `r ⊗ p ↦ r.fst • p`:
the reduction followed by `k ⊗ P = P`. -/
def trivSqZeroExtTensorFst : TrivSqZeroExt k V ⊗[k] P →ₗ[k] P :=
  (TensorProduct.lid k P).toLinearMap ∘ₗ (trivSqZeroExtTensorReduction k P V).toLinearMap

/-- The first coordinate sends `r ⊗ p` to `r.fst • p`. -/
@[simp]
theorem trivSqZeroExtTensorFst_tmul (r : TrivSqZeroExt k V) (p : P) :
    trivSqZeroExtTensorFst k P V (r ⊗ₜ p) = r.fst • p := by
  simp [trivSqZeroExtTensorFst, trivSqZeroExtTensorReduction_tmul]

variable (k P) in
/-- **The second coordinate of the trivial deformation**, `k[V] ⊗ P → P ⊗ V`,
`r ⊗ p ↦ p ⊗ r.snd`. It identifies the kernel of the reduction with `P ⊗ V`. -/
def trivSqZeroExtTensorSnd : TrivSqZeroExt k V ⊗[k] P →ₗ[k] P ⊗[k] V :=
  (TensorProduct.comm k V P).toLinearMap ∘ₗ
    TensorProduct.map (TrivSqZeroExt.sndHom k V) (LinearMap.id : P →ₗ[k] P)

omit [Module kᵐᵒᵖ V] [IsCentralScalar k V] in
/-- The second coordinate sends `r ⊗ p` to `p ⊗ r.snd`. -/
@[simp]
theorem trivSqZeroExtTensorSnd_tmul (r : TrivSqZeroExt k V) (p : P) :
    trivSqZeroExtTensorSnd k P V (r ⊗ₜ p) = p ⊗ₜ r.snd := rfl

/-- The second coordinate of a product: `(q q')₂ = q₁ • q'₂ + q'₁ • q₂`, the `P`-action on
`P ⊗ V` being on the left factor. -/
theorem trivSqZeroExtTensorSnd_mul (q q' : TrivSqZeroExt k V ⊗[k] P) :
    trivSqZeroExtTensorSnd k P V (q * q') =
      trivSqZeroExtTensorFst k P V q • trivSqZeroExtTensorSnd k P V q' +
        trivSqZeroExtTensorFst k P V q' • trivSqZeroExtTensorSnd k P V q := by
  induction q using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb, add_smul, smul_add]
    abel
  | tmul r p =>
    induction q' using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [mul_add, map_add, ha, hb, add_smul, smul_add]
      abel
    | tmul r' p' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, trivSqZeroExtTensorSnd_tmul,
        trivSqZeroExtTensorSnd_tmul, trivSqZeroExtTensorSnd_tmul, trivSqZeroExtTensorFst_tmul,
        trivSqZeroExtTensorFst_tmul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, tmul_add,
        ← smul_tmul, ← smul_tmul, smul_tmul', smul_tmul', smul_eq_mul, smul_eq_mul,
        smul_mul_assoc, smul_mul_assoc, mul_comm p' p]

/-- The trivial deformation is recovered from its two coordinates:
`q = 1 ⊗ q₁ + ι(q₂)`, where `ι : P ⊗ V → k[V] ⊗ P` is `p ⊗ v ↦ v ⊗ p`. -/
theorem trivSqZeroExtTensor_eq_add (q : TrivSqZeroExt k V ⊗[k] P) :
    (1 : TrivSqZeroExt k V) ⊗ₜ trivSqZeroExtTensorFst k P V q +
        TensorProduct.map (TrivSqZeroExt.inrHom k V) (LinearMap.id : P →ₗ[k] P)
          (TensorProduct.comm k P V (trivSqZeroExtTensorSnd k P V q)) = q := by
  induction q using TensorProduct.inductionOn with
  | add a b ha hb =>
    rw [map_add, map_add, map_add, map_add, tmul_add, add_add_add_comm, ha, hb]
  | tmul r p =>
    rw [trivSqZeroExtTensorFst_tmul, trivSqZeroExtTensorSnd_tmul, comm_tmul, map_tmul,
      LinearMap.id_apply, ← smul_tmul, ← add_tmul]
    congr 1
    ext <;> simp

/-- An element of the trivial deformation is determined by its two coordinates. -/
theorem trivSqZeroExtTensor_ext {q q' : TrivSqZeroExt k V ⊗[k] P}
    (h₁ : trivSqZeroExtTensorFst k P V q = trivSqZeroExtTensorFst k P V q')
    (h₂ : trivSqZeroExtTensorSnd k P V q = trivSqZeroExtTensorSnd k P V q') : q = q' := by
  rw [← trivSqZeroExtTensor_eq_add V q, ← trivSqZeroExtTensor_eq_add V q', h₁, h₂]

omit [Module kᵐᵒᵖ V] [IsCentralScalar k V] in
/-- The second coordinate maps `k[V] ⊗ P_d` into the image of `P_d ⊗ V`. -/
theorem trivSqZeroExtTensorSnd_mem_range (d : ℕ) {q : TrivSqZeroExt k V ⊗[k] P}
    (hq : q ∈ LinearMap.range
      (TensorProduct.map (LinearMap.id : TrivSqZeroExt k V →ₗ[k] TrivSqZeroExt k V)
        (grading d).subtype)) :
    trivSqZeroExtTensorSnd k P V q ∈
      LinearMap.range (TensorProduct.map (grading d).subtype (LinearMap.id : V →ₗ[k] V)) := by
  obtain ⟨z, rfl⟩ := hq
  induction z using TensorProduct.inductionOn with
  | tmul r x => exact ⟨x ⊗ₜ r.snd, rfl⟩
  | add a b ha hb =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

variable {V} {W : Type w} [AddCommGroup W] [Module k W] [Module kᵐᵒᵖ W] [IsCentralScalar k W]

variable (P) in
/-- **The map of trivial deformations** `k[V] ⊗ P → k[W] ⊗ P` induced by `f : V → W`. -/
def trivSqZeroExtTensorMap (f : V →ₗ[k] W) :
    TrivSqZeroExt k V ⊗[k] P →ₐ[k] TrivSqZeroExt k W ⊗[k] P :=
  Algebra.TensorProduct.map (TrivSqZeroExt.map f) (AlgHom.id k P)

/-- The map of trivial deformations sends `r ⊗ p` to `TrivSqZeroExt.map f r ⊗ p`. -/
@[simp]
theorem trivSqZeroExtTensorMap_tmul (f : V →ₗ[k] W) (r : TrivSqZeroExt k V) (p : P) :
    trivSqZeroExtTensorMap P f (r ⊗ₜ p) = TrivSqZeroExt.map f r ⊗ₜ p := rfl

/-- The second coordinate is natural: `(β q)₂ = (P ⊗ f) q₂`. -/
theorem trivSqZeroExtTensorSnd_trivSqZeroExtTensorMap (f : V →ₗ[k] W)
    (q : TrivSqZeroExt k V ⊗[k] P) :
    trivSqZeroExtTensorSnd k P W (trivSqZeroExtTensorMap P f q) =
      f.lTensor P (trivSqZeroExtTensorSnd k P V q) := by
  induction q using TensorProduct.inductionOn with
  | tmul r p => simp
  | add a b ha hb => simp only [map_add, ha, hb]

end TrivialDeformation

/-! ### Automorphisms of the trivial deformation as derivations -/

section DerivationOfAlgHom

variable (V : FGModuleCat.{w} k) [Module kᵐᵒᵖ V] [IsCentralScalar k V]

/-- A map reducing to the identity on `1 ⊗ x` has first coordinate `x` there. -/
theorem trivSqZeroExtTensorFst_of_reduction
    {σ : TrivSqZeroExt k V ⊗[k] P →ₐ[TrivSqZeroExt k V] TrivSqZeroExt k V ⊗[k] P}
    (hred : ∀ x : P, trivSqZeroExtTensorReduction k P V (σ (1 ⊗ₜ x)) = 1 ⊗ₜ x) (x : P) :
    trivSqZeroExtTensorFst k P V (σ (1 ⊗ₜ x)) = x := by
  simp [trivSqZeroExtTensorFst, hred]

/-- **The derivation of an automorphism of the trivial deformation.** For a `k[V]`-algebra
map `σ` of `k[V] ⊗ P` which sends `1 ⊗ x` into `k[V] ⊗ P_d` for `x ∈ P_d` (`hgr`) and reduces
to the identity (`hred`), this is the degree-preserving derivation `x ↦ σ (1 ⊗ x) - 1 ⊗ x`,
read in the kernel `P ⊗ V` of the reduction through `trivSqZeroExtTensorSnd`. -/
def derivationOfAlgHom
    (σ : TrivSqZeroExt k V ⊗[k] P →ₐ[TrivSqZeroExt k V] TrivSqZeroExt k V ⊗[k] P)
    (hgr : ∀ d x, x ∈ grading d → σ (1 ⊗ₜ x) ∈ LinearMap.range
      (TensorProduct.map (LinearMap.id : TrivSqZeroExt k V →ₗ[k] TrivSqZeroExt k V)
        (grading d).subtype))
    (hred : ∀ x : P, trivSqZeroExtTensorReduction k P V (σ (1 ⊗ₜ x)) = 1 ⊗ₜ x) :
    (gradedDerivationFunctor grading).obj V :=
  (⟨Derivation.mk' (trivSqZeroExtTensorSnd k P V ∘ₗ (σ.restrictScalars k).toLinearMap ∘ₗ
      (Algebra.TensorProduct.includeRight : P →ₐ[k] TrivSqZeroExt k V ⊗[k] P).toLinearMap)
      (fun x y => by
        have h : (1 : TrivSqZeroExt k V) ⊗ₜ[k] (x * y) = (1 ⊗ₜ x) * (1 ⊗ₜ y) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars',
          Algebra.TensorProduct.includeRight_apply]
        rw [h, map_mul, trivSqZeroExtTensorSnd_mul, trivSqZeroExtTensorFst_of_reduction V hred,
          trivSqZeroExtTensorFst_of_reduction V hred]),
    fun d x hx => trivSqZeroExtTensorSnd_mem_range grading V d (hgr d x hx)⟩ :
      gradedDerivations grading V)

/-- The derivation of `σ` sends `x` to the second coordinate of `σ (1 ⊗ x)`. -/
@[simp]
theorem derivationOfAlgHom_apply
    (σ : TrivSqZeroExt k V ⊗[k] P →ₐ[TrivSqZeroExt k V] TrivSqZeroExt k V ⊗[k] P)
    (hgr : ∀ d x, x ∈ grading d → σ (1 ⊗ₜ x) ∈ LinearMap.range
      (TensorProduct.map (LinearMap.id : TrivSqZeroExt k V →ₗ[k] TrivSqZeroExt k V)
        (grading d).subtype))
    (hred : ∀ x : P, trivSqZeroExtTensorReduction k P V (σ (1 ⊗ₜ x)) = 1 ⊗ₜ x) (x : P) :
    (derivationOfAlgHom grading V σ hgr hred : gradedDerivations grading V).1 x =
      trivSqZeroExtTensorSnd k P V (σ (1 ⊗ₜ x)) := rfl

/-- **An automorphism of the trivial deformation is determined by its derivation.** A
`k[V]`-algebra map of `k[V] ⊗ P` is determined by the values `σ (1 ⊗ x)`, and each of those is
determined by its two coordinates: the first is `x` by the reduction hypothesis, the second is
the value of the derivation. -/
theorem derivationOfAlgHom_injective
    {σ τ : TrivSqZeroExt k V ⊗[k] P →ₐ[TrivSqZeroExt k V] TrivSqZeroExt k V ⊗[k] P}
    {hσgr : ∀ d x, x ∈ grading d → σ (1 ⊗ₜ x) ∈ LinearMap.range
      (TensorProduct.map (LinearMap.id : TrivSqZeroExt k V →ₗ[k] TrivSqZeroExt k V)
        (grading d).subtype)}
    {hσred : ∀ x : P, trivSqZeroExtTensorReduction k P V (σ (1 ⊗ₜ x)) = 1 ⊗ₜ x}
    {hτgr : ∀ d x, x ∈ grading d → τ (1 ⊗ₜ x) ∈ LinearMap.range
      (TensorProduct.map (LinearMap.id : TrivSqZeroExt k V →ₗ[k] TrivSqZeroExt k V)
        (grading d).subtype)}
    {hτred : ∀ x : P, trivSqZeroExtTensorReduction k P V (τ (1 ⊗ₜ x)) = 1 ⊗ₜ x}
    (h : derivationOfAlgHom grading V σ hσgr hσred = derivationOfAlgHom grading V τ hτgr hτred) :
    σ = τ := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · refine AlgHom.ext fun x => ?_
    have h₂ : trivSqZeroExtTensorSnd k P V (σ (1 ⊗ₜ x)) =
        trivSqZeroExtTensorSnd k P V (τ (1 ⊗ₜ x)) :=
      congrArg (fun D : gradedDerivations grading V => D.1 x) h
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars',
      Algebra.TensorProduct.includeRight_apply]
    exact trivSqZeroExtTensor_ext V
      ((trivSqZeroExtTensorFst_of_reduction V hσred x).trans
        (trivSqZeroExtTensorFst_of_reduction V hτred x).symm) h₂

/-- **The identity of the trivial deformation has derivation zero.** -/
theorem derivationOfAlgHom_id
    (hgr : ∀ d x, x ∈ grading d →
      AlgHom.id (TrivSqZeroExt k V) (TrivSqZeroExt k V ⊗[k] P) (1 ⊗ₜ x) ∈ LinearMap.range
        (TensorProduct.map (LinearMap.id : TrivSqZeroExt k V →ₗ[k] TrivSqZeroExt k V)
          (grading d).subtype))
    (hred : ∀ x : P, trivSqZeroExtTensorReduction k P V
      (AlgHom.id (TrivSqZeroExt k V) (TrivSqZeroExt k V ⊗[k] P) (1 ⊗ₜ x)) = 1 ⊗ₜ x) :
    derivationOfAlgHom grading V (AlgHom.id _ _) hgr hred = 0 := by
  refine Subtype.ext (Derivation.ext fun x => ?_)
  change trivSqZeroExtTensorSnd k P V (1 ⊗ₜ x) = 0
  simp

/-- **Naturality of the derivation of an automorphism.** If `f : V → W` and automorphisms
`σ_V`, `σ_W` of the trivial deformations over `k[V]` and `k[W]` commute with the induced map
`β : k[V] ⊗ P → k[W] ⊗ P`, then the derivation of `σ_W` is the pushforward along `f` of the
derivation of `σ_V`. -/
theorem derivationOfAlgHom_naturality {V W : FGModuleCat.{w} k} [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] [Module kᵐᵒᵖ W] [IsCentralScalar k W] (f : V ⟶ W)
    (σV : TrivSqZeroExt k V ⊗[k] P →ₐ[TrivSqZeroExt k V] TrivSqZeroExt k V ⊗[k] P)
    (hVgr : ∀ d x, x ∈ grading d → σV (1 ⊗ₜ x) ∈ LinearMap.range
      (TensorProduct.map (LinearMap.id : TrivSqZeroExt k V →ₗ[k] TrivSqZeroExt k V)
        (grading d).subtype))
    (hVred : ∀ x : P, trivSqZeroExtTensorReduction k P V (σV (1 ⊗ₜ x)) = 1 ⊗ₜ x)
    (σW : TrivSqZeroExt k W ⊗[k] P →ₐ[TrivSqZeroExt k W] TrivSqZeroExt k W ⊗[k] P)
    (hWgr : ∀ d x, x ∈ grading d → σW (1 ⊗ₜ x) ∈ LinearMap.range
      (TensorProduct.map (LinearMap.id : TrivSqZeroExt k W →ₗ[k] TrivSqZeroExt k W)
        (grading d).subtype))
    (hWred : ∀ x : P, trivSqZeroExtTensorReduction k P W (σW (1 ⊗ₜ x)) = 1 ⊗ₜ x)
    (hcomm : ∀ q, trivSqZeroExtTensorMap P f.hom.hom (σV q) =
      σW (trivSqZeroExtTensorMap P f.hom.hom q)) :
    derivationOfAlgHom grading W σW hWgr hWred =
      ((gradedDerivationFunctor grading).map f).hom
        (derivationOfAlgHom grading V σV hVgr hVred) := by
  refine Subtype.ext (Derivation.ext fun x => ?_)
  change trivSqZeroExtTensorSnd k P W (σW (1 ⊗ₜ x)) =
    f.hom.hom.lTensor P (trivSqZeroExtTensorSnd k P V (σV (1 ⊗ₜ x)))
  rw [← trivSqZeroExtTensorSnd_trivSqZeroExtTensorMap, hcomm, trivSqZeroExtTensorMap_tmul, map_one]

end DerivationOfAlgHom

end GradedAlgebra

end
