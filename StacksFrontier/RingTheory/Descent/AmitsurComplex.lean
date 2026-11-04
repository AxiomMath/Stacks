module

public import StacksFrontier.RingTheory.Descent.FaithfullyFlatModules

/-!
# Degree-one exactness of the Amitsur complex

Let `R → S` be a ring map and let `M` be an `R`-module. The *Amitsur complex* (or descent complex,
or Čech complex) of `M` along `R → S` is

`0 → M → S ⊗[R] M → S ⊗[R] S ⊗[R] M → S ⊗[R] S ⊗[R] S ⊗[R] M → ⋯`,

where the differential in degree `n` is the alternating sum of the `n + 2` maps inserting a `1`
into one of the `S`-slots. This file constructs the complex up to degree two and proves that for
`S` faithfully flat over `R` it is exact in degree one: every `1`-cocycle is a coboundary.

The proof is by an explicit contracting homotopy. After base changing to `S` the complex becomes
split: the map multiplying together the two leading tensor factors is a homotopy between the
identity and zero, with no flatness hypothesis whatsoever. Faithful flatness enters only through
`Module.FaithfullyFlat.lTensor_reflects_exact`, which transports the resulting exactness back down
to `R`. The same homotopy argument, with the leading tensor factor absorbed into the coefficient
module instead, shows that the complex of an `S`-module is split exact over any base.

Exactness in degree zero is `Module.Descent.exact_mk_one`, restated here as
`Module.Descent.exact_amitsur_degree_zero` so that both degrees are available in the same
notation.

## Main definitions

* `Module.Descent.amitsurAug`: the augmentation `M →ₗ[R] S ⊗[R] M`, `m ↦ 1 ⊗ₜ m`.
* `Module.Descent.amitsurDiff₀`: the differential `S ⊗[R] M →ₗ[R] S ⊗[R] (S ⊗[R] M)` from degree
  zero to degree one.
* `Module.Descent.amitsurDiff₁`: the differential
  `S ⊗[R] (S ⊗[R] M) →ₗ[R] S ⊗[R] (S ⊗[R] (S ⊗[R] M))` from degree one to degree two.
* `Module.Descent.amitsurFold`: the multiplication of the two leading tensor factors, which is the
  contracting homotopy of the base-changed complex.
* `Module.Descent.toCocycleOne`: the degree-one differential viewed as a map into the module of
  `1`-cocycles.

## Main results

* `Module.Descent.amitsurDiff₁_comp_amitsurDiff₀`: the Amitsur complex is a complex.
* `Module.Descent.lTensor_amitsurFold_homotopy`: the contracting homotopy of the base-changed
  complex in degree one.
* `Module.Descent.exact_lTensor_amitsurDiff`: the base-changed Amitsur complex is exact in degree
  one, with no flatness hypothesis.
* `Module.Descent.exact_amitsur_degree_one_of_isScalarTower`: the Amitsur complex of an `S`-module
  is exact in degree one, with no flatness hypothesis.
* `Module.Descent.exact_amitsur_degree_one`: **exactness of the Amitsur complex in degree one**
  for `S` faithfully flat over `R`.
* `Module.Descent.exists_amitsurDiff₀_eq`: the same statement in element form, every `1`-cocycle is
  a coboundary.
* `Module.Descent.surjective_toCocycleOne`: the same statement as the surjectivity of the map from
  degree-zero cochains onto the `1`-cocycles, i.e. the vanishing of the first cohomology of the
  Amitsur complex.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open TensorProduct

namespace Module.Descent

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The augmentation `M →ₗ[R] S ⊗[R] M`, `m ↦ 1 ⊗ₜ m`, of the Amitsur complex of `M` along
`R → S`. -/
def amitsurAug : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1

/-- `Module.Descent.amitsurAug` on an element. -/
@[simp]
lemma amitsurAug_apply (m : M) : amitsurAug R S M m = (1 : S) ⊗ₜ[R] m := rfl

/-- The degree-zero differential of the Amitsur complex of `M` along `R → S`, the difference of
the two maps `S ⊗[R] M → S ⊗[R] (S ⊗[R] M)` inserting a `1`. -/
noncomputable def amitsurDiff₀ : S ⊗[R] M →ₗ[R] S ⊗[R] (S ⊗[R] M) :=
  LinearMap.lTensor S (TensorProduct.mk R S M 1) - TensorProduct.mk R S (S ⊗[R] M) 1

/-- `Module.Descent.amitsurDiff₀` on a pure tensor. -/
@[simp]
lemma amitsurDiff₀_tmul (s : S) (m : M) :
    amitsurDiff₀ R S M (s ⊗ₜ[R] m) =
      s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] m) - (1 : S) ⊗ₜ[R] (s ⊗ₜ[R] m) := rfl

/-- The degree-one differential of the Amitsur complex of `M` along `R → S`, the alternating sum
of the three maps `S ⊗[R] (S ⊗[R] M) → S ⊗[R] (S ⊗[R] (S ⊗[R] M))` inserting a `1`. -/
noncomputable def amitsurDiff₁ :
    S ⊗[R] (S ⊗[R] M) →ₗ[R] S ⊗[R] (S ⊗[R] (S ⊗[R] M)) :=
  TensorProduct.mk R S (S ⊗[R] (S ⊗[R] M)) 1 -
      LinearMap.lTensor S (TensorProduct.mk R S (S ⊗[R] M) 1) +
    LinearMap.lTensor S (LinearMap.lTensor S (TensorProduct.mk R S M 1))

/-- `Module.Descent.amitsurDiff₁` on a pure tensor. -/
@[simp]
lemma amitsurDiff₁_tmul (s t : S) (m : M) :
    amitsurDiff₁ R S M (s ⊗ₜ[R] (t ⊗ₜ[R] m)) =
      (1 : S) ⊗ₜ[R] (s ⊗ₜ[R] (t ⊗ₜ[R] m)) - s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (t ⊗ₜ[R] m)) +
        s ⊗ₜ[R] (t ⊗ₜ[R] ((1 : S) ⊗ₜ[R] m)) := rfl

/-- The Amitsur complex is a complex: the composite of its degree-zero and degree-one
differentials vanishes. -/
theorem amitsurDiff₁_comp_amitsurDiff₀ :
    amitsurDiff₁ R S M ∘ₗ amitsurDiff₀ R S M = 0 := by
  ext s m
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply, amitsurDiff₀_tmul,
    map_sub, amitsurDiff₁_tmul, LinearMap.zero_apply]
  abel

/-- Exactness of the Amitsur complex in degree zero, for `S` faithfully flat over `R`: the kernel
of the degree-zero differential is the image of the augmentation. -/
theorem exact_amitsur_degree_zero [Module.FaithfullyFlat R S] :
    Function.Exact (amitsurAug R S M) (amitsurDiff₀ R S M) :=
  exact_mk_one R S M

section Fold

variable (P : Type*) [AddCommGroup P] [Module R P]

/-- Multiplication of the two leading tensor factors, `s ⊗ₜ t ⊗ₜ p ↦ (s * t) ⊗ₜ p`. Applied in
degrees one and two it is the contracting homotopy exhibiting the Amitsur complex of `M` as split
after base change to `S`. -/
noncomputable def amitsurFold : S ⊗[R] (S ⊗[R] P) →ₗ[R] S ⊗[R] P :=
  (counit R S (S ⊗[R] P)).restrictScalars R

/-- `Module.Descent.amitsurFold` on a pure tensor. -/
@[simp]
lemma amitsurFold_tmul (s t : S) (p : P) :
    amitsurFold R S P (s ⊗ₜ[R] (t ⊗ₜ[R] p)) = (s * t) ⊗ₜ[R] p := by
  rw [amitsurFold, LinearMap.restrictScalars_apply, counit_tmul, TensorProduct.smul_tmul',
    smul_eq_mul]

end Fold

/-- The contracting homotopy of the base-changed Amitsur complex in degree one: multiplying the
two leading tensor factors is a homotopy between the identity of `S ⊗[R] (S ⊗[R] (S ⊗[R] M))` and
zero. No flatness hypothesis is needed. -/
theorem lTensor_amitsurFold_homotopy :
    amitsurFold R S (S ⊗[R] (S ⊗[R] M)) ∘ₗ LinearMap.lTensor S (amitsurDiff₁ R S M) -
        LinearMap.lTensor S (amitsurDiff₀ R S M) ∘ₗ amitsurFold R S (S ⊗[R] M) =
      LinearMap.id := by
  ext t s₀ s₁ m
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply,
    LinearMap.lTensor_tmul, amitsurDiff₁_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_add,
    map_sub, map_add, amitsurFold_tmul, mul_one, amitsurDiff₀_tmul, LinearMap.id_coe, id_eq]
  abel

/-- **The base-changed Amitsur complex is exact in degree one**, with no flatness hypothesis: after
applying `S ⊗[R] -` the complex is split, by the homotopy of
`Module.Descent.lTensor_amitsurFold_homotopy`. -/
theorem exact_lTensor_amitsurDiff :
    Function.Exact (LinearMap.lTensor S (amitsurDiff₀ R S M))
      (LinearMap.lTensor S (amitsurDiff₁ R S M)) := by
  intro x
  constructor
  · intro hx
    refine ⟨-amitsurFold R S (S ⊗[R] M) x, ?_⟩
    simpa only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq, hx, map_zero, zero_sub, map_neg] using congr($(lTensor_amitsurFold_homotopy R S M) x)
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, amitsurDiff₁_comp_amitsurDiff₀,
      LinearMap.lTensor_zero, LinearMap.zero_apply]

section Tower

variable (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The contracting homotopy of the Amitsur complex of an `S`-module in degree one: absorbing the
trailing tensor factor into the coefficient module is a homotopy between the identity of
`S ⊗[R] (S ⊗[R] N)` and zero. No flatness hypothesis is needed. -/
theorem counit_amitsurDiff_homotopy :
    amitsurDiff₀ R S N ∘ₗ LinearMap.lTensor S ((counit R S N).restrictScalars R) +
        LinearMap.lTensor S
          (LinearMap.lTensor S ((counit R S N).restrictScalars R)) ∘ₗ amitsurDiff₁ R S N =
      LinearMap.id := by
  ext s t n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
    LinearMap.lTensor_tmul, counit_tmul, amitsurDiff₀_tmul, amitsurDiff₁_tmul, map_sub, map_add,
    one_smul, LinearMap.id_coe, id_eq]
  abel

/-- **The Amitsur complex of an `S`-module is exact in degree one**, with no flatness hypothesis:
for an `S`-module `N` the complex `N → S ⊗[R] N → S ⊗[R] (S ⊗[R] N) → ⋯` is split, by the homotopy
of `Module.Descent.counit_amitsurDiff_homotopy`. -/
theorem exact_amitsur_degree_one_of_isScalarTower :
    Function.Exact (amitsurDiff₀ R S N) (amitsurDiff₁ R S N) := by
  intro x
  constructor
  · intro hx
    refine ⟨LinearMap.lTensor S ((counit R S N).restrictScalars R) x, ?_⟩
    simpa only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq, hx, map_zero, add_zero] using congr($(counit_amitsurDiff_homotopy R S N) x)
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, amitsurDiff₁_comp_amitsurDiff₀, LinearMap.zero_apply]

end Tower

section FaithfullyFlat

variable [Module.FaithfullyFlat R S]

/-- **Exactness of the Amitsur complex in degree one.** For `S` faithfully flat over `R` and `M`
any `R`-module, the kernel of the degree-one differential
`S ⊗[R] (S ⊗[R] M) → S ⊗[R] (S ⊗[R] (S ⊗[R] M))` of the Amitsur complex of `M` along `R → S` is
the image of its degree-zero differential `S ⊗[R] M → S ⊗[R] (S ⊗[R] M)`.

Over an affine base this is the vanishing of the first Čech cohomology of a quasi-coherent module
along a faithfully flat covering. -/
theorem exact_amitsur_degree_one :
    Function.Exact (amitsurDiff₀ R S M) (amitsurDiff₁ R S M) :=
  Module.FaithfullyFlat.lTensor_reflects_exact R S _ _ (exact_lTensor_amitsurDiff R S M)

/-- **Every `1`-cocycle of the Amitsur complex is a coboundary**, the element form of
`Module.Descent.exact_amitsur_degree_one`. -/
theorem exists_amitsurDiff₀_eq {x : S ⊗[R] (S ⊗[R] M)} (hx : amitsurDiff₁ R S M x = 0) :
    ∃ y : S ⊗[R] M, amitsurDiff₀ R S M y = x :=
  (exact_amitsur_degree_one R S M x).1 hx

end FaithfullyFlat

/-- The degree-zero differential of the Amitsur complex viewed as a map onto the module of
`1`-cocycles. -/
noncomputable def toCocycleOne :
    S ⊗[R] M →ₗ[R] LinearMap.ker (amitsurDiff₁ R S M) :=
  LinearMap.codRestrict _ (amitsurDiff₀ R S M) fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, amitsurDiff₁_comp_amitsurDiff₀,
      LinearMap.zero_apply]

/-- `Module.Descent.toCocycleOne` followed by the inclusion of the cocycles. -/
@[simp]
lemma coe_toCocycleOne (x : S ⊗[R] M) :
    (toCocycleOne R S M x : S ⊗[R] (S ⊗[R] M)) = amitsurDiff₀ R S M x := rfl

/-- **Vanishing of the first cohomology of the Amitsur complex**, in the form that the map from
degree-zero cochains onto the `1`-cocycles is surjective. For `S` faithfully flat over `R` every
`1`-cocycle of the Amitsur complex of `M` along `R → S` is the coboundary of a section over `S`. -/
theorem surjective_toCocycleOne [Module.FaithfullyFlat R S] :
    Function.Surjective (toCocycleOne R S M) := fun x =>
  (exists_amitsurDiff₀_eq R S M x.2).imp fun _ hy => Subtype.ext hy

end Module.Descent
