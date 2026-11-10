module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexedUniversalProperty

/-!
# Reindexing the variables of a set-indexed divided power polynomial algebra

A map `σ : V → W` of index types induces a divided power morphism
`A⟨x_v : v ∈ V⟩ → A⟨x_w : w ∈ W⟩` sending `x_v` to `x_{σ v}`, and that morphism is an
isomorphism of divided power rings when `σ` is a bijection.

The library already has `DividedPowerAlgebra.map` for the underlying algebra map, but nothing
says that map is compatible with the divided powers of
`DividedPowers.setIndexedDividedPowerPolynomialDividedPowers`: those are assembled from the
finite-variable stages, and compatibility is not visible from the formula for the map.  So the
morphism is built here from the universal property
`DividedPowers.existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial` instead, which
produces a `DividedPowers.DPMorphism` by construction, and the uniqueness half of that same
universal property is what gives the functoriality identities — and, for a bijection, the
inverse.

## Main definitions

* `DividedPowers.setIndexedDividedPowerPolynomialReindex` — the divided power morphism
  `A⟨x_v⟩ → A⟨x_w⟩` along `σ : V → W`.
* `DividedPowers.setIndexedDividedPowerPolynomialReindexAlgHom` — the same map as an
  `A`-algebra homomorphism.
* `DividedPowers.setIndexedDividedPowerPolynomialReindexEquiv` — for `σ : V ≃ W`, the induced
  ring isomorphism, a divided power morphism in both directions.

## Main results

* `DividedPowers.setIndexedDividedPowerPolynomialReindex_variable` — it sends `x_v` to
  `x_{σ v}`.
* `DividedPowers.setIndexedDividedPowerPolynomialReindex_algebraMap` — it fixes the
  coefficients.
* `DividedPowers.setIndexedDividedPowerPolynomialReindex_id` and `..._comp` — functoriality.
* `DividedPowers.setIndexedDividedPowerPolynomialReindexEquiv_isDPMorphism` and
  `..._symm_isDPMorphism` — **both directions of the isomorphism are divided power
  morphisms**, which is what carries it through the divided power differentials.

## References

* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
-/

@[expose] public section

namespace DividedPowers

universe u v w x

variable (A : DividedPowerRing.{u})

section Reindex

variable {V : Type v} {W : Type w}

/-- **The divided power morphism `A⟨x_v : v ∈ V⟩ → A⟨x_w : w ∈ W⟩` reindexing the variables
along `σ : V → W`.**  It is the morphism produced by the universal property of the source for
the coefficient morphism of the target and the images `x_v ↦ x_{σ v}`, the variables of the
target lying in its divided power ideal by
`DividedPowers.variable_mem_polynomialIdeal`. -/
public noncomputable def setIndexedDividedPowerPolynomialReindex (σ : V → W) :
    _root_.DividedPowers.DPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers A V)
      (setIndexedDividedPowerPolynomialDividedPowers A W) :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial A V
    (setIndexedDividedPowerPolynomialDividedPowerRing A W)
    (setIndexedDividedPowerPolynomialCoefficientDPMorphism A W)
    fun v ↦ ⟨dividedPowerPolynomialVariable A (σ v),
      variable_mem_polynomialIdeal A (σ v)⟩).choose

/-- The reindexing morphism restricted to the coefficients is the coefficient morphism of the
target: the two divided power morphisms out of `A` agree. -/
public theorem setIndexedDividedPowerPolynomialReindex_comp_coefficient (σ : V → W) :
    (setIndexedDividedPowerPolynomialReindex A σ).comp
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism A V) =
      setIndexedDividedPowerPolynomialCoefficientDPMorphism A W :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial A V
    (setIndexedDividedPowerPolynomialDividedPowerRing A W)
    (setIndexedDividedPowerPolynomialCoefficientDPMorphism A W)
    fun v ↦ ⟨dividedPowerPolynomialVariable A (σ v),
      variable_mem_polynomialIdeal A (σ v)⟩).choose_spec.1.1

/-- **The reindexing morphism sends the variable `x_v` to the variable `x_{σ v}`.** -/
public theorem setIndexedDividedPowerPolynomialReindex_variable (σ : V → W) (v : V) :
    setIndexedDividedPowerPolynomialReindex A σ (dividedPowerPolynomialVariable A v) =
      dividedPowerPolynomialVariable A (σ v) :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial A V
    (setIndexedDividedPowerPolynomialDividedPowerRing A W)
    (setIndexedDividedPowerPolynomialCoefficientDPMorphism A W)
    fun v ↦ ⟨dividedPowerPolynomialVariable A (σ v),
      variable_mem_polynomialIdeal A (σ v)⟩).choose_spec.1.2 v

/-- **The reindexing morphism fixes the coefficients**, read on elements. -/
public theorem setIndexedDividedPowerPolynomialReindex_algebraMap (σ : V → W) (a : A) :
    setIndexedDividedPowerPolynomialReindex A σ
        (algebraMap A (setIndexedDividedPowerPolynomialAlgebra A V) a) =
      algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W) a :=
  congrArg (fun q : _root_.DividedPowers.DPMorphism A.dividedPowers
      (setIndexedDividedPowerPolynomialDividedPowers A W) ↦ q.toRingHom a)
    (setIndexedDividedPowerPolynomialReindex_comp_coefficient A σ)

/-- **The reindexing morphism is the only divided power morphism fixing the coefficients and
sending each variable to the variable of its image.** -/
public theorem setIndexedDividedPowerPolynomialReindex_unique (σ : V → W)
    (φ : _root_.DividedPowers.DPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers A V)
      (setIndexedDividedPowerPolynomialDividedPowers A W))
    (hcoeff : φ.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism A V) =
      setIndexedDividedPowerPolynomialCoefficientDPMorphism A W)
    (hvar : ∀ v : V, φ (dividedPowerPolynomialVariable A v) =
      dividedPowerPolynomialVariable A (σ v)) :
    φ = setIndexedDividedPowerPolynomialReindex A σ :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial A V
    (setIndexedDividedPowerPolynomialDividedPowerRing A W)
    (setIndexedDividedPowerPolynomialCoefficientDPMorphism A W)
    fun v ↦ ⟨dividedPowerPolynomialVariable A (σ v),
      variable_mem_polynomialIdeal A (σ v)⟩).choose_spec.2 φ ⟨hcoeff, hvar⟩

/-- Reindexing along the identity is the identity. -/
public theorem setIndexedDividedPowerPolynomialReindex_id :
    setIndexedDividedPowerPolynomialReindex A (id : V → V) =
      _root_.DividedPowers.DPMorphism.id
        (setIndexedDividedPowerPolynomialDividedPowers A V) :=
  (setIndexedDividedPowerPolynomialReindex_unique A id _ (by ext; rfl) fun _ ↦ rfl).symm

/-- Reindexing along a composite is the composite of the reindexings. -/
public theorem setIndexedDividedPowerPolynomialReindex_comp {X : Type x}
    (σ : V → W) (τ : W → X) :
    setIndexedDividedPowerPolynomialReindex A (τ ∘ σ) =
      (setIndexedDividedPowerPolynomialReindex A τ).comp
        (setIndexedDividedPowerPolynomialReindex A σ) :=
  (setIndexedDividedPowerPolynomialReindex_unique A (τ ∘ σ) _
    (by
      ext a
      change setIndexedDividedPowerPolynomialReindex A τ
          (setIndexedDividedPowerPolynomialReindex A σ
            (algebraMap A (setIndexedDividedPowerPolynomialAlgebra A V) a)) =
        algebraMap A (setIndexedDividedPowerPolynomialAlgebra A X) a
      rw [setIndexedDividedPowerPolynomialReindex_algebraMap,
        setIndexedDividedPowerPolynomialReindex_algebraMap])
    fun v ↦ by
      change setIndexedDividedPowerPolynomialReindex A τ
        (setIndexedDividedPowerPolynomialReindex A σ
          (dividedPowerPolynomialVariable A v)) = _
      rw [setIndexedDividedPowerPolynomialReindex_variable,
        setIndexedDividedPowerPolynomialReindex_variable]
      rfl).symm

/-- The reindexing morphism as an `A`-algebra homomorphism. -/
public noncomputable def setIndexedDividedPowerPolynomialReindexAlgHom (σ : V → W) :
    setIndexedDividedPowerPolynomialAlgebra A V →ₐ[A]
      setIndexedDividedPowerPolynomialAlgebra A W where
  __ := (setIndexedDividedPowerPolynomialReindex A σ).toRingHom
  commutes' := setIndexedDividedPowerPolynomialReindex_algebraMap A σ

/-- The reindexing algebra homomorphism agrees pointwise with the reindexing morphism. -/
@[simp] public theorem setIndexedDividedPowerPolynomialReindexAlgHom_apply (σ : V → W)
    (z : setIndexedDividedPowerPolynomialAlgebra A V) :
    setIndexedDividedPowerPolynomialReindexAlgHom A σ z =
      setIndexedDividedPowerPolynomialReindex A σ z := rfl

/-- The algebra homomorphism underlying the reindexing morphism is a divided power morphism. -/
public theorem setIndexedDividedPowerPolynomialReindexAlgHom_isDPMorphism (σ : V → W) :
    _root_.DividedPowers.IsDPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers A V)
      (setIndexedDividedPowerPolynomialDividedPowers A W)
      (setIndexedDividedPowerPolynomialReindexAlgHom A σ).toRingHom :=
  (setIndexedDividedPowerPolynomialReindex A σ).isDPMorphism

end Reindex

section ReindexEquiv

variable {V : Type v} {W : Type w}

/-- The two reindexings along the halves of a bijection compose to the identity. -/
public theorem setIndexedDividedPowerPolynomialReindex_symm_comp (σ : V ≃ W) :
    (setIndexedDividedPowerPolynomialReindex A σ.symm).comp
        (setIndexedDividedPowerPolynomialReindex A σ) =
      _root_.DividedPowers.DPMorphism.id
        (setIndexedDividedPowerPolynomialDividedPowers A V) := by
  rw [← setIndexedDividedPowerPolynomialReindex_comp,
    show (σ.symm : W → V) ∘ (σ : V → W) = id from funext σ.symm_apply_apply,
    setIndexedDividedPowerPolynomialReindex_id]

/-- The two reindexings along the halves of a bijection compose to the identity, in the other
order.  This is the previous lemma for `σ.symm`, whose own inverse is `σ` definitionally. -/
public theorem setIndexedDividedPowerPolynomialReindex_comp_symm (σ : V ≃ W) :
    (setIndexedDividedPowerPolynomialReindex A σ).comp
        (setIndexedDividedPowerPolynomialReindex A σ.symm) =
      _root_.DividedPowers.DPMorphism.id
        (setIndexedDividedPowerPolynomialDividedPowers A W) :=
  setIndexedDividedPowerPolynomialReindex_symm_comp A σ.symm

/-- **For a bijection of index types, the reindexing is a ring isomorphism.** -/
public noncomputable def setIndexedDividedPowerPolynomialReindexEquiv (σ : V ≃ W) :
    setIndexedDividedPowerPolynomialAlgebra A V ≃+*
      setIndexedDividedPowerPolynomialAlgebra A W :=
  RingEquiv.ofRingHom (setIndexedDividedPowerPolynomialReindex A σ).toRingHom
    (setIndexedDividedPowerPolynomialReindex A σ.symm).toRingHom
    (by
      refine RingHom.ext fun z ↦ ?_
      change ((setIndexedDividedPowerPolynomialReindex A σ).comp
        (setIndexedDividedPowerPolynomialReindex A σ.symm)) z = z
      rw [setIndexedDividedPowerPolynomialReindex_comp_symm]
      rfl)
    (by
      refine RingHom.ext fun z ↦ ?_
      change ((setIndexedDividedPowerPolynomialReindex A σ.symm).comp
        (setIndexedDividedPowerPolynomialReindex A σ)) z = z
      rw [setIndexedDividedPowerPolynomialReindex_symm_comp]
      rfl)

/-- The reindexing isomorphism agrees pointwise with the reindexing morphism. -/
@[simp] public theorem setIndexedDividedPowerPolynomialReindexEquiv_apply (σ : V ≃ W)
    (z : setIndexedDividedPowerPolynomialAlgebra A V) :
    setIndexedDividedPowerPolynomialReindexEquiv A σ z =
      setIndexedDividedPowerPolynomialReindex A σ z := rfl

/-- The inverse of the reindexing isomorphism along `σ` is the reindexing morphism along
`σ.symm`. -/
@[simp] public theorem setIndexedDividedPowerPolynomialReindexEquiv_symm_apply (σ : V ≃ W)
    (z : setIndexedDividedPowerPolynomialAlgebra A W) :
    (setIndexedDividedPowerPolynomialReindexEquiv A σ).symm z =
      setIndexedDividedPowerPolynomialReindex A σ.symm z := rfl

/-- **The reindexing isomorphism is a divided power morphism.** -/
public theorem setIndexedDividedPowerPolynomialReindexEquiv_isDPMorphism (σ : V ≃ W) :
    _root_.DividedPowers.IsDPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers A V)
      (setIndexedDividedPowerPolynomialDividedPowers A W)
      (setIndexedDividedPowerPolynomialReindexEquiv A σ).toRingHom :=
  (setIndexedDividedPowerPolynomialReindex A σ).isDPMorphism

/-- **The inverse of the reindexing isomorphism is a divided power morphism too**, so the
isomorphism is one of divided power rings and carries the divided power differentials along. -/
public theorem setIndexedDividedPowerPolynomialReindexEquiv_symm_isDPMorphism (σ : V ≃ W) :
    _root_.DividedPowers.IsDPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers A W)
      (setIndexedDividedPowerPolynomialDividedPowers A V)
      (setIndexedDividedPowerPolynomialReindexEquiv A σ).symm.toRingHom :=
  (setIndexedDividedPowerPolynomialReindex A σ.symm).isDPMorphism

/-- The reindexing isomorphism sends `x_v` to `x_{σ v}`. -/
public theorem setIndexedDividedPowerPolynomialReindexEquiv_variable (σ : V ≃ W) (v : V) :
    setIndexedDividedPowerPolynomialReindexEquiv A σ (dividedPowerPolynomialVariable A v) =
      dividedPowerPolynomialVariable A (σ v) :=
  setIndexedDividedPowerPolynomialReindex_variable A σ v

/-- The reindexing isomorphism fixes the coefficients. -/
public theorem setIndexedDividedPowerPolynomialReindexEquiv_algebraMap (σ : V ≃ W) (a : A) :
    setIndexedDividedPowerPolynomialReindexEquiv A σ
        (algebraMap A (setIndexedDividedPowerPolynomialAlgebra A V) a) =
      algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W) a :=
  setIndexedDividedPowerPolynomialReindex_algebraMap A σ a

end ReindexEquiv

end DividedPowers

end
