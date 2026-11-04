module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsDPIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPolynomialDecomposition
public import StacksFrontier.AlgebraicGeometry.Crystalline.TensorPowerEnvelope

/-!
# The divided power forms of `D(n)` are the completed polynomial forms over the envelope

The double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of
[Stacks, Proposition 60.21.3, Tag 07LG] is compared, row by row, with the complex
`M ⊗̂_D Ω^*_D`, and the comparison rests on [Stacks, Lemma 60.17.5, Tag 07L2]: the ring `D(b)`
is the completed divided power polynomial algebra `D⟨ξ_i(j)⟩^∧` on the difference coordinates.
What the rows of the double complex are built from is not the ring but its **forms**, and the
statement the comparison needs is therefore that

`Ω^a_{D(b)} = Ω̂^a_{D_{P,γ}(J)⟨ξ_i(j)⟩}`,

the right hand side being
`Crystalline.DividedPowerPolynomial.completedPolynomialForms` — the family on which the
completed Poincaré lemma
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_completedPolynomialForms` of
[Stacks, Lemma 60.19.2, Tag 07LD] is proved.  This module proves that identification, and
proves it compatibly with the wedge product, with the de Rham differential and with the
universal differential.

## Which `B`

`Crystalline.DividedPowerPolynomial.completedPolynomialForms A B W p a` is the completion
along `(p) ⊆ B⟨x_w⟩` of the forms of the **uncompleted** divided power polynomial algebra
`B⟨x_w : w ∈ W⟩`, and `Crystalline.completedDividedPowerForms p A hJ a` is the completion along
`(p) ⊆ B` of the forms of the uncompleted `B`.  The two are therefore the *same* construction,
the second at the ring `B` and the first at the ring `B⟨x_w⟩`; and `Ω^a_{D(b)}` as the double
complex uses it — `Crystalline.CosimplicialDPAlgebra.forms`, hence
`Crystalline.envelopeForms` — is the second at the uncompleted divided power envelope
of `J(b)`.

So the `B` for which the identification holds, and the `B` taken here, is the **uncompleted**
divided power envelope `D_{P,γ}(J) = (polynomialDividedPowerEnvelope s f).object`, not its
`p`-adic completion `D`.  That is not a weakening: the `D` of
[Stacks, Lemma 60.19.2, Tag 07LD] as this library states it is
`Crystalline.completedDividedPowerRing p (B := B)`, the completion of whatever `B` is given, so
at `B = D_{P,γ}(J)` it is exactly the `D` of [Stacks, Tag 07J8] — the same `AdicCompletion`
along the same ideal; the Poincaré lemma carries no completeness hypothesis on `B`, and
`Crystalline.completedDividedPowerForms p A B.dividedPowers` at that `B` is exactly the
`Ω̂^*_D` the target complex `M ⊗̂_D Ω^*_D` is built from.  Taking `B` to be the completed envelope
instead would ask for the forms of a completed ring, which is a different and genuinely unproved
comparison — see the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedEnvelopeFactorizationForms.lean`.

## How

`Crystalline.tensorEnvelopeDPEquiv` identifies the uncompleted envelope of `J(b)` with
`D_{P,γ}(J)⟨ξ_i(j)⟩` as divided power rings over `A`, in both directions.  A divided power
morphism over `A` induces a comparison of completed forms respecting all three structures, by
`Crystalline.completedMapDifferentialForms` and its lemmas, and the two comparisons induced by
the two directions are mutually inverse by the functoriality
`Crystalline.completedMapDifferentialForms_eq_comp` and
`Crystalline.completedMapDifferentialForms_eq_self`.  No completion-level argument is needed:
the whole statement is the completion of one isomorphism of uncompleted divided power rings.

## Main definitions

* `Crystalline.envelopeVariableForms` — the right hand side `Ω̂^a_{D_{P,γ}(J)⟨ξ_i(j)⟩}`, with
  `Crystalline.envelopeVariableForms_eq` identifying it with
  `Crystalline.DividedPowerPolynomial.completedPolynomialForms`.
* `Crystalline.tensorEnvelopeFormsAlgHom` — the identification of
  `Crystalline.tensorEnvelopeDPEquiv` as an `A`-algebra homomorphism, with
  `Crystalline.tensorEnvelopeFormsSymmAlgHom` its inverse, and
  `..._isDPMorphism` for each saying it is a divided power morphism.
* `Crystalline.tensorEnvelopeFormsMap` and `Crystalline.tensorEnvelopeFormsSymmMap` — the two
  comparisons `Ω^a_{D(b)} → Ω̂^a_{D⟨ξ⟩}` and back, semilinear over those ring maps.
* `Crystalline.tensorEnvelopeFormsIso` — **the identification
  `Ω^*_{D(b)} ≅ Ω̂^*_{D_{P,γ}(J)⟨ξ_i(j)⟩}` of completed de Rham complexes**, as a
  `Crystalline.CompletedFormsDPIso`: an additive equivalence in each exterior degree together
  with its compatibility with the wedge product in both bidegrees, with the de Rham
  differential and with the universal differential.  Those five compatibilities are its fields
  `equiv`, `wedge`, `wedgeMul`, `deRham` and `differential`.
* `Crystalline.tensorEnvelopeFormsEquiv` — its degree-`a` component
  `Ω^a_{D(b)} ≃+ Ω̂^a_{D_{P,γ}(J)⟨ξ_i(j)⟩}`, with
  `Crystalline.tensorEnvelopeFormsEquiv_apply` and `..._symm_apply` identifying it with the two
  comparisons above.

## Main results

* `Crystalline.tensorEnvelopeFormsSymmMap_tensorEnvelopeFormsMap` and
  `Crystalline.tensorEnvelopeFormsMap_tensorEnvelopeFormsSymmMap` — the two comparisons are
  mutually inverse.
* `(Crystalline.tensorEnvelopeFormsIso s f n).wedge` and `...wedgeMul` — **the identification
  respects the wedge product**, in the bidegree the completed de Rham complex is built from and
  in a general bidegree.
* `(Crystalline.tensorEnvelopeFormsIso s f n).deRham` — **the identification respects the de
  Rham differential**, so it is an isomorphism of completed de Rham complexes.
* `(Crystalline.tensorEnvelopeFormsIso s f n).differential` — **the identification respects the
  universal differential** `d : D(b) → Ω^1_{D(b)}`, on the canonical image of the uncompleted
  envelope.

No tag attribute is placed.  [Stacks, Tag 07L2] is the statement about the rings, already
tagged on `Crystalline.exists_ringEquiv_pAdicCompletedDividedPowerPolynomial`; the statement
about the forms is a step inside the proof of [Stacks, Tag 07LG] and is not itself a tag.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L2](https://stacks.math.columbia.edu/tag/07L2)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open DividedPowers

universe u v w

namespace Crystalline

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-! ### The two families of forms -/

/-- The `A`-algebra structure on the **uncompleted** divided power envelope of `J`, given by its
structure map.  This is the `B` of
`Crystalline.DividedPowerPolynomial.completedPolynomialForms` below, and the structure map is
the only `A`-algebra structure the envelope has; it is the one under which
`Crystalline.tensorEnvelopeDPEquiv` is an `A`-algebra map, by
`Crystalline.tensorEnvelopeDPEquiv_structureMap`. -/
public noncomputable instance algebraEnvelopeObject :
    Algebra (s.A : Type u) (polynomialDividedPowerEnvelope s f).object :=
  (polynomialDividedPowerEnvelope s f).structureMap.toRingHom.toAlgebra

/-- The divided powers of the divided power polynomial algebra `D_{P,γ}(J)⟨ξ_i(j)⟩` on the
difference coordinates over the uncompleted divided power envelope of `J`. -/
public noncomputable abbrev envelopeVariableDividedPowers (n : ℕ) :
    DividedPowers (dividedPowerPolynomialIdeal
      (polynomialDividedPowerEnvelope s f).object.ideal (ι × Fin n)) :=
  setIndexedDividedPowerPolynomialDividedPowers
    (polynomialDividedPowerEnvelope s f).object (ι × Fin n)

/-- **The family `Ω̂^a_{D_{P,γ}(J)⟨ξ_i(j)⟩}`**: the `p`-adic completion of the divided power
forms of the divided power polynomial algebra on the difference coordinates over the
uncompleted divided power envelope of `J`.

It is spelled as `Crystalline.completedDividedPowerForms` of the divided powers of that
algebra, which is the spelling the comparison of forms along a divided power morphism produces;
`Crystalline.envelopeVariableForms_eq` says it *is*
`Crystalline.DividedPowerPolynomial.completedPolynomialForms` at
`B = (polynomialDividedPowerEnvelope s f).object` and `W = ι × Fin n`, the family the completed
Poincaré lemma of [Stacks, Lemma 60.19.2, Tag 07LD] is proved for. -/
public noncomputable abbrev envelopeVariableForms (n a : ℕ) :=
  completedDividedPowerForms s.p (s.A : Type u) (envelopeVariableDividedPowers s f n) a

/-- **The family above is the completed polynomial forms of [Stacks, Lemma 60.19.2, Tag 07LD].**

`Crystalline.DividedPowerPolynomial.completedPolynomialForms A B W p a` completes the forms of
`B⟨x_w : w ∈ W⟩` along `(p)` of that algebra, and `Crystalline.completedDividedPowerForms p A hJ
a` completes the forms of the ring of `hJ` along `(p)` of that ring; at
`hJ = Crystalline.envelopeVariableDividedPowers` the ring *is* `B⟨x_w⟩`, so the two are the same
type and the identification needs no proof.  It is recorded because it is what makes the
comparison below a comparison with the family the Poincaré lemma applies to. -/
public theorem envelopeVariableForms_eq (n a : ℕ) :
    envelopeVariableForms s f n a =
      DividedPowerPolynomial.completedPolynomialForms (s.A : Type u)
        (polynomialDividedPowerEnvelope s f).object (ι × Fin n) s.p a := rfl

/-! ### The identification of the rings as an `A`-algebra isomorphism -/

/-- **`Crystalline.tensorEnvelopeDPEquiv` as an `A`-algebra homomorphism.**  It commutes with
the two structure maps from `A` by `Crystalline.tensorEnvelopeDPEquiv_structureMap`, the
structure map of the target factoring through the coefficients of the divided power polynomial
algebra. -/
public noncomputable def tensorEnvelopeFormsAlgHom (n : ℕ) :
    (envelopeDPAlgebra s f).carrier n →ₐ[(s.A : Type u)]
      setIndexedDividedPowerPolynomialAlgebra
        (polynomialDividedPowerEnvelope s f).object (ι × Fin n) where
  __ := (tensorEnvelopeDPEquiv s f n).toRingHom
  commutes' a := (tensorEnvelopeDPEquiv_structureMap s f n a).trans
    (IsScalarTower.algebraMap_apply (s.A : Type u)
      ((polynomialDividedPowerEnvelope s f).object : Type (max u w))
      (setIndexedDividedPowerPolynomialAlgebra
        (polynomialDividedPowerEnvelope s f).object (ι × Fin n)) a).symm

/-- The inverse of `Crystalline.tensorEnvelopeFormsAlgHom`, as an `A`-algebra homomorphism. -/
public noncomputable def tensorEnvelopeFormsSymmAlgHom (n : ℕ) :
    setIndexedDividedPowerPolynomialAlgebra
        (polynomialDividedPowerEnvelope s f).object (ι × Fin n) →ₐ[(s.A : Type u)]
      (envelopeDPAlgebra s f).carrier n where
  __ := (tensorEnvelopeDPEquiv s f n).symm.toRingHom
  commutes' a := (tensorEnvelopeDPEquiv s f n).injective
    (((tensorEnvelopeDPEquiv s f n).apply_symm_apply _).trans
      ((tensorEnvelopeFormsAlgHom s f n).commutes a).symm)

/-- The `A`-algebra map is a divided power morphism. -/
public theorem tensorEnvelopeFormsAlgHom_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism ((envelopeDPAlgebra s f).dividedPowers n)
      (envelopeVariableDividedPowers s f n)
      (tensorEnvelopeFormsAlgHom s f n).toRingHom :=
  tensorEnvelopeDPEquiv_isDPMorphism s f n

/-- Its inverse is a divided power morphism as well. -/
public theorem tensorEnvelopeFormsSymmAlgHom_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism (envelopeVariableDividedPowers s f n)
      ((envelopeDPAlgebra s f).dividedPowers n)
      (tensorEnvelopeFormsSymmAlgHom s f n).toRingHom :=
  tensorEnvelopeDPEquiv_symm_isDPMorphism s f n

/-! ### The comparison of completed forms -/

/-- **The comparison `Ω^a_{D(b)} → Ω̂^a_{D_{P,γ}(J)⟨ξ_i(j)⟩}` of completed divided power
forms**, semilinear over the identification of the rings. -/
public noncomputable def tensorEnvelopeFormsMap (n a : ℕ) :
    envelopeForms s f a n →ₛₗ[(tensorEnvelopeFormsAlgHom s f n).toRingHom]
      envelopeVariableForms s f n a :=
  completedMapDifferentialForms s.p (s.A : Type u)
    ((envelopeDPAlgebra s f).dividedPowers n) (envelopeVariableDividedPowers s f n)
    (tensorEnvelopeFormsAlgHom s f n) (tensorEnvelopeFormsAlgHom_isDPMorphism s f n) a

/-- **The comparison in the other direction.** -/
public noncomputable def tensorEnvelopeFormsSymmMap (n a : ℕ) :
    envelopeVariableForms s f n a →ₛₗ[(tensorEnvelopeFormsSymmAlgHom s f n).toRingHom]
      envelopeForms s f a n :=
  completedMapDifferentialForms s.p (s.A : Type u)
    (envelopeVariableDividedPowers s f n) ((envelopeDPAlgebra s f).dividedPowers n)
    (tensorEnvelopeFormsSymmAlgHom s f n) (tensorEnvelopeFormsSymmAlgHom_isDPMorphism s f n) a

/-- The composite of the two `A`-algebra maps, in one order, is the identity. -/
public theorem tensorEnvelopeFormsSymmAlgHom_comp (n : ℕ) :
    AlgHom.id (s.A : Type u) ((envelopeDPAlgebra s f).carrier n) =
      (tensorEnvelopeFormsSymmAlgHom s f n).comp (tensorEnvelopeFormsAlgHom s f n) :=
  AlgHom.coe_ringHom_injective (RingHom.ext fun z ↦
    ((tensorEnvelopeDPEquiv s f n).symm_apply_apply z).symm)

/-- The composite of the two `A`-algebra maps, in the other order, is the identity. -/
public theorem tensorEnvelopeFormsAlgHom_comp (n : ℕ) :
    AlgHom.id (s.A : Type u) (setIndexedDividedPowerPolynomialAlgebra
        (polynomialDividedPowerEnvelope s f).object (ι × Fin n)) =
      (tensorEnvelopeFormsAlgHom s f n).comp (tensorEnvelopeFormsSymmAlgHom s f n) :=
  AlgHom.coe_ringHom_injective (RingHom.ext fun z ↦
    ((tensorEnvelopeDPEquiv s f n).apply_symm_apply z).symm)

/-- **The identification `Ω^*_{D(b)} ≅ Ω̂^*_{D_{P,γ}(J)⟨ξ_i(j)⟩}` of the completed divided power
de Rham complexes.**

The left hand side is `Crystalline.envelopeForms`, the bigraded family the double complex
`K^{a,b}` of [Stacks, Proposition 60.21.3, Tag 07LG] is built from, and the right hand side is
`Crystalline.envelopeVariableForms`, which by `Crystalline.envelopeVariableForms_eq` is the
family `Crystalline.DividedPowerPolynomial.completedPolynomialForms` on which the completed
Poincaré lemma of [Stacks, Lemma 60.19.2, Tag 07LD] is proved.  So this is the forms-level form
of [Stacks, Lemma 60.17.5, Tag 07L2].

It is `Crystalline.completedFormsDPIso` at the divided power isomorphism
`Crystalline.tensorEnvelopeDPEquiv`, so it is an additive equivalence in every exterior degree
together with its compatibility with the wedge product in both bidegrees, with the de Rham
differential and with the universal differential — the fields `equiv`, `wedge`, `wedgeMul`,
`deRham` and `differential` of `Crystalline.CompletedFormsDPIso`.  The equivalence is additive
and not linear: the two sides are modules over the two different rings, identified by the field
`algHom`, which is `Crystalline.tensorEnvelopeFormsAlgHom`. -/
public noncomputable def tensorEnvelopeFormsIso (n : ℕ) :
    CompletedFormsDPIso s.p (s.A : Type u) ((envelopeDPAlgebra s f).dividedPowers n)
      (envelopeVariableDividedPowers s f n) :=
  completedFormsDPIso s.p (s.A : Type u) ((envelopeDPAlgebra s f).dividedPowers n)
    (envelopeVariableDividedPowers s f n)
    (tensorEnvelopeFormsAlgHom s f n) (tensorEnvelopeFormsSymmAlgHom s f n)
    (tensorEnvelopeFormsAlgHom_isDPMorphism s f n)
    (tensorEnvelopeFormsSymmAlgHom_isDPMorphism s f n)
    (tensorEnvelopeFormsSymmAlgHom_comp s f n) (tensorEnvelopeFormsAlgHom_comp s f n)

/-- **The identification `Ω^a_{D(b)} ≃ Ω̂^a_{D_{P,γ}(J)⟨ξ_i(j)⟩}` in exterior degree `a`.** -/
public noncomputable def tensorEnvelopeFormsEquiv (n a : ℕ) :
    envelopeForms s f a n ≃+ envelopeVariableForms s f n a :=
  (tensorEnvelopeFormsIso s f n).equiv a

/-- The identification in degree `a` is the comparison of completed forms along
`Crystalline.tensorEnvelopeFormsAlgHom`. -/
public theorem tensorEnvelopeFormsEquiv_apply (n a : ℕ) (x : envelopeForms s f a n) :
    tensorEnvelopeFormsEquiv s f n a x = tensorEnvelopeFormsMap s f n a x := rfl

/-- The inverse of the identification in degree `a` is the comparison along
`Crystalline.tensorEnvelopeFormsSymmAlgHom`. -/
public theorem tensorEnvelopeFormsEquiv_symm_apply (n a : ℕ)
    (y : envelopeVariableForms s f n a) :
    (tensorEnvelopeFormsEquiv s f n a).symm y = tensorEnvelopeFormsSymmMap s f n a y := rfl

/-- **The two comparisons are mutually inverse**, one way round. -/
public theorem tensorEnvelopeFormsSymmMap_tensorEnvelopeFormsMap (n a : ℕ)
    (x : envelopeForms s f a n) :
    tensorEnvelopeFormsSymmMap s f n a (tensorEnvelopeFormsMap s f n a x) = x :=
  (tensorEnvelopeFormsEquiv s f n a).symm_apply_apply x

/-- **The two comparisons are mutually inverse**, the other way round. -/
public theorem tensorEnvelopeFormsMap_tensorEnvelopeFormsSymmMap (n a : ℕ)
    (y : envelopeVariableForms s f n a) :
    tensorEnvelopeFormsMap s f n a (tensorEnvelopeFormsSymmMap s f n a y) = y :=
  (tensorEnvelopeFormsEquiv s f n a).apply_symm_apply y

/-- The ring isomorphism the identification is semilinear over is
`Crystalline.tensorEnvelopeFormsAlgHom`, hence `Crystalline.tensorEnvelopeDPEquiv`. -/
public theorem tensorEnvelopeFormsIso_algHom (n : ℕ) :
    (tensorEnvelopeFormsIso s f n).algHom = tensorEnvelopeFormsAlgHom s f n := rfl

end Crystalline

end
