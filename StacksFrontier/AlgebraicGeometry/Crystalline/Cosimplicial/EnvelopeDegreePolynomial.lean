module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsDPIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Codiagonal
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamDoubleComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential
public import StacksFrontier.AlgebraicGeometry.Crystalline.TensorPowerEnvelope

/-!
# The cosimplicial degree `b` of the envelope as a divided power polynomial algebra

Work in an affine crystalline situation `(A, I, γ)` with target `C`, fix a polynomial
presentation `f : P = A[x_i] → C`, and let `D(*)_env` be the cosimplicial family
`Crystalline.envelopeDPAlgebra` of divided power `A`-algebras: `D(b)_env` is the divided power
envelope of the kernel `J(b)` of `P ⊗_A ⋯ ⊗_A P → C` on the `(b + 1)`-fold tensor power, and its
`p`-adic completion is the ring `D(b)` of [Stacks, Equation 60.17.3, Tag 07JF].

[Stacks, Lemma 60.17.5, Tag 07L2] says that `D(b)` is the `p`-adically completed divided power
polynomial algebra `D⟨ξ_i(j)⟩^∧` over `D` on the differences `ξ_i(j) = x_i(0) - x_i(j)`,
`j = 1, …, b`.  `Crystalline.tensorEnvelopeDPEquiv` proves the uncompleted statement over the
envelope of `J ⊆ P` itself.  The row argument of [Stacks, Proposition 60.21.3, Tag 07LG] needs it
over the degree `0` of the cosimplicial object, compatibly with the coprojection
`σ_b = const ⦋0⦌ ⦋b⦌ 0 : ⦋0⦌ ⟶ ⦋b⦌`, as divided power rings, and for the completed rings and their
completed forms.  This module supplies exactly that.

## How it is constructed

The coprojection `D_env → D(0)_env` and the codiagonal `D(0)_env → D_env` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/Codiagonal.lean` are mutually inverse
divided power morphisms, and a divided power isomorphism of the coefficients induces one of the
divided power polynomial algebras, by the universal property of [Stacks, Tag 07H6]
(`DividedPowers.setIndexedDividedPowerPolynomialBaseChangeEquiv`).  Composing
`Crystalline.tensorEnvelopeDPEquiv` with it gives the identification of the degree `b`.  That
`σ_b` goes to the coefficient inclusion is checked on the polynomial algebra and extended to the
envelope by the uniqueness half of its universal property,
`Crystalline.polynomialDividedPowerEnvelope_dpMorphism_ext`.  The completed statements are the
`p`-adic completions, the forms being compared by `Crystalline.completedMapDifferentialForms` in
both directions.

## Main definitions

* `DividedPowers.setIndexedDividedPowerPolynomialBaseChange` and
  `DividedPowers.setIndexedDividedPowerPolynomialBaseChangeEquiv` — the divided power polynomial
  algebra on a fixed set of variables is functorial in the divided power coefficient ring.
* `Crystalline.envelopeDegreePolynomialEquiv` — **`D(b)_env ≅ D(0)_env⟨ξ_i(j)⟩`**, with
  `Crystalline.envelopeDegreePolynomialAlgEquiv` its form as an isomorphism of `A`-algebras.
* `Crystalline.envelopeDegreeCompletedRingEquiv` — **`D(b) ≅ D(0)⟨ξ_i(j)⟩^∧`** on the completed
  rings.
* `Crystalline.envelopeDegreeFormsEquiv` — **`Ω̂^a_{D(b)} ≅ Ω̂^a_{D(0)⟨ξ_i(j)⟩}`** on the completed
  forms, in every exterior degree `a`.

## Main results

* `Crystalline.envelopeDegreePolynomialEquiv_isDPMorphism`,
  `Crystalline.envelopeDegreePolynomialEquiv_symm_isDPMorphism` and
  `Crystalline.envelopeDegreePolynomialEquiv_algebraMap` — it is an isomorphism of divided power
  rings over `A`.
* `Crystalline.envelopeDegreePolynomialEquiv_map_const` — **`σ_b` becomes the inclusion of the
  coefficients**, and `Crystalline.envelopeDegreePolynomialEquiv_coprojectionDifference` — the
  image of `ξ_i(j)` is the divided power variable of index `(i, j)`.
* `Crystalline.envelopeDegreeCompletedRingEquiv_completedRingMap_const` — the completed `σ_b`
  becomes the completed coefficient inclusion.
* `Crystalline.envelopeDegreeFormsEquiv_smul`, `..._wedge`, `..._wedgeMul`, `..._deRham`,
  `..._differential`, `..._differential_completedRingMap_const`,
  `..._formsMapCompleted_const` and
  `..._formsMapCompleted_const_eq_completedCoefficientFormsMapₗ` (all in the namespace
  `Crystalline`) — the identification of the forms is semilinear over the completed rings,
  respects the wedge products, the de Rham differential and the universal differential, and
  carries the transition map along `σ_b` to the comparison `ψ̂` along the coefficient inclusion,
  in the spelling of [Stacks, Lemma 60.20.2, Tag 07LD].

No tag attribute is placed: this is the form of [Stacks, Tag 07L2] the proof of
[Stacks, Tag 07LG] consumes, not a restatement of the tag.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L2](https://stacks.math.columbia.edu/tag/07L2)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.20.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
-/

@[expose] public noncomputable section

universe u v w

namespace DividedPowers

/-! ### Base change of a divided power polynomial algebra along a divided power morphism -/

section BaseChange

variable {R R' R'' : DividedPowerRing.{u}} (W : Type w)

/-- **The divided power morphism `R⟨x_w : w ∈ W⟩ → R'⟨x_w : w ∈ W⟩` induced by a divided power
morphism `g : R → R'` of the coefficients**, fixing every variable.  It is the morphism produced
by the universal property of the source for the coefficient morphism of the target composed
with `g`, and the variables of the target. -/
public def setIndexedDividedPowerPolynomialBaseChange
    (g : _root_.DividedPowers.DPMorphism R.dividedPowers R'.dividedPowers) :
    _root_.DividedPowers.DPMorphism (setIndexedDividedPowerPolynomialDividedPowers R W)
      (setIndexedDividedPowerPolynomialDividedPowers R' W) :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial R W
    (setIndexedDividedPowerPolynomialDividedPowerRing R' W)
    ((setIndexedDividedPowerPolynomialCoefficientDPMorphism R' W).comp g)
    fun w ↦ ⟨dividedPowerPolynomialVariable R' w, variable_mem_polynomialIdeal R' w⟩).choose

/-- The base change morphism restricted to the coefficients is `g` followed by the coefficient
morphism of the target. -/
public theorem setIndexedDividedPowerPolynomialBaseChange_comp_coefficient
    (g : _root_.DividedPowers.DPMorphism R.dividedPowers R'.dividedPowers) :
    (setIndexedDividedPowerPolynomialBaseChange W g).comp
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W) =
      (setIndexedDividedPowerPolynomialCoefficientDPMorphism R' W).comp g :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial R W
    (setIndexedDividedPowerPolynomialDividedPowerRing R' W)
    ((setIndexedDividedPowerPolynomialCoefficientDPMorphism R' W).comp g)
    fun w ↦ ⟨dividedPowerPolynomialVariable R' w,
      variable_mem_polynomialIdeal R' w⟩).choose_spec.1.1

/-- **The base change morphism sends the coefficient `r` to the coefficient `g r`.** -/
public theorem setIndexedDividedPowerPolynomialBaseChange_algebraMap
    (g : _root_.DividedPowers.DPMorphism R.dividedPowers R'.dividedPowers) (r : R) :
    setIndexedDividedPowerPolynomialBaseChange W g
        (algebraMap R (setIndexedDividedPowerPolynomialAlgebra R W) r) =
      algebraMap R' (setIndexedDividedPowerPolynomialAlgebra R' W) (g r) :=
  congrArg (fun q : _root_.DividedPowers.DPMorphism R.dividedPowers
      (setIndexedDividedPowerPolynomialDividedPowers R' W) ↦ q.toRingHom r)
    (setIndexedDividedPowerPolynomialBaseChange_comp_coefficient W g)

/-- **The base change morphism sends the variable `x_w` to the variable `x_w`.** -/
public theorem setIndexedDividedPowerPolynomialBaseChange_variable
    (g : _root_.DividedPowers.DPMorphism R.dividedPowers R'.dividedPowers) (w : W) :
    setIndexedDividedPowerPolynomialBaseChange W g (dividedPowerPolynomialVariable R w) =
      dividedPowerPolynomialVariable R' w :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial R W
    (setIndexedDividedPowerPolynomialDividedPowerRing R' W)
    ((setIndexedDividedPowerPolynomialCoefficientDPMorphism R' W).comp g)
    fun w ↦ ⟨dividedPowerPolynomialVariable R' w,
      variable_mem_polynomialIdeal R' w⟩).choose_spec.1.2 w

/-- **The base change morphism is the only divided power morphism restricting to `g` on the
coefficients and fixing the variables.** -/
public theorem setIndexedDividedPowerPolynomialBaseChange_unique
    (g : _root_.DividedPowers.DPMorphism R.dividedPowers R'.dividedPowers)
    (φ : _root_.DividedPowers.DPMorphism (setIndexedDividedPowerPolynomialDividedPowers R W)
      (setIndexedDividedPowerPolynomialDividedPowers R' W))
    (hcoeff : φ.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W) =
      (setIndexedDividedPowerPolynomialCoefficientDPMorphism R' W).comp g)
    (hvar : ∀ w : W, φ (dividedPowerPolynomialVariable R w) =
      dividedPowerPolynomialVariable R' w) :
    φ = setIndexedDividedPowerPolynomialBaseChange W g :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial R W
    (setIndexedDividedPowerPolynomialDividedPowerRing R' W)
    ((setIndexedDividedPowerPolynomialCoefficientDPMorphism R' W).comp g)
    fun w ↦ ⟨dividedPowerPolynomialVariable R' w,
      variable_mem_polynomialIdeal R' w⟩).choose_spec.2 φ ⟨hcoeff, hvar⟩

/-- Base change along the identity is the identity. -/
public theorem setIndexedDividedPowerPolynomialBaseChange_id :
    setIndexedDividedPowerPolynomialBaseChange W
        (_root_.DividedPowers.DPMorphism.id R.dividedPowers) =
      _root_.DividedPowers.DPMorphism.id (setIndexedDividedPowerPolynomialDividedPowers R W) :=
  (setIndexedDividedPowerPolynomialBaseChange_unique W _ _ (by ext; rfl) fun _ ↦ rfl).symm

/-- Base change along a composite is the composite of the base changes. -/
public theorem setIndexedDividedPowerPolynomialBaseChange_comp
    (g : _root_.DividedPowers.DPMorphism R.dividedPowers R'.dividedPowers)
    (h : _root_.DividedPowers.DPMorphism R'.dividedPowers R''.dividedPowers) :
    setIndexedDividedPowerPolynomialBaseChange W (h.comp g) =
      (setIndexedDividedPowerPolynomialBaseChange W h).comp
        (setIndexedDividedPowerPolynomialBaseChange W g) :=
  (setIndexedDividedPowerPolynomialBaseChange_unique W (h.comp g) _
    (by
      ext r
      change setIndexedDividedPowerPolynomialBaseChange W h
          (setIndexedDividedPowerPolynomialBaseChange W g
            (algebraMap R (setIndexedDividedPowerPolynomialAlgebra R W) r)) =
        algebraMap R'' (setIndexedDividedPowerPolynomialAlgebra R'' W) (h (g r))
      rw [setIndexedDividedPowerPolynomialBaseChange_algebraMap,
        setIndexedDividedPowerPolynomialBaseChange_algebraMap])
    fun w ↦ by
      change setIndexedDividedPowerPolynomialBaseChange W h
        (setIndexedDividedPowerPolynomialBaseChange W g
          (dividedPowerPolynomialVariable R w)) = _
      rw [setIndexedDividedPowerPolynomialBaseChange_variable,
        setIndexedDividedPowerPolynomialBaseChange_variable]).symm

/-- Base change along one half of a divided power isomorphism, followed by base change along the
other half, is the identity. -/
public theorem setIndexedDividedPowerPolynomialBaseChange_comp_apply_of_comp_eq_id
    (g : _root_.DividedPowers.DPMorphism R.dividedPowers R'.dividedPowers)
    (g' : _root_.DividedPowers.DPMorphism R'.dividedPowers R.dividedPowers)
    (hg : ∀ r, g' (g r) = r) (z : setIndexedDividedPowerPolynomialAlgebra R W) :
    setIndexedDividedPowerPolynomialBaseChange W g'
        (setIndexedDividedPowerPolynomialBaseChange W g z) = z := by
  have hid : g'.comp g = _root_.DividedPowers.DPMorphism.id R.dividedPowers :=
    DFunLike.ext _ _ hg
  have h := congrArg (fun q : _root_.DividedPowers.DPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers R W)
      (setIndexedDividedPowerPolynomialDividedPowers R W) ↦ q z)
    ((setIndexedDividedPowerPolynomialBaseChange_comp W g g').symm.trans
      (hid ▸ setIndexedDividedPowerPolynomialBaseChange_id W))
  exact h

/-- **The ring isomorphism `R⟨x_w : w ∈ W⟩ ≅ R'⟨x_w : w ∈ W⟩` induced by a divided power
isomorphism `R ≅ R'`**, given by its two halves `g` and `g'`.  Both directions are divided power
morphisms, by `DividedPowers.setIndexedDividedPowerPolynomialBaseChangeEquiv_isDPMorphism` and
`DividedPowers.setIndexedDividedPowerPolynomialBaseChangeEquiv_symm_isDPMorphism`. -/
public def setIndexedDividedPowerPolynomialBaseChangeEquiv
    (g : _root_.DividedPowers.DPMorphism R.dividedPowers R'.dividedPowers)
    (g' : _root_.DividedPowers.DPMorphism R'.dividedPowers R.dividedPowers)
    (hg : ∀ r, g' (g r) = r) (hg' : ∀ r, g (g' r) = r) :
    setIndexedDividedPowerPolynomialAlgebra R W ≃+*
      setIndexedDividedPowerPolynomialAlgebra R' W where
  __ := (setIndexedDividedPowerPolynomialBaseChange W g).toRingHom
  invFun := setIndexedDividedPowerPolynomialBaseChange W g'
  left_inv := setIndexedDividedPowerPolynomialBaseChange_comp_apply_of_comp_eq_id W g g' hg
  right_inv := setIndexedDividedPowerPolynomialBaseChange_comp_apply_of_comp_eq_id W g' g hg'

section Equiv

variable (g : _root_.DividedPowers.DPMorphism R.dividedPowers R'.dividedPowers)
  (g' : _root_.DividedPowers.DPMorphism R'.dividedPowers R.dividedPowers)
  (hg : ∀ r, g' (g r) = r) (hg' : ∀ r, g (g' r) = r)

/-- The base change isomorphism is the base change morphism along `g`. -/
@[simp] public theorem setIndexedDividedPowerPolynomialBaseChangeEquiv_apply
    (z : setIndexedDividedPowerPolynomialAlgebra R W) :
    setIndexedDividedPowerPolynomialBaseChangeEquiv W g g' hg hg' z =
      setIndexedDividedPowerPolynomialBaseChange W g z := rfl

/-- The inverse of the base change isomorphism is the base change morphism along `g'`. -/
@[simp] public theorem setIndexedDividedPowerPolynomialBaseChangeEquiv_symm_apply
    (z : setIndexedDividedPowerPolynomialAlgebra R' W) :
    (setIndexedDividedPowerPolynomialBaseChangeEquiv W g g' hg hg').symm z =
      setIndexedDividedPowerPolynomialBaseChange W g' z := rfl

/-- The base change isomorphism is a divided power morphism. -/
public theorem setIndexedDividedPowerPolynomialBaseChangeEquiv_isDPMorphism :
    _root_.DividedPowers.IsDPMorphism (setIndexedDividedPowerPolynomialDividedPowers R W)
      (setIndexedDividedPowerPolynomialDividedPowers R' W)
      (setIndexedDividedPowerPolynomialBaseChangeEquiv W g g' hg hg').toRingHom :=
  (setIndexedDividedPowerPolynomialBaseChange W g).isDPMorphism

/-- The inverse of the base change isomorphism is a divided power morphism. -/
public theorem setIndexedDividedPowerPolynomialBaseChangeEquiv_symm_isDPMorphism :
    _root_.DividedPowers.IsDPMorphism (setIndexedDividedPowerPolynomialDividedPowers R' W)
      (setIndexedDividedPowerPolynomialDividedPowers R W)
      (setIndexedDividedPowerPolynomialBaseChangeEquiv W g g' hg hg').symm.toRingHom :=
  (setIndexedDividedPowerPolynomialBaseChange W g').isDPMorphism

end Equiv

end BaseChange

end DividedPowers

namespace Crystalline

open CategoryTheory DividedPowers Simplicial

/-! ### Divided power morphisms out of the envelope of a polynomial presentation -/

section Ext

variable (s : AffineCrystallineSituation.{u, v}) {κ : Type w}
  (g : MvPolynomial κ s.A →ₐ[s.A] s.C)

/-- **A divided power morphism out of the envelope of a polynomial presentation, into any divided
power ring, is determined by its values on the image of the polynomial algebra.**  The
compatibility with the structure maps from the base is automatic, the structure map of the
envelope factoring through the polynomial algebra. -/
public theorem polynomialDividedPowerEnvelope_dpMorphism_ext (C : DividedPowerRing.{max u w})
    (a b : DividedPowers.DPMorphism (polynomialDividedPowerEnvelope s g).object.dividedPowers
      C.dividedPowers)
    (hab : ∀ x, a ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x) =
      b ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x)) : a = b := by
  have hstruct : b.comp (polynomialDividedPowerEnvelope s g).structureMap =
      a.comp (polynomialDividedPowerEnvelope s g).structureMap := by
    ext c
    have h := RingHom.congr_fun (polynomialDividedPowerEnvelope s g).algebraMap_comp c
    change b ((polynomialDividedPowerEnvelope s g).structureMap.toRingHom c) =
      a ((polynomialDividedPowerEnvelope s g).structureMap.toRingHom c)
    rw [← h, RingHom.comp_apply]
    exact (hab _).symm
  suffices h : (polynomialDividedPowerEnvelope s g).homEquiv C
        (a.comp (polynomialDividedPowerEnvelope s g).structureMap) ⟨a, rfl⟩ =
      (polynomialDividedPowerEnvelope s g).homEquiv C
        (a.comp (polynomialDividedPowerEnvelope s g).structureMap) ⟨b, hstruct⟩ from
    congrArg Subtype.val (((polynomialDividedPowerEnvelope s g).homEquiv C
      (a.comp (polynomialDividedPowerEnvelope s g).structureMap)).injective h)
  refine Subtype.ext ?_
  rw [(polynomialDividedPowerEnvelope s g).homEquiv_apply,
    (polynomialDividedPowerEnvelope s g).homEquiv_apply]
  exact IdealPair.Hom.ext_toRingHom _ _ (RingHom.ext hab)

end Ext

/-! ### The comparison of completed forms and the universal differential of the completion -/

section CompletedDifferential

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J) {C : Type w} [CommRing C] [Algebra A C] {K : Ideal C}
  (epsilon : DividedPowers K) (e : B →ₐ[A] C)
  (he : DividedPowers.IsDPMorphism hJ epsilon e.toRingHom)

/-- **The comparison of completed forms respects the universal differential of the completion**,
at every element of the completion and not only on the image of the uncompleted ring:
`ψ_1 (d r) = d (ê r)`, where `ê` is the completion of the ring map.  Both sides are computed at
each level `pⁿ`, where this is `Crystalline.mapDifferentialFormsOfDPMorphism_oneForm`. -/
public theorem completedMapDifferentialForms_completedFormsDifferential
    (r : completedDividedPowerRing p (B := B)) :
    completedMapDifferentialForms p A hJ epsilon e he 1 (completedFormsDifferential p A hJ r) =
      completedFormsDifferential p A epsilon
        (adicCompletionRingMap e.toRingHom (map_pAdicIdeal_le p _) r) := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := B) p ^ n • ⊤ : Submodule B B) (r.val n)
  have hr : (adicCompletionRingMap e.toRingHom (map_pAdicIdeal_le p _) r).val n =
      Submodule.Quotient.mk (e c) := by
    change adicQuotientMap (ringHomₛₗ e.toRingHom) _ n (r.val n) = _
    rw [← hc]
    rfl
  rw [completedMapDifferentialForms_val p A hJ epsilon e he 1 n _ (dividedPowerOneForm A hJ c)
      (completedFormsDifferential_val p A hJ n r c hc.symm),
    completedFormsDifferential_val p A epsilon n _ (e c) hr,
    mapDifferentialFormsOfDPMorphism_oneForm]

end CompletedDifferential

/-! ### The cosimplicial degree `b` as a divided power polynomial algebra -/

section Degree

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

attribute [local instance] tensorPowerEnvelopeAlgebraInstance

/-- **The divided power polynomial algebras over `D_env` and over `D(0)_env` are isomorphic**, by
base change along the divided power isomorphism `D_env ≅ D(0)_env` whose two halves are the
coprojection `Crystalline.envelopePolynomialCoprojection` and the codiagonal
`Crystalline.envelopeCodiagonal`.  It fixes the variables. -/
public def envelopeZeroPolynomialEquiv (W : Type w) :
    setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object W ≃+*
      setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object W :=
  setIndexedDividedPowerPolynomialBaseChangeEquiv W (envelopePolynomialCoprojection s f 0 0).1
    (envelopeCodiagonal s f 0).1 (envelopeCodiagonal_comp_coprojection s f 0 0)
    (envelopePolynomialCoprojection_comp_envelopeCodiagonal_zero s f)

/-- **The cosimplicial degree `b` of the cosimplicial envelope is the divided power polynomial
algebra `D(0)_env⟨ξ_i(j)⟩` over its degree `0`**, on the variables indexed by
`(i, j) : ι × Fin b`.

This is the uncompleted form of [Stacks, Lemma 60.17.5, Tag 07L2] in the shape the row argument
of [Stacks, Proposition 60.21.3, Tag 07LG] consumes: both sides are divided power rings over `A`
and the isomorphism is one of divided power rings over `A`
(`Crystalline.envelopeDegreePolynomialEquiv_isDPMorphism`,
`Crystalline.envelopeDegreePolynomialEquiv_symm_isDPMorphism`,
`Crystalline.envelopeDegreePolynomialEquiv_algebraMap`), under which the coprojection
`σ_b = const ⦋0⦌ ⦋b⦌ 0` of the cosimplicial object becomes the inclusion of the coefficients
(`Crystalline.envelopeDegreePolynomialEquiv_map_const`) and the image of
`ξ_i(j) = x_i(0) - x_i(j + 1)` becomes the divided power variable of index `(i, j)`
(`Crystalline.envelopeDegreePolynomialEquiv_coprojectionDifference`).  It is
`Crystalline.tensorEnvelopeDPEquiv`, whose base is the envelope of `J ⊆ P` itself, followed by
the change of base `Crystalline.envelopeZeroPolynomialEquiv` to the degree `0`. -/
public def envelopeDegreePolynomialEquiv (b : ℕ) :
    (envelopeDPAlgebra s f).carrier b ≃+*
      setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object (ι × Fin b) :=
  (tensorEnvelopeDPEquiv s f b).trans (envelopeZeroPolynomialEquiv s f (ι × Fin b))

/-- **The identification of the degree `b` is a divided power morphism.** -/
public theorem envelopeDegreePolynomialEquiv_isDPMorphism (b : ℕ) :
    DividedPowers.IsDPMorphism ((envelopeDPAlgebra s f).dividedPowers b)
      (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
        (ι × Fin b))
      (envelopeDegreePolynomialEquiv s f b).toRingHom :=
  DividedPowers.IsDPMorphism.comp
    (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
      (ι × Fin b))
    (setIndexedDividedPowerPolynomialBaseChange (ι × Fin b)
      (envelopePolynomialCoprojection s f 0 0).1).isDPMorphism
    (tensorEnvelopeDPEquiv_isDPMorphism s f b)

/-- **The inverse of the identification of the degree `b` is a divided power morphism.** -/
public theorem envelopeDegreePolynomialEquiv_symm_isDPMorphism (b : ℕ) :
    DividedPowers.IsDPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
        (ι × Fin b))
      ((envelopeDPAlgebra s f).dividedPowers b)
      (envelopeDegreePolynomialEquiv s f b).symm.toRingHom :=
  DividedPowers.IsDPMorphism.comp ((envelopeDPAlgebra s f).dividedPowers b)
    (tensorEnvelopeDPEquiv_symm_isDPMorphism s f b)
    (setIndexedDividedPowerPolynomialBaseChange (ι × Fin b)
      (envelopeCodiagonal s f 0).1).isDPMorphism

/-- **The identification of the degree `b` commutes with the structure maps from `A`.** -/
public theorem envelopeDegreePolynomialEquiv_algebraMap (b : ℕ) (a : s.A) :
    envelopeDegreePolynomialEquiv s f b (algebraMap s.A ((envelopeDPAlgebra s f).carrier b) a) =
      algebraMap s.A
        (setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object
          (ι × Fin b)) a := by
  change setIndexedDividedPowerPolynomialBaseChange (ι × Fin b)
      (envelopePolynomialCoprojection s f 0 0).1
      (tensorEnvelopeDPEquiv s f b ((polynomialDividedPowerEnvelope s
        (tensorPowerPresentation s f b)).structureMap.toRingHom a)) = _
  rw [tensorEnvelopeDPEquiv_structureMap, setIndexedDividedPowerPolynomialBaseChange_algebraMap,
    IsScalarTower.algebraMap_apply s.A (tensorPowerEnvelope s f 0).object
      (setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object (ι × Fin b))]
  exact congrArg _ (congrArg (fun q : DividedPowers.DPMorphism _ _ ↦ q.toRingHom a)
    (envelopePolynomialCoprojection s f 0 0).2)

/-- **The identification of the degree `b` as an isomorphism of `A`-algebras.** -/
public def envelopeDegreePolynomialAlgEquiv (b : ℕ) :
    (envelopeDPAlgebra s f).carrier b ≃ₐ[s.A]
      setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object (ι × Fin b) :=
  AlgEquiv.ofRingEquiv (envelopeDegreePolynomialEquiv_algebraMap s f b)

/-- The algebra isomorphism has the ring isomorphism as its underlying function. -/
@[simp] public theorem envelopeDegreePolynomialAlgEquiv_apply (b : ℕ)
    (x : (envelopeDPAlgebra s f).carrier b) :
    envelopeDegreePolynomialAlgEquiv s f b x = envelopeDegreePolynomialEquiv s f b x := rfl

/-- The inverse of the algebra isomorphism is the inverse of the ring isomorphism. -/
@[simp] public theorem envelopeDegreePolynomialAlgEquiv_symm_apply (b : ℕ)
    (y : setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object
      (ι × Fin b)) :
    (envelopeDegreePolynomialAlgEquiv s f b).symm y =
      (envelopeDegreePolynomialEquiv s f b).symm y := rfl

/-- On the base `D_env`, the reindexing along the coprojection `σ_b` followed by the identification
of the envelope of `J(b)` is the coefficient inclusion after the codiagonal: both are divided
power morphisms out of the envelope of `J(0)`, and on the polynomial algebra they agree since
`σ_b` places every variable in the factor `0`. -/
private theorem tensorEnvelopeDPEquiv_reindex_const (b : ℕ)
    (x : (tensorPowerEnvelope s f 0).object) :
    tensorEnvelopeDPEquiv s f b ((envelopeReindex s f (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)).1 x) =
      algebraMap (polynomialDividedPowerEnvelope s f).object
        (setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object
          (ι × Fin b))
        ((envelopeCodiagonal s f 0).1 x) := by
  have hpoly : ∀ y : MvPolynomial (Fin 1 × ι) s.A,
      tensorEnvelopeDPEquiv s f b ((envelopeReindex s f (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)).1
          ((tensorPowerEnvelope s f 0).algebraMap.toRingHom y)) =
        algebraMap (polynomialDividedPowerEnvelope s f).object
          (setIndexedDividedPowerPolynomialAlgebra (polynomialDividedPowerEnvelope s f).object
            (ι × Fin b))
          ((envelopeCodiagonal s f 0).1 ((tensorPowerEnvelope s f 0).algebraMap.toRingHom y)) := by
    intro y
    have hr : MvPolynomial.rename (simplexVariableMap (ι := ι)
        (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)) y =
        mvPolynomialCoprojection s.A (0 : Fin (b + 1)) (MvPolynomial.rename Prod.snd y) := by
      rw [mvPolynomialCoprojection, MvPolynomial.rename_rename]
      rfl
    rw [envelopeReindex_polynomial, envelopeCodiagonal_polynomial, hr]
    exact tensorEnvelopeDPEquiv_coprojection s f b _
  have h := polynomialDividedPowerEnvelope_dpMorphism_ext s (tensorPowerPresentation s f 0)
    (setIndexedDividedPowerPolynomialDividedPowerRing (polynomialDividedPowerEnvelope s f).object
      (ι × Fin b))
    ((DividedPowers.DPMorphism.mk' (tensorEnvelopeDPEquiv_isDPMorphism s f b)).comp
      (envelopeReindex s f (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)).1)
    ((setIndexedDividedPowerPolynomialCoefficientDPMorphism
      (polynomialDividedPowerEnvelope s f).object (ι × Fin b)).comp (envelopeCodiagonal s f 0).1)
    hpoly
  exact congrArg (fun q : DividedPowers.DPMorphism _ _ ↦ q x) h

/-- **The coprojection `σ_b = const ⦋0⦌ ⦋b⦌ 0` becomes the inclusion of the coefficients**: under
the identification of the degree `b` with `D(0)_env⟨ξ_i(j)⟩`, the transition map
`D(0)_env → D(b)_env` of the cosimplicial envelope along `σ_b` is `algebraMap`.  This is the
clause of [Stacks, Tag 07L2] saying that the isomorphism is one of algebras over `D`. -/
public theorem envelopeDegreePolynomialEquiv_map_const (b : ℕ)
    (x : (envelopeDPAlgebra s f).carrier 0) :
    envelopeDegreePolynomialEquiv s f b
        ((envelopeDPAlgebra s f).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) x) =
      algebraMap (tensorPowerEnvelope s f 0).object
        (setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object (ι × Fin b))
        x := by
  change setIndexedDividedPowerPolynomialBaseChange (ι × Fin b)
      (envelopePolynomialCoprojection s f 0 0).1
      (tensorEnvelopeDPEquiv s f b
        ((envelopeReindex s f (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)).1 x)) = _
  exact (congrArg _ (tensorEnvelopeDPEquiv_reindex_const s f b x)).trans
    ((setIndexedDividedPowerPolynomialBaseChange_algebraMap _ _ _).trans
      (congrArg _ (envelopePolynomialCoprojection_comp_envelopeCodiagonal_zero s f x)))

/-- **The image of `ξ_i(j) = x_i(0) - x_i(j + 1)` is the divided power variable of index
`(i, j)`**, `j : Fin b` standing for the slot `j + 1`.  This is the clause of [Stacks, Tag 07L2]
pinning down what the isomorphism does to the difference coordinates. -/
public theorem envelopeDegreePolynomialEquiv_coprojectionDifference (b : ℕ) (q : ι × Fin b) :
    envelopeDegreePolynomialEquiv s f b
        ((tensorPowerEnvelope s f b).algebraMap.toRingHom (coprojectionDifference s b q)) =
      dividedPowerPolynomialVariable (tensorPowerEnvelope s f 0).object q := by
  change setIndexedDividedPowerPolynomialBaseChange (ι × Fin b)
      (envelopePolynomialCoprojection s f 0 0).1
      (tensorEnvelopeDPEquiv s f b ((polynomialDividedPowerEnvelope s
        (tensorPowerPresentation s f b)).algebraMap.toRingHom (coprojectionDifference s b q))) = _
  rw [tensorEnvelopeDPEquiv_coprojectionDifference,
    setIndexedDividedPowerPolynomialBaseChange_variable]

/-! ### The identification as a pair of `A`-algebra maps -/

/-- The identification of the degree `b`, as an `A`-algebra map. -/
public def envelopeDegreePolynomialAlgHom (b : ℕ) :
    (envelopeDPAlgebra s f).carrier b →ₐ[s.A]
      setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object (ι × Fin b) :=
  (envelopeDegreePolynomialAlgEquiv s f b).toAlgHom

/-- The inverse of the identification of the degree `b`, as an `A`-algebra map. -/
public def envelopeDegreePolynomialSymmAlgHom (b : ℕ) :
    setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object (ι × Fin b)
      →ₐ[s.A] (envelopeDPAlgebra s f).carrier b :=
  (envelopeDegreePolynomialAlgEquiv s f b).symm.toAlgHom

/-- The `A`-algebra map underlying the identification is the ring isomorphism. -/
@[simp] public theorem envelopeDegreePolynomialAlgHom_apply (b : ℕ)
    (x : (envelopeDPAlgebra s f).carrier b) :
    envelopeDegreePolynomialAlgHom s f b x = envelopeDegreePolynomialEquiv s f b x := rfl

/-- The `A`-algebra map underlying the inverse is the inverse ring isomorphism. -/
@[simp] public theorem envelopeDegreePolynomialSymmAlgHom_apply (b : ℕ)
    (y : setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object
      (ι × Fin b)) :
    envelopeDegreePolynomialSymmAlgHom s f b y = (envelopeDegreePolynomialEquiv s f b).symm y :=
  rfl

/-- The identification, as an `A`-algebra map, is a divided power morphism. -/
public theorem envelopeDegreePolynomialAlgHom_isDPMorphism (b : ℕ) :
    DividedPowers.IsDPMorphism ((envelopeDPAlgebra s f).dividedPowers b)
      (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
        (ι × Fin b))
      (envelopeDegreePolynomialAlgHom s f b).toRingHom :=
  envelopeDegreePolynomialEquiv_isDPMorphism s f b

/-- The inverse of the identification, as an `A`-algebra map, is a divided power morphism. -/
public theorem envelopeDegreePolynomialSymmAlgHom_isDPMorphism (b : ℕ) :
    DividedPowers.IsDPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
        (ι × Fin b))
      ((envelopeDPAlgebra s f).dividedPowers b)
      (envelopeDegreePolynomialSymmAlgHom s f b).toRingHom :=
  envelopeDegreePolynomialEquiv_symm_isDPMorphism s f b

/-- The inverse after the identification is the identity. -/
public theorem envelopeDegreePolynomialSymmAlgHom_comp (b : ℕ) :
    AlgHom.id s.A ((envelopeDPAlgebra s f).carrier b) =
      (envelopeDegreePolynomialSymmAlgHom s f b).comp (envelopeDegreePolynomialAlgHom s f b) :=
  AlgHom.ext fun x ↦ ((envelopeDegreePolynomialEquiv s f b).symm_apply_apply x).symm

/-- The identification after the inverse is the identity. -/
public theorem envelopeDegreePolynomialAlgHom_comp_symm (b : ℕ) :
    AlgHom.id s.A
        (setIndexedDividedPowerPolynomialAlgebra (tensorPowerEnvelope s f 0).object
          (ι × Fin b)) =
      (envelopeDegreePolynomialAlgHom s f b).comp (envelopeDegreePolynomialSymmAlgHom s f b) :=
  AlgHom.ext fun y ↦ ((envelopeDegreePolynomialEquiv s f b).apply_symm_apply y).symm

/-- **The coefficient inclusion `D(0)_env → D(0)_env⟨ξ_i(j)⟩` is the coprojection `σ_b` followed
by the identification of the degree `b`**, as `A`-algebra maps. -/
public theorem coefficientAlgHom_eq_envelopeDegreePolynomialAlgHom_comp_map_const (b : ℕ) :
    DividedPowerPolynomial.coefficientAlgHom s.A (tensorPowerEnvelope s f 0).object (ι × Fin b) =
      (envelopeDegreePolynomialAlgHom s f b).comp
        ((envelopeDPAlgebra s f).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)) :=
  AlgHom.ext fun y ↦ (envelopeDegreePolynomialEquiv_map_const s f b y).symm

/-! ### The completed form: the completed rings and the completed forms -/

/-- **The completed cosimplicial degree `D̂(b)` is the completed divided power polynomial algebra
over the degree `0`**: the `p`-adic completion of `Crystalline.envelopeDegreePolynomialEquiv`,
with inverse the completion of its inverse.  Under it the completed transition map along the
coprojection `σ_b` is the completed coefficient inclusion,
`Crystalline.envelopeDegreeCompletedRingEquiv_completedRingMap_const`. -/
public def envelopeDegreeCompletedRingEquiv (b : ℕ) :
    (envelopeDPAlgebra s f).completedRing s.p b ≃+*
      DividedPowerPolynomial.completedDividedPowerPolynomialRing
        (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p where
  __ := adicCompletionRingMap (envelopeDegreePolynomialAlgHom s f b).toRingHom
    (map_pAdicIdeal_le s.p _)
  invFun := adicCompletionRingMap (envelopeDegreePolynomialSymmAlgHom s f b).toRingHom
    (map_pAdicIdeal_le s.p _)
  left_inv x :=
    ((adicCompletionMapₛₗ_comp_apply
      (ringHomₛₗ (envelopeDegreePolynomialAlgHom s f b).toRingHom)
      (ringHomₛₗ (envelopeDegreePolynomialSymmAlgHom s f b).toRingHom)
      (ringHomₛₗ (RingHom.id _)) (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _)
      (map_pAdicIdeal_le s.p _)
      (fun y ↦ ((envelopeDegreePolynomialEquiv s f b).symm_apply_apply y).symm) x).symm).trans
      (adicCompletionMapₛₗ_id_apply _ _ (fun _ ↦ rfl) x)
  right_inv x :=
    ((adicCompletionMapₛₗ_comp_apply
      (ringHomₛₗ (envelopeDegreePolynomialSymmAlgHom s f b).toRingHom)
      (ringHomₛₗ (envelopeDegreePolynomialAlgHom s f b).toRingHom)
      (ringHomₛₗ (RingHom.id _)) (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _)
      (map_pAdicIdeal_le s.p _)
      (fun y ↦ ((envelopeDegreePolynomialEquiv s f b).apply_symm_apply y).symm) x).symm).trans
      (adicCompletionMapₛₗ_id_apply _ _ (fun _ ↦ rfl) x)

/-- The completed identification is the completion of the uncompleted one. -/
public theorem envelopeDegreeCompletedRingEquiv_apply (b : ℕ)
    (x : (envelopeDPAlgebra s f).completedRing s.p b) :
    envelopeDegreeCompletedRingEquiv s f b x =
      adicCompletionRingMap (envelopeDegreePolynomialAlgHom s f b).toRingHom
        (map_pAdicIdeal_le s.p _) x := rfl

/-- The inverse of the completed identification is the completion of the uncompleted inverse. -/
public theorem envelopeDegreeCompletedRingEquiv_symm_apply (b : ℕ)
    (y : DividedPowerPolynomial.completedDividedPowerPolynomialRing
      (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p) :
    (envelopeDegreeCompletedRingEquiv s f b).symm y =
      adicCompletionRingMap (envelopeDegreePolynomialSymmAlgHom s f b).toRingHom
        (map_pAdicIdeal_le s.p _) y := rfl

/-- The completed identification on the image of the uncompleted ring. -/
public theorem envelopeDegreeCompletedRingEquiv_of (b : ℕ)
    (x : (envelopeDPAlgebra s f).carrier b) :
    envelopeDegreeCompletedRingEquiv s f b (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (envelopeDegreePolynomialEquiv s f b x) :=
  adicCompletionRingMap_of _ _ x

/-- **The completed coprojection `σ_b : D̂(0) → D̂(b)` becomes the completed coefficient
inclusion `D̂(0) → D̂(0)⟨ξ_i(j)⟩^∧`** under the completed identification of the degree `b`. -/
public theorem envelopeDegreeCompletedRingEquiv_completedRingMap_const (b : ℕ)
    (x : (envelopeDPAlgebra s f).completedRing s.p 0) :
    envelopeDegreeCompletedRingEquiv s f b
        ((envelopeDPAlgebra s f).completedRingMap s.p (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) x) =
      DividedPowerPolynomial.completedCoefficientRingHom s.A (tensorPowerEnvelope s f 0).object
        (ι × Fin b) s.p x :=
  (adicCompletionMapₛₗ_comp_apply
    (ringHomₛₗ ((envelopeDPAlgebra s f).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)).toRingHom)
    (ringHomₛₗ (envelopeDegreePolynomialAlgHom s f b).toRingHom)
    (ringHomₛₗ (DividedPowerPolynomial.coefficientAlgHom s.A (tensorPowerEnvelope s f 0).object
      (ι × Fin b)).toRingHom)
    (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _)
    (fun y ↦ (envelopeDegreePolynomialEquiv_map_const s f b y).symm) x).symm

/-- **The completed divided power de Rham complexes of the degree `b` and of the divided power
polynomial algebra `D(0)_env⟨ξ_i(j)⟩` are isomorphic**, by `Crystalline.completedFormsDPIso` at
the divided power isomorphism of `A`-algebras `Crystalline.envelopeDegreePolynomialAlgHom`. -/
public def envelopeDegreeFormsDPIso (b : ℕ) :
    CompletedFormsDPIso s.p s.A ((envelopeDPAlgebra s f).dividedPowers b)
      (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
        (ι × Fin b)) :=
  completedFormsDPIso s.p s.A _ _ (envelopeDegreePolynomialAlgHom s f b)
    (envelopeDegreePolynomialSymmAlgHom s f b)
    (envelopeDegreePolynomialAlgHom_isDPMorphism s f b)
    (envelopeDegreePolynomialSymmAlgHom_isDPMorphism s f b)
    (envelopeDegreePolynomialSymmAlgHom_comp s f b)
    (envelopeDegreePolynomialAlgHom_comp_symm s f b)

/-- **The forms `Ω̂^a_{D(b)}` of the cosimplicial envelope are the completed forms of the divided
power polynomial algebra `D(0)_env⟨ξ_i(j)⟩`**, in every exterior degree `a`.  It is the
comparison `Crystalline.completedMapDifferentialForms` of completed forms along the
identification of the degree `b`, with inverse the comparison along its inverse
(`Crystalline.envelopeDegreeFormsEquiv_apply`, `Crystalline.envelopeDegreeFormsEquiv_symm_apply`);
it is semilinear over `Crystalline.envelopeDegreeCompletedRingEquiv` and respects the wedge
products, the de Rham differentials and the universal differentials. -/
public def envelopeDegreeFormsEquiv (b a : ℕ) :
    (envelopeDPAlgebra s f).forms s.p a b ≃+
      DividedPowerPolynomial.completedPolynomialForms s.A (tensorPowerEnvelope s f 0).object
        (ι × Fin b) s.p a :=
  (envelopeDegreeFormsDPIso s f b).equiv a

/-- The identification of the forms is the comparison of completed forms along the
identification of the degree `b`. -/
public theorem envelopeDegreeFormsEquiv_apply (b a : ℕ)
    (x : (envelopeDPAlgebra s f).forms s.p a b) :
    envelopeDegreeFormsEquiv s f b a x =
      completedMapDifferentialForms s.p s.A ((envelopeDPAlgebra s f).dividedPowers b)
        (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
          (ι × Fin b))
        (envelopeDegreePolynomialAlgHom s f b)
        (envelopeDegreePolynomialAlgHom_isDPMorphism s f b) a x := by
  change (envelopeDegreeFormsDPIso s f b).equiv a x = _
  unfold envelopeDegreeFormsDPIso
  exact completedFormsDPIso_equiv_apply _ _ _ _ _ _ _ _ _ _ _ _

/-- The inverse of the identification of the forms is the comparison of completed forms along
the inverse of the identification of the degree `b`. -/
public theorem envelopeDegreeFormsEquiv_symm_apply (b a : ℕ)
    (y : DividedPowerPolynomial.completedPolynomialForms s.A (tensorPowerEnvelope s f 0).object
      (ι × Fin b) s.p a) :
    (envelopeDegreeFormsEquiv s f b a).symm y =
      completedMapDifferentialForms s.p s.A
        (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
          (ι × Fin b))
        ((envelopeDPAlgebra s f).dividedPowers b)
        (envelopeDegreePolynomialSymmAlgHom s f b)
        (envelopeDegreePolynomialSymmAlgHom_isDPMorphism s f b) a y := by
  change ((envelopeDegreeFormsDPIso s f b).equiv a).symm y = _
  unfold envelopeDegreeFormsDPIso
  exact completedFormsDPIso_equiv_symm_apply _ _ _ _ _ _ _ _ _ _ _ _

/-- **The identification of the forms is semilinear over the completed identification of the
rings.** -/
public theorem envelopeDegreeFormsEquiv_smul (b a : ℕ)
    (r : (envelopeDPAlgebra s f).completedRing s.p b)
    (x : (envelopeDPAlgebra s f).forms s.p a b) :
    envelopeDegreeFormsEquiv s f b a (r • x) =
      envelopeDegreeCompletedRingEquiv s f b r • envelopeDegreeFormsEquiv s f b a x :=
  (envelopeDegreeFormsEquiv_apply s f b a (r • x)).trans
    ((adicCompletionMapₛₗ_smul _ _ r x).trans
      (congrArg (envelopeDegreeCompletedRingEquiv s f b r • ·)
        (envelopeDegreeFormsEquiv_apply s f b a x).symm))

/-- **The identification of the forms respects the wedge product**, the wedge of the divided
power polynomial algebra being read as in [Stacks, Lemma 60.20.2, Tag 07LD]. -/
public theorem envelopeDegreeFormsEquiv_wedge (b a : ℕ)
    (x : (envelopeDPAlgebra s f).forms s.p a b) (y : (envelopeDPAlgebra s f).forms s.p 1 b) :
    envelopeDegreeFormsEquiv s f b (a + 1) ((envelopeDPAlgebra s f).wedge s.p b a x y) =
      DividedPowerPolynomial.completedPolynomialFormsWedge s.A
        (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p a
        (envelopeDegreeFormsEquiv s f b a x) (envelopeDegreeFormsEquiv s f b 1 y) :=
  (envelopeDegreeFormsDPIso s f b).wedge a x y

/-- **The identification of the forms respects the bigraded wedge product.** -/
public theorem envelopeDegreeFormsEquiv_wedgeMul (b a a' : ℕ)
    (x : (envelopeDPAlgebra s f).forms s.p a b) (y : (envelopeDPAlgebra s f).forms s.p a' b) :
    envelopeDegreeFormsEquiv s f b (a + a') ((envelopeDPAlgebra s f).wedgeMul s.p b a a' x y) =
      completedDividedPowerWedgeMul s.p s.A
        (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
          (ι × Fin b)) a a'
        (envelopeDegreeFormsEquiv s f b a x) (envelopeDegreeFormsEquiv s f b a' y) :=
  (envelopeDegreeFormsDPIso s f b).wedgeMul a a' x y

/-- **The identification of the forms respects the de Rham differential.** -/
public theorem envelopeDegreeFormsEquiv_deRham (b a : ℕ)
    (x : (envelopeDPAlgebra s f).forms s.p a b) :
    envelopeDegreeFormsEquiv s f b (a + 1) ((envelopeDPAlgebra s f).deRham s.p b a x) =
      completedDividedPowerDeRham s.p s.A
        (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
          (ι × Fin b)) a (envelopeDegreeFormsEquiv s f b a x) :=
  (envelopeDegreeFormsDPIso s f b).deRham a x

/-- **The identification of the forms respects the universal differential**:
`d r ↦ d r'`, where `r'` is the image of `r` under the completed identification of the rings. -/
public theorem envelopeDegreeFormsEquiv_differential (b : ℕ)
    (r : (envelopeDPAlgebra s f).completedRing s.p b) :
    envelopeDegreeFormsEquiv s f b 1 ((envelopeDPAlgebra s f).differential s.p b r) =
      completedFormsDifferential s.p s.A
        (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
          (ι × Fin b)) (envelopeDegreeCompletedRingEquiv s f b r) :=
  (envelopeDegreeFormsEquiv_apply s f b 1 _).trans
    (completedMapDifferentialForms_completedFormsDifferential s.p s.A _ _
      (envelopeDegreePolynomialAlgHom s f b) (envelopeDegreePolynomialAlgHom_isDPMorphism s f b)
      r)

/-- **The differential of a scalar of the degree `0`, carried along `σ_b`, is the differential
`D̂(0) → Ω̂¹` of the divided power polynomial algebra over `D̂(0)`** of
[Stacks, Lemma 60.20.2, Tag 07LD],
`Crystalline.DividedPowerPolynomial.completedPolynomialFormsDifferential`. -/
public theorem envelopeDegreeFormsEquiv_differential_completedRingMap_const (b : ℕ)
    (r : (envelopeDPAlgebra s f).completedRing s.p 0) :
    envelopeDegreeFormsEquiv s f b 1 ((envelopeDPAlgebra s f).differential s.p b
        ((envelopeDPAlgebra s f).completedRingMap s.p (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) r)) =
      DividedPowerPolynomial.completedPolynomialFormsDifferential s.A
        (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p r :=
  (envelopeDegreeFormsEquiv_differential s f b _).trans
    (congrArg (completedFormsDifferential s.p s.A
      (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
        (ι × Fin b))) (envelopeDegreeCompletedRingEquiv_completedRingMap_const s f b r))

/-- **The transition map of the forms along the coprojection `σ_b` becomes the comparison of
completed forms along the coefficient inclusion** `D(0)_env → D(0)_env⟨ξ_i(j)⟩`. -/
public theorem envelopeDegreeFormsEquiv_formsMapCompleted_const (b a : ℕ)
    (x : (envelopeDPAlgebra s f).forms s.p a 0) :
    envelopeDegreeFormsEquiv s f b a
        ((envelopeDPAlgebra s f).formsMapCompleted s.p (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) a x) =
      completedMapDifferentialForms s.p s.A (tensorPowerEnvelope s f 0).object.dividedPowers
        (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
          (ι × Fin b))
        (DividedPowerPolynomial.coefficientAlgHom s.A (tensorPowerEnvelope s f 0).object
          (ι × Fin b))
        (DividedPowerPolynomial.coefficientAlgHom_isDPMorphism s.A
          (tensorPowerEnvelope s f 0).object (ι × Fin b)) a x :=
  (envelopeDegreeFormsEquiv_apply s f b a _).trans (completedMapDifferentialForms_eq_comp s.p s.A
    ((envelopeDPAlgebra s f).dividedPowers 0) ((envelopeDPAlgebra s f).dividedPowers b)
    (setIndexedDividedPowerPolynomialDividedPowers (tensorPowerEnvelope s f 0).object
      (ι × Fin b))
    ((envelopeDPAlgebra s f).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0))
    (envelopeDegreePolynomialAlgHom s f b)
    (DividedPowerPolynomial.coefficientAlgHom s.A (tensorPowerEnvelope s f 0).object
      (ι × Fin b))
    ((envelopeDPAlgebra s f).map_isDPMorphism (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0))
    (envelopeDegreePolynomialAlgHom_isDPMorphism s f b)
    (DividedPowerPolynomial.coefficientAlgHom_isDPMorphism s.A
      (tensorPowerEnvelope s f 0).object (ι × Fin b))
    (coefficientAlgHom_eq_envelopeDegreePolynomialAlgHom_comp_map_const s f b) a x).symm

/-- **The transition map of the forms along the coprojection `σ_b` becomes the completed
comparison `ψ̂ : Ω̂^a_{D(0)} → Ω̂^a_{D(0)⟨ξ⟩}`** of [Stacks, Lemma 60.20.2, Tag 07LD], read
`D̂(0)`-linearly as `Crystalline.DividedPowerPolynomial.completedCoefficientFormsMapₗ`, for any
linear order on the variables (which that map is stated with). -/
public theorem envelopeDegreeFormsEquiv_formsMapCompleted_const_eq_completedCoefficientFormsMapₗ
    (b : ℕ) [LinearOrder (ι × Fin b)] (a : ℕ) (x : (envelopeDPAlgebra s f).forms s.p a 0) :
    envelopeDegreeFormsEquiv s f b a
        ((envelopeDPAlgebra s f).formsMapCompleted s.p (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) a x) =
      DividedPowerPolynomial.completedCoefficientFormsMapₗ s.A
        (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p a x :=
  (envelopeDegreeFormsEquiv_formsMapCompleted_const s f b a x).trans
    (DividedPowerPolynomial.completedCoefficientFormsMapₗ_apply s.A
      (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p a x).symm

end Degree

end Crystalline

end
