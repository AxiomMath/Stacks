module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Base change of elementary and strictly standard elements

Let `R → A` be a ring map of finite presentation. A *presentation* of `A` over `R` is an
isomorphism `A ≅ R[x_1, …, x_n]/(f_1, …, f_m)`; write `I = (f_1, …, f_m)` for the ideal of
relations. An element `a ∈ A` is elementary standard, resp. strictly standard, if for some
presentation and some `c ≤ min(n, m)` it is a multiple of the principal `c × c` Jacobian minor,
resp. a combination of the `c × c` Jacobian minors on the first `c` relations, and
`a · f_{c+j} ∈ (f_1, …, f_c) + I^2` for every `j`. These properties are preserved by base change
along any ring map `R → R'`.

## Main definitions

* `Presentation`: a presentation of an `R`-algebra as a quotient of a polynomial ring.
* `IsElementaryStandard`: `a` is elementary standard in `A` over `R`.
* `IsStrictlyStandard`: `a` is strictly standard in `A` over `R`.
* `Presentation.basechangePres`: the base change of a presentation of `A` over `R` to a
  presentation of `R' ⊗[R] A` over `R'`.

## Main results

* `isElementaryStandard_basechange`: if `a` is elementary standard in `A` over `R`, then
  `1 ⊗ a` is elementary standard in `R' ⊗[R] A` over `R'`.
* `isStrictlyStandard_basechange`: if `a` is strictly standard in `A` over `R`, then
  `1 ⊗ a` is strictly standard in `R' ⊗[R] A` over `R'`.

## Implementation notes

* Indices are `0`-indexed, so the polynomial ring is `MvPolynomial (Fin n) R` with
  variables `x_0, …, x_{n-1}`, the relations are `f : Fin m → R[x]`, and the
  integer parameter `c` satisfies `c ≤ n` and `c ≤ m`.
* When `c = 0` the relevant Jacobian determinant is the empty determinant `= 1`,
  and condition (ii) ranges over all `j`.  When `c = m` condition (ii) is vacuous.
* The formal partial derivative `∂ f_j / ∂ x_i` is `MvPolynomial.pderiv i (f j)`.
* The Jacobian minor for elementary standard uses rows `0,…,c-1` and columns
  `0,…,c-1`; for strictly standard it ranges over all column subsets of size `c`.
* Condition (ii), `a · f_{c+j} ∈ (f_1,…,f_c) + I^2`, is a statement about lifts of
  `a` to the polynomial ring; since two lifts differ by an element of `I`, their
  product with `f_{c+j}` differs by an element of `I^2`, so the condition does not
  depend on the chosen lift.  We therefore quantify over all lifts.
* `A ⊗_R R'` is modelled as `R' ⊗[R] A`, and `a ⊗ 1` as `1 ⊗ a`.
-/

open MvPolynomial
open scoped TensorProduct

universe u v w

/-- A *presentation* of an `R`-algebra `A`: integers `n, m`, a family of relations
`f : Fin m → R[x_1,…,x_n]`, and an `R`-algebra isomorphism
`A ≃ₐ[R] R[x_1,…,x_n] / (f_1,…,f_m)`. -/
@[ega "IV 1.4.1", sga "1 VIII 3.6"]
structure Presentation (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] where
  n : ℕ
  m : ℕ
  f : Fin m → MvPolynomial (Fin n) R
  iso : A ≃ₐ[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))

noncomputable section

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {R' : Type w} [CommRing R'] [Algebra R R']

namespace Presentation

/-- The ideal of relations `I = (f_1, …, f_m)` inside the polynomial ring. -/
def relIdeal (P : Presentation R A) : Ideal (MvPolynomial (Fin P.n) R) :=
  Ideal.span (Set.range P.f)

/-- The composite `R[x_1,…,x_n] → R[x]/I ≃ A`, sending a polynomial to the element
of `A` it represents. -/
def lift (P : Presentation R A) (p : MvPolynomial (Fin P.n) R) : A :=
  P.iso.symm (Ideal.Quotient.mkₐ R (Ideal.span (Set.range P.f)) p)

/-- `p` is a lift of `a ∈ A` to the polynomial ring, i.e. `p` represents `a`. -/
def IsLift (P : Presentation R A) (a : A) (p : MvPolynomial (Fin P.n) R) : Prop :=
  P.lift p = a

/-- The `c × c` Jacobian minor with rows `0,…,c-1` and columns indexed by a subset
`s ⊆ {0,…,n-1}` of size `c` (a polynomial in `R[x_1,…,x_n]`).  The columns are
taken in increasing order via `s.orderIsoOfFin`.  When `c = 0` this is the empty
determinant, equal to `1`. -/
def jacobianMinor (P : Presentation R A) (c : ℕ) (hc : c ≤ P.m)
    (s : Finset (Fin P.n)) (hs : s.card = c) : MvPolynomial (Fin P.n) R :=
  Matrix.det (fun (j : Fin c) (i : Fin c) =>
    pderiv ((s.orderIsoOfFin hs i : Fin P.n)) (P.f (Fin.castLE hc j)))

/-- The principal `c × c` Jacobian minor with rows `0,…,c-1` and columns `0,…,c-1`.
When `c = 0` this is the empty determinant, equal to `1`. -/
def jacobianMinorPrincipal (P : Presentation R A) (c : ℕ) (hcn : c ≤ P.n) (hcm : c ≤ P.m) :
    MvPolynomial (Fin P.n) R :=
  Matrix.det (fun (j : Fin c) (i : Fin c) =>
    pderiv (Fin.castLE hcn i) (P.f (Fin.castLE hcm j)))

/-- The ideal `(f_1, …, f_c)` generated by the first `c` relations. -/
def firstRelIdeal (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) :
    Ideal (MvPolynomial (Fin P.n) R) :=
  Ideal.span (Set.range (fun j : Fin c => P.f (Fin.castLE hcm j)))

/-- The `c × c` Jacobian minor `det(∂f_j/∂x_i)_{j ∈ V, i ∈ U}` on an arbitrary set `V` of `c`
relations and an arbitrary set `U` of `c` variables, both enumerated in increasing order.  When
`c = 0` this is the empty determinant, equal to `1`.

`jacobianMinor` is the case where `V` consists of the first `c` relations; see
`Presentation.jacobianMinorOn_firstRels`. -/
def jacobianMinorOn (P : Presentation R A) (c : ℕ) (U : Finset (Fin P.n))
    (V : Finset (Fin P.m)) (hU : U.card = c) (hV : V.card = c) : MvPolynomial (Fin P.n) R :=
  Matrix.det (fun (j : Fin c) (i : Fin c) =>
    pderiv ((U.orderIsoOfFin hU i : Fin P.n)) (P.f ((V.orderIsoOfFin hV j : Fin P.m))))

/-- The ideal `(f_j, j ∈ V)` generated by the relations indexed by a set `V`.

`firstRelIdeal` is the case where `V` consists of the first `c` relations; see
`Presentation.selectedRelIdeal_firstRels`. -/
def selectedRelIdeal (P : Presentation R A) (V : Finset (Fin P.m)) :
    Ideal (MvPolynomial (Fin P.n) R) :=
  Ideal.span (Set.range (fun j : ↑V => P.f j.1))

/-- The set `{0, …, c-1}` of the first `c` relation indices. -/
def firstRels (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) : Finset (Fin P.m) :=
  Finset.univ.image (Fin.castLE hcm)

/-- The set of the first `c` relation indices has `c` elements. -/
@[simp]
theorem card_firstRels (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) :
    (P.firstRels c hcm).card = c := by
  rw [firstRels, Finset.card_image_of_injective _ (Fin.castLE_injective hcm)]
  simp

/-- The increasing enumeration of the first `c` relation indices is `Fin.castLE`. -/
theorem coe_orderIsoOfFin_firstRels (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) (j : Fin c) :
    (((P.firstRels c hcm).orderIsoOfFin (P.card_firstRels c hcm) j : Fin P.m)) =
      Fin.castLE hcm j := by
  have he : (Fin.castLEOrderEmb hcm : Fin c ↪o Fin P.m) =
      (P.firstRels c hcm).orderEmbOfFin (P.card_firstRels c hcm) :=
    Finset.orderEmbOfFin_unique' _ fun x =>
      Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  rw [Finset.coe_orderIsoOfFin_apply, ← he]
  rfl

/-- On the first `c` relations, the minor on a general row set is the minor of `jacobianMinor`. -/
theorem jacobianMinorOn_firstRels (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m)
    (U : Finset (Fin P.n)) (hU : U.card = c) :
    P.jacobianMinorOn c U (P.firstRels c hcm) hU (P.card_firstRels c hcm) =
      P.jacobianMinor c hcm U hU := by
  rw [jacobianMinorOn, jacobianMinor]
  congr 1
  funext j i
  rw [P.coe_orderIsoOfFin_firstRels c hcm j]

/-- On the first `c` relations, the ideal generated by the selected relations is
`firstRelIdeal`. -/
theorem selectedRelIdeal_firstRels (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) :
    P.selectedRelIdeal (P.firstRels c hcm) = P.firstRelIdeal c hcm := by
  rw [selectedRelIdeal, firstRelIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨Fin.castLE hcm k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩, rfl⟩

/-- Condition (ii) (Stacks 16.2.3.2 / 16.2.3.4): for every `j = 1,…,m-c` and every
lift `ã` of `a`, the element `ã · f_{c+j}` lies in `(f_1,…,f_c) + I^2`. -/
def StandardCond2 (P : Presentation R A) (a : A) (c : ℕ) (hcm : c ≤ P.m) : Prop :=
  ∀ (j : Fin (P.m - c)) (ã : MvPolynomial (Fin P.n) R), P.IsLift a ã →
    ã * P.f ⟨c + j.1, by have := j.2; omega⟩ ∈ P.firstRelIdeal c hcm + (P.relIdeal) ^ 2

/-- `a` is *elementary standard with respect to the presentation `P` and parameter
`c`* (Stacks 16.2.3.1 + 16.2.3.2): there is `a' ∈ A` with
`a = a' · det(∂f_j/∂x_i)_{i,j=1,…,c}` (condition (i)) and condition (ii) holds. -/
def IsElementaryStandardFor (P : Presentation R A) (a : A) (c : ℕ)
    (hcn : c ≤ P.n) (hcm : c ≤ P.m) : Prop :=
  (∃ a' : A, a = a' * P.lift (P.jacobianMinorPrincipal c hcn hcm)) ∧
    P.StandardCond2 a c hcm

/-- `a` is *strictly standard with respect to the presentation `P` and parameter
`c`* (Stacks 16.2.3.3 + 16.2.3.4): there are elements `a_I ∈ A` indexed by subsets
`I ⊆ {1,…,n}` of size `c` with
`a = ∑_I a_I · det(∂f_j/∂x_i)_{j=1,…,c, i∈I}` (condition (i)) and condition (ii)
holds. -/
def IsStrictlyStandardFor (P : Presentation R A) (a : A) (c : ℕ)
    (hcm : c ≤ P.m) : Prop :=
  (∃ aI : Finset (Fin P.n) → A,
      a = ∑ s ∈ Finset.powersetCard c (Finset.univ : Finset (Fin P.n)),
        aI s * P.lift (if h : s.card = c then P.jacobianMinor c hcm s h else 0)) ∧
    P.StandardCond2 a c hcm

end Presentation

/-- An element `a ∈ A` is *elementary standard in `A` over `R`* if there exists a presentation
of `A` over `R` and an integer `c` with `0 ≤ c ≤ min(n, m)` realizing `a` as elementary
standard. -/
@[stacks 07C7 "the first of the two notions the definition introduces: `a` is elementary \
standard in `A` over `R`, i.e. some presentation `A = R[x_1,…,x_n]/(f_1,…,f_m)` and some \
`0 ≤ c ≤ min(n, m)` satisfy 16.2.3.1 and 16.2.3.2. The two conditions themselves are \
`Presentation.IsElementaryStandardFor`"]
def IsElementaryStandard (a : A) : Prop :=
  ∃ (P : Presentation R A) (c : ℕ) (hcn : c ≤ P.n) (hcm : c ≤ P.m),
    P.IsElementaryStandardFor a c hcn hcm

/-- An element `a ∈ A` is *strictly standard in `A` over `R`* if there exists a presentation of
`A` over `R` and an integer `c` with `0 ≤ c ≤ min(n, m)` realizing `a` as strictly standard. -/
@[stacks 07C7 "the second of the two notions the definition introduces: `a` is strictly \
standard in `A` over `R`, i.e. some presentation `A = R[x_1,…,x_n]/(f_1,…,f_m)` and some \
`0 ≤ c ≤ min(n, m)` satisfy 16.2.3.3 and 16.2.3.4. The two conditions themselves are \
`Presentation.IsStrictlyStandardFor`"]
def IsStrictlyStandard (a : A) : Prop :=
  ∃ (P : Presentation R A) (c : ℕ) (_ : c ≤ P.n) (hcm : c ≤ P.m),
    P.IsStrictlyStandardFor a c hcm

namespace Presentation

/-- Given `R → R'` and a presentation `A = R[x_1,…,x_n]/(f_1,…,f_m)`, the base-changed
relations `f'_j ∈ R'[x_1,…,x_n]` are the images of the `f_j` under the natural map
`R[x_1,…,x_n] → R'[x_1,…,x_n]` induced by `R → R'`. -/
def basechangeRel (P : Presentation R A) (R' : Type w) [CommRing R'] [Algebra R R'] :
    Fin P.m → MvPolynomial (Fin P.n) R' :=
  fun j => MvPolynomial.map (algebraMap R R') (P.f j)

/-- Base change of a quotient: `(R' ⊗ S)/(I·(R'⊗S)) ≃ R' ⊗ (S/I)` as `R'`-algebras. -/
noncomputable def quotBaseChange {S : Type*} [CommRing S] [Algebra R S] (I : Ideal S) :
    ((R' ⊗[R] S) ⧸ (Ideal.map (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S) I))
      ≃ₐ[R'] R' ⊗[R] (S ⧸ I) := by
  set g' := Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R I) with hg'def
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R I) :=
    Ideal.Quotient.mkₐ_surjective R I
  have hg : Function.Surjective g' :=
    Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩) hsurj
  have hker : Ideal.map (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S) I
      = RingHom.ker g' := by
    have hrfl : RingHom.ker g'
        = RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R R') (Ideal.Quotient.mkₐ R I)) := rfl
    rw [hrfl, Algebra.TensorProduct.lTensor_ker _ hsurj,
      ← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
  exact (Ideal.quotientEquivAlgOfEq R' hker).trans (Ideal.quotientKerAlgEquivOfSurjective hg)

/-- The base-change algebra iso `R' ⊗ A ≃ R'[x]/(f')`. -/
@[ega "IV 1.4.1"]
noncomputable def basechangeIso (P : Presentation R A) :
    (R' ⊗[R] A) ≃ₐ[R']
      (MvPolynomial (Fin P.n) R' ⧸ Ideal.span (Set.range (P.basechangeRel R'))) := by
  have e1 : (R' ⊗[R] A) ≃ₐ[R']
      R' ⊗[R] (MvPolynomial (Fin P.n) R ⧸ Ideal.span (Set.range P.f)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl) P.iso
  have e2 := (quotBaseChange (R := R) (R' := R') (Ideal.span (Set.range P.f))).symm
  have hmap : Ideal.span (Set.range (P.basechangeRel R'))
      = Ideal.map (MvPolynomial.algebraTensorAlgEquiv R R')
          (Ideal.map (Algebra.TensorProduct.includeRight :
              MvPolynomial (Fin P.n) R →ₐ[R] R' ⊗[R] MvPolynomial (Fin P.n) R)
            (Ideal.span (Set.range P.f))) := by
    rw [Ideal.map_span, Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨Algebra.TensorProduct.includeRight (P.f j), ⟨P.f j, ⟨j, rfl⟩, rfl⟩, ?_⟩
      rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul,
        one_smul]
      rfl
    · rintro ⟨_, ⟨p, ⟨j, rfl⟩, rfl⟩, rfl⟩
      refine ⟨j, ?_⟩
      rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul,
        one_smul]
      rfl
  have e3 := Ideal.quotientEquivAlg
      (Ideal.map (Algebra.TensorProduct.includeRight :
          MvPolynomial (Fin P.n) R →ₐ[R] R' ⊗[R] MvPolynomial (Fin P.n) R)
        (Ideal.span (Set.range P.f)))
      (Ideal.span (Set.range (P.basechangeRel R')))
      (MvPolynomial.algebraTensorAlgEquiv R R') hmap
  exact e1.trans (e2.trans e3)

/-- `quotBaseChange` sends the class of `x` to the image of `x` under
`R' ⊗[R] S → R' ⊗[R] (S ⧸ I)`. -/
theorem quotBaseChange_mk {S : Type*} [CommRing S] [Algebra R S] (I : Ideal S)
    (x : R' ⊗[R] S) :
    quotBaseChange (R := R) (R' := R') I (Ideal.Quotient.mk _ x)
      = Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R I) x := by
  unfold quotBaseChange
  simp only [AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_apply]
  rfl

/-- The canonical base-change presentation of `R' ⊗ A` over `R'`. -/
@[ega "IV 1.4.1"]
def basechangePres (P : Presentation R A) : Presentation R' (R' ⊗[R] A) :=
  ⟨P.n, P.m, P.basechangeRel R', P.basechangeIso⟩

/-- The base-change iso sends `1 ⊗ (lift p)` to `[map p]`. -/
theorem basechangeIso_includeRight (P : Presentation R A)
    (p : MvPolynomial (Fin P.n) R) :
    P.basechangeIso (Algebra.TensorProduct.includeRight (P.lift p))
      = Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R R') p) := by
  unfold basechangeIso
  simp only [AlgEquiv.trans_apply]
  rw [show (Algebra.TensorProduct.includeRight (P.lift p) : R' ⊗[R] A)
        = (1 : R') ⊗ₜ[R] (P.lift p) from rfl]
  rw [show (Algebra.TensorProduct.congr (AlgEquiv.refl) P.iso ((1 : R') ⊗ₜ[R] (P.lift p)))
        = (1 : R') ⊗ₜ[R] (P.iso (P.lift p)) by simp [Algebra.TensorProduct.congr]]
  have hlift : P.iso (P.lift p) = Ideal.Quotient.mk _ p := by
    unfold Presentation.lift
    rw [AlgEquiv.apply_symm_apply]; rfl
  rw [hlift]
  have he2 : (quotBaseChange (R := R) (R' := R') (Ideal.span (Set.range P.f))).symm
        ((1 : R') ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span (Set.range P.f)) p))
      = Ideal.Quotient.mk _ (Algebra.TensorProduct.includeRight p) := by
    rw [AlgEquiv.symm_apply_eq, quotBaseChange_mk, Algebra.TensorProduct.includeRight_apply]
    simp only [Algebra.TensorProduct.map_tmul, map_one,
      Ideal.Quotient.mkₐ_eq_mk]
  rw [he2, Ideal.quotientEquivAlg_mk]
  congr 1
  rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-- A presentation of `A` over `R` with `n` variables and `m` relations `f_j` gives a
presentation of `R' ⊗[R] A` over `R'` with `n` variables and the `m` relations
`Presentation.basechangeRel`, the images of the `f_j` in `R'[x_1, …, x_n]`. -/
@[ega "IV 1.4.1",
  ega "IV 1.6.2" "(iii), special case",
  sga "1 VIII 3.6" "special case",
  sga "3 XIX 2.1" "special case"]
theorem exists_basechange_presentation (P : Presentation R A) :
    ∃ Q : Presentation R' (R' ⊗[R] A),
      Q.n = P.n ∧ Q.m = P.m ∧ HEq Q.f (P.basechangeRel R') :=
  ⟨⟨P.n, P.m, P.basechangeRel R', P.basechangeIso⟩, rfl, rfl, HEq.rfl⟩

/-! ### Compatibility of the base-change presentation `Q := basechangePres P`

The lifts, Jacobian minors and relation ideals of `Q = basechangePres P` are the images of
those of `P` under `MvPolynomial.map (algebraMap R R')`. Here `Q.n = P.n`, `Q.m = P.m` and
`Q.f = P.basechangeRel R'` hold definitionally. -/

/-- The lift map of the base-change presentation applied to the base-changed polynomial
`map φ p` equals `includeRight` of the original lift. -/
theorem basechangePres_lift_map (P : Presentation R A) (p : MvPolynomial (Fin P.n) R) :
    (P.basechangePres (R' := R')).lift (MvPolynomial.map (algebraMap R R') p)
      = Algebra.TensorProduct.includeRight (P.lift p) := by
  change (P.basechangePres (R' := R')).iso.symm _ = _
  rw [show (P.basechangePres (R' := R')).iso = P.basechangeIso from rfl,
    AlgEquiv.symm_apply_eq, Ideal.Quotient.mkₐ_eq_mk]
  exact (P.basechangeIso_includeRight p).symm

/-- The partial derivative of a base-changed relation is the base change of the partial
derivative. -/
theorem pderiv_basechangeRel (P : Presentation R A) (i : Fin P.n) (j : Fin P.m) :
    pderiv i (P.basechangeRel R' j) = MvPolynomial.map (algebraMap R R') (pderiv i (P.f j)) := by
  simp only [basechangeRel]
  rw [MvPolynomial.pderiv_map]

/-- The principal `c × c` Jacobian minor of the base-change presentation is the base change of
that of `P`. -/
theorem jacobianMinorPrincipal_basechangePres (P : Presentation R A) (c : ℕ)
    (hcn : c ≤ P.n) (hcm : c ≤ P.m) :
    (P.basechangePres (R' := R')).jacobianMinorPrincipal c hcn hcm
      = MvPolynomial.map (algebraMap R R') (P.jacobianMinorPrincipal c hcn hcm) := by
  unfold Presentation.jacobianMinorPrincipal
  rw [RingHom.map_det]
  congr 1
  funext j i
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact P.pderiv_basechangeRel _ _

/-- The `c × c` Jacobian minor of the base-change presentation on a column subset `s` of size
`c` is the base change of that of `P`. -/
theorem jacobianMinor_basechangePres (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m)
    (s : Finset (Fin P.n)) (hs : s.card = c) :
    (P.basechangePres (R' := R')).jacobianMinor c hcm s hs
      = MvPolynomial.map (algebraMap R R') (P.jacobianMinor c hcm s hs) := by
  unfold Presentation.jacobianMinor
  rw [RingHom.map_det]
  congr 1
  funext j i
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact P.pderiv_basechangeRel _ _

/-- The ring hom `MvPolynomial.map (algebraMap R R')` maps `relIdeal P` into
`relIdeal (basechangePres P)`. -/
theorem relIdeal_map_le (P : Presentation R A) :
    Ideal.map (MvPolynomial.map (algebraMap R R')) P.relIdeal
      ≤ (P.basechangePres (R' := R')).relIdeal := by
  unfold Presentation.relIdeal
  rw [Ideal.map_span, Ideal.span_le]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨j, rfl⟩ := hx
  exact Ideal.subset_span ⟨j, rfl⟩

/-- The ring hom `MvPolynomial.map (algebraMap R R')` maps `firstRelIdeal P c` into
`firstRelIdeal (basechangePres P) c`. -/
theorem firstRelIdeal_map_le (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) :
    Ideal.map (MvPolynomial.map (algebraMap R R')) (P.firstRelIdeal c hcm)
      ≤ (P.basechangePres (R' := R')).firstRelIdeal c hcm := by
  unfold Presentation.firstRelIdeal
  rw [Ideal.map_span, Ideal.span_le]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨j, rfl⟩ := hx
  exact Ideal.subset_span ⟨j, rfl⟩

/-- If `q ∈ firstRelIdeal P c + (relIdeal P)^2`, then
`map φ q ∈ firstRelIdeal Q c + (relIdeal Q)^2`, where `Q = basechangePres P`. -/
theorem standardCond2_mem_transfer (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m)
    (q : MvPolynomial (Fin P.n) R)
    (hq : q ∈ P.firstRelIdeal c hcm + (P.relIdeal) ^ 2) :
    MvPolynomial.map (algebraMap R R') q
      ∈ (P.basechangePres (R' := R')).firstRelIdeal c hcm
          + ((P.basechangePres (R' := R')).relIdeal) ^ 2 := by
  have h := Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap R R')) hq
  rw [Ideal.add_eq_sup, Ideal.map_sup, Ideal.map_pow] at h
  rw [Ideal.add_eq_sup]
  have hpow : (Ideal.map (MvPolynomial.map (algebraMap R R')) P.relIdeal) ^ 2
      ≤ ((P.basechangePres (R' := R')).relIdeal) ^ 2 := by
    rw [pow_two, pow_two]
    exact Ideal.mul_mono (P.relIdeal_map_le) (P.relIdeal_map_le)
  exact (sup_le_sup (P.firstRelIdeal_map_le c hcm) hpow) h

/-- Every lift of `includeRight a` over `Q = basechangePres P` differs from `map φ` of a
`P`-lift of `a` by an element of `relIdeal Q`: if `Q.IsLift (includeRight a) q` and
`P.IsLift a p`, then `q - map φ p ∈ relIdeal Q`. -/
theorem lift_sub_map_mem_relIdeal (P : Presentation R A) (a : A)
    (p : MvPolynomial (Fin P.n) R) (hp : P.IsLift a p)
    (q : MvPolynomial (Fin P.n) R')
    (hq : (P.basechangePres (R' := R')).IsLift (Algebra.TensorProduct.includeRight a) q) :
    q - MvPolynomial.map (algebraMap R R') p ∈ (P.basechangePres (R' := R')).relIdeal := by
  set Q := P.basechangePres (R' := R')
  have hpe : P.lift p = a := hp
  have hqe : Q.lift q = Algebra.TensorProduct.includeRight a := hq
  have hQ : Q.lift q = Q.lift (MvPolynomial.map (algebraMap R R') p) := by
    rw [P.basechangePres_lift_map p, hpe, hqe]
  have hmk : Ideal.Quotient.mk (Ideal.span (Set.range Q.f)) q
      = Ideal.Quotient.mk (Ideal.span (Set.range Q.f))
          (MvPolynomial.map (algebraMap R R') p) := by
    simpa only [Presentation.lift, Ideal.Quotient.mkₐ_eq_mk] using Q.iso.symm.injective hQ
  have : q - MvPolynomial.map (algebraMap R R') p ∈ Ideal.span (Set.range Q.f) :=
    Ideal.Quotient.eq.mp hmk
  simpa only [Presentation.relIdeal] using this

/-- Every `a : A` has a lift `p` to the polynomial ring. -/
theorem exists_isLift (P : Presentation R A) (a : A) : ∃ p, P.IsLift a p := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (P.iso a)
  refine ⟨p, ?_⟩
  change P.iso.symm (Ideal.Quotient.mkₐ R (Ideal.span (Set.range P.f)) p) = a
  rw [Ideal.Quotient.mkₐ_eq_mk, hp, AlgEquiv.symm_apply_apply]

/-- Condition (ii) is preserved by the base-change presentation. -/
private theorem standardCond2_basechangePres (P : Presentation R A) (a : A) (c : ℕ)
    (hcm : c ≤ P.m) (h : P.StandardCond2 a c hcm) :
    (P.basechangePres (R' := R')).StandardCond2 (Algebra.TensorProduct.includeRight a) c hcm := by
  intro ⟨k, hk⟩ q hq
  simp only [Presentation.basechangePres] at q hq
  obtain ⟨p, hp⟩ := P.exists_isLift a
  have hkm : c + k < P.m := by have : k < P.m - c := hk; omega
  have hg : (P.basechangePres (R' := R')).f ⟨c + k, hkm⟩
      = MvPolynomial.map (algebraMap R R') (P.f ⟨c + k, hkm⟩) := rfl
  rw [hg, mul_comm]
  set g := MvPolynomial.map (algebraMap R R') (P.f ⟨c + k, hkm⟩)
  have h1 : g * (q - MvPolynomial.map (algebraMap R R') p)
      ∈ (P.basechangePres (R' := R')).relIdeal ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (hg ▸ Ideal.subset_span ⟨_, rfl⟩)
      (P.lift_sub_map_mem_relIdeal a p hp q hq)
  have h2 : g * MvPolynomial.map (algebraMap R R') p
      ∈ (P.basechangePres (R' := R')).firstRelIdeal c hcm
          + (P.basechangePres (R' := R')).relIdeal ^ 2 := by
    rw [← map_mul, mul_comm]
    exact P.standardCond2_mem_transfer c hcm _ (h ⟨k, hk⟩ p hp)
  have hsplit : g * q = g * (q - MvPolynomial.map (algebraMap R R') p)
      + g * MvPolynomial.map (algebraMap R R') p := by ring
  rw [hsplit]
  exact Submodule.add_mem _ (Ideal.mem_sup_right h1) h2

end Presentation

/-- Let `R → A` be a ring map of finite presentation and `R → R'` a ring map. If `a ∈ A` is
elementary standard in `A` over `R`, then `a ⊗ 1 ∈ A ⊗_R R'` is elementary standard in
`A ⊗_R R'` over `R'`. Here `A ⊗_R R'` is modelled as `R' ⊗[R] A` and `a ⊗ 1` as `1 ⊗ a`. -/
@[stacks 07CC "(1)"]
theorem isElementaryStandard_basechange (a : A) (ha : IsElementaryStandard (R := R) a) :
    IsElementaryStandard (R := R')
      (Algebra.TensorProduct.includeRight a : R' ⊗[R] A) := by
  obtain ⟨P, c, hcn, hcm, ⟨a', ha'⟩, hcond⟩ := ha
  refine ⟨P.basechangePres (R' := R'), c, hcn, hcm, ⟨Algebra.TensorProduct.includeRight a', ?_⟩, ?_⟩
  · rw [Presentation.jacobianMinorPrincipal_basechangePres, ha', map_mul]
    exact congrArg (Algebra.TensorProduct.includeRight a' * ·)
      (P.basechangePres_lift_map (R' := R') (P.jacobianMinorPrincipal c hcn hcm)).symm
  · exact Presentation.standardCond2_basechangePres P a c hcm hcond

/-- Let `R → A` be a ring map of finite presentation and `R → R'` a ring map. If `a ∈ A` is
strictly standard in `A` over `R`, then `a ⊗ 1 ∈ A ⊗_R R'` is strictly standard in `A ⊗_R R'`
over `R'`. -/
@[stacks 07CC "(2)"]
theorem isStrictlyStandard_basechange (a : A) (ha : IsStrictlyStandard (R := R) a) :
    IsStrictlyStandard (R := R')
      (Algebra.TensorProduct.includeRight a : R' ⊗[R] A) := by
  obtain ⟨P, c, hcn, hcm, ⟨aI, haI⟩, hcond⟩ := ha
  refine ⟨P.basechangePres (R' := R'), c, hcn, hcm,
    ⟨fun s => Algebra.TensorProduct.includeRight (aI s), ?_⟩, ?_⟩
  · rw [haI, map_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hsc : s.card = c := (Finset.mem_powersetCard.mp hs).2
    rw [dite_eq_left hsc, dite_eq_left hsc, map_mul]
    rw [P.jacobianMinor_basechangePres c hcm s hsc]
    exact congrArg (Algebra.TensorProduct.includeRight (aI s) * ·)
      (P.basechangePres_lift_map (R' := R') (P.jacobianMinor c hcm s hsc)).symm
  · exact Presentation.standardCond2_basechangePres P a c hcm hcond

end
