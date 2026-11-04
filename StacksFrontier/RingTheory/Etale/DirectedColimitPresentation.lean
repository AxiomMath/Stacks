module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import StacksFrontier.RingTheory.MvPolynomial.DirectedColimit
public import StacksFrontier.RingTheory.Spectrum.Prime.DirectedColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Standard étale presentations over a directed colimit of rings

Let `(G i)` be a directed system of commutative rings with colimit `A`, and let `B` be presented as
`A[x_k : k ∈ κ] ⧸ (g_k : k ∈ κ)` with `κ` finite and Jacobian determinant
`Δ = det (∂g_l/∂x_k)` invertible in `B`, so that `A → B` is étale by the standard-étale criterion.
This file shows that the whole picture descends to a stage: there are an index `j`, polynomials
`g_{k,j}` over `G j` lifting the `g_k`, and the Jacobian determinant of the lifted family is again
invertible, so that `G j → G j[x] ⧸ (g_{·,j})` is étale; moreover the quotient over `A` is the base
change of the quotient over `G j` along `G j → A`.

## Main results

* `Algebra.etale_mvPolynomialQuotient_of_isUnit_det`: the standard-étale criterion in the form it
  is used here — a square family of polynomials whose Jacobian determinant is invertible in the
  quotient presents an étale algebra.  This is the special case of Stacks 00U9 /
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero` that the source invokes.
* `MvPolynomial.exists_ge_isUnit_detJacobian_of_directed`: invertibility of the Jacobian
  determinant descends to a stage.
* `MvPolynomial.exists_ge_etale_quotient_of_directed`: hence the presentation at that stage is
  étale over that stage.
* `Algebra.tensorQuotientSpanEquiv`: `T ⊗[R] (R[x] ⧸ (g)) ≃ₐ[T] T[x] ⧸ (g)`, the base change of a
  finitely presented quotient of a polynomial ring.
* `MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_le` and
  `MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_directed`: the two instances of that
  equivalence used in Stacks 07SQ, namely `B_j ≅ B_i ⊗_{A_i} A_j` for `j ≥ i` and
  `B ≅ B_i ⊗_{A_i} A`.
* `MvPolynomial.exists_ge_surjective_comap_quotient_of_directed`: if `Spec B → Spec A` is
  surjective then `Spec B_j → Spec (G j)` is surjective for some `j ≥ i`, with `B_j` the
  presentation at the stage `j`.

## Implementation notes

The lifting of the polynomials themselves is
`MvPolynomial.exists_ge_forall_map_eq_of_directed`, and the descent of invertibility is
`MvPolynomial.exists_ge_isUnit_quotientMk_of_directed`; both live in
`StacksFrontier.RingTheory.MvPolynomial.DirectedColimit`.  What is added here is the identification of
the Jacobian determinant of a base-changed family with the base change of the Jacobian determinant,
`MvPolynomial.map_detJacobian`, which turns the descent of invertibility of `Δ` into the descent of
invertibility of `Δ_j`, and the packaging through Mathlib's
`Algebra.PreSubmersivePresentation.naive`.

The base change `Algebra.tensorQuotientSpanEquiv` is Mathlib's
`Algebra.Presentation.baseChange` of the naive presentation, read through
`Algebra.Presentation.quotientEquiv`; nothing else is needed, so no tensor-product computation
appears.  The two corollaries are stated with `letI := _.toAlgebra` because a transition map of a
directed system of rings is a bare ring map, not an `Algebra` instance.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public section

universe u v w

open MvPolynomial TensorProduct

/-! ### The Jacobian determinant of a square family of polynomials -/

namespace MvPolynomial

/-- The Jacobian determinant of a family of polynomials indexed by the variables: the determinant
of the matrix of partial derivatives `∂g_b/∂x_a`. -/
noncomputable def detJacobian {R : Type u} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (g : κ → MvPolynomial κ R) : MvPolynomial κ R :=
  (Matrix.of fun a b ↦ pderiv a (g b)).det

/-- The Jacobian determinant commutes with base change: forming the matrix of partial derivatives
of the image family and taking its determinant is the same as taking the image of the Jacobian
determinant. -/
theorem map_detJacobian {R : Type u} [CommRing R] {S : Type v} [CommRing S] (ψ : R →+* S)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (g : κ → MvPolynomial κ R) :
    map ψ (detJacobian g) = detJacobian fun k ↦ map ψ (g k) := by
  rw [detJacobian, detJacobian, RingHom.map_det]
  congr 1
  ext a b
  simp [pderiv_map]

end MvPolynomial

/-! ### The standard-étale criterion -/

namespace Algebra

/-- **A square family of polynomials with invertible Jacobian determinant presents an étale
algebra.**  If `g : κ → R[x_k : k ∈ κ]` is a family of polynomials indexed by the variables, with
`κ` finite, whose Jacobian determinant is invertible in `R[x] ⧸ (g)`, then `R[x] ⧸ (g)` is étale
over `R`.  This is the direction of Stacks 00U9 used to recognise a standard-étale presentation,
via `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`. -/
@[sga "1 I 7.4" "(F)"]
theorem etale_mvPolynomialQuotient_of_isUnit_det {R : Type u} [CommRing R] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (g : κ → MvPolynomial κ R)
    (hg : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g))) :
    Algebra.Etale R (MvPolynomial κ R ⧸ Ideal.span (Set.range g)) := by
  have hmat : (PreSubmersivePresentation.naive (v := g) (R := R) _root_.id
      Function.injective_id).jacobiMatrix = Matrix.of fun a b ↦ pderiv a (g b) := by
    ext a b
    simp [PreSubmersivePresentation.jacobiMatrix_naive]
  have hjac : (PreSubmersivePresentation.naive (v := g) (R := R) _root_.id
      Function.injective_id).jacobian
      = Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g) := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hmat, detJacobian]
    rfl
  have : IsStandardSmoothOfRelativeDimension 0 R (MvPolynomial κ R ⧸ Ideal.span (Set.range g)) :=
    SubmersivePresentation.isStandardSmoothOfRelativeDimension
      { __ := PreSubmersivePresentation.naive (v := g) _root_.id Function.injective_id
        jacobian_isUnit := hjac ▸ hg } (by simp [Presentation.dimension])
  infer_instance

end Algebra

/-! ### Descending the presentation to a stage -/

namespace MvPolynomial

variable {ι : Type u} [Preorder ι] {G : ι → Type v} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} {A : Type w} [CommRing A] {φ : ∀ i, G i →+* A}

/-- **Invertibility of the Jacobian determinant descends to a stage.**  Let `g` be a square family
of polynomials over a stage `G i` of a directed system with colimit `A`.  If the Jacobian
determinant of the image family over `A` is invertible in `A[x] ⧸ (g)`, then at some later stage
`j` the Jacobian determinant of the image family over `G j` is already invertible in
`G j[x] ⧸ (g)`. -/
theorem exists_ge_isUnit_detJacobian_of_directed [IsDirectedOrder ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    {κ : Type*} [Fintype κ] [DecidableEq κ] {i : ι} (g : κ → MvPolynomial κ (G i))
    (hg : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range fun k ↦ map (φ i) (g k)))
      (detJacobian fun k ↦ map (φ i) (g k)))) :
    ∃ (j : ι) (h : i ≤ j), IsUnit (Ideal.Quotient.mk
      (Ideal.span (Set.range fun k ↦ map (f i j h) (g k)))
      (detJacobian fun k ↦ map (f i j h) (g k))) := by
  rw [← map_detJacobian] at hg
  obtain ⟨j, hij, hj⟩ :=
    exists_ge_isUnit_quotientMk_of_directed hφ hsurj hzero g (detJacobian g) hg
  exact ⟨j, hij, by rwa [map_detJacobian] at hj⟩

/-- **A standard-étale presentation over a directed colimit of rings descends to a stage.**  Let
`(G i)` be a directed system of rings with colimit `A` and let `B = A[x_k : k ∈ κ] ⧸ (g_k)` be a
standard-étale presentation, with `κ` finite and the Jacobian determinant invertible in `B`, whose
relations are the images of polynomials `g` over a stage `G i`.  Then at some later stage `j` the
family of images of `g` over `G j` again has invertible Jacobian determinant, and so presents an
étale `G j`-algebra. -/
theorem exists_ge_etale_quotient_of_directed [IsDirectedOrder ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    {κ : Type*} [Fintype κ] [DecidableEq κ] {i : ι} (g : κ → MvPolynomial κ (G i))
    (hg : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range fun k ↦ map (φ i) (g k)))
      (detJacobian fun k ↦ map (φ i) (g k)))) :
    ∃ (j : ι) (h : i ≤ j), Algebra.Etale (G j)
      (MvPolynomial κ (G j) ⧸ Ideal.span (Set.range fun k ↦ map (f i j h) (g k))) := by
  obtain ⟨j, hij, hj⟩ :=
    exists_ge_isUnit_detJacobian_of_directed hφ hsurj hzero g hg
  exact ⟨j, hij, Algebra.etale_mvPolynomialQuotient_of_isUnit_det _ hj⟩

/-- **Every polynomial relation over a directed colimit comes from a stage.**  Restated for a
square family, this is the first step of the descent: the `κ` polynomials `g_k` cutting out `B`
are the images of `κ` polynomials over a single stage, which may be taken above any prescribed
stage. -/
theorem exists_ge_forall_map_eq_square_of_directed [IsDirectedOrder ι] [Nonempty ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    {κ : Type*} [Finite κ] (g : κ → MvPolynomial κ A) (i₀ : ι) :
    ∃ (j : ι) (_ : i₀ ≤ j) (q : κ → MvPolynomial κ (G j)), ∀ k, map (φ j) (q k) = g k :=
  exists_ge_forall_map_eq_of_directed hφ hsurj g i₀

end MvPolynomial

/-! ### Base change of a finitely presented quotient of a polynomial ring -/

namespace Algebra

/-- **Base change of a quotient of a polynomial ring.**  For a commutative ring `R`, an `R`-algebra
`T` and a family `v` of polynomials over `R`, the base change to `T` of `R[x] ⧸ (v)` is
`T[x] ⧸ (v)`, where the relations are read as polynomials over `T`.  This is Mathlib's base change
of the naive presentation. -/
noncomputable def tensorQuotientSpanEquiv (R : Type u) [CommRing R] (T : Type v) [CommRing T]
    [Algebra R T] {ιp : Type*} {σ : Type*} (v : ιp → MvPolynomial σ R) :
    T ⊗[R] (MvPolynomial σ R ⧸ Ideal.span (Set.range v))
      ≃ₐ[T] MvPolynomial σ T ⧸
        Ideal.span (Set.range fun k ↦ MvPolynomial.map (algebraMap R T) (v k)) :=
  (AlgEquiv.restrictScalars T
      ((Presentation.naive (v := v)).baseChange T).quotientEquiv).symm.trans
    (Ideal.quotientEquivAlgOfEq T
      ((Presentation.naive (v := v)).baseChange T).span_range_relation_eq_ker.symm)

/-- `Algebra.tensorQuotientSpanEquiv` is the natural map: its inverse sends the class of a
polynomial `p` over `T` to `p` evaluated at the elements `1 ⊗ x_s`. -/
theorem tensorQuotientSpanEquiv_symm_mk (R : Type u) [CommRing R] (T : Type v) [CommRing T]
    [Algebra R T] {ιp : Type*} {σ : Type*} (v : ιp → MvPolynomial σ R) (p : MvPolynomial σ T) :
    (tensorQuotientSpanEquiv R T v).symm (Ideal.Quotient.mk _ p) =
      MvPolynomial.aeval
        (fun s ↦ (1 : T) ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range v)) (MvPolynomial.X s))
        p :=
  rfl

end Algebra

namespace MvPolynomial

variable {ι : Type u} [Preorder ι] {G : ι → Type v} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} {A : Type w} [CommRing A] {φ : ∀ i, G i →+* A}

/-- **The presentation at a later stage is the base change of the presentation at an earlier one.**
For `i ≤ j` in a directed system of rings and a family `g` of polynomials over `G i`, the quotient
`G j[x] ⧸ (g)` is the base change of `G i[x] ⧸ (g)` along the transition map `G i → G j`. -/
theorem nonempty_quotientSpanEquiv_tensor_of_le {κ : Type*} {σ : Type*} {i j : ι} (h : i ≤ j)
    (g : κ → MvPolynomial σ (G i)) :
    letI := (f i j h).toAlgebra
    Nonempty ((G j) ⊗[G i] (MvPolynomial σ (G i) ⧸ Ideal.span (Set.range g))
      ≃ₐ[G j] MvPolynomial σ (G j) ⧸ Ideal.span (Set.range fun k ↦ map (f i j h) (g k))) :=
  letI := (f i j h).toAlgebra
  ⟨Algebra.tensorQuotientSpanEquiv (G i) (G j) g⟩

/-- **Surjectivity on spectra descends to a stage, for the presentation at that stage.**  Let
`(G i)` be a directed system of rings with colimit `A`, let `g` be a finite family of polynomials
over a stage `G i` in finitely many variables, and let `D` be a ring with ring maps `χ : A → D` and
`θ : G i[x] ⧸ (g) → D` making the square commute.  If `Spec D → Spec A` is surjective, then
`Spec (G j[x] ⧸ (g)) → Spec (G j)` is surjective for some `j ≥ i`.

This is part (4) of the commutative-algebra core of Stacks 07SQ, in the presented form in which
the source states it: `D` is the coordinate ring `B` of the étale chart over the limit and
`G i[x] ⧸ (g)` its model `B_i` at the stage `i`.  It combines
`PrimeSpectrum.exists_ge_surjective_comap_tensorProduct_of_directed`, which produces the stage,
with `nonempty_quotientSpanEquiv_tensor_of_le`, which identifies the base change with the
presentation at that stage. -/
theorem exists_ge_surjective_comap_quotient_of_directed [IsDirectedOrder ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    {κ : Type*} [Finite κ] {i : ι} (g : κ → MvPolynomial κ (G i))
    {D : Type*} [CommRing D] (χ : A →+* D)
    (θ : (MvPolynomial κ (G i) ⧸ Ideal.span (Set.range g)) →+* D)
    (hcomm : χ.comp (φ i) =
      θ.comp (algebraMap (G i) (MvPolynomial κ (G i) ⧸ Ideal.span (Set.range g))))
    (hD : Function.Surjective (PrimeSpectrum.comap χ)) :
    ∃ (j : ι) (h : i ≤ j), Function.Surjective (PrimeSpectrum.comap
      (algebraMap (G j) (MvPolynomial κ (G j) ⧸
        Ideal.span (Set.range fun k ↦ map (f i j h) (g k))))) := by
  have hfp : (algebraMap (G i)
      (MvPolynomial κ (G i) ⧸ Ideal.span (Set.range g))).FinitePresentation := by
    rw [RingHom.finitePresentation_algebraMap]
    exact (Algebra.Presentation.naive (v := g)).finitePresentation_of_isFinite
  obtain ⟨j, hij, hs⟩ := PrimeSpectrum.exists_ge_surjective_comap_tensorProduct_of_directed
    hφ hsurj hzero hfp χ θ hcomm hD
  obtain ⟨e⟩ := nonempty_quotientSpanEquiv_tensor_of_le hij g
  exact ⟨j, hij, PrimeSpectrum.surjective_comap_algebraMap_of_algEquiv e hs⟩

omit [Preorder ι] in
/-- **The presentation over the colimit is the base change of the presentation at a stage.**  For a
family `g` of polynomials over a stage `G i` of a directed system of rings with colimit `A`, the
quotient `A[x] ⧸ (g)` is the base change of `G i[x] ⧸ (g)` along the structure map `G i → A`. -/
theorem nonempty_quotientSpanEquiv_tensor_of_directed {κ : Type*} {σ : Type*} {i : ι}
    (g : κ → MvPolynomial σ (G i)) :
    letI := (φ i).toAlgebra
    Nonempty (A ⊗[G i] (MvPolynomial σ (G i) ⧸ Ideal.span (Set.range g))
      ≃ₐ[A] MvPolynomial σ A ⧸ Ideal.span (Set.range fun k ↦ map (φ i) (g k))) :=
  letI := (φ i).toAlgebra
  ⟨Algebra.tensorQuotientSpanEquiv (G i) A g⟩

end MvPolynomial

end
