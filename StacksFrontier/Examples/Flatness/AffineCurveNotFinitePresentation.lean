module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Flatness.FiniteFlatNonprojectiveQuotient
public import StacksFrontier.Examples.Flatness.NodalAlgebra
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.GeometricallyConnected.Defs

/-!
# A flat family of complete-intersection curves not of finite presentation

There is a flat ring map of finite type, not of finite presentation, all of whose fibres are
geometrically connected and geometrically reduced one-dimensional complete intersections.

The family is the affine nodal algebra `R[x, y]/(xy, ay : a ∈ I)` for a ring `R` and an
ideal `I` which is pure but not finitely generated: flatness and the failure of finite
presentation are exactly the two properties of that algebra. Its fibres are the node
`k[x, y]/(xy)` and the affine line `k[x]`, and both have the four stated properties.

## Main results

* `Stacks.Examples.exists_flat_finiteType_not_finitePresentation_of_curve_fibers`: such a
  ring map exists.

## References

* [Stacks Project, Tag 05LC](https://stacks.math.columbia.edu/tag/05LC)
-/

@[expose] public section

namespace Stacks.Examples

universe u v

open MvPolynomial
open scoped TensorProduct

/-- The affine nodal curve `k[x, y]/(xy)` over a commutative ring `k`. -/
private abbrev node (k : Type*) [CommRing k] :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span ({X 0 * X 1} : Set (MvPolynomial (Fin 2) k))

/-- Over a domain the node is reduced. -/
private theorem isReduced_node (k : Type*) [CommRing k] [IsDomain k] : IsReduced (node k) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  rintro f ⟨n, hn⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  have h0 : X (0 : Fin 2) ∣ f :=
    X_prime.dvd_of_dvd_pow ((dvd_mul_right _ _).trans hn)
  have h1 : X (1 : Fin 2) ∣ f :=
    X_prime.dvd_of_dvd_pow ((dvd_mul_left _ _).trans hn)
  obtain ⟨g, rfl⟩ := h0
  have hg : X (1 : Fin 2) ∣ g := (X_prime.dvd_mul.mp h1).resolve_left (by simp [X_dvd_X])
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h, (mul_assoc _ _ _).symm⟩

/-- The spectrum of the node over a domain is connected. -/
private theorem connectedSpace_primeSpectrum_node (k : Type*) [CommRing k] [IsDomain k] :
    ConnectedSpace (PrimeSpectrum (node k)) := by
  have hp (i : Fin 2) : (Ideal.span ({X i} : Set (MvPolynomial (Fin 2) k))).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero i)).mpr X_prime
  have hc (i : Fin 2) :
      IsConnected (PrimeSpectrum.zeroLocus ({X i} : Set (MvPolynomial (Fin 2) k))) := by
    rw [← PrimeSpectrum.zeroLocus_span]
    exact ((PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _
      (hp i).isRadical).mpr (hp i)).isConnected
  have hi : (PrimeSpectrum.zeroLocus ({X 0} : Set (MvPolynomial (Fin 2) k)) ∩
      PrimeSpectrum.zeroLocus {X 1}).Nonempty := by
    refine ⟨⟨RingHom.ker (constantCoeff : MvPolynomial (Fin 2) k →+* k),
      RingHom.ker_isPrime _⟩, ?_, ?_⟩ <;>
      simp [PrimeSpectrum.mem_zeroLocus, RingHom.mem_ker]
  let q := Ideal.Quotient.mk (Ideal.span ({X 0 * X 1} : Set (MvPolynomial (Fin 2) k)))
  let e := (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (node k) q
    Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph
  refine e.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp ?_)
  rw [range_comap_of_surjective _ q Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_singleton_mul]
  exact IsConnected.union hi (hc 0) (hc 1)

/-- The node over a field has Krull dimension one. -/
private theorem ringKrullDim_node (k : Type*) [Field k] : ringKrullDim (node k) = 1 := by
  have hu := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (R := MvPolynomial (Fin 2) k) (r := X 0 * X 1)
    (mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero (X_ne_zero _) (X_ne_zero _)))
  have hu' : ringKrullDim (node k) + 1 ≤ 2 := by
    simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] using hu
  let f : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
    aeval (fun i => if i = 0 then Polynomial.X else 0)
  have hf : Function.Surjective f := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨p, rfl⟩ := hp
      obtain ⟨q, rfl⟩ := hq
      exact ⟨p + q, map_add f p q⟩
    | monomial n a =>
      refine ⟨C a * X 0 ^ n, ?_⟩
      simp [f, Polynomial.C_mul_X_pow_eq_monomial]
  have hker : Ideal.span ({X 0 * X 1} : Set (MvPolynomial (Fin 2) k)) ≤ RingHom.ker f := by
    rw [Ideal.span_le]
    simp [Set.singleton_subset_iff, RingHom.mem_ker, f]
  let g := Ideal.Quotient.liftₐ _ f hker
  have hg : Function.Surjective g := by
    intro p
    obtain ⟨q, rfl⟩ := hf p
    exact ⟨Ideal.Quotient.mk _ q, rfl⟩
  have hl : 1 ≤ ringKrullDim (node k) := by
    simpa [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] using
      ringKrullDim_le_of_surjective g.toRingHom hg
  exact le_antisymm (ENat.WithBot.add_le_add_one_right_iff.mp (by convert hu' using 1; norm_num)) hl

/-- The node is stable under base change of the coefficients. -/
private noncomputable def nodeTensorEquiv (k K : Type*) [CommRing k] [CommRing K]
    [Algebra k K] : K ⊗[k] node k ≃ₐ[K] node K :=
  (Algebra.TensorProduct.tensorQuotientEquiv K (MvPolynomial (Fin 2) k) K _).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv k K) (by
      simp only [Ideal.map_span, Set.image_singleton]
      simp [Algebra.TensorProduct.includeRight_apply]))

/-- The node over a field is a global complete intersection. -/
private theorem isGlobalCompleteIntersection_node (k : Type*) [Field k] :
    IsGlobalCompleteIntersection k (node k) := by
  refine .inr ⟨2, 1, (fun _ => X 0 * X 1), ?_, by decide, ?_⟩
  · exact Ideal.quotientEquivAlgOfEq k (by simp [Set.range_const])
  · simpa using ringKrullDim_node k

/-- The affine line over a field is a global complete intersection. -/
private theorem isGlobalCompleteIntersection_polynomial (k : Type*) [Field k] :
    IsGlobalCompleteIntersection k (Polynomial k) := by
  refine .inr ⟨1, 0, (fun i => Fin.elim0 i), ?_, by decide, ?_⟩
  · exact (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.trans
      ((AlgEquiv.quotientBot k (MvPolynomial (Fin 1) k)).symm.trans
        (Ideal.quotientEquivAlgOfEq k (by simp)))
  · simp [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]

/-- Connectedness of the spectrum and reducedness transport along a ring equivalence. -/
private theorem connectedSpace_and_isReduced_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : ConnectedSpace (PrimeSpectrum B) ∧ IsReduced B) :
    ConnectedSpace (PrimeSpectrum A) ∧ IsReduced A := by
  have := h.2
  exact ⟨(PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr h.1,
    isReduced_of_injective e e.injective⟩

/-- The four fibre properties transport along an algebra equivalence, given connectedness
and reducedness of every base change of the model. -/
private theorem fiber_properties_of_equiv (k : Type u) (A B : Type*) [Field k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (h : ∀ (K : Type u) [Field K] [Algebra k K],
      ConnectedSpace (PrimeSpectrum (K ⊗[k] B)) ∧ IsReduced (K ⊗[k] B))
    (hd : ringKrullDim B = 1) (hg : IsGlobalCompleteIntersection k B) :
    Algebra.IsGeometricallyConnected k A ∧ Algebra.IsGeometricallyReduced k A ∧
      ringKrullDim A = 1 ∧ IsGlobalCompleteIntersection k A := by
  have he (K : Type u) [Field K] [Algebra k K] := connectedSpace_and_isReduced_of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e).toRingEquiv (h K)
  refine ⟨⟨fun K _ _ => (he K).1⟩, ?_, ?_, ?_⟩
  · rw [Algebra.isGeometricallyReduced_field_iff]
    exact (he _).2
  · exact e.toRingEquiv.ringKrullDim.trans hd
  · exact gci_transport k e.symm hg

/-- An algebra equivalent to the node has the four fibre properties. -/
private theorem node_fiber_properties (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] node k) :
    Algebra.IsGeometricallyConnected k A ∧ Algebra.IsGeometricallyReduced k A ∧
      ringKrullDim A = 1 ∧ IsGlobalCompleteIntersection k A := by
  refine fiber_properties_of_equiv k A (node k) e (fun K _ _ => ?_) (ringKrullDim_node k)
    (isGlobalCompleteIntersection_node k)
  have := isReduced_node K
  have := connectedSpace_primeSpectrum_node K
  exact connectedSpace_and_isReduced_of_ringEquiv (nodeTensorEquiv k K).toRingEquiv ⟨‹_›, ‹_›⟩

/-- An algebra equivalent to the affine line has the four fibre properties. -/
private theorem polynomial_fiber_properties (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] Polynomial k) :
    Algebra.IsGeometricallyConnected k A ∧ Algebra.IsGeometricallyReduced k A ∧
      ringKrullDim A = 1 ∧ IsGlobalCompleteIntersection k A := by
  refine fiber_properties_of_equiv k A (Polynomial k) e (fun K _ _ => ?_)
    (by simp [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field])
    (isGlobalCompleteIntersection_polynomial k)
  exact connectedSpace_and_isReduced_of_ringEquiv (polyEquivTensor' k K).symm.toRingEquiv
    ⟨inferInstance, inferInstance⟩

/-- The nodal relation ideal transports along an algebra equivalence of base rings. -/
private theorem nodalRelationIdeal_map (k R S : Type*) [CommRing k] [CommRing R]
    [CommRing S] [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S)
    (I : Ideal R) (J : Ideal S) (h : J = I.map e) :
    nodalRelationIdeal S J =
      (nodalRelationIdeal R I).map (MvPolynomial.mapAlgEquiv (Fin 2) e) := by
  unfold nodalRelationIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨X 0 * X 1, Or.inl rfl, by simp⟩
    · have hj : (j : S) ∈ I.map e := h ▸ j.property
      obtain ⟨i, hi, he⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).mp hj
      exact ⟨C i * X 1, Or.inr ⟨⟨i, hi⟩, rfl⟩, by simp [he]⟩
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | ⟨i, rfl⟩
    · exact Or.inl (by simp)
    · exact Or.inr ⟨⟨e i, h.symm ▸ Ideal.mem_map_of_mem e i.property⟩, by simp⟩

/-- The affine nodal algebra transports along an algebra equivalence of base rings. -/
private noncomputable def nodalAlgebra_congr (k R S : Type*) [CommRing k] [CommRing R]
    [CommRing S] [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S)
    (I : Ideal R) (J : Ideal S) (h : J = I.map e) :
    nodalAlgebra R I ≃ₐ[k] nodalAlgebra S J :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.mapAlgEquiv (Fin 2) e)
    (nodalRelationIdeal_map k R S e I J h)

/-- A flat algebra of finite type with geometrically
connected and geometrically reduced one-dimensional complete-intersection fibres need not be
of finite presentation. -/
@[stacks 05LC "(2)"]
theorem exists_flat_finiteType_not_finitePresentation_of_curve_fibers :
    ∃ (R : Type u) (A : Type v) (_ : CommRing R) (_ : CommRing A)
      (_ : Algebra R A),
      Module.Flat R A ∧ Algebra.FiniteType R A ∧ ¬ Algebra.FinitePresentation R A ∧
        (∀ (p : Ideal R) [p.IsPrime],
          Algebra.IsGeometricallyConnected p.ResidueField (p.Fiber A) ∧
          Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber A) ∧
          ringKrullDim (p.Fiber A) = 1 ∧
          IsGlobalCompleteIntersection p.ResidueField (p.Fiber A)) := by
  classical
  obtain ⟨D⟩ := nonempty_finiteFlatNonprojectiveQuotient.{0}
  let R := ULift.{u} D.R
  let A := ULift.{v} (nodalAlgebra D.R D.I)
  let : Algebra R D.R := ULift.algebra' D.R D.R
  let e : R ≃ₐ[R] D.R := { ULift.ringEquiv with commutes' := fun _ => rfl }
  let I := D.I.comap e
  have hI : D.I = I.map e := (Ideal.map_comap_of_surjective e e.surjective D.I).symm
  let eQ : (R ⧸ I) ≃ₐ[R] (D.R ⧸ D.I) := Ideal.quotientEquivAlg I D.I e hI
  have : Module.Flat R D.R := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  have := D.flat
  have : Module.Flat R (D.R ⧸ D.I) := Module.Flat.trans R D.R (D.R ⧸ D.I)
  have hflatI : Module.Flat R (R ⧸ I) := Module.Flat.of_linearEquiv eQ.toLinearEquiv
  have hnfg : ¬ I.FG := fun h ↦ D.not_fg (hI ▸ h.map e.toRingHom)
  let eA : nodalAlgebra R I ≃ₐ[R] A :=
    (nodalAlgebra_congr R R D.R e I D.I hI).trans ULift.algEquiv.symm
  have := nodalAlgebra_flat R I hflatI
  have hnotfp := nodalAlgebra_not_finitePresentation R I hnfg
  refine ⟨R, A, inferInstance, inferInstance, inferInstance,
    Module.Flat.of_linearEquiv eA.symm.toLinearEquiv,
    Algebra.FiniteType.of_surjective eA.toAlgHom eA.surjective, ?_, ?_⟩
  · exact fun _ ↦ hnotfp (Algebra.FinitePresentation.equiv eA.symm)
  · intro p hp
    let ef : p.Fiber A ≃ₐ[p.ResidueField] p.Fiber (nodalAlgebra R I) :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] _) eA.symm
    rcases nodalAlgebra_fiber R I p with hn | hl
    · obtain ⟨en⟩ := hn
      exact node_fiber_properties p.ResidueField (p.Fiber A) (ef.trans en)
    · obtain ⟨el⟩ := hl
      exact polynomial_fiber_properties p.ResidueField (p.Fiber A) (ef.trans el)

end Stacks.Examples
