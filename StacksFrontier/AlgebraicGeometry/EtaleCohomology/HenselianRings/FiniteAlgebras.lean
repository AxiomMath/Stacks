module

public import Mathlib.RingTheory.Henselian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.QuasiFinite

/-!
# Finite algebras over a henselian local ring

A finite algebra over a henselian local ring splits as a finite product of henselian local
rings, each of them again finite over the base. The factors are the quotients cut out by a
complete orthogonal family of idempotents, which exists because a finite algebra over a
henselian local ring lifts the idempotents of its reduction.

## Main results

* `exists_algEquiv_pi_henselianLocalRing_of_module_finite` gives the decomposition of a finite
  algebra into henselian local factors.

## Implementation notes

The finite product is represented by a `Pi` type over a finite index type, and the
decomposition is an equivalence of algebras over the base ring. The factors retain their finite
algebra structures over the base. Since the base ring and the algebra may live in different
universes, the idempotent lifting is performed after transporting the algebra through `ULift`.

## References

* [Stacks Project, Tag 03QJ](https://stacks.math.columbia.edu/tag/03QJ)
-/

@[expose] public section

universe u v


/-- A finite algebra over a henselian local ring is a finite product of
henselian local rings, each finite over the base. -/
@[stacks 03QJ,
  ega "IV 18.5.10" "R henselian local",
  ega "IV 18.5.9" "(ii) necessity",
  ega "IV 18.5.11" "(F), partial",
  ega "IV 18.6.7" "special case", sga "4 VIII 4.1" "(i), forward direction"]
theorem exists_algEquiv_pi_henselianLocalRing_of_module_finite
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ (ι : Type v) (_ : Finite ι) (B : ι → Type v)
      (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
      (_ : ∀ i, HenselianLocalRing (B i)),
      (∀ i, Module.Finite R (B i)) ∧ Nonempty (A ≃ₐ[R] ∀ i, B i) := by
  let A' := ULift.{u} A
  obtain ⟨n, e', hco', hloc'⟩ := exists_completeOrthogonalIdempotents_lift R A'
  let ι := ULift.{v} (Fin n)
  let e : ι → A := fun i => (e' i.down).down
  have hco : CompleteOrthogonalIdempotents e :=
    (CompleteOrthogonalIdempotents.equiv (Equiv.ulift : ι ≃ Fin n)).mpr
      (hco'.map (ULift.ringEquiv (R := A) |>.toRingHom))
  let B : ι → Type v := fun i => A ⧸ Ideal.span {1 - e i}
  have hhenselian (i : ι) : HenselianLocalRing (B i) := by
    let I' : Ideal A' := Ideal.span {1 - e' i.down}
    let I : Ideal A := Ideal.span {1 - e i}
    have hI : I = I'.map (ULift.ringEquiv : A' ≃+* A) := by
      simp only [I, I', Ideal.map_span, Set.image_singleton]
      congr 1
    have : IsLocalRing (A' ⧸ I') := hloc' i.down
    have : IsLocalRing (B i) :=
      (Ideal.quotientEquiv I' I (ULift.ringEquiv : A' ≃+* A) hI).isLocalRing
    exact (HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt.{u, v, v}
      (R := R)).2.1 (B i) inferInstance |>.1
  refine ⟨ι, inferInstance, B, inferInstance, inferInstance, hhenselian,
    fun _ => inferInstance, ?_⟩
  let φ : A →ₐ[R] (∀ i, B i) :=
    AlgHom.pi (fun i => Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))
  exact ⟨AlgEquiv.ofBijective φ (by convert hco.bijective_pi using 1; rfl)⟩

