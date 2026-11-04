module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Smooth.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Spectrum.Prime.Specialization

/-!
# Retractions of étale covers descend to quotient rings

If every faithfully flat étale algebra over a commutative ring `A` admits a retraction, then the
same holds over every quotient `A ⧸ I`.

## Main results

* `AlgebraicGeometry.ProEtale.etale_faithfullyFlat_retracts_quotient`: if every faithfully flat
  étale `A`-algebra admits an `A`-algebra map to `A`, then every faithfully flat étale
  `A ⧸ I`-algebra admits an `A ⧸ I`-algebra map to `A ⧸ I`.

## Implementation notes

A retraction of an algebra structure map is expressed by an algebra homomorphism back to the base
ring. The assertion quantifies over all faithfully flat étale algebras over the quotient, not only
those obtained by quotienting a fixed algebra over the original ring.

## References

* [Stacks Project, Tag 097U](https://stacks.math.columbia.edu/tag/097U)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- If every faithfully flat étale `A`-algebra `B` admits an `A`-algebra map `B → A`, then for
every ideal `I` of `A`, every faithfully flat étale `A ⧸ I`-algebra admits an `A ⧸ I`-algebra map
to `A ⧸ I`. -/
@[stacks 097U]
theorem etale_faithfullyFlat_retracts_quotient
    (A : Type u) [CommRing A]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
      [Module.FaithfullyFlat A B], Nonempty (B →ₐ[A] A))
    (I : Ideal A) :
    ∀ (B : Type u) [CommRing B] [Algebra (A ⧸ I) B]
      [Algebra.Etale (A ⧸ I) B] [Module.FaithfullyFlat (A ⧸ I) B],
      Nonempty (B →ₐ[A ⧸ I] A ⧸ I) := by
  classical
  intro B _ _ _ _
  let A' := A ⧸ I
  let : Algebra A B := ((algebraMap A' B).comp (algebraMap A A')).toAlgebra
  let : IsScalarTower A A' B := .of_algebraMap_eq fun _ => rfl
  obtain ⟨C, hCR, hCA, hCE, ψ, hψsurj, hψker⟩ :=
    etale_lift_along_surjection A A' B Ideal.Quotient.mk_surjective
  let : CommRing C := hCR
  let : Algebra A C := hCA
  let : Algebra.Etale A C := hCE
  have hψker' : RingHom.ker (ψ : C →+* B) = I.map (algebraMap A C) := by
    rw [hψker, show RingHom.ker (algebraMap A A') = I from Ideal.mk_ker]
  have hUopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap A C))) := by
    simpa using primeSpectrum_comap_isOpenMap_of_flat_of_finitePresentation A C
      (Set.univ : Set (PrimeSpectrum C)) isOpen_univ
  have hffB : (algebraMap A' B).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hsurjB : Function.Surjective (PrimeSpectrum.comap (algebraMap A' B)) :=
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hffB).2
  have hV : ∀ p : PrimeSpectrum A, (I : Set A) ⊆ p.asIdeal →
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A C)) := by
    intro p hp
    let q : PrimeSpectrum A' :=
      ⟨p.asIdeal.map (Ideal.Quotient.mk I),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
          rw [Ideal.mk_ker]
          exact hp)⟩
    have hq : PrimeSpectrum.comap (Ideal.Quotient.mk I) q = p := by
      apply PrimeSpectrum.ext
      show Ideal.comap (Ideal.Quotient.mk I)
        (p.asIdeal.map (Ideal.Quotient.mk I)) = p.asIdeal
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact sup_eq_left.mpr hp
    obtain ⟨qB, hqB⟩ := hsurjB q
    refine ⟨PrimeSpectrum.comap (ψ : C →+* B) qB, ?_⟩
    have hcomp : (ψ : C →+* B).comp (algebraMap A C) = algebraMap A B := ψ.comp_algebraMap
    calc
      PrimeSpectrum.comap (algebraMap A C) (PrimeSpectrum.comap (ψ : C →+* B) qB) =
          PrimeSpectrum.comap ((algebraMap A' B).comp (algebraMap A A')) qB := by
            rw [← PrimeSpectrum.comap_comp_apply, hcomp]
            rfl
      _ = PrimeSpectrum.comap (algebraMap A A')
            (PrimeSpectrum.comap (algebraMap A' B) qB) := by
            rw [PrimeSpectrum.comap_comp_apply]
      _ = PrimeSpectrum.comap (algebraMap A A') q := congrArg _ hqB
      _ = p := hq
  let Z : Set (PrimeSpectrum A) := (Set.range (PrimeSpectrum.comap (algebraMap A C)))ᶜ
  have hZcompact : IsCompact Z := hUopen.isClosed_compl.isCompact
  have hcover :
      Z ⊆ ⋃ f : I, (PrimeSpectrum.basicOpen (f : A) : Set (PrimeSpectrum A)) := by
    intro p hp
    obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp (show ¬ (I : Set A) ⊆ p.asIdeal from
      fun h => hp (hV p h))
    simp only [Set.mem_iUnion]
    exact ⟨⟨f, hfI⟩, (PrimeSpectrum.mem_basicOpen f p).mpr hfp⟩
  obtain ⟨s, hs⟩ := hZcompact.elim_finite_subcover
    (fun f : I => (PrimeSpectrum.basicOpen (f : A) : Set (PrimeSpectrum A)))
    (fun f => PrimeSpectrum.isOpen_basicOpen) hcover
  let f : s → I := fun i => i.1
  let E : Option s → Type u := fun j =>
    match j with
    | none => C
    | some i => Localization.Away (f i : A)
  let : ∀ j, CommRing (E j)
    | none => hCR
    | some _ => inferInstance
  let : ∀ j, Algebra A (E j)
    | none => hCA
    | some _ => inferInstance
  let D := ∀ j : Option s, E j
  let : Algebra A D := inferInstance
  let : Algebra.Etale A D := by
    let : ∀ j, Algebra.Etale A (E j)
      | none => hCE
      | some _ => inferInstance
    infer_instance
  have hDspec : Function.Surjective (PrimeSpectrum.comap (algebraMap A D)) := by
    intro p
    have hlift (j : Option s) (q : PrimeSpectrum (E j))
        (hq : PrimeSpectrum.comap (algebraMap A (E j)) q = p) :
        ∃ q' : PrimeSpectrum D, PrimeSpectrum.comap (algebraMap A D) q' = p := by
      refine ⟨PrimeSpectrum.comap (Pi.evalRingHom E j) q, ?_⟩
      show PrimeSpectrum.comap ((Pi.evalRingHom E j).comp (algebraMap A D)) q = p
      convert hq using 1
      ext a
      rfl
    by_cases hpU : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A C))
    · obtain ⟨q, hq⟩ := hpU
      exact hlift none q hq
    · have hpZ : p ∈ Z := hpU
      obtain ⟨j, hjmem, hj⟩ := Set.mem_iUnion₂.mp (hs hpZ)
      have hj' : p ∈ (PrimeSpectrum.basicOpen (f ⟨j, hjmem⟩ : A) : Set (PrimeSpectrum A)) := hj
      rw [← PrimeSpectrum.localization_away_comap_range
        (Localization.Away (f ⟨j, hjmem⟩ : A)) (f ⟨j, hjmem⟩ : A)] at hj'
      obtain ⟨q, hq⟩ := hj'
      exact hlift (some ⟨j, hjmem⟩) q hq
  have hDff : Module.FaithfullyFlat A D := RingHom.faithfullyFlat_algebraMap_iff.mp <|
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective).mpr
      ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, hDspec⟩
  obtain ⟨r⟩ := h D
  let φ : D →+* B := (ψ : C →+* B).comp (Pi.evalRingHom E none)
  have hφsurj : Function.Surjective φ := hψsurj.comp (Function.surjective_eval _)
  have hφker : RingHom.ker φ = I.map (algebraMap A D) := by
    let J : Ideal D := I.map (algebraMap A D)
    have hmap : ∀ j : Option s,
        J.map (Pi.evalRingHom E j) = I.map (algebraMap A (E j)) := by
      intro j
      rw [Ideal.map_map]
      congr 1
    have hJpi : J = Ideal.pi (fun j : Option s => J.map (Pi.evalRingHom E j)) := by
      apply (Ideal.piOrderIso (R := E)).injective
      funext j
      show J.map (Pi.evalRingHom E j) =
        (Ideal.pi (fun j : Option s => J.map (Pi.evalRingHom E j))).map
          (Pi.evalRingHom E j)
      rw [Ideal.map_evalRingHom_pi]
    have htop : ∀ i : s, J.map (Pi.evalRingHom E (some i)) = ⊤ := by
      intro i
      rw [hmap]
      exact Ideal.eq_top_of_isUnit_mem
        (I := Ideal.map (algebraMap A (Localization.Away (f i : A))) I)
        (Ideal.mem_map_of_mem (algebraMap A (Localization.Away (f i : A))) (f i).2)
        (IsLocalization.Away.algebraMap_isUnit (f i : A))
    ext x
    show ψ (x none) = 0 ↔ x ∈ J
    rw [hJpi, Ideal.mem_pi, Option.forall]
    simp only [htop, Submodule.mem_top, implies_true, and_true]
    simp [E, hmap, ← hψker', RingHom.mem_ker]
  let e : D ⧸ RingHom.ker φ ≃+* B := φ.quotientKerEquivOfSurjective hφsurj
  have hkill :
      RingHom.ker φ ≤ RingHom.ker ((Ideal.Quotient.mk I).comp (r : D →+* A)) := by
    rw [hφker, Ideal.map_le_iff_le_comap]
    intro a ha
    show Ideal.Quotient.mk I (r (algebraMap A D a)) = 0
    rw [r.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let rbar : D ⧸ RingHom.ker φ →+* A' :=
    Ideal.Quotient.lift (RingHom.ker φ)
      ((Ideal.Quotient.mk I).comp (r : D →+* A))
      (fun x hx => RingHom.mem_ker.mp (hkill hx))
  let g : B →+* A' := rbar.comp e.symm.toRingHom
  have hg : ∀ a : A, g (algebraMap A B a) = Ideal.Quotient.mk I a := by
    intro a
    have he : e.symm (algebraMap A B a) =
        Ideal.Quotient.mk (RingHom.ker φ) (algebraMap A D a) := by
      rw [show algebraMap A B a = φ (algebraMap A D a) from (ψ.commutes a).symm]
      exact RingHom.quotientKerEquivOfSurjective_symm_apply hφsurj _
    show rbar (e.symm (algebraMap A B a)) = Ideal.Quotient.mk I a
    rw [he]
    show Ideal.Quotient.mk I (r (algebraMap A D a)) = _
    simp [r.commutes]
  exact ⟨{ toRingHom := g, commutes' := Ideal.Quotient.mk_surjective.forall.2 hg }⟩

end AlgebraicGeometry.ProEtale

end
