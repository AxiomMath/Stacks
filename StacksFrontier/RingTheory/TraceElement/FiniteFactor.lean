module

public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement

/-!
# Finite direct factors of a quasi-finite algebra

Let `A → C → B` be a finite-open factorization. This file records two facts about it that the
theory of trace elements uses constantly.

The first is that `B` is flat over the intermediate algebra `C`. This is a local statement:
`Spec B → Spec C` is an open immersion, so `Spec B` is covered by basic opens of `C` over which
the map is an away localization, and flatness is local on a spanning set of the target.

The second concerns a decomposition `B ≃ C₁ × D` of the target over a Noetherian base, with
`C₁` finite over the base. Such a factor is a retract of `B`, hence flat; being finitely
presented it is projective, and the same argument over the intermediate algebra makes it
finite projective there. That is exactly the data the restriction map to a finite factor
requires.

## Main results

* `Stacks.Discriminant.flat_of_finiteOpenFactorization`: the target of a finite-open
  factorization is flat over the intermediate algebra.
* `Stacks.Discriminant.flat_of_prodRingEquiv`: a direct factor of a flat algebra on which the
  base acts through the decomposition is flat.
* `Stacks.Discriminant.projective_of_prodEquiv_baseChange`: a finite direct factor of a
  scalar extension of a flat algebra over a Noetherian base is projective.
* `Stacks.Discriminant.projective_of_prodEquiv_of_finite`: the same conclusion for a direct
  factor of an algebra that is finite over a Noetherian base through the decomposition.
* `Stacks.Discriminant.finite_and_projective_of_prodEquiv_middle`: a finite direct factor of
  the target is finite projective over the intermediate algebra of a factorization.

## References

* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
-/

@[expose] public section

open Topology
open scoped TensorProduct

namespace Stacks.Discriminant

/-- The basic opens of the source contained in the image of an open embedding of spectra, and
indexed by elements of the source, generate the unit ideal of the target: they cover it. -/
theorem exists_finset_principal_cover {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (hopen : IsOpenEmbedding (PrimeSpectrum.comap (algebraMap R B))) :
    ∃ s : Finset {g : R // (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap R B))},
      Ideal.span (Set.range fun g : s => algebraMap R B g.1) = ⊤ := by
  classical
  let V := {g : R // (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
    Set.range (PrimeSpectrum.comap (algebraMap R B))}
  let U : V → Set (PrimeSpectrum B) := fun g =>
    (PrimeSpectrum.comap (algebraMap R B)) ⁻¹' PrimeSpectrum.basicOpen g.1
  have hUopen (g : V) : IsOpen (U g) :=
    (PrimeSpectrum.basicOpen g.1).2.preimage (PrimeSpectrum.continuous_comap (algebraMap R B))
  have hUcover (q : PrimeSpectrum B) : ∃ g : V, q ∈ U g := by
    have hp : PrimeSpectrum.comap (algebraMap R B) q ∈
        Set.range (PrimeSpectrum.comap (algebraMap R B)) := ⟨q, rfl⟩
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hsubset⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp hopen.isOpen_range
    exact ⟨⟨g, hsubset⟩, by simpa [U] using hpg⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen
    (fun q _ => Set.mem_iUnion.mpr (hUcover q))
  refine ⟨s, ?_⟩
  by_contra hone
  obtain ⟨m, hmmax, hm⟩ := Ideal.exists_le_maximal _ hone
  let q : PrimeSpectrum B := ⟨m, hmmax.isPrime⟩
  obtain ⟨g, hgs, hqg⟩ : ∃ g ∈ s, q ∈ U g := by
    simpa only [Set.mem_iUnion, exists_prop] using hs (Set.mem_univ q)
  have hgnm : algebraMap R B g.1 ∉ q.asIdeal := by
    simpa [U, PrimeSpectrum.comap_asIdeal] using hqg
  exact hgnm (hm (Ideal.subset_span ⟨⟨g, hgs⟩, rfl⟩))

/-- **The target of a finite-open factorization is flat over the intermediate algebra.** The
spectrum of the target is covered by basic opens of the intermediate algebra over which the
map is an away localization, and flatness is local on such a cover. -/
theorem flat_of_finiteOpenFactorization {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (F : FiniteOpenFactorization A B) : Module.Flat F.middle B := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_principal_cover F.isOpenEmbedding_comap
  refine Module.flat_of_isLocalized_span B B (Set.range fun g : s => algebraMap F.middle B g.1)
    hs (fun r => Localization.Away r.1) (fun r => Algebra.linearMap B (Localization.Away r.1)) ?_
  rintro ⟨r, g, rfl⟩
  let e : Localization.Away g.1.1 ≃ₐ[F.middle]
      Localization.Away (algebraMap F.middle B g.1.1) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId F.middle B) g.1.1)
      (F.awayMap_bijective g.1.1 g.1.2)
  have := IsLocalization.isLocalization_of_algEquiv (Submonoid.powers g.1.1) e
  exact IsLocalization.flat _ (Submonoid.powers g.1.1)

/-- A direct factor of a flat algebra is flat, provided the base acts on the factor through
the decomposition. The factor is a retract of the algebra as a module over the base. -/
theorem flat_of_prodRingEquiv {R S C D : Type*}
    [CommRing R] [CommRing S] [CommRing C] [CommRing D] [Algebra R S] [Algebra R C]
    [Module.Flat R S] (e : S ≃+* C × D)
    (h : ∀ r : R, (e (algebraMap R S r)).1 = algebraMap R C r) : Module.Flat R C := by
  let p : S →ₗ[R] C :=
    { toFun := fun s => (e s).1
      map_add' _ _ := by simp
      map_smul' _ _ := by simp [Algebra.smul_def, h] }
  let i : C →ₗ[R] S :=
    { toFun := fun c => e.symm (c, 0)
      map_add' _ _ := by simp [← map_add]
      map_smul' := by
        intro r c
        refine e.injective ?_
        simp only [RingEquiv.apply_symm_apply, Algebra.smul_def, map_mul]
        ext <;> simp [h] }
  exact Module.Flat.of_retract i p (by ext; simp [p, i])

/-- A finite flat module over a Noetherian ring is projective. -/
private theorem projective_of_flat_of_finite {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [IsNoetherianRing R] [Module.Finite R M] [Module.Flat R M] :
    Module.Projective R M :=
  have := Module.finitePresentation_of_finite R M
  Module.Flat.projective_of_finitePresentation

/-- A finite direct factor of a scalar extension of a flat algebra over a Noetherian base is
projective: it is a retract of the extension, hence flat, and finitely presented. -/
theorem projective_of_prodEquiv_baseChange {R S B C D : Type*}
    [CommRing R] [CommRing S] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R B] [IsNoetherianRing S] [Algebra S C] [Algebra S D]
    [Module.Flat R B] (e : (S ⊗[R] B) ≃ₐ[S] (C × D)) (hfinite : Module.Finite S C) :
    Module.Projective S C := by
  let : Algebra S (S ⊗[R] B) := Algebra.TensorProduct.leftAlgebra
  have : Module.Flat S (C × D) := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  have : Module.Flat S C :=
    Module.Flat.of_retract (LinearMap.inl S C D) (LinearMap.fst S C D) (by ext x; rfl)
  exact projective_of_flat_of_finite

/-- A direct factor of a flat algebra over an intermediate ring is projective over that ring,
when the whole is finite over a Noetherian base below it. -/
theorem projective_of_prodEquiv_of_finite {A R T C D : Type*}
    [CommRing A] [CommRing R] [CommRing T] [CommRing C] [CommRing D]
    [Algebra A R] [Algebra A T] [Algebra R T] [IsScalarTower A R T]
    [Algebra A C] [Algebra R C] [IsScalarTower A R C]
    [Algebra A D] [Algebra R D] [IsScalarTower A R D]
    [IsNoetherianRing A] [Module.Finite A R] [Module.Finite A C] [Module.Flat R T]
    (e : T ≃ₐ[A] C × D)
    (hcompat : ∀ r : R, e (algebraMap R T r) = (algebraMap R C r, algebraMap R D r)) :
    Module.Projective R C := by
  have : Module.Flat R C := flat_of_prodRingEquiv e.toRingEquiv fun r => by simp [hcompat]
  have : Module.Finite R C := Module.Finite.of_restrictScalars_finite A R C
  have : IsNoetherianRing R := IsNoetherianRing.of_finite A R
  exact projective_of_flat_of_finite

/-- A finite direct factor of the target of a finite-open factorization is finite projective
over the intermediate algebra. Finiteness comes from finiteness over the Noetherian base and
projectivity from flatness of the target over the intermediate algebra. -/
theorem finite_and_projective_of_prodEquiv_middle {S B C D : Type*}
    [CommRing S] [CommRing B] [CommRing C] [CommRing D] [IsNoetherianRing S]
    [Algebra S B] [Algebra S C] [Algebra S D] (F : FiniteOpenFactorization S B)
    (e : B ≃ₐ[S] (C × D)) [Algebra F.middle C]
    (hcompat : ∀ a : F.middle, algebraMap F.middle C a = (e (algebraMap F.middle B a)).1)
    (hfinite : Module.Finite S C) :
    Module.Finite F.middle C ∧ Module.Projective F.middle C := by
  classical
  have : Module.Flat F.middle B := flat_of_finiteOpenFactorization F
  have : IsScalarTower S F.middle C := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun s => by
    calc
      algebraMap S C s = (e (algebraMap S B s)).1 := by rw [e.commutes]; rfl
      _ = (e (algebraMap F.middle B (algebraMap S F.middle s))).1 := by
        rw [IsScalarTower.algebraMap_apply S F.middle B s]
      _ = algebraMap F.middle C (algebraMap S F.middle s) := (hcompat _).symm)
  have : Module.Finite S F.middle := F.finite_middle
  have hfiniteM : Module.Finite F.middle C := Module.Finite.of_restrictScalars_finite S F.middle C
  have : IsNoetherianRing F.middle := IsNoetherianRing.of_finite S F.middle
  have : Module.Flat F.middle C :=
    flat_of_prodRingEquiv e.toRingEquiv fun a => (hcompat a).symm
  exact ⟨hfiniteM, projective_of_flat_of_finite⟩

end Stacks.Discriminant

end
