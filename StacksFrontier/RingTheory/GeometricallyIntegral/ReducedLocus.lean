module

public import Mathlib.RingTheory.FiniteStability
public import StacksFrontier.RingTheory.GeometricallyIntegral.OpenLocus
public import StacksFrontier.RingTheory.GeometricallyReduced.SeparableBaseChange
public import StacksFrontier.Topology.Constructible.InConstructible
public import StacksFrontier.Topology.Noetherian.ConstructibleDichotomy
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The geometrically reduced fibre locus over an integral base governs it everywhere

Stacks 0579 says that for a quasi-compact morphism of finite presentation the set of points of the
base whose fibre is geometrically reduced is locally constructible. In the affine case this is the
statement that `Algebra.geometricallyReducedFibreLocus A C` is constructible in `Spec A` for a
Noetherian ring `A` and a finite type `A`-algebra `C`; together with the irreducible half it is the
single remaining hypothesis of
`Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible`, i.e. of Stacks 05FT.

This file carries out the part of the Stacks proof that is formal, namely everything except the
spreading-out statements over an integral base. The Stacks argument has three steps: reduce to a
Noetherian base (already done — the consumer only ever needs the Noetherian case), apply the
constructibility criterion of Stacks 053Z, and then, on an irreducible closed subset `V(p)` of the
base, invoke Stacks 0578 (if the generic fibre is geometrically reduced, so are the fibres over a
dense open) and Stacks 0577 (if it is not, neither are the fibres over a dense open). The third
step is the mathematical content, EGA IV 9.7.7, and it is left as the hypothesis `hspread` below;
the first two steps and the passage from `A` to the quotient domain `A ⧸ p` are proved here.

So the net effect is a change of the remaining gap: instead of "the locus is constructible over
every Noetherian base" one now has to prove only "over a Noetherian *domain* the locus either
contains or misses a nonempty basic open", which is how Stacks 0577 and 0578 are stated and is a
statement about one generic fibre rather than about a topology on the base.

Everything about the dichotomy is independent of which property of the fibres is being tested, so
it is proved once for an arbitrary iso-invariant property of rings, as `Algebra.fibreLocus`; the
irreducible half of Stacks 05FT reuses it in
`StacksFrontier.RingTheory.GeometricallyIntegral.IrreducibleLocus`.

## Main definitions

* `Algebra.fibreLocus A C P`: the set of primes `p` of `A` such that `P (C ⊗[A] K)` holds for
  every field `K` over `A` with `ker (A → K) = p`. Taking `P = IsReduced` gives
  `Algebra.geometricallyReducedFibreLocus`, and taking `P R = IrreducibleSpace (PrimeSpectrum R)`
  gives `Algebra.geometricallyIrreducibleFibreLocus`.

## Main results

  (The bridge `isConstructible_of_isConstructibleSet`, from the predicate `IsConstructibleSet`
  used by the Stacks 053Z dichotomy to Mathlib's `Topology.IsConstructible`, lives beside that
  predicate in `StacksFrontier.Topology.Constructible.InConstructible`, which this file imports.)
* `PrimeSpectrum.isConstructible_of_forall_exists_basicOpen`: the ring-theoretic form of the
  criterion of Stacks 053Z. A subset of the spectrum of a Noetherian ring is constructible as soon
  as for every prime `p` some basic open `D(f)` with `f ∉ p` has `V(p) ∩ D(f)` either inside the
  subset or disjoint from it.
* `Algebra.mem_fibreLocus_quotient_iff`: the fibre locus of `(A ⧸ I) ⊗[A] C` over `A ⧸ I` is the
  preimage of the fibre locus of `C` over `A`. This is the affine, surjective case of Stacks 0576
  and Stacks 0555.
* `Algebra.isConstructible_fibreLocus`: the dichotomy of Stacks 053Z for a fibre locus follows from
  spreading out over Noetherian domains.
* `Algebra.isConstructible_geometricallyReducedFibreLocus`: the affine case of Stacks 0579,
  conditional on the affine case of Stacks 0577 and Stacks 0578.

## Implementation notes

The spreading-out hypothesis is stated over a Noetherian *domain* `D` with a finite type algebra
`T`, in the form "some nonempty basic open `D(f)` is contained in, or disjoint from, the locus".
Over a domain the zero ideal is prime, so `f ≠ 0` says exactly that `D(f)` is nonempty, i.e. that
it contains the generic point; the disjunction is therefore the dichotomy of Stacks 0577 and 0578
at the generic point. Flatness is deliberately absent: Stacks 0579 does not need it, and the
quotient `A ⧸ p` destroys it in any case. A prover may reinstate it after shrinking, by generic
flatness.

`Algebra.geometricallyReducedFibreLocus` quantifies over *every* field `K` over `A` with
`ker (A → K) = p`, not only over an algebraic closure of `κ(p)`; that is the shape in which
`StacksFrontier.RingTheory.GeometricallyIntegral.OpenLocus` states it and the shape the proof of
Stacks 05FT consumes. Identifying the two formulations is the content of Stacks 0384 and is not
needed anywhere below: hypothesis and conclusion are stated with the same definition, and the
argument moves one field at a time.

Nothing here carries a `@[stacks 0579]` attribute, because the statements proved are conditional;
`Algebra.isConstructible_geometricallyReducedFibreLocus` becomes the affine case of Stacks 0579 as
soon as `hspread` is supplied. That has since been done, in
`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromSmoothLocus`, where
`Algebra.isConstructible_geometricallyReducedFibreLocus'` is the affine case
unconditionally; the tag stays off there too, Stacks 0579 being a statement about an arbitrary
quasi-compact morphism locally of finite presentation.

## References

* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 0577](https://stacks.math.columbia.edu/tag/0577)
* [Stacks Project, Tag 0576](https://stacks.math.columbia.edu/tag/0576)
* [Stacks Project, Tag 053Z](https://stacks.math.columbia.edu/tag/053Z)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open Topology
open scoped TensorProduct

universe u

namespace PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- Every irreducible closed subset of a prime spectrum is the zero locus of one of its own
points, namely of its vanishing ideal, which is prime precisely because the subset is
irreducible. -/
@[ega "0 16.1.1" "partial", ega "I 1.1.14" "partial"]
theorem exists_zeroLocus_eq_of_isIrreducible {Z : Set (PrimeSpectrum R)} (hirr : IsIrreducible Z)
    (hcl : IsClosed Z) : ∃ p : PrimeSpectrum R, p ∈ Z ∧ zeroLocus (p.asIdeal : Set R) = Z := by
  have hZeq : zeroLocus ((vanishingIdeal Z : Ideal R) : Set R) = Z :=
    (zeroLocus_vanishingIdeal_eq_closure Z).trans hcl.closure_eq
  exact ⟨⟨vanishingIdeal Z, isIrreducible_iff_vanishingIdeal_isPrime.mp hirr⟩,
    hZeq.le ((mem_zeroLocus _ _).mpr subset_rfl), hZeq⟩

/-- **The criterion of Stacks 053Z for the spectrum of a Noetherian ring.** A subset `E` of
`Spec R` is constructible as soon as every prime `p` has an `f ∉ p` for which `V(p) ∩ D(f)` is
either contained in `E` or disjoint from `E`.

The irreducible closed subsets of `Spec R` are the `V(p)`, with `p` as generic point, and `D(f)` is
an open neighbourhood of `p`; so the first alternative says that `E ∩ V(p)` contains a nonempty
open of `V(p)` and the second that `E ∩ V(p)` is contained in the proper closed subset
`V(p) \ D(f)`, hence is not dense in `V(p)`. -/
@[ega "0 9.2.3" "special case", sga "1 IV 6.1" "special case"]
theorem isConstructible_of_forall_exists_basicOpen [IsNoetherianRing R] {E : Set (PrimeSpectrum R)}
    (h : ∀ p : PrimeSpectrum R, ∃ f : R, f ∉ p.asIdeal ∧
      (zeroLocus (p.asIdeal : Set R) ∩ (basicOpen f : Set (PrimeSpectrum R)) ⊆ E ∨
        Disjoint (zeroLocus (p.asIdeal : Set R) ∩ (basicOpen f : Set (PrimeSpectrum R))) E)) :
    IsConstructible E := by
  refine isConstructible_of_isConstructibleSet
    ((constructible_iff_dichotomy_irreducible_closed E).mpr fun Z hZirr hZcl => ?_)
  obtain ⟨p, hpZ, hZeq⟩ := exists_zeroLocus_eq_of_isIrreducible hZirr hZcl
  obtain ⟨f, hf, hcase⟩ := h p
  have hpU : p ∈ (basicOpen f : Set (PrimeSpectrum R)) := hf
  rcases hcase with hsub | hdisj
  · exact Or.inl ⟨basicOpen f, (basicOpen f).isOpen, ⟨p, hpU, hpZ⟩,
      fun x ⟨hxU, hxZ⟩ => ⟨hsub ⟨hZeq.ge hxZ, hxU⟩, hxZ⟩⟩
  · refine Or.inr fun hdense => ?_
    have hEZ : E ∩ Z ⊆ Z \ (basicOpen f : Set (PrimeSpectrum R)) := fun x ⟨hxE, hxZ⟩ =>
      ⟨hxZ, fun hxU => Set.disjoint_left.mp hdisj ⟨hZeq.ge hxZ, hxU⟩ hxE⟩
    exact (closure_minimal hEZ (hZcl.sdiff (basicOpen f).isOpen) (hdense hpZ)).2 hpU

end PrimeSpectrum

namespace Algebra

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]

/-- **The fibre locus of a property of rings.** The set of primes `p` of `A` at which
`P (C ⊗[A] K)` holds for every field `K` over `A` with `ker (A → K) = p`; that is, the set of
points of `Spec A` whose fibre has the property `P` after any field-valued base change.

Taking `P R = IsReduced R` gives `Algebra.geometricallyReducedFibreLocus` and taking
`P R = IrreducibleSpace (PrimeSpectrum R)` gives `Algebra.geometricallyIrreducibleFibreLocus`;
the constructibility argument of Stacks 0579 and Stacks 055B is insensitive to which of the two is
meant, so it is carried out at this level of generality. -/
def fibreLocus (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    (P : ∀ (R : Type u) [CommRing R], Prop) : Set (PrimeSpectrum A) :=
  {p | ∀ (K : Type u) [Field K] [Algebra A K],
    RingHom.ker (algebraMap A K) = p.asIdeal → P (C ⊗[A] K)}

/-- **The fibre of a base change to a quotient.** For a field `K` which is an algebra over both `A`
and `A ⧸ I`, compatibly, the fibre of `(A ⧸ I) ⊗[A] C` at `K` is the fibre of `C` at `K`. Both are
`K ⊗[A] C` up to the commutativity of the tensor product and the cancellation
`K ⊗[A ⧸ I] ((A ⧸ I) ⊗[A] C) = K ⊗[A] C`. -/
noncomputable def quotientTensorEquiv (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) (K : Type u) [CommRing K] [Algebra A K] [Algebra (A ⧸ I) K]
    [IsScalarTower A (A ⧸ I) K] :
    (C ⊗[A] K) ≃+* (((A ⧸ I) ⊗[A] C) ⊗[A ⧸ I] K) :=
  (((TensorProduct.comm A C K).toRingEquiv.trans
    (TensorProduct.cancelBaseChange A (A ⧸ I) (A ⧸ I) K C).symm.toRingEquiv).trans
    (TensorProduct.comm (A ⧸ I) K ((A ⧸ I) ⊗[A] C)).toRingEquiv)

/-- **The affine, surjective case of Stacks 0576 and Stacks 0555.** The fibre locus of
`(A ⧸ I) ⊗[A] C` over `A ⧸ I` is the preimage of the fibre locus of `C` over `A` under the closed
immersion `Spec (A ⧸ I) → Spec A`, for any property `P` of rings invariant under ring isomorphism.

The fields `K` over `A ⧸ I` with `ker (A ⧸ I → K) = q` are exactly the fields over `A` with
`ker (A → K)` the contraction of `q`, because such a kernel contains `I` and the map therefore
factors through `A ⧸ I`; and at such a `K` the two fibres agree by
`Algebra.quotientTensorEquiv`. -/
theorem mem_fibreLocus_quotient_iff {P : ∀ (R : Type u) [CommRing R], Prop}
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S], (R ≃+* S) → (P R ↔ P S)) (I : Ideal A)
    (q : PrimeSpectrum (A ⧸ I)) :
    q ∈ fibreLocus (A ⧸ I) ((A ⧸ I) ⊗[A] C) P ↔
      PrimeSpectrum.comap (algebraMap A (A ⧸ I)) q ∈ fibreLocus A C P := by
  have hIle : I ≤ Ideal.comap (algebraMap A (A ⧸ I)) q.asIdeal := fun x hx => by
    rw [Ideal.mem_comap, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.asIdeal.zero_mem
  constructor
  · intro h K _ _ hker
    have hIK : ∀ a ∈ I, algebraMap A K a = 0 := fun a ha =>
      RingHom.mem_ker.mp (hker ▸ hIle ha)
    let _ : Algebra (A ⧸ I) K := (Ideal.Quotient.lift I (algebraMap A K) hIK).toAlgebra
    have : IsScalarTower A (A ⧸ I) K := IsScalarTower.of_algebraMap_eq fun a => by
      rw [Ideal.Quotient.algebraMap_eq]
      exact (Ideal.Quotient.lift_mk I (algebraMap A K) hIK).symm
    have hker' : RingHom.ker (algebraMap (A ⧸ I) K) = q.asIdeal := by
      refine Ideal.ext fun x => ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingHom.mem_ker, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply A (A ⧸ I) K, ← RingHom.mem_ker, hker]
      simp [Ideal.mem_comap, Ideal.Quotient.algebraMap_eq]
    exact (hP _ _ (quotientTensorEquiv A C I K)).mpr (h K hker')
  · intro h K _ _ hker
    let _ : Algebra A K := ((algebraMap (A ⧸ I) K).comp (algebraMap A (A ⧸ I))).toAlgebra
    have : IsScalarTower A (A ⧸ I) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hker' : RingHom.ker (algebraMap A K) =
        (PrimeSpectrum.comap (algebraMap A (A ⧸ I)) q).asIdeal := by
      rw [IsScalarTower.algebraMap_eq A (A ⧸ I) K, ← RingHom.comap_ker, hker,
        PrimeSpectrum.comap_asIdeal]
    exact (hP _ _ (quotientTensorEquiv A C I K)).mp (h K hker')

/-- **Constructibility of a fibre locus from spreading out over Noetherian domains.** Let `P` be a
property of rings invariant under isomorphism and suppose that for every Noetherian domain `D` and
every finite type `D`-algebra `T` some nonempty basic open of `Spec D` is contained in, or disjoint
from, the fibre locus of `T`. Then the fibre locus of a finite type algebra over a Noetherian ring
is constructible.

This is the formal part of Stacks 0579 and Stacks 055B. Given a prime `p` of `A`, the hypothesis is
applied to the Noetherian domain `A ⧸ p` and the base change `(A ⧸ p) ⊗[A] C`; the resulting basic
open `D(g)` pulls back along the closed immersion `Spec (A ⧸ p) → Spec A` with image `V(p)` to
`V(p) ∩ D(f)` for any lift `f` of `g`, and the two fibre loci correspond by
`Algebra.mem_fibreLocus_quotient_iff`. The criterion of Stacks 053Z,
`PrimeSpectrum.isConstructible_of_forall_exists_basicOpen`, then applies. -/
theorem isConstructible_fibreLocus {P : ∀ (R : Type u) [CommRing R], Prop}
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S], (R ≃+* S) → (P R ↔ P S))
    (hspread : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T], ∃ f : D, f ≠ 0 ∧
        ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ fibreLocus D T P ∨
          Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) (fibreLocus D T P)))
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (fibreLocus A C P) := by
  refine PrimeSpectrum.isConstructible_of_forall_exists_basicOpen fun p => ?_
  have := p.isPrime
  obtain ⟨g, hg0, hgcase⟩ := hspread (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⊗[A] C)
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective g
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap A (A ⧸ p.asIdeal))) =
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) := by
    rw [Ideal.Quotient.algebraMap_eq, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    simp [Ideal.mk_ker]
  have key : ∀ x ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)),
      ∃ q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (A ⧸ p.asIdeal))),
        PrimeSpectrum.comap (algebraMap A (A ⧸ p.asIdeal)) q = x := fun x ⟨hxZ, hxU⟩ => by
    obtain ⟨q, rfl⟩ := hrange ▸ hxZ
    refine ⟨q, ?_, rfl⟩
    simpa only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, ← hf, PrimeSpectrum.comap_asIdeal,
      Ideal.mem_comap, Ideal.Quotient.algebraMap_eq] using hxU
  refine ⟨f, fun hfp => hg0 (hf ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hfp), ?_⟩
  rcases hgcase with hsub | hdisj
  · refine Or.inl fun x hx => ?_
    obtain ⟨q, hq, rfl⟩ := key x hx
    exact (mem_fibreLocus_quotient_iff hP _ q).mp (hsub hq)
  · refine Or.inr (Set.disjoint_left.mpr fun x hx hxE => ?_)
    obtain ⟨q, hq, rfl⟩ := key x hx
    exact Set.disjoint_left.mp hdisj hq ((mem_fibreLocus_quotient_iff hP _ q).mpr hxE)

/-- The geometrically reduced fibre locus is the fibre locus of the property of being reduced. -/
theorem geometricallyReducedFibreLocus_eq_fibreLocus (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] :
    geometricallyReducedFibreLocus A C = fibreLocus A C (fun R _ => IsReduced R) := rfl

/-- **The affine case of Stacks 0579, granted the affine cases of Stacks 0577 and Stacks 0578.**
Let `A` be a Noetherian ring and `C` a finite type `A`-algebra. If over every Noetherian domain `D`
and finite type `D`-algebra `T` some nonempty basic open of `Spec D` either lies in or misses the
geometrically reduced fibre locus of `T`, then the geometrically reduced fibre locus of `C` is
constructible in `Spec A`.

The hypothesis is exactly the dichotomy supplied by Stacks 0578 (the generic fibre is
geometrically reduced, hence so is every fibre over a nonempty open) and Stacks 0577 (it is not,
hence neither is any fibre over a nonempty open), the two cases being distinguished by whether the
generic fibre of `T` is geometrically reduced. -/
theorem isConstructible_geometricallyReducedFibreLocus
    (hspread : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T], ∃ f : D, f ≠ 0 ∧
        ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
            geometricallyReducedFibreLocus D T ∨
          Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D))
            (geometricallyReducedFibreLocus D T)))
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyReducedFibreLocus A C) :=
  isConstructible_fibreLocus (fun _ _ _ _ e => isReduced_congr e) hspread A C

end Algebra

end
