module

public import StacksFrontier.RingTheory.LocalCohomology.FinitenessAnnihilatorCriterionPlus
public import StacksFrontier.RingTheory.LocalCohomology.SupportedAugmentation

/-!
# From an annihilating ideal back to finiteness of local cohomology

Let `A` be a Noetherian ring, let `T ⊆ Spec(A)` be stable under specialization, let `K` be an
object of the bounded-below derived category of `A`-modules whose cohomology modules are all
finite, and let `n ∈ ℤ`. If one ideal `J` with `V(J) ⊆ T` annihilates `H^i_T(K)` for every
`i ≤ n`, then every one of those modules is finite.

The opposite direction, from finiteness to the ideal, is
`Stacks.LocalCohomology.exists_annihilator_localCohomologyWithSupportInPlus_of_finite`. Together
they give the equivalence of the source's clauses (1) and (2), which is
`Stacks.LocalCohomology.localCohomologyWithSupportInPlus_finite_iff_exists_annihilator` below.

## The argument

Write `F = RΓ_T` for derived sections with support in `T` on `D⁺`, so that
`H^i_T(K) = H^i(F(K))`. Pick generators `r_1, …, r_k` of `J` and induct on the number of
generators, proving the statement in the following form: if the cohomology of `K` is finite and
supported in a set `S` with `S ∩ V(r_1, …, r_k) ⊆ T`, and every `r_j` has a power annihilating
`H^i(F(K))` for `i ≤ n`, then those modules are finite. With no generators the hypothesis says
that the cohomology of `K` is already supported in `T`, and then the augmentation
`F(K) ⟶ K` is an isomorphism — this is
`Stacks.LocalCohomology.finite_localCohomologyWithSupportInPlus_of_support_subset` — so the
conclusion is the finiteness of the cohomology of `K` itself. For the inductive step, let `r` be
one generator with `r ^ e` annihilating the range and let `L` be the fibre of
`r ^ e • 𝟙 : K ⟶ K`, that is the object completing it to a distinguished triangle. Both halves of
the triangle's long exact sequence are used:

* at `K`, where `L` has finite cohomology because it sits between two finite modules, and that
  cohomology is supported in `S ∩ V(r)` because `(r ^ e) ^ 2` annihilates it; the inductive
  hypothesis then applies to `L` with the smaller generating set;
* after applying `F`, where the map `H^i(F(L)) ⟶ H^i(F(K))` is surjective because the next map
  along is `r ^ e`, which acts as zero on `H^i(F(K))` in the range.

Surjectivity from a finite module is what makes `H^i(F(K))` finite.

## Main results

* `Stacks.LocalCohomology.finite_localCohomologyWithSupportInPlus_of_annihilator` —
  **Stacks 0EI1, the implication (2) ⟹ (1).**
* `Stacks.LocalCohomology.localCohomologyWithSupportInPlus_finite_iff_exists_annihilator` — the
  resulting equivalence of the source's clauses (1) and (2).

## Implementation notes

`Stacks.LocalCohomology.derivedSectionsWithSupportInPlus_linear` is the `A`-linearity of `RΓ_T`
on `D⁺`, deduced from the `A`-linearity of the unbounded derived functor along the comparison
`Stacks.LocalCohomology.derivedSectionsWithSupportInPlusIso` and the faithfulness of
`DerivedCategory.Plus.ι`; it is what turns `r ^ e • 𝟙 K` into multiplication by `r ^ e` on
cohomology. And `Stacks.LocalCohomology.homology_finite_of_support_and_nilpotent_generators` is
the induction itself, stated for an arbitrary `A`-linear exact endofunctor of `D⁺` satisfying the
base case, since nothing else about `RΓ_T` enters.

## References

* [Stacks Project, Tag 0EI1](https://stacks.math.columbia.edu/tag/0EI1)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- The derived functor `RΓ_T` of sections with support in `T` on the bounded-below derived
category of `A`-modules is `A`-linear. -/
instance derivedSectionsWithSupportInPlus_linear (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    Functor.Linear A (derivedSectionsWithSupportInPlus.{u, v} A T) where
  map_smul {K L} f r := by
    have hcomp : (derivedSectionsWithSupportInPlus.{u, v} A T ⋙
        DerivedCategory.Plus.ι).Linear A :=
      Functor.linear_of_iso A (derivedSectionsWithSupportInPlusIso.{u, v} A T).symm
    apply DerivedCategory.Plus.ι.map_injective
    calc DerivedCategory.Plus.ι.map
          ((derivedSectionsWithSupportInPlus.{u, v} A T).map (r • f))
        = (derivedSectionsWithSupportInPlus.{u, v} A T ⋙
            DerivedCategory.Plus.ι).map (r • f) := rfl
      _ = r • (derivedSectionsWithSupportInPlus.{u, v} A T ⋙
            DerivedCategory.Plus.ι).map f := Functor.map_smul _ _ _
      _ = r • DerivedCategory.Plus.ι.map
            ((derivedSectionsWithSupportInPlus.{u, v} A T).map f) := rfl
      _ = DerivedCategory.Plus.ι.map
            (r • (derivedSectionsWithSupportInPlus.{u, v} A T).map f) :=
          (Functor.map_smul _ _ _).symm

/-! ### Three facts about exact sequences of modules -/

/-- The middle term of an exact sequence of modules over a Noetherian ring with finite outer
terms is finite. -/
private theorem finite_of_exact_noetherian {R M N P : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module.Finite R M] [Module.Finite R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hex : Function.Exact f g) :
    Module.Finite R N := by
  have hker : LinearMap.ker g ≤ LinearMap.range f := fun x hx ↦ (hex x).mp hx
  have : IsNoetherian R (LinearMap.ker g) := isNoetherian_of_le hker
  have : Module.Finite R (N ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

/-- If `r` kills the image of `f` and acts as zero on the target of `g`, then `r ^ 2` kills the
middle term of the exact sequence `M ⟶ N ⟶ P`. -/
private theorem smul_sq_eq_zero_of_exact {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hex : Function.Exact f g)
    (r : R) (hf : ∀ x, f (r • x) = 0) (hg : ∀ x, r • g x = 0) (x : N) :
    r ^ 2 • x = 0 := by
  obtain ⟨y, hy⟩ := (hex (r • x)).mp (by rw [map_smul, hg])
  rw [pow_two, mul_smul, ← hy, ← map_smul, hf]

/-! ### The long exact sequence attached to multiplication by a scalar -/

/-- Let `H` be a homological functor with a shift sequence out of an `A`-linear triangulated
category, and let `L ⟶ K ⟶ K ⟶ L[1]` be a distinguished triangle whose second map is `r • 𝟙 K`.
The piece
`H^{i-1}(K) ⟶ H^i(L) ⟶ H^i(K)`
of the associated long exact sequence is exact, `r` kills the image of its first map, and `r`
acts as zero on the image of its second. -/
private theorem exists_exact_of_scalar_triangle {A : Type u} [CommRing A]
    {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
    [∀ i : ℤ, (shiftFunctor C i).Additive] [HasZeroObject C] [Pretriangulated C]
    [Linear A C] (H : C ⥤ ModuleCat.{v} A) [H.IsHomological] [H.ShiftSequence ℤ]
    (hlin : ∀ i : ℤ, (H.shift i).Linear A)
    {L K : C} (r : A) (f : L ⟶ K) (g : K ⟶ L⟦(1 : ℤ)⟧)
    (ht : Triangle.mk f (r • 𝟙 K) g ∈ distTriang C) (i : ℤ) :
    ∃ d : (H.shift (i - 1)).obj K ⟶ (H.shift i).obj L,
      Function.Exact d.hom ((H.shift i).map f).hom ∧
      (∀ x, d.hom (r • x) = 0) ∧
      (∀ x, r • ((H.shift i).map f).hom x = 0) := by
  let t := Triangle.mk f (r • 𝟙 K) g
  let d := H.homologySequenceδ t (i - 1) i (by omega)
  have : (H.shift (i - 1)).Linear A := hlin _
  have : (H.shift i).Linear A := hlin _
  refine ⟨d, ?_, ?_, ?_⟩
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (H.homologySequence_exact₁ t ht (i - 1) i (by omega))
  · intro x
    have h := ConcreteCategory.congr_hom
      (H.comp_homologySequenceδ t ht (i - 1) i (by omega)) x
    simpa [t, Functor.map_smul, d] using h
  · intro x
    have h := ConcreteCategory.congr_hom
      (show (H.shift i).map t.mor₁ ≫ (H.shift i).map t.mor₂ = 0 from by
        rw [← CategoryTheory.Functor.map_comp, comp_distTriang_mor_zero₁₂ t ht,
          CategoryTheory.Functor.map_zero]) x
    simpa [t, Functor.map_smul] using h

/-! ### The descending induction on the generators of the annihilating ideal -/

/-- **The inductive step of Tag 0EI1's implication `(2) ⟹ (1)`, in the abstract.** Let `F` be an
`A`-linear exact endofunctor of the bounded-below derived category which takes an object with
finite cohomology supported in `T` to an object with finite cohomology. Let `K` have finite
cohomology supported in a set `S`, let `s` be a finite subset of `A` with
`S ∩ V(s) ⊆ T`, and suppose each element of `s` has a power annihilating `H^i(F(K))` for every
`i ≤ n`. Then `H^i(F(K))` is finite for every `i ≤ n`.

The induction is on `s`. For `r ∈ s` with `r ^ e` annihilating the range, the cone `L` of
`r ^ e • 𝟙 K` has finite cohomology, by the long exact sequence, and that cohomology is
supported in `S ∩ V(r)`, because `(r ^ e) ^ 2` annihilates it. The inductive hypothesis makes
`H^i(F(L))` finite, and `H^i(F(L)) ⟶ H^i(F(K))` is surjective because the map it comes from
is multiplication by `r ^ e`, which is zero there. -/
private theorem homology_finite_of_support_and_nilpotent_generators
    (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (F : DerivedCategory.Plus (ModuleCat.{max u v} A) ⥤
      DerivedCategory.Plus (ModuleCat.{max u v} A))
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear A]
    (hF : ∀ K : DerivedCategory.Plus (ModuleCat.{max u v} A),
      (∀ i, Module.Finite A
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) →
      (∀ i, Module.support A
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K) ⊆ T) →
      ∀ i, Module.Finite A
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj (F.obj K)))
    (s : Finset A) (n : ℤ) (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hK : ∀ i, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (S : Set (PrimeSpectrum A))
    (hKS : ∀ i, Module.support A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K) ⊆ S)
    (hST : S ∩ PrimeSpectrum.zeroLocus (s : Set A) ⊆ T)
    (hkill : ∀ r ∈ s, ∃ e : ℕ, 0 < e ∧ ∀ i : ℤ, i ≤ n →
      r ^ e ∈ Module.annihilator A
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj (F.obj K))) :
    ∀ i : ℤ, i ≤ n → Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj (F.obj K)) := by
  classical
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) 0
  have hlin (i : ℤ) : (H.shift i).Linear A := by
    change (DerivedCategory.Plus.ι ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).Linear A
    infer_instance
  have hFlin (i : ℤ) : ((F ⋙ H).shift i).Linear A := by
    change (F ⋙ H.shift i).Linear A
    have := hlin i
    infer_instance
  induction s using Finset.induction_on generalizing K S with
  | empty =>
    intro i hi
    exact hF K hK (fun j ↦ (hKS j).trans (by simpa using hST)) i
  | @insert r s hrs ih =>
    obtain ⟨e, he, hrej⟩ := hkill r (Finset.mem_insert_self _ _)
    obtain ⟨L, f, g, ht⟩ := distinguished_cocone_triangle₁ (r ^ e • 𝟙 K)
    let t := Triangle.mk f (r ^ e • 𝟙 K) g
    have hdata (i : ℤ) := exists_exact_of_scalar_triangle H hlin (r ^ e) f g ht i
    have hFdata (i : ℤ) := exists_exact_of_scalar_triangle (F ⋙ H) hFlin (r ^ e) f g ht i
    have hL (i : ℤ) : Module.Finite A
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj L) := by
      obtain ⟨d, hd, _, _⟩ := hdata i
      have : Module.Finite A ((H.shift (i - 1)).obj K) := hK (i - 1)
      have : Module.Finite A ((H.shift i).obj K) := hK i
      exact finite_of_exact_noetherian d.hom ((H.shift i).map f).hom hd
    have hLS (i : ℤ) : Module.support A
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj L) ⊆
          S ∩ PrimeSpectrum.zeroLocus ({r} : Set A) := by
      obtain ⟨d, hd, hdr, hfr⟩ := hdata i
      intro p hp
      refine ⟨?_, ?_⟩
      · exact Set.union_subset (hKS (i - 1)) (hKS i)
          (support_subset_union_of_exact d.hom ((H.shift i).map f).hom hd hp)
      · have hz : (r ^ e) ^ 2 ∈ Module.annihilator A ((H.shift i).obj L) :=
          Module.mem_annihilator.mpr
            (smul_sq_eq_zero_of_exact d.hom ((H.shift i).map f).hom hd (r ^ e) hdr hfr)
        have hp' := Module.annihilator_le_of_mem_support hp hz
        have hrp := p.isPrime.mem_of_pow_mem e (p.isPrime.mem_of_pow_mem 2 hp')
        exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (by simpa using hrp)
    have hLT : (S ∩ PrimeSpectrum.zeroLocus ({r} : Set A)) ∩
        PrimeSpectrum.zeroLocus (s : Set A) ⊆ T := by
      intro p hp
      apply hST
      refine ⟨hp.1.1, ?_⟩
      change (↑(insert r s) : Set A) ⊆ p.asIdeal
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp.1.2 (by rfl)
      · exact hp.2 hx
    have hLkill : ∀ r' ∈ s, ∃ e' : ℕ, 0 < e' ∧ ∀ i : ℤ, i ≤ n →
        r' ^ e' ∈ Module.annihilator A
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj (F.obj L)) := by
      intro r' hr'
      obtain ⟨e', he', hpow⟩ := hkill r' (Finset.mem_insert_of_mem hr')
      refine ⟨e' * 2, by omega, ?_⟩
      intro i hi
      obtain ⟨d, hd, _, _⟩ := hFdata i
      rw [pow_mul, Module.mem_annihilator]
      apply smul_sq_eq_zero_of_exact d.hom (((F ⋙ H).shift i).map f).hom hd
      · intro x
        have hx : r' ^ e' • x = 0 := Module.mem_annihilator.mp (hpow (i - 1) (by omega)) x
        rw [hx, map_zero]
      · intro x
        exact Module.mem_annihilator.mp (hpow i hi) _
    have hFL := ih L hL (S ∩ PrimeSpectrum.zeroLocus ({r} : Set A)) hLS hLT hLkill
    intro i hi
    have : ((F ⋙ H).shift i).Linear A := hFlin i
    have hzero : ((F ⋙ H).shift i).map t.mor₂ = 0 := by
      change ((F ⋙ H).shift i).map (r ^ e • 𝟙 K) = 0
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
      ext x
      exact Module.mem_annihilator.mp (hrej i hi) x
    have : Epi (((F ⋙ H).shift i).map f) :=
      ((F ⋙ H).homologySequence_epi_shift_map_mor₁_iff t ht i).mpr hzero
    have : Module.Finite A (((F ⋙ H).shift i).obj L) := hFL i hi
    exact Module.Finite.of_surjective (((F ⋙ H).shift i).map f).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-! ### Tag 0EI1's implication from an annihilator to finiteness -/

/-- **Stacks 0EI1, the implication (2) ⟹ (1).** Let `A` be a Noetherian ring, let
`T ⊆ Spec(A)` be stable under specialization, let `K` be an object of the bounded-below derived
category whose cohomology modules are finite, and let `n ∈ ℤ`. If one ideal `J` with `V(J) ⊆ T`
annihilates `H^i_T(K)` for every `i ≤ n`, then those modules are finite. -/
theorem finite_localCohomologyWithSupportInPlus_of_annihilator (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (n : ℤ) (J : Ideal A) (hJT : PrimeSpectrum.zeroLocus (J : Set A) ⊆ T)
    (hJ : ∀ i : ℤ, i ≤ n → J ≤ Module.annihilator A
      (localCohomologyWithSupportInPlus.{u, v} A T K i)) :
    ∀ i : ℤ, i ≤ n →
      Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A T K i) := by
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing J
  refine homology_finite_of_support_and_nilpotent_generators.{u, v} A T
    (derivedSectionsWithSupportInPlus.{u, v} A T)
    (fun L hL hsupport i ↦
      have := hL i
      finite_localCohomologyWithSupportInPlus_of_support_subset.{u, v} A T hT L hsupport i)
    s n K hK Set.univ (fun _ ↦ Set.subset_univ _) ?_ ?_
  · simpa only [Set.univ_inter, ← hs, PrimeSpectrum.zeroLocus_span] using hJT
  · intro r hr
    refine ⟨1, Nat.zero_lt_one, ?_⟩
    intro i hi
    rw [pow_one]
    exact hJ i hi (by rw [← hs]; exact Ideal.subset_span hr)

/-- **Stacks 0EI1, the equivalence of (1) and (2).** Let `A` be a Noetherian ring, let
`T ⊆ Spec(A)` be stable under specialization, let `K` be an object of the bounded-below derived
category whose cohomology modules are finite, and let `n ∈ ℤ`. Then `H^i_T(K)` is finite for
every `i ≤ n` if and only if there is an ideal `J` with `V(J) ⊆ T` annihilating `H^i_T(K)` for
every `i ≤ n`.

The implication from finiteness is
`exists_annihilator_localCohomologyWithSupportInPlus_of_finite`, which needs neither finiteness
of the cohomology of `K` nor stability of `T`; the converse is
`finite_localCohomologyWithSupportInPlus_of_annihilator`. -/
theorem localCohomologyWithSupportInPlus_finite_iff_exists_annihilator (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (n : ℤ) :
    (∀ i : ℤ, i ≤ n →
        Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A T K i)) ↔
      (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
        ∀ i : ℤ, i ≤ n → J ≤ Module.annihilator A
          (localCohomologyWithSupportInPlus.{u, v} A T K i)) where
  mp hfin := exists_annihilator_localCohomologyWithSupportInPlus_of_finite.{u, v} A T K n hfin
  mpr := fun ⟨J, hJT, hJ⟩ ↦
    finite_localCohomologyWithSupportInPlus_of_annihilator.{u, v} A T hT K hK n J hJT hJ

end Stacks.LocalCohomology

end
