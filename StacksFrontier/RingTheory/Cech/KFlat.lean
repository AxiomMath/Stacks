module

public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.RingTheory.Cech.Substrate

/-!
# The extended alternating Čech complex of a ring is K-flat

Let `A` be a commutative ring and `f₁, …, f_r ∈ A`. The extended alternating Čech complex
`C^•(f₁, …, f_r; A)` of the ring itself has, in degree `p`, the finite direct sum of the
localizations `A_{f_{i_0} \cdots f_{i_{p-1}}}` over the `p`-element subsets of `{1, …, r}`. A
localization is flat and a finite direct sum of flat modules is flat, so every term is flat; and
there are no subsets of cardinality above `r`, so the complex is zero above degree `r`. A complex
which is bounded above with flat terms is K-flat
(`CochainComplex.KFlat.kFlat_of_flat`, [Stacks, Tag 06Y5]). This file records that conclusion.

It matters because K-flatness is what makes degreewise extension of scalars along a ring map
`A → B` compute the *derived* tensor product `C^•(f; A) ⊗^L_A B`, which is the hypothesis under
which condition (c) of [Stacks, Tag 099D] can be read off the complex-level base-change
isomorphism `Stacks.CechBaseChange.cechComplexBaseChangeIso` of [Stacks, Tag 0G6I].

## Main results

* `Cech.kFlat_extend_cechComplex`: the integer-indexed extended alternating Čech complex of `A`
  on a finite family of its elements is K-flat.

## Implementation notes

The statement is about the integer-indexed complex `(Cech.cechComplex f A).extend
ComplexShape.embeddingUpNat`, which is the form `Stacks.LocalCohomology.extendedCechComplex`
takes and the only form in which K-flatness is defined, since `CochainComplex.KFlat` is a
property of a complex indexed by `ℤ`.

The flatness of the terms is read off the definition of `Cech.cechTerm` as a direct sum of
`Cech.cechMod`s, each a `LocalizedModule`, by instance search; the degrees below zero are zero
because the embedding `ComplexShape.embeddingUpNat` misses them, and the degrees above `r` are
zero because `Finset (Fin r)` has no subset of cardinality greater than `r`.

This lemma was previously a `private` lemma of
`StacksFrontier/Homology/DerivedComplete/CechCompletion.lean`, used there for the derived tensor
comparison of [Stacks, Tag 091V]; it is stated here so that the base-change consumers can reach
it without depending on the derived-Hom construction.

## References

* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 0G6I](https://stacks.math.columbia.edu/tag/0G6I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Cech

/-- **The extended alternating Čech complex of a ring is K-flat.** Its terms are finite direct
sums of localizations of `A`, hence flat, and it vanishes above degree `r`; a complex which is
bounded above with flat terms is K-flat. -/
public lemma kFlat_extend_cechComplex {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    CochainComplex.KFlat ((Cech.cechComplex f A).extend ComplexShape.embeddingUpNat) := by
  let K : CochainComplex (ModuleCat A) ℤ :=
    (Cech.cechComplex f A).extend ComplexShape.embeddingUpNat
  have ht (n : ℕ) : Module.Flat A ((Cech.cechComplex f A).X n) := by
    change Module.Flat A (Cech.cechTerm f A n)
    unfold Cech.cechTerm Cech.cechMod
    infer_instance
  have hz (q : ℤ) (hq : q < 0) : IsZero (K.X q) := by
    apply HomologicalComplex.isZero_extend_X
    intro n hn
    simp only [ComplexShape.embeddingUpNat_f] at hn
    omega
  have hsub (n : ℕ) (hn : r < n) : IsZero ((Cech.cechComplex f A).X n) := by
    refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => ?_⟩
    apply DirectSum.ext
    intro s
    exact False.elim (by
      have hs := Finset.card_le_univ s.1
      simp only [Fintype.card_fin] at hs
      omega)
  have hiso (n : ℕ) : K.X n ≅ (Cech.cechComplex f A).X n :=
    (Cech.cechComplex f A).extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
      (by simp)
  have hflat : ∀ q : ℤ, Module.Flat A (K.X q) := fun q => by
    by_cases hq : 0 ≤ q
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      have := ht n
      exact Module.Flat.of_linearEquiv (hiso n).toLinearEquiv
    · have := ht (r + 1)
      exact Module.Flat.of_linearEquiv
        ((hz q (lt_of_not_ge hq)).iso (hsub (r + 1) (by omega))).toLinearEquiv
  have hle : K.IsStrictlyLE r := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
    exact IsZero.of_iso (hsub n (by omega)) (hiso n)
  exact CochainComplex.KFlat.kFlat_of_flat K r

end Cech

end
