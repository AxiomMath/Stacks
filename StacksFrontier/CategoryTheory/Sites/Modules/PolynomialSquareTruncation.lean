module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialSubstitution

/-!
# Truncating a member of the square of the kernel of a polynomial presentation

Let `φ : R₀[ι] →+* T` be a presentation of a commutative ring by a polynomial ring and let `z`
lie in the square of its kernel.  A decomposition of `z` as a sum of products of two kernel
elements involves finitely many polynomials, hence finitely many variables, so after adding
those variables to any finite set `s₀` the element `z` is the image of a polynomial on the
resulting finite set which lies in the square of the kernel of the *truncated* presentation
`φ ∘ rename val`.

This is the `I²` counterpart of
`Stacks.Sites.Conormal.exists_finset_rename_forall_rename_pderiv_mem` of
`StacksFrontier/CategoryTheory/Sites/Modules/ConormalPolynomialSubstitution.lean`, which truncates
a polynomial all of whose partial derivatives lie in an ideal; both are needed by the degree
`-1` comparison of two presentations, where a conormal class and the square it is taken modulo
have to be pushed down to the same finite set of variables.

## Main results

* `Stacks.Sites.Conormal.exists_finset_rename_mem_ker_sq`: **a member of the square of the
  kernel of a polynomial presentation comes, together with the witness of its membership, from
  the polynomial ring on finitely many variables** — and the finite set of variables may be
  taken to contain any prescribed finite set.

## Implementation notes

The proof is `Submodule.mul_induction_on` on the membership `z ∈ I * I`, with the whole
conclusion as the predicate; the motive is given explicitly, since the element being
decomposed occurs inside the statement.  A single kernel element is truncated to the union of
the prescribed set with its own variables by `MvPolynomial.exists_rename_eq_of_vars_subset_range`,
and the two branches of the induction then enlarge the two finite sets they are handed to
their union.

The transport of the kernel, and of its square, along the enlargement is reproved here for
bare `RingHom`s rather than quoted from `Stacks.Sites.Conormal.map_mem_ker_sq_of_fac`, whose
`CommRingCat` packaging would have to be installed and stripped again around every use; the
argument is two lines either way.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), the naive cotangent
  complex, whose degree `-1` term is the conormal module this serves.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of
  the naive cotangent complex from the presentation, the consumer of the truncation.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Sites.Conormal

section Composition

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring map carries a power of the kernel of a composite into the same power of the kernel of
the second factor. -/
private theorem map_mem_ker_pow_of_comp (f : A →+* B) (g : B →+* C) {z : A} {n : ℕ}
    (hz : z ∈ RingHom.ker (g.comp f) ^ n) : f z ∈ RingHom.ker g ^ n := by
  have h : (RingHom.ker (g.comp f)).map f ≤ RingHom.ker g :=
    Ideal.map_le_iff_le_comap.mpr fun m hm ↦ hm
  exact Ideal.pow_right_mono h n (by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hz)

end Composition

section Truncation

variable {R₀ : Type*} [CommRing R₀] {ι : Type*} {T : Type*} [CommRing T]
  (φ : MvPolynomial ι R₀ →+* T)

/-- Renaming along the inclusion of a finite set of variables into a larger one, and then along
the inclusion of the larger one into all of `ι`, is renaming along the inclusion of the
smaller one into all of `ι`. -/
private theorem rename_rename_inclusion {s t : Finset ι} (hst : s ⊆ t)
    (p : MvPolynomial {x // x ∈ s} R₀) :
    MvPolynomial.rename (Subtype.val : {x // x ∈ t} → ι)
        (MvPolynomial.rename (fun x : {x // x ∈ s} ↦ (⟨x.1, hst x.2⟩ : {x // x ∈ t})) p) =
      MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι) p := by
  rw [MvPolynomial.rename_rename]
  rfl

/-- The truncated presentations on a finite set of variables and on a larger one are compatible
with the inclusion of the smaller set into the larger. -/
private theorem comp_rename_inclusion {s t : Finset ι} (hst : s ⊆ t) :
    (φ.comp (MvPolynomial.rename (Subtype.val : {x // x ∈ t} → ι)).toRingHom).comp
        (MvPolynomial.rename
          (fun x : {x // x ∈ s} ↦ (⟨x.1, hst x.2⟩ : {x // x ∈ t}))).toRingHom =
      φ.comp (MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι)).toRingHom := by
  refine RingHom.ext fun p ↦ ?_
  have h := rename_rename_inclusion hst p
  exact congrArg φ h

/-- **Enlarging the set of variables.**  A polynomial on a finite set of variables lying in a
power of the kernel of the truncated presentation is renamed, along the inclusion into a larger
finite set, to a polynomial with the same image in `R₀[ι]` lying in the same power of the kernel
of the presentation truncated to the larger set. -/
private theorem exists_rename_eq_and_mem_ker_pow_of_subset {s t : Finset ι} (hst : s ⊆ t)
    {z : MvPolynomial ι R₀} {p : MvPolynomial {x // x ∈ s} R₀} {n : ℕ}
    (hpz : MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι) p = z)
    (hpk : p ∈ RingHom.ker
      (φ.comp (MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι)).toRingHom) ^ n) :
    ∃ q : MvPolynomial {x // x ∈ t} R₀,
      MvPolynomial.rename (Subtype.val : {x // x ∈ t} → ι) q = z ∧
        q ∈ RingHom.ker
          (φ.comp (MvPolynomial.rename (Subtype.val : {x // x ∈ t} → ι)).toRingHom) ^ n := by
  refine ⟨MvPolynomial.rename
    (fun x : {x // x ∈ s} ↦ (⟨x.1, hst x.2⟩ : {x // x ∈ t})) p, ?_, ?_⟩
  · exact (rename_rename_inclusion hst p).trans hpz
  · rw [← comp_rename_inclusion φ hst] at hpk
    exact map_mem_ker_pow_of_comp _ _ hpk

/-- **Truncation of a single kernel element.**  An element of the kernel of a polynomial
presentation is the image of an element of the kernel of the presentation truncated to a finite
set of variables, which may be taken to contain any prescribed finite set. -/
private theorem exists_finset_rename_mem_ker (s₀ : Finset ι) (m : MvPolynomial ι R₀)
    (hm : m ∈ RingHom.ker φ) :
    ∃ s : Finset ι, s₀ ⊆ s ∧ ∃ p : MvPolynomial {x // x ∈ s} R₀,
      MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι) p = m ∧
        p ∈ RingHom.ker
          (φ.comp (MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι)).toRingHom) := by
  classical
  refine ⟨s₀ ∪ m.vars, Finset.subset_union_left, ?_⟩
  obtain ⟨p, hp⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range m
    (Subtype.val : {x // x ∈ s₀ ∪ m.vars} → ι) Subtype.val_injective (by
      intro i hi
      exact ⟨⟨i, Finset.mem_union_right _ (Finset.mem_coe.mp hi)⟩, rfl⟩)
  refine ⟨p, hp, RingHom.mem_ker.mpr ?_⟩
  have h : φ (MvPolynomial.rename (Subtype.val : {x // x ∈ s₀ ∪ m.vars} → ι) p) = 0 := by
    rw [hp]
    exact RingHom.mem_ker.mp hm
  exact h

/-- **Truncation of a member of the square of the kernel.**  If `z` lies in the square of the
kernel of a polynomial presentation `φ : R₀[ι] →+* T`, then for every finite set `s₀` of
variables there is a finite `s ⊇ s₀` and a polynomial `p` on the variables `s` with image `z`
in `R₀[ι]` which lies in the square of the kernel of the truncated presentation
`φ ∘ rename val`.

Only finitely many variables occur in a decomposition of `z` as a sum of products of two kernel
elements, which is what makes the truncation possible; the freedom in `s₀` is what lets a
caller truncate `z` and other data to one and the same finite set of variables. -/
theorem exists_finset_rename_mem_ker_sq (s₀ : Finset ι) (z : MvPolynomial ι R₀)
    (hz : z ∈ RingHom.ker φ ^ 2) :
    ∃ s : Finset ι, s₀ ⊆ s ∧ ∃ p : MvPolynomial {x // x ∈ s} R₀,
      MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι) p = z ∧
        p ∈ RingHom.ker (φ.comp (MvPolynomial.rename
          (Subtype.val : {x // x ∈ s} → ι)).toRingHom) ^ 2 := by
  classical
  rw [pow_two] at hz
  refine Submodule.mul_induction_on
    (C := fun w ↦ ∃ s : Finset ι, s₀ ⊆ s ∧ ∃ p : MvPolynomial {x // x ∈ s} R₀,
      MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι) p = w ∧
        p ∈ RingHom.ker (φ.comp (MvPolynomial.rename
          (Subtype.val : {x // x ∈ s} → ι)).toRingHom) ^ 2) hz ?_ ?_
  · intro m hm n hn
    obtain ⟨s₁, hs₁, m', hm'z, hm'k⟩ := exists_finset_rename_mem_ker φ s₀ m hm
    obtain ⟨s₂, _, n', hn'z, hn'k⟩ := exists_finset_rename_mem_ker φ s₀ n hn
    obtain ⟨M, hMz, hMk⟩ :=
      exists_rename_eq_and_mem_ker_pow_of_subset φ (Finset.subset_union_left (s₂ := s₂)) hm'z
        (by rwa [pow_one])
    obtain ⟨N, hNz, hNk⟩ :=
      exists_rename_eq_and_mem_ker_pow_of_subset φ (Finset.subset_union_right (s₁ := s₁)) hn'z
        (by rwa [pow_one])
    refine ⟨s₁ ∪ s₂, hs₁.trans Finset.subset_union_left, M * N, ?_, ?_⟩
    · rw [map_mul, hMz, hNz]
    · rw [pow_one] at hMk hNk
      rw [pow_two]
      exact Ideal.mul_mem_mul hMk hNk
  · intro x y hx hy
    obtain ⟨s₁, hs₁, p₁, hp₁z, hp₁k⟩ := hx
    obtain ⟨s₂, _, p₂, hp₂z, hp₂k⟩ := hy
    obtain ⟨P₁, hP₁z, hP₁k⟩ :=
      exists_rename_eq_and_mem_ker_pow_of_subset φ (Finset.subset_union_left (s₂ := s₂)) hp₁z hp₁k
    obtain ⟨P₂, hP₂z, hP₂k⟩ :=
      exists_rename_eq_and_mem_ker_pow_of_subset φ (Finset.subset_union_right (s₁ := s₁)) hp₂z hp₂k
    refine ⟨s₁ ∪ s₂, hs₁.trans Finset.subset_union_left, P₁ + P₂, ?_, ?_⟩
    · rw [map_add, hP₁z, hP₂z]
    · exact Ideal.add_mem _ hP₁k hP₂k

end Truncation

end Stacks.Sites.Conormal

end
