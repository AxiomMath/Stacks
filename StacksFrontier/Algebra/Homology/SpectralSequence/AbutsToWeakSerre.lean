module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo

/-!
# A weak Serre class containing a page of a spectral sequence contains its abutment

Let `𝒜` be an abelian category, let `P` be a weak Serre subcategory of `𝒜` (**Stacks 0754**) and
let `E` be a cohomological spectral sequence in `𝒜` which abuts to a graded object `H` in the
sense of `CategoryTheory.SpectralSequence.AbutsTo`. If every term of one page of `E` belongs to
`P`, then every `H n` belongs to `P`.

This is the content of part (4) of **Stacks 0132** read off the abutment rather than off a double
complex: [Stacks, Tag 0132] states it for the two spectral sequences of a diagonally finite double
complex, and
`CochainComplex.HomologicalComplex₂.isBounded_and_converges_totalFiltration₁` delivers it in that
form only. Consumers which hold a spectral sequence as an abstract `AbutsTo` statement -- the
Čech-to-cohomology spectral sequence of **Stacks 072D** and the pushforward spectral sequences
built on it among them -- cannot use that form, because the double complex has been forgotten.
The hypothesis of diagonal finiteness is not needed here: abutment already asks for a finite
filtration in each degree, which is exactly what the argument consumes.

## Main results

* `CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page`: a weak Serre class containing one
  page of a spectral sequence contains every term of its abutment.
* `CategoryTheory.SpectralSequence.prop_pageInfinity_of_prop_page`: the same for the infinity
  page, which is the step the previous result factors through.

## Implementation notes

The two inputs are that a weak Serre class containing a page contains every later page (the
pages that follow are iterated homology of it) and that an object with a finite filtration whose
graded pieces lie in a weak Serre class lies in it. Both already occur in this development, as
`prop_page_of_le` and `prop_of_filtration`, but privately: in
`StacksFrontier/Algebra/Homology/SpectralSequence/FilteredComplex/Basic.lean`.
They are private there and are reproved here, with the same proofs.

The infinity page is reached at `max r (E.rMin pq)`, not at `E.rMin pq`: the page `r` the
hypothesis is about need not be beyond the stabilisation point, so the comparison
`SpectralSequence.pageInfinityIso` is taken at a page beyond both.

## References

* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A weak Serre class containing one page of a spectral sequence contains every later page: the
pages that follow are iterated homology of it. -/
public lemma prop_page_of_le {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}
    (E : SpectralSequence C c r₀) (P : ObjectProperty C) [P.IsWeakSerreClass] {r : ℤ}
    (hr : r₀ ≤ r) (hpage : ∀ pq : ι, P ((E.page r hr).X pq)) :
    ∀ r' : ℤ, r ≤ r' → ∀ (hr' : r₀ ≤ r') (pq : ι), P ((E.page r' hr').X pq) := by
  intro r' hle
  induction r', hle using Int.leInduction with
  | base => exact fun _ pq => hpage pq
  | succ m hm ih =>
    have hm0 : r₀ ≤ m := hr.trans hm
    refine fun _ pq => P.prop_of_iso (E.iso m (m + 1) pq rfl hm0) ?_
    exact P.prop_of_isColimit_cokernelCofork
      ((E.page m hm0).homologyIsCokernel ((c m).prev pq) pq rfl) (ih hm0 _)
      (P.prop_of_isLimit_kernelFork ((E.page m hm0).cyclesIsKernel pq ((c m).next pq) rfl)
        (ih hm0 pq) (ih hm0 _))

/-- **A weak Serre class containing one page of a spectral sequence contains its infinity page.**
At a position where the spectral sequence stabilises, the infinity page is a term of every
sufficiently late page, and the later pages are iterated homology of the given one. -/
theorem prop_pageInfinity_of_prop_page {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}
    (E : SpectralSequence C c r₀) (P : ObjectProperty C) [P.IsWeakSerreClass] {r : ℤ}
    (hr : r₀ ≤ r) (hpage : ∀ pq : ι, P ((E.page r hr).X pq)) (pq : ι)
    [E.HasPageInfinityAt pq] : P (E.pageInfinity pq) := by
  have h₁ : E.HasEdgeMonoAtFrom pq (max r (E.rMin pq)) :=
    E.hasEdgeMonoAtFrom_of_GE pq (E.rMin pq) _ (le_max_right _ _)
  have h₂ : E.HasEdgeEpiAtFrom pq (max r (E.rMin pq)) :=
    E.hasEdgeEpiAtFrom_of_GE pq (E.rMin pq) _ (le_max_right _ _)
  exact P.prop_of_iso (E.pageInfinityIso pq (max r (E.rMin pq))).symm
    (prop_page_of_le E P hr hpage (max r (E.rMin pq)) (le_max_left _ _) _ pq)

/-- **A weak Serre class containing one page of a spectral sequence contains its abutment.** If
the cohomological spectral sequence `E` abuts to `H` in the sense of
`CategoryTheory.SpectralSequence.AbutsTo` and every term of the page `r` of `E` lies in the weak
Serre class `P`, then every `H n` lies in `P`.

This is part (4) of [Stacks, Tag 0132], stated at the abutment: the filtration of `H n` which
abutment provides is finite and its graded pieces are the terms of the infinity page, which lie
in `P` by `CategoryTheory.SpectralSequence.prop_pageInfinity_of_prop_page`. -/
theorem AbutsTo.prop_of_prop_page {r₀ : ℤ} {E : CohomologicalSpectralSequence C r₀} {H : ℤ → C}
    (hE : AbutsTo E H) (P : ObjectProperty C) [P.IsWeakSerreClass] {r : ℤ} (hr : r₀ ≤ r)
    (hpage : ∀ pq : ℤ × ℤ, P ((E.page r hr).X pq)) (n : ℤ) : P (H n) := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  obtain ⟨a, b, hab, htop, hbot⟩ := hbounds n
  refine prop_of_filtration P (F n) (fun p => hF n (by omega)) a b hab htop hbot fun p => ?_
  obtain ⟨q, rfl⟩ : ∃ q, n = p + q := ⟨n - p, by omega⟩
  have : E.HasPageInfinityAt (p, q) := hinf p q
  exact P.prop_of_iso (hgr p q).some (prop_pageInfinity_of_prop_page E P hr hpage (p, q))

end CategoryTheory.SpectralSequence

end
