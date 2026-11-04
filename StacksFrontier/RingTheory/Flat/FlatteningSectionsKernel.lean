module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.QuotientInf

/-!
# Flattening modulo the sections kernel of a quasi-compact open

Let `A` be a commutative ring, `I ⊆ A` an ideal, `M` an `A`-module and
`U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ Spec A` a quasi-compact open. Stacks 0ATC says that if `M/IM` is flat
over `A/I` and `M` is flat over `U`, then `M/I₂M` is flat over `A/I₂`, where
`I₂ = Ker (I → Γ(U, I/I²))`.

Because `U` is covered by the `D(f_i)` and `I/I²` is a sheaf on `Spec A`, an element of `I` dies
in `Γ(U, I/I²)` exactly when it dies in each `(I/I²)_{f_i}`, i.e. exactly when
`f_i ^ n • x ∈ I²` for some `n` and each `i`. That is `Stacks.sectionsKernel`, and the hypothesis
"`M` is flat over `U`" is flatness of `M_{f_i}` over `A_{f_i}` for each `i`, flatness being local
on `Spec A`.

In that form the lemma is a consequence of two results already in the library, with no sheaf
theory: Stacks 051I produces flatness modulo `idealTwo I A_{f_i} = (I²A_{f_i}) ∩ A` from flatness
of `M/IM` over `A/I` and flatness of `M_{f_i}` over `A_{f_i}`, and Stacks 0522
(`Module.Flat.quotient_inf`) intersects finitely many flattening ideals. The intersection taken
is over the `r` ideals `idealTwo I A_{f_i}` **together with `I` itself** — the first hypothesis
contributes `I` to the family, and that is what cuts the intersection down from
`⨅ i, idealTwo I A_{f_i}`, which need not be contained in `I`, to `I₂`.

## Main definitions

* `Stacks.sectionsKernel I f` is the ideal `I₂ = Ker (I → Γ(U, I/I²))` for the quasi-compact
  open `U = ⋃ i, D(f i)`, written algebraically.

## Main results

* `Stacks.mem_sectionsKernel_iff`: membership in `I₂` is `x ∈ I` together with
  `∃ n, f i ^ n * x ∈ I ^ 2` for each `i`, which is the vanishing of `x` in `Γ(U, I/I²)`.
* `Stacks.flat_quotient_sectionsKernel`: Stacks 0ATC.

## Implementation notes

The index type of the cover is an arbitrary `Finite` type rather than `Fin r`: quasi-compactness
of `U` is what makes it finite, and nothing else about it is used. No hypothesis is placed on `A`
— Stacks 0ATC assumes `A` local, and the proof does not use it.

`Stacks.sectionsKernel` is defined as `I ⊓ ⨅ i, idealTwo I (Localization.Away (f i))` rather than
by the elementwise condition, so that `Module.Flat.quotient_inf` applies to it directly;
`Stacks.mem_sectionsKernel_iff` is the comparison with the elementwise condition, and it is what
identifies the ideal with the one in the source. The intersection over the family together with
`I` is realized as an infimum indexed by `Option ι`, so that the finite-index iteration of
`Module.Flat.quotient_inf` is run once.

## References

* [Stacks Project, Tag 051I](https://stacks.math.columbia.edu/tag/051I)
* [Stacks Project, Tag 0522](https://stacks.math.columbia.edu/tag/0522)
* [Stacks Project, Tag 0ATC](https://stacks.math.columbia.edu/tag/0ATC)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u v w

open TensorProduct

namespace Stacks

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- Flatness of the reductions modulo a finite family of ideals descends to the intersection of
the family, by iterating the binary case `Module.Flat.quotient_inf` (Stacks 0522). -/
theorem flat_quotient_iInf {κ : Type w} [Finite κ] (J : κ → Ideal A)
    (hJ : ∀ k, Module.Flat (A ⧸ J k) (M ⧸ J k • (⊤ : Submodule A M))) :
    Module.Flat (A ⧸ ⨅ k, J k) (M ⧸ (⨅ k, J k) • (⊤ : Submodule A M)) := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  have hfin : ∀ s : Finset κ, Module.Flat (A ⧸ s.inf J) (M ⧸ s.inf J • (⊤ : Submodule A M)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      rw [Finset.inf_empty, Module.Flat.iff_rTensor_injective']
      exact fun _ => Function.injective_of_subsingleton _
    | @insert a s _ ih =>
      rw [Finset.inf_insert]
      exact Module.Flat.quotient_inf (J a) (s.inf J) (hJ a) ih
  have heq : Finset.univ.inf J = ⨅ k, J k := by ext x; simp
  exact heq ▸ hfin Finset.univ

/-- The ideal `I₂ = Ker (I → Γ(U, I/I²))` of Stacks 0ATC, for the quasi-compact open
`U = ⋃ i, D(f i)` of `Spec A`.

It is written as the intersection of `I` with the contractions to `A` of the extensions of `I²`
to the localizations `A_{f i}`; `Stacks.mem_sectionsKernel_iff` identifies it with the
elementwise description. -/
noncomputable def sectionsKernel (I : Ideal A) {ι : Type w} (f : ι → A) : Ideal A :=
  I ⊓ ⨅ i, idealTwo I (Localization.Away (f i))

/-- An element of `A` lies in the contraction of `I²A_f` to `A` exactly when `fⁿ x ∈ I²` for
some `n`, which is the vanishing of the class of `x` in `(I/I²)_f`. -/
theorem mem_idealTwo_away_iff (I : Ideal A) (f x : A) :
    x ∈ idealTwo I (Localization.Away f) ↔ ∃ n : ℕ, f ^ n * x ∈ I ^ 2 := by
  rw [idealTwo, Ideal.mem_comap,
    IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f)]
  exact ⟨fun ⟨m, hm, hmx⟩ => by obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff m f |>.mp hm
                                exact ⟨n, hmx⟩,
    fun ⟨n, hn⟩ => ⟨f ^ n, ⟨n, rfl⟩, hn⟩⟩

/-- **The ideal of Stacks 0ATC, elementwise.** An element of `A` lies in
`Stacks.sectionsKernel I f` exactly when it lies in `I` and its class in `I/I²` dies in every
`(I/I²)_{f i}` — that is, exactly when it dies in `Γ(⋃ i, D(f i), I/I²)`. -/
theorem mem_sectionsKernel_iff (I : Ideal A) {ι : Type w} (f : ι → A) (x : A) :
    x ∈ sectionsKernel I f ↔ x ∈ I ∧ ∀ i, ∃ n : ℕ, f i ^ n * x ∈ I ^ 2 := by
  simp only [sectionsKernel, Submodule.mem_inf, Submodule.mem_iInf, mem_idealTwo_away_iff]

/-- The ideal of Stacks 0ATC is contained in `I`, being the kernel of a map out of `I`. -/
theorem sectionsKernel_le (I : Ideal A) {ι : Type w} (f : ι → A) : sectionsKernel I f ≤ I :=
  inf_le_left

/-- `I²` lies in `sectionsKernel I f`, so the image of `I` in `A ⧸ sectionsKernel I f` is square
zero. -/
theorem sq_le_sectionsKernel (I : Ideal A) {ι : Type w} (f : ι → A) :
    I ^ 2 ≤ sectionsKernel I f :=
  le_inf (by rw [pow_two]; exact Ideal.mul_le_left) (le_iInf fun _ => sq_le_idealTwo I)

/-- Let `I ⊆ A` be an ideal, `M` an `A`-module and `U = ⋃ i, D(f i)` a quasi-compact open of
`Spec A`. If `M/IM` is flat over `A/I` and `M` is flat over `U`, that is `M_{f i}` is flat over
`A_{f i}` for each `i`, then `M/I₂M` is flat over `A/I₂`, where `I₂ = Ker (I → Γ(U, I/I²))` is
`sectionsKernel I f`. -/
@[stacks 0ATC]
theorem flat_quotient_sectionsKernel (I : Ideal A) {ι : Type w} [Finite ι] (f : ι → A)
    (hI : Module.Flat (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)))
    (hU : ∀ i, Module.Flat (Localization.Away (f i)) (Localization.Away (f i) ⊗[A] M)) :
    Module.Flat (A ⧸ sectionsKernel I f)
      (M ⧸ sectionsKernel I f • (⊤ : Submodule A M)) := by
  set J : Option ι → Ideal A :=
    fun o => o.elim I fun i => idealTwo I (Localization.Away (f i)) with hJ
  have hiInf : ⨅ o, J o = sectionsKernel I f := by
    rw [iInf_option]
    rfl
  have hflat : ∀ o, Module.Flat (A ⧸ J o) (M ⧸ J o • (⊤ : Submodule A M)) := by
    intro o
    match o with
    | none => exact hI
    | some i => exact flat_quot_idealTwo_smul_top_of_flat_quot_and_flat_baseChange I hI (hU i)
  exact hiInf ▸ flat_quotient_iInf J hflat

end Stacks

end
