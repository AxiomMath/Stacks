module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusFixedPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.TopDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# Étale cohomology with constant coefficients `𝐙/p𝐙` of a proper scheme

Let `X` be proper over an algebraically closed field `k` of characteristic `p > 0`. Then every
étale cohomology group `H ^ q (X_étale, 𝐙/p𝐙)` is finite, and it is unchanged by extension of `k`
to a larger algebraically closed field.

The Artin–Schreier sequence `0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` identifies `H ^ q (X_étale, 𝐙/p𝐙)` with
the group of `F`-fixed vectors of `H ^ q (X, 𝒪_X)`, where `F` is the Frobenius-semilinear
endomorphism induced by the Frobenius of `𝒪_X`: the map `F - 1` is surjective in degree `q - 1`,
so the connecting map into degree `q` vanishes and the inclusion of `𝐙/p𝐙` is injective on
cohomology, while exactness in the middle makes its image the whole of `ker (F - 1)`. The group
`H ^ q (X, 𝒪_X)` is a finite-dimensional `k`-vector space because `X` is proper, and the fixed
vectors of a Frobenius-semilinear endomorphism of a finite-dimensional space form a
finite-dimensional module over the prime field.

Extension of the ground field becomes, through that identification, a question of linear algebra:
the fixed vectors of a Frobenius-semilinear endomorphism do not change under base change along an
extension of algebraically closed fields. The number of fixed vectors is `p` to the dimension of
the largest subspace on which the endomorphism is bijective, computed here as the eventual value
of the spans of the images of its iterates; that subspace of the base change is spanned by the
image of its counterpart downstairs, so the two counts agree and the injection of fixed vectors
is onto.

## Main results

* `Stacks.ArtinSchreier.artinSchreierComparison`: the map from the étale cohomology of `𝐙/p𝐙` to
  the cohomology of the structure sheaf.
* `Stacks.ArtinSchreier.frobenius_artinSchreierComparison`: its values are `F`-fixed.
* `Stacks.ArtinSchreier.injective_artinSchreierComparison`: it is injective.
* `Stacks.ArtinSchreier.exists_preimage_artinSchreierComparison`: every `F`-fixed vector is a
  value.
* `Stacks.ArtinSchreier.finite_etaleH_constantZMod_of_isProper`: finiteness of
  `H ^ q (X_étale, 𝐙/p𝐙)` from an Artin–Schreier sequence and a Frobenius comparison.
* `Stacks.ArtinSchreier.bijOn_fixedPoints_of_frobenius_base_change`: the Frobenius-fixed vectors
  of a finite-dimensional vector space are unchanged by extension of the ground field.
* `Stacks.ArtinSchreier.bijective_of_frobenius_base_change`: bijectivity of a map on
  `H ^ q (X_étale, 𝐙/p𝐙)` compatible with a base change of the cohomology of the structure
  sheaves.

[Stacks, Tag 0A3P] itself, with neither the Artin–Schreier sequence nor the comparisons as
inputs, is `Stacks.ArtinSchreier.finite_etaleH_constantZMod_of_isProper_unconditional` (1) and
`Stacks.ArtinSchreier.bijective_etaleCohomologyBaseChangeMap_constantZMod` (2) in
`ProperConstantCoefficientsUnconditional`.

## Implementation notes

The results here take as arguments, in the same shape as the neighbouring modules
`ConstantCoefficientVanishing` and `TopDegreeVanishing`: exactness of the Artin–Schreier
sequence ([Stacks, Tag 0A3J]), as
`Stacks.ArtinSchreier.ArtinSchreierSequence`, and the comparison of the étale cohomology of
`𝐆_a` with the cohomology of the structure sheaf together with the Frobenius-semilinear
description of the Artin–Schreier map on it ([Stacks, Tag 03P2]), as
`Stacks.ArtinSchreier.TopDegreeFrobeniusComparison`. The library constructs both:
`Stacks.ArtinSchreier.constantArtinSchreierSequenceDatum` and
`Stacks.ArtinSchreier.gaFrobeniusComparison`. The comparison is taken in every degree, not
just the top one: the argument here reads the long exact sequence in two consecutive degrees at
once.

The finite dimensionality of `H ^ q (X, 𝒪_X)` is not an argument here. It is a theorem of this
repository for a proper `X`:
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`, which is
[Stacks, Tag 02O6] over a field, applied to the structure sheaf, coherent because a scheme
proper over a field is locally Noetherian.

The second result takes two further arguments: the base-change map `β` on the cohomology of the
structure sheaves, which is the flat base change of [Stacks, Tag 02KH] and is recorded in the shape
that says `H ^ q (X', 𝒪_{X'})` is the base change of `H ^ q (X, 𝒪_X)` along `k ⟶ k'` — additive,
semilinear, injective, with `k'`-spanning image — compatibly with the Frobenius; and the induced map
`γ` on the étale cohomology of `𝐙/p𝐙`, with its compatibility with `β` through the two
Artin–Schreier comparisons. For the canonical `γ`,
`Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap`, the statement is
`Stacks.ArtinSchreier.bijective_etaleCohomologyBaseChangeMap_constantZMod`. The compatibility
hypothesis determines `γ` uniquely, the Artin–Schreier comparison of `X'` being injective. The
second part is also stated for an arbitrary `X'` proper over `k'` rather than for the scalar
extension `X ×_k k'`, the only property of the scalar extension used being that `β` exists.

Étale cohomology is Mathlib's `CategoryTheory.Sheaf.H` on `Scheme.smallEtaleTopology` at the
coefficient universe `u + 1`, and the constant sheaf `𝐙/p𝐙` is
`Stacks.ArtinSchreier.etaleConstantZMod`, both as in [Stacks, Tag 0A3K]. Finiteness is
`Finite` on the underlying type, which for the `𝐙/p𝐙`-module `H ^ q (X_étale, 𝐙/p𝐙)` is the
statement of the source.

## References

* [Stacks Project, Tag 0A3P](https://stacks.math.columbia.edu/tag/0A3P)
* [Stacks Project, Tag 0A3L](https://stacks.math.columbia.edu/tag/0A3L)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the sequence.
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2): the comparison.
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH): the base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w u

namespace Stacks.ArtinSchreier

section Comparison

variable {p : ℕ} (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  (AS : ArtinSchreierSequence p X) (q : ℕ)

/-- **The Artin–Schreier comparison in degree `q`**: the map
`H ^ q (X_étale, 𝐙/p𝐙) ⟶ H ^ q (X, 𝒪_X)` obtained from the inclusion of the constant sheaf in
`𝐆_a` followed by the comparison of the degree-`q` étale cohomology of `𝐆_a` with the cohomology
of the structure sheaf. -/
public noncomputable def artinSchreierComparison
    (cmp : TopDegreeFrobeniusComparison p k f AS.Ga AS.φ q) :
    Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q →+
      cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q :=
  cmp.equiv.toAddMonoidHom.comp (Sheaf.H.map AS.ι q)

/-- The values of the Artin–Schreier comparison are fixed by the Frobenius: the composite of the
inclusion of `𝐙/p𝐙` with the Artin–Schreier map `F - 1` is zero. -/
public theorem frobenius_artinSchreierComparison
    (cmp : TopDegreeFrobeniusComparison p k f AS.Ga AS.φ q)
    (x : Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) :
    cmp.frobenius (artinSchreierComparison k f AS q cmp x) =
      artinSchreierComparison k f AS q cmp x := by
  have hz : Sheaf.H.map AS.φ q (Sheaf.H.map AS.ι q x) = 0 := by
    rw [← Sheaf.H.map_comp_apply, AS.comp_eq_zero, Sheaf.H.map_apply, Ext.mk₀_zero,
      Ext.comp_zero]
  have h := cmp.equiv_map (Sheaf.H.map AS.ι q x)
  rw [hz, map_zero] at h
  exact sub_eq_zero.mp h.symm

/-- **The Artin–Schreier comparison is injective.** Let `X` be a scheme over an algebraically
closed field `k` of characteristic `p > 0` whose structure-sheaf cohomology is
finite-dimensional. Then `H ^ q (X_étale, 𝐙/p𝐙) ⟶ H ^ q (X, 𝒪_X)` is injective.

In degree `0` this is the injectivity of the left-hand map of a short exact sequence. In degree
`q = q' + 1` a class killed by the map comes, by the long exact sequence, from
`H ^ q' (𝐆_a)` under the connecting map; but `F - 1` is surjective on `H ^ q' (𝐆_a)` by
[Stacks, Tag 0A3L], and the composite of `F - 1` with the connecting map is zero. -/
public theorem injective_artinSchreierComparison (hp : 0 < p) [IsAlgClosed k] [CharP k p]
    (cmp : ∀ i : ℕ, TopDegreeFrobeniusComparison p k f AS.Ga AS.φ i)
    (hfin : ∀ i : ℕ, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) i)) :
    Function.Injective (artinSchreierComparison k f AS q (cmp q)) := by
  have hι : Function.Injective (Sheaf.H.map AS.ι q) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    match q with
    | 0 =>
      have : Mono AS.ι := AS.shortExact.mono_f
      exact (injective_iff_map_eq_zero ((Ext.mk₀ AS.ι).postcomp _ (add_zero 0))).mp
        (Ext.postcomp_mk₀_injective_of_mono _ AS.ι) x hx
    | (q' + 1) =>
      obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ AS.shortExact x hx rfl
      obtain ⟨x₂, rfl⟩ := surjective_sheafH_map_of_topDegreeFrobeniusComparison hp k f AS.φ
        (cmp q') (hfin q') x₃
      rw [← hx₃, Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero,
        AS.shortExact.comp_extClass, Ext.comp_zero]
  exact (cmp q).equiv.injective.comp hι

/-- **Every `F`-fixed vector is a value of the Artin–Schreier comparison.** This is exactness of
the long exact sequence at `H ^ q (𝐆_a)`: a class on which the Artin–Schreier map `F - 1`
vanishes comes from `H ^ q (X_étale, 𝐙/p𝐙)`. -/
public theorem exists_preimage_artinSchreierComparison
    (cmp : TopDegreeFrobeniusComparison p k f AS.Ga AS.φ q)
    (v : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q)
    (hv : cmp.frobenius v = v) :
    ∃ x, artinSchreierComparison k f AS q cmp x = v := by
  have hz : Sheaf.H.map AS.φ q (cmp.equiv.symm v) = 0 := by
    refine cmp.equiv.injective ?_
    rw [cmp.equiv_map, cmp.equiv.apply_symm_apply, hv, sub_self, map_zero]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ _ AS.shortExact (cmp.equiv.symm v) hz
  refine ⟨x, ?_⟩
  have : Sheaf.H.map AS.ι q x = cmp.equiv.symm v := hx
  simp only [artinSchreierComparison, AddMonoidHom.coe_comp, Function.comp_apply, this,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]

/-- The cohomology of the structure sheaf of a scheme proper over a field is finite-dimensional. -/
private theorem finiteDimensional_cohomologyOverField_unit {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : ℕ) :
    FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) i) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact finiteDimensional_cohomologyOverField_of_isProper k f (SheafOfModules.unit X.ringCatSheaf) i

/-- **Finiteness from an Artin–Schreier sequence.** Let `X` be a scheme proper over an
algebraically closed field `k` of characteristic `p > 0`, with an Artin–Schreier sequence and a
Frobenius comparison in every degree. Then `H ^ q (X_étale, 𝐙/p𝐙)` is finite for every `q`.

The Artin–Schreier comparison embeds `H ^ q (X_étale, 𝐙/p𝐙)` into the `F`-fixed vectors of
`H ^ q (X, 𝒪_X)`. That group is a finite-dimensional `k`-vector space by [Stacks, Tag 02O6],
`X` being proper over `k`, so its `F`-fixed vectors form a finite-dimensional module over the
prime field `𝐙/p𝐙` by [Stacks, Tag 0A3L], hence a finite set. -/
public theorem finite_etaleH_constantZMod_of_isProper (hp : 0 < p) [IsAlgClosed k] [CharP k p]
    [IsProper f] (cmp : ∀ i : ℕ, TopDegreeFrobeniusComparison p k f AS.Ga AS.φ i) :
    Finite (Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) := by
  have : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have hfin := finiteDimensional_cohomologyOverField_unit f
  let : Module (ZMod p) (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q) :=
    Module.compHom _ (ZMod.castHom (dvd_refl p) k)
  have hker : FiniteDimensional (ZMod p)
      (AddMonoidHom.ker ((cmp q).frobenius - AddMonoidHom.id _)) := by
    have := hfin q
    exact fixedPoints_finiteDimensional_of_frobenius_semilinear p k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q) (cmp q).frobenius
      (cmp q).frobenius_smul
  have : Finite (AddMonoidHom.ker ((cmp q).frobenius - AddMonoidHom.id
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q))) :=
    Module.finite_of_finite (ZMod p)
  have hmem : ∀ x, artinSchreierComparison k f AS q (cmp q) x ∈
      AddMonoidHom.ker ((cmp q).frobenius - AddMonoidHom.id _) := by
    intro x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]
    exact frobenius_artinSchreierComparison k f AS q (cmp q) x
  refine Finite.of_injective (fun x => (⟨_, hmem x⟩ :
    AddMonoidHom.ker ((cmp q).frobenius - AddMonoidHom.id _))) ?_
  intro a b hab
  exact injective_artinSchreierComparison k f AS q hp cmp hfin (Subtype.ext_iff.mp hab)

end Comparison

/-! ### Fixed vectors of a Frobenius-semilinear endomorphism under extension of the field -/

section FixedVectors

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

private lemma iterate_map_smul {p : ℕ} (F : V →+ V)
    (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v) (n : ℕ) (c : k) (v : V) :
    F^[n] (c • v) = c ^ p ^ n • F^[n] v := by
  induction n generalizing c v with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hF, ih, ← pow_mul, ← pow_succ']

/-- The span of the image of the `n`-fold iterate of an additive endomorphism. For a
Frobenius-semilinear endomorphism of a finite-dimensional space these spans decrease to the
largest subspace on which the endomorphism acts bijectively. -/
private def iterateSpan (k : Type*) [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (F : V →+ V) (n : ℕ) : Submodule k V :=
  Submodule.span k (Set.range fun v => F^[n] v)

private lemma mem_iterateSpan (F : V →+ V) (n : ℕ) (v : V) : F^[n] v ∈ iterateSpan k F n :=
  Submodule.subset_span ⟨v, rfl⟩

private lemma iterateSpan_succ_le (F : V →+ V) (n : ℕ) :
    iterateSpan k F (n + 1) ≤ iterateSpan k F n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  exact Submodule.subset_span ⟨F v, (Function.iterate_succ_apply F n v).symm⟩

private lemma iterateSpan_succ {p : ℕ} (F : V →+ V)
    (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v) (n : ℕ) :
    iterateSpan k F (n + 1) = Submodule.span k (F '' (iterateSpan k F n : Set V)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span
      ⟨F^[n] v, mem_iterateSpan F n v, (Function.iterate_succ_apply' F n v).symm⟩
  · rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      exact Submodule.subset_span ⟨y, Function.iterate_succ_apply' F n y⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih => rw [hF]; exact Submodule.smul_mem _ _ ih

private lemma iterateSpan_succ_of_eq {p : ℕ} (F : V →+ V)
    (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v) {m : ℕ}
    (h : iterateSpan k F (m + 1) = iterateSpan k F m) :
    iterateSpan k F (m + 2) = iterateSpan k F (m + 1) := by
  rw [iterateSpan_succ F hF (m + 1), h, ← iterateSpan_succ F hF m]
  exact h

/-- The spans of the images of the iterates of a Frobenius-semilinear endomorphism of a
finite-dimensional space are eventually constant. -/
private lemma exists_iterateSpan_stable [FiniteDimensional k V] {p : ℕ} (F : V →+ V)
    (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v) :
    ∃ N : ℕ, ∀ n, N ≤ n → iterateSpan k F n = iterateSpan k F N := by
  have hex : ∃ N : ℕ, Module.finrank k (iterateSpan k F (N + 1)) =
      Module.finrank k (iterateSpan k F N) := by
    by_contra h
    push Not at h
    have key : ∀ n : ℕ, Module.finrank k (iterateSpan k F n) + n ≤
        Module.finrank k (iterateSpan k F 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hle : Module.finrank k (iterateSpan k F (n + 1)) ≤
            Module.finrank k (iterateSpan k F n) :=
          Submodule.finrank_mono (iterateSpan_succ_le F n)
        have := h n
        omega
    have := key (Module.finrank k (iterateSpan k F 0) + 1)
    omega
  obtain ⟨N, hN⟩ := hex
  have hstep : iterateSpan k F (N + 1) = iterateSpan k F N :=
    Submodule.eq_of_le_of_finrank_eq (iterateSpan_succ_le F N) hN
  have hall : ∀ j : ℕ, iterateSpan k F (N + j + 1) = iterateSpan k F (N + j) := by
    intro j
    induction j with
    | zero => exact hstep
    | succ j ih => exact iterateSpan_succ_of_eq F hF ih
  have hfix : ∀ j : ℕ, iterateSpan k F (N + j) = iterateSpan k F N := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← ih]; exact hall j
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact hfix j

/-- Once the spans of the images of the iterates are constant, the endomorphism is surjective on
that span: the span is spanned by its own image, and the image is already a subspace because
every scalar of an algebraically closed field is a `p`-th power. -/
private lemma exists_apply_eq_of_iterateSpan_stable {p : ℕ} (hp : 0 < p) [IsAlgClosed k]
    (F : V →+ V) (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v) {N : ℕ}
    (hN : iterateSpan k F (N + 1) = iterateSpan k F N) {w : V}
    (hw : w ∈ iterateSpan k F N) : ∃ v ∈ iterateSpan k F N, F v = w := by
  let U := iterateSpan k F N
  let W : Submodule k V :=
    { carrier := {w | ∃ v ∈ U, F v = w}
      zero_mem' := ⟨0, U.zero_mem, map_zero F⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, U.add_mem ha hb, map_add F a b⟩
      smul_mem' := by
        intro c x hx
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hp
        exact ⟨d • a, U.smul_mem d ha, by rw [hF, hd]⟩ }
  have hle : U ≤ W := by
    rw [show U = iterateSpan k F (N + 1) from hN.symm, iterateSpan_succ F hF N]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  exact hle hw

/-- A surjective Frobenius-semilinear endomorphism of a finite-dimensional vector space over an
algebraically closed field of positive characteristic is injective: the images of a basis span,
hence are linearly independent, and a vector in the kernel has all its coordinates `p`-th roots
of `0`. -/
private lemma injective_of_surjective_frobeniusSemilinear {p : ℕ} (hp : 0 < p) [IsAlgClosed k]
    [FiniteDimensional k V] (F : V →+ V) (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v)
    (hsurj : Function.Surjective F) : Function.Injective F := by
  classical
  let b := Module.finBasis k V
  have hsum : ∀ v : V, F v = ∑ i, b.repr v i ^ p • F (b i) := by
    intro v
    calc F v = F (∑ i, b.repr v i • b i) := by rw [b.sum_repr v]
      _ = ∑ i, b.repr v i ^ p • F (b i) := by
          rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hF _ _
  have hspan : ⊤ ≤ Submodule.span k (Set.range fun i => F (b i)) := by
    intro v _
    obtain ⟨u, rfl⟩ := hsurj v
    rw [hsum u]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent k (fun i => F (b i)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h0 : ∑ i, b.repr v i ^ p • F (b i) = 0 := by rw [← hsum v]; exact hv
  have hz := Fintype.linearIndependent_iff.mp hli (fun i => b.repr v i ^ p) h0
  refine b.repr.map_eq_zero_iff.mp ?_
  ext i
  simpa using (pow_eq_zero_iff (by omega : p ≠ 0)).mp (hz i)

/-- **The number of fixed vectors of a Frobenius-semilinear endomorphism** of a
finite-dimensional vector space over an algebraically closed field of characteristic `p > 0`: it
is `p` to the dimension of the largest subspace on which the endomorphism acts bijectively, that
subspace being the eventual value of the spans of the images of the iterates. -/
private lemma natCard_fixedPoints_eq {p : ℕ} [CharP k p] (hp : 0 < p) [IsAlgClosed k]
    [FiniteDimensional k V] (F : V →+ V) (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v)
    {N : ℕ} (hN : iterateSpan k F (N + 1) = iterateSpan k F N) :
    Nat.card {v : V // F v = v} = p ^ Module.finrank k (iterateSpan k F N) := by
  classical
  have hstable : ∀ v : V, v ∈ iterateSpan k F N → F v ∈ iterateSpan k F N := by
    intro v hv
    rw [← hN, iterateSpan_succ F hF N]
    exact Submodule.subset_span ⟨v, hv, rfl⟩
  let U := iterateSpan k F N
  let G : U →+ U := AddMonoidHom.mk' (fun v => ⟨F v.1, hstable v.1 v.2⟩)
    (fun a b => Subtype.ext (map_add F a.1 b.1))
  have hG : ∀ (c : k) (v : U), G (c • v) = c ^ p • G v := fun c v => Subtype.ext (hF c v.1)
  have hGsurj : Function.Surjective G := by
    intro w
    obtain ⟨v, hv, hvw⟩ := exists_apply_eq_of_iterateSpan_stable hp F hF hN w.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  have hGinj : Function.Injective G :=
    injective_of_surjective_frobeniusSemilinear hp G hG hGsurj
  have hcard := natCard_fiber_sub_id_eq p hp G hG hGinj 0
  have hiff : ∀ x : U, G x - x = 0 ↔ F x.1 = x.1 := by
    intro x
    rw [sub_eq_zero, Subtype.ext_iff]
    exact Iff.rfl
  have hmem : ∀ v : V, F v = v → v ∈ U := by
    intro v hv
    have hfix : F^[N] v = v := Function.iterate_fixed hv N
    rw [← hfix]
    exact mem_iterateSpan F N v
  let e : {x : U // G x - x = 0} ≃ {v : V // F v = v} :=
    { toFun := fun x => ⟨x.1.1, (hiff x.1).mp x.2⟩
      invFun := fun v => ⟨⟨v.1, hmem v.1 v.2⟩, (hiff _).mpr v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e]
  exact hcard

/-- **Fixed vectors of a Frobenius-semilinear endomorphism under extension of the base field.**
Let `k` and `k'` be algebraically closed fields of characteristic `p > 0` with a ring map
`φ : k ⟶ k'`, let `V` be a finite-dimensional `k`-vector space with a Frobenius-semilinear
endomorphism `F`, and let `V'` be a `k'`-vector space with a Frobenius-semilinear endomorphism
`F'`. If `β : V ⟶ V'` is additive, semilinear over `φ`, injective, intertwines `F` with `F'` and
has `k'`-spanning image — that is, if `V'` is the base change of `V` along `φ` — then `β` maps
the `F`-fixed vectors of `V` bijectively onto the `F'`-fixed vectors of `V'`.

Both fixed-vector sets are counted by `p` to the dimension of the subspace on which the
endomorphism is bijective, and that subspace of `V'` is spanned by the image of its counterpart
in `V`, so the second count is at most the first; an injection between finite sets with the
first no larger than the second is a bijection. -/
public theorem bijOn_fixedPoints_of_frobenius_base_change {p : ℕ} (hp : 0 < p)
    {k k' : Type*} [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k']
    [CharP k p] [CharP k' p] (φ : k →+* k')
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {V' : Type*} [AddCommGroup V'] [Module k' V']
    (F : V →+ V) (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v)
    (F' : V' →+ V') (hF' : ∀ (c : k') (v : V'), F' (c • v) = c ^ p • F' v)
    (β : V →+ V') (hβ : ∀ (c : k) (v : V), β (c • v) = φ c • β v)
    (hβinj : Function.Injective β) (hβspan : Submodule.span k' (Set.range β) = ⊤)
    (hcomm : ∀ v : V, β (F v) = F' (β v)) :
    Set.BijOn β {v : V | F v = v} {w : V' | F' w = w} := by
  classical
  -- the image under `β` of a `k`-subspace spanned by a family lies in the `k'`-span of its image
  have hmapspan : ∀ {ι : Type} (c : ι → V) {v : V},
      v ∈ Submodule.span k (Set.range c) →
        β v ∈ Submodule.span k' (Set.range fun i => β (c i)) := by
    intro ι c v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih => rw [hβ]; exact Submodule.smul_mem _ _ ih
  let b := Module.finBasis k V
  have hspan' : Submodule.span k' (Set.range fun i => β (b i)) = ⊤ := by
    rw [eq_top_iff, ← hβspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    exact hmapspan b (by rw [b.span_eq]; trivial)
  have : Module.Finite k' V' :=
    ⟨by rw [← hspan']; exact Submodule.fg_span (Set.finite_range _)⟩
  obtain ⟨N, hNs⟩ := exists_iterateSpan_stable F hF
  obtain ⟨N', hNs'⟩ := exists_iterateSpan_stable F' hF'
  set M := max N N' with hM
  have hMF : iterateSpan k F (M + 1) = iterateSpan k F M := by
    rw [hNs (M + 1) (by omega), hNs M (by omega)]
  have hMF' : iterateSpan k' F' (M + 1) = iterateSpan k' F' M := by
    rw [hNs' (M + 1) (by omega), hNs' M (by omega)]
  -- the stable subspace of `V'` is spanned by the image of the stable subspace of `V`
  have hsemi : Function.Semiconj β F F' := hcomm
  have hiter : ∀ v : V, β (F^[M] v) = F'^[M] (β v) := hsemi.iterate_right M
  let bU := Module.finBasis k (iterateSpan k F M)
  let cU : Fin (Module.finrank k (iterateSpan k F M)) → V := fun i => (bU i : V)
  have hUspan : Submodule.span k (Set.range cU) = iterateSpan k F M := by
    have hr : Set.range cU = (iterateSpan k F M).subtype '' Set.range bU := Set.range_comp _ _
    rw [hr, Submodule.span_image, bU.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hkey : ∀ w : V', F'^[M] w ∈ Submodule.span k' (Set.range fun i => β (cU i)) := by
    intro w
    have hw : w ∈ Submodule.span k' (Set.range β) := by rw [hβspan]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [← hiter v]
      exact hmapspan cU (by rw [hUspan]; exact mem_iterateSpan F M v)
    | zero => rw [iterate_map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [iterate_map_add]; exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih => rw [iterate_map_smul F' hF']; exact Submodule.smul_mem _ _ ih
  have hUle : iterateSpan k' F' M ≤ Submodule.span k' (Set.range fun i => β (cU i)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    exact hkey w
  have hdim : Module.finrank k' (iterateSpan k' F' M) ≤
      Module.finrank k (iterateSpan k F M) := by
    have : FiniteDimensional k' (Submodule.span k' (Set.range fun i => β (cU i))) :=
      FiniteDimensional.span_of_finite k' (Set.finite_range _)
    have h₁ : Module.finrank k' (iterateSpan k' F' M) ≤
        Module.finrank k' (Submodule.span k' (Set.range fun i => β (cU i))) :=
      Submodule.finrank_mono hUle
    exact h₁.trans ((finrank_range_le_card fun i => β (cU i)).trans (by simp))
  have hcardF := natCard_fixedPoints_eq hp F hF hMF
  have hcardF' := natCard_fixedPoints_eq hp F' hF' hMF'
  have hle : Nat.card {w : V' // F' w = w} ≤ Nat.card {v : V // F v = v} := by
    rw [hcardF, hcardF']
    exact Nat.pow_le_pow_right hp hdim
  -- the restriction of `β` to the fixed vectors
  have hmaps : ∀ v : V, F v = v → F' (β v) = β v := by
    intro v hv
    rw [← hcomm, hv]
  let g : {v : V // F v = v} → {w : V' // F' w = w} := fun v => ⟨β v.1, hmaps v.1 v.2⟩
  have hginj : Function.Injective g := fun a b hab =>
    Subtype.ext (hβinj (Subtype.ext_iff.mp hab))
  have hgbij : Function.Bijective g := by
    have : Finite {w : V' // F' w = w} := by
      have := natCard_fixedPoints_eq hp F' hF' hMF'
      refine Nat.finite_of_card_ne_zero ?_
      rw [this]
      exact pow_ne_zero _ (by omega)
    refine (Nat.bijective_iff_injective_and_card g).mpr ⟨hginj, le_antisymm ?_ hle⟩
    exact Nat.card_le_card_of_injective g hginj
  refine ⟨fun v hv => hmaps v hv, fun a ha b hb hab => hβinj hab, fun w hw => ?_⟩
  obtain ⟨v, hv⟩ := hgbij.2 ⟨w, hw⟩
  exact ⟨v.1, v.2, Subtype.ext_iff.mp hv⟩

end FixedVectors

/-! ### Invariance of the constant-coefficient cohomology under extension of the ground field -/

section BaseChange

variable {p : ℕ} (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
  (k' : Type u) [Field k'] [IsAlgClosed k'] [CharP k' p] (φ : k →+* k')
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of k')) [IsProper f']
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})]
  (AS : ArtinSchreierSequence p X) (AS' : ArtinSchreierSequence p X') (q : ℕ)

/-- **Bijectivity from a base change of the structure-sheaf cohomology.** Let `X` be proper over an
algebraically closed field `k` of characteristic `p > 0`, let `k'` be another algebraically closed
field with a ring map `φ : k ⟶ k'`, and let `X'` be proper over `k'`. Suppose `β` is the base-change
map on the cohomology of the structure sheaves, so that `H ^ q (X', 𝒪_{X'})` is the base change
along `φ` of `H ^ q (X, 𝒪_X)` compatibly with the Frobenius, and suppose `γ` is a map on the étale
cohomology of `𝐙/p𝐙` compatible with `β` through the two Artin–Schreier comparisons. Then `γ` is
bijective.

The compatibility `hγ` determines `γ` uniquely, the Artin–Schreier comparison of `X'` being
injective. For the scalar extension `X' = X ×_k k'` along an extension of algebraically closed
fields, `β` is the flat base change of [Stacks, Tag 02KH] and `γ` is the canonical map
`Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap`; that case is
`Stacks.ArtinSchreier.bijective_etaleCohomologyBaseChangeMap_constantZMod`.

Both sides are identified with the Frobenius-fixed vectors of the cohomology of the structure
sheaf, finite-dimensional because `X` and `X'` are proper, and
`bijOn_fixedPoints_of_frobenius_base_change` matches the two groups of fixed vectors. -/
public theorem bijective_of_frobenius_base_change (hp : 0 < p)
    (cmp : ∀ i : ℕ, TopDegreeFrobeniusComparison p k f AS.Ga AS.φ i)
    (cmp' : ∀ i : ℕ, TopDegreeFrobeniusComparison p k' f' AS'.Ga AS'.φ i)
    (β : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q →+
      cohomologyOverField k' f' (SheafOfModules.unit X'.ringCatSheaf) q)
    (hβ : ∀ (c : k) (v : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q),
      β (c • v) = φ c • β v)
    (hβinj : Function.Injective β) (hβspan : Submodule.span k' (Set.range β) = ⊤)
    (hβfrob : ∀ v, β ((cmp q).frobenius v) = (cmp' q).frobenius (β v))
    (γ : Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q →+
      Sheaf.H.{w, u + 1} (etaleConstantZMod X' p) q)
    (hγ : ∀ x, artinSchreierComparison k' f' AS' q (cmp' q) (γ x) =
      β (artinSchreierComparison k f AS q (cmp q) x)) :
    Function.Bijective γ := by
  have hfin := finiteDimensional_cohomologyOverField_unit f
  have hfin' := finiteDimensional_cohomologyOverField_unit f'
  have := hfin q
  have hbij := bijOn_fixedPoints_of_frobenius_base_change hp φ (cmp q).frobenius
    (cmp q).frobenius_smul (cmp' q).frobenius (cmp' q).frobenius_smul β hβ hβinj hβspan hβfrob
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · refine injective_artinSchreierComparison k f AS q hp cmp hfin (hβinj ?_)
    rw [← hγ, ← hγ, hab]
  · have hy : (cmp' q).frobenius (artinSchreierComparison k' f' AS' q (cmp' q) y) =
        artinSchreierComparison k' f' AS' q (cmp' q) y :=
      frobenius_artinSchreierComparison k' f' AS' q (cmp' q) y
    obtain ⟨v, hv, hvy⟩ := hbij.surjOn hy
    obtain ⟨x, hx⟩ := exists_preimage_artinSchreierComparison k f AS q (cmp q) v hv
    refine ⟨x, injective_artinSchreierComparison k' f' AS' q hp cmp' hfin' ?_⟩
    rw [hγ, hx, hvy]

end BaseChange

end Stacks.ArtinSchreier

end
