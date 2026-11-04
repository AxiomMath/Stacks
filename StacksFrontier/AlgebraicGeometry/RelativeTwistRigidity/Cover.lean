module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Basic

/-!
# Degreewise generation for a nested pair of affine opens

For a quasi-coherent graded `𝒪_S`-algebra `A` in the sheaf-theoretic form of Situation 01NN and
a nested pair of affine opens `U ⊆ V` of `S`, the restriction `Γ(V, A_k) → Γ(U, A_k)` is **not**
surjective. This file proves the two statements that replace surjectivity: every homogeneous
section over `U` becomes a restriction from `V` after multiplication by a power of any function
of `V` whose basic open sits inside `U`, and those functions generate the unit ideal of
`Γ(S, U)`, so at least one of them is nonvanishing at any prescribed point.

Together these are the generating hypothesis of
`StacksFrontier/AlgebraicGeometry/RelativeTwistRigidity/Criterion.lean`; the assembly is in the
sibling `Basic.lean`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.innerBasicSections`: the sections over `V`
  whose basic open sits inside `U`, restricted to `U`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.span_innerBasicSections`: those sections span
  `Γ(S, U)`, because the basic opens of `V` contained in `U` cover `U`.
* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.exists_basicOpen_strHom_notMem`: hence at every
  point of `Proj Γ(U, A)` one of them is nonvanishing, as a degree-`0` element of the graded ring
  of sections.
* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.exists_pow_smul_eq_resPiece`: **degreewise
  surjectivity for the nested pair**, after multiplying by a power of such a function.
* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.exists_pow_mul_eq_res`: the same, read in the
  graded ring of sections.

## The route

**Where the covering argument happens, and why it is on the base.** The failure of surjectivity
is a statement about the base `S`, not about `Proj`: `Γ(V, 𝒪) → Γ(U, 𝒪)` already fails to be
surjective for `U` a basic open of an affine `V`. So the cover used here is a cover of the *open*
`U` by basic opens of `V`, and nothing covers `Proj Γ(U, A)` — the Proj-level statement that
consumes this is checked pointwise instead. Taking `s` to be the set of **all** sections of `V`
whose basic open lies inside `U` makes the cover canonical, so no choice of a finite cover and no
quasi-compactness argument is needed; `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le` for
the affine `V` supplies a member of `s` around each point of `U`, and
`AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff` for the affine `U` turns the covering
into the span condition.

The nonvanishing statement is then a one-line contradiction: if every one of those sections had
its degree-`0` section inside the relevant homogeneous prime `x`, the comap of `x` along the
structure map would be a prime ideal of `Γ(S, U)` containing the unit ideal.

**Degreewise surjectivity needs quasi-coherence twice, on two different affines.** For
`D = S.basicOpen f` with `f : Γ(S, V)` and `D ≤ U`, surjectivity *onto `D`* comes from
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.exists_resPiece_eq` on the
affine `V`: it gives `a : Γ(V, A_k)` and `m` with `f^m · y|_D = a|_D`. That is an equation over
`D`, not over `U`, and the gap is closed by the *annihilation* half,
`exists_pow_smul_eq_zero` on the affine `U`: the difference `f^m · y - a|_U` restricts to zero on
`D = S.basicOpen (f|_U)`, so a further power of `f|_U` kills it. Both halves are therefore used,
and `U`'s affineness is needed for the second one alone.

## Implementation notes

The restriction `Γ(V, A_k) → Γ(D, A_k)` is invoked with `hf.trans h` as its inclusion witness
rather than with `S.basicOpen_le f`. The two are proofs of the same proposition, hence equal, but
`rw` matches syntactically and the composite `A.resPiece hf k ∘ A.resPiece h k` normalises to the
one spelled with `hf.trans h`; passing the other witness leaves a rewrite that does not fire.
`presheaf_map_map` and `resPiece_comp` are the two functoriality statements this needs, both
proved by `← Functor.map_comp_apply` followed by `rfl`, since the hom sets of a poset are
subsingletons.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)

## Not done here

Nothing is said about a non-affine `U` or `V`, and nothing about `Proj`: the four results are
statements about sections over opens of `S` and about one prime of one graded ring. No tag is
claimed; this supplies an input.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite DirectSum
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeTwistRigidity

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) {U V : S.Opens}

/-- The sections over `V` whose basic open sits inside `U`, restricted to `U`. -/
public def innerBasicSections (h : U ≤ V) : Set Γ(S, U) :=
  S.presheaf.map (homOfLE h).op '' {f : Γ(S, V) | S.basicOpen f ≤ U}

/-- **The basic opens of `V` contained in `U` cover `U`.** -/
public theorem span_innerBasicSections (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : Ideal.span (innerBasicSections (S := S) h) = ⊤ := by
  refine hU.self_le_iSup_basicOpen_iff.mp fun ξ hξ => ?_
  obtain ⟨f, hfU, hξf⟩ := hV.exists_basicOpen_le (V := U) ⟨ξ, hξ⟩ (h hξ)
  have hmem : S.presheaf.map (homOfLE h).op f ∈ innerBasicSections (S := S) h := ⟨f, hfU, rfl⟩
  refine le_iSup (fun t : (innerBasicSections (S := S) h) => S.basicOpen (t : Γ(S, U)))
    ⟨_, hmem⟩ ?_
  rw [Scheme.basicOpen_res]
  exact ⟨hξ, hξf⟩

/-- **At every point of `Proj Γ(U, A)` some basic open of `V` inside `U` is nonvanishing.** -/
public theorem exists_basicOpen_strHom_notMem (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (x : ProjectiveSpectrum (A.grading U)) :
    ∃ f : Γ(S, V), S.basicOpen f ≤ U ∧
      A.strHom U (S.presheaf.map (homOfLE h).op f) ∉ x.asHomogeneousIdeal := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle : Ideal.span (innerBasicSections (S := S) h) ≤
      Ideal.comap (A.strHom U) x.asHomogeneousIdeal.toIdeal := by
    refine Ideal.span_le.mpr ?_
    rintro g ⟨f, hf, rfl⟩
    exact hcon f hf
  rw [span_innerBasicSections (S := S) h hU hV] at hle
  have h1 : (1 : A.sectionRing U) ∈ x.asHomogeneousIdeal.toIdeal := by
    have h2 := hle (Submodule.mem_top (x := (1 : Γ(S, U))))
    rw [Ideal.mem_comap, map_one] at h2
    exact h2
  exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- Restriction of functions is functorial, in the `≤`-indexed spelling. -/
public theorem presheaf_map_map {U V W : S.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (r : Γ(S, W)) :
    S.presheaf.map (homOfLE hUV).op (S.presheaf.map (homOfLE hVW).op r) =
      S.presheaf.map (homOfLE (hUV.trans hVW)).op r := by
  rw [← Functor.map_comp_apply]
  rfl

/-- Restriction of homogeneous sections is functorial. -/
public theorem resPiece_comp {U V W : S.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (n : ℕ)
    (y : A.sectionPieces W n) :
    A.resPiece hUV n (A.resPiece hVW n y) = A.resPiece (hUV.trans hVW) n y := by
  rw [A.resPiece_apply, A.resPiece_apply, A.resPiece_apply, ← Functor.map_comp_apply]
  rfl

/-- Restriction as a graded ring homomorphism is restriction as a ring homomorphism. -/
public theorem res_apply {U V : S.Opens} (h : U ≤ V) (x : A.sectionRing V) :
    A.res h x = A.resRingHom h x := rfl

/-! ### Degreewise surjectivity for a nested affine pair -/

/-- **Degreewise surjectivity after multiplying by a power of a function cutting out a basic
open inside the smaller member of a nested affine pair.** -/
public theorem exists_pow_smul_eq_resPiece (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (f : Γ(S, V)) (hf : S.basicOpen f ≤ U) (k : ℕ)
    (y : A.sectionPieces U k) :
    ∃ (N : ℕ) (b : A.sectionPieces V k),
      S.presheaf.map (homOfLE h).op f ^ N • y = A.resPiece h k b := by
  have hD : S.basicOpen f = S.basicOpen (S.presheaf.map (homOfLE h).op f) := by
    rw [Scheme.basicOpen_res]
    exact (inf_eq_right.mpr hf).symm
  obtain ⟨a, m, hm⟩ := A.exists_resPiece_eq (U := V) (V := S.basicOpen f) hV f rfl
    (hf.trans h) k (A.resPiece hf k y)
  have hd : A.resPiece hf k
      (S.presheaf.map (homOfLE h).op f ^ m • y - A.resPiece h k a) = 0 := by
    rw [map_sub, A.resPiece_smul, resPiece_comp A, map_pow, presheaf_map_map, ← map_pow, hm,
      sub_self]
  obtain ⟨l, hl⟩ := A.exists_pow_smul_eq_zero (U := U) (V := S.basicOpen f) hU
    (S.presheaf.map (homOfLE h).op f) hD hf k _ hd
  have h1 : S.presheaf.map (homOfLE h).op f ^ l •
      (S.presheaf.map (homOfLE h).op f ^ m • y) =
      S.presheaf.map (homOfLE h).op f ^ l • A.resPiece h k a := by
    rw [← sub_eq_zero, ← smul_sub]
    exact hl
  refine ⟨l + m, f ^ l • a, ?_⟩
  rw [A.resPiece_smul, map_pow, ← h1, smul_smul, ← pow_add]

/-- **The ring-level form of degreewise surjectivity.** -/
public theorem exists_pow_mul_eq_res (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (f : Γ(S, V)) (hf : S.basicOpen f ≤ U) (k : ℕ) (a : A.grading U k) :
    ∃ (N : ℕ) (c : A.grading V k),
      (a : A.sectionRing U) * A.strHom U (S.presheaf.map (homOfLE h).op f ^ N) =
        A.res h (c : A.sectionRing V) := by
  obtain ⟨y, hy⟩ := a.2
  obtain ⟨N, b, hb⟩ := exists_pow_smul_eq_resPiece A h hU hV f hf k y
  refine ⟨N, ⟨DirectSum.of (A.sectionPieces V) k b, A.of_mem_grading V b⟩, ?_⟩
  rw [← hy, mul_comm, A.strHom_mul_of, hb, res_apply A, A.resRingHom_of]

end Stacks.AlgebraicGeometry.RelativeTwistRigidity

end
