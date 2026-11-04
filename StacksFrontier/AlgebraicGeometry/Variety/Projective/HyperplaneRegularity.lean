module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.FieldTheory.RatFunc.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.Normalized
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwistQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.Regularity
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Castelnuovo–Mumford regularity restricts to a hyperplane, and advances by one

Let `k` be a field, `n ≥ 1`, and let `ℱ` be a coherent sheaf on `ℙⁿ_k`. Tag 08A5 says that if
`ℱ` is `m`-regular then so is its restriction `𝒢` to a hyperplane `H ≅ ℙ^{n-1}_k`. This file
proves the cohomological content of that statement, and then runs the induction on `n` of
Tag 08A6: an `m`-regular coherent sheaf on `ℙⁿ_k` is `(m + 1)`-regular.

## Main definitions

* `AlgebraicGeometry.HasHyperplaneRestrictionSequences` packages the twisted hyperplane
  restriction sequences of [Stacks, Tag 08A0], transported to `ℙ^{n-1}_k` along the
  identification of [Stacks, Tag 089Z].
* `AlgebraicGeometry.HasHyperplaneRestrictionData` is that package made uniform in the
  dimension: every coherent sheaf on `ℙᴺ_k`, for every `N ≥ 1`, admits such a hyperplane and
  such sequences. This is what an induction on the dimension consumes.

## Main results

* `AlgebraicGeometry.isMRegular_of_hyperplaneRestriction`: the argument of [Stacks, Tag 08A5].
  In that situation, `m`-regularity of `ℱ` on `ℙⁿ_k` gives `m`-regularity of `𝒢` on
  `ℙ^{n-1}_k`. Tag 08A5 for the hyperplane of [Stacks, Tag 08A0], the sequences constructed, is
  `AlgebraicGeometry.exists_hyperplane_isMRegular_pullback`.
* `AlgebraicGeometry.hasHyperplaneRestrictionData`: over an infinite field the hyperplane
  restriction data exists in every positive dimension, so the hypothesis of
  `AlgebraicGeometry.isMRegular_of_hyperplaneRestriction` is discharged there.
* `AlgebraicGeometry.isMRegular_add_one`: **[Stacks, Tag 08A6].** An `m`-regular coherent sheaf
  on `ℙⁿ_k` is `(m + 1)`-regular, for any field `k` and any `n ≥ 0`.

## The mathematics

Write `j : ℙ^{n-1}_k ⟶ ℙⁿ_k` for the hyperplane inclusion and `d = m - q`. The restriction
sequence, twisted by `d`, reads

`0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ j_*𝒢(d) ⟶ 0`,

and `H^•(ℙⁿ_k, -)` is a cohomological `δ`-functor on module sheaves — it is the right derived
functor of global sections, and `rightDerivedDeltaFunctorOfEnoughInjectives` makes the long
exact sequence available because the category of module sheaves is Grothendieck abelian and so
has enough injectives. The relevant three consecutive terms are

`H^q(ℙⁿ_k, ℱ(m-q)) ⟶ H^q(ℙⁿ_k, j_*𝒢(m-q)) ⟶ H^{q+1}(ℙⁿ_k, ℱ(m-q-1))`.

For `1 ≤ q ≤ n-1` the left term vanishes by `m`-regularity at index `q`, and the right term —
whose twist is `m - (q+1)` — vanishes by `m`-regularity at index `q+1`, which is legitimate
exactly because `q ≤ n-1` forces `q+1 ≤ n`. So the middle term vanishes. Finally `j` is an
affine morphism and `𝒢(m-q)` is quasi-coherent, so
`Stacks.AffineCohomologyResolution.cohomologyPushforwardIso` identifies that middle term with
`H^q(ℙ^{n-1}_k, 𝒢(m-q))`, which is the vanishing `m`-regularity of `𝒢` asks for.

Tag 08A6 then runs the induction on `n`. For `n = 0` there is nothing to prove, the range
`1 ≤ i ≤ 0` being empty. For `n ≥ 1`, Tag 08A5 makes `𝒢` `m`-regular and the inductive
hypothesis in dimension `n - 1` makes it `(m+1)`-regular; the segment

`H^i(ℙⁿ_k, ℱ(m-i)) ⟶ H^i(ℙⁿ_k, ℱ(m+1-i)) ⟶ H^i(ℙⁿ_k, j_*𝒢(m+1-i))`

of the same long exact sequence, now twisted by `d = m+1-i`, has its left end killed by
`m`-regularity of `ℱ` at `i` and its right end — which is `H^i(ℙ^{n-1}_k, 𝒢(m+1-i))` — killed
by `(m+1)`-regularity of `𝒢` when `i ≤ n - 1`, and by vanishing above the dimension
([Stacks, Tag 01YS] clause (2)) when `i = n`. The reduction to an **infinite** field, which is
where the hyperplane of Tag 08A0 is available, is [Stacks, Tag 08A4] applied to the field of
rational functions `k(t)`.

## What is carried and what is proved

`AlgebraicGeometry.isMRegular_add_one` is proved under the source's own hypotheses: `k` a field,
`n ≥ 0`, `ℱ` coherent and `m`-regular. Nothing is carried. The restriction sequences it needs
are constructed, uniformly in the dimension and over an infinite field — which is the generality
in which [Stacks, Tag 08A0] asserts them, the hyperplane there being chosen to avoid the
finitely many associated points of `ℱ` — by
`AlgebraicGeometry.hasHyperplaneRestrictionData`, whose content is
`AlgebraicGeometry.exists_restrictionSequences` in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionConstruction.lean`: the
short exact sequence of [Stacks, Tag 08A0], the identification `H ≅ ℙ^{n-1}_k` of
[Stacks, Tag 089Z] and the twisting of [Stacks, Tag 0EGK], each proved elsewhere and transported
there to this spelling.

`AlgebraicGeometry.isMRegular_of_hyperplaneRestriction` (Tag 08A5) keeps those sequences as the
hypothesis `hses`, since it is stated for a single arbitrary hyperplane and restriction rather
than for the one the construction produces; everything downstream of them — the long exact
sequence, the index bookkeeping, the affine cohomology comparison and the vanishing deduction,
which is the whole argument the source gives for Tag 08A5 — is proved, and
`AlgebraicGeometry.hasHyperplaneRestrictionData` discharges the hypothesis over an infinite
field.

## References

* [Stacks Project, Tag 08A6](https://stacks.math.columbia.edu/tag/08A6)
* [Stacks Project, Tag 08A5](https://stacks.math.columbia.edu/tag/08A5)
* [Stacks Project, Tag 08A4](https://stacks.math.columbia.edu/tag/08A4)
* [Stacks Project, Tag 08A3](https://stacks.math.columbia.edu/tag/08A3)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **The twisted hyperplane restriction sequences of [Stacks, Tag 08A0].** For every twist `d`
there is a short exact sequence `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ j_*𝒢(d) ⟶ 0` on `ℙⁿ_k`, where
`j : ℙ^{n-1}_k ⟶ ℙⁿ_k` is the hyperplane cut out by the chosen section of `𝒪(1)` composed with
the identification of that hyperplane with `ℙ^{n-1}_k` ([Stacks, Tag 089Z]), and `𝒢` is the
restriction of `ℱ`.

The first arrow is multiplication by the section and the second is restriction; this predicate
records only that the sequences exist, which is what the proof of [Stacks, Tag 08A5] consumes. -/
public def HasHyperplaneRestrictionSequences {k : Type u} [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules)
    (G : (projectiveSpaceOverRing (n - 1) (.of k)).Modules)
    (j : projectiveSpaceOverRing (n - 1) (.of k) ⟶ projectiveSpaceOverRing n (.of k)) : Prop :=
  ∀ d : ℤ, ∃ (a : projectiveTwist n F (d - 1) ⟶ projectiveTwist n F d)
      (b : projectiveTwist n F d ⟶
        (Scheme.Modules.pushforward j).obj (projectiveTwist (n - 1) G d))
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact

/-- Vanishing of `H^i` of a sheaf on the hyperplane is equivalent to that of its pushforward,
since the inclusion `j` is affine. -/
private theorem isZero_Hgroup_iff_isZero_pushforward {k : Type u} [Field k] {n : ℕ}
    (G : (projectiveSpaceOverRing (n - 1) (.of k)).Modules) [G.IsQuasicoherent]
    (j : projectiveSpaceOverRing (n - 1) (.of k) ⟶ projectiveSpaceOverRing n (.of k))
    [IsAffineHom j] (i : ℕ) (d : ℤ) :
    IsZero (Hgroup (projectiveSpaceOverRing (n - 1) (.of k)).ringCatSheaf ⊤ i
        (projectiveTwist (n - 1) G d)) ↔
      IsZero (((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (secF (projectiveSpaceOverRing n (.of k)).ringCatSheaf ⊤)).functor i).obj
          ((Scheme.Modules.pushforward j).obj (projectiveTwist (n - 1) G d))) :=
  ⟨fun h => IsZero.of_iso h
    ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso j i).app
      ⟨projectiveTwist (n - 1) G d, inferInstance⟩).symm,
    fun h => IsZero.of_iso h
    ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso j i).app
      ⟨projectiveTwist (n - 1) G d, inferInstance⟩)⟩

/-- **The cohomological argument of [Stacks, Tag 08A5].** Given a hyperplane
`j : ℙ^{n-1}_k ⟶ ℙⁿ_k`, the restriction `𝒢` of `ℱ` to it, and the twisted restriction sequences
they fit into — if `ℱ` is `m`-regular on `ℙⁿ_k` then `𝒢` is `m`-regular on `ℙ^{n-1}_k`.

For `1 ≤ q ≤ n-1` the segment
`H^q(ℙⁿ_k, ℱ(m-q)) ⟶ H^q(ℙⁿ_k, j_*𝒢(m-q)) ⟶ H^{q+1}(ℙⁿ_k, ℱ(m-q-1))`
of the long exact sequence has both ends killed by `m`-regularity of `ℱ`, at indices `q` and
`q+1` respectively — the latter is in range precisely because `q ≤ n-1`. The middle term is
`H^q(ℙ^{n-1}_k, 𝒢(m-q))` because `j` is affine and `𝒢(m-q)` is quasi-coherent.

The sequences are an input here. Tag 08A5 itself, with the hyperplane of [Stacks, Tag 08A0] and
`𝒢` its restriction of `ℱ`, the sequences being constructed, is
`AlgebraicGeometry.exists_hyperplane_isMRegular_pullback` in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionRegularity.lean`. -/
public theorem isMRegular_of_hyperplaneRestriction
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (m : ℤ)
    (G : (projectiveSpaceOverRing (n - 1) (.of k)).Modules) [G.IsCoherent]
    (j : projectiveSpaceOverRing (n - 1) (.of k) ⟶ projectiveSpaceOverRing n (.of k))
    [IsAffineHom j]
    (hses : HasHyperplaneRestrictionSequences n F G j)
    (hF : IsMRegular k n F m) :
    IsMRegular k (n - 1) G m := by
  intro q hq hqn
  let _ : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  obtain ⟨a, b, w, hS⟩ := hses (m - q)
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (secF (projectiveSpaceOverRing n (.of k)).ringCatSheaf ⊤)
  have hleft : IsZero ((D.functor q).obj (projectiveTwist n F (m - q))) := hF q hq (by omega)
  have hright : IsZero ((D.functor (q + 1)).obj (projectiveTwist n F (m - q - 1))) := by
    have h := hF (q + 1) (by omega) (by omega)
    rwa [show m - ((q + 1 : ℕ) : ℤ) = m - q - 1 by push_cast; ring] at h
  exact (isZero_Hgroup_iff_isZero_pushforward G j q _).mpr
    ((D.scδ₁_exact hS q).isZero_of_both_isZero hleft hright)

/-! ### Regularity advances by one -/

/-- **The hyperplane restriction data of [Stacks, Tag 08A0], uniformly in the dimension.** For
every `N ≥ 1` and every coherent sheaf `ℱ` on `ℙᴺ_k` there are a hyperplane
`j : ℙ^{N-1}_k ⟶ ℙᴺ_k`, a coherent restriction `𝒢` of `ℱ` to it, and the twisted restriction
sequences `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ j_*𝒢(d) ⟶ 0` that `HasHyperplaneRestrictionSequences`
records.

An induction on the dimension needs the data in every dimension it passes through, which is why
the dimension is quantified here rather than fixed. -/
public def HasHyperplaneRestrictionData (k : Type u) [Field k] : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ F : (projectiveSpaceOverRing N (.of k)).Modules, F.IsCoherent →
    ∃ (G : (projectiveSpaceOverRing (N - 1) (.of k)).Modules) (_ : G.IsCoherent)
      (j : projectiveSpaceOverRing (N - 1) (.of k) ⟶ projectiveSpaceOverRing N (.of k))
      (_ : IsAffineHom j), HasHyperplaneRestrictionSequences N F G j

/-- The induction on the dimension behind [Stacks, Tag 08A6], over a field that carries the
hyperplane restriction data of [Stacks, Tag 08A0] in every positive dimension. -/
private theorem isMRegular_add_one_of_hasData (k : Type u) [Field k]
    (hres : HasHyperplaneRestrictionData k) (n : ℕ) :
    ∀ (F : (projectiveSpaceOverRing n (.of k)).Modules) (hF : F.IsCoherent) (m : ℤ),
      @IsMRegular k _ n F hF m → @IsMRegular k _ n F hF (m + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hFc m hFreg
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · intro i hi hin
      omega
    · obtain ⟨G, hGc, j, hjaff, hses⟩ := hres n hn F hFc
      let _ : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
      have hG' : @IsMRegular k _ (n - 1) G hGc (m + 1) := ih (n - 1) (by omega) G hGc m
        (isMRegular_of_hyperplaneRestriction k n hn F m G j hses hFreg)
      intro i hi hin
      obtain ⟨a, b, w, hS⟩ := hses (m + 1 - (i : ℤ))
      let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (secF (projectiveSpaceOverRing n (.of k)).ringCatSheaf ⊤)
      have hleft : IsZero ((D.functor i).obj
          (projectiveTwist n F (m + 1 - (i : ℤ) - 1))) := by
        rw [show m + 1 - (i : ℤ) - 1 = m - (i : ℤ) by ring]
        exact hFreg i hi hin
      have hdown : IsZero (Hgroup (projectiveSpaceOverRing (n - 1) (.of k)).ringCatSheaf ⊤ i
          (projectiveTwist (n - 1) G (m + 1 - (i : ℤ)))) := by
        by_cases hi1 : i ≤ n - 1
        · exact hG' i hi hi1
        · exact Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt (n - 1) (.of k)
            (projectiveTwist (n - 1) G (m + 1 - (i : ℤ))) i (by omega)
      exact (D.exact_map hS i).isZero_of_both_isZero hleft
        ((isZero_Hgroup_iff_isZero_pushforward G j i _).mp hdown)

/-- The field of rational functions over a field is infinite: the powers of `t` are distinct.

This is the infinite extension to which [Stacks, Tag 08A6] and [Stacks, Tag 08AC] both reduce, so
it is stated publicly rather than inside this file. -/
theorem infinite_ratFunc (k : Type u) [Field k] : Infinite (RatFunc k) := by
  apply Infinite.of_injective
    fun e : ℕ => algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ e)
  intro a b hab
  simpa using
    congrArg Polynomial.natDegree (IsFractionRing.injective (Polynomial k) (RatFunc k) hab)

/-- **The hyperplane restriction data of [Stacks, Tag 08A0] over an infinite field.** For every
infinite field `K`, every dimension `N ≥ 1` and every coherent sheaf on `ℙᴺ_K` there are a
hyperplane `j : ℙ^{N-1}_K ⟶ ℙᴺ_K`, a coherent restriction of the sheaf to it, and the twisted
restriction sequences.

This is `AlgebraicGeometry.exists_restrictionSequences`, read at `N = m + 1`; the two statements
are the same, the dimension being written there as `m + 1` so that the hyperplane is `ℙᵐ_K` with
no truncated subtraction. -/
public theorem hasHyperplaneRestrictionData (K : Type u) [Field K] [Infinite K] :
    HasHyperplaneRestrictionData K := by
  intro N hN F hFc
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨G, hGc, j, hjaff, -, -, -, -, hseq⟩ := exists_restrictionSequences K m F hFc
  exact ⟨G, hGc, j, hjaff, hseq⟩

/-- **[Stacks, Tag 08A6].** Let `k` be a field, let `n ≥ 0` and let `ℱ` be a coherent sheaf on
`ℙⁿ_k`. If `ℱ` is `m`-regular then `ℱ` is `(m + 1)`-regular.

The argument is an induction on `n`, vacuous for `n = 0`. Passing to `k(t)`, which is infinite,
changes nothing by [Stacks, Tag 08A4]; there a hyperplane `j : ℙ^{n-1} ⟶ ℙⁿ` is available, the
restriction `𝒢` of `ℱ` to it is `m`-regular by [Stacks, Tag 08A5] and hence `(m+1)`-regular by
induction, and the segment
`H^i(ℙⁿ, ℱ(m-i)) ⟶ H^i(ℙⁿ, ℱ(m+1-i)) ⟶ H^i(ℙ^{n-1}, 𝒢(m+1-i))` of the long exact sequence has
both ends zero — the right one by `(m+1)`-regularity of `𝒢` for `i ≤ n-1`, and by vanishing
above the dimension for `i = n`. -/
@[stacks 08A6 "an m-regular coherent sheaf on projective space is (m+1)-regular"]
public theorem isMRegular_add_one
    (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (m : ℤ)
    (hF : IsMRegular k n F m) :
    IsMRegular k n F (m + 1) := by
  let _ : Infinite (RatFunc k) := infinite_ratFunc k
  let _ : IsLocallyNoetherian (projectiveSpaceOverRing n (.of (RatFunc k))) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (.of (RatFunc k)))
  let hFK : ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj F).IsCoherent :=
    isCoherent_pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n) F
  exact (isMRegular_iff_fieldExtension k (RatFunc k) n F (m + 1)).mpr
    (isMRegular_add_one_of_hasData (RatFunc k) (hasHyperplaneRestrictionData (RatFunc k)) n _
      hFK m ((isMRegular_iff_fieldExtension k (RatFunc k) n F m).mp hF))

end AlgebraicGeometry

end
