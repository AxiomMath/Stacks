module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulHighDegreeOrthogonality

/-!
# Detecting boundedness: Hom-vanishing is insensitive to one canonical truncation

Let `X` be a quasi-compact and quasi-separated scheme, let `P` be a perfect object of `D(𝒪_X)`,
let `E` be an object of `D_QCoh(𝒪_X)` and let `a` be an integer. [Stacks, Tag 0GEL] says that

1. `Hom(P⟦-i⟧, E) = 0` for `i ≫ 0`, and
2. `Hom(P⟦-i⟧, τ_{≥a}E) = 0` for `i ≫ 0`

are equivalent, and [Stacks, Tag 0GEM] says the same of

1. `Hom(P⟦-i⟧, E) = 0` for `i ≪ 0`, and
2. `Hom(P⟦-i⟧, τ_{≤a}E) = 0` for `i ≪ 0`.

Both reduce, through the truncation triangle, to the claim that the *other* truncation half
receives nothing from the relevant shifts of `P`: `Hom(P⟦-i⟧, τ_{<a}E) = 0` for `i ≫ 0` in the
first case, `Hom(P⟦-i⟧, τ_{>a}E) = 0` for `i ≪ 0` in the second.

**The two halves are not of equal difficulty, and this file treats them differently.**

For [Stacks, Tag 0GEM] the vanishing is free: `τ_{>a}E` is `≥ a + 1` for the canonical
t-structure, `P⟦-i⟧` is `≤ n + i` once `P` is `≤ n`, and a morphism from an object bounded above
by `c` to an object bounded below by `d > c` is zero. Only boundedness above of `P` is used — no
perfectness, no quasi-coherence, no hypothesis on `X` — so the statement proved here is strictly
more general than the source's, and it is stated at an arbitrary abelian category.

For [Stacks, Tag 0GEL] no such orthogonality exists: a morphism from an object bounded below to
an object bounded above need not vanish, `Ext¹(A/x, A/x) ≠ 0` over `A = k[x]`. What is used
instead is that `P` is perfect, hence locally a bounded complex of finite free modules, so that
`Hom(P⟦-m⟧, −)` sees only the homology of its argument in a window of `r + 1` consecutive
degrees ending at `m`. That window is [Stacks, Tag 09M4], which is **not** formalized in this
repository, and it enters below as the explicit hypothesis `hwindow`. For the sheafified Koszul
complex on an affine scheme the corresponding window *is* proved, as
`Stacks.Koszul.Truncation.subsingleton_hom_koszulObject_shift_of_isLE` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineKoszulWindow.lean`, which is
what [Stacks, Tag 0GEJ] uses; the general perfect object on a quasi-compact quasi-separated
scheme needed here is a different and harder statement.

## Main results

* `Stacks.DerivedTruncation.subsingleton_hom_of_isLE_of_isGE`: there is no nonzero morphism from
  an object bounded above by `c` to an object bounded below by `d`, when `c < d`.
* `Stacks.DerivedTruncation.subsingleton_hom_of_subsingleton_hom_truncLE` and
  `Stacks.DerivedTruncation.subsingleton_hom_truncLE_of_subsingleton_hom`: the triangle
  `τ_{≤a}M ⟶ M ⟶ τ_{≥a+1}M ⟶` transports Hom-vanishing between `M` and `τ_{≤a}M` in both
  directions. These are the `τ_{≤a}` counterparts of
  `Stacks.DerivedTruncation.subsingleton_hom_of_subsingleton_hom_truncGE` and
  `Stacks.DerivedTruncation.subsingleton_hom_truncGE_of_subsingleton_hom`.
* `Stacks.DerivedTruncation.eventually_subsingleton_hom_iff_truncGE`: [Stacks, Tag 0GEL]
  abstractly, granted `hwindow`.
* `Stacks.DerivedTruncation.eventually_subsingleton_hom_iff_truncLE`: [Stacks, Tag 0GEM]
  abstractly, for `P` bounded above.
* `Stacks.Perfect.eventually_subsingleton_hom_iff_truncLE_of_isLE`: [Stacks, Tag 0GEM], on the
  derived category of modules on a scheme.

## Implementation notes

**"For `i ≫ 0`" and "for `i ≪ 0`".** These are `∃ N : ℤ, ∀ i : ℤ, N ≤ i → _` and
`∃ N : ℤ, ∀ i : ℤ, i ≤ N → _`, the idiom already used for eventual statements over `ℤ` in this
repository (for instance
`StacksFrontier/AlgebraicGeometry/AmpleEventualGeneration/Basic.lean`). Vanishing of a Hom-group is
`Subsingleton` of its morphism type, as in the two Koszul orthogonality files; the derived
category is additive, so this says that every morphism is zero.

**`@[stacks 0GEM]` is bare and `@[stacks 0GEL]` is clause-qualified.** The statement carrying
[Stacks, Tag 0GEM] replaces "`P` perfect on a quasi-compact quasi-separated `X`, `E` in
`D_QCoh`" by "`P` bounded above", which is implied by the source's hypotheses and is all the
argument consumes; a consumer holding the source's hypotheses may restrict, so nothing of the
tag is lost. The statement carrying [Stacks, Tag 0GEL], by contrast, *adds* the hypothesis
`hwindow`, which is the content of [Stacks, Tag 09M4] and is not proved anywhere in this
repository; the clause string says so, so that the dashboard does not record the tag as closed on
the strength of the formal part of the argument.

**What is still owed for [Stacks, Tag 0GEL].** Exactly [Stacks, Tag 09M4]: for `K` perfect on a
quasi-compact quasi-separated scheme there are integers `a ≤ b` such that `Hom(K, L) = 0` for
every `L` in `D_QCoh(𝒪_X)` whose homology vanishes in `[a, b]`. Its proof passes through the dual
perfect complex ([Stacks, Tag 08DQ], in this repository as
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/PerfectDual.lean`), the tor-amplitude
spectral sequence, and the uniform vanishing bound of [Stacks, Tag 071L] (in this repository as
`StacksFrontier/AlgebraicGeometry/Cohomology/UniformVanishing/Basic.lean`). None of that is carried
out here.

**What is owed for [Stacks, Tag 0GEM] beyond what is proved.** Only that a perfect object on a
quasi-compact scheme is bounded above. What is available is the local form, [Stacks, Tag 0FEP] as
`Stacks.AlgebraicGeometry.PerfectCohomology.locally_finite_homology`
(`StacksFrontier/AlgebraicGeometry/Perfect/PseudoCoherentComplex/LocallyFiniteCohomology.lean`), and
a global form under a Noetherian hypothesis,
`Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect`
(`StacksFrontier/AlgebraicGeometry/Perfect/PseudoCoherentComplex/PerfectBoundedCoherent.lean`); the
quasi-compactness patch from the former to a global bound over a merely quasi-compact
quasi-separated `X` is not carried out anywhere. So the perfect object's bound is an argument of
the statement below rather than something derived from perfectness.

**Everything carries a free `[HasDerivedCategory.{w} _]` binder** and mentions
`CategoryTheory.HasDerivedCategory.standard` nowhere, matching the two Koszul orthogonality files,
so the results are available at the locally small model as well as at the standard one.

## References

* [Stacks Project, Tag 0GEL](https://stacks.math.columbia.edu/tag/0GEL)
* [Stacks Project, Tag 0GEM](https://stacks.math.columbia.edu/tag/0GEM)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 0GEJ](https://stacks.math.columbia.edu/tag/0GEJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace Stacks.DerivedTruncation

universe w v u

section Truncation

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **No nonzero morphism goes from an object bounded above to an object bounded below it.** If
`Q` is `≤ c` and `M` is `≥ d` for the canonical t-structure and `c < d`, then every morphism
`Q ⟶ M` is zero.

This is `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`, packaged as
subsingletonness of the morphism group, which is the shape in which Hom-vanishing is recorded in
this part of the repository. -/
theorem subsingleton_hom_of_isLE_of_isGE {Q M : DerivedCategory C} (c d : ℤ) (h : c < d)
    (hQ : Q.IsLE c) (hM : M.IsGE d) : Subsingleton (Q ⟶ M) :=
  subsingleton_of_forall_eq 0 fun u =>
    DerivedCategory.TStructure.t.zero_of_isLE_of_isGE u c d h hQ hM

/-- **Hom-vanishing descends from `τ_{≤a}M` to `M`.** If no morphism `K⟦-n⟧ ⟶ τ_{≤a}M` and no
morphism `K⟦-n⟧ ⟶ τ_{≥a+1}M` is nonzero, then no morphism `K⟦-n⟧ ⟶ M` is.

A morphism `K⟦-n⟧ ⟶ M` composes to zero into `τ_{≥a+1}M`, hence factors through `τ_{≤a}M`, which
receives nothing. This is the `τ_{≤a}` counterpart of
`Stacks.DerivedTruncation.subsingleton_hom_of_subsingleton_hom_truncGE`, and it is the direction
"(2) implies (1)" of [Stacks, Tag 0GEM] once the first hypothesis is supplied. -/
theorem subsingleton_hom_of_subsingleton_hom_truncLE {K M : DerivedCategory C} (a n : ℤ)
    (hhigh : Subsingleton (K⟦-n⟧ ⟶ (DerivedCategory.TStructure.t.truncGE (a + 1)).obj M))
    (h : Subsingleton (K⟦-n⟧ ⟶ (DerivedCategory.TStructure.t.truncLE a).obj M)) :
    Subsingleton (K⟦-n⟧ ⟶ M) := by
  refine subsingleton_of_forall_eq 0 fun u => ?_
  obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl M) u (hhigh.allEq _ 0)
  rw [hv, h.allEq v 0]
  exact zero_comp

/-- **Hom-vanishing ascends from `M` to `τ_{≤a}M`.** If no morphism `K⟦-n⟧ ⟶ M` and no morphism
`K⟦-n⟧ ⟶ (τ_{≥a+1}M)⟦-1⟧` is nonzero, then no morphism `K⟦-n⟧ ⟶ τ_{≤a}M` is.

A morphism `K⟦-n⟧ ⟶ τ_{≤a}M` composes to zero into `M`, hence — by the inverse rotation of the
truncation triangle — factors through `(τ_{≥a+1}M)⟦-1⟧`, which receives nothing. This is the
`τ_{≤a}` counterpart of
`Stacks.DerivedTruncation.subsingleton_hom_truncGE_of_subsingleton_hom`, and it is the direction
"(1) implies (2)" of [Stacks, Tag 0GEM] once the first hypothesis is supplied. -/
theorem subsingleton_hom_truncLE_of_subsingleton_hom {K M : DerivedCategory C} (a n : ℤ)
    (hhigh : Subsingleton
      (K⟦-n⟧ ⟶ ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj M)⟦(-1 : ℤ)⟧))
    (h : Subsingleton (K⟦-n⟧ ⟶ M)) :
    Subsingleton (K⟦-n⟧ ⟶ (DerivedCategory.TStructure.t.truncLE a).obj M) := by
  refine subsingleton_of_forall_eq 0 fun u => ?_
  obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl M)) u (h.allEq _ 0)
  rw [hv, hhigh.allEq v 0]
  exact zero_comp

/-! ### [Stacks, Tag 0GEL] and [Stacks, Tag 0GEM], abstractly -/

/-- **[Stacks, Tag 0GEL], abstractly.** For `P` whose Hom-functor is concentrated in a window of
`r + 1` degrees — the hypothesis `hwindow`, which is what perfectness of `P` supplies — and any
`E` and any integer `a`, the vanishing of `Hom(P⟦-i⟧, E)` for `i ≫ 0` is equivalent to the
vanishing of `Hom(P⟦-i⟧, τ_{≥a}E)` for `i ≫ 0`.

Both directions are the truncation triangle `τ_{≤a-1}E ⟶ E ⟶ τ_{≥a}E ⟶` together with the
vanishing of `Hom(P⟦-i⟧, τ_{≤a-1}E)` and of `Hom(P⟦-i⟧, (τ_{≤a-1}E)⟦1⟧)`, both of which
`hwindow` gives once `i > a - 1 + r`. The common threshold is `a + r`. -/
theorem eventually_subsingleton_hom_iff_truncGE {P E : DerivedCategory C} (r : ℕ)
    (hwindow : ∀ (M : DerivedCategory C) (b m : ℤ), M.IsLE b → b + (r : ℤ) < m →
      Subsingleton (P⟦-m⟧ ⟶ M))
    (a : ℤ) :
    (∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P⟦-i⟧ ⟶ E)) ↔
      ∃ N : ℤ, ∀ i : ℤ, N ≤ i →
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj E) := by
  have hiff : ∀ i : ℤ, a + (r : ℤ) ≤ i →
      (Subsingleton (P⟦-i⟧ ⟶ E) ↔
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj E)) := by
    intro i hi
    have hlow : Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncLE (a - 1)).obj E) :=
      hwindow _ (a - 1) i inferInstance (by omega)
    have hlow' : Subsingleton
        (P⟦-i⟧ ⟶ ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E)⟦(1 : ℤ)⟧) :=
      hwindow _ (a - 2) i
        (DerivedCategory.TStructure.t.isLE_shift _ (a - 1) 1 (a - 2) (by omega)) (by omega)
    exact ⟨subsingleton_hom_truncGE_of_subsingleton_hom a i hlow',
      subsingleton_hom_of_subsingleton_hom_truncGE a i hlow⟩
  simp only [← Filter.eventually_atTop]
  exact Filter.eventually_congr ((Filter.eventually_ge_atTop (a + r)).mono hiff)

/-- **[Stacks, Tag 0GEM], abstractly.** For `P` bounded above by `nP` and any `E` and any integer
`a`, the vanishing of `Hom(P⟦-i⟧, E)` for `i ≪ 0` is equivalent to the vanishing of
`Hom(P⟦-i⟧, τ_{≤a}E)` for `i ≪ 0`.

Both directions are the truncation triangle `τ_{≤a}E ⟶ E ⟶ τ_{≥a+1}E ⟶` together with the
vanishing of `Hom(P⟦-i⟧, τ_{≥a+1}E)` and of `Hom(P⟦-i⟧, (τ_{≥a+1}E)⟦-1⟧)`. Here, unlike in the
`τ_{≥a}` case, those come for free from t-structure orthogonality: `P⟦-i⟧` is `≤ nP + i`, the two
targets are `≥ a + 1` and `≥ a + 2`, and `nP + i < a + 1` as soon as `i ≤ a - nP`. The common
threshold is therefore `a - nP`. -/
theorem eventually_subsingleton_hom_iff_truncLE {P E : DerivedCategory C} (nP : ℤ)
    (hP : P.IsLE nP) (a : ℤ) :
    (∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P⟦-i⟧ ⟶ E)) ↔
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N →
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncLE a).obj E) := by
  have hiff : ∀ i : ℤ, i ≤ a - nP →
      (Subsingleton (P⟦-i⟧ ⟶ E) ↔
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncLE a).obj E)) := by
    intro i hi
    have hshift : DerivedCategory.IsLE (P⟦-i⟧) (nP + i) :=
      DerivedCategory.TStructure.t.isLE_shift P nP (-i) (nP + i) (by omega)
    have hhigh : Subsingleton
        (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncGE (a + 1)).obj E) :=
      subsingleton_hom_of_isLE_of_isGE (nP + i) (a + 1) (by omega) hshift inferInstance
    have hhigh' : Subsingleton
        (P⟦-i⟧ ⟶ ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E)⟦(-1 : ℤ)⟧) :=
      subsingleton_hom_of_isLE_of_isGE (nP + i) (a + 2) (by omega) hshift
        (DerivedCategory.TStructure.t.isGE_shift _ (a + 1) (-1) (a + 2) (by omega))
    exact ⟨subsingleton_hom_truncLE_of_subsingleton_hom a i hhigh',
      subsingleton_hom_of_subsingleton_hom_truncLE a i hhigh⟩
  simp only [← Filter.eventually_atBot]
  exact Filter.eventually_congr ((Filter.eventually_le_atBot (a - nP)).mono hiff)

end Truncation

end Stacks.DerivedTruncation

/-! ### The two tags, on the derived category of modules on a scheme -/

namespace Stacks.Perfect

universe w u

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

/-- **[Stacks, Tag 0GEM].** Let `X` be a scheme, let `P` and `E` be objects of `D(𝒪_X)` with `P`
bounded above by `nP`, and let `a` be an integer. Then `Hom(P⟦-i⟧, E) = 0` for `i ≪ 0` if and only
if `Hom(P⟦-i⟧, τ_{≤a}E) = 0` for `i ≪ 0`.

The source states this for `P` perfect on a quasi-compact quasi-separated scheme and `E` in
`D_QCoh(𝒪_X)`; the argument consumes only boundedness above of `P`, which those hypotheses imply,
so the statement here is strictly more general and a consumer holding the source's hypotheses may
restrict. The vanishing that makes the truncation triangle harmless is pure t-structure
orthogonality: `P⟦-i⟧` is `≤ nP + i`, while `τ_{>a}E` is `≥ a + 1`, and `nP + i < a + 1` for
`i ≪ 0`. -/
@[stacks 0GEM]
theorem eventually_subsingleton_hom_iff_truncLE_of_isLE
    (P E : DerivedCategory X.Modules) (nP : ℤ) (hP : P.IsLE nP) (a : ℤ) :
    (∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P⟦-i⟧ ⟶ E)) ↔
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N →
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncLE a).obj E) :=
  Stacks.DerivedTruncation.eventually_subsingleton_hom_iff_truncLE nP hP a

end Stacks.Perfect

end
