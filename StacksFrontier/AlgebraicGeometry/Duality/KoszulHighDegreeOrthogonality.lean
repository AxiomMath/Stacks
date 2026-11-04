module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulTruncatedOrthogonality
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineKoszulWindow

/-!
# Orthogonality in high degrees to an object killed by the left adjoint

Let `L ⊣ R` be an adjunction between the derived categories of two abelian categories and let `K`
be an object of the source killed by `L`. Think of `L` as restriction `j^*` to an open subscheme,
of `R` as derived direct image `Rj_*`, and of `K` as the Koszul complex on generators of the ideal
cutting out the closed complement. For an integer `a`, [Stacks, Tag 0GEJ] compares two conditions
on an object `E` of the source:

1. the truncation `τ_{≥a}(E ⟶ R (L E))` of the unit is invertible, and
2. every morphism `K⟦-n⟧ ⟶ E` vanishes for every `n ≥ a`.

This file proves both implications, for `E` with quasi-coherent cohomology sheaves:
(2) at `a` implies (1) at `a`, and (1) at `a` implies (2) at `a + r`. The companion
`StacksFrontier/AlgebraicGeometry/Duality/KoszulTruncatedOrthogonality.lean` treats `τ_{≤a}` in place
of `τ_{≥a}`, where the shifts come out the other way round.

## The two routes

The forward implication (2) ⟹ (1) goes through the cone `N` of the unit, as in the `τ_{≤a}` case:
`Hom(K⟦-n⟧, N) ≅ Hom(K⟦-n-1⟧, E)` because `K` is killed by `L`, so (2) at `a` makes `N` right
orthogonal to `K⟦-n⟧` for every `n ≥ a - 1`, and `τ_{≥a-1}N = 0` is exactly what makes `τ_{≥a}` of
the unit invertible. The commutative algebra sits in the passage from that orthogonality to the
vanishing of the homology of `N`, and that is
`Stacks.Koszul.Truncation.isZero_homology_of_forall_hom_koszulObject_eq_zero` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineComparison.lean`.

The reverse implication (1) ⟹ (2) does **not** go through the cone, and this is where `τ_{≥a}`
differs from `τ_{≤a}`. For `τ_{≤a}` the lost degree is recovered from one-sided boundedness of
`K`, which the canonical t-structure supplies for free. For `τ_{≥a}` no such orthogonality is
available — a morphism from an object bounded below to an object bounded above need not vanish,
`Hom(A/x, (A/x)⟦1⟧) = Ext¹(A/x, A/x) ≠ 0` over `A = k[x]` — and what is used instead is that `K`
is a *perfect* complex, concentrated in degrees `-r, …, 0`, so that `Hom(K⟦-m⟧, M)` sees only the
homology of `M` in the `r + 1` degrees `m - r, …, m`. That is
`Stacks.Koszul.Truncation.subsingleton_hom_koszulObject_shift_of_isLE` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineKoszulWindow.lean`, and with
it the argument is the one of the source: for `n ≥ a + r` the truncation triangle
`τ_{≤a-1}M ⟶ M ⟶ τ_{≥a}M ⟶` gives

> `Hom(K⟦-n⟧, M) ≅ Hom(K⟦-n⟧, τ_{≥a}M)` for `M` either `E` or `R (L E)`,

so (1) at `a` carries the vanishing `Hom(K⟦-n⟧, R (L E)) = 0` — which holds for every `n`, since
`L K = 0` — back to `Hom(K⟦-n⟧, E) = 0`.

## On the index of the reverse implication

The index is `a + r`, and **not** the `a + 1` of the published summary of
[Stacks, Tag 0GEJ], which is false as soon as `r ≥ 2`. **This is an approved erratum of the
Stacks Project**: the corrected statement reads `a + r`, and that is what the registration
below states. The Stacks source text is deliberately left as published — the erratum is
recorded against the tag, not in the source. Over `A = k[x, y]`
with `f = (x, y)`, so that `U = Spec A ∖ {origin}` and `K` is the Koszul complex on `x, y` in
degrees `-2, -1, 0`, take `E` the structure sheaf of the origin. Then `E|_U = 0`, so
`Rj_*(E|_U) = 0` and `τ_{≥1}E = 0`, and (1) holds at `a = 1`; while `Hom^•(K, k)` is `k, k², k`
in degrees `0, 1, 2` with zero differentials, so `Hom(K⟦-2⟧, E) = k ≠ 0` and (2) fails at
`a + 1 = 2`. It holds at `a + r = 3`, which is sharp here. The published index of the *forward*
implication, on the other hand, is correct, and is the one proved below.

## Main results

* `Stacks.DerivedTruncation.isIso_homologyMap_truncGEπ` — the comparison `K ⟶ τ_{≥a}K` is a
  homology isomorphism in every degree `i ≥ a`.
* `Stacks.DerivedTruncation.isZero_homology_truncGE_obj` — and `τ_{≥a}K` has no homology below
  `a`.
* `Stacks.DerivedTruncation.isIso_truncGE_map_iff_forall_isIso_homologyMap` — `τ_{≥a}φ` is
  invertible if and only if `H^i(φ)` is invertible for all `i ≥ a`.
* `Stacks.DerivedTruncation.isIso_truncGE_map_of_isZero_homology_obj₃` and
  `Stacks.DerivedTruncation.isZero_homology_obj₃_of_isIso_truncGE_map` — the two one-sided
  implications relating invertibility of `τ_{≥a}(T.mor₁)` to the vanishing of the homology of the
  third vertex of a distinguished triangle.
* `Stacks.DerivedTruncation.subsingleton_hom_of_subsingleton_hom_truncGE` and
  `Stacks.DerivedTruncation.subsingleton_hom_truncGE_of_subsingleton_hom` — the truncation
  triangle transports Hom-vanishing between `M` and `τ_{≥a}M` in both directions.
* `Stacks.DerivedTruncation.isIso_truncGE_map_unit_of_subsingleton_hom_shift` — the implication
  (2) ⟹ (1), abstractly, for an adjunction `L ⊣ R` and an object `K` killed by `L`, taking the
  detection statement for cones of the unit as a hypothesis.
* `Stacks.DerivedTruncation.subsingleton_hom_shift_of_isIso_truncGE_map_unit` — the implication
  (1) ⟹ (2) at `a + r`, abstractly, taking the window on a class `Q` as a hypothesis.
* `Stacks.Koszul.Truncation.truncGE_restriction_of_hom_koszul_eq_zero` and
  `Stacks.Koszul.Truncation.hom_koszul_eq_zero_of_truncGE_restriction` — the two implications of
  [Stacks, Tag 0GEJ] for the sheafified Koszul complex on an affine scheme, each proved
  outright.

## Implementation notes

**The two `@[stacks 0GEJ]` sites each have a clause string, and there is no bare tag.** The two
implications have different conclusions and the reverse one has an index the source gets wrong,
so they are tagged separately and the clause strings say which half each is. Their union is the
whole statement of the tag, in Situation [Stacks, Tag 08CZ] and for `E` with quasi-coherent
cohomology sheaves, exactly as in the source.

**The two geometric inputs.** The implications rest on two statements, proved in
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineComparison.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineKoszulWindow.lean`:

* detection, that an object of `D_QCoh(𝒪_{Spec A})` restricting to zero on `U` and receiving no
  morphism from `K⟦-q⟧` has no homology in degree `q`. This is the source's own
  route — replace `K` by the Koszul complexes on the powers `f_i^e` using the triangles of
  [Stacks, Tag 062C], and read the object through the affine comparison of [Stacks, Tag 06Z0] —
  with the degree bookkeeping made explicit, so that it refines the statement
  `Stacks.Koszul.Truncation.isZero_of_forall_hom_koszulObject_eq_zero` behind
  [Stacks, Tag 09IR] (and is shared with [Stacks, Tag 0GEK]);
* the window, that a morphism `K⟦-m⟧ ⟶ M` vanishes whenever `M` has no homology above `b` and
  `m > b + r`. This is the perfectness of `K`, proved by induction on the length of the
  sequence; the empty sequence gives `𝒪_X`, which corepresents cohomology over the ring.

The window is genuinely needed: for a `K` bounded below only, the reverse implication is false,
by the `Ext¹` example quoted above.

**Quasi-coherence is needed.** The source states both implications for `E ∈ D_QCoh(𝒪_X)`, and so
do the two statements below. Detection and the window are both false for arbitrary objects of
`D(𝒪_X)`. Over `A = k[x]` with `f = (x)`:

* the skyscraper at the origin with value `k(x)`, in degree `0`, restricts to zero on `D(x)`, is
  flasque, and has `x` acting invertibly on its global sections, so it receives no morphism from
  any `K⟦-n⟧` with `n ≥ 0` and yet has nonzero `H⁰` — so detection fails for it;
* for the empty sequence, where `K = 𝒪_X`, the extension by zero `j_!𝒪_{D(x)}` in degree `0` is
  `≤ 0`, and `Hom(𝒪_X⟦-1⟧, −)` is `H¹(X, −) = k[x]_{(x)}/k[x] ≠ 0` although `0 + 0 < 1` — so
  the window fails for it.

Neither sheaf is quasi-coherent. The abstract statements accordingly take the window on an
`ObjectProperty` the consumer chooses, and the detection statement on cones of the unit, where
the consumer has the triangle to deduce whatever it needs.

**Models.** The abstract statements carry free `[HasDerivedCategory.{w} _]` binders. The two
tagged statements are at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, because the affine comparison of
[Stacks, Tag 06Z0] is available there and nowhere else; that is also the only model at which the
compact generation statements these feed into have content.
`CategoryTheory.HasDerivedCategory.standard` is mentioned nowhere.

## References

* [Stacks Project, Tag 0GEJ](https://stacks.math.columbia.edu/tag/0GEJ)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
* [Stacks Project, Tag 0GEK](https://stacks.math.columbia.edu/tag/0GEK)
* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
* [Stacks Project, Tag 062C](https://stacks.math.columbia.edu/tag/062C)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

namespace Stacks.DerivedTruncation

universe w₁ w₂ v₁ v₂ u₁ u₂

/-! ### Reading `τ_{≥a}` off homology -/

section Truncation

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]

/-- **The truncation comparison is a homology isomorphism in high degrees.** For `K` an object of
`D(C)` and `i ≥ a`, the map `H^i(K) ⟶ H^i(τ_{≥a}K)` induced by the canonical morphism
`K ⟶ τ_{≥a}K` is invertible.

The truncation triangle `τ_{≤a-1}K ⟶ K ⟶ τ_{≥a}K ⟶` has first vertex with no homology in degrees
`> a - 1`, so the homology sequence forces the second map to be both mono and epi in degree
`i`. -/
theorem isIso_homologyMap_truncGEπ (K : DerivedCategory C) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLEGE (a - 1) a (by omega)).obj K
  have hT : T ∈ distTriang (DerivedCategory C) :=
    DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) K
  have hle : T.obj₁.IsLE (a - 1) :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncLE (a - 1)).obj K).IsLE (a - 1))
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).2
      ((DerivedCategory.isZero_of_isLE T.obj₁ (a - 1) i (by omega)).eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl).2
      ((DerivedCategory.isZero_of_isLE T.obj₁ (a - 1) (i + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C i).map T.mor₂)

/-- **A truncated morphism is invertible exactly when it is a homology isomorphism in every
degree above the truncation.** This is the bridge that turns the derived-category condition
appearing in [Stacks, Tag 0GEJ] — "the canonical map `τ_{≥a}E ⟶ τ_{≥a}Rj_*(E|_U)` is an
isomorphism" — into a statement about cohomology sheaves, where the Koszul criterion can be
applied. -/
theorem isIso_truncGE_map_iff_forall_isIso_homologyMap {K L : DerivedCategory C} (φ : K ⟶ L)
    (a : ℤ) :
    IsIso ((DerivedCategory.TStructure.t.truncGE a).map φ) ↔
      ∀ i : ℤ, a ≤ i → IsIso ((DerivedCategory.homologyFunctor C i).map φ) := by
  have hsq : ∀ i : ℤ,
      (DerivedCategory.homologyFunctor C i).map φ ≫
          (DerivedCategory.homologyFunctor C i).map
            ((DerivedCategory.TStructure.t.truncGEπ a).app L) =
        (DerivedCategory.homologyFunctor C i).map
            ((DerivedCategory.TStructure.t.truncGEπ a).app K) ≫
          (DerivedCategory.homologyFunctor C i).map
            ((DerivedCategory.TStructure.t.truncGE a).map φ) := by
    intro i
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ a).naturality φ)
  refine ⟨fun h i hi => ?_, fun h => ?_⟩
  · have := isIso_homologyMap_truncGEπ K a i hi
    have := isIso_homologyMap_truncGEπ L a i hi
    have : IsIso ((DerivedCategory.homologyFunctor C i).map φ ≫
        (DerivedCategory.homologyFunctor C i).map
          ((DerivedCategory.TStructure.t.truncGEπ a).app L)) := by
      rw [hsq i]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app L))
  · rw [DerivedCategory.isIso_iff]
    intro i
    by_cases hi : a ≤ i
    · have := isIso_homologyMap_truncGEπ K a i hi
      have := isIso_homologyMap_truncGEπ L a i hi
      have := h i hi
      have : IsIso ((DerivedCategory.homologyFunctor C i).map
            ((DerivedCategory.TStructure.t.truncGEπ a).app K) ≫
          (DerivedCategory.homologyFunctor C i).map
            ((DerivedCategory.TStructure.t.truncGE a).map φ)) := by
        rw [← hsq i]
        infer_instance
      exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor C i).map
        ((DerivedCategory.TStructure.t.truncGEπ a).app K)) _
    · exact (DerivedCategory.isZero_of_isGE _ a i (by omega)).isIso
        (DerivedCategory.isZero_of_isGE _ a i (by omega)) _

/-- **Vanishing homology of the cone from `a - 1` upwards makes the truncated map invertible.**
For a distinguished triangle `T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁[1]`, if `H^i(T.obj₃) = 0` for
every `i ≥ a - 1` then `τ_{≥a}(T.mor₁)` is an isomorphism.

This is the implication "(2) implies (1)" of [Stacks, Tag 0GEJ], stripped of its geometry. -/
theorem isIso_truncGE_map_of_isZero_homology_obj₃ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (a : ℤ)
    (h : ∀ i : ℤ, a - 1 ≤ i → IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃)) :
    IsIso ((DerivedCategory.TStructure.t.truncGE a).map T.mor₁) := by
  rw [isIso_truncGE_map_iff_forall_isIso_homologyMap]
  intro i hi
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2
      ((h i (by omega)).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
      ((h (i - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- **An invertible truncated map kills the homology of the cone from `a` upwards, and no
further.** For a distinguished triangle `T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁[1]` with
`τ_{≥a}(T.mor₁)` an isomorphism, `H^i(T.obj₃) = 0` for every `i ≥ a`.

This is the implication "(1) implies (2) with `a` replaced by `a + 1`" of [Stacks, Tag 0GEJ] at
the level of the cone. The lost degree is real: invertibility of `H^a(T.mor₁)` says nothing about
`H^{a-1}(T.obj₃)`, which is a quotient of `H^{a-1}(T.obj₂)` by the image of `H^{a-1}(T.mor₁)`. -/
theorem isZero_homology_obj₃_of_isIso_truncGE_map (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (a : ℤ)
    (h : IsIso ((DerivedCategory.TStructure.t.truncGE a).map T.mor₁)) (i : ℤ) (hi : a ≤ i) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃) := by
  rw [isIso_truncGE_map_iff_forall_isIso_homologyMap] at h
  have h₂ : (DerivedCategory.homologyFunctor C i).map T.mor₂ = 0 := by
    rw [← DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    have := h i hi
    infer_instance
  have h₃ : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    rw [← DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1) rfl]
    have := h (i + 1) (by omega)
    infer_instance
  exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl).isZero_of_both_zeros h₂ h₃

/-! ### Transporting Hom-vanishing across the truncation triangle -/

/-- Hom-vanishing into the third vertex of a distinguished triangle follows from Hom-vanishing into
the second vertex and into the shifted first vertex. -/
private theorem subsingleton_hom_obj₃_of_subsingleton_hom {T : Triangle (DerivedCategory C)}
    (hT : T ∈ distTriang (DerivedCategory C)) {X : DerivedCategory C}
    (h₂ : Subsingleton (X ⟶ T.obj₂)) (h₁ : Subsingleton (X ⟶ T.obj₁⟦(1 : ℤ)⟧)) :
    Subsingleton (X ⟶ T.obj₃) :=
  subsingleton_of_forall_eq 0 fun u => by
    obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₃ _ hT u (h₁.allEq _ 0)
    rw [hv, h₂.allEq v 0, zero_comp]

/-- **Hom-vanishing descends from `τ_{≥a}M` to `M`.** If no morphism `K⟦-n⟧ ⟶ τ_{≥a}M` and no
morphism `K⟦-n⟧ ⟶ τ_{≤a-1}M` is nonzero, then no morphism `K⟦-n⟧ ⟶ M` is.

A morphism `K⟦-n⟧ ⟶ M` composes to zero into `τ_{≥a}M`, hence factors through `τ_{≤a-1}M`, which
receives nothing. -/
theorem subsingleton_hom_of_subsingleton_hom_truncGE {K M : DerivedCategory C} (a n : ℤ)
    (hlow : Subsingleton (K⟦-n⟧ ⟶ (DerivedCategory.TStructure.t.truncLE (a - 1)).obj M))
    (h : Subsingleton (K⟦-n⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj M)) :
    Subsingleton (K⟦-n⟧ ⟶ M) := by
  have hT : (DerivedCategory.TStructure.t.triangleLEGE (a - 1) a (by omega)).obj M ∈
      distTriang (DerivedCategory C) :=
    DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) M
  refine subsingleton_of_forall_eq 0 fun u => ?_
  obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _ hT u (h.allEq _ 0)
  rw [hv, hlow.allEq v 0]
  exact zero_comp

/-- **Hom-vanishing ascends from `M` to `τ_{≥a}M`.** If no morphism `K⟦-n⟧ ⟶ M` and no morphism
`K⟦-n⟧ ⟶ (τ_{≤a-1}M)[1]` is nonzero, then no morphism `K⟦-n⟧ ⟶ τ_{≥a}M` is.

A morphism `K⟦-n⟧ ⟶ τ_{≥a}M` composes to zero into `(τ_{≤a-1}M)[1]`, hence factors through `M`,
which receives nothing. -/
theorem subsingleton_hom_truncGE_of_subsingleton_hom {K M : DerivedCategory C} (a n : ℤ)
    (hlow : Subsingleton
      (K⟦-n⟧ ⟶ ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj M)⟦(1 : ℤ)⟧))
    (h : Subsingleton (K⟦-n⟧ ⟶ M)) :
    Subsingleton (K⟦-n⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj M) := by
  exact subsingleton_hom_obj₃_of_subsingleton_hom
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) M) h hlow

end Truncation

/-! ### The two implications of [Stacks, Tag 0GEJ], abstractly -/

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {L : DerivedCategory C ⥤ DerivedCategory D} {R : DerivedCategory D ⥤ DerivedCategory C}
  (adj : L ⊣ R) [L.CommShift ℤ]

/-- **An invertible truncated unit kills the maps from the high shifts of an object killed by the
left adjoint, `r` degrees up.** This is the implication "(1) implies (2) with `a` replaced by
`a + r`" of [Stacks, Tag 0GEJ], with the perfectness of `K` isolated as `hKwindow`:

> a morphism `K⟦-m⟧ ⟶ M` vanishes whenever `M` lies in the class `Q`, has no homology above
> `b`, and `m > b + r`.

For `n ≥ a + r` the truncation triangle makes `Hom(K⟦-n⟧, −)` insensitive to replacing an object
by its `τ_{≥a}`: on `R (L E)` through
`Stacks.DerivedTruncation.subsingleton_hom_truncGE_of_subsingleton_hom`, where the vanishing
`Hom(K⟦-n⟧, R (L E)) = 0` comes from `L K = 0` and the adjunction, and on `E` through
`Stacks.DerivedTruncation.subsingleton_hom_of_subsingleton_hom_truncGE`. Invertibility of
`τ_{≥a}` of the unit identifies the two middle terms.

**The window is asked for on the class `Q` only, not on every object.** It is used twice, on
`τ_{≤a-1}E` and on `τ_{≤a-1}(R (L E))`, so `Q` need only contain `E` and `R (L E)` and be closed
under `τ_{≤}`. Quantifying it over all of `D(C)` would make the statement vacuous in the case it
is meant for: for the Koszul complex on an affine scheme the window fails without
quasi-coherence, and
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineKoszulWindow.lean` gives the
counterexample.

No triangulatedness of `L` and no full faithfulness of `R` is used, and the cone of the unit does
not appear: unlike in the `τ_{≤a}` case, the lost degree of the truncation sandwich is not what
this implication spends. -/
theorem subsingleton_hom_shift_of_isIso_truncGE_map_unit {K E : DerivedCategory C}
    (hK : IsZero (L.obj K)) (r : ℕ) (Q : ObjectProperty (DerivedCategory C)) (hQE : Q E)
    (hQR : Q (R.obj (L.obj E)))
    (hQtruncLE : ∀ (M : DerivedCategory C) (b : ℤ), Q M →
      Q ((DerivedCategory.TStructure.t.truncLE b).obj M))
    (hKwindow : ∀ (M : DerivedCategory C) (b m : ℤ), Q M → M.IsLE b → b + (r : ℤ) < m →
      Subsingleton (K⟦-m⟧ ⟶ M))
    (a : ℤ) (h : IsIso ((DerivedCategory.TStructure.t.truncGE a).map (adj.unit.app E)))
    (n : ℤ) (hn : a + (r : ℤ) ≤ n) : Subsingleton (K⟦-n⟧ ⟶ E) := by
  have hsubR : Subsingleton (K⟦-n⟧ ⟶ R.obj (L.obj E)) :=
    subsingleton_hom_rightAdjoint_obj_of_isZero adj
      (isZero_map_shift_of_isZero_map hK (-n)) (L.obj E)
  have hR : Subsingleton
      (K⟦-n⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj (R.obj (L.obj E))) := by
    refine subsingleton_hom_truncGE_of_subsingleton_hom a n ?_ hsubR
    exact subsingleton_hom_shift_one_of_subsingleton_hom (-n) (-(n + 1)) (by omega)
      (hKwindow _ (a - 1) (n + 1) (hQtruncLE _ _ hQR) inferInstance (by omega))
  have hGE : Subsingleton (K⟦-n⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj E) :=
    ⟨fun u v => (cancel_mono
      ((DerivedCategory.TStructure.t.truncGE a).map (adj.unit.app E))).mp (hR.allEq _ _)⟩
  exact subsingleton_hom_of_subsingleton_hom_truncGE a n
    (hKwindow _ (a - 1) n (hQtruncLE _ _ hQE) inferInstance (by omega)) hGE

variable [L.IsTriangulated]

/-- **Vanishing of the maps from the high shifts of `K` makes the truncated unit invertible.**
This is the implication "(2) implies (1)" of [Stacks, Tag 0GEJ], at the index the source has, with
its commutative algebra isolated as `hdet`.

The cone `N` of the unit is killed by `L`, because `L` of the unit is invertible wherever the
counit is; and it receives no morphism from `K⟦-n⟧` for `n ≥ a - 1`, because such a morphism
composes to zero into `E⟦1⟧` — this is where the hypothesis at `a` is spent, one degree below —
hence factors through `R (L E)`, which receives none. So `hdet` applies to `N` and the homology of
the cone vanishes in degrees `≥ a - 1`, which is what makes the truncated map invertible.

**`hdet` is asked for on cones of the unit at `E` only.** It carries the distinguished triangle
`E ⟶ R (L E) ⟶ N ⟶ E⟦1⟧` as a hypothesis, so a consumer may use it to establish whatever
further property of `N` the detection statement it has needs — quasi-coherence, in the geometric
case. Asked for on every object of `D(C)` the hypothesis would be unsatisfiable there, and the
statement vacuous; see
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineComparison.lean`. -/
theorem isIso_truncGE_map_unit_of_subsingleton_hom_shift {K E : DerivedCategory C}
    (hK : IsZero (L.obj K)) (hcounit : IsIso (adj.counit.app (L.obj E))) (a : ℤ)
    (hdet : ∀ (M : DerivedCategory C) (g : R.obj (L.obj E) ⟶ M) (p : M ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk (adj.unit.app E) g p ∈ distTriang (DerivedCategory C) →
      IsZero (L.obj M) →
      (∀ n : ℤ, a - 1 ≤ n → Subsingleton (K⟦-n⟧ ⟶ M)) →
      ∀ i : ℤ, a - 1 ≤ i → IsZero ((DerivedCategory.homologyFunctor C i).obj M))
    (h : ∀ n : ℤ, a ≤ n → Subsingleton (K⟦-n⟧ ⟶ E)) :
    IsIso ((DerivedCategory.TStructure.t.truncGE a).map (adj.unit.app E)) := by
  obtain ⟨N, g, i, hT⟩ := distinguished_cocone_triangle (adj.unit.app E)
  have hLN : IsZero (L.obj N) :=
    Triangle.isZero₃_of_isIso₁ _ (L.map_distinguished _ hT)
      (isIso_map_unit_of_isIso_counit adj E hcounit)
  have hortho : ∀ n : ℤ, a - 1 ≤ n → Subsingleton (K⟦-n⟧ ⟶ N) := by
    intro n hn
    have hsub : Subsingleton (K⟦-n⟧ ⟶ R.obj (L.obj E)) :=
      subsingleton_hom_rightAdjoint_obj_of_isZero adj
        (isZero_map_shift_of_isZero_map hK (-n)) (L.obj E)
    have hshift : Subsingleton (K⟦-n⟧ ⟶ E⟦(1 : ℤ)⟧) :=
      subsingleton_hom_shift_one_of_subsingleton_hom (-n) (-(n + 1)) (by omega)
        (h (n + 1) (by omega))
    exact subsingleton_hom_obj₃_of_subsingleton_hom (T := Triangle.mk (adj.unit.app E) g i) hT
      hsub hshift
  exact isIso_truncGE_map_of_isZero_homology_obj₃ _ hT a (hdet N g i hT hLN hortho)

end Adjunction

end Stacks.DerivedTruncation

/-! ### [Stacks, Tag 0GEJ] for the Koszul complex on an affine scheme -/

namespace Stacks.Koszul.Truncation

open Stacks.Duality.OpenImmersion

universe u

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)

/-- **[Stacks, Tag 0GEJ], the implication "Koszul orthogonality implies truncated
restriction".** Let `f₁, …, f_r ∈ A`, let `U = ⋃ᵢ D(f_i) ⊆ Spec A`, let `j : U ⟶ Spec A` be the
inclusion and let `K` be the sheafified Koszul complex of the sequence. Let `E` be an object of
`D_QCoh(𝒪_{Spec A})`. If every morphism `K⟦-n⟧ ⟶ E` vanishes for `n ≥ a`, then the canonical map
`E ⟶ Rj_*(E|_U)` becomes invertible after truncation in degrees `≥ a`.

This is condition (2) of the source implying condition (1), at the source's own index: the
premise is at `a` and the conclusion at `a`.

The cone `N` of the unit restricts to zero on `U`, receives no morphism from `K⟦-n⟧` for
`n ≥ a - 1`, and has quasi-coherent cohomology sheaves — the last because `E` does and `Rj_*`
preserves quasi-coherent cohomology along a quasi-compact open immersion ([Stacks, Tag 08D5]).
The graded detection statement
`Stacks.Koszul.Truncation.isZero_homology_of_forall_hom_koszulObject_eq_zero` then kills the
homology of `N` in degrees `≥ a - 1`, which is what makes the truncated map invertible. That is
where the commutative algebra of the source sits: the Koszul power triangles of
[Stacks, Tag 062C], the lifting lemma of [Stacks, Tag 08E3] and the affine comparison
`D(A) ≌ D_QCoh(𝒪_{Spec A})` of [Stacks, Tag 06Z0]. The two other inputs of the source are
proved too: the Koszul object restricts to zero on `U` by
`Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject`, and `Rj_*` is fully faithful
by the instance
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit_app`. -/
@[stacks 0GEJ "(2) implies (1)"]
theorem truncGE_restriction_of_hom_koszul_eq_zero
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules) (hE : qcohSpec A E) (a : ℤ)
    (h : ∀ n : ℤ, a ≤ n → Subsingleton ((koszulObject f)⟦-n⟧ ⟶ E)) :
    IsIso ((DerivedCategory.TStructure.t.truncGE a).map
      ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E)) := by
  refine Stacks.DerivedTruncation.isIso_truncGE_map_unit_of_subsingleton_hom_shift
    (derivedRestrictPushforwardAdjunction (openComplement f).ι)
    (Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f) inferInstance a
    (fun N g p hT hLN hortho => ?_) h
  have hQN := AlgebraicGeometry.derivedCategoryB_obj₃_of_distTriang _ hT hE
    (derivedCategoryB_derivedPushforward_openComplement f _
      (Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict (openComplement f).ι E hE))
  exact fun i hi =>
    isZero_homology_of_forall_hom_koszulObject_eq_zero f N hQN hLN i
      fun g' => (hortho i hi).allEq g' 0

/-- **[Stacks, Tag 0GEJ], the implication "truncated restriction implies Koszul orthogonality
`r` degrees up".** In the situation above, if the canonical map `E ⟶ Rj_*(E|_U)` is invertible
after truncation in degrees `≥ a`, then every morphism `K⟦-n⟧ ⟶ E` vanishes for `n ≥ a + r`.

The argument spends the window
`Stacks.Koszul.Truncation.subsingleton_hom_koszulObject_shift_of_isLE`, which is the perfectness
of `K`: `K` is a bounded complex of finite free modules in degrees `-r, …, 0`, so `Hom(K⟦-m⟧, M)`
sees only the homology of `M` in the `r + 1` degrees `m - r, …, m`. It is applied to
`τ_{≤a-1}E` and to `τ_{≤a-1}(Rj_*(E|_U))`, both of which have quasi-coherent cohomology
sheaves — and quasi-coherence is not a convenience here, the window being false without it.

**The index is `a + r`, and the `a + 1` of the published statement of the tag is false for
`r ≥ 2`.** This is an approved erratum of the Stacks Project, recorded against the tag; the
Stacks source text is left as published. The module documentation gives the counterexample
over `k[x, y]`, where `a + r` is sharp. -/
@[stacks 0GEJ "(1) implies (2) with a replaced by a + r, not the published a + 1, which is false
for r ≥ 2 — see the module docstring for the counterexample over k[x,y]"]
theorem hom_koszul_eq_zero_of_truncGE_restriction
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules) (hE : qcohSpec A E) (a : ℤ)
    (h : IsIso ((DerivedCategory.TStructure.t.truncGE a).map
      ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E))) :
    ∀ n : ℤ, a + (r : ℤ) ≤ n → Subsingleton ((koszulObject f)⟦-n⟧ ⟶ E) := by
  have hQR := derivedCategoryB_derivedPushforward_openComplement f _
    (Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict (openComplement f).ι E hE)
  exact fun n hn => Stacks.DerivedTruncation.subsingleton_hom_shift_of_isIso_truncGE_map_unit
    (derivedRestrictPushforwardAdjunction (openComplement f).ι)
    (Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f) r (qcohSpec A) hE hQR
    (fun M b hQM i => Stacks.Duality.isQuasicoherent_homology_truncLE M hQM b i)
    (fun M b m hQM hle hlt =>
      subsingleton_hom_koszulObject_shift_of_isLE f M hQM b (-m) hle (by omega))
    a h n hn

end Stacks.Koszul.Truncation

end
