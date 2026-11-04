module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementComparison
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementComposition
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementXi
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.DenseInterior
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Independence of the upper shriek functor from the compactification

In the situation of [Stacks, Tag 0F42] — a Noetherian base `S` and the category
`AlgebraicGeometry.FTS S` of schemes separated and of finite type over `S` — let `f : X ⟶ Y` be a
morphism.  [Stacks, Tag 0A9Y] attaches to every compactification `j` of `X` over `Y` the functor

  `f^!_j = j^* ∘ ā : D⁺_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`,

which is `Stacks.Duality.compactificationUpperShriek`, and [Stacks, Tag 0AA0] is the statement
that this functor is, up to canonical isomorphism, independent of `j`.  The source reads `f^!`
on `D⁺_QCoh(𝒪_Y)`, and so does this file; see *The bounded-below domain* below.

The comparison is the source's.  Two compactifications `j` and `k` have a common refinement `r`
with dense interior, by [Stacks, Tag 0ATU] parts (a) and (b); every morphism out of a
compactification with dense interior preserves the interior, by part (c); and an
interior-preserving morphism `g : r ⟶ j` carries the comparison
`Stacks.Duality.refinementIso` — the `α_g` of the source.  The comparison of `j` and `k` is
`α_{g₁}⁻¹ ≫ α_{g₂}` for the two projections of the common refinement.

That it does not depend on the common refinement used is, in this repository, a consequence of
[Stacks, Tag 0ATU] in a sharper form than the source's: there is **at most one** morphism out of a
compactification with dense interior
(`AlgebraicGeometry.CategoryOfCompactifications.hom_ext_of_hasDenseInterior`), so no choice is
being made among the morphisms, only among the refinements.

## Main definitions

All in the namespace `Stacks.Duality`.

* `compactificationSituation` — the standing data of [Stacks, Tag 0ATU] for the compactifications
  of `f`.
* `compactificationUpperShriekIso` — **the canonical comparison `f^!_j ≅ f^!_k`**.

## Main results

* `exists_denseRefinement`, `hom_ext_of_dense`, `preservesInterior_of_dense` — the three
  consequences of [Stacks, Tag 0ATU] that the construction uses.
* `refinementIso_congr` — the comparison `α_g` depends on `g` alone.
* `compactificationUpperShriekIso_refl` — the comparison of a compactification with itself is
  the identity.
* `compactificationUpperShriekIso_eq`, `compactificationUpperShriekIso_eq_iso` — the comparison
  is `α_a⁻¹ ≫ α_b` for any compactification with dense interior mapping to both, and it **agrees
  with the source's `α_g`** whenever the two compactifications are joined by an
  interior-preserving morphism `g`.
* `compactificationUpperShriekIso_trans` — the comparisons of three compactifications are
  compatible.
* `exists_coherent_compactificationUpperShriekIso` — a family of comparisons that is the identity
  on the diagonal, transitive, and equal to `α_g` on an interior-preserving morphism.

## Implementation notes

*The bounded-below domain.*  `Stacks.Duality.compactificationUpperShriek` is read on
`D⁺_QCoh(𝒪_Y)`, exactly as [Stacks, Tag 0AA0] reads `f^!`. This is also what the source's proof
uses: the comparison `α_g` of an interior-preserving `g : j ⟶ k` needs the base change map of
[Stacks, Tag 0AA6] for the square of `g` to be invertible, and [Stacks, Tag 0A9P] gives that
through [Stacks, Tag 0A9N] part **(1)**, on `D⁺_QCoh(𝒪_{X̄₂})`. The functor `ā_k` carries
`D⁺_QCoh(𝒪_Y)` there by [Stacks, Tag 0A9I].

The *codomain* is left as `D_QCoh(𝒪_X)` rather than `D⁺_QCoh(𝒪_X)`. Since the inclusion of
`D⁺_QCoh(𝒪_X)` is fully faithful, an isomorphism of the functors into `D_QCoh(𝒪_X)` is the same
datum as an isomorphism of the functors into `D⁺_QCoh(𝒪_X)`, so no content is lost.

*Nothing is assumed.* The two inputs of the comparison `α_g` are instances:
[Stacks, Tag 0A9K] for the square of `g` is `Stacks.Duality.isIso_refinementXi`, and
[Stacks, Tag 0A9P] (2) for it — `G : X̄₁ ⟶ X̄₂` is proper and `X̄₂` is Noetherian — is
`Stacks.Duality.isIso_refinementBaseChangePlus`, which is
`Stacks.Duality.isIso_twistedInverseImageRestrictionMap_app_of_isProper` read through the base
change map of [Stacks, Tag 0AA6]
(`Stacks.Duality.isIso_twistedInverseImageBaseChangeMap_app_iff`) and composed with
[Stacks, Tag 0A9I] (`Stacks.Duality.isBoundedBelow_twistedInverseImage_obj`). Everything that
[Stacks, Tag 08D5], [Stacks, Tag 08DW] and [Stacks, Tag 0A9E] contribute is discharged over a
Noetherian base, and so is the whole of [Stacks, Tag 0ATU]. The compactifications themselves are
arguments, which is [Stacks, Tag 0F41].

*The agreement with the source's comparison.*  The canonical comparison is *constructed* from the
`α` of a dense common refinement, and it agrees with `α_g` for every interior-preserving
`g : j ⟶ k`, by `compactificationUpperShriekIso_eq_iso`. What that needs is the cocycle identity
`α_{g ≫ h} = α_g ≫ α_h`, which is `Stacks.Duality.refinementIso_comp` in
`StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementComposition`,
together with the uniqueness of a morphism out of a compactification with dense interior: the
second projection of the common refinement of `j` and `k` is the first projection followed by
`g`.

## References

* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
* [Stacks Project, Tag 0A9N](https://stacks.math.columbia.edu/tag/0A9N)
* [Stacks Project, Tag 0A9R](https://stacks.math.columbia.edu/tag/0A9R)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 0A9C](https://stacks.math.columbia.edu/tag/0A9C)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.CategoryOfCompactifications

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)

/-! ### The consequences of Tag 0ATU that the comparison uses -/

/-- The standing data of [Stacks, Tag 0ATU] for the compactifications of `f`, witnessed by a
given compactification.  Over a Noetherian base the open immersion of any compactification is
quasi-compact, so one compactification supplies the whole structure. -/
abbrev compactificationSituation (j₀ : CompactificationOf (Over.mk f.left)) :
    CategoryOfCompactifications.{u} where
  S := Y.left
  X := Over.mk f.left
  isQuasiCompact := inferInstance
  isQuasiSeparated := inferInstance
  exists_quasiCompact_compactification := ⟨j₀, inferInstance⟩

/-- **[Stacks, Tag 0ATU] parts (a) and (b): two compactifications have a common refinement with
dense interior.**  The common refinement is the scheme-theoretic closure of the interior inside
the fibre product of the two ambient schemes. -/
@[sga "4 XVII 3.2.6" "(ii)"]
theorem exists_denseRefinement (j k : CompactificationOf (Over.mk f.left)) :
    ∃ (r : CompactificationOf (Over.mk f.left)) (_ : r ⟶ j) (_ : r ⟶ k),
      HasDenseInterior (Over.mk f.left) r :=
  ⟨commonRefinement (compactificationSituation f j) j k,
    commonRefinementFst (compactificationSituation f j) j k,
    commonRefinementSnd (compactificationSituation f j) j k,
    hasDenseInterior_commonRefinement (compactificationSituation f j) j k⟩

/-- **There is at most one morphism out of a compactification with dense interior.**  This is
what makes the comparison below independent of the morphisms used, and it is a consequence of
[Stacks, Tag 0ATU]. -/
theorem hom_ext_of_dense {r j : CompactificationOf (Over.mk f.left)}
    (hr : HasDenseInterior (Over.mk f.left) r) (a b : r ⟶ j) : a = b :=
  hom_ext_of_hasDenseInterior (compactificationSituation f r) hr a b

/-- **[Stacks, Tag 0ATU] part (c): a morphism out of a compactification with dense interior
preserves the interior.** -/
theorem preservesInterior_of_dense {r j : CompactificationOf (Over.mk f.left)}
    (hr : HasDenseInterior (Over.mk f.left) r) (g : r ⟶ j) :
    CompactificationOf.PreservesInterior g :=
  CompactificationOf.preservesInterior_of_denseRange g hr.1.denseRange

/-! ### The comparison `α_g` depends on `g` alone -/

/-- The comparison `α_g` of [Stacks, Tag 0AA0] depends on `g` alone: the interior-preserving
hypothesis is a `Prop`, and both instance arguments of `Stacks.Duality.refinementIso` — the
inputs of [Stacks, Tag 0A9K] and [Stacks, Tag 0A9P] — are instances
(`Stacks.Duality.isIso_refinementXi` and `Stacks.Duality.isIso_refinementBaseChangePlus`). -/
theorem refinementIso_congr {j k : CompactificationOf (Over.mk f.left)} {g₁ g₂ : j ⟶ k}
    (e : g₁ = g₂) (h₁ : CompactificationOf.PreservesInterior g₁)
    (h₂ : CompactificationOf.PreservesInterior g₂) :
    refinementIso f g₁ h₁ = refinementIso f g₂ h₂ := by
  subst e; rfl

/-! ### The canonical comparison -/

/-- **[Stacks, Tag 0AA0]: the canonical comparison of the upper shriek functors of two
compactifications.**  It is `α_{g₁}⁻¹ ≫ α_{g₂}` for the two projections of the common refinement
with dense interior of [Stacks, Tag 0ATU], as an isomorphism of functors out of
`D⁺_QCoh(𝒪_Y)`. -/
@[stacks 0AA0 "the canonical isomorphism f^!_j = f^!_k between the upper shriek functors \
  (Stacks.Duality.compactificationUpperShriek, which is Stacks.Duality.upperShriek of Stacks \
  0A9Y, read on D^+_QCoh(O_Y) as in the source) of any two compactifications j, k of a morphism \
  f : X -> Y of FTS S over a Noetherian S: the source's alpha_{g_1}^{-1} then alpha_{g_2} for the \
  two projections of the common refinement with dense interior of Stacks 0ATU. Nothing is \
  carried: alpha_g needs Stacks 0A9K for the square of g, which is \
  Stacks.Duality.isIso_refinementXi, and Stacks 0A9P (2) for it (G proper, Xbar_2 Noetherian), \
  which is Stacks.Duality.isIso_refinementBaseChangePlus, both instances. Its value on the \
  diagonal is the identity (Stacks.Duality.compactificationUpperShriekIso_refl), it is \
  transitive (Stacks.Duality.compactificationUpperShriekIso_trans) and it is the source's \
  alpha_g for an interior-preserving g (Stacks.Duality.compactificationUpperShriekIso_eq_iso); \
  Stacks.Duality.exists_coherent_compactificationUpperShriekIso collects these. The \
  compactifications are arguments; that one exists is Stacks 0F41"]
def compactificationUpperShriekIso (j k : CompactificationOf (Over.mk f.left)) :
    compactificationUpperShriek f j ≅ compactificationUpperShriek f k :=
  (refinementIso f (commonRefinementFst (compactificationSituation f j) j k)
      (preservesInterior_of_dense f
        (hasDenseInterior_commonRefinement (compactificationSituation f j) j k) _)).symm ≪≫
    refinementIso f (commonRefinementSnd (compactificationSituation f j) j k)
      (preservesInterior_of_dense f
        (hasDenseInterior_commonRefinement (compactificationSituation f j) j k) _)

/-- **The canonical comparison of a compactification with itself is the identity.**  The two
projections of the common refinement of `j` with itself are morphisms out of a compactification
with dense interior, hence equal. -/
theorem compactificationUpperShriekIso_refl (j : CompactificationOf (Over.mk f.left)) :
    compactificationUpperShriekIso f j j = Iso.refl _ := by
  rw [compactificationUpperShriekIso, refinementIso_congr f
    (hom_ext_of_dense f (hasDenseInterior_commonRefinement (compactificationSituation f j) j j)
      (commonRefinementFst (compactificationSituation f j) j j)
      (commonRefinementSnd (compactificationSituation f j) j j)) _
    (preservesInterior_of_dense f
      (hasDenseInterior_commonRefinement (compactificationSituation f j) j j) _)]
  exact Iso.symm_self_id _

/-- **The canonical comparison is `α_a⁻¹ ≫ α_b` for *any* compactification with dense interior
mapping to both.**  The definition uses the common refinement of [Stacks, Tag 0ATU]; a second
dense refinement is compared with it by a third, out of which there is at most one morphism into
each of the two, and the cocycle identity `Stacks.Duality.refinementIso_comp` makes the
two answers agree. -/
theorem compactificationUpperShriekIso_eq {j k r : CompactificationOf (Over.mk f.left)}
    (hr : HasDenseInterior (Over.mk f.left) r)
    (a : r ⟶ j) (b : r ⟶ k) :
    compactificationUpperShriekIso f j k =
      (refinementIso f a (preservesInterior_of_dense f hr a)).symm ≪≫
        refinementIso f b (preservesInterior_of_dense f hr b) := by
  have hr₀ := hasDenseInterior_commonRefinement (compactificationSituation f j) j k
  have hr₁ := hasDenseInterior_commonRefinement (compactificationSituation f r) r
    (commonRefinement (compactificationSituation f j) j k)
  set p₁ := commonRefinementFst (compactificationSituation f j) j k with hp₁
  set p₂ := commonRefinementSnd (compactificationSituation f j) j k with hp₂
  set c₁ := commonRefinementFst (compactificationSituation f r) r
    (commonRefinement (compactificationSituation f j) j k) with hc₁
  set c₂ := commonRefinementSnd (compactificationSituation f r) r
    (commonRefinement (compactificationSituation f j) j k) with hc₂
  have key : ∀ {t : CompactificationOf (Over.mk f.left)} (p : _ ⟶ t) (q : r ⟶ t),
      refinementIso f p (preservesInterior_of_dense f hr₀ p) =
        (refinementIso f c₂ (preservesInterior_of_dense f hr₁ c₂)).symm ≪≫
          refinementIso f c₁ (preservesInterior_of_dense f hr₁ c₁) ≪≫
            refinementIso f q (preservesInterior_of_dense f hr q) := by
    intro t p q
    have e : refinementIso f c₂ (preservesInterior_of_dense f hr₁ c₂) ≪≫
          refinementIso f p (preservesInterior_of_dense f hr₀ p) =
        refinementIso f c₁ (preservesInterior_of_dense f hr₁ c₁) ≪≫
          refinementIso f q (preservesInterior_of_dense f hr q) := by
      rw [← refinementIso_comp f c₂ p _ _ (preservesInterior_of_dense f hr₁ (c₂ ≫ p)),
        ← refinementIso_comp f c₁ q _ _ (preservesInterior_of_dense f hr₁ (c₁ ≫ q)),
        refinementIso_congr f (hom_ext_of_dense f hr₁ (c₂ ≫ p) (c₁ ≫ q)) _
          (preservesInterior_of_dense f hr₁ (c₁ ≫ q))]
    rw [← e]; simp
  rw [compactificationUpperShriekIso, key p₁ a, key p₂ b]
  simp

/-- **[Stacks, Tag 0AA0]: the canonical comparison agrees with the source's `α_g` for an
interior-preserving morphism `g : j ⟶ k` of compactifications.**  Take the dense common refinement
`r` and its projection `p` to `j`: the second projection and `p ≫ g` are two morphisms out of a
compactification with dense interior, hence equal, so the canonical comparison is
`α_p⁻¹ ≫ α_{p ≫ g}`, which the cocycle identity turns into `α_g`. -/
theorem compactificationUpperShriekIso_eq_iso {j k : CompactificationOf (Over.mk f.left)}
    (g : j ⟶ k)
    (hg : CompactificationOf.PreservesInterior g) :
    compactificationUpperShriekIso f j k = refinementIso f g hg := by
  have hr := hasDenseInterior_commonRefinement (compactificationSituation f j) j k
  rw [compactificationUpperShriekIso_eq f hr
    (commonRefinementFst (compactificationSituation f j) j k)
    (commonRefinementFst (compactificationSituation f j) j k ≫ g),
    refinementIso_comp f _ g (preservesInterior_of_dense f hr
      (commonRefinementFst (compactificationSituation f j) j k)) hg]
  simp

/-- **The canonical comparisons of three compactifications are compatible.**  A dense refinement
of all three is obtained by refining the common refinement of the first two together with the
third, and `Stacks.Duality.compactificationUpperShriekIso_eq` reads all three comparisons off
it. -/
theorem compactificationUpperShriekIso_trans (j k l : CompactificationOf (Over.mk f.left)) :
    compactificationUpperShriekIso f j k ≪≫ compactificationUpperShriekIso f k l =
      compactificationUpperShriekIso f j l := by
  have hr := hasDenseInterior_commonRefinement (compactificationSituation f
    (commonRefinement (compactificationSituation f j) j k))
    (commonRefinement (compactificationSituation f j) j k) l
  set q := commonRefinementFst (compactificationSituation f
    (commonRefinement (compactificationSituation f j) j k))
    (commonRefinement (compactificationSituation f j) j k) l with hq
  set ql := commonRefinementSnd (compactificationSituation f
    (commonRefinement (compactificationSituation f j) j k))
    (commonRefinement (compactificationSituation f j) j k) l with hql
  rw [compactificationUpperShriekIso_eq f hr
      (q ≫ commonRefinementFst (compactificationSituation f j) j k)
      (q ≫ commonRefinementSnd (compactificationSituation f j) j k),
    compactificationUpperShriekIso_eq f hr
      (q ≫ commonRefinementSnd (compactificationSituation f j) j k) ql,
    compactificationUpperShriekIso_eq f hr
      (q ≫ commonRefinementFst (compactificationSituation f j) j k) ql]
  simp

/-! ### A coherent family of comparisons -/

/-- **[Stacks, Tag 0AA0]: the upper shriek functor is independent of the compactification, by a
coherent family of isomorphisms.**  There is a family of isomorphisms `e j k : f^!_j ≅ f^!_k`
of functors out of `D⁺_QCoh(𝒪_Y)`,
indexed by pairs of compactifications of `X` over `Y`, which is the identity on the diagonal,
composes transitively, and **agrees with the source's comparison `α_g` whenever `j` and `k` are
joined by an interior-preserving morphism `g`**.  So the isomorphism class of `f^!` does not
depend on the compactification, the identifications of three compactifications are compatible,
and the family is the source's.

The family is `Stacks.Duality.compactificationUpperShriekIso` itself; reflexivity is
`Stacks.Duality.compactificationUpperShriekIso_refl`, transitivity is
`Stacks.Duality.compactificationUpperShriekIso_trans`, and the agreement with `α_g` is
`Stacks.Duality.compactificationUpperShriekIso_eq_iso`. -/
@[stacks 0AA0 "the upper shriek functor of a compactification \
  (Stacks.Duality.compactificationUpperShriek, which is Stacks.Duality.upperShriek of Stacks \
  0A9Y) on D^+_QCoh(O_Y), the source's own domain for it, is independent of the compactification \
  up to canonical isomorphism: a family of isomorphisms between the functors of any two \
  compactifications that is the identity on the diagonal, transitive, and equal to the source's \
  alpha_g (Stacks.Duality.refinementIso) whenever the two compactifications are joined by an \
  interior-preserving morphism g. Nothing is carried; the family is \
  Stacks.Duality.compactificationUpperShriekIso"]
theorem exists_coherent_compactificationUpperShriekIso :
    ∃ e : ∀ j k : CompactificationOf (Over.mk f.left),
        compactificationUpperShriek f j ≅ compactificationUpperShriek f k,
      (∀ j, e j j = Iso.refl _) ∧ (∀ j k l, e j k ≪≫ e k l = e j l) ∧
        ∀ (j k : CompactificationOf (Over.mk f.left)) (g : j ⟶ k)
          (hg : CompactificationOf.PreservesInterior g), e j k = refinementIso f g hg :=
  ⟨compactificationUpperShriekIso f, compactificationUpperShriekIso_refl f,
    compactificationUpperShriekIso_trans f,
    fun _ _ g hg => compactificationUpperShriekIso_eq_iso f g hg⟩

end Stacks.Duality

end
