module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdgeIso
public import StacksFrontier.Algebra.Homology.RightDerivedCoEdgeReflective
public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImages
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# The comparison of higher direct images under a change of topology

In the situation of Stacks 0EZ3 write `ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology
morphism from the finer site to the coarser one, and let `(V_n)` be the condition
`Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition`: the higher direct images
`R^i ε_{X,*} ℱ` vanish for `1 ≤ i ≤ n`, for every object `X` and every `ℱ` in the class `𝒜_X`.

Stacks 0EZF asserts `(V_n)` for every `n`, and obtains it by the induction `(V_n) ⇒ (V_{n+1})`
of Stacks 0EZE from the observation that `(V_0)` is the empty condition. This file proves
everything that follows from `(V_n)` by pure homological algebra, with no descent argument and
no spectral sequence:

* `(V_0)` holds, because no degree satisfies `1 ≤ i ≤ 0`, and `(V_n)` implies `(V_m)` for
  `m ≤ n`;
* **Stacks 0EZA**: under `(V_n)`, for `f : X ⟶ Y` in the distinguished class, `ℱ` in `𝒜_X` and
  `i ≤ n`, the comparison `R^i f_{τ',*} ε_{X,*} ℱ ⟶ ε_{Y,*} R^i f_{τ,*} ℱ` of
  `Stacks.ComparingTopologies.higherDirectImageComparison` is an isomorphism;
* the case of **Stacks 0EZB** in which the bounded below object is a single sheaf: under
  `(V_n)`, for `ℱ` in `𝒜_X` and `m ≤ n`, the change-of-topology map
  `H^m_{τ'}(X, ε_{X,*} ℱ) ⟶ H^m_τ(X, ℱ)` is an isomorphism.

## The mechanism

All three nontrivial statements are degeneration statements for one of the two edge morphisms of
a Grothendieck spectral sequence, and both edge morphisms are available in this development
without any spectral sequence, as `Stacks.Cohomology.RightDerivedEdge.edge` and
`Stacks.Cohomology.RightDerivedCoEdge.secondEdge`.

The *first* edge morphism `R^i Q (P ℱ) ⟶ R^i (Q ∘ P) ℱ` is invertible as soon as `R^q P ℱ`
vanishes for `1 ≤ q ≤ i` (`Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app`), which is
exactly what `(V_n)` supplies for `P = ε_{X,*}`. Taking `Q = f_{τ',*}` gives the first factor of
the comparison of Stacks 0EZA; taking `Q = Γ_{τ'}(X, -)`, whose composite with `ε_{X,*}` is
`Γ_τ(X, -)` on the nose, gives the whole of the single-sheaf case of Stacks 0EZB.

The *second* edge morphism `R^i (Q ∘ P) ℱ ⟶ Q (R^i P ℱ)` is **not** invertible in general in
positive degrees, and the source's proof of Stacks 0EZA controls it by analysing the second page
of the spectral sequence through degree `n`, with an extra argument in degree `n` exactly. That
analysis is avoided here. The change-of-topology direct image `ε_{Y,*}` is a fully faithful
functor with an exact left adjoint, so the subcategory it embeds is reflective, and for a
reflective inclusion the second edge morphism is invertible at an object as soon as **that
object lies in the subcategory** — this is
`Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_of_isIso_unit`, which uses no
vanishing hypothesis at all. In the situation of Stacks 0EZA the object in question is
`R^i f_{τ',*} ε_{X,*} ℱ`, identified with `R^i(ε_{X,*} ⋙ f_{τ',*}) ℱ` by the first edge
morphism; it lies in the weak Serre class `𝒜'_Y` because `ε_{X,*} ℱ` lies in `𝒜'_X` by
Stacks 0EZ9 and the distinguished class is stable under higher direct images by assumption
`0EZ7` of the situation, and an object of `𝒜'_Y` satisfies the sheaf condition for the finer
topology by assumption `0EZ6`, which is precisely the invertibility of the unit there.

## Main results

* `Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition_zero`: `(V_0)`.
* `Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition_of_le`: `(V_n)` is
  decreasing in `n`.
* `Stacks.ComparingTopologies.isIso_higherDirectImageComparison_zero_app`: the comparison
  transformation of Stacks 0EZA is invertible in degree zero, unconditionally.
* `Stacks.ComparingTopologies.isIso_higherDirectImageComparison_app`: **Stacks 0EZA**, the
  comparison is invertible in every degree `i ≤ n` under `(V_n)`.
* `Stacks.ComparingTopologies.fineWeakSerre_rightDerived_overPushforward`: under `(V_n)`, the
  class `𝒜` is stable under the higher direct images of the distinguished class in degrees
  `i ≤ n`.
* `Stacks.ComparingTopologies.nonempty_iso_abelianComparisonPullback_rightDerived`: under
  `(V_n)`, the degreewise base change identification `ε_Y^{-1} R^i f_{τ',*} ℱ' ≅
  R^i f_{τ,*} ε_X^{-1} ℱ'` of Stacks 0EZF part (2), for `i ≤ n` and a single sheaf of `𝒜'_X`.
* `Stacks.ComparingTopologies.isIso_cohomologyComparison_app`: the single-sheaf case of
  Stacks 0EZB.
* `Stacks.ComparingTopologies.cohomologyComparison_eq_edge`: the comparison map of
  Stacks 0EZC **is** the edge morphism of the pair `(ε_{X,*}, Γ_{τ'}(X, -))`.
* `Stacks.ComparingTopologies.cohomologyComparison_comp_rightDerivedIso`: and so, under
  `Stacks.DerivedIndexing.rightDerivedIso`, it is the degreewise comparison
  `Stacks.DerivedIndexing.rightDerivedPlusEdge` built from the composition isomorphism
  `R(Γ_{τ'}(X, -) ∘ ε_{X,*}) ≅ RΓ_{τ'}(X, -) ∘ Rε_{X,*}` of Stacks 015M.

## What this file does not contain

The induction step `(V_n) ⇒ (V_{n+1})` of Stacks 0EZE, and consequently Stacks 0EZF. That step
is not homological algebra: it is a descent argument, and two things it consumes are still
missing for abelian sheaves.

1. **Stacks 0EZB in full.** *This is no longer missing.* It is proved, for a bounded-below
   object `L` whose cohomology sheaves lie in `𝒜'` in the degrees `0, …, n`, as
   `Stacks.ComparingTopologies.isIso_homology_derivedCohomologyComparison`
   (`ChangeOfTopology/ComparingCohomology.lean:405`, tagged `@[stacks 0EZB]`). The paragraphs
   below describe the ingredients of that proof. The dévissage along the truncation triangles of such an `L` is
   available --
   the hypercohomology of a bounded below complex of abelian sheaves, with its long exact
   sequence, is available in
   `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.AbelianHypercohomology` --
   and the property to propagate along it is "invertible in degrees `≤ n` and a monomorphism
   in degree `n + 1`", the monomorphism half being the injectivity clause of Stacks 0EZC,
   `mono_cohomologyComparison`. The remaining ingredient is the comparison of the *derived* map
   `L ⟶ Rε_{X,*} ε_X^{-1} L` of `Stacks.ComparingTopologies.derivedComparisonUnit`, read on
   hypercohomology, with the degreewise map `cohomologyComparison` of this file: the first is
   produced by the universal property of right derivation on `D⁺` and the second by a comparison
   of injective resolutions.

   That comparison is available in both halves. One is the naturality of
   `Stacks.DerivedIndexing.rightDerivedIso` in the functor variable,
   `Stacks.DerivedIndexing.rightDerivedIso_hom_naturality`, which identifies Mathlib's
   `ℕ`-indexed `CategoryTheory.NatTrans.rightDerived` with the morphism of right derived
   functors on `D⁺` produced by the universal property. The other -- which that does not cover,
   `cohomologyComparison` not being of the form `NatTrans.rightDerived τ i` for a transformation
   `τ` of functors on abelian sheaves -- is
   `cohomologyComparison_comp_rightDerivedIso` of this file: `cohomologyComparison` is the
   *edge* morphism of the pair `(ε_{X,*}, Γ_{τ'}(X, -))`
   (`cohomologyComparison_eq_edge`), and the edge morphism is, under
   `Stacks.DerivedIndexing.rightDerivedIso`, the degreewise comparison built from the
   composition isomorphism `R(Γ_{τ'}(X, -) ∘ ε_{X,*}) ≅ RΓ_{τ'}(X, -) ∘ Rε_{X,*}` -- which
   holds, since `ε_{X,*}` preserves injectives, being a right adjoint with exact left adjoint --
   by `Stacks.DerivedIndexing.edge_comp_rightDerivedIso`.

   The dévissage then needs the step from that degreewise statement to a
   transformation of functors on `D⁺`: the natural map
   `H^n_{τ'}(X, L) ⟶ H^n_τ(X, ε_X^{-1}L)` for `L` in `D⁺(C_{τ'}/X)`, obtained from
   `Stacks.ComparingTopologies.derivedComparisonUnit` and the isomorphism
   `derivedGlobalSectionsComparisonIso` of Stacks 0D6H, together with the statement that on a
   single sheaf `ε_{X,*}ℱ` it is `cohomologyComparison`; and then the dévissage itself along the
   truncation triangles of `L`, propagating "invertible in degrees `≤ n`, monomorphism in degree
   `n + 1`" through the long exact sequences of
   `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.AbelianHypercohomology`.
2. **The derived base change map in degrees `≤ n`**: that
   `Stacks.ComparingTopologies.derivedComparisonBaseChange` induces, on cohomology sheaves in
   degrees `≤ n`, the degreewise comparison `higherDirectImageComparison`, so that Stacks 0EZA
   identifies `ε_Y^{-1} τ_{≤n} R f_{τ',*} ε_{X,*} f_τ^{-1} ℱ` with
   `τ_{≤n} R f_{τ,*} f_τ^{-1} ℱ`. That identification is what produces the object `L` of (1).

Two further inputs which the source's proof uses are available. Stacks 03F3 part (2), by which
the source replaces `X` by an object over it, is not needed in the form the source uses it: the
vanishing of `R^i ε_{X,*} ℱ` reduces to the vanishing of its global sections alone, for every
object of the site, by
`Stacks.ComparingTopologies.isZero_rightDerived_of_isZero_globalSections`. And the criterion by
which a higher change-of-topology direct image is killed by making cohomology classes die on
coverings for the coarser topology -- the abelian-sheaf instance of Stacks 072W -- is
`Stacks.ComparingTopologies.isZero_rightDerived_abelianComparisonPushforward_of_locally_zero`.

Neither `isIso_cohomologyComparison_app` nor
`nonempty_iso_abelianComparisonPullback_rightDerived` carries a Stacks attribute: the first is
one case of the single statement of Stacks 0EZB rather than one clause of it, and the second
assumes `(V_n)`, which is itself the first assertion of Stacks 0EZF -- so it is a step inside
the proof of that tag and not one of its clauses. A tag belongs on a covering set.

## References

* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
* [Stacks Project, Tag 0EZB](https://stacks.math.columbia.edu/tag/0EZB)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0EZE](https://stacks.math.columbia.edu/tag/0EZE)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

namespace CohomologyComparison

/-- **The condition `(V_0)` holds.** It is the empty condition: no natural number `i` satisfies
both `1 ≤ i` and `i ≤ 0`. This is the base of the induction by which Stacks 0EZF obtains
`(V_n)` for every `n`. -/
theorem vanishingCondition_zero (S : CohomologyComparison C) : S.vanishingCondition 0 :=
  fun _ _ _ _ hi hi0 ↦ absurd (hi.trans hi0) (by simp)

/-- The conditions `(V_n)` are decreasing in `n`: vanishing through degree `n` gives vanishing
through any smaller degree. -/
theorem vanishingCondition_of_le {S : CohomologyComparison C} {m n : ℕ} (hmn : m ≤ n)
    (hV : S.vanishingCondition n) : S.vanishingCondition m :=
  fun X F hF i hi him ↦ hV X F hF i hi (him.trans hmn)

end CohomologyComparison

/-- **Stacks 0EZA in degree zero**, the base case `(C_0)` of the induction in its proof: the
comparison

`f_{τ',*} ε_{X,*} ℱ ⟶ ε_{Y,*} f_{τ,*} ℱ`

is invertible, for every morphism `f` of the site and every abelian sheaf `ℱ` on the finer
localized site over `X`. Neither the vanishing condition `(V_n)` nor membership of `ℱ` in `𝒜_X`
nor membership of `f` in the distinguished class is used.

Both factors of the comparison are invertible in degree zero: the first edge morphism because
its vanishing hypothesis is empty there, the second because an `ℕ`-indexed cochain complex has
no boundaries in degree zero and the change-of-topology direct image preserves cycles, being
left exact. -/
instance isIso_higherDirectImageComparison_zero_app (S : CohomologyComparison C) {X Y : C}
    (f : X ⟶ Y) (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) :
    IsIso ((higherDirectImageComparison S f 0).app F) := by
  have h₁ : IsIso ((Stacks.Cohomology.RightDerivedEdge.edge
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
      (overPushforward S.coarseCoverage.toGrothendieck f) 0).app F) :=
    Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app_zero _ _ F
  have h₂ : IsIso ((Stacks.Cohomology.RightDerivedCoEdge.secondEdge
      (overPushforward S.fineCoverage.toGrothendieck f)
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine Y) 0).app F) := inferInstance
  exact IsIso.comp_isIso' h₁ h₂

/-- **Stacks 0EZA in degree zero**, as the invertibility of the whole comparison
transformation. -/
instance isIso_higherDirectImageComparison_zero (S : CohomologyComparison C) {X Y : C}
    (f : X ⟶ Y) : IsIso (higherDirectImageComparison S f 0) :=
  NatIso.isIso_of_isIso_app _

/-- The higher direct images of the distinguished class send `ε_{X,*} ℱ` to `𝒜'_Y` for `ℱ` in
`𝒜_X`. -/
private theorem weakSerre_rightDerived_pushforward_obj (S : CohomologyComparison C) {X Y : C}
    (f : X ⟶ Y) (hf : S.morphismProperty f) (i : ℕ)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) (hF : S.fineWeakSerre X F) :
    S.weakSerre Y (((overPushforward S.coarseCoverage.toGrothendieck f).rightDerived i).obj
      ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).obj F)) :=
  S.weakSerre_rightDerived_relocalizationPushforward f hf _
    ((CohomologyComparison.fineWeakSerre_iff_weakSerre_pushforward S X F).1 hF) i

/-- **Stacks 0EZA.** Assume the vanishing condition `(V_n)`. For a morphism `f : X ⟶ Y` of the
distinguished class, an abelian sheaf `ℱ` of `𝒜_X` on the finer localized site over `X`, and a
degree `i ≤ n`, the comparison

`R^i f_{τ',*} ε_{X,*} ℱ ⟶ ε_{Y,*} R^i f_{τ,*} ℱ`

is an isomorphism.

Both factors of the comparison are invertible, for different reasons. The first edge morphism is
invertible in degree `i` as soon as `R^q ε_{X,*} ℱ` vanishes for `1 ≤ q ≤ i`, which is `(V_n)`;
this is `Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app`, and no spectral sequence is
needed for it. The second edge morphism is invertible as soon as the object it starts from lies
in the essential image of the change-of-topology direct image, by
`Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_of_isIso_unit`; and that object is
`R^i f_{τ',*} ε_{X,*} ℱ` — by the first edge morphism, which has just been seen to be
invertible — which lies in the weak Serre class `𝒜'_Y` because `ε_{X,*} ℱ` lies in `𝒜'_X` and the
distinguished class is stable under higher direct images. -/
@[stacks 0EZA "the comparison is an isomorphism through degree `n`"]
theorem isIso_higherDirectImageComparison_app (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) {X Y : C} (f : X ⟶ Y) (hf : S.morphismProperty f)
    (i : ℕ) (hi : i ≤ n) (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F) :
    IsIso ((higherDirectImageComparison S f i).app F) := by
  have hX : ∀ q, 1 ≤ q → q ≤ i → IsZero (((abelianComparisonPushforward S.fineCoverage
      S.coarseCoverage S.coarse_le_fine X).rightDerived q).obj F) :=
    fun q hq hqi ↦ hV X F hF q hq (hqi.trans hi)
  have h₁ : IsIso ((Stacks.Cohomology.RightDerivedEdge.edge
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
      (overPushforward S.coarseCoverage.toGrothendieck f) i).app F) :=
    Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app _ _ F i hX
  have hM : S.weakSerre Y
      (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X ⋙
        overPushforward S.coarseCoverage.toGrothendieck f).rightDerived i).obj F) :=
    (S.weakSerreClass Y).toIsClosedUnderIsomorphisms.of_iso
      (Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso
        (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
        (overPushforward S.coarseCoverage.toGrothendieck f) F i hX)
      (weakSerre_rightDerived_pushforward_obj S f hf i F hF)
  have h₂ : IsIso ((Stacks.Cohomology.RightDerivedCoEdge.secondEdge
      (overPushforward S.fineCoverage.toGrothendieck f)
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine Y) i).app F) :=
    Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_of_isIso_unit _
      (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage S.coarse_le_fine Y) i F
      (isIso_abelianComparisonAdjunction_unit_of_weakSerre S Y _ hM)
  exact IsIso.comp_isIso' h₁ h₂

/-- **The class `𝒜` is stable under the higher direct images of the distinguished class, in the
range where the comparison of Stacks 0EZA is available.** Assume `(V_n)`. For `f : X ⟶ Y` in the
distinguished class, `ℱ` in `𝒜_X` and `i ≤ n`, the higher direct image `R^i f_{τ,*} ℱ` lies in
`𝒜_Y`.

The assumption `0EZ7` of the situation gives this for the coarser topology: `R^i f_{τ',*} ε_{X,*}
ℱ` lies in `𝒜'_Y`. Stacks 0EZA identifies that sheaf with `ε_{Y,*} R^i f_{τ,*} ℱ`, and Stacks
0EZ9 then detects membership in `𝒜_Y` through `ε_{Y,*}`. -/
theorem fineWeakSerre_rightDerived_overPushforward (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) {X Y : C} (f : X ⟶ Y) (hf : S.morphismProperty f)
    (i : ℕ) (hi : i ≤ n) (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F) :
    S.fineWeakSerre Y
      (((overPushforward S.fineCoverage.toGrothendieck f).rightDerived i).obj F) := by
  have hiso := isIso_higherDirectImageComparison_app S n hV f hf i hi F hF
  refine (CohomologyComparison.fineWeakSerre_iff_weakSerre_pushforward S Y _).2 ?_
  exact (S.weakSerreClass Y).toIsClosedUnderIsomorphisms.of_iso
    (@asIso _ _ _ _ ((higherDirectImageComparison S f i).app F) hiso)
    (weakSerre_rightDerived_pushforward_obj S f hf i F hF)

/-- **The degreewise base change identification of Stacks 0EZF part (2), for a single abelian
sheaf.** Assume `(V_n)`. For `f : X ⟶ Y` in the distinguished class, `ℱ'` in `𝒜'_X` and `i ≤ n`,

`ε_Y^{-1} R^i f_{τ',*} ℱ' ≅ R^i f_{τ,*} ε_X^{-1} ℱ'`.

This is the last line of the proof of Stacks 0EZF: the tag reduces its base change assertion, by
comparing the two spectral sequences of the derived direct image, to this statement for a single
sheaf, and this statement is Stacks 0EZA read through `ε_Y^{-1}`. Concretely, the unit
`ℱ' ⟶ ε_{X,*} ε_X^{-1} ℱ'` is invertible because `ℱ'` lies in `𝒜'_X`, so Stacks 0EZA applies to
`ℱ = ε_X^{-1} ℱ'`, and the counit `ε_Y^{-1} ε_{Y,*} ⟶ 𝟭` is invertible because the
change-of-topology direct image is fully faithful. -/
theorem nonempty_iso_abelianComparisonPullback_rightDerived (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) {X Y : C} (f : X ⟶ Y) (hf : S.morphismProperty f)
    (i : ℕ) (hi : i ≤ n) (F : Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.weakSerre X F) :
    Nonempty ((abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).obj
        (((overPushforward S.coarseCoverage.toGrothendieck f).rightDerived i).obj F) ≅
      ((overPushforward S.fineCoverage.toGrothendieck f).rightDerived i).obj
        ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).obj F)) := by
  have hunit := isIso_abelianComparisonAdjunction_unit_of_weakSerre S X F hF
  have hfine : S.fineWeakSerre X
      ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).obj F) :=
    ⟨F, hF, ⟨Iso.refl _⟩⟩
  have hcomp := isIso_higherDirectImageComparison_app S n hV f hf i hi _ hfine
  exact ⟨(abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).mapIso
      (((overPushforward S.coarseCoverage.toGrothendieck f).rightDerived i).mapIso
          (@asIso _ _ _ _ ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
            S.coarse_le_fine X).unit.app F) hunit) ≪≫
        @asIso _ _ _ _ ((higherDirectImageComparison S f i).app _) hcomp) ≪≫
    asIso ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
      S.coarse_le_fine Y).counit.app _)⟩

/-- **Stacks 0EZB for a single abelian sheaf.** Assume the vanishing condition `(V_n)`. For `ℱ`
in `𝒜_X` and `m ≤ n` the change-of-topology map on cohomology

`H^m_{τ'}(X, ε_{X,*} ℱ) ⟶ H^m_τ(X, ℱ)`

is an isomorphism.

This is the case of Stacks 0EZB in which the bounded below object `L` of `D(C_{τ'}/X)` is a
single sheaf of `𝒜'_X` placed in degree zero: there `ε_X^{-1} L` is `ℱ` and `L` is `ε_{X,*} ℱ`,
by the sheaf-condition assumption of the situation.

The map is the edge morphism of the pair `(ε_{X,*}, Γ_{τ'}(X, -))`, whose composite is
`Γ_τ(X, -)`, so the assertion is the degeneration of that edge morphism in degrees `≤ n`, which
`Stacks.Cohomology.RightDerivedEdgeIso.isIso_homologyMap_of_exactAt` supplies from `(V_n)`: the
direct image of an injective resolution of `ℱ` is exact in the degrees `1, …, m` precisely
because `R^q ε_{X,*} ℱ` vanishes there. No spectral sequence is used. -/
theorem isIso_cohomologyComparison_app (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C) (m : ℕ) (hm : m ≤ n)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) (hF : S.fineWeakSerre X F) :
    IsIso ((cohomologyComparison S X m).app F) := by
  obtain ⟨φ, hφ⟩ := exists_injectiveResolutionComparison S X F (injectiveResolution F)
    (injectiveResolution ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).obj F))
  rw [cohomologyComparison_eq_injectiveResolution S X m F _ _ φ hφ]
  have hmap : IsIso (HomologicalComplex.homologyMap
      (((globalSectionsOver S.coarseCoverage.toGrothendieck X).mapHomologicalComplex
        (ComplexShape.up ℕ)).map φ) m) :=
    Stacks.Cohomology.RightDerivedEdgeIso.isIso_homologyMap_of_exactAt
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
      (injectiveResolution F) _ φ hφ
      (globalSectionsOver S.coarseCoverage.toGrothendieck X) m
      (fun q hq hqm ↦ by
        rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact (hV X F hF q hq (hqm.trans hm)).of_iso
          ((injectiveResolution F).isoRightDerivedObj _ q).symm)
  exact Stacks.Cohomology.RightDerivedEdgeIso.isIso_sandwich _ _ _ hmap

/-! ### The comparison map as the edge morphism of a composite -/

/-- **The change-of-topology comparison on cohomology is the edge morphism of the pair
`(ε_{X,*}, Γ_{τ'}(X, -))`.** Both transformations are characterised by the same formula on any
pair of injective resolutions compatible with the augmentations --
`cohomologyComparison_eq_injectiveResolution` and
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq` -- so evaluating both at the chosen
resolutions and the chosen comparison
`Stacks.Cohomology.RightDerivedEdge.resolutionComparison` identifies them.

The two targets agree on the nose, `ε_{X,*} ⋙ Γ_{τ'}(X, -)` being `Γ_τ(X, -)`
(`abelianComparisonPushforward_comp_globalSectionsOver`). -/
theorem cohomologyComparison_eq_edge (S : CohomologyComparison C) (X : C) (i : ℕ) :
    cohomologyComparison S X i =
      Stacks.Cohomology.RightDerivedEdge.edge
        (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
        (globalSectionsOver S.coarseCoverage.toGrothendieck X) i := by
  refine NatTrans.ext (funext fun F => ?_)
  exact (cohomologyComparison_eq_injectiveResolution S X i F (injectiveResolution F)
      (injectiveResolution _)
      (Stacks.Cohomology.RightDerivedEdge.resolutionComparison _ F)
      (Stacks.Cohomology.RightDerivedEdge.ι_f_zero_comp_resolutionComparison _ F)).trans
    (Stacks.Cohomology.RightDerivedEdge.edge_app_eq _ _ i (injectiveResolution F)
      (injectiveResolution _)
      (Stacks.Cohomology.RightDerivedEdge.resolutionComparison _ F)
      (Stacks.Cohomology.RightDerivedEdge.ι_f_zero_comp_resolutionComparison _ F)).symm

attribute [local instance] HasDerivedCategory.standard

/-- **The change-of-topology comparison on cohomology, read in the derived category.** Under the
comparison `Stacks.DerivedIndexing.rightDerivedIso` of Mathlib's `ℕ`-indexed right derived
functors with the `ℤ`-indexed ones of `CategoryTheory.Functor.rightDerivedPlus`, the degreewise
map `cohomologyComparison` of Stacks 0EZC *is* the degreewise comparison
`Stacks.DerivedIndexing.rightDerivedPlusEdge` built from the composition isomorphism
`R(Γ_{τ'}(X, -) ∘ ε_{X,*}) ≅ RΓ_{τ'}(X, -) ∘ Rε_{X,*}` of Stacks 015M -- which is available
because `ε_{X,*}` preserves injective objects.

This is `cohomologyComparison_eq_edge` followed by
`Stacks.DerivedIndexing.edge_comp_rightDerivedIso`. -/
theorem cohomologyComparison_comp_rightDerivedIso (S : CohomologyComparison C) (X : C) (i : ℕ)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) :
    (cohomologyComparison S X i).app F ≫
        (Stacks.DerivedIndexing.rightDerivedIso
          (globalSectionsOver S.fineCoverage.toGrothendieck X) i).hom.app F =
      (Stacks.DerivedIndexing.rightDerivedIso
            (globalSectionsOver S.coarseCoverage.toGrothendieck X) i).hom.app
          ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
            S.coarse_le_fine X).obj F) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusEdge
          (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
          (globalSectionsOver S.coarseCoverage.toGrothendieck X) (i : ℤ)).app F := by
  rw [cohomologyComparison_eq_edge]
  exact Stacks.DerivedIndexing.edge_comp_rightDerivedIso _ _ i F

end Stacks.ComparingTopologies

end
