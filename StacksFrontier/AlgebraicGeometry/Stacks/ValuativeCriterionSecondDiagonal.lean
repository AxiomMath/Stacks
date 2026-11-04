module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniquenessPoints

/-!
# Valuative criterion for the second diagonal (Stacks 0CLR)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site `B`.
**Stacks 0CLR** says that if the relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is quasi-separated and
if the category of dotted arrows of *every* valuative diagram for `f` — every diagram (0CLB)
together with every choice of the 2-morphism `γ` of Definition 0CLA — is a setoid, then `Δ_f` is
separated. It is the converse of the setoid assertion of Stacks 0CLC, which is formalized in
`StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionDottedGroupoid`.

The route taken here is not the source's, which the source itself invites the reader to replace
("we strongly urge the reader to find their own proof"). The source argues through the relative
inertia: it shows that the neutral section `e = Δ_{f,2}` satisfies the existence part of the
valuative criterion, because the setoid hypothesis forces the automorphism carried by a point of
the inertia to be trivial, and then concludes by Stacks 04YZ, Stacks 0CLL and the valuative
criterion for universal closedness of morphisms of algebraic spaces. Here instead the setoid
hypothesis is fed into Stacks 0E8L, which already identifies the dotted arrows of a valuative
diagram for `Δ_f` with the morphisms between two dotted arrows for `f`, and the conclusion comes
from the valuative criterion for *separatedness* of morphisms of algebraic spaces, Stacks 03KV.
In two steps:

1. A setoid category is thin, so the setoid hypothesis makes the morphisms between the two
   dotted arrows `(a₁, α₁, id)` and `(a₂, α₂, φ)` of Stacks 0E8L unique when they exist. Through
   the bijection of Stacks 0E8L, part (2), a dotted-arrow category for `Δ_f` therefore has at
   most one isomorphism class; being a setoid already (Stacks 0E8L, part (2), again,
   unconditionally), `Δ_f` satisfies the uniqueness part of the valuative criterion,
   Definition 0CLG.
2. By Stacks 0CLJ that uniqueness is inherited by every algebraic space representing a base
   change of `Δ_f` along a scheme-valued point, where it combines with quasi-separatedness
   through Stacks 03KV to give separatedness. Reassembling those base changes is the relative
   sense of Stacks 04XB in which separatedness of `Δ_f` is read.

## Main results

* `AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_of_isSetoidCategory_dottedArrow`:
  **Stacks 0CLR**.
* `AlgebraicGeometry.Stack.valuativeCriterionUniqueness_relativeDiagonal_of_isSetoid_dottedArrow`:
  step 1, the uniqueness part of the valuative criterion for `Δ_f`.
* `AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_of_valuativeCriterionUniqueness`:
  step 2, Stacks 03KV for the relative diagonal of a 1-morphism of algebraic stacks.
* `IsSetoidCategory.subsingleton_hom`: a setoid category is thin.

## Implementation notes

Quasi-separatedness and separatedness of `Δ_f` are read in the relative sense of Properties of
Stacks, Section 04XB, as `AlgebraicGeometry.Stack.IsQuasiSeparated` and
`AlgebraicGeometry.Stack.IsSeparated` of the 1-morphism
`AlgebraicGeometry.Stack.relativeDiagonal` of categories fibred in groupoids. That is the sense
`Δ_f` is representable by algebraic spaces in — part (1) of Stacks 04XS, so no hypothesis on `f`
is needed for it — and the sense in which the hypothesis of Stacks 0CLC and the statements of
Stacks 04YZ are written, so 0CLR and 0CLC are visibly converse. Both hypotheses are used: the
setoid hypothesis in step 1 and quasi-separatedness in step 2.

The two dotted-arrow bundles of the hypothesis and of step 1 are the same one,
`AlgebraicGeometry.Stack.ValuativeDiagram`, which is diagram (0CLB) together with `γ`; the
`Δ_f`-diagram of step 1 is built from the given `f`-diagram by replacing only its special point
and its `γ`, so no transport is needed. Step 1 quantifies the hypothesis over the diagrams for
`f` whose special point is `(a₁ ∘ f, id ⋆ α₁)`, which is the shape Stacks 0E8L produces.

Step 2 passes through the lower-shriek extension rather than through Stacks 03YK directly: the
uniqueness criterion that Stacks 0CLJ delivers is one for the structural morphism of the
representing presheaf over the *slice* site of the scheme-valued point, whereas the relative
property of Stacks 04XB is read over `S`. The two are identified by
`AlgebraicGeometry.Space.isQuasiSeparated_relocalizeToYoneda_iff` on the way in and by
`AlgebraicGeometry.Space.isSeparated_relocalize` on the way out, together with
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`, which replaces the structural morphism of
Stacks 04SG by the relocalization's own. The two `RespectsIso` hypotheses are supplied by hand
from the base-change stability of the two properties, because the instance available for
quasi-separatedness goes through an fpqc precoverage whose universe is not determined by the
goal.

## References

* [Stacks Project, Tag 02XZ](https://stacks.math.columbia.edu/tag/02XZ)
* [Stacks Project, Tag 03KV](https://stacks.math.columbia.edu/tag/03KV)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 0CLA](https://stacks.math.columbia.edu/tag/0CLA)
* [Stacks Project, Tag 0CLB](https://stacks.math.columbia.edu/tag/0CLB)
* [Stacks Project, Tag 0CLC](https://stacks.math.columbia.edu/tag/0CLC)
* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
* [Stacks Project, Tag 0CLJ](https://stacks.math.columbia.edu/tag/0CLJ)
* [Stacks Project, Tag 0CLR](https://stacks.math.columbia.edu/tag/0CLR)
* [Stacks Project, Tag 0E8L](https://stacks.math.columbia.edu/tag/0E8L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

/-- **A setoid category is thin.** All its morphisms are invertible, so it is a groupoid, and
each of its endomorphism monoids is a subsingleton; `CategoryTheory.Groupoid.isThin_iff` turns
the second fact into thinness. -/
theorem IsSetoidCategory.subsingleton_hom {C : Type*} [Category C]
    (h : IsSetoidCategory C) (X Y : C) : Subsingleton (X ⟶ Y) :=
  let : Groupoid C := Groupoid.ofIsIso h.1
  (Groupoid.isThin_iff C).2 (fun c => ⟨fun f g => (h.2 c f).trans (h.2 c g).symm⟩) X Y

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-! ### The uniqueness part of the valuative criterion for the relative diagonal -/

/-- **Any two dotted arrows of a valuative diagram for the relative diagonal are isomorphic, as
soon as the dotted-arrow category of `f` is a setoid at the diagram's valuation ring.**

By part (2) of Stacks 0E8L the isomorphism classes of dotted arrows of a valuative diagram `D` for
`Δ_f` are the morphisms between the two dotted arrows `(a₁, α₁, id)` and `(a₂, α₂, φ)` of part
(1), for the `f`-diagram with the same generic point as `D` and special point `f ∘ a₁`; the setoid
hypothesis makes that a subsingleton, so `D` has at most one isomorphism class.

That `f`-diagram differs from `D` only in its special point and filler, so its valuation ring is
`D`'s with the same ring structure: a setoid hypothesis imposed only on a restricted class of
valuation rings — discrete ones, for **Stacks 0E80** — suffices. The ring, domain and
valuation-ring structures are passed to `Pred` explicitly because
`AlgebraicGeometry.Stack.ValuativeDiagram` does not register its fields as instances. -/
theorem nonempty_iso_dottedArrow_relativeDiagonal_of_pred (f : 𝒳 ⟶ 𝒴)
    (Pred : ∀ R : Type u, [CommRing R] → [IsDomain R] → [ValuationRing R] → Prop)
    (hsetoid : ∀ D : ValuativeDiagram B S hS 𝒳 𝒴 f,
      @Pred D.R D.ring D.domain D.valuation →
      IsSetoidCategory (CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ))
    (D : ValuativeDiagram B S hS 𝒳 (AlgebraicStacks.twoFibreProduct B S hS f f)
      (AlgebraicStacks.relativeDiagonal B S hS f))
    (hD : @Pred D.R D.ring D.domain D.valuation)
    (a b : CategoryTheory.DottedArrow D.x D.j
      (AlgebraicStacks.relativeDiagonal B S hS f).hom D.y D.γ) :
    Nonempty (a ≅ b) := by
  have hthin := (hsetoid { D with
      y := (D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ≫ f.hom
      γ := diagonalWitness B S hS D } hD).subsingleton_hom
    (diagonalDottedArrowFst B S hS D) (diagonalDottedArrowSnd B S hS D)
  have hq : (diagonalDottedArrowClassesEquiv B S hS D) (Quotient.mk _ a)
      = (diagonalDottedArrowClassesEquiv B S hS D) (Quotient.mk _ b) :=
    hthin.allEq _ _
  exact Quotient.exact ((diagonalDottedArrowClassesEquiv B S hS D).injective hq)

/-- **The relative diagonal satisfies the uniqueness part of the valuative criterion as soon as
every dotted-arrow category of `f` is a setoid.** This is Definition 0CLG for
`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`.

The setoid half holds unconditionally and the other half is
`AlgebraicGeometry.Stack.nonempty_iso_dottedArrow_relativeDiagonal_of_pred` at the trivially true
predicate. -/
theorem valuativeCriterionUniqueness_relativeDiagonal_of_isSetoid_dottedArrow
    (f : 𝒳 ⟶ 𝒴)
    (hsetoid : ∀ D : ValuativeDiagram B S hS 𝒳 𝒴 f,
      IsSetoidCategory (CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ)) :
    ValuativeCriterion.Uniqueness B S hS (AlgebraicStacks.relativeDiagonal B S hS f) :=
  fun D => ⟨isSetoidCategory_dottedArrow_relativeDiagonal B S hS D,
    nonempty_iso_dottedArrow_relativeDiagonal_of_pred B S hS f (fun _ => True)
      (fun D' _ => hsetoid D') D trivial⟩

/-! ### Stacks 03KV for the relative diagonal -/

/-- **Stacks 03KV for the relative diagonal of a 1-morphism of algebraic stacks.** A
quasi-separated relative diagonal satisfying the uniqueness part of the valuative criterion is
separated, both conditions read in the relative sense of Stacks 04XB.

`Δ_f` is representable by algebraic spaces, so by Stacks 0CLJ the uniqueness criterion holds for
the structural morphism of every presheaf representing a base change of `Δ_f` along a
scheme-valued point of `𝒳 ×_𝒴 𝒳`, over the site of that point. Quasi-separatedness of that
structural morphism is quasi-separatedness of the base change, and Stacks 03KV turns the two into
separatedness, which the lower-shriek extension carries back to `S`. -/
theorem isSeparated_relativeDiagonal_of_valuativeCriterionUniqueness (f : 𝒳 ⟶ 𝒴)
    (hqs : IsQuasiSeparated B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom))
    (hU : ValuativeCriterion.Uniqueness B S hS (AlgebraicStacks.relativeDiagonal B S hS f)) :
    IsSeparated B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) := by
  have hslice := (valuativeCriterionUniqueness_iff_baseChange B S hS
    (AlgebraicStacks.relativeDiagonal B S hS f)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).mp hU
  have hriqs : MorphismProperty.RespectsIso (Space.quasiSeparatedProperty B S hS) :=
    (Space.isQuasiSeparated_isStableUnderBaseChange B S hS).respectsIso
  have hrisep' : MorphismProperty.RespectsIso (@Space.IsSeparated B S hS) :=
    Space.isSeparated_respectsIso B S hS
  intro U y hy F hF he
  obtain ⟨e⟩ := he
  -- quasi-separatedness of the base change, moved to the site of `U`
  have hqsW : Space.IsQuasiSeparated B U.left.1 U.left.2
      (Space.toYonedaId B U.left.1 U.left.2 F) :=
    (Space.isQuasiSeparated_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom F).mp
      ((prop_algebraicSpaceMap_iff B S hS (Space.quasiSeparatedProperty B S hS) U F hF).mp
        (hqs U y hy F hF ⟨e⟩))
  -- separatedness of the base change over the site of `U`, by Stacks 03KV
  have hsepW : Space.IsSeparated B U.left.1 U.left.2
      (Space.toYonedaId B U.left.1 U.left.2 F) :=
    Space.isSeparated_of_isQuasiSeparated_of_valuativeCriterion_uniqueness hF
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _) _ hqsW
      (hslice U y hy F hF e (Space.toYonedaId B U.left.1 U.left.2 F))
  have _ := isIso_relocalizeToYoneda_yonedaId B U.left.1 S U.left.2 hS U.hom
  have hsepS : Space.IsSeparated B S hS (OverShriek.relocalizeToYoneda U.hom F) := by
    rw [← relocalizeToYoneda_eq_map_toYonedaId B U.left.1 S U.left.2 hS U.hom F]
    refine (MorphismProperty.cancel_right_of_respectsIso (@Space.IsSeparated B S hS) _ _).2 ?_
    exact Space.isSeparated_relocalize B U.left.1 U.left.2 hS U.hom hsepW
  exact (prop_algebraicSpaceMap_iff B S hS (Space.separatedProperty B S hS) U F hF).mpr hsepS

/-! ### Stacks 0CLR -/

/-- **Stacks 0CLR.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. If the
relative diagonal `Δ_f` is quasi-separated, and if for every diagram (0CLB) and every choice of
`γ` as in Definition 0CLA the category of dotted arrows is a setoid, then `Δ_f` is separated.

Both conditions on `Δ_f` are read in the relative sense of Stacks 04XB. The setoid hypothesis
gives the uniqueness part of the valuative criterion for `Δ_f` through Stacks 0E8L, and
quasi-separatedness turns that into separatedness through Stacks 03KV. This is the converse of
the setoid assertion of Stacks 0CLC. -/
@[stacks 0CLR]
theorem isSeparated_relativeDiagonal_of_isSetoidCategory_dottedArrow (f : 𝒳 ⟶ 𝒴)
    (hqs : IsQuasiSeparated B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom))
    (hsetoid : ∀ D : ValuativeDiagram B S hS 𝒳 𝒴 f,
      IsSetoidCategory (CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ)) :
    IsSeparated B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
  isSeparated_relativeDiagonal_of_valuativeCriterionUniqueness B S hS f hqs
    (valuativeCriterionUniqueness_relativeDiagonal_of_isSetoid_dottedArrow B S hS f
      hsetoid)

end AlgebraicGeometry.Stack

end
