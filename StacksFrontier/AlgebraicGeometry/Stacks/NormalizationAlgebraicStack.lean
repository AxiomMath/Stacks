module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackModel
public import StacksFrontier.AlgebraicGeometry.Stacks.Normalization
public import StacksFrontier.AlgebraicGeometry.Stacks.NormalizationGroupoidConstruction
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAtlasSmallUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationExistence

/-!
# The normalization of an algebraic stack (Stacks 0GMK)

Let `𝒳` be an algebraic stack over `S` satisfying the equivalent conditions of Stacks 0GMI:
some smooth surjective chart `U ⟶ 𝒳` by a scheme has finitely many irreducible components over
every quasi-compact open. Stacks 0GMK defines the *normalization* of `𝒳` as the morphism
`ν : 𝒳^ν ⟶ 𝒳` constructed in the proof of Stacks 0GMJ, which this file carries out:

1. choose a presentation `𝒳 ≃ [U/R]` by a smooth groupoid in algebraic spaces (Stacks 04T3);
2. its object space `U` is smooth over `𝒳`, so it satisfies the conditions of Stacks 0BB1 by
   Stacks 0GMI, and the normalized groupoid `(U^ν, R^ν, s^ν, t^ν, c^ν)` is constructed
   (`AlgebraicGeometry.Stack.normalizationGroupoid`, through Stacks 07U4);
3. `𝒳^ν = [U^ν/R^ν]` is an algebraic stack by Stacks 04TK, and `ν` is the 1-morphism of
   Stacks 046Q induced by the morphism of groupoids `(U^ν, R^ν) ⟶ (U, R)`, followed by the
   presentation `[U/R] ≃ 𝒳`.

Nothing is assumed beyond the hypothesis of Stacks 0GMI: every ingredient of the normalized
groupoid is constructed.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.normalizationStack`: the algebraic stack `𝒳^ν`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.normalization`: **Stacks 0GMK**, the normalization
  `ν : 𝒳^ν ⟶ 𝒳`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasLocallyFiniteIrreducibleComponents_objects`: the
  object space of every presentation of `𝒳` satisfies the conditions of Stacks 0BB1.

## Implementation notes

The source does not assert that the construction is independent of the chosen presentation
(that is a consequence of the base change property of Stacks 0GMJ, which characterizes `ν`), so
the presentation is a choice, `AlgebraicGeometry.Stack.AlgebraicStacks.normalizationPresentation`,
made once from Stacks 04T3.

The 1-morphism of quotient stacks used is `AlgebraicGeometry.Stack.quotientStackMap`, the one
for which Stacks 04ZN is proved
(`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare_of_isPullback`), and its source
square is cartesian by construction
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Normalized.isPullback_source`).

## References

* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04T3](https://stacks.math.columbia.edu/tag/04T3)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0GMI](https://stacks.math.columbia.edu/tag/0GMI)
* [Stacks Project, Tag 0GMJ](https://stacks.math.columbia.edu/tag/0GMJ)
* [Stacks Project, Tag 0GMK](https://stacks.math.columbia.edu/tag/0GMK)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The chosen presentation `𝒳 ≃ [U/R]` of an algebraic stack by a smooth groupoid in algebraic
spaces (Stacks 04T3) from which its normalization is built. -/
noncomputable def normalizationPresentation (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    GroupoidPresentation B S hS 𝒳.val.val :=
  (nonempty_groupoidPresentation B S hS 𝒳.val 𝒳.property).some

/-- **The object space of a presentation of an algebraic stack satisfying the conditions of
Stacks 0GMI satisfies the conditions of Stacks 0BB1.** Its atlas `U ⟶ 𝒳` is smooth (Stacks 04X0),
and condition (3) of Stacks 0GMI applies to it. -/
theorem hasLocallyFiniteIrreducibleComponents_objects (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} =>
        ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) 𝒳)
    (P : GroupoidPresentation B S hS 𝒳.val.val) :
    Space.HasLocallyFiniteIrreducibleComponents B S hS P.groupoid.objects.obj := by
  obtain ⟨hrep, hrel⟩ := GroupoidPresentation.isRelativelySmooth_atlasMap P 𝒳.property
  have hsm : AlgebraicStacks.IsSmooth B S hS
      (show algebraicSpaceStack.{u, w} B S hS P.groupoid.objects.obj P.groupoid.objects.property ⟶
          𝒳 from Bicategory.InducedBicategory.mkHom (GroupoidPresentation.atlasMap P)) :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hrep hrel
  exact (forall_smooth_chart_iff_forall_space B S hS 𝒳).1
    ((exists_smooth_atlas_iff_forall_smooth_chart B S hS 𝒳).1 h𝒳) _ _ _ hsm

/-- The normalized groupoid `(U^ν, R^ν, s^ν, t^ν, c^ν)` of the chosen presentation. -/
noncomputable def normalizationGroupoidOf (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} =>
        ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) 𝒳) :
    NormalizationGroupoid B S hS (normalizationPresentation 𝒳).groupoid :=
  normalizationGroupoid (normalizationPresentation 𝒳).smooth
    (hasLocallyFiniteIrreducibleComponents_objects 𝒳 h𝒳 (normalizationPresentation 𝒳))

/-- **The algebraic stack `𝒳^ν`** of an algebraic stack satisfying the conditions of
Stacks 0GMI: the quotient stack `[U^ν/R^ν]` of the normalized groupoid of a presentation, an
algebraic stack by Stacks 04TK. -/
noncomputable def normalizationStack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} =>
        ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) 𝒳) :
    AlgebraicStacks.{u, w} B S hS :=
  smoothQuotientAlgebraicStack.{u, w} (normalizationGroupoidOf 𝒳 h𝒳).smooth

/-- **Stacks 0GMK, the normalization of an algebraic stack.** Let `𝒳` be an algebraic stack
satisfying the equivalent conditions of Stacks 0GMI. Its *normalization* is the morphism
`ν : 𝒳^ν ⟶ 𝒳` constructed in the proof of Stacks 0GMJ: for a presentation `𝒳 ≃ [U/R]`
(Stacks 04T3), `𝒳^ν = [U^ν/R^ν]` is the quotient stack of the normalized groupoid, and `ν` is the
1-morphism `[U^ν/R^ν] ⟶ [U/R]` of Stacks 046Q induced by the morphism of groupoids
`(U^ν, R^ν) ⟶ (U, R)`, followed by the presentation.

Every ingredient is constructed from `𝒳` and the hypothesis of Stacks 0GMI: the normalization
`U^ν` (Stacks 07U4), the cartesian square `R^ν = U^ν ×_{U, s} R`, the groupoid structure and its
smoothness are those of `AlgebraicGeometry.Stack.normalizationGroupoid`. -/
@[stacks 0GMK]
noncomputable def normalization (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} =>
        ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) 𝒳) :
    normalizationStack 𝒳 h𝒳 ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp
      (BasedFunctor.comp
        ⟨(smoothQuotientAlgebraicStackEquivalenceOver.{u, w}
            (normalizationGroupoidOf 𝒳 h𝒳).smooth).inv.functor,
          (smoothQuotientAlgebraicStackEquivalenceOver.{u, w}
            (normalizationGroupoidOf 𝒳 h𝒳).smooth).inv.w⟩
        (quotientStackMap (normalizationGroupoidOf 𝒳 h𝒳).hom))
      (normalizationPresentation 𝒳).basedFunctor))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
