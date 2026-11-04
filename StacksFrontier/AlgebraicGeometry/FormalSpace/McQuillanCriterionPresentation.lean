module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSectionProjections
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSupplement

/-!
# The closed-immersion criterion makes every presentation surjective (Stacks 0AIC)

Let `X` be an affine formal algebraic space over a scheme `S` admitting a morphism
`f : X ⟶ Spec A` to an affine scheme through which every closed immersion of an affine
scheme into `X` becomes a closed immersion — condition (2) of **Stacks 0AIC**. This file proves
that then *every* presentation `X = colim X_λ` of `X` by affine thickenings has surjective
section-ring projections `lim Γ(X_μ, 𝒪) → Γ(X_λ, 𝒪)`, which is condition (5).

This is the step the source takes under the heading "Assume (2) for `A` and `X → Spec(A)`": each
stage `X_λ → X` is a thickening, hence a closed immersion into `X`, so by the hypothesis the
composition `X_λ → Spec A` is a closed immersion of affine schemes and `A → Γ(X_λ, 𝒪)` is
surjective. Those surjections are compatible with the transition morphisms of the presentation,
because the comparison morphisms `X_λ → Spec A` are all values of the one natural family `f`;
so the one ring `A` surjects compatibly onto every stage ring, and
`AlgebraicGeometry.FormalSpace.hasSurjectiveSectionProjections_of_surjective_family` turns that
into surjectivity of the projections out of the inverse limit.

Together with
`HasSchemeClosedImmersionCriterionMapToSpec.hasAffineClosedImmersionCriterionMapToSpec`
(condition (3) implies condition (2)) this also gives the two implications out of condition (3).

## Main results

All names are in the namespace `AlgebraicGeometry.FormalSpace`.

* `isClosedImmersionInto_colimitι`: a stage of a presentation of an affine formal algebraic space
  by affine thickenings is a closed immersion into it.
* `hasSurjectiveSectionProjections_of_closedImmersionCriterion`: the surjectivity statement for a
  single presentation.
* `HasAffineClosedImmersionCriterionMapToSpec.hasAllSurjectivePresentations`: **Stacks 0AIC**,
  condition (2) implies condition (5).
* `HasSchemeClosedImmersionCriterionMapToSpec.hasAllSurjectivePresentations` and
  `HasSchemeClosedImmersionCriterionMapToSpec.hasSomeSurjectivePresentation`: **Stacks 0AIC**,
  condition (3) implies conditions (5) and (4).

## Implementation notes

The hypothesis of condition (2) quantifies over closed immersions of *affine* schemes into `X`,
and the stages of a presentation are affine, so nothing is lost by using the affine form of the
criterion; the form with arbitrary schemes is obtained from it in
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan`.

That a stage map is a closed immersion into `X` is `Stacks 0AI9`: the stage map is a
*thickening* into `X` by `AlgebraicGeometry.FormalSpace.isThickening_colimitι`, and a thickening
of schemes is in particular a closed immersion, so the relative property transports along
`CategoryTheory.MorphismProperty.relative_monotone`.

The morphism `X ⟶ Spec A` of condition (2) is an
`AlgebraicGeometry.FormalSpace.MapToScheme`, so its value at a stage is already a morphism
of schemes `X_λ ⟶ Spec A` and nothing has to be descended along the sheafified Yoneda embedding;
the compatibility of those values with the transition morphisms of the presentation is the
naturality of that family, applied to the colimit identity `X_λ ⟶ X_μ ⟶ X`. In particular
`Spec A` is required neither to be an object of the site nor to carry a morphism to `S`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A thickening of schemes is a closed immersion, as an inequality of morphism properties. -/
private theorem isThickening_le_isClosedImmersion :
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) ≤
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
  fun _ _ _ h ↦ h.1

/-- **A stage of a presentation by affine thickenings is a closed immersion into the presented
sheaf.** It is a thickening into it by **Stacks 0AI9**, and a thickening of schemes is a closed
immersion. -/
theorem isClosedImmersionInto_colimitι {I : Type (u + 1)} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : FppfSheaf B S hS)
    (e : colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X) (i : I) :
    IsClosedImmersionInto B S hS
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.hom) :=
  MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
      isThickening_le_isClosedImmersion) _
    (isThickening_colimitι B S hS D hD X e i)

/-- **Stacks 0AIC, the step from condition (2) to condition (5), for a single presentation.**
If a morphism `X ⟶ Spec A` to an affine scheme turns every closed immersion of an
affine scheme into `X` into a closed immersion of schemes, then the section-ring projections of
any presentation of `X` by affine thickenings are surjective: each stage of the presentation is
a closed immersion into `X`, hence a closed subscheme of `Spec A`, so `A` surjects onto all the
stage rings, compatibly because the comparison morphisms are the values of one natural family. -/
theorem hasSurjectiveSectionProjections_of_closedImmersionCriterion
    {X : FppfSheaf B S hS} (A : CommRingCat.{u})
    (f : MapToScheme B S hS (Spec A) X)
    (hf : ∀ (T : BigAffineFppf B S hS)
      (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj T) ⟶ X),
      IsClosedImmersionInto B S hS g →
      IsClosedImmersion (f.app ((BigAffineFppf.inclusion B S hS).obj T) g))
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    HasSurjectiveSectionProjections B S hS D := by
  let Fs := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  let G := D ⋙ T ⋙ Fs
  let q : ∀ i : I, (BigAffineFppf.toScheme B S hS).obj (D.obj i) ⟶ Spec A :=
    fun i ↦ f.app (T.obj (D.obj i)) (colimit.ι G i ≫ e.inv)
  -- They are compatible with the transition morphisms, by naturality of the family.
  have hcomp ⦃i j : I⦄ (φ : i ⟶ j) :
      q i = (BigAffineFppf.toScheme B S hS).map (D.map φ) ≫ q j := by
    have hw : Fs.map (T.map (D.map φ)) ≫ colimit.ι G j = colimit.ι G i := colimit.w G φ
    have hnat := f.app_naturality (T.obj (D.obj j)) (T.obj (D.obj i)) (T.map (D.map φ))
      (colimit.ι G j ≫ e.inv)
    rwa [reassoc_of% hw] at hnat
  -- So the one ring `Γ(Spec A, 𝒪)` surjects compatibly onto every stage ring.
  refine hasSurjectiveSectionProjections_of_surjective_family B S hS
    (Λ := Scheme.Γ.obj (op (Spec A)))
    (fun j x ↦ Scheme.Γ.map (q (unop j)).op x) (fun {j k} g x ↦ ?_) (fun j ↦ ?_)
  · have key : Scheme.Γ.map (q (unop j)).op ≫
        Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map (D.map g.unop)).op =
        Scheme.Γ.map (q (unop k)).op := by
      rw [← Scheme.Γ.map_comp, ← op_comp, ← hcomp g.unop]
    calc (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).map g
            (Scheme.Γ.map (q (unop j)).op x)
        = (Scheme.Γ.map (q (unop j)).op ≫
            Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map (D.map g.unop)).op) x :=
          (CommRingCat.comp_apply _ _ _).symm
      _ = Scheme.Γ.map (q (unop k)).op x := by rw [key]
  · -- Each stage is a closed immersion into `X`, hence a closed subscheme of `Spec A`.
    have : IsClosedImmersion (q (unop j)) :=
      hf (D.obj (unop j)) _ (isClosedImmersionInto_colimitι B S hS D hD X e.symm (unop j))
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (q (unop j))).2

/-- **Stacks 0AIC, condition (2) implies condition (5).** If some morphism from `X` to an affine
scheme turns every closed immersion of an affine scheme into `X` into a closed immersion, then
every presentation of `X` by affine thickenings has surjective section-ring projections. -/
@[stacks 0AIC "(2) implies (5)"]
theorem HasAffineClosedImmersionCriterionMapToSpec.hasAllSurjectivePresentations
    {X : FppfSheaf B S hS} (hX : HasAffineClosedImmersionCriterionMapToSpec B S hS X) :
    HasAllSurjectivePresentations B S hS X := by
  obtain ⟨hA, A, f, hf⟩ := hX
  exact ⟨hA, fun _ _ _ _ D hD ⟨e⟩ ↦
    hasSurjectiveSectionProjections_of_closedImmersionCriterion B S hS A f hf D hD e⟩

/-- **Stacks 0AIC, condition (3) implies condition (5).** The criterion for closed immersions of
arbitrary schemes restricts to affine schemes, and then condition (2) gives condition (5). -/
@[stacks 0AIC "(3) implies (5)"]
theorem HasSchemeClosedImmersionCriterionMapToSpec.hasAllSurjectivePresentations
    {X : FppfSheaf B S hS} (hX : HasSchemeClosedImmersionCriterionMapToSpec B S hS X) :
    HasAllSurjectivePresentations B S hS X :=
  HasAffineClosedImmersionCriterionMapToSpec.hasAllSurjectivePresentations B S hS
    (hX.hasAffineClosedImmersionCriterionMapToSpec B S hS)

/-- **Stacks 0AIC, condition (3) implies condition (4).** Every presentation of `X` by affine
thickenings has surjective section-ring projections, and `X` has one. -/
@[stacks 0AIC "(3) implies (4)"]
theorem HasSchemeClosedImmersionCriterionMapToSpec.hasSomeSurjectivePresentation
    {X : FppfSheaf B S hS} (hX : HasSchemeClosedImmersionCriterionMapToSpec B S hS X) :
    HasSomeSurjectivePresentation B S hS X :=
  (HasSchemeClosedImmersionCriterionMapToSpec.hasAllSurjectivePresentations B S hS
    hX).hasSomeSurjectivePresentation B S hS

end AlgebraicGeometry.FormalSpace

end
