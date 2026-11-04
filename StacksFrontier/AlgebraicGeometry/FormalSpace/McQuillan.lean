module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver

/-!
# McQuillan's criterion for affine formal algebraic spaces

Stacks 0AIC says that for an fppf sheaf `X` on the big fppf site of `S` satisfying the
set-theoretic condition of Stacks 0AIS the following are equivalent.

1. `X` is the colimit of `Spec (A / I)` over the weak ideals of definition `I` of a weakly
   admissible topological ring `A` over `S`.
2. `X` is an affine formal algebraic space admitting a morphism to an affine scheme through
   which every closed immersion of an *affine scheme* into `X` is a closed immersion.
3. The same with *scheme* in place of *affine scheme*.
4. `X` is an affine formal algebraic space and for *some* presentation `X = colim Xλ` by
   affine thickenings the projections `lim Γ(Xλ, 𝒪) → Γ(Xλ, 𝒪)` are surjective.
5. The same for *every* such presentation.

## Main definitions

* `AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation`: a presentation of `X` by the
  quotients of a topological ring by its weak ideals of definition, used by condition (1).
* `AlgebraicGeometry.FormalSpace.IsClosedImmersionInto`: the relative closed-immersion
  property for a morphism of fppf sheaves.
* `AlgebraicGeometry.FormalSpace.sectionDiagram` and
  `AlgebraicGeometry.FormalSpace.HasSurjectiveSectionProjections`: the inverse system of
  section rings of a presentation, and surjectivity of all its projections.
* `AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterion` and
  `AlgebraicGeometry.FormalSpace.HasSchemeClosedImmersionCriterion`: conditions (2) and (3).
* `AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation` and
  `AlgebraicGeometry.FormalSpace.HasAllSurjectivePresentations`: conditions (4) and (5).

## Main results

* `HasSchemeClosedImmersionCriterion.hasAffineClosedImmersionCriterion`: condition (3) implies
  condition (2).
* `HasAllSurjectivePresentations.hasSomeSurjectivePresentation`: condition (5) implies
  condition (4).

## Implementation notes

Not all implications of Stacks 0AIC are proved, so its tag, which names the equivalence of the
five conditions, is registered on no declaration.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The weak ideals of definition of a topological ring, ordered by reverse inclusion. -/
abbrev WeakIdeals (A : Type u) [CommRing A] [TopologicalSpace A] :=
  OrderDual (TopologicalRing.WeakIdealOfDefinitionIndex A)

/-- A presentation of an fppf sheaf `X` as the formal spectrum of a topological ring `A`: a
diagram of affine schemes over `S` indexed by the weak ideals of definition of `A`, an
identification of its stages with the spectra of the quotients of `A`, compatibility of the
transition morphisms with the canonical quotient homomorphisms, and an identification of its
colimit with `X`. The ring is not required to carry a morphism to `S`; the structure morphisms
of the quotients are the datum instead. -/
structure WeakIdealColimitPresentation (A : Type u) [CommRing A] [TopologicalSpace A]
    (X : FppfSheaf B S hS) where
  /-- The affine scheme over `S` attached to each weak ideal of definition. -/
  diagram : WeakIdeals A ⥤ BigAffineFppf B S hS
  /-- Each stage is the spectrum of the corresponding quotient of `A`. -/
  quotientIso : ∀ J : WeakIdeals A,
    (BigAffineFppf.toScheme B S hS).obj (diagram.obj J) ≅ Spec (.of (A ⧸ J.1))
  /-- The transition morphisms are induced by the canonical quotient homomorphisms. -/
  quotientIso_natural : ∀ ⦃J K : WeakIdeals A⦄ (f : J ⟶ K),
    (BigAffineFppf.toScheme B S hS).map (diagram.map f) ≫ (quotientIso K).hom =
      (quotientIso J).hom ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom f)))
  /-- The colimit of the diagram is `X`. -/
  colimitIso : X ≅ colimit
    (diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))

/-- A morphism of fppf sheaves is a *closed immersion* when each of its base changes along a
represented sheaf is a closed immersion of schemes. -/
abbrev IsClosedImmersionInto {Y Z : FppfSheaf B S hS} (f : Y ⟶ Z) : Prop :=
  (MorphismProperty.relative
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f

/-- The inverse system of rings of global sections of the stages of an affine presentation. It
is contravariant in the index, so it is a functor out of the opposite category. -/
abbrev sectionDiagram {I : Type (u + 1)} [Category I] (D : I ⥤ BigAffineFppf B S hS) :
    Iᵒᵖ ⥤ CommRingCat.{u} :=
  D.op ⋙ (BigAffineFppf.toScheme B S hS).op ⋙ Scheme.Γ

/-- Every projection from the inverse limit of the section rings of an affine presentation to
a single stage is surjective, the limit being the set of sections of the underlying set-valued
diagram. -/
abbrev HasSurjectiveSectionProjections {I : Type (u + 1)} [Category I]
    (D : I ⥤ BigAffineFppf B S hS) : Prop :=
  ∀ i : I, Function.Surjective
    (fun s : (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections ↦
      s.1 (Opposite.op i))

/-- Condition (2) of Stacks 0AIC: `X` is an affine formal algebraic space and there is a
morphism from `X` to an affine scheme over `S` which turns every closed immersion of an
affine scheme into `X` into a closed immersion of schemes. -/
abbrev HasAffineClosedImmersionCriterion (X : FppfSheaf B S hS) : Prop :=
  IsAffineFormalAlgebraicSpace B S hS X ∧
    ∃ A : BigAffineFppf B S hS,
      ∃ f : X ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj A),
        ∀ (T : BigAffineFppf B S hS)
          (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
              ((BigAffineFppf.inclusion B S hS).obj T) ⟶ X),
          IsClosedImmersionInto B S hS g → IsClosedImmersionInto B S hS (g ≫ f)

/-- Condition (3) of Stacks 0AIC: as `HasAffineClosedImmersionCriterion`, but the closed
immersions into `X` range over all schemes of the site rather than only the affine ones. -/
abbrev HasSchemeClosedImmersionCriterion (X : FppfSheaf B S hS) : Prop :=
  IsAffineFormalAlgebraicSpace B S hS X ∧
    ∃ A : BigAffineFppf B S hS,
      ∃ f : X ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj A),
        ∀ (T : BigFppfOver B S hS)
          (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X),
          IsClosedImmersionInto B S hS g → IsClosedImmersionInto B S hS (g ≫ f)

/-- Condition (4) of Stacks 0AIC: `X` is an affine formal algebraic space and *some*
presentation of it by affine thickenings has all its section-ring projections surjective. -/
abbrev HasSomeSurjectivePresentation (X : FppfSheaf B S hS) : Prop :=
  IsAffineFormalAlgebraicSpace B S hS X ∧
    ∃ (I : Type (u + 1)) (pre : Preorder I),
      letI : Preorder I := pre
      Nonempty I ∧ IsDirected I (· ≤ ·) ∧
        ∃ D : I ⥤ BigAffineFppf B S hS,
          (∀ ⦃i j : I⦄ (f : i ⟶ j),
            Stacks.Thickenings.IsThickening
              ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
          Nonempty (X ≅ colimit
            (D ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ∧
          HasSurjectiveSectionProjections B S hS D

/-- Condition (5) of Stacks 0AIC: `X` is an affine formal algebraic space and *every*
presentation of it by affine thickenings has all its section-ring projections surjective. -/
abbrev HasAllSurjectivePresentations (X : FppfSheaf B S hS) : Prop :=
  IsAffineFormalAlgebraicSpace B S hS X ∧
    ∀ (I : Type (u + 1)) (pre : Preorder I),
      letI : Preorder I := pre
      [Nonempty I] → [IsDirected I (· ≤ ·)] →
      ∀ D : I ⥤ BigAffineFppf B S hS,
        (∀ ⦃i j : I⦄ (f : i ⟶ j),
          Stacks.Thickenings.IsThickening
            ((BigAffineFppf.toScheme B S hS).map (D.map f))) →
        Nonempty (X ≅ colimit
          (D ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) →
        HasSurjectiveSectionProjections B S hS D

/-- Condition (3) of Stacks 0AIC implies condition (2). -/
theorem HasSchemeClosedImmersionCriterion.hasAffineClosedImmersionCriterion
    {X : FppfSheaf B S hS} (hX : HasSchemeClosedImmersionCriterion B S hS X) :
    HasAffineClosedImmersionCriterion B S hS X := by
  obtain ⟨hA, A, f, hf⟩ := hX
  exact ⟨hA, A, f, fun T g hg ↦ hf ((BigAffineFppf.inclusion B S hS).obj T) g hg⟩

/-- Condition (5) of Stacks 0AIC implies condition (4). -/
theorem HasAllSurjectivePresentations.hasSomeSurjectivePresentation
    {X : FppfSheaf B S hS} (hX : HasAllSurjectivePresentations B S hS X) :
    HasSomeSurjectivePresentation B S hS X := by
  obtain ⟨hA, hall⟩ := hX
  obtain ⟨hset, I, pre, hne, hdir, D, hD, he⟩ := hA
  exact ⟨⟨hset, I, pre, hne, hdir, D, hD, he⟩, I, pre, hne, hdir, D, hD, he,
    @hall I pre hne hdir D hD he⟩

end AlgebraicGeometry.FormalSpace

end
