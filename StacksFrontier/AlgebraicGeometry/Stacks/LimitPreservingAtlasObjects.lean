module

public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRelativeDescentFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# An atlas whose composite with a locally finitely presented 1-morphism is limit preserving on
objects

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` locally of finite presentation. The
scheme presentation `a : (Sch/S)/U ⟶ 𝒳` of the fourth clause of Stacks 026O lifts every object of
`𝒳` along a single flat, locally finitely presented, surjective morphism of schemes, and its
composite with `f` is limit preserving on objects (Stacks 06CU). These are the two inputs about
the atlas that the descent of an object over an affine inverse limit along `f` consumes in the
proofs of Stacks 0CMX and Stacks 0CMY.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_atlas_isLimitPreservingOnObjects_comp`.

## Implementation notes

The lifting property is
`AlgebraicGeometry.Stack.exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation`,
smooth morphisms of algebraic spaces being flat and locally of finite presentation. The composite
`a ≫ f` is locally of finite presentation by Stacks 0DNP and Stacks 06Q3, and representable by
algebraic spaces because its source is represented by a scheme and the diagonal of `𝒴` is
representable; so Stacks 06CX applies to it.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 06Q3](https://stacks.math.columbia.edu/tag/06Q3)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An atlas of `𝒳` lifting objects along single fppf morphisms, whose composite with a locally
finitely presented `f` is limit preserving on objects.** See the module documentation. -/
theorem exists_atlas_isLimitPreservingOnObjects_comp
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    ∃ (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (a : 𝒲 ⟶ 𝒳.val),
      (∀ (U : BigFppfOver B S hS) (y : 𝒳.val.val.p.Fiber U),
        ∃ (T : B.Schemes) (m : T ⟶ U.left), Flat (B.inclusion.map m) ∧
          LocallyOfFinitePresentation (B.inclusion.map m) ∧ Surjective (B.inclusion.map m) ∧
          ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor a).obj z ⟶ y.1),
            𝒳.val.val.p.IsHomLift
              (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ) ∧
      BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒲 𝒴.val (a ≫ f.hom) := by
  obtain ⟨_, _, _, U, a₀, hrep, ha⟩ := 𝒳.property
  let A : schemeStack.{u, w} B S hS U ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom a₀)
  have hAsm : IsSmooth B S hS A :=
    Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hrep
      (fun V y hy G hG he => (ha V y hy G hG he).2)
  have hg : IsLocallyOfFinitePresentation B S hS (A ≫ f) :=
    isLocallyOfFinitePresentation_comp B S hS A f
      (isLocallyOfFinitePresentation_of_isSmooth B S hS A hAsm) hf
  have hgrep : IsRepresentableByAlgebraicSpaces B S hS (A ≫ f).hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) (A ≫ f).hom
  refine ⟨schemeFibredCategory B S hS U, Bicategory.InducedBicategory.mkHom a₀, ?_,
    isLimitPreservingOnObjects_of_isRepresentable_of_isLocallyOfFinitePresentation B S hS
      (A ≫ f) hgrep hg⟩
  exact Stack.exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS
    (Bicategory.InducedBicategory.mkHom a₀) hrep fun V yv hyv F hF he =>
      ⟨(ha V yv hyv F hF he).1, Space.isFlat_of_isSmooth B S hS _ (ha V yv hyv F hF he).2,
        Space.isLocallyOfFinitePresentation_of_isSmooth B S hS (ha V yv hyv F hF he).2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
