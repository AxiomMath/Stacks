module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Contains
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.RestrictionDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Shrink
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ShrinkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesBaseChangeProj

/-!
# The relative homogeneous spectrum of Situation 0849 is an algebraic space

In Situation 0849 let `F` be the functor of quadruples of Stacks 084A. This file proves
Stacks 084B: `F` is an algebraic space; for every scheme point `g : Z → X` there is a canonical
cartesian square identifying `Z ×_X F` with `Proj_Z(g^*𝒜)`; and these identifications are
compatible with further base change `Z' → Z`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.quadrupleRestriction`: the restriction datum of
  Stacks 084A for the situation: the restrictions `f^*𝒜` to the scheme points and the
  comparisons between them.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`: the functor `F`.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjπ`: the morphism `F ⟶ X`.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`: the second assertion.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.isAlgebraicSpace_relativeProjFunctor`: the first
  assertion.
* `AlgebraicGeometry.Space.RelativeProjSituation.isPullback_projComparison`: the third assertion,
  with the comparison morphism identified with the base-change morphism of Tag 01O3.

## Implementation notes

The functor `F` is the functor of quadruples of Stacks 084A as the library constructs it for a
restriction datum, `AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleSpace`: its
value on a test object `T` is the limit, over the quasi-compact test objects `W ⟶ T`, of the
unions `AlgebraicGeometry.Space.GradedAlgebraPoints.F` of the classes of quadruples
`(d, f, ℒ, ψ)`, and on a quasi-compact `T` it is that union itself (`relativeProjFunctorEquivF`).
It is applied to the restriction datum of the situation, `quadrupleRestriction`.

The restrictions `g^*𝒜` to scheme points are sheaves of graded algebras on schemes, and the
inverse image of sheaves of graded algebras along a morphism of ringed topoi, like the relative
Proj of Stacks 01NQ, is available in the library only for algebras whose sections lie in the
universe `u` of the coefficient rings. The homogeneous sections of `𝒜` lie in an arbitrary
universe `m` and are bounded by the cutoff of the site, so `g^*𝒜` is taken to be the inverse image
of the re-presentation `AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebra` of `𝒜` with
sections in `u`, which is identified with `𝒜` degreewise and sectionwise, compatibly with
restriction, multiplication and unit
(`AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebraEquiv`).
When `m = u`, so that `g^*𝒜` itself is defined, it is isomorphic to the algebra used here, as a
sheaf of graded algebras: `AlgebraicGeometry.Space.RelativeProjSituation.shrinkPointAlgebraIso`.

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **The restriction datum of Stacks 084A for Situation 0849**: to a scheme point `f : T → X`
the restriction `f^*𝒜`, a quasi-coherent graded algebra on the scheme of `T`, and to a morphism
`τ : T' ⟶ T` of test objects the identification of `(f ∘ τ)^*𝒜` with `τ^*(f^*𝒜)`. -/
def quadrupleRestriction :
    GradedAlgebraRestriction
      (GradedAlgebraPoints.ofQuasicoherentFamily s.shrink.pointAlgebra) :=
  s.shrink.gradedAlgebraRestriction

/-- **The functor `F` of Stacks 084A** for Situation 0849: on a test object `T` the limit, over
the quasi-compact test objects `W ⟶ T`, of the unions `F(W)` of the classes of quadruples
`(d, f, ℒ, ψ)`, and on a quasi-compact `T` the union `F(T)` itself
(`relativeProjFunctorEquivF`). -/
def relativeProjFunctor : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u :=
  s.quadrupleRestriction.quadrupleSpace
    s.shrink.contains_relativeProj_pointAlgebra s.space.property.isSheaf

/-- **On a quasi-compact test object `T` the value of `F` is the set `F(T)` of Stacks 084A** of
classes of quadruples `(d, f, ℒ, ψ)`, `AlgebraicGeometry.Space.GradedAlgebraPoints.F`. -/
def relativeProjFunctorEquivF (T : BigFppfOver s.site s.base s.containsBase)
    (hT : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) :
    s.relativeProjFunctor.obj (op T) ≃
      (GradedAlgebraPoints.ofQuasicoherentFamily s.shrink.pointAlgebra).F T :=
  s.quadrupleRestriction.quadrupleSpaceEquivF
    s.shrink.contains_relativeProj_pointAlgebra s.space.property.isSheaf T hT

/-- **The morphism `F ⟶ X` of Stacks 084A**, sending a quadruple `(d, f, ℒ, ψ)` to `f`. -/
def relativeProjπ : s.relativeProjFunctor ⟶ s.space.1 :=
  s.quadrupleRestriction.quadrupleSpaceπ
    s.shrink.contains_relativeProj_pointAlgebra s.space.property.isSheaf

/-- **Stacks 084B, first assertion: the functor `F` of Stacks 084A is an algebraic space.** -/
@[stacks 084B "first assertion: the functor F of Tag 084A is an algebraic space"]
theorem isAlgebraicSpace_relativeProjFunctor :
    IsAlgebraicSpace s.site s.base s.containsBase s.relativeProjFunctor :=
  s.quadrupleRestriction.isAlgebraicSpace_quadrupleSpace
    s.shrink.contains_relativeProj_pointAlgebra s.space.property

/-- **Stacks 084B, second assertion: `Z ×_X F = Proj_Z(g^*𝒜)`.** For every scheme point
`g : Z → X` an object of the site whose scheme is the relative Proj of the restriction `g^*𝒜`
(`relativeProjPoints_algebra`), with a cartesian square identifying it with `Z ×_X F`.

The restriction `g^*𝒜` is that of the re-presentation of `𝒜` with sections in the universe `u`
(`smallAlgebra`, compared with `𝒜` by `smallAlgebraEquiv`); when the sections of `𝒜` already lie
in `u` it is isomorphic to the restriction of `𝒜` itself by `shrinkPointAlgebraIso`. -/
@[stacks 084B "second assertion: for every morphism g : Z -> X from a scheme of the site, a \
canonical isomorphism Proj_Z(g^*A) = Z x_X F, as a cartesian square"]
def relativeProjPoints : RelativeProjPoints s.site s.base s.containsBase s.relativeProjπ :=
  s.quadrupleRestriction.quadrupleRelativeProjPoints
    s.shrink.contains_relativeProj_pointAlgebra s.space.property.isSheaf

/-- The graded algebra of the second assertion at a scheme point `g` is the restriction `g^*𝒜`. -/
@[simp] theorem relativeProjPoints_algebra (T : BigFppfOver s.site s.base s.containsBase)
    (g : yoneda.obj T ⟶ s.space.1) :
    s.relativeProjPoints.algebra T g = s.shrink.pointAlgebra T g :=
  rfl

/-- **Stacks 084B, third assertion: compatibility with further base change.** For a morphism
`h : Z' ⟶ Z` of test objects and a scheme point `g : Z → X`, the comparison morphism
`Proj_{Z'}((g ∘ h)^*𝒜) ⟶ Proj_Z(g^*𝒜)` exhibits the source as `Z' ×_Z Proj_Z(g^*𝒜)`; it is
compatible with the identifications with `Z ×_X F` and `Z' ×_X F` of the second assertion; and
it is the canonical one: the identification `Proj_{Z'}((g ∘ h)^*𝒜) ≅ Proj_{Z'}(h^*(g^*𝒜))` of
the restricted algebras followed by the base-change morphism of Tag 01O3. -/
@[stacks 084B "third assertion: the identifications Proj_Z(g^*A) = Z x_X F are compatible with \
further base change Z' -> Z, through the canonical base-change morphism of Tag 01O3"]
theorem isPullback_projComparison {Z Z' : BigFppfOver s.site s.base s.containsBase}
    (g : yoneda.obj Z ⟶ s.space.1) (h : Z' ⟶ Z) :
    IsPullback (s.quadrupleRestriction.projComparison
      s.shrink.contains_relativeProj_pointAlgebra g h)
        (s.relativeProjPoints.fibreHom Z' (yoneda.map h ≫ g))
        (s.relativeProjPoints.fibreHom Z g) h ∧
      yoneda.map (s.quadrupleRestriction.projComparison
        s.shrink.contains_relativeProj_pointAlgebra g h) ≫
          s.relativeProjPoints.fibreToSpace Z g =
        s.relativeProjPoints.fibreToSpace Z' (yoneda.map h ≫ g) ∧
      (BigFppfOver.toScheme s.site s.base s.containsBase).map
          (s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra g h) =
        (s.quadrupleRestriction.restrictProjIso g h).hom ≫
          Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
            (s.shrink.pointAlgebra Z g)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map h) :=
  ⟨(s.quadrupleRestriction.isPullback_projComparison
    s.shrink.contains_relativeProj_pointAlgebra g h).1,
    s.quadrupleRestriction.projToQuadrupleSpace_comp
      s.shrink.contains_relativeProj_pointAlgebra s.space.property.isSheaf g h,
    s.quadrupleRestriction.toScheme_map_projComparison
      s.shrink.contains_relativeProj_pointAlgebra g h⟩

end RelativeProjSituation

end AlgebraicGeometry.Space

end
