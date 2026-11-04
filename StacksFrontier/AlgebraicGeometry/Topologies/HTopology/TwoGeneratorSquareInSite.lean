module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorConditions
public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite

/-!
# Objects of the big h category over a scheme, and the two-generator square among them

The induction of Stacks 0EVI replaces an affine object `X = Spec A` of the big h site by the
square of Example 0EVH over it, whose modification is `Proj (A[T₀,T₁]/(f₂T₀ - f₁T₁))`.  Both
steps need to know that the schemes produced are again objects of the site, which for the big h
site means that their size is below the site's cutoff.

This file supplies the two things the h site lacks for that: the constructor turning a scheme
below the cutoff with a morphism to the base into an object of the big h category over the base,
together with the matching constructor for morphisms, and the cutoff bound for the modification
of the square of Example 0EVH.

## Main definitions

* `AlgebraicGeometry.BigHOver.mk` and `AlgebraicGeometry.BigHOver.homMk`: objects and morphisms
  of the big h category over `S` from schemes and morphisms over `S`.

## Main results

* `AlgebraicGeometry.Scheme.size_proj_modificationGrading_lt`: the modification of the square of
  Example 0EVH is below every cutoff the base is below.

## Implementation notes

The cutoff bound is the general bound for a morphism of finite type, Stacks 000R (5),
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`, applied to
`Stacks.AlmostBlowUp.modificationToBase`: that morphism is of finite presentation by
`Stacks.AlmostBlowUp.finitePresentation_modificationToBase`, hence locally of finite type and
quasi-compact.  No property of `Proj` itself is needed, exactly as for affine space over an
object of a big site.

The object constructor mirrors `AlgebraicGeometry.BigFppfOver.mk` for the big fppf site; the big
h site had no analogue.

## References

* [Stacks Project, Tag 0EU1](https://stacks.math.columbia.edu/tag/0EU1)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Objects and morphisms of the big h category over a scheme -/

/-- A scheme contained in a big h site, together with a morphism to `S`, regarded as an object of
the big h category over `S`. -/
public def BigHOver.mk {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S) : BigHOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj Y hY) (Y := B.obj S hS) p)

/-- The underlying scheme of `AlgebraicGeometry.BigHOver.mk` is the given scheme. -/
public theorem BigHOver.toScheme_obj_mk {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S) :
    (BigHOver.toScheme B S hS).obj (BigHOver.mk B S hS hY p) = Y :=
  rfl

/-- A morphism of schemes over `S` into a scheme contained in a big h site, regarded as a
morphism of the big h category over `S`. -/
public def BigHOver.homMk {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S)
    {T : BigHOver B S hS} (h : (BigHOver.toScheme B S hS).obj T ⟶ Y)
    (w : h ≫ p = B.inclusion.map T.hom) : T ⟶ BigHOver.mk B S hS hY p :=
  Over.homMk (ObjectProperty.homMk h) (by apply ObjectProperty.hom_ext; exact w)

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigHOver.homMk` is the given
morphism. -/
public theorem BigHOver.toScheme_map_homMk {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S)
    {T : BigHOver B S hS} (h : (BigHOver.toScheme B S hS).obj T ⟶ Y)
    (w : h ≫ p = B.inclusion.map T.hom) :
    (BigHOver.toScheme B S hS).map (BigHOver.homMk B S hS hY p h w) = h :=
  rfl

/-! ### The modification of the square of Example 0EVH is below the cutoff -/

/-- **The modification of the square of Example 0EVH lies in every big site its base lies in.**
The projective hypersurface `Proj (A[T₀,T₁]/(f₂T₀ - f₁T₁))` has size below `κ` as soon as
`Spec A` does.

Its structure morphism to `Spec A` is of finite presentation, hence locally of finite type and
quasi-compact, so this is Stacks 000R (5). -/
public theorem Scheme.size_proj_modificationGrading_lt {κ : Cardinal.{u}} (A : Type u)
    [CommRing A] (f₁ f₂ : A) (hA : (Spec (CommRingCat.of A)).size < κ) :
    letI := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
    (AlgebraicGeometry.Proj (Stacks.AlmostBlowUp.modificationGrading A f₁ f₂)).size < κ := by
  let := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
  have hfp := Stacks.AlmostBlowUp.finitePresentation_modificationToBase A f₁ f₂
  let : LocallyOfFinitePresentation (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) :=
    hfp.locallyOfFinitePresentation
  let : QuasiCompact (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) := hfp.quasiCompact
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) hA

end AlgebraicGeometry

end
