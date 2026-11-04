module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbertRelativeRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalFamilyNormalisation

/-!
# Two of the three steps of Stacks 05YH

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. Stacks 05YH asserts that the 1-morphism
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD — which is
`AlgebraicGeometry.Stack.forgetToProduct` — is representable by algebraic spaces as soon as the
diagonal `𝒴 ⟶ 𝒴 × 𝒴` is representable by algebraic spaces.

The source's proof unwinds the fibre over a scheme-valued point of the target. Such a point over
`U` is, up to 2-isomorphism, an object of `ℋ_d(𝒳) × 𝒴`: a degree-`d` finite locally free cover
`q : Z ⟶ U`, an object `x` of `𝒳` over `Z`, and an object `y` of `𝒴` over `U`. An object of the
fibre over `U' ⟶ U` is an object of `ℋ_d(𝒳/𝒴)` restricting to that point, that is a choice of
identification of `F x` with `y|_Z` after base change to `Z ×_U U'` — in other words a section
over `U'` of `I ⟶ Z`, where `I = Isom_𝒴(y|_Z, F x)`. So the fibre is the restriction of scalars
`Res_{Z/U}(I)`, which is an algebraic space by Stacks 05YF because `I` is one (Stacks 045G, from
the hypothesis on the diagonal) and `Z ⟶ U` is finite locally free.

This file performs two of the three steps of that proof. It does **not** perform the fibre
identification, and so it does **not** prove Stacks 05YH; see below.

## Main definitions

Nothing new: the 1-morphism of Equation 05WD, the product it lands in and the statement of the
conclusion of Stacks 05YH all live in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductMorphism`.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_universalFamilies_product`: the
  2-Yoneda normalisation of a scheme-valued point of the product `ℋ_d(𝒳) × 𝒴`, which is
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_objUniversalFamilies` read at the
  fibredness witness
  `AlgebraicGeometry.Stack.isFiberedInGroupoids_absoluteHilbertTargetProductProjection`.
* `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_restrictionOfScalars_isomPresheaf`: the
  candidate representing object of the fibre is an algebraic space — for an object
  `P = (q : Z ⟶ U, x)` of `ℋ_d(𝒳)` and an object `y` of `𝒴` over `U`, there are a restriction
  `y|_Z` of `y` along `q` and an algebraic space `I` over `Z` representing
  `Isom_𝒴(y|_Z, F x)`, and the restriction of scalars of `I` along `q` is an algebraic space
  over `U`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpacesForgetToProduct_of_fibres`: the
  conclusion of Stacks 05YH follows from the fibre identification alone.

## What of Stacks 05YH is and is not proved

Proved: the normalisation step, in full, and the production of the candidate representing object
of the fibre, Stacks 05YF entering as
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree` exactly as in the
companion tag Stacks 05YJ. The hypothesis of Stacks 05YH on the diagonal of `𝒴`
is used where the source uses it, namely to produce `I`: it passes through
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_isomPresheaf_cover`, hence through Stacks 045G.

**Not proved: Stacks 05YH itself.** No declaration here carries its tag. What is missing is one
named statement, the *fibre identification*:

> `AlgebraicGeometry.Stack.FibresOverObjUniversalFamiliesAlgebraic`
> `AlgebraicGeometry.Stack.isFiberedInGroupoids_absoluteHilbertTargetProductProjection`
> `AlgebraicGeometry.Stack.forgetToProduct`,

that is: for every object `X` of `ℋ_d(𝒳) × 𝒴`, the first projection of the 2-fibre product of
`AlgebraicGeometry.Stack.forgetToProduct` with the 2-Yoneda point
`AlgebraicGeometry.Stack.objUniversalFamily` of `X` is equivalent, over the big fppf site of the
base of `X`, to the category of elements of an algebraic space. Once that is available,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpacesForgetToProduct_of_fibres` turns it
into the conclusion of Stacks 05YH immediately, and
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_restrictionOfScalars_isomPresheaf` supplies the
algebraic space it needs.

The identification itself is the analogue, for this 1-morphism, of
`AlgebraicGeometry.Stack.FiniteHilbert.Object.nonempty_equivalenceOver_sectionSpace` in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FibreSectionSpace`, which is the same
statement for the 1-morphism of Stacks 05XN; it is a construction of an equivalence of
categories over the site and is the bulk of the work. It must not be carried as a hypothesis: a
hypothesis identifying every fibre with a restriction of scalars, together with Stacks 05YF, is
jointly equivalent to the conclusion of Stacks 05YH, and would leave the hypothesis on the
diagonal unused.

## Implementation notes

`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_restrictionOfScalars_isomPresheaf` is stated
for an object of `ℋ_d(𝒳)` together with an object of `𝒴` over its base, rather than for an
object of the product `ℋ_d(𝒳) × 𝒴`: an object of the product carries its base as a separate
field, together with equalities identifying it with the bases of the two components, and every
statement made at it would have to transport along those equalities.

The restriction `y|_Z` is produced by the fibredness of `𝒴` and returned as an actual morphism
over `q`, not as an object of the fibre over `Z` chosen from an existence statement: that is
what makes it a restriction of `y` rather than an arbitrary object over the cover, and
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_isomPresheaf_cover` takes it in that shape.

The presentation `w` of the relocalized Isom space over the cover is not quantified over here:
it is the structural morphism `CategoryTheory.OverShriek.relocalizeToYoneda`, exactly as in the
proof of Stacks 05YJ.

## References

* [Stacks Project, Tag 02Y4](https://stacks.math.columbia.edu/tag/02Y4)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 05YH](https://stacks.math.columbia.edu/tag/05YH)
* [Stacks Project, Tag 05YJ](https://stacks.math.columbia.edu/tag/05YJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w v₂ u₂ a₁ b₁

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] BasedCategory.ofFunctor absoluteHilbertTargetProduct
  finiteHilbertCategory absoluteHilbertCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- **The 2-Yoneda normalisation of a scheme-valued point of the product `ℋ_d(𝒳) × 𝒴`.** A
1-morphism into `ℋ_d(𝒳) × 𝒴` whose 2-fibre product with the 2-Yoneda point of every *object* of
the product is representable by an algebraic space is representable by algebraic spaces in the
sense of Stacks 02ZW.

This is `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_objUniversalFamilies` read
at the fibredness witness
`AlgebraicGeometry.Stack.isFiberedInGroupoids_absoluteHilbertTargetProductProjection`. -/
theorem isRepresentableByAlgebraicSpaces_of_universalFamilies_product
    {𝒵 : BasedCategory.{a₁, b₁} (BigFppfOver B S hS)}
    (g : 𝒵 ⥤ᵇ absoluteHilbertTargetProduct
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴))
    (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    (hfam : FibresOverObjUniversalFamiliesAlgebraic
      isFiberedInGroupoids_absoluteHilbertTargetProductProjection g) :
    IsRepresentableByAlgebraicSpaces B S hS g :=
  isRepresentableByAlgebraicSpaces_of_objUniversalFamilies g h𝒵 _ hfam

/-- **The candidate representing object of the fibre of Stacks 05YH is an algebraic space.** Let
`P = (q : Z ⟶ U, x)` be an object of `ℋ_d(𝒳)` and let `y` be an object of `𝒴` over the base `U`;
together they are an object of `ℋ_d(𝒳) × 𝒴`. If the diagonal of `𝒴` is representable by
algebraic spaces then there are a restriction `y|_Z` of `y` along the cover and an algebraic
space `I` over `Z` representing `Isom_𝒴(y|_Z, F x)`, and the restriction of scalars of `I` along
`q` — the space of sections over `U` of the relocalization of `I` — is an algebraic space over
`U`.

The hypothesis on the diagonal enters through
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_isomPresheaf_cover`, hence through Stacks 045G;
Stacks 05YF is `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree`. The
restriction `y|_Z` is a genuine morphism over `q`, produced by the fibredness of `𝒴`. -/
theorem exists_isAlgebraicSpace_restrictionOfScalars_isomPresheaf
    [𝒴.toBasedCategory.p.IsFibered]
    (hΔ : HasRepresentableDiagonal B S hS (targetCFG (𝒴 := 𝒴)))
    (P : AbsoluteHilbert.Object B S hS d 𝒳) (y : 𝒴.toBasedCategory.obj)
    (hy : 𝒴.toBasedCategory.p.obj y = P.U) :
    ∃ (yZ : 𝒴.toBasedCategory.obj) (φ : yZ ⟶ y),
      𝒴.toBasedCategory.p.IsHomLift P.q φ ∧
      ∃ (hyZ : 𝒴.toBasedCategory.p.obj yZ = P.Z)
        (I : (BigFppfOver B P.Z.left.1 P.Z.left.2)ᵒᵖ ⥤ Type u),
        IsAlgebraicSpace B P.Z.left.1 P.Z.left.2 I ∧
        Nonempty (I ⋙ uliftFunctor.{v₂, u} ≅
          ((Over.iteratedSliceBackward P.Z).op ⋙ 𝒴.toBasedCategory.p.isomPresheaf
              (Functor.Fiber.mk hyZ)
              (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P))) ⋙
            uliftFunctor.{u, v₂}) ∧
        IsAlgebraicSpace B P.U.left.1 P.U.left.2
          (Space.sectionSpace B P.U.left.1 P.U.left.2 (Over.mk P.q.left)
            ((OverShriek.relocalizePresheafFunctor P.q.left).obj I)
            (OverShriek.relocalizeToYoneda P.q.left I)) := by
  obtain ⟨yZ, φ, hφ⟩ :=
    𝒴.isStackInGroupoids.isFiberedInGroupoids.exists_lift P.q y hy
  have hyZ := IsHomLift.domain_eq 𝒴.toBasedCategory.p P.q φ
  obtain ⟨I, hI, hiso⟩ := exists_isAlgebraicSpace_isomPresheaf_cover (F := F) hΔ P yZ hyZ
  have : Stacks.Morphisms.IsFiniteLocallyFree (B.inclusion.map (Over.mk P.q.left).hom) :=
    @Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ d P.finiteLocallyFree
  exact ⟨yZ, φ, hφ, hyZ, I, hI, hiso,
    Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree (Over.mk P.q.left)
      (isAlgebraicSpace_viewOver B P.Z.left.1 P.U.left.1 P.Z.left.2 P.U.left.2 P.q.left I hI) _⟩

/-- **The conclusion of Stacks 05YH follows from the fibre identification alone.** If the
2-fibre product of the 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD with the 2-Yoneda
point of every object of `ℋ_d(𝒳) × 𝒴` is representable by an algebraic space, then that
1-morphism is representable by algebraic spaces in the sense of Stacks 02ZW.

This records the exact remaining gap in the proof of Stacks 05YH: its hypothesis is the fibre
identification, and nothing else is missing. The hypothesis is **not** a legitimate carried
input — together with Stacks 05YF it is jointly equivalent to the conclusion of Stacks 05YH and
leaves the hypothesis of Stacks 05YH on the diagonal of `𝒴` unused — which is why this statement
carries no tag. -/
theorem isRepresentableByAlgebraicSpacesForgetToProduct_of_fibres
    (hfam : FibresOverObjUniversalFamiliesAlgebraic
      (isFiberedInGroupoids_absoluteHilbertTargetProductProjection
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴))
      (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F))) :
    IsRepresentableByAlgebraicSpacesForgetToProduct
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) :=
  isRepresentableByAlgebraicSpaces_of_universalFamilies_product _
    isFiberedInGroupoids_finiteHilbertProjection hfam

end AlgebraicGeometry.Stack

end
