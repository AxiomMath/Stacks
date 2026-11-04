module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint

/-!
# Finiteness of the relative dimension at a point

The relative dimension of Stacks 04NM of a morphism of algebraic spaces at a point of the
source is, a priori, an element of `ℕ∞`, and the relative dimension of Stacks 0DRG of a
1-morphism from an algebraic space to an algebraic stack is an element of `WithBot ℕ∞`. For a
morphism locally of finite type both are natural numbers: the fibre through the point is a
scheme locally of finite type over a field, and such a scheme has finite local dimension at
each of its points, being covered by spectra of finitely generated algebras over that field.

Consequently the two formulas that subtract such a relative dimension — Stacks 0AFM, the
independence of the chart in the formula of Stacks 0AFN, and Stacks 0DRJ, its identification with
the dimension of the stack — hold with no finiteness assumption on the value they subtract.

## Main results

* `AlgebraicGeometry.Space.exists_hasRelativeDimensionAt_natCast`: a morphism of algebraic
  spaces locally of finite type has a natural-number relative dimension at every point of its
  source.
* `AlgebraicGeometry.Stack.exists_relativeDimensionAt_eq_natCast`: the relative dimension of
  Stacks 0DRG of a 1-morphism locally of finite type from an algebraic space to an algebraic
  stack is a natural number at every point of its source.
* `AlgebraicGeometry.Stack.exists_dimensionSubNat_eq_dimensionSubNat_of_isSmooth`: the value of
  the formula of Stacks 0AFN is independent of the smooth chart and of the point above `x` at
  which it is read, the relative dimension it subtracts being produced rather than assumed to be a
  natural number.
* `AlgebraicGeometry.Stack.exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`: the
  dimension formula of Stacks 0DRJ with the relative dimension it subtracts produced rather
  than assumed to be a natural number.

## References

* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A morphism of algebraic spaces locally of finite type has a natural-number relative
dimension at each point of its source.** -/
theorem exists_hasRelativeDimensionAt_natCast (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f)
    (x : points B S hS F) :
    ∃ d : ℕ, HasRelativeDimensionAt (d : ℕ∞) B S hS f x := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hF hG f x
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) :=
    hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  obtain ⟨n, hn⟩ := exists_topologicalKrullDimAt_fiber_eq_nat
    ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)
  refine ⟨n, (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@HasFiberDimensionAt.{u} _)
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget _) f x c).2 ?_⟩
  rw [hasFiberDimensionAt_ofSchemeHom_iff, hn]
  rfl

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relative dimension of Stacks 0DRG is a natural number.** For a 1-morphism
`f : T ⟶ 𝒳` locally of finite type from an algebraic space to an algebraic stack and a point
`t ∈ |T|`, the value `dim_t(T_x)` is finite. -/
@[stacks 0DRJ "finiteness of the relative dimension"]
theorem exists_relativeDimensionAt_eq_natCast
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : Space.points B S hS T) :
    ∃ d : ℕ, relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞) := by
  classical
  obtain ⟨p, q, -, -, hval⟩ := exists_eq_fieldFibreDimensionAt B S hS T hT 𝒳 f hf t
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS
    f.hom 𝒳.property (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) p
  obtain ⟨x, hx⟩ := (bijective_spacePointMap_representing B S hS W
    (fieldFibreSquare B S hS f.hom p).pt eW).surjective q
  have hdim : fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) p q =
      Space.dimensionAtPoint B S hS W hW x := by
    rw [← hx]
    exact fieldFibreDimensionAt_eq_dimensionAtPoint.{u, w} B S hS _ _ _ p W hW eW x
  have hgft : Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS (fieldFibreSquare B S hS f.hom p).pt
        (schemeFibredCategory B S hS p.base) W (yoneda.obj p.base) eW
        (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
        (fieldFibreSquare B S hS f.hom p).snd) :=
    isLocallyOfFiniteType_representingMap_fieldFibreSquare_snd.{u, w} B S hS f hf p
      W (yoneda.obj p.base) hW (isAlgebraicSpace_yoneda B S hS p.base) eW
      (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
  obtain ⟨d, hd⟩ := Space.exists_hasRelativeDimensionAt_natCast B S hS hW
    (isAlgebraicSpace_yoneda B S hS p.base) _ hgft x
  refine ⟨d, ?_⟩
  rw [hval, hdim]
  refine (dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback B S hS p
    IsPullback.of_id_snd hW hW (isAlgebraicSpace_yoneda B S hS p.base) hgft x d).mpr ?_
  simpa using hd

/-- Let `𝒳` be a locally Noetherian algebraic stack over `S`, let `f : T ⟶ 𝒳` and
`f' : T' ⟶ 𝒳` be smooth, locally-of-finite-type 1-morphisms from algebraic spaces, and let
`t ∈ |T|` and `t' ∈ |T'|` have the same image `x ∈ |𝒳|`. Then the relative dimensions of
Stacks 0DRG of `f` at `t` and of `f'` at `t'` are natural numbers `d` and `d'`, and the two values
of the formula of Stacks 0AFN agree: `dim_t(T) - d = dim_{t'}(T') - d'` in `ℤ ∪ {±∞}`.

So the quantity `dim_u(U) - dim_{e(u)}(R_u)` of the source is defined — its subtrahend is
finite — and does not depend on the presentation or on the point above `x` used to read it.
A presentation `[U/R] → 𝒳` enters through the smooth, locally of finite type 1-morphism
`U ⟶ 𝒳` it induces: the fibre `R_u` of the source map `s : R = U ×_𝒳 U ⟶ U` at the identity
arrow `e(u)` is the fibre of that 1-morphism over a field-valued point representing `x`, so its
local dimension there is the relative dimension of Stacks 0DRG subtracted here. -/
@[stacks 0AFM]
theorem exists_dimensionSubNat_eq_dimensionSubNat_of_isSmooth
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hT' : IsAlgebraicSpace B S hS T')
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (f' : algebraicSpaceStack.{u, w} B S hS T' hT' ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f) (hsm' : AlgebraicStacks.IsSmooth B S hS f')
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hf' : AlgebraicStacks.IsLocallyOfFiniteType B S hS f')
    (t : Space.points B S hS T) (t' : Space.points B S hS T')
    (hx : pointsMap B S hS (fibredCategory B S hS T).val
        (fibredCategory B S hS T).property 𝒳.val.property f.hom.hom
        (stackPointOfSpacePoint B S hS T t) =
      pointsMap B S hS (fibredCategory B S hS T').val
        (fibredCategory B S hS T').property 𝒳.val.property f'.hom.hom
        (stackPointOfSpacePoint B S hS T' t')) :
    ∃ d d' : ℕ, relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞) ∧
      relativeDimensionAt.{u, w} B S hS T' hT' 𝒳 f' hf' t' = (d' : WithBot ℕ∞) ∧
        dimensionSubNat (Space.dimensionAtPoint B S hS T hT t) d =
          dimensionSubNat (Space.dimensionAtPoint B S hS T' hT' t') d' := by
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS T hT 𝒳 f hf t
  obtain ⟨d', hd'⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS T' hT' 𝒳 f' hf' t'
  exact ⟨d, d', hd, hd', dimensionSubNat_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳
    hT hT' f f' hsm hsm' hf hf' t t' hx d d' hd hd'⟩

/-- **The dimension formula of Stacks 0DRJ, with the relative dimension produced.** For a
smooth, locally-of-finite-type 1-morphism `f : T ⟶ 𝒳` from an algebraic space to a locally
Noetherian algebraic stack and a point `t ∈ |T|` above `x`, the relative dimension of
Stacks 0DRG of `f` at `t` is a natural number `d` and `dim_x(𝒳) = dim_t(T) - d`. -/
theorem exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : Space.points B S hS T)
    (ht : pointsMap B S hS (fibredCategory B S hS T).val
      (fibredCategory B S hS T).property 𝒳.val.property f.hom.hom
      (stackPointOfSpacePoint B S hS T t) = x) :
    ∃ d : ℕ, relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞) ∧
      dimensionAtPoint B S hS 𝒳 h𝒳 x =
        dimensionSubNat (Space.dimensionAtPoint B S hS T hT t) d := by
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS T hT 𝒳 f hf t
  exact ⟨d, hd, dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 x hT f
    hsm hf t ht d hd⟩

end Stack

end AlgebraicGeometry

end
