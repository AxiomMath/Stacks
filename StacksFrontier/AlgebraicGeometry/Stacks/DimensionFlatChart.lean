module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# The dimension of an algebraic stack read off a flat chart of constant relative dimension

Let `𝒳` be a locally Noetherian algebraic stack and let `f : X ⟶ 𝒳` be a 1-morphism from a
locally Noetherian algebraic space which is flat and locally of finite type, of relative dimension
`e` (Stacks 0DRG) at every point of `X`. Then at every point `t` of `X` above `x ∈ |𝒳|` the
dimension of Stacks 0AFN is `dim_x(𝒳) = dim_t(X) - e`. The chart need not be smooth: this is what
computes the dimension of a quotient stack `[X/G]` by a group `G` which is flat but not smooth,
through the atlas `X ⟶ [X/G]`.

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isFlat`: the pointwise
  formula.

## Implementation notes

The proof is that of Stacks 0AFM with one of its two charts only flat. Take a smooth chart
`a : T ⟶ 𝒳` through `x`, of relative dimension `d` at a point `u` above `x`, so that
`dim_x(𝒳) = dim_u(T) - d` by Stacks 0DRJ. The 2-fibre product `P = T ×_𝒳 X` is an algebraic space
with a point `z` above `u` and `t`. Its projection to `X` is smooth, a base change of `a`, of
relative dimension `d` at `z`, so `dim_z(P) = dim_t(X) + d` by Stacks 0AFI. Its projection to `T`
is flat and locally of finite type, a base change of `f`, of relative dimension `e` at every point
by base change of the relative dimension of Stacks 0DRG, so `dim_z(P) = dim_u(T) + e` by
Stacks 0AFE. Hence `dim_u(T) - d = dim_t(X) - e`.

## References

* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFE](https://stacks.math.columbia.edu/tag/0AFE)
* [Stacks Project, Tag 0AFI](https://stacks.math.columbia.edu/tag/0AFI)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The dimension of an algebraic stack at a point, read off a flat chart.** Let `𝒳` be a
locally Noetherian algebraic stack over `S` and let `f : X ⟶ 𝒳` be flat and locally of finite
type from a locally Noetherian algebraic space, of relative dimension `e` (Stacks 0DRG) at every
point of `X`. Then `dim_x(𝒳) = dim_t(X) - e` at every point `t ∈ |X|` above `x`. -/
theorem dimensionAtPoint_eq_dimensionSubNat_of_isFlat
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hNX : Space.HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (f : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (e : ℕ) (he : ∀ t : Space.points B S hS X,
      relativeDimensionAt.{u, w} B S hS X hX 𝒳 f hf t = (e : WithBot ℕ∞))
    (t : Space.points B S hS X)
    (ht : pointsMap B S hS (fibredCategory B S hS X).val
      (fibredCategory B S hS X).property 𝒳.val.property f.hom.hom
      (stackPointOfSpacePoint B S hS X t) = x) :
    dimensionAtPoint B S hS 𝒳 h𝒳 x =
      dimensionSubNat (Space.dimensionAtPoint B S hS X hX t) e := by
  classical
  obtain ⟨T, hT, a, hasm, u, hu⟩ := exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w}
    B S hS 𝒳 x
  have haft := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a hasm
  obtain ⟨dT, hdT⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS T hT 𝒳 a haft u
  rw [dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 x hT a hasm haft u hu
    dT hdT]
  have hNT := hasEtaleLocalProperty_isLocallyNoetherian_of_chart.{u, w} B S hS 𝒳 h𝒳 hT a haft
  have hTrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT
  have hXrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS X hX
  let Q := twoFibreProductSquareAlgebraicStacks B S hS a f
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks.{u, w} B S hS a f
  have hQc : Bicategory.IsTwoFibreProduct Q.underlying :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      a.hom f.hom
  have hQpt : IsRepresentableByAlgebraicSpace B S hS Q.underlying.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS X) 𝒳.val (fibredCategory B S hS T) f.hom a.hom _ hQc
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hXrep
        f.hom)
      hTrep
  obtain ⟨P, hP, ⟨eP⟩⟩ := id hQpt
  let pr (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : Q.underlying.pt ⟶ fibredCategory B S hS Y) :=
    representingMap B S hS Q.underlying.pt (fibredCategory B S hS Y) P Y eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) g
  let prT := pr T Q.underlying.fst
  let prX := pr X Q.underlying.snd
  have hflatT :=
    isFlat_representingMap_of_isFlat.{u, w} B S hS P T hP hT eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst
      (AlgebraicStacks.isFlat_baseChange B S hS f a Q hQ hflat)
  have hftT :=
    isLocallyOfFiniteType_representingMap.{u, w} B S hS P T hP hT eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst
      (AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f a Q hQ hf)
  have hsmX :=
    isSmooth_representingMap_of_isSmooth.{u, w} B S hS
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) P X hP hX eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd
      (AlgebraicStacks.isSmooth_baseChange B S hS a f Q.swap
        (Bicategory.isTwoFibreProduct_swap hQ) hasm)
  have hftX := Space.isLocallyOfFiniteType_of_isSmooth B S hS hsmX
  have hNP := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hP hX _ hftX hNX
  have hpt : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (g : Q.underlying.pt ⟶ fibredCategory B S hS Y) (w : Space.points B S hS P),
      pointsMap B S hS _ _ (fibredCategory B S hS Y).property g.hom
          (spacePointMap B S hS P _ (representingEquivalence B S hS P _ eP).functor w) =
        stackPointOfSpacePoint B S hS Y (Space.pointsMap B S hS P (pr Y g) w) := fun Y g w =>
    (spacePointMap_representing_naturality B S hS P Y Q.underlying.pt
      (fibredCategory B S hS Y) eP (StacksRepresentableCFG.EquivalenceOver.refl _) g w).symm
  have hrelT : ∀ w : Space.points B S hS P, Space.HasRelativeDimensionAt (e : ℕ∞) B S hS prT w := by
    intro w
    obtain ⟨p', q', -, hq', hval⟩ := exists_eq_fieldFibreDimensionAt B S hS X hX 𝒳 f hf
      (Space.pointsMap B S hS P prX w)
    exact hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt.{u, w} B S hS a f
      hXrep hf hQc hQpt T P hT hP (StacksRepresentableCFG.EquivalenceOver.refl _) eP hftT rfl _ w
      rfl p' q' (hq'.trans (hpt X Q.underlying.snd w).symm) (e : ℕ∞) (by rw [← hval, he]; rfl)
  obtain ⟨ζ, hζ, hζ'⟩ := exists_point_of_isTwoFibreProduct B S hS Q.underlying hQc
    (stackPointOfSpacePoint B S hS T u) (stackPointOfSpacePoint B S hS X t) (hu.trans ht.symm)
  obtain ⟨z, hz⟩ := (bijective_spacePointMap_representing B S hS P Q.underlying.pt eP).surjective ζ
  have hz_eq : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (g : Q.underlying.pt ⟶ fibredCategory B S hS Y) (v : Space.points B S hS Y),
      pointsMap B S hS _ _ (fibredCategory B S hS Y).property g.hom ζ =
        stackPointOfSpacePoint B S hS Y v → Space.pointsMap B S hS P (pr Y g) z = v :=
    fun Y g v h => (bijective_spacePointMap_representing B S hS Y (fibredCategory B S hS Y)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).injective
      ((hpt Y g z).symm.trans (by rw [hz, h]; rfl))
  obtain ⟨p, q, -, hq, hvald⟩ := exists_eq_fieldFibreDimensionAt B S hS T hT 𝒳 a haft u
  have hrelX : Space.HasRelativeDimensionAt (dT : ℕ∞) B S hS prX z :=
    hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt.{u, w} B S hS f a
      hTrep haft (Q := Q.underlying.swap) (Bicategory.isTwoFibreProduct_swap hQc) hQpt X P hX hP
      (StacksRepresentableCFG.EquivalenceOver.refl _) eP hftX rfl ζ z hz p q
      (hq.trans hζ.symm)
      (dT : ℕ∞) (by rw [← hvald, hdT]; rfl)
  have heq₁ := Space.dimensionAtPoint_eq_add_of_isFlat B S hS hP hT hNT prT hflatT hftT hrelT z
  have heq₂ := Space.dimensionAtPoint_eq_add_of_isSmooth B S hS hP hX hNP hNX prX hsmX z hrelX
  rw [hz_eq T _ u hζ] at heq₁
  rw [hz_eq X _ t hζ'] at heq₂
  exact dimensionSubNat_eq_dimensionSubNat_of_add_eq
    (Space.dimensionAtPoint_ne_bot B S hS T hT u)
    (Space.dimensionAtPoint_ne_bot B S hS X hX t) (heq₁.symm.trans heq₂)

end AlgebraicGeometry.Stack

end
