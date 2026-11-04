module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise

/-!
# An equivalence over the site is a homeomorphism on points

An equivalence over the big fppf site of `S` between categories fibred in groupoids induces a
homeomorphism between their spaces of points `AlgebraicGeometry.Stack.points`, with the topology
`AlgebraicGeometry.Stack.pointTopology`. No algebraicity hypothesis is needed.

## Main definitions

* `AlgebraicGeometry.Stack.pointsHomeomorphOfBasedEquivalence`: the homeomorphism on points
  induced by an equivalence over the site.

## Main results

* `AlgebraicGeometry.Stack.isOpenMap_pointsMap_of_basedEquivalence` and
  `AlgebraicGeometry.Stack.isQuotientMap_pointsMap_of_basedEquivalence`: the map on points of an
  equivalence over the site is open and a quotient map.
* `AlgebraicGeometry.Stack.exists_basedEquivalence_functor_eq`: a based functor whose underlying
  functor is an equivalence is the forward 1-morphism of an equivalence over the site.
* `AlgebraicGeometry.Stack.isOpenMap_pointsMap_of_comp_isEquivalence` and
  `AlgebraicGeometry.Stack.isQuotientMap_pointsMap_of_comp_isEquivalence`: openness and the
  quotient-map condition on points transport along such an equivalence.

## References

* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- An equivalence over the big fppf site of `S` induces a homeomorphism on the topological
spaces of points. -/
noncomputable def pointsHomeomorphOfBasedEquivalence
    (e : BasedCategory.Equivalence 𝒜.val 𝒞.val) :
    @Homeomorph (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒞.val 𝒞.property)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞) :=
  letI := pointTopology B S hS 𝒜
  letI := pointTopology B S hS 𝒞
  { toEquiv := pointsEquivOfBasedEquivalence B S hS 𝒜.property 𝒞.property e
    continuous_toFun := continuous_pointsMap B S hS 𝒜 𝒞 e.functor
    continuous_invFun := continuous_pointsMap B S hS 𝒞 𝒜 e.inverse }

/-- The map on points of an equivalence over the site is an open map. -/
theorem isOpenMap_pointsMap_of_basedEquivalence (e : BasedCategory.Equivalence 𝒜.val 𝒞.val) :
    @IsOpenMap (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒞.val 𝒞.property)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property e.functor) :=
  let := pointTopology B S hS 𝒜
  let := pointTopology B S hS 𝒞
  Homeomorph.isOpenMap (pointsHomeomorphOfBasedEquivalence B S hS 𝒜 𝒞 e)

/-- The map on points of an equivalence over the site is a quotient map, i.e. submersive. -/
theorem isQuotientMap_pointsMap_of_basedEquivalence
    (e : BasedCategory.Equivalence 𝒜.val 𝒞.val) :
    @Topology.IsQuotientMap (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒞.val 𝒞.property)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property e.functor) :=
  let := pointTopology B S hS 𝒜
  let := pointTopology B S hS 𝒞
  Homeomorph.isQuotientMap (pointsHomeomorphOfBasedEquivalence B S hS 𝒜 𝒞 e)

/-- A based functor between two categories fibred in groupoids over the site whose underlying
functor is an equivalence of categories is the forward 1-morphism of an equivalence *over the
site*. -/
theorem exists_basedEquivalence_functor_eq (F : 𝒜.val ⥤ᵇ 𝒞.val)
    (hF : F.toFunctor.IsEquivalence) :
    ∃ e : BasedCategory.Equivalence 𝒜.val 𝒞.val, e.functor = F := by
  obtain ⟨G, hG, η, ε, hη, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    𝒜.val.p 𝒞.val.p 𝒜.property 𝒞.property F.toFunctor F.w hF
  exact ⟨{ functor := F
           inverse := ⟨G, hG⟩
           unitIso := BasedNatIso.mkNatIso η hη
           counitIso := BasedNatIso.mkNatIso ε hε }, rfl⟩

/-- The map on points of a based functor whose underlying functor is an equivalence of categories
is an open map. -/
theorem isOpenMap_pointsMap_of_isEquivalence (F : 𝒜.val ⥤ᵇ 𝒞.val)
    (hF : F.toFunctor.IsEquivalence) :
    @IsOpenMap (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒞.val 𝒞.property)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property F) := by
  obtain ⟨e, he⟩ := exists_basedEquivalence_functor_eq B S hS 𝒜 𝒞 F hF
  rw [← he]
  exact isOpenMap_pointsMap_of_basedEquivalence B S hS 𝒜 𝒞 e

/-- The map on points of a based functor whose underlying functor is an equivalence of categories
is a quotient map. -/
theorem isQuotientMap_pointsMap_of_isEquivalence (F : 𝒜.val ⥤ᵇ 𝒞.val)
    (hF : F.toFunctor.IsEquivalence) :
    @Topology.IsQuotientMap (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒞.val 𝒞.property)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property F) := by
  obtain ⟨e, he⟩ := exists_basedEquivalence_functor_eq B S hS 𝒜 𝒞 F hF
  rw [← he]
  exact isQuotientMap_pointsMap_of_basedEquivalence B S hS 𝒜 𝒞 e

section Transport

variable (𝒟 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- The map on points of a strictly commuting triangle of based functors is the composite of the
maps on points. -/
private theorem pointsMap_eq_comp_of_comp_eq
    (F : 𝒜.val ⥤ᵇ 𝒞.val) (a : 𝒜.val ⥤ᵇ 𝒟.val) (b : 𝒞.val ⥤ᵇ 𝒟.val) (hab : F.comp b = a) :
    pointsMap B S hS 𝒜.val 𝒜.property 𝒟.property a =
      (pointsMap B S hS 𝒞.val 𝒞.property 𝒟.property b) ∘
        (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property F) :=
  funext fun z => by rw [Function.comp_apply, pointsMap_comp, hab]

/-- Transport of openness on points along an equivalence over the site that commutes strictly
with two 1-morphisms to a common target. -/
theorem isOpenMap_pointsMap_of_comp_isEquivalence
    (F : 𝒜.val ⥤ᵇ 𝒞.val) (hF : F.toFunctor.IsEquivalence)
    (a : 𝒜.val ⥤ᵇ 𝒟.val) (b : 𝒞.val ⥤ᵇ 𝒟.val) (hab : F.comp b = a)
    (hb : @IsOpenMap (points B S hS 𝒞.val 𝒞.property) (points B S hS 𝒟.val 𝒟.property)
      (pointTopology B S hS 𝒞) (pointTopology B S hS 𝒟)
      (pointsMap B S hS 𝒞.val 𝒞.property 𝒟.property b)) :
    @IsOpenMap (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒟.val 𝒟.property)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒟)
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒟.property a) := by
  let _ := pointTopology B S hS 𝒜
  let _ := pointTopology B S hS 𝒞
  let _ := pointTopology B S hS 𝒟
  exact pointsMap_eq_comp_of_comp_eq B S hS 𝒜 𝒞 𝒟 F a b hab ▸
    hb.comp (isOpenMap_pointsMap_of_isEquivalence B S hS 𝒜 𝒞 F hF)

/-- Transport of the quotient-map condition on points along an equivalence over the site that
commutes strictly with two 1-morphisms to a common target. -/
theorem isQuotientMap_pointsMap_of_comp_isEquivalence
    (F : 𝒜.val ⥤ᵇ 𝒞.val) (hF : F.toFunctor.IsEquivalence)
    (a : 𝒜.val ⥤ᵇ 𝒟.val) (b : 𝒞.val ⥤ᵇ 𝒟.val) (hab : F.comp b = a)
    (hb : @Topology.IsQuotientMap (points B S hS 𝒞.val 𝒞.property)
      (points B S hS 𝒟.val 𝒟.property)
      (pointTopology B S hS 𝒞) (pointTopology B S hS 𝒟)
      (pointsMap B S hS 𝒞.val 𝒞.property 𝒟.property b)) :
    @Topology.IsQuotientMap (points B S hS 𝒜.val 𝒜.property)
      (points B S hS 𝒟.val 𝒟.property)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒟)
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒟.property a) := by
  let _ := pointTopology B S hS 𝒜
  let _ := pointTopology B S hS 𝒞
  let _ := pointTopology B S hS 𝒟
  exact pointsMap_eq_comp_of_comp_eq B S hS 𝒜 𝒞 𝒟 F a b hab ▸
    hb.comp (isQuotientMap_pointsMap_of_isEquivalence B S hS 𝒜 𝒞 F hF)

end Transport

end AlgebraicGeometry.Stack

end
