module

public import StacksFrontier.CategoryTheory.Triangulated.CoreflectiveExtBijective
public import StacksFrontier.Deformation.AlgebraExtension.PushoutEssSurj
public import StacksFrontier.Deformation.AlgebraExtension.PushoutFunctor

/-!
# Pushout of extensions along a map inverted by a coreflection of the derived category

Let `a : 𝒜 ⟶ 𝒪` be a morphism of sheaves of commutative rings on a small site, let `Pq` be a
shift-stable property of objects of `D(𝒪)` whose inclusion has a right adjoint `R`, and suppose
that `NL_{𝒪/𝒜}` satisfies `Pq`. If `φ : ℳ ⟶ 𝒩` is a morphism of `𝒪`-modules with `R(φ)` an
isomorphism, then pushout along `φ` is an equivalence between the categories of extensions of
`𝒜`-algebras of `𝒪` by `ℳ` and by `𝒩`.

This is the proof of [Stacks Project, Tag 0D3P] at the level of a site: there `Pq` is
`D_QCoh(𝒪_X)`, `R` is the derived coherator `DQ_X` of [Stacks Project, Tag 0CR4], and `NL_{X/B}`
lies in `D_QCoh(𝒪_X)` by [Stacks Project, Tag 0D0Y]. The source's proof: the maps
`Ext^i(NL, ℱ) ⟶ Ext^i(NL, 𝒢)` are isomorphisms, so the functor is fully faithful by
[Stacks Project, Tag 08UG] and essentially surjective by [Stacks Project, Tag 08UK].

## Main results

* `Deformation.AlgebraExtension.isEquivalence_pushoutFunctor_of_isIso_rightAdjoint_map`
* `Deformation.AlgebraExtension.IsPushoutFunctor.isEquivalence_of_isIso_rightAdjoint_map`

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.SheafOfModules (naiveCotangentComplex)

universe t u

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)} {φ : M ⟶ N}
  (Pq : ObjectProperty (DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))))
  [Pq.ι.IsLeftAdjoint] [Pq.IsStableUnderShift ℤ]

/-- **Pushout along `φ` is an equivalence when `R(φ)` is an isomorphism** and `NL_{𝒪/𝒜}` lies in
the coreflective subcategory, for any functor with the universal property of pushout. -/
theorem IsPushoutFunctor.isEquivalence_of_isIso_rightAdjoint_map
    {F : AlgebraExtension a M ⥤ AlgebraExtension a N} (hF : IsPushoutFunctor φ F)
    (hNL : Pq (DerivedCategory.Q.obj (naiveCotangentComplex.{u, u, u, u} J A O a)))
    [IsIso (Pq.ι.rightAdjoint.map ((DerivedCategory.singleFunctor _ 0).map (tensorMap φ)))] :
    F.IsEquivalence := by
  have h1 := Pq.bijective_comp_shift_map_of_isIso_rightAdjoint_map hNL
    ((DerivedCategory.singleFunctor _ 0).map (tensorMap φ)) 1
  exact hF.isEquivalence (Pq.bijective_comp_of_isIso_rightAdjoint_map hNL _) h1

/-- **[Stacks Project, Tag 0D3P] at the level of a site**: the pushout functor along `φ` is an
equivalence when `R(φ)` is an isomorphism and `NL_{𝒪/𝒜}` lies in the coreflective
subcategory. -/
theorem isEquivalence_pushoutFunctor_of_isIso_rightAdjoint_map
    (hNL : Pq (DerivedCategory.Q.obj (naiveCotangentComplex.{u, u, u, u} J A O a)))
    [IsIso (Pq.ι.rightAdjoint.map ((DerivedCategory.singleFunctor _ 0).map (tensorMap φ)))] :
    (pushoutFunctor a φ).IsEquivalence :=
  (isPushoutFunctor_pushoutFunctor a φ).isEquivalence_of_isIso_rightAdjoint_map Pq hNL

end Deformation.AlgebraExtension

end
