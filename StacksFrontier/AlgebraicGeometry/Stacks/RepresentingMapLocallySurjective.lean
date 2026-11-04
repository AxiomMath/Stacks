module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProduct

/-!
# Local surjectivity of the induced morphism of representing presheaves

Let `𝒳` and `𝒴` be categories fibred in groupoids over the big fppf site of `S`, represented by
presheaves `F` and `G` through chosen equivalences over the site, and let `f : 𝒳 ⟶ 𝒴` be a
1-morphism. The morphism `F ⟶ G` of the representing presheaves
(`AlgebraicGeometry.Stack.representingMap`, Stacks 04SW) and the morphism
`\overline{𝒳} ⟶ \overline{𝒴}` of the presheaves of isomorphism classes of the fibres
(`CategoryTheory.Functor.isoClassMap`, Stacks 04SC) agree under the identification of the presheaf
of isomorphism classes with the representing presheaf by naming sections
(`AlgebraicGeometry.Stack.morphismSpaceEquiv_app_isoClassSection`). Consequently the induced
morphism of representing presheaves is locally surjective as soon as the morphism of presheaves
of isomorphism classes is.

## Main results

* `AlgebraicGeometry.Stack.isLocallySurjective_representingMap_of_isoClassMap`: if the morphism of
  presheaves of isomorphism classes attached to a 1-morphism is locally surjective, then so is the
  induced morphism of representing presheaves.

## References

* [Stacks Project, Tag 04SC](https://stacks.math.columbia.edu/tag/04SC)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, w} (BigFppfOver B S hS))
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eX : StacksRepresentableCFG.EquivalenceOver
    𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eY : StacksRepresentableCFG.EquivalenceOver
    𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
  (J : GrothendieckTopology (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴)

/-- The induced morphism of representing presheaves is locally surjective as soon as the
morphism of presheaves of isomorphism classes is. -/
theorem isLocallySurjective_representingMap_of_isoClassMap
    (h : letI : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.property.isFibered
      Presheaf.IsLocallySurjective J (Functor.isoClassMap
        (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.property
          (CatFiberedInGroupoids.homFunctor_comp_p f)))) :
    Presheaf.IsLocallySurjective J (representingMap B S hS 𝒳 𝒴 F G eX eY f) := by
  let : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.property.isFibered
  refine ⟨fun {U} s => ?_⟩
  obtain ⟨c, hc⟩ := PresheafOfCategories.isoClassSection_surjective eY U s
  refine J.superset_covering ?_ (h.imageSieve_mem (U := U) c)
  rintro V g ⟨t, ht⟩
  refine ⟨PresheafOfCategories.isoClassSection eX V t, ?_⟩
  rw [morphismSpaceEquiv_app_isoClassSection B S hS 𝒳 𝒴 F G eX eY
    ⟨CatFiberedInGroupoids.homFunctor f, CatFiberedInGroupoids.homFunctor_comp_p f⟩ V t, ht,
    ← hc]
  exact PresheafOfCategories.isoClassSection_map eY g c

end AlgebraicGeometry.Stack

end
