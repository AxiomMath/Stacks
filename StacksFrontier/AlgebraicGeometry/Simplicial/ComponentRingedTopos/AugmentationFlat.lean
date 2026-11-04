module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleRestrictUnit
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.FlatMapIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphism

/-!
# Flatness of a ringed augmentation of the total site of a simplicial site

Let `S` be a simplicial-site situation, let `O` be a sheaf of commutative rings on its total site
and let `a : (Sh(𝒞_total), O) ⟶ (Sh(𝒟), O_𝒟)` be a morphism of ringed topoi augmenting the total
ringed topos over a ringed topos `(Sh(𝒟), O_𝒟)`. In simplicial degree `n` the augmentation of the
component is `a_n = a ∘ g_n`, where `g_n : (Sh(𝒞_n), O_n) ⟶ (Sh(𝒞_total), O)` is the canonical
morphism. The morphism `g_n` is flat, and if `a` is flat then so is every `a_n`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation`: the augmentation
  `a_n = a ∘ g_n` of the component of simplicial degree `n`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentRingedToposHom_isFlat`: the canonical
  morphism `g_n` from a simplicial component to the total ringed topos is flat.
* `CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation_toToposHom`: the geometric
  morphism underlying `a_n`.
* `CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation_fSharpInverseImage`: the
  structure map of `a_n` in inverse-image form is `a⁻¹O_𝒟 ⟶ O` pulled back along `g_n`, between
  the comparison of iterated inverse images and the comparison of structure sheaves.
* `CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation_isFlat`: if `a` is flat,
  then so is every `a_n`.

## Implementation notes

Flatness is `AlgebraicGeometry.RingedToposHom.IsFlat`, flatness of the structure map in
inverse-image form. The augmentation is an arbitrary morphism of ringed topoi out of
`CategoryTheory.SimplicialSiteSituation.totalRingedTopos`, with target at
`AlgebraicGeometry.RingedTopos.{u, u, u}`, the single universe of the simplicial-site situation.

## References

* [Stacks Project, Tag 0D9D](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The canonical morphism `g_n` from a simplicial component to the total ringed topos is flat. -/
theorem componentRingedToposHom_isFlat (n : SimplexCategory) :
    (componentRingedToposHom S O n).IsFlat :=
  SheafOfModules.isFlatMapULift_of_isIso _ inferInstance

section Augmentation

variable {D : RingedTopos.{u, u, u}}
  [D.J.HasSheafCompose (forget RingCat.{u})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (a : RingedToposHom (totalRingedTopos S O) D)

/-- The augmentation of a simplicial component, `a_n = a ∘ g_n`: the canonical morphism from the
component of simplicial degree `n` to the total ringed topos, followed by the augmentation of the
total ringed topos. -/
def componentRingedAugmentation (n : SimplexCategory) :
    RingedToposHom (componentRingedTopos S O n) D :=
  a.comp (componentRingedToposHom S O n)

/-- The geometric morphism underlying `a_n` is the component morphism of topoi followed by the
one underlying `a`. -/
theorem componentRingedAugmentation_toToposHom (n : SimplexCategory) :
    (componentRingedAugmentation S O a n).toToposHom =
      a.toToposHom.comp (componentMorphism S n) :=
  rfl

/-- The structure map of `a_n` in inverse-image form is the inverse image along `g_n` of the
structure map `a⁻¹O_𝒟 ⟶ O` of the augmentation, read between the comparison of the iterated
inverse image with the inverse image along `a_n` and the comparison `g_n⁻¹O ≅ O_n`. -/
theorem componentRingedAugmentation_fSharpInverseImage (n : SimplexCategory) :
    (componentRingedAugmentation S O a n).fSharpInverseImage =
      (inverseImageCommRingComp a.toToposHom (componentMorphism S n)).inv.app D.O ≫
        (inverseImageCommRingFunctor (componentMorphism S n)).map a.fSharpInverseImage ≫
          (componentRingedTopos_restrictionIso S n).hom.app O :=
  (RingedToposHom.comp_fSharpInverseImage a (componentRingedToposHom S O n)).trans
    (congrArg
      (fun m ↦ (inverseImageCommRingComp a.toToposHom (componentMorphism S n)).inv.app D.O ≫
        (inverseImageCommRingFunctor (componentMorphism S n)).map a.fSharpInverseImage ≫ m)
      (componentRingedToposHom_fSharpInverseImage S O n))

/-- Abelian sheaves at the site universe are sheafifiable on any site of this size, and the maps
sheafification inverts are the locally bijective ones. -/
private theorem sheafifyAux {E : Type u} [Category.{u} E] (K : GrothendieckTopology E) :
    HasWeakSheafify K AddCommGrpCat.{u} ∧ K.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  ⟨(GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} K).1,
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} K⟩

/-- If the augmentation `a` of the total ringed topos is flat, then so is the augmentation `a_n`
of every simplicial component. -/
@[stacks 0DH3 "the forward implication: flatness of a gives flatness of every a_n"]
theorem componentRingedAugmentation_isFlat (ha : a.IsFlat) (n : SimplexCategory) :
    (componentRingedAugmentation S O a n).IsFlat := by
  obtain ⟨_, _⟩ := sheafifyAux S.totalTopology
  obtain ⟨_, _⟩ := sheafifyAux (S.componentTopology n)
  have hΦ : ((componentMorphism S n).inverseImage).IsLeftAdjoint :=
    ⟨_, ⟨(componentMorphism S n).adj⟩⟩
  have hΦ' : Limits.PreservesFiniteLimits ((componentMorphism S n).inverseImage) :=
    (componentMorphism S n).preservesFiniteLimits
  have h0 : SheafOfModules.IsFlatMap a.fSharpInverseImage :=
    (SheafOfModules.isFlatMapULift_iff_isFlatMap a.fSharpInverseImage).mp ha
  have h1 : SheafOfModules.IsFlatMap
      ((inverseImageCommRingFunctor (componentMorphism S n)).map a.fSharpInverseImage) :=
    Stacks.Sheaves.ToposPullback.isFlatMap_pullbackCommRingSheafMap
      ((componentMorphism S n).inverseImage) a.fSharpInverseImage h0
  have h2 : SheafOfModules.IsFlatMap
      (componentRingedAugmentation S O a n).fSharpInverseImage := by
    rw [componentRingedAugmentation_fSharpInverseImage]
    exact SheafOfModules.isFlatMap_comp_iso
      (((inverseImageCommRingComp a.toToposHom (componentMorphism S n)).app D.O).symm)
      ((componentRingedTopos_restrictionIso S n).app O) h1
  exact (SheafOfModules.isFlatMapULift_iff_isFlatMap
    (componentRingedAugmentation S O a n).fSharpInverseImage).mpr h2

end Augmentation

end CategoryTheory.SimplicialSiteSituation

end
