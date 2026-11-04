module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack

/-!
# Replacing a stack by a stack with set-sized fibres

A stack `p : 𝒳 ⥤ 𝒮` over a locally small base, whose source is essentially small in a
universe `u`, has a strictly full subcategory which is still a stack over the same site,
whose inclusion is essentially surjective, and all of whose fibres are `u`-small. The
subcategory is cut out by the objects obtained as chosen pullbacks of a set of
representatives of `𝒳` along isomorphisms of the base, so each fibre is indexed by a pair of
a representative and an isomorphism, and both are sets.

## Main results

* `CategoryTheory.Functor.IsStack.exists_small_fullSubcategory`.

## Implementation notes

The objects of the subcategory are indexed by triples `(Y, T, T ≅ p.obj Y)` with `Y` running
over a set of representatives of the objects of `𝒳`, obtained from
`CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le`; the object attached to a
triple is the chosen pullback `Functor.IsPreFibered.pullbackObj` of `Y` along the
isomorphism. That index type is `u`-small because the base is locally small, which bounds
the isomorphisms, and the projection of the chosen pullback along the isomorphism is `T` by
`Functor.IsPreFibered.pullbackObj_proj`, so the fibre over `T` is covered by the triples with
second component `T`.

Essential surjectivity and both conditions of Stacks 04TU hold for the same reason: every
object of `𝒳` is isomorphic *over the identity of its image* to an object of the
subcategory, which is `Functor.IsoOverId`. That is proved by taking a representative `Y` of
the object, pulling it back along the isomorphism of images, and observing that the resulting
cartesian morphism lies over an isomorphism, hence is one
(`Functor.IsStronglyCartesian.isIso_of_base_isIso`). Since that single statement implies both
conditions outright, no closure property of the subcategory has to be checked separately, and
`Functor.IsStack.fullSubcategory` applies.

## References

* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
-/

@[expose] public section

open CategoryTheory

universe u v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- A stack whose source is essentially small in `u`, over a `u`-locally small base, has a
strictly full subcategory with `u`-small fibres whose inclusion is essentially surjective and
whose restricted projection is still a stack. -/
theorem Functor.IsStack.exists_small_fullSubcategory [LocallySmall.{u} 𝒮] [EssentiallySmall.{u} 𝒳]
    (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (hp : p.IsStack J) :
    ∃ P : ObjectProperty 𝒳,
      (∀ T : 𝒮, Small.{u} ((Functor.restrict p P).Fiber T)) ∧ P.ι.EssSurj ∧
        (Functor.restrict p P).IsStack J := by
  classical
  have := hp.isFibered
  obtain ⟨Q, hQ, _, hrep⟩ :=
    ObjectProperty.EssentiallySmall.exists_small_le.{u} (⊤ : ObjectProperty 𝒳)
  let _smallIso (U V : 𝒮) : Small.{u} (U ≅ V) :=
    small_of_injective (f := fun e : U ≅ V => e.hom) (fun _ _ h => Iso.ext h)
  let I := Σ Y : Subtype Q, Σ U : 𝒮, U ≅ p.obj Y.val
  let obj (i : I) : 𝒳 :=
    Functor.IsPreFibered.pullbackObj (p := p) (a := i.1.val) rfl i.2.2.hom
  let P := ObjectProperty.ofObj obj
  have hP : ∀ X, Functor.IsoOverId p P X := by
    intro X
    obtain ⟨Y, hY, ⟨e⟩⟩ := hrep X trivial
    let α := p.mapIso e
    let i : I := ⟨⟨Y, hY⟩, p.obj X, α⟩
    let φ : obj i ⟶ Y := Functor.IsPreFibered.pullbackMap (p := p) rfl α.hom
    have : p.IsStronglyCartesian α.hom φ := inferInstance
    have : IsIso φ := Functor.IsStronglyCartesian.isIso_of_base_isIso p α.hom φ
    refine ⟨obj i, ⟨i⟩, e ≪≫ (asIso φ).symm, ?_⟩
    show p.IsHomLift (𝟙 (p.obj X)) (e.hom ≫ _root_.CategoryTheory.inv φ)
    have : p.IsHomLift α.hom e.hom := Functor.IsHomLift.map e.hom
    have : p.IsHomLift (_root_.CategoryTheory.inv α.hom)
      (_root_.CategoryTheory.inv φ) := inferInstance
    simpa using (show p.IsHomLift (α.hom ≫ _root_.CategoryTheory.inv α.hom)
      (e.hom ≫ _root_.CategoryTheory.inv φ) from inferInstance)
  refine ⟨P, fun T => ?_, ⟨fun X => ?_⟩, ?_⟩
  · let K := Σ Y : Subtype Q, T ≅ p.obj Y.val
    have : Small.{u} K := inferInstance
    let F : K → (Functor.restrict p P).Fiber T := fun k =>
      let i : I := ⟨k.1, T, k.2⟩
      ⟨⟨obj i, ⟨i⟩⟩, Functor.IsPreFibered.pullbackObj_proj (p := p) rfl k.2.hom⟩
    apply small_of_surjective (f := F)
    rintro ⟨⟨X, ⟨i⟩⟩, hXT⟩
    dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at hXT
    obtain rfl : i.2.1 = T :=
      (Functor.IsPreFibered.pullbackObj_proj (p := p) rfl i.2.2.hom).symm.trans hXT
    exact ⟨⟨i.1, i.2.2⟩, rfl⟩
  · obtain ⟨Y, hY, e, _⟩ := hP X
    exact ⟨⟨Y, hY⟩, ⟨e.symm⟩⟩
  · exact Functor.IsStack.fullSubcategory p J hp P (fun _ _ _ _ => hP _)
      (fun _ _ _ X _ => hP X.1)

end CategoryTheory

end
