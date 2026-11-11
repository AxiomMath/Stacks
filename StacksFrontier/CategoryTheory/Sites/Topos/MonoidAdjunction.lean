module

public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.MonSheaf
public import StacksFrontier.CategoryTheory.Sites.Topos.StructureAdjunction

/-!
# Morphisms of topoi preserve sheaves of monoids

Let `f = (f⁻¹, f_*)` be a morphism of topoi `Sh(C) → Sh(D)`. A sheaf of monoids is a sheaf of
sets `F` together with a multiplication `F × F → F` and a unit `* → F` satisfying the monoid
axioms, and these are expressed by finite products and commutative diagrams in the topos of
sheaves of sets. The inverse image `f⁻¹` is left exact, so it preserves finite products, and
the direct image `f_*` preserves all limits, being a right adjoint; both therefore carry monoid
objects to monoid objects. This gives an adjoint pair `(f⁻¹, f_*)` on sheaves of monoids, and
by construction it is compatible with taking underlying sheaves of sets. This is case (4) of
Stacks 00YV.

## Main definitions

* `Stacks.Topos.monInverseImage`: the inverse image `f⁻¹ : Sh(D, Mon) ⥤ Sh(C, Mon)`.
* `Stacks.Topos.monPushforward`: the direct image `f_* : Sh(C, Mon) ⥤ Sh(D, Mon)`.
* `Stacks.Topos.monAdjunction`: the adjunction `f⁻¹ ⊣ f_*` on sheaves of monoids.
* `Stacks.Topos.monStructureAdjunction`: the adjoint pair on sheaves of monoids, compatible
  with taking underlying sheaves of sets.

## Main results

* `Stacks.Topos.monAdjunction_unit_forget`: forgetting the monoid operations takes the unit
  of `monAdjunction` to the unit of `f⁻¹ ⊣ f_*` on sheaves of sets.

## Implementation notes

Sheaves of monoids are identified with monoid objects in sheaves of sets by
`CategoryTheory.Sites.MonSheaf.equivalence`, both of whose directions leave the underlying
sheaf of sets untouched. The two functors are Mathlib's `CategoryTheory.Functor.mapMon` applied
to `f⁻¹` and `f_*`. The inverse image is made monoidal for the cartesian structures by
`CategoryTheory.Functor.Braided.ofChosenFiniteProducts`, and the direct image carries the lax
monoidal structure `CategoryTheory.Adjunction.rightAdjointLaxMonoidal` of the right adjoint of a
monoidal functor, for which the adjunction is monoidal by construction; the adjunction is then
`CategoryTheory.Adjunction.mapMon` of `f⁻¹ ⊣ f_*`, read through the identification. Hence the
comparisons with the underlying sheaves of sets are identities, and the unit of the composite
adjunction is the unit of `f⁻¹ ⊣ f_*` followed by the direct image of an identity.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

namespace Stacks.Topos

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe w v u v' u'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- The functor induced on monoid objects by the inverse image of a morphism of topoi, which is
monoidal for the cartesian structures since it is left exact. -/
noncomputable def monObjInverseImage : Mon (Sheaf K (Type w)) ⥤ Mon (Sheaf J (Type w)) :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  f.inverseImage.mapMon

/-- The functor induced on monoid objects by the direct image of a morphism of topoi, which is
lax monoidal for the cartesian structures as the right adjoint of a monoidal functor. -/
noncomputable def monObjPushforward : Mon (Sheaf J (Type w)) ⥤ Mon (Sheaf K (Type w)) :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : f.pushforward.LaxMonoidal := f.adj.rightAdjointLaxMonoidal
  f.pushforward.mapMon

/-- The adjunction induced on monoid objects by a morphism of topoi. -/
noncomputable def monObjAdjunction : monObjInverseImage f ⊣ monObjPushforward f :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : f.pushforward.LaxMonoidal := f.adj.rightAdjointLaxMonoidal
  f.adj.mapMon

/-- The inverse image of sheaves of monoids along a morphism of topoi: apply the inverse image
of sheaves of sets to the monoid operations and read the result sectionwise. -/
noncomputable def monInverseImage : Sheaf K MonCat.{w} ⥤ Sheaf J MonCat.{w} :=
  MonSheaf.internalSheaf K ⋙ monObjInverseImage f ⋙ MonSheaf.externalSheaf J

/-- The direct image of sheaves of monoids along a morphism of topoi: apply the direct image of
sheaves of sets to the monoid operations and read the result sectionwise. -/
noncomputable def monPushforward : Sheaf J MonCat.{w} ⥤ Sheaf K MonCat.{w} :=
  MonSheaf.internalSheaf J ⋙ monObjPushforward f ⋙ MonSheaf.externalSheaf K

/-- The inverse image of sheaves of monoids is left adjoint to the direct image. -/
noncomputable def monAdjunction : monInverseImage f ⊣ monPushforward f :=
  ((MonSheaf.equivalence K).toAdjunction.comp (monObjAdjunction f)).comp
    (MonSheaf.equivalence J).symm.toAdjunction

/-- Forgetting the monoid operations of `monInverseImage f` recovers the inverse image of the
underlying sheaf of sets, on the nose. -/
noncomputable def monInverseImageForgetIso :
    monInverseImage f ⋙ sheafCompose J (forget MonCat.{w}) ≅
      sheafCompose K (forget MonCat.{w}) ⋙ f.inverseImage :=
  Iso.refl _

/-- Forgetting the monoid operations of `monPushforward f` recovers the direct image of the
underlying sheaf of sets, on the nose. -/
noncomputable def monPushforwardForgetIso :
    monPushforward f ⋙ sheafCompose K (forget MonCat.{w}) ≅
      sheafCompose J (forget MonCat.{w}) ⋙ f.pushforward :=
  Iso.refl _

/-- Forgetting the monoid operations takes the unit of `monAdjunction f` to the unit of
`f⁻¹ ⊣ f_*` on sheaves of sets. -/
theorem monAdjunction_unit_forget (G : Sheaf K MonCat.{w}) :
    (sheafCompose K (forget MonCat.{w})).map ((monAdjunction f).unit.app G) =
      f.adj.unit.app ((sheafCompose K (forget MonCat.{w})).obj G) := by
  have key : (sheafCompose K (forget MonCat.{w})).map ((monAdjunction f).unit.app G) =
      f.adj.unit.app ((sheafCompose K (forget MonCat.{w})).obj G) ≫
        f.pushforward.map (𝟙 (f.inverseImage.obj
          ((sheafCompose K (forget MonCat.{w})).obj G))) := rfl
  refine key.trans (Eq.trans (congrArg (fun t =>
    f.adj.unit.app ((sheafCompose K (forget MonCat.{w})).obj G) ≫ t)
      (f.pushforward.map_id _)) ?_)
  exact Category.comp_id _

/-- **Stacks 00YV, sheaves of monoids.** A morphism of topoi `f` gives an adjoint pair
`(f⁻¹, f_*)` on sheaves of monoids, compatible with taking underlying sheaves of sets: both
functors leave the underlying sheaves of sets as `f⁻¹` and `f_*` make them, and the unit of the
adjunction is the unit of `f⁻¹ ⊣ f_*` on sheaves of sets. -/
noncomputable def monStructureAdjunction : StructureAdjunction f (forget MonCat.{w}) where
  inverseImage := monInverseImage f
  pushforward := monPushforward f
  adj := monAdjunction f
  inverseImageForgetIso := monInverseImageForgetIso f
  pushforwardForgetIso := monPushforwardForgetIso f
  forget_map_unit_app F := by
    refine Eq.trans ?_ (monAdjunction_unit_forget f F)
    refine Eq.trans (congrArg (fun t =>
      (sheafCompose K (forget MonCat.{w})).map ((monAdjunction f).unit.app F) ≫ t)
      (Eq.trans (Category.id_comp _) (f.pushforward.map_id _))) ?_
    exact Category.comp_id _

end Stacks.Topos

end
