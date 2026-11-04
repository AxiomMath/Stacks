module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of scalars along a locally surjective morphism of sheaves of rings

Let `f : O ⟶ O'` be a morphism of sheaves of rings on a site. Restriction of scalars
`SheafOfModules O' ⥤ SheafOfModules O` is always faithful, and it is full as soon as `f` is
locally surjective: for two sheaves of `O'`-modules `G₁` and `G₂`, every `O`-linear morphism
`G₁ ⟶ G₂` is automatically `O'`-linear, because a section of `O'` is locally in the image of
`f` and the target is a sheaf.

## Main definitions

* `fullyFaithfulOfIsLocallySurjective`: restriction of scalars along a locally surjective `f`,
  as a `Functor.FullyFaithful` datum.
* `homEquivOfIsLocallySurjective`: the bijection `Hom_{O'}(G₁, G₂) ≃ Hom_O(G₁, G₂)` for a locally
  surjective `f`.

## Main results

* `faithful_restrictScalars`: restriction of scalars is faithful, with no hypothesis on `f`.
* `full_restrictScalars` and `restrictScalars_fullyFaithful_of_isLocallySurjective`:
  restriction of scalars along a locally surjective morphism of sheaves of rings is full, hence
  fully faithful.

## Implementation notes

The hypothesis here is `Sheaf.IsLocallySurjective f` (equivalently
`Presheaf.IsLocallySurjective J f.hom`), *not* `Epi f` in `Sheaf J RingCat`. The two are
genuinely different: a categorical epimorphism of sheaves of rings need not be locally
surjective. Already on the one-object site with the trivial topology, where sheaves of rings are
just rings, `Int.castRingHom ℚ : ℤ →+* ℚ` is an epimorphism in `RingCat` (every ring homomorphism
out of `ℚ` is unique, `Rat.subsingleton_ringHom`) and is not surjective. Mathlib's
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'` accordingly assumes `Balanced (Sheaf J A)`,
which fails for `A = RingCat`.

All four universes are independent: the site is `C : Type u'` with `Category.{v'} C`, the sheaves
of rings are `RingCat.{u}`-valued and the module universe `v` is unconstrained.

## References

* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
-/


@[expose] public section

open CategoryTheory

universe v v' u u'

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable {O O' : Sheaf J RingCat.{u}} (f : O ⟶ O')

/-- Restriction of scalars along any morphism of sheaves of rings is faithful. -/
instance faithful_restrictScalars :
    (SheafOfModules.restrictScalars.{v} f).Faithful where
  map_injective h :=
    SheafOfModules.hom_ext ((PresheafOfModules.restrictScalars f.hom).map_injective
      (congrArg SheafOfModules.Hom.val h))

/-- If `f : O ⟶ O'` is a locally surjective morphism of sheaves of rings, restriction of
scalars along `f` is fully faithful: an `O`-linear morphism between sheaves of `O'`-modules is
`O'`-linear. Its inverse on morphisms is
`PresheafOfModules.restrictHomEquivOfIsLocallySurjective`. -/
noncomputable def fullyFaithfulOfIsLocallySurjective [Sheaf.IsLocallySurjective f] :
    (SheafOfModules.restrictScalars.{v} f).FullyFaithful where
  preimage {_G₁ G₂} g :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective f.hom G₂.isSheaf).symm g.val⟩
  map_preimage {_G₁ G₂} g := SheafOfModules.hom_ext
    ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective f.hom
      G₂.isSheaf).apply_symm_apply g.val)
  preimage_map {_G₁ G₂} φ := SheafOfModules.hom_ext
    ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective f.hom
      G₂.isSheaf).symm_apply_apply φ.val)

/-- For a locally surjective morphism of sheaves of rings `f : O ⟶ O'` and two sheaves of
`O'`-modules `G₁` and `G₂`, the `O'`-linear morphisms `G₁ ⟶ G₂` are exactly the `O`-linear
ones. -/
noncomputable def homEquivOfIsLocallySurjective [Sheaf.IsLocallySurjective f]
    (G₁ G₂ : SheafOfModules.{v} O') :
    (G₁ ⟶ G₂) ≃ ((SheafOfModules.restrictScalars.{v} f).obj G₁ ⟶
      (SheafOfModules.restrictScalars.{v} f).obj G₂) :=
  (fullyFaithfulOfIsLocallySurjective.{v} f).homEquiv

/-- Restriction of scalars along a locally surjective morphism of sheaves of rings is full. -/
instance full_restrictScalars [Sheaf.IsLocallySurjective f] :
    (SheafOfModules.restrictScalars.{v} f).Full :=
  (fullyFaithfulOfIsLocallySurjective.{v} f).full

/-- Restriction of scalars along a locally surjective morphism of sheaves of rings is fully
faithful. -/
theorem restrictScalars_fullyFaithful_of_isLocallySurjective [Sheaf.IsLocallySurjective f] :
    Nonempty (SheafOfModules.restrictScalars.{v} f).FullyFaithful :=
  ⟨fullyFaithfulOfIsLocallySurjective.{v} f⟩

end Stacks.SheafOfModules.ChangeOfRings

end
