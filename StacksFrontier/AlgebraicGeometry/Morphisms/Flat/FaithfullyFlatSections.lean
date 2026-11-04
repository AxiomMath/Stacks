module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A flat surjective morphism is injective on sections

A flat morphism of schemes is injective on stalks: each stalk map is a flat local homomorphism of
local rings, hence faithfully flat, hence injective. If the morphism is in addition surjective,
every point of the target lies in the image, so two sections of the target agreeing after pullback
have the same germ at every point and are therefore equal by the sheaf axiom. Surjectivity of a
single morphism is only used to reach every point, so the same argument separates sections along a
family of flat morphisms that is merely jointly surjective.

## Main results

* `AlgebraicGeometry.Scheme.Hom.stalkMap_injective_of_flat`: every stalk map of a flat morphism
  of schemes is injective.
* `AlgebraicGeometry.Scheme.Hom.app_injective_of_flat_of_surjective`: a flat surjective morphism
  of schemes is injective on the sections over an arbitrary open of the target.
* `AlgebraicGeometry.Scheme.Hom.appTop_injective_of_flat_of_surjective`: the same statement for
  global sections.
* `AlgebraicGeometry.Scheme.section_ext_of_flat_of_jointlySurjective`: two sections over an open
  of the target agreeing after pullback along every member of a jointly surjective family of flat
  morphisms are equal.

## References

* [Stacks Project, Tag 02VW](https://stacks.math.columbia.edu/tag/02VW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every stalk map of a flat morphism of schemes is injective, because a flat local homomorphism
of local rings is faithfully flat. -/
public theorem Scheme.Hom.stalkMap_injective_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (x : X) : Function.Injective (f.stalkMap x) := by
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

/-- Two sections over an open `U` with the same pullback along a flat morphism `f` have the same
germ at `f x`. -/
private theorem germ_eq_of_app_eq_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (U : Y.Opens)
    {s t : Γ(Y, U)} (h : (f.app U).hom s = (f.app U).hom t) (x : X) (hx : f x ∈ U) :
    Y.presheaf.germ U (f x) hx s = Y.presheaf.germ U (f x) hx t := by
  refine f.stalkMap_injective_of_flat x ?_
  simp only [Scheme.Hom.germ_stalkMap_apply, h]

/-- A flat surjective morphism of schemes is injective on the sections over any open of the
target: two sections with the same pullback have equal germs at every point of the open. -/
public theorem Scheme.Hom.app_injective_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] (U : Y.Opens) : Function.Injective (f.app U).hom := by
  intro s t hst
  refine TopCat.Presheaf.section_ext Y.sheaf U s t fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := f.surjective x
  exact germ_eq_of_app_eq_of_flat f U hst y hx

/-- A flat surjective morphism of schemes is injective on global sections. -/
@[sga "3 VIB 12.3" "partial"]
public theorem Scheme.Hom.appTop_injective_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] : Function.Injective f.appTop.hom :=
  f.app_injective_of_flat_of_surjective ⊤

/-- Two sections of the structure sheaf over an open of `T` agreeing after pullback along every
member of a jointly surjective family of flat morphisms to `T` are equal: each member is injective
on stalks, so the two sections have the same germ at every point of the open. -/
public theorem Scheme.section_ext_of_flat_of_jointlySurjective {T : Scheme.{u}} {ι : Type*}
    {V : ι → Scheme.{u}} (π : ∀ i, V i ⟶ T) (hflat : ∀ i, Flat (π i))
    (hsurj : ∀ t : T, ∃ i, ∃ y : V i, π i y = t) (U : T.Opens) {s t : Γ(T, U)}
    (h : ∀ i, ((π i).app U).hom s = ((π i).app U).hom t) : s = t := by
  refine TopCat.Presheaf.section_ext T.sheaf U s t fun x hx ↦ ?_
  obtain ⟨i, y, rfl⟩ := hsurj x
  have := hflat i
  exact germ_eq_of_app_eq_of_flat (π i) U (h i) y hx

end AlgebraicGeometry

end
