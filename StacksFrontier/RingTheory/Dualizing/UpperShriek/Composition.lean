module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Surjective

/-!
# Composing algebraic upper shriek with a surjection

Let `g : R →+* A` be a homomorphism of finite type and `h : A →+* B` a surjection.  Then `h` is
again of finite type, and a polynomial presentation `p` of `g` induces one of `h ∘ g` with the
*same* polynomial algebra: compose the surjection of `p` with `h`.  For these presentations upper
shriek composes: there is an isomorphism

`h^! ∘ g^! ≅ (h ∘ g)^!`

on all of `D(R)`.

## Main definitions

* `Dualizing.PolynomialPresentation.compSurjective` — the presentation of `h ∘ g` induced by a
  presentation of `g` and a surjection `h`.

## Main results

* `Dualizing.PolynomialPresentation.upperShriekFunctor_comp_derivedHom` — composing upper shriek
  of a presentation with derived coextension of scalars along a surjection gives upper shriek of
  the induced presentation of the composite.
* `Dualizing.upperShriekFunctor_comp_ofSurjective` — the composition law `h^! ∘ g^! ≅ (h ∘ g)^!`
  for a surjective second map, at the induced presentation of the composite.

## References

* [Stacks Project, Tag 0BZT](https://stacks.math.columbia.edu/tag/0BZT)
* [Stacks Project, Tag 0C0F](https://stacks.math.columbia.edu/tag/0C0F)
* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

noncomputable section

/-- Restriction of scalars preserves finite limits. -/
local instance restrictScalars_preservesFiniteLimits {X Y : Type u} [Ring X] [Ring Y]
    (g : X →+* Y) : Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{max v u} g) :=
  ⟨fun _ _ _ => ⟨inferInstance⟩⟩

/-- Restriction of scalars preserves finite colimits. -/
local instance restrictScalars_preservesFiniteColimits {X Y : Type u} [Ring X] [Ring Y]
    (g : X →+* Y) : Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{max v u} g) :=
  ⟨fun _ _ _ => ⟨inferInstance⟩⟩

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- Derived coextension of scalars commutes with the shift. -/
theorem nonempty_commShift_derivedHom (g : A →+* B) :
    Nonempty ((derivedHom.{u, v, u} g).CommShift ℤ) :=
  ⟨(Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, v, u} g)).rightAdjointCommShift ℤ⟩

namespace PolynomialPresentation

variable {g : R →+* A}

/-- The presentation of `h ∘ g` induced by a presentation of `g` and a surjection `h`: the
polynomial algebra and the number of variables are those of the given presentation of `g`, and
the surjection onto the target is the composite of the two surjections. -/
def compSurjective (p : PolynomialPresentation g) (h : A →+* B) (hh : Function.Surjective h) :
    PolynomialPresentation (h.comp g) where
  variableCount := p.variableCount
  toRingHom := h.comp p.toRingHom
  commutes := by rw [RingHom.comp_assoc, p.commutes]
  surjective := hh.comp p.surjective

/-- Upper shriek of a presentation, composed with derived coextension of scalars along a
surjection, is upper shriek of the induced presentation of the composite. -/
theorem upperShriekFunctor_comp_derivedHom (p : PolynomialPresentation g) (h : A →+* B)
    (hh : Function.Surjective h) :
    Nonempty (p.upperShriekFunctor.{u, v} ⋙ derivedHom.{u, v, u} h ≅
      (p.compSurjective h hh).upperShriekFunctor.{u, v}) := by
  obtain ⟨hcs⟩ := nonempty_commShift_derivedHom.{u, v} h
  obtain ⟨eComp⟩ := derivedHomCompIso.{u, v} p.toRingHom h
  refine ⟨Functor.associator p.derivedExtension.{u, v} _ _ ≪≫
    Functor.isoWhiskerLeft p.derivedExtension.{u, v} ?_⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedHom.{u, v, u} p.toRingHom)
      ((derivedHom.{u, v, u} h).commShiftIso (p.variableCount : ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eComp
      (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) (p.variableCount : ℤ))

end PolynomialPresentation

/-- The composition law for upper shriek, for a surjective second map.  Let `g : R →+* A` be a
homomorphism of finite type with a polynomial presentation `p`, and let `h : A →+* B` be
surjective.  Then upper shriek of `h` at its presentation with no variables, composed with upper
shriek of `p`, is upper shriek of the presentation of `h ∘ g` that `p` and `h` induce:

`h^! ∘ g^! ≅ (h ∘ g)^!` -/
theorem upperShriekFunctor_comp_ofSurjective {g : R →+* A} (p : PolynomialPresentation g)
    (h : A →+* B) (hh : Function.Surjective h) :
    Nonempty (p.upperShriekFunctor.{u, v} ⋙
        (PolynomialPresentation.ofSurjective h hh).upperShriekFunctor.{u, v} ≅
      (p.compSurjective h hh).upperShriekFunctor.{u, v}) := by
  obtain ⟨e⟩ := upperShriekFunctor_ofSurjective_iso_derivedHom.{u, v} h hh
  obtain ⟨e'⟩ := p.upperShriekFunctor_comp_derivedHom.{u, v} h hh
  exact ⟨Functor.isoWhiskerLeft p.upperShriekFunctor.{u, v} e ≪≫ e'⟩

end

end Dualizing

end
