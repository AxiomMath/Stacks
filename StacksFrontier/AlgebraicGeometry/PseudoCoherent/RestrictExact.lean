module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Restriction of modules along an open immersion is exact

For an open immersion of schemes `f`, the restriction functor
`AlgebraicGeometry.Scheme.Modules.restrictFunctor f` on sheaves of modules is additive and
preserves finite limits. Being a left adjoint, it also preserves colimits, so it is exact.

## Main results

* `AlgebraicGeometry.Scheme.Modules.restrictFunctor_additive`: restriction is additive.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits`: restriction preserves
  finite limits.

## References

* [The Stacks Project, Lemma 36.14.2 (0A86)](https://stacks.math.columbia.edu/tag/0A86)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Restriction of sheaves of modules along an open immersion is additive. -/
public instance restrictFunctor_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).Additive :=
  letI : PreservesBinaryBiproducts (restrictFunctor f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- Restriction of sheaves of modules along an open immersion preserves finite limits. -/
public instance restrictFunctor_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (restrictFunctor f) :=
  have : PreservesLimitsOfSize.{0, 0} (toPresheaf Y) := preservesLimitsOfSize_shrink _
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ Ab.{u}).obj f.opensFunctor.op) := inferInstance
  have e : restrictFunctor f ⋙ toPresheaf X ≅
      toPresheaf Y ⋙ (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op := Iso.refl _
  have : PreservesFiniteLimits (restrictFunctor f ⋙ toPresheaf X) :=
    preservesFiniteLimits_of_natIso e.symm
  preservesFiniteLimits_of_reflects_of_preserves _ (toPresheaf X)

end AlgebraicGeometry.Scheme.Modules

end
