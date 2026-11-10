module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# The cartesian square of a pulled-back zero scheme

Let `f : X' ⟶ X` be a morphism of schemes, let `L` be an invertible `𝒪_X`-module and let
`s ∈ Γ(X, L)`. Stacks 0B6Y says that the zero scheme of the pulled-back section is the
scheme-theoretic inverse image of the zero scheme, and that the resulting square

  `Z(f^* s) ⟶ Z(s)`,  `Z(f^* s) ⟶ X'`,  `X' ⟶ X`,  `Z(s) ⟶ X`

is cartesian. `Stacks.Divisors.zeroScheme_pullback` is the equality of ideal sheaves
`Z(f^* s) = f⁻¹(Z(s))`. This file names the morphism `Z(f^* s) ⟶ Z(s)` the square consists of and
proves the square cartesian for that morphism, which is the form the Gysin maps of chapter 42
consume: `Stacks.Chow.GysinCompatibleWithPushforward` and the Gysin axiom of
`Stacks.Chow.BivariantClass` both take such a morphism, its properness and its compatibility with
the structure morphisms as parameters.

## Main definitions

* `Stacks.Divisors.zeroSchemePullbackMap` — the morphism `Z(f^* s) ⟶ Z(s)` induced by `f`.

## Main results

* `Stacks.Divisors.isPullback_zeroSchemePullbackMap` — the square it sits in is cartesian.
* `Stacks.Divisors.isProper_zeroSchemePullbackMap` — it is proper when `f` is, by base change.
* `Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism` — it commutes with the structure
  morphisms of `X` and `X'` over a base.

## Implementation notes

The morphism is `AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap` of the two zero schemes,
which is characterized by lying over `f`, so it is the only candidate: the closed immersion of
`Z(s)` is a monomorphism, hence a morphism over `f` is unique. Cartesianness is then
`AlgebraicGeometry.isPullback_of_isClosedImmersion` applied to the two closed immersions, whose
hypothesis on the defining ideals is exactly `Stacks.Divisors.zeroScheme_pullback`; no transport
along that equality of ideal sheaves is needed.

No `@[stacks]` attribute is placed here. The cartesian-square clause of Stacks 0B6Y is already
recorded, on `AlgebraicGeometry.Scheme.IdealSheafData.comapIso` and its two projection identities,
by `StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic`; what is below is that clause
read off for the zero scheme of a section, not a further clause of the tag.

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **Stacks 0B6Y.** The morphism `Z(f^* s) ⟶ Z(s)` of zero schemes induced by `f : X' ⟶ X`: the
restriction of `f` to the zero scheme of the pulled-back section, which lands in the zero scheme of
`s` because the inverse image of the latter is the former. -/
def zeroSchemePullbackMap :
    (zeroScheme X' ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)).subscheme ⟶
      (zeroScheme X L s).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ f
    (Scheme.IdealSheafData.le_map_iff_comap_le.2 (le_of_eq (zeroScheme_pullback f L s).symm))

/-- The morphism of zero schemes induced by `f` lies over `f`. -/
@[reassoc (attr := simp)]
theorem zeroSchemePullbackMap_comp_subschemeι :
    zeroSchemePullbackMap f L s ≫ (zeroScheme X L s).subschemeι =
      (zeroScheme X' ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)).subschemeι ≫ f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- **Stacks 0B6Y, the cartesian square.** The zero scheme of a pulled-back section is the fibre
product of the zero scheme with the ambient scheme: the square formed by the two closed immersions,
by `f` and by `Stacks.Divisors.zeroSchemePullbackMap` is cartesian. -/
theorem isPullback_zeroSchemePullbackMap :
    IsPullback
      (zeroScheme X' ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)).subschemeι
      (zeroSchemePullbackMap f L s) f (zeroScheme X L s).subschemeι :=
  AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ f
    (zeroSchemePullbackMap_comp_subschemeι f L s).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      zeroScheme_pullback])

/-- The morphism of zero schemes induced by a proper morphism is proper, being a base change of
it. -/
instance isProper_zeroSchemePullbackMap [IsProper f] : IsProper (zeroSchemePullbackMap f L s) :=
  MorphismProperty.of_isPullback (isPullback_zeroSchemePullbackMap f L s) inferInstance

/-- The morphism of zero schemes induced by `f` commutes with the structure morphisms of `X` and
`X'` over a base scheme. -/
theorem zeroSchemePullbackMap_comp_structureMorphism {S : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S)
    (hf : f ≫ p = p') :
    zeroSchemePullbackMap f L s ≫ ((zeroScheme X L s).subschemeι ≫ p) =
      (zeroScheme X' ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)).subschemeι ≫ p' := by
  rw [← Category.assoc, zeroSchemePullbackMap_comp_subschemeι, Category.assoc, hf]

end Stacks.Divisors

end
