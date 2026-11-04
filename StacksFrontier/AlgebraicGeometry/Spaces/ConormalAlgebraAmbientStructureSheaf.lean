module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraAmbient

/-!
# The ambient factor of the canonical map, read inside the structure sheaf

Let `i : Z ⟶ X` and `g : X ⟶ X'` be morphisms of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, and write `𝓘 = Ker(i^♯)` and `𝓙 = Ker((i ≫ g)^♯)` for the kernel ideal
sheaves of `AlgebraicGeometry.Space.kernelIdealSheaf`.  The map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` of
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` lands in a sheaf of ideals, and the
sheaf of ideals sits inside the structure sheaf by a monomorphism.  This file identifies the
composite with that inclusion.

## Main results

* `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_comp_ι`: **the map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ`,
  followed by the inclusion `𝓘ⁿ ⊆ 𝒪_X`, is the inverse image along `g` of the inclusion
  `𝓙ⁿ ⊆ 𝒪_{X'}` read in `𝒪_X` through `AlgebraicGeometry.Space.structureModulePullbackMap`.**
* `AlgebraicGeometry.Space.mono_kernelIdealSheafZPowPullbackMap_of_mono_comp`: injectivity of
  that inverse image gives injectivity of the map of powers of the kernel ideal sheaves.

## Route

The proof is the one `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` uses for
the defining ideal sheaves of closed subspaces, and it is the same proof because the two
morphisms are built in the same way.  Both sides are morphisms out of `g^*(𝓙ⁿ)`, hence determined
by their transposes along the adjunction of [Stacks Project, Tag 03D7], and those by their
chartwise linear maps of sections along `g`.  Both chartwise maps are pullback of regular
functions along the vertical morphism of a chart diagram: on the left by
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_transpose` together with
`AlgebraicGeometry.Space.kernelIdealSheafZPowFMap_app_coe`, on the right by
`AlgebraicGeometry.Space.structureModulePullbackMap_transpose`.

## Implementation notes

This is the statement that the `What is not proved` section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMapAmbientComparison.lean` names as
"the `n`-th power analogue of `AlgebraicGeometry.Space.idealSheafMap_comp_ι`", owed for the flat
clause of [Stacks Project, Tag 09RT]; it is also what part (2) of [Stacks Project, Tag 04G2]
needs in degree one, since it is what makes the spaces-side canonical map of
[Stacks Project, Tag 04CP] readable inside the structure sheaf, where the ringed-space map of
[Stacks Project, Tag 01R4] is read by `Stacks.ClosedImmersion.idealSheafMap_comp_ι`.

The structure sheaf is written `CategoryTheory.SheafOfModules.unit` of
`AlgebraicGeometry.Space.structureRingSheaf` throughout, never as
`AlgebraicGeometry.Space.structureUnitModule`: the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonSpacesUnit.lean` record that
bridging the two spellings of one morphism on this chain is a kernel deterministic timeout.
Here the spelling is forced anyway, since it is the one
`AlgebraicGeometry.Space.structureModulePullbackMap` carries in its own type and the one the
inclusion of a sheaf of ideals lands in.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RT](https://stacks.math.columbia.edu/tag/09RT)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X X' : AlgebraicSpaces B S hS} (i : Z ⟶ X) (g : X ⟶ X')

/-- **The map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` of the ambient factor, read inside the structure sheaf.**  The map
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` of
[Stacks Project, Tag 09RS], followed by the inclusion `𝓘ⁿ ⊆ 𝒪_X`, is the inverse image along `g`
of the inclusion `𝓙ⁿ ⊆ 𝒪_{X'}` read in `𝒪_X` through
`AlgebraicGeometry.Space.structureModulePullbackMap`.

Both sides are morphisms out of `g^*(𝓙ⁿ)`, hence determined by their transposes along the
adjunction of [Stacks Project, Tag 03D7], and those by their chartwise linear maps of sections
along `g`; both of those are pullback of regular functions along the vertical morphism of a
chart diagram.  This is the `n`-th power analogue of
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι`. -/
theorem kernelIdealSheafZPowPullbackMap_comp_ι (n : ℤ) :
    kernelIdealSheafZPowPullbackMap B S hS i g n ≫ (kernelIdealSheafZPow B S hS i n).ι =
      (modulePullback B S hS g).map (kernelIdealSheafZPow B S hS (i ≫ g) n).ι ≫
        structureModulePullbackMap B S hS g := by
  refine ((modulePullbackAdjunction B S hS g).homEquiv _ _).injective ?_
  refine Eq.trans ((modulePullbackAdjunction B S hS g).homEquiv_naturality_right
      (kernelIdealSheafZPowPullbackMap B S hS i g n) (kernelIdealSheafZPow B S hS i n).ι)
    (Eq.trans ?_ ((modulePullbackAdjunction B S hS g).homEquiv_naturality_left
      (kernelIdealSheafZPow B S hS (i ≫ g) n).ι (structureModulePullbackMap B S hS g)).symm)
  refine Eq.trans ?_ (congrArg (fun t ↦ (kernelIdealSheafZPow B S hS (i ≫ g) n).ι ≫ t)
    (structureModulePullbackMap_transpose B S hS g).symm)
  refine (modulePushforwardHomEquiv B S hS g _ _).injective ?_
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  refine Eq.trans (modulePushforwardHomEquiv_app_comp_right B S hS g
    ((modulePullbackAdjunction B S hS g).homEquiv _ _
      (kernelIdealSheafZPowPullbackMap B S hS i g n))
    (kernelIdealSheafZPow B S hS i n).ι d s) ?_
  refine Eq.trans (congrArg ((kernelIdealSheafZPow B S hS i n).ι.val.app (op d.U))
    (congrFun (congrFun (congrArg ModuleFMap.app
      (kernelIdealSheafZPowPullbackMap_transpose B S hS i g n)) d) s)) ?_
  refine Eq.trans ?_ (modulePushforwardHomEquiv_app_comp_left B S hS g
    (kernelIdealSheafZPow B S hS (i ≫ g) n).ι
    ((modulePushforwardHomEquiv B S hS g _ _).symm (structureModuleFMap B S hS g)) d s).symm
  refine Eq.trans ?_ (congrFun (congrFun (congrArg ModuleFMap.app
      (Equiv.apply_symm_apply (modulePushforwardHomEquiv B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.unit (structureRingSheaf B S hS X')))
        (structureModuleFMap B S hS g)).symm) d)
      ((kernelIdealSheafZPow B S hS (i ≫ g) n).ι.val.app (op d.V) s))
  rfl

/-- **Injectivity of the inverse image of the inclusion `𝓙ⁿ ⊆ 𝒪_{X'}` gives injectivity of the
map of the powers of the kernel ideal sheaves.**  By
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_comp_ι` the hypothesis says that
`g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` followed by the inclusion `𝓘ⁿ ⊆ 𝒪_X` is a monomorphism, and a morphism whose
composite with another is a monomorphism is one. -/
theorem mono_kernelIdealSheafZPowPullbackMap_of_mono_comp (n : ℤ)
    (h : Mono ((modulePullback B S hS g).map (kernelIdealSheafZPow B S hS (i ≫ g) n).ι ≫
      structureModulePullbackMap B S hS g)) :
    Mono (kernelIdealSheafZPowPullbackMap B S hS i g n) := by
  have hcomp : Mono (kernelIdealSheafZPowPullbackMap B S hS i g n ≫
      (kernelIdealSheafZPow B S hS i n).ι) := by
    rw [kernelIdealSheafZPowPullbackMap_comp_ι]
    exact h
  exact mono_of_mono _ (kernelIdealSheafZPow B S hS i n).ι

end AlgebraicGeometry.Space

end
