module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleImmersionClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionFlatCommute

/-!
# Two properties of the Gysin classes of regular immersions

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. For a regular immersion
`i` of schemes locally of finite type over `S`, the class `i^! = c(X ⟶ P, 𝒩_{X/P})` of its normal
sheaf (`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`) is attached to the immersion by
Stacks 0FBQ (3) (`Stacks.Chow.completedVirtualNormalGysinClassOfImmersion`). This file states,
as propositions, two properties of these classes: their composition law (Stacks 0FF0) and their
base change along a smooth morphism (Stacks 0FBK).

## Main definitions

* `Stacks.Chow.RegularImmersionCompositionCase` — `(s ≫ j)^! = s^! ∘ j^!` for regular immersions
  `s` and `j` (Stacks 0FF0).
* `Stacks.Chow.RegularImmersionSmoothBaseChangeCase` — the restriction of `i^!` along a smooth
  morphism is the class of the base change of `i` (Stacks 0FBK).

## References

* [Stacks Project, Tag 0FF0](https://stacks.math.columbia.edu/tag/0FF0)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-! ### The two cases -/

section Inputs

variable (C : ChowSituation.{u})

/-- The composition law for Gysin classes: for regular immersions `s : X ⟶ W` and `j : W ⟶ P`
of schemes locally of finite type over the base, `(s ≫ j)^! = s^! ∘ j^!` in `A^*(X ⟶ P)^∧`, for
the classes of the normal sheaves (`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`) of the
three regular immersions, attached to immersions by Stacks 0FBQ (3). -/
def RegularImmersionCompositionCase : Prop :=
  ∀ {X W P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (s : X ⟶ W) (j : W ⟶ P)
    [IsImmersion s] [IsImmersion j] (hs : s ≫ sW = sX) (hj : j ≫ sP = sW)
    (hsr : IsRegularImmersion s) (hjr : IsRegularImmersion j) (hr : IsRegularImmersion (s ≫ j)),
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
    letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
    completedVirtualNormalGysinClassOfImmersion C sX sP (s ≫ j)
        (comp_comp_structureMorphism_eq hs hj)
        (VirtualNormalBundle.ofIsRegularImmersion (s ≫ j) hr) =
      completedBivariantCompositeOfInvertible C sX sW sP s j hs hj
        (completedVirtualNormalGysinClassOfImmersion C sX sW s hs
          (VirtualNormalBundle.ofIsRegularImmersion s hsr))
        (completedVirtualNormalGysinClassOfImmersion C sW sP j hj
          (VirtualNormalBundle.ofIsRegularImmersion j hjr))

/-- Smooth base change for Gysin classes: for a regular immersion `i : X ⟶ P` of schemes locally
of finite type over the base and a smooth morphism `p : P' ⟶ P`, the restriction (Stacks 0F9Z) of
`i^! ∈ A^*(X ⟶ P)^∧` along `p` is `j^!` for the base change `j : X ×_P P' ⟶ P'`, for the classes
of the normal sheaves (`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`) attached to
immersions by Stacks 0FBQ (3). -/
def RegularImmersionSmoothBaseChangeCase : Prop :=
  ∀ {X P P' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (i : X ⟶ P) [IsImmersion i] (hi : i ≫ sP = sX) (p : P' ⟶ P)
    [Smooth p] (hr : IsRegularImmersion i) (hr' : IsRegularImmersion (pullback.snd i p)),
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
    letI : IsLocallyNoetherian P' := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sP)
    letI : IsLocallyNoetherian (pullback i p) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i p ≫ sX)
    completedBivariantRestrictionViaSequence C sX sP i hi p
        (completedVirtualNormalGysinClassOfImmersion C sX sP i hi
          (VirtualNormalBundle.ofIsRegularImmersion i hr)) =
      completedVirtualNormalGysinClassOfImmersion C (pullback.fst i p ≫ sX) (p ≫ sP)
        (pullback.snd i p) (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p)
        (VirtualNormalBundle.ofIsRegularImmersion (pullback.snd i p) hr')

end Inputs

end Stacks.Chow

end
