module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRecoveredFromSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationModificationFromMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RecoveryOverBase

/-!
# The morphism of ringed topoi `α = (a')^♯ + D` of Stacks 04D0, built from `θ`

Let `X ⊂ X'` and `Y ⊂ Y'` be closed subspaces of algebraic spaces over a scheme `S` contained in
a big fppf site, with `X ⊂ X'` a **first order thickening**, let `(a, a')` be a morphism of the
two pairs — so `i_X ≫ a' = a ≫ i_Y` — let `p : Y' ⟶ T` be a structure morphism and let

`θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}`

be an `𝒪_X`-linear map.  [Stacks Project, Tag 04D0] modifies the structure map of `a'` by the
`𝒪_T`-derivation `D` attached to `θ` by Equation (0619), forming

`α = (a')^♯ + D`,

and asserts that there is exactly one morphism `b' : X' ⟶ Y'` whose structure map is `α`, with
`(a, b')` a morphism of pairs.

This file builds `α` — with **nothing assumed** beyond the source's own hypotheses — and proves
the **uniqueness** half of Tag 04D0 for it, which needs nothing further: two morphisms of
algebraic spaces inducing one and the same morphism of small étale ringed topoi are equal, by
[Stacks Project, Tag 04M6].

## Main definitions

* `AlgebraicGeometry.Space.derivationModificationHomOfMap`: the morphism `α = (a')^♯ + D` of
  small étale ringed topoi, with the same underlying morphism of topoi as `a'` and with
  structure map the sum of `(a')^♯` and the derivation of
  `AlgebraicGeometry.Space.thickeningRingSheafDerivation`.

## Main results

* `AlgebraicGeometry.Space.derivationModificationHomOfMap_fSharp_apply`: the value of `α` on a
  section is `(a')^♯(x) + D(x)`, which is what identifies it with the source's map.
* `AlgebraicGeometry.Space.derivationModificationHomOfMap_isLocallyRinged`,
  `AlgebraicGeometry.Space.nonempty_smallEtaleTwoIso_derivationModificationHomOfMap_comp` and
  `AlgebraicGeometry.Space.nonempty_smallEtaleTwoIso_derivationModificationHomOfMap_base`: the
  three properties of `α` that [Stacks Project, Tag 05ZN] consumes — it is locally ringed, it
  fits the source's square `i_X^♯ ∘ α = a^♯ ∘ i_Y^♯`, and it is a map of `𝒪_T`-algebras.  All
  three are proved outright.
* `AlgebraicGeometry.Space.eq_of_derivationModificationHomOfMap_induces`: **the uniqueness half
  of [Stacks Project, Tag 04D0], with nothing assumed.**  Two morphisms `b₁', b₂' : X' ⟶ Y'`
  which both induce `α` are equal.
* `AlgebraicGeometry.Space.existsUnique_hom_of_derivationModificationHomOfMap`: the whole of
  [Stacks Project, Tag 04D0], with nothing assumed.  The recovery of morphisms over the base
  (`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`) is proved by
  `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`.

## Implementation notes

`α` is built in the direct-image form `𝒪_{Y'} ⟶ (a')_*𝒪_{X'}`, which is the `fSharp` field of
`AlgebraicGeometry.RingedToposHom` and the form of the source's displayed composite of
[Stacks Project, Tag 0619]; the source writes `α : a^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`, which is its
transpose along `a^{-1} ⊣ a_*` and carries exactly the same information
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is that transpose).  The reason the
direct-image form is the one built is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/DerivationModificationFromMap.lean`: nothing
in this development describes the sections of `a^{-1}𝒪_{Y'}`, while Equation (0619) produces the
direct-image form outright.

The wrapper is an `abbrev` rather than a `def`: as a semireducible definition its `.toToposHom`
does not reduce at `implicit` transparency, and every consumer that composes `α` with another
morphism of ringed topoi pays that.

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' Y' T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X'.1)
  (hZ : IsFirstOrderThickening B S hS X' Z.1) (a' : X' ⟶ Y')
  (W : ClosedSubspaces B S hS Y'.1) (p : Y' ⟶ T)
  (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W.1.toFunctor, W.2.1⟩)
  (hcompat : subspaceInclusion B S hS X' Z ≫ a' = a ≫ subspaceInclusion B S hS Y' W)
  (θ : (modulePullback B S hS a).obj
      (sheafOfDifferentials B S hS (subspaceInclusion B S hS Y' W ≫ p)) ⟶
    conormalModule B S hS X' Z)

/-- **The map `α = (a')^♯ + D` of [Stacks Project, Tag 04D0]**, as a morphism of the small étale
ringed topoi of `X'` and `Y'`: the same underlying morphism of topoi as `a'`, with structure map
the sum of `(a')^♯` and the `𝒪_T`-derivation attached to `θ` by Equation (0619). -/
noncomputable abbrev derivationModificationHomOfMap :
    RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y') :=
  { toToposHom := (smallEtaleRingedToposHom B S hS a').toToposHom
    fSharp := (thickeningRingSheafDerivation B S hS Z hZ a' W p a hcompat θ).add }

/-- The modified morphism has the same underlying morphism of topoi as `a'`. -/
@[simp]
theorem derivationModificationHomOfMap_toToposHom :
    (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ).toToposHom =
      (smallEtaleRingedToposHom B S hS a').toToposHom := rfl

/-- **The value of `α` on a section is `(a')^♯(x) + D(x)`.**  This is what identifies
`AlgebraicGeometry.Space.derivationModificationHomOfMap` with the map of
[Stacks Project, Tag 04D0]. -/
theorem derivationModificationHomOfMap_fSharp_apply
    (V' : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (x : (smallEtaleRingedTopos B S hS Y').O.obj.obj V') :
    (((derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ).fSharp.hom.app V').hom x) =
      ((smallEtaleRingedToposHom B S hS a').fSharp.hom.app V').hom x +
        (thickeningRingSheafDerivation B S hS Z hZ a' W p a hcompat θ).toFun V' x :=
  (thickeningRingSheafDerivation B S hS Z hZ a' W p a hcompat θ).add_apply V' x

/-- **`i_X^♯` kills the values of `D`, read through the factorization.**  The derivation's values
come from the conormal module, and the inclusion of the conormal module of a first order
thickening into `𝒪_{X'}` lands in the defining ideal, which is the kernel of `i_X^♯` chart by
chart.  The vanishing is then transported to the small étale site of `Y'` — where nothing
describes the sections of the direct image — by
`Stacks.Sheaves.ToposPushforward.pushforward_map_apply_eq_zero_of_mem_range`. -/
theorem structureSharp_map_thickeningConormalDerivation_eq_zero
    (V' : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (x : (structureRingSheaf B S hS Y').obj.obj V') :
    ((((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS a').toToposHom).map
          (structureSharpCommRing B S hS (subspaceInclusion B S hS X' Z))).hom.app V').hom
        ((smallEtaleDirectImage B S hS a' ⋙
            CategoryTheory.Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y'.1) V').map
          ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
            (firstOrderConormalModuleι B S hS Z hZ))
          ((thickeningConormalDerivation B S hS Z a' W p a hcompat θ).d x))) = 0 :=
  Stacks.Sheaves.ToposPushforward.pushforward_map_apply_eq_zero_of_mem_range
    (smallEtaleRingedToposHom B S hS a').toToposHom
    (structureSharpCommRing B S hS (subspaceInclusion B S hS X' Z))
    ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
      (firstOrderConormalModuleι B S hS Z hZ))
    (fun U s => (structureSharpCommRing_app_apply B S hS
        (subspaceInclusion B S hS X' Z) U _).trans
      (structureSharpKillsDefiningIdeal_subspaceInclusion B S hS Z U _
        (firstOrderConormalModuleι_app_mem_definingIdealAt B S hS Z hZ U s))) V' _

/-- **`i_X^♯` kills the values of `D`.**  This is
`AlgebraicGeometry.Space.structureSharp_map_thickeningConormalDerivation_eq_zero` with the
factorization of the values folded back in.  For [Stacks Project, Tag 04D0] it is the source's
equation `i_X^♯ ∘ α = a^♯ ∘ i_Y^♯`: the modification by `D` is invisible to `i_X^♯`. -/
theorem structureSharp_map_thickeningDerivationFun_eq_zero
    (V' : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (x : (structureRingSheaf B S hS Y').obj.obj V') :
    ((((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS a').toToposHom).map
          (structureSharpCommRing B S hS (subspaceInclusion B S hS X' Z))).hom.app V').hom
        (thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' x)) = 0 :=
  (congrArg (fun z : ToType ((structureRingSheafDirectImage B S hS a').obj.obj V') =>
      (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS a').toToposHom).map
          (structureSharpCommRing B S hS (subspaceInclusion B S hS X' Z))).hom.app V').hom z)
    (thickeningDerivationFun_eq_map B S hS Z hZ a' W p a hcompat θ V' x)).trans
    (structureSharp_map_thickeningConormalDerivation_eq_zero B S hS Z hZ a' W p a hcompat θ V' x)

/-- **The square of [Stacks Project, Tag 05ZN] for `α`**, which is the source's equation
`i_X^♯ ∘ α = a^♯ ∘ i_Y^♯`: the structure map of `a'` and its modification `α = (a')^♯ + D` become
equal after the direct image along `a'` of the structure map of `i_X`.  The proof is that `D`
takes its values in the kernel of `i_X^♯`. -/
theorem derivationModificationHomOfMap_fSharp_comp_eq :
    (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ).fSharp ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS a').toToposHom).map
          (structureSharpCommRing B S hS (subspaceInclusion B S hS X' Z)) =
      (smallEtaleRingedToposHom B S hS a').fSharp ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS a').toToposHom).map
          (structureSharpCommRing B S hS (subspaceInclusion B S hS X' Z)) :=
  (thickeningRingSheafDerivation B S hS Z hZ a' W p a hcompat θ).add_comp_eq _
    (structureSharp_map_thickeningDerivationFun_eq_zero B S hS Z hZ a' W p a hcompat θ)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of sheaves on the small étale site times out
/-- Pullbacks of sheaves on the small étale site of `X'` (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullbacks_sheaf_DerivationModificationMorphism :
    Limits.HasPullbacks (Sheaf (smallEtaleRingedTopos B S hS X').J (Type u)) :=
  inferInstance

/-- Pullbacks of sheaves on the small étale site of `X'`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_sheaf_DerivationModificationMorphism
    {P Q R : Sheaf (smallEtaleRingedTopos B S hS X').J (Type u)} (f : P ⟶ R) (g : Q ⟶ R) :
    Limits.HasLimit (Limits.cospan f g) :=
  Limits.HasLimitsOfShape.has_limit _

/-- **`α` is a morphism of locally ringed topoi**, with nothing assumed beyond the source's
hypotheses.  This is the `isLocallyRinged` input that [Stacks Project, Tag 05ZN] consumes for
[Stacks Project, Tag 04D0].

The morphism of small étale ringed topoi of `a'` is locally ringed by
[Stacks Project, Tag 04KJ] (`AlgebraicGeometry.Space.smallEtaleRingedToposHom_isLocallyRinged`,
proved unconditionally), and the two structure maps agree after `i_X^♯`, whose sectionwise
kernel is the defining ideal and so has square zero; a section of `𝒪_{X'}` is invertible exactly
when its translate by a square-zero section is, so the two have the same cartesian units
square. -/
theorem derivationModificationHomOfMap_isLocallyRinged :
    (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ).IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_of_fSharp_comp_eq (smallEtaleRingedToposHom B S hS a')
    (smallEtaleRingedToposHom_isLocallyRinged B S hS a')
    (thickeningRingSheafDerivation B S hS Z hZ a' W p a hcompat θ).add
    (structureSharpCommRing B S hS (subspaceInclusion B S hS X' Z))
    (fun U x hx => mul_eq_zero_of_mem_definingIdealAt B S hS Z hZ
      (structureSharpKernelLeDefiningIdeal_subspaceInclusion B S hS Z U x hx)
      (structureSharpKernelLeDefiningIdeal_subspaceInclusion B S hS Z U x hx))
    (derivationModificationHomOfMap_fSharp_comp_eq B S hS Z hZ a' W p a hcompat θ).symm

/-- **`α` composed with `i_X` is the structure map of `a'` composed with `i_X`.**  The two
morphisms of ringed topoi have the same underlying morphism of topoi, and their structure maps
agree after the direct image of `i_X^♯`, which is exactly the first factor of the structure map
of the composite. -/
theorem smallEtaleComp_derivationModificationHomOfMap :
    smallEtaleComp B S hS (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ)
        (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X' Z)) =
      smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS a')
        (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X' Z)) := by
  simp only [smallEtaleComp, RingedToposHom.comp]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _)
    (derivationModificationHomOfMap_fSharp_comp_eq B S hS Z hZ a' W p a hcompat θ)

/-- **The square of [Stacks Project, Tag 05ZN] for `α`, in the 2-isomorphism form.**  This is the
`hsquare` argument of
`AlgebraicGeometry.Space.existsUnique_thickeningHom_of_isLocallyRinged`: `α` composed with the
morphism of ringed topoi of `i_X` is 2-isomorphic to the morphism of ringed topoi of
`a ≫ i_Y`. -/
theorem nonempty_smallEtaleTwoIso_derivationModificationHomOfMap_comp :
    Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ)
        (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X' Z)))
      (smallEtaleRingedToposHom B S hS (a ≫ subspaceInclusion B S hS Y' W))) := by
  refine ⟨?_⟩
  rw [smallEtaleComp_derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ, ← hcompat]
  exact smallEtaleRingedToposHomCompTwoIso B S hS (subspaceInclusion B S hS X' Z) a'

/-- **`α` is a map of `𝒪_T`-algebras, in the inverse-image form.**  The derivation `D` is an
`𝒪_T`-derivation — that is the `d_app` clause of Equation (0619) — so it vanishes on the image
of `p^{-1}𝒪_T`, and the modification is invisible there. -/
theorem structureSharpInverseImage_comp_derivationModificationHomOfMap_fSharp :
    structureSharpInverseImage B S hS p ≫
        (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ).fSharp =
      structureSharpInverseImage B S hS p ≫ (smallEtaleRingedToposHom B S hS a').fSharp := by
  refine (thickeningRingSheafDerivation B S hS Z hZ a' W p a hcompat θ).precomp_add_eq
    (structureSharpInverseImage B S hS p) fun V' t => ?_
  rw [thickeningRingSheafDerivation_toFun B S hS Z hZ a' W p a hcompat θ]
  exact thickeningDerivationFun_structureSharpInverseImage B S hS Z hZ a' W p a hcompat θ V' t

/-- **`α` is a map of `𝒪_T`-algebras**, in the direct-image form: the transpose of
`AlgebraicGeometry.Space.structureSharpInverseImage_comp_derivationModificationHomOfMap_fSharp`
along `p^{-1} ⊣ p_*`. -/
theorem fSharp_comp_pushforward_derivationModificationHomOfMap_fSharp :
    (smallEtaleRingedToposHom B S hS p).fSharp ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS p).toToposHom).map
          (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ).fSharp =
      (smallEtaleRingedToposHom B S hS p).fSharp ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS p).toToposHom).map
          (smallEtaleRingedToposHom B S hS a').fSharp := by
  have hfs : ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS p).toToposHom).homEquiv
      (smallEtaleRingedTopos B S hS T).O (smallEtaleRingedTopos B S hS Y').O)
      (structureSharpInverseImage B S hS p) = (smallEtaleRingedToposHom B S hS p).fSharp :=
    ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
      (smallEtaleRingedToposHom B S hS p).toToposHom).homEquiv _ _).apply_symm_apply _
  let adj := Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
    (smallEtaleRingedToposHom B S hS p).toToposHom
  have h1 := adj.homEquiv_naturality_right (structureSharpInverseImage B S hS p)
    (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ).fSharp
  have h2 := adj.homEquiv_naturality_right (structureSharpInverseImage B S hS p)
    (smallEtaleRingedToposHom B S hS a').fSharp
  have key := congrArg (adj.homEquiv (smallEtaleRingedTopos B S hS T).O _)
    (structureSharpInverseImage_comp_derivationModificationHomOfMap_fSharp
      B S hS Z hZ a' W p a hcompat θ)
  rw [← hfs]
  exact h1.symm.trans (key.trans h2)

/-- **`α` composed with the structure morphism of `Y'` is `a'` composed with it.**  The two have
the same underlying morphism of topoi, and their structure maps agree after the direct image of
`p^♯` because the derivation is an `𝒪_T`-derivation. -/
theorem smallEtaleComp_derivationModificationHomOfMap_base :
    smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS p)
        (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ) =
      smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS p)
        (smallEtaleRingedToposHom B S hS a') := by
  simp only [smallEtaleComp, RingedToposHom.comp]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _)
    (fSharp_comp_pushforward_derivationModificationHomOfMap_fSharp B S hS Z hZ a' W p a hcompat θ)

/-- **`α` is a map of `𝒪_T`-algebras, in the 2-isomorphism form.**  This is the `halgebra`
argument of `AlgebraicGeometry.Space.existsUnique_thickeningHom_of_isLocallyRinged`: the
structure morphism of `Y'` composed with `α` is 2-isomorphic to the morphism of ringed topoi of
the structure morphism `a' ≫ p` of `X'`. -/
theorem nonempty_smallEtaleTwoIso_derivationModificationHomOfMap_base :
    Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS p)
        (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ))
      (smallEtaleRingedToposHom B S hS (a' ≫ p))) := by
  refine ⟨?_⟩
  rw [smallEtaleComp_derivationModificationHomOfMap_base B S hS Z hZ a' W p a hcompat θ]
  exact smallEtaleRingedToposHomCompTwoIso B S hS a' p

/-- **[Stacks Project, Tag 04D0], with the recovery of morphisms over the base as its only
argument.**  For a morphism `(a, a')` of first order thickenings over `T` and an `𝒪_X`-linear
map `θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}` there is exactly one morphism `b' : X' ⟶ Y'` whose structure
map is `α = (a')^♯ + D`, and the pair `(a, b')` is a morphism of thickenings over `T`.

Setting `b = a` this is the unique morphism of pairs `(b, b')` of the source: conditions (1) and
(2) of [Stacks Project, Tag 0618] are the two displayed equations, and the derivation `D` is
related to `θ` by Equation (0619) because that is how
`AlgebraicGeometry.Space.derivationModificationHomOfMap` is built.

Unlike
`AlgebraicGeometry.Space.existsUnique_hom_of_derivationModification` this takes **no datum** for
the modified structure map: `α` is constructed from `θ`, and its three properties that
[Stacks Project, Tag 05ZN] consumes — that it is locally ringed, that it fits the square and
that it is a map of `𝒪_T`-algebras — are proved above, and the recovery of
morphisms of algebraic spaces from morphisms of their small étale ringed topoi over a base is
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`.  So nothing is assumed. -/
@[stacks 04D0 "the morphism of pairs (b, b') and its uniqueness, for the modified structure map \
alpha = (a')^sharp + D BUILT from theta by Equation 0619: alpha is constructed, and its three \
properties that Stacks 05ZN consumes -- locally ringed, the square, the O_T-algebra condition \
-- are proved outright, as is the recovery of morphisms of algebraic spaces from morphisms of \
their small etale ringed topoi over a base, isRecoveredFromSmallEtale_holds; the uniqueness alone \
is also eq_of_derivationModificationHomOfMap_induces"]
theorem existsUnique_hom_of_derivationModificationHomOfMap
    (hW : IsFirstOrderThickening B S hS Y' W.1) :
    ∃! b' : X' ⟶ Y', InducesSmallEtaleRingedToposHom B S hS b'
        (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ) ∧
      subspaceInclusion B S hS X' Z ≫ b' = a ≫ subspaceInclusion B S hS Y' W ∧
      b' ≫ p = a' ≫ p :=
  existsUnique_thickeningHom_of_isLocallyRinged B S hS (isRecoveredFromSmallEtale_holds B S hS)
    hZ.isThickening hW.isThickening
    (a' ≫ p) p a (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ)
    (derivationModificationHomOfMap_isLocallyRinged B S hS Z hZ a' W p a hcompat θ)
    (nonempty_smallEtaleTwoIso_derivationModificationHomOfMap_comp
      B S hS Z hZ a' W p a hcompat θ)
    (nonempty_smallEtaleTwoIso_derivationModificationHomOfMap_base
      B S hS Z hZ a' W p a hcompat θ)

/-- **The uniqueness half of [Stacks Project, Tag 04D0], with nothing assumed.**  Two morphisms
`b₁', b₂' : X' ⟶ Y'` whose structure maps are both the modification `α = (a')^♯ + D` of the
structure map of `a'` by the derivation attached to an `𝒪_X`-linear map
`θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}` are equal.

This is the "unique" of the source's "there exists a unique morphism of pairs `(b, b')`", and it
needs neither [Stacks Project, Tag 04KL] nor any property of `α`: two morphisms inducing the
same morphism of small étale ringed topoi are 2-isomorphic to one another, and
[Stacks Project, Tag 04M6] identifies them.  Since the source's construction fixes `b = a`,
uniqueness of `b'` is uniqueness of the pair.

The hypotheses are exactly the source's: `X ⊂ X'` and `Y ⊂ Y'` closed subspaces with `X ⊂ X'` of
first order, `(a, a')` a morphism of the pairs, `p` the structure morphism to the base, and `θ`
an `𝒪_X`-linear map `a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}`. -/
@[stacks 04D0 "the uniqueness of the morphism of pairs (b, b'), for the modified structure map \
alpha = (a')^sharp + D built from theta by Equation 0619: no recovery of morphisms over the \
base (Stacks 04KL) and no property of alpha is used, only Stacks 04M6"]
theorem eq_of_derivationModificationHomOfMap_induces (b₁' b₂' : X' ⟶ Y')
    (h₁ : InducesSmallEtaleRingedToposHom B S hS b₁'
      (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ))
    (h₂ : InducesSmallEtaleRingedToposHom B S hS b₂'
      (derivationModificationHomOfMap B S hS Z hZ a' W p a hcompat θ)) :
    b₁' = b₂' :=
  eq_of_inducesCommonSmallEtaleRingedToposHom B S hS b₁' b₂' h₁ h₂

end AlgebraicGeometry.Space

end
