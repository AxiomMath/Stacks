module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The hyperplane restriction sequence after a Serre twist

Let `i : H ⟶ X` be a closed immersion of schemes, let `L` be an invertible `𝒪_X`-module playing
the role of `𝒪(1)`, write `F(d) = F ⊗_{𝒪_X} L^{⊗ d}` and let `𝒢 = i^*ℱ`.  Suppose given a short
exact sequence

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*𝒢 ⟶ 0`

— the conclusion of [Stacks, Tag 08A0].  [Stacks, Tag 0EGK] observes that for every `d ∈ ℤ`
there is a corresponding short exact sequence

`0 ⟶ ℱ(d - 1) ⟶ ℱ(d) ⟶ i_*(𝒢(d)) ⟶ 0`,

because tensoring by `L^{⊗ d}` is an exact functor and because the projection formula
([Stacks, Tag 01E8], here through the closed-immersion case
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`) identifies
`i_*(𝒢(d))` with `i_*𝒢 ⊗_{𝒪_X} L^{⊗ d}`; and that the associated long exact cohomology sequence

`H^j(X, ℱ(d-1)) ⟶ H^j(X, ℱ(d)) ⟶ H^j(H, 𝒢(d)) ⟶ H^{j+1}(X, ℱ(d-1))`

has its third term computed *on `H`*, because a closed immersion is affine and so
[Stacks, Tag 089W] applies.  Finally, on projective space the hyperplane is itself a projective
space and the twists match up: `𝒪_H(d) = i^*𝒪_{ℙⁿ_k}(d)`.

## Main definitions

* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistModule`: the twist
  `ℱ(d) = ℱ ⊗_{𝒪_X} L^{⊗ d}` of an `𝒪_X`-module by an integer power of an invertible module.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso`:
  `f^*(M^{⊗ d}) ≅ (f^*M)^{⊗ d}` in **every integer degree**, extending
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` from the nonnegative ones.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorPowModuleIsoOfIsoInt`: isomorphic
  invertible modules have isomorphic tensor powers in every integer degree.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules` and
  `tensorRightModulesObjIso`: tensoring on the right by an `𝒪_X`-module, as an endofunctor of
  `X.Modules`, and the identification of its value at `ℱ` with the twist `ℱ(d)`.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistedSequence`: **the twisted hyperplane
  restriction sequence** `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ i_*(𝒢(d)) ⟶ 0`, as a `ShortComplex`.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.cohomologyToHyperplaneMap` and
  `cohomologyConnectingMap`: the two maps of the displayed long exact sequence whose target,
  respectively source, is cohomology on `H`.

## Main results

* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistOverIso`: **the Serre twists on
  the hyperplane**, `𝒪_{ℙⁿ⁻¹}(d) ≅ (φ ≫ i)^*𝒪_{ℙⁿ}(d)` for every `d ∈ ℤ`, given the degree-one
  comparison `h089Z`.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistModuleIso`:
  `i^*(ℱ(d)) ≅ (i^*ℱ)(d)`, the twist of a module restricted to the closed subscheme.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pushforwardTwistModuleIso`: **the projection
  formula clause**, `i_*𝒢 ⊗_{𝒪_X} L^{⊗ d} ≅ i_*(𝒢(d))`.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.shortExact_twistedSequence`: **the twisted
  short exact sequence is short exact**, tensoring by an invertible module being an equivalence
  and hence exact.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.cohomologyHyperplaneIso`:
  `H^j(X, i_*(𝒢(d))) ≅ H^j(H, 𝒢(d))`, which is [Stacks, Tag 089W] at the twisted module.
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.exact_cohomology_twistedSequence`: **the long
  exact sequence of the remark**, exact at each of the three displayed spots, with the
  connecting morphism the canonical one of the cohomological `δ`-functor of [Stacks, Tag 071H]
  transported across the comparison of [Stacks, Tag 089W].

[Stacks, Tag 0EGK] itself, for the hyperplanes of `ℙⁿ_k` over an infinite field, is
`AlgebraicGeometry.exists_hyperplane_twistedSequence_cohomology` in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneTwistUnconditional.lean`, which feeds
the results above the hyperplane of [Stacks, Tag 089Z] and the sequence of [Stacks, Tag 08A0].

## Implementation notes

**Everything here is stated for an arbitrary closed immersion `i : H ⟶ X` and an arbitrary
invertible `𝒪_X`-module `L`**, which is the generality the arguments need: none of them uses
that `X` is a projective space, that `H` is a hyperplane or that the untwisted sequence comes
from multiplication by a global section of `𝒪(1)`.  At that generality the degree-one twist
comparison `φ : ℙⁿ⁻¹_k ≅ H` of [Stacks, Tag 089Z] and the untwisted sequence
`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*𝒢 ⟶ 0` of [Stacks, Tag 08A0] are data of the morphism rather than
consequences of it — there is no projective space to apply either tag to — so they are the
arguments `h089Z` and `f`, `g`, `w`, `hS` of the lemmas below.
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneTwistUnconditional.lean` specialises
them to the hyperplanes of `ℙⁿ_k` over an infinite field, where both come from this chapter's own
[Stacks, Tag 089Z] and [Stacks, Tag 08A0], and is where [Stacks, Tag 0EGK]'s sequence clauses
are registered.

**Ampleness-theory spellings are used for the tensor product and the tensor powers.**
`Stacks.RelativeVeryAmple.tensorModules` and `Stacks.Ample.tensorPowModule` are the spellings in
which the multiplication isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a+b)` and the identification
`𝒪(1)^{⊗ d} ≅ 𝒪(d)` of `Constructions/ProjTwistTensorPow.lean` are available; the former is
definitionally `Stacks.RingedSpace.tensorSheaf`, which is where the projection formula and the
associativity constraint `Stacks.SheafOfModules.tensorSheafAssociator` live, so no bridge is
needed.  `isInvertibleModule_schemeModulesPullback` restates Tag 0B8L at
`AlgebraicGeometry.Scheme.Modules.pullback` rather than at the definitionally equal
`RingedSpaceModuleAdjunction.modulePullback`, because instance search does not unfold the
former.

**`twistedSequence` is an `abbrev`, and `tensorRightModulesObjIso` is the identity.**  Tensoring
on the right by `L^{⊗ d}` as a *functor* and the twist `ℱ(d)` as an *object* are the same thing,
but not by the same expression, and a composite one of whose factors is stated at the one
spelling and the other at the other is not type-correct at the transparency `rw` and `simp`
check their rewrites at, which makes those tactics fail on goals that typecheck.  So the
identification is made explicit by `tensorRightModulesObjIso`, used wherever the two meet, and
`twistedSequence` is reducible so that its component projections `.X₂`, `.f`, `.g` are too.

**Cohomology is the right derived global sections of `Stacks.Cohomology.AffineBase`**, the
functor [Stacks, Tag 089W] is stated at, and its long exact sequence is the `δ`-functor of
[Stacks, Tag 071H] obtained from
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, whose functors are that
right derived functor on the nose.  Using one cohomology functor for both halves is what lets
the connecting morphism of the long exact sequence be transported across the Tag 089W
comparison rather than merely compared with it.

## References

* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.Cohomology.AffineBase
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor
  cohomologyDeltaFunctor_functor)
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.HyperplaneTwistSequence

attribute [local instance] HasDerivedCategory.standard

/-! ### Tensoring on the right by an invertible module -/

/-- Tensoring an `𝒪_X`-module on the right by `M`, as an endofunctor of `X.Modules`.  This is
`Stacks.SheafOfModules.TensorPower.tensorRightFunctor` with the sheaf condition on the structure
presheaf of rings of the scheme supplied; on objects it is
`Stacks.RelativeVeryAmple.tensorModules X · M`. -/
abbrev tensorRightModules (X : Scheme.{u}) (M : X.Modules) : X.Modules ⥤ X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)⟩).flip.obj M)

/-- Tensoring on the right by an invertible module preserves zero morphisms: it is an
equivalence, hence a left adjoint. -/
instance tensorRightModules_preservesZeroMorphisms (X : Scheme.{u}) (M : X.Modules)
    [IsInvertibleModule X M] : (tensorRightModules X M).PreservesZeroMorphisms :=
  haveI : (tensorRightModules X M).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X M
  haveI : (tensorRightModules X M).IsLeftAdjoint :=
    ((tensorRightModules X M).asEquivalence.toAdjunction).isLeftAdjoint
  inferInstance

/-- Tensoring on the right by an invertible module preserves finite limits: it is an
equivalence, hence a right adjoint. -/
instance tensorRightModules_preservesFiniteLimits (X : Scheme.{u}) (M : X.Modules)
    [IsInvertibleModule X M] : PreservesFiniteLimits (tensorRightModules X M) :=
  haveI : (tensorRightModules X M).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X M
  haveI : (tensorRightModules X M).IsRightAdjoint :=
    ((tensorRightModules X M).asEquivalence.symm.toAdjunction).isRightAdjoint
  inferInstance

/-- Tensoring on the right by an invertible module preserves finite colimits: it is an
equivalence, hence a left adjoint. -/
instance tensorRightModules_preservesFiniteColimits (X : Scheme.{u}) (M : X.Modules)
    [IsInvertibleModule X M] : PreservesFiniteColimits (tensorRightModules X M) :=
  haveI : (tensorRightModules X M).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X M
  haveI : (tensorRightModules X M).IsLeftAdjoint :=
    ((tensorRightModules X M).asEquivalence.toAdjunction).isLeftAdjoint
  inferInstance

/-- **[Stacks, Tag 0B8L]** at the `AlgebraicGeometry.Scheme.Modules.pullback` spelling: the
pullback of an invertible `𝒪_S`-module along a morphism of schemes is invertible.  This is
`Stacks.InvertiblePullback.isInvertibleModule_pullback`, whose statement uses the definitionally
equal `RingedSpaceModuleAdjunction.modulePullback`; instance search does not unfold
`AlgebraicGeometry.Scheme.Modules.pullback` to reach it. -/
instance isInvertibleModule_schemeModulesPullback {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules)
    [IsInvertibleModule S M] : IsInvertibleModule X ((Scheme.Modules.pullback f).obj M) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback f M

/-! ### Tensor powers in negative degrees -/

/-- **Pullback commutes with the tensor powers of an invertible module in the negative
degrees**, `f^*(M^{⊗ -(k+1)}) ≅ (f^*M)^{⊗ -(k+1)}`.

Both sides are tensor inverses of `(f^*M)^{⊗ (k+1)}`: the right-hand side by the addition law
for the powers, and the left-hand side because `f^*` carries the addition law on `S` to one on
`X` — through [Stacks, Tag 01CD] and `f^*𝒪_S ≅ 𝒪_X` — after the nonnegative-degree case
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` has identified `(f^*M)^{⊗ (k+1)}` with
`f^*(M^{⊗ (k+1)})`.  A tensor inverse is unique up to isomorphism. -/
def pullbackTensorPowModuleNegSuccIso {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules)
    [IsInvertibleModule S M] (k : ℕ) :
    (Scheme.Modules.pullback f).obj (tensorPowModule S M (-((k + 1 : ℕ) : ℤ))) ≅
      tensorPowModule X ((Scheme.Modules.pullback f).obj M) (-((k + 1 : ℕ) : ℤ)) :=
  isoOfTensorUnitIso X
    ((Scheme.Modules.pullback f).obj (tensorPowModule S M (-((k + 1 : ℕ) : ℤ))))
    (tensorPowModule X ((Scheme.Modules.pullback f).obj M) (-((k + 1 : ℕ) : ℤ)))
    (tensorPowModule X ((Scheme.Modules.pullback f).obj M) ((k + 1 : ℕ) : ℤ))
    (tensorModulesMapIso X (Iso.refl _) (pullbackTensorPowModuleIso f M (k + 1)).symm ≪≫
      (pullbackTensorModulesIso f (tensorPowModule S M (-((k + 1 : ℕ) : ℤ)))
        (tensorPowModule S M ((k + 1 : ℕ) : ℤ))).symm ≪≫
      (Scheme.Modules.pullback f).mapIso
        (tensorPowModuleAddIso S M (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) ≪≫
          tensorPowModuleCongr S M (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 by ring) ≪≫
          tensorPowModuleZeroIso S M) ≪≫
      Stacks.RelativeAmple.pullbackUnitModuleIso f)
    (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M)
        (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) ≪≫
      tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
        (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 by ring) ≪≫
      tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M))

/-- **Pullback commutes with the tensor powers of an invertible module in every integer
degree**, `f^*(M^{⊗ d}) ≅ (f^*M)^{⊗ d}`.  The nonnegative degrees are
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` and the negative ones
`pullbackTensorPowModuleNegSuccIso`. -/
@[ega "0 5.4.5" "special case"]
def pullbackTensorPowModuleIntIso {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules)
    [IsInvertibleModule S M] : (d : ℤ) →
    (Scheme.Modules.pullback f).obj (tensorPowModule S M d) ≅
      tensorPowModule X ((Scheme.Modules.pullback f).obj M) d
  | .ofNat k => pullbackTensorPowModuleIso f M k
  | .negSucc k =>
      (Scheme.Modules.pullback f).mapIso
          (tensorPowModuleCongr S M
            (show (Int.negSucc k) = -((k + 1 : ℕ) : ℤ) by push_cast; rfl)) ≪≫
        pullbackTensorPowModuleNegSuccIso f M k ≪≫
        tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
          (show -((k + 1 : ℕ) : ℤ) = (Int.negSucc k) by push_cast; rfl)

/-- **Isomorphic invertible modules have isomorphic tensor powers in the negative degrees.**
Both `N^{⊗ -(k+1)}` and `N'^{⊗ -(k+1)}` are tensor inverses of `N^{⊗ (k+1)}`, the second one
after transporting along the nonnegative-degree case
`Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso`, and a tensor inverse is unique up to
isomorphism. -/
def tensorPowModuleIsoOfIsoNegSucc (X : Scheme.{u}) (N N' : X.Modules)
    [IsInvertibleModule X N] [IsInvertibleModule X N'] (e : N ≅ N') (k : ℕ) :
    tensorPowModule X N (-((k + 1 : ℕ) : ℤ)) ≅
      tensorPowModule X N' (-((k + 1 : ℕ) : ℤ)) :=
  isoOfTensorUnitIso X (tensorPowModule X N (-((k + 1 : ℕ) : ℤ)))
    (tensorPowModule X N' (-((k + 1 : ℕ) : ℤ)))
    (tensorPowModule X N ((k + 1 : ℕ) : ℤ))
    (tensorPowModuleAddIso X N (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) ≪≫
      tensorPowModuleCongr X N (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 by ring) ≪≫
      tensorPowModuleZeroIso X N)
    (tensorModulesMapIso X (Iso.refl _) (tensorPowModuleIsoOfIso X N N' e (k + 1)) ≪≫
      tensorPowModuleAddIso X N' (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) ≪≫
      tensorPowModuleCongr X N' (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 by ring) ≪≫
      tensorPowModuleZeroIso X N')

/-- **Isomorphic invertible modules have isomorphic tensor powers in every integer degree.**
The nonnegative degrees are `Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso` and the negative
ones `tensorPowModuleIsoOfIsoNegSucc`. -/
def tensorPowModuleIsoOfIsoInt (X : Scheme.{u}) (N N' : X.Modules)
    [IsInvertibleModule X N] [IsInvertibleModule X N'] (e : N ≅ N') : (d : ℤ) →
    tensorPowModule X N d ≅ tensorPowModule X N' d
  | .ofNat k => tensorPowModuleIsoOfIso X N N' e k
  | .negSucc k =>
      tensorPowModuleCongr X N (show (Int.negSucc k) = -((k + 1 : ℕ) : ℤ) by push_cast; rfl) ≪≫
        tensorPowModuleIsoOfIsoNegSucc X N N' e k ≪≫
        tensorPowModuleCongr X N' (show -((k + 1 : ℕ) : ℤ) = (Int.negSucc k) by push_cast; rfl)

/-! ### The twists of a module -/

/-- **The `d`-th twist `ℱ(d) = ℱ ⊗_{𝒪_X} L^{⊗ d}`** of an `𝒪_X`-module by the integer tensor
powers ([Stacks, Tag 01CU]) of an invertible module `L`. -/
abbrev twistModule (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] (F : X.Modules)
    (d : ℤ) : X.Modules :=
  tensorModules X F (tensorPowModule X L d)

/-- Reindexing of the twists along an equality of degrees. -/
def twistModuleCongr (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] (F : X.Modules)
    {a b : ℤ} (h : a = b) : twistModule X L F a ≅ twistModule X L F b :=
  eqToIso (by rw [h])

/-- **Twisting twice adds the degrees**, `(ℱ(a))(b) ≅ ℱ(a + b)`: the associativity constraint
of the tensor product of sheaves of modules followed by the addition law for the tensor
powers. -/
def twistTwistIso (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] (F : X.Modules)
    (a b : ℤ) :
    (tensorRightModules X (tensorPowModule X L b)).obj (twistModule X L F a) ≅
      twistModule X L F (a + b) :=
  Stacks.SheafOfModules.tensorSheafAssociator X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F
      (tensorPowModule X L a) (tensorPowModule X L b) ≪≫
    tensorModulesMapIso X (Iso.refl F) (tensorPowModuleAddIso X L a b)

/-! ### The Serre twists on a hyperplane -/

/-- **From degree one to every degree for the twists on a subscheme of `ℙⁿ_S`.**  Let
`i : H ⟶ ℙⁿ_S` be a morphism of schemes with `H` identified with `ℙⁿ⁻¹_S` by `φ`, and let `h089Z`
be an isomorphism exhibiting `𝒪_{ℙⁿ⁻¹}(1)` as the pullback of `𝒪_{ℙⁿ}(1)` along `φ ≫ i`.  Then
the same holds in **every** integer degree: `(φ ≫ i)^*𝒪_{ℙⁿ}(d) ≅ 𝒪_{ℙⁿ⁻¹}(d)`.

The argument runs through `𝒪(1)^{⊗ d} ≅ 𝒪(d)`
(`Stacks.AlgebraicGeometry.ProjTwistTensorPow.tensorPowModuleProjectiveTwistIso`) on both
projective spaces, `pullbackTensorPowModuleIntIso` to move the pullback inside the power, and
`tensorPowModuleIsoOfIsoInt` to apply `h089Z` to the base of the power.

For a hyperplane of `ℙⁿ_k` the degree-one datum `h089Z` is [Stacks, Tag 089Z], and
`AlgebraicGeometry.exists_iso_pullbackTwistOver_zeroScheme` in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneTwistUnconditional.lean` supplies it
from this chapter's form of that tag; that is where the resulting clause of
[Stacks, Tag 0EGK] is registered.

The ambient space is written `ℙ^{m+1}_S` rather than `ℙⁿ_S` with `1 ≤ n`, so that the smaller
projective space is `ℙ^m_S` with no truncated subtraction; the base is an arbitrary scheme `S`,
of which Tag 089Z's `Spec k` is a case. -/
def pullbackTwistOverIso (m : ℕ) (S : Scheme.{u}) {Hy : Scheme.{u}}
    (i : Hy ⟶ projectiveSpaceOver (m + 1) S) (φ : projectiveSpaceOver m S ≅ Hy)
    (h089Z : (Scheme.Modules.pullback (φ.hom ≫ i)).obj (twistOver (m + 1) S 1) ≅
      twistOver m S 1) (d : ℤ) :
    (Scheme.Modules.pullback (φ.hom ≫ i)).obj (twistOver (m + 1) S d) ≅ twistOver m S d :=
  (Scheme.Modules.pullback (φ.hom ≫ i)).mapIso
      (tensorPowModuleProjectiveTwistIso (m + 1) S d).symm ≪≫
    pullbackTensorPowModuleIntIso (φ.hom ≫ i) (twistOver (m + 1) S 1) d ≪≫
    tensorPowModuleIsoOfIsoInt (projectiveSpaceOver m S)
      ((Scheme.Modules.pullback (φ.hom ≫ i)).obj (twistOver (m + 1) S 1))
      (twistOver m S 1) h089Z d ≪≫
    tensorPowModuleProjectiveTwistIso m S d

/-! ### The twisted hyperplane restriction sequence -/

section Sequence

variable {Hy X : Scheme.{u}} (i : Hy ⟶ X) [IsClosedImmersion i]
  (L : X.Modules) [IsInvertibleModule X L] (F : X.Modules) (G : Hy.Modules)

/-- Tensoring on the right by `L^{⊗ d}` is twisting: `(tensorRightModules X (L^{⊗ d})).obj ℱ` is
`ℱ(d)`.  The two are the same object, and this isomorphism is the identity; it exists so that
compositions can be written with the twist as their stated source or target. -/
def tensorRightModulesObjIso (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]
    (A : X.Modules) (d : ℤ) :
    (tensorRightModules X (tensorPowModule X L d)).obj A ≅ twistModule X L A d :=
  Iso.refl _

/-- **[Stacks, Tag 0EGK], the twist of a module restricted to the closed subscheme.**
`i^*(ℱ(d)) ≅ (i^*ℱ)(d)`, the twist on `H` being taken with respect to `i^*L`.  This is
[Stacks, Tag 01CD] for the tensor product followed by `pullbackTensorPowModuleIntIso` for the
tensor power. -/
@[stacks 0EGK "the twist of a module restricted to the hyperplane: i^*(F(d)) = (i^*F)(d)"]
def pullbackTwistModuleIso (d : ℤ) :
    (Scheme.Modules.pullback i).obj (twistModule X L F d) ≅
      twistModule Hy ((Scheme.Modules.pullback i).obj L)
        ((Scheme.Modules.pullback i).obj F) d :=
  pullbackTensorModulesIso i F (tensorPowModule X L d) ≪≫
    tensorModulesMapIso Hy (Iso.refl _) (pullbackTensorPowModuleIntIso i L d)

/-- **[Stacks, Tag 0EGK], the projection formula clause.**
`i_*𝒢 ⊗_{𝒪_X} L^{⊗ d} ≅ i_*(𝒢(d))`, which is what makes the third term of the twisted sequence
the direct image of a twist on `H`.

This is [Stacks, Tag 01E8] at a closed immersion — available with no quasi-coherence hypothesis
as `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` — followed by
`pullbackTensorPowModuleIntIso`, which rewrites `i^*(L^{⊗ d})` as `(i^*L)^{⊗ d}` so that the
twist on `H` is taken with respect to `i^*L`. -/
@[stacks 0EGK "the projection formula clause: i_*(G(d)) = i_*G ⊗ O(d), by [Stacks, Tag 01E8] at \
a closed immersion"]
def pushforwardTwistModuleIso (d : ℤ) :
    (tensorRightModules X (tensorPowModule X L d)).obj
        ((Scheme.Modules.pushforward i).obj G) ≅
      (Scheme.Modules.pushforward i).obj
        (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d) :=
  Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i G
      (tensorPowModule X L d) ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (tensorModulesMapIso Hy (Iso.refl G) (pullbackTensorPowModuleIntIso i L d))

variable (f : twistModule X L F (-1) ⟶ F)
  (g : F ⟶ (Scheme.Modules.pushforward i).obj G) (w : f ≫ g = 0)

include w in
/-- **The twisted restriction sequence** `0 ⟶ ℱ(d - 1) ⟶ ℱ(d) ⟶ i_*(𝒢(d)) ⟶ 0`, as a short
complex.

It is the image of the complex `ℱ(-1) ⟶ ℱ ⟶ i_*𝒢` under tensoring by `L^{⊗ d}`, with
its outer terms rewritten: the first by `twistTwistIso`, which turns `(ℱ(-1))(d)` into
`ℱ(d - 1)`, and the third by `pushforwardTwistModuleIso`, the projection formula.  Short
exactness is `shortExact_twistedSequence`. -/
abbrev twistedSequence (d : ℤ) : ShortComplex X.Modules :=
  ShortComplex.mk
    ((twistTwistIso X L F (-1) d ≪≫
        twistModuleCongr X L F (show (-1 : ℤ) + d = d - 1 by ring)).inv ≫
      (tensorRightModules X (tensorPowModule X L d)).map f ≫
        (tensorRightModulesObjIso X L F d).hom)
    ((tensorRightModulesObjIso X L F d).inv ≫
      (tensorRightModules X (tensorPowModule X L d)).map g ≫
        (pushforwardTwistModuleIso i L G d).hom)
    (by
      have hfg : (tensorRightModules X (tensorPowModule X L d)).map f ≫
          (tensorRightModules X (tensorPowModule X L d)).map g = 0 := by
        rw [← Functor.map_comp, w, Functor.map_zero]
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
        ← Category.assoc ((tensorRightModules X (tensorPowModule X L d)).map f), hfg, zero_comp,
        comp_zero])

/-- The twisted sequence is isomorphic, as a short complex, to the image of the untwisted
sequence under tensoring by `L^{⊗ d}`: that is how its two outer terms were rewritten. -/
def twistedSequenceIso (d : ℤ) :
    (ShortComplex.mk f g w).map (tensorRightModules X (tensorPowModule X L d)) ≅
      twistedSequence i L F G f g w d := by
  let tensorFunctor : X.Modules ⥤ X.Modules := tensorRightModules X (tensorPowModule X L d)
  let first : tensorFunctor.obj (twistModule X L F (-1)) ≅ twistModule X L F (d - 1) :=
    twistTwistIso X L F (-1) d ≪≫
      twistModuleCongr X L F (show (-1 : ℤ) + d = d - 1 by ring)
  let middle : tensorFunctor.obj F ≅ twistModule X L F d := tensorRightModulesObjIso X L F d
  let last : tensorFunctor.obj ((Scheme.Modules.pushforward i).obj G) ≅
      (Scheme.Modules.pushforward i).obj
        (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d) :=
    pushforwardTwistModuleIso i L G d
  refine ShortComplex.isoMk (C := X.Modules)
    (S₁ := (ShortComplex.mk f g w).map (tensorRightModules X (tensorPowModule X L d)))
    (S₂ := twistedSequence i L F G f g w d)
    first middle last ?_ ?_
  · exact first.hom_inv_id_assoc (tensorFunctor.map f ≫ middle.hom)
  · exact middle.hom_inv_id_assoc (tensorFunctor.map g ≫ last.hom)

/-- **Twisting preserves short exactness.**  If `0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*𝒢 ⟶ 0` is short exact, then
so is `0 ⟶ ℱ(d - 1) ⟶ ℱ(d) ⟶ i_*(𝒢(d)) ⟶ 0` for every `d ∈ ℤ`.

This is the argument "tensoring by `𝒪(d)` is an exact functor" of [Stacks, Tag 0EGK]: tensoring
on the right by an invertible module is an equivalence of categories
(`Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule`), hence
preserves finite limits and colimits, hence carries short exact sequences to short exact
sequences; the outer terms are then rewritten by `twistedSequenceIso`.

For a hyperplane of `ℙⁿ_k` the datum `hS` is [Stacks, Tag 08A0], and
`AlgebraicGeometry.exists_hyperplane_twistedSequence_cohomology` in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneTwistUnconditional.lean` supplies it
from this chapter's form of that tag; that is where the resulting clause of
[Stacks, Tag 0EGK] is registered. -/
theorem shortExact_twistedSequence (hS : (ShortComplex.mk f g w).ShortExact) (d : ℤ) :
    (twistedSequence i L F G f g w d).ShortExact :=
  ShortComplex.shortExact_of_iso (twistedSequenceIso i L F G f g w d)
    (hS.map_of_exact (tensorRightModules X (tensorPowModule X L d)))

end Sequence

/-! ### The long exact cohomology sequence -/

section Cohomology

variable {Hy X : Scheme.{u}} (i : Hy ⟶ X) [IsClosedImmersion i]
  (L : X.Modules) [IsInvertibleModule X L] (F : X.Modules) (G : Hy.Modules)

/-- **The cohomology comparison** `H^j(X, i_*(𝒢(d))) ≅ H^j(H, 𝒢(d))` as `Γ(X, ⊤)`-modules, the
right-hand side read through restriction of scalars along `i^♯`.

This is [Stacks, Tag 089W] at the twisted module `𝒢(d)`: a closed immersion is affine, so the
higher direct images vanish and cohomology upstairs is cohomology of the direct image
downstairs.  Its quasi-coherence hypothesis `hG` is that tag's; for `𝒢` the restriction of a
quasi-coherent module it is `AlgebraicGeometry.isQuasicoherent_twistModule_pullback`. -/
def cohomologyHyperplaneIso (d : ℤ)
    (hG : (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d).IsQuasicoherent) (j : ℕ) :
    ((cohomologyDeltaFunctor X).functor j).obj
        ((Scheme.Modules.pushforward i).obj
          (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d)) ≅
      (ModuleCat.restrictScalars i.appTop.hom).obj
        (((cohomologyDeltaFunctor Hy).functor j).obj
          (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d)) :=
  haveI := hG
  (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward i
    (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d) j).symm

variable (f : twistModule X L F (-1) ⟶ F)
  (g : F ⟶ (Scheme.Modules.pushforward i).obj G) (w : f ≫ g = 0)

/-- The map `H^j(X, ℱ(d)) ⟶ H^j(H, 𝒢(d))` of the long exact sequence of the remark: the map
induced by `ℱ(d) ⟶ i_*(𝒢(d))`, followed by the comparison `cohomologyHyperplaneIso` of
[Stacks, Tag 089W]. -/
def cohomologyToHyperplaneMap (d : ℤ)
    (hG : (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d).IsQuasicoherent) (j : ℕ) :
    ((cohomologyDeltaFunctor X).functor j).obj (twistModule X L F d) ⟶
      (ModuleCat.restrictScalars i.appTop.hom).obj
        (((cohomologyDeltaFunctor Hy).functor j).obj
          (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d)) :=
  ((cohomologyDeltaFunctor X).functor j).map (twistedSequence i L F G f g w d).g ≫
    (cohomologyHyperplaneIso i L G d hG j).hom

/-- The connecting map `H^j(H, 𝒢(d)) ⟶ H^{j+1}(X, ℱ(d-1))` of the long exact sequence of the
remark: the comparison `cohomologyHyperplaneIso` of [Stacks, Tag 089W] read backwards, followed
by the canonical connecting morphism of the cohomological `δ`-functor of [Stacks, Tag 071H] at
the twisted short exact sequence. -/
def cohomologyConnectingMap (hS : (ShortComplex.mk f g w).ShortExact) (d : ℤ)
    (hG : (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d).IsQuasicoherent) (j : ℕ) :
    (ModuleCat.restrictScalars i.appTop.hom).obj
        (((cohomologyDeltaFunctor Hy).functor j).obj
          (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d)) ⟶
      ((cohomologyDeltaFunctor X).functor (j + 1)).obj (twistModule X L F (d - 1)) :=
  (cohomologyHyperplaneIso i L G d hG j).inv ≫
    (cohomologyDeltaFunctor X).δ (shortExact_twistedSequence i L F G f g w hS d) j

/-- A morphism pair `f, g` of modules with `f ≫ g = 0` is function-exact once the short complex
`f, g` is isomorphic to an exact one. -/
private theorem function_exact_of_iso_mk {R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
    {A B C : ModuleCat R} {f : A ⟶ B} {g : B ⟶ C} (hfg : f ≫ g = 0)
    (e : S ≅ ShortComplex.mk f g hfg) (h : S.Exact) : Function.Exact f g :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (ShortComplex.mk f g hfg)).1
    (ShortComplex.exact_of_iso e h)

/-- **The long exact cohomology sequence of the twisted sequence.**  For every `d ∈ ℤ` and every
`j ≥ 0` the four-term sequence

`H^j(X, ℱ(d-1)) ⟶ H^j(X, ℱ(d)) ⟶ H^j(H, 𝒢(d)) ⟶ H^{j+1}(X, ℱ(d-1)) ⟶ H^{j+1}(X, ℱ(d))`

is exact at each of its three inner spots.  The first and last maps are induced by
`ℱ(d-1) ⟶ ℱ(d)`, the second is `cohomologyToHyperplaneMap` and the third is
`cohomologyConnectingMap`.

The exactness is that of the long exact sequence of the cohomological `δ`-functor
([Stacks, Tag 071H]) at the twisted short exact sequence `shortExact_twistedSequence`, with the
third term transported along the comparison of [Stacks, Tag 089W]; transporting along an
isomorphism preserves exactness, so the connecting morphism appearing here is the canonical one
read through that comparison.

For a hyperplane of `ℙⁿ_k` the data `hS` and `hG` are [Stacks, Tag 08A0] and the quasi-coherence
of a restricted coherent sheaf, and
`AlgebraicGeometry.exists_hyperplane_twistedSequence_cohomology` in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneTwistUnconditional.lean` supplies
both; that is where [Stacks, Tag 0EGK]'s long exact sequence is registered. -/
@[sga "6 XIII 2.6" "partial"]
theorem exact_cohomology_twistedSequence (hS : (ShortComplex.mk f g w).ShortExact) (d : ℤ)
    (hG : (twistModule Hy ((Scheme.Modules.pullback i).obj L) G d).IsQuasicoherent) (j : ℕ) :
    Function.Exact
        (((cohomologyDeltaFunctor X).functor j).map
          (twistedSequence i L F G f g w d).f)
        (cohomologyToHyperplaneMap i L F G f g w d hG j) ∧
      Function.Exact (cohomologyToHyperplaneMap i L F G f g w d hG j)
        (cohomologyConnectingMap i L F G f g w hS d hG j) ∧
      Function.Exact (cohomologyConnectingMap i L F G f g w hS d hG j)
        (((cohomologyDeltaFunctor X).functor (j + 1)).map
          (twistedSequence i L F G f g w d).f) := by
  have hTex : (twistedSequence i L F G f g w d).ShortExact :=
    shortExact_twistedSequence i L F G f g w hS d
  refine ⟨?_, ?_, ?_⟩
  · have hzero : ((cohomologyDeltaFunctor X).functor j).map
          (twistedSequence i L F G f g w d).f ≫
        cohomologyToHyperplaneMap i L F G f g w d hG j = 0 := by
      simp only [cohomologyToHyperplaneMap]
      rw [← Category.assoc, ← Functor.map_comp, (twistedSequence i L F G f g w d).zero,
        Functor.map_zero, zero_comp]
    refine function_exact_of_iso_mk hzero
      (S := (twistedSequence i L F G f g w d).map ((cohomologyDeltaFunctor X).functor j))
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
          (cohomologyHyperplaneIso i L G d hG j)
          (by simp [-cohomologyDeltaFunctor_functor])
          (by simp [cohomologyToHyperplaneMap, -cohomologyDeltaFunctor_functor]))
        ((cohomologyDeltaFunctor X).exact_map hTex j)
  · have hzero : cohomologyToHyperplaneMap i L F G f g w d hG j ≫
        cohomologyConnectingMap i L F G f g w hS d hG j = 0 := by
      simp only [cohomologyToHyperplaneMap, cohomologyConnectingMap, Category.assoc,
        Iso.hom_inv_id_assoc]
      exact (cohomologyDeltaFunctor X).map_g_δ hTex j
    refine function_exact_of_iso_mk hzero (S := (cohomologyDeltaFunctor X).scδ₁ hTex j)
        (ShortComplex.isoMk (Iso.refl _) (cohomologyHyperplaneIso i L G d hG j) (Iso.refl _)
          (by simp [cohomologyToHyperplaneMap, -cohomologyDeltaFunctor_functor])
          (by simp [cohomologyConnectingMap, -cohomologyDeltaFunctor_functor]))
        ((cohomologyDeltaFunctor X).scδ₁_exact hTex j)
  · have hzero : cohomologyConnectingMap i L F G f g w hS d hG j ≫
        ((cohomologyDeltaFunctor X).functor (j + 1)).map
          (twistedSequence i L F G f g w d).f = 0 := by
      simp only [cohomologyConnectingMap, Category.assoc]
      rw [(cohomologyDeltaFunctor X).δ_map_f hTex j, comp_zero]
    refine function_exact_of_iso_mk hzero (S := (cohomologyDeltaFunctor X).scδ₂ hTex j)
        (ShortComplex.isoMk (cohomologyHyperplaneIso i L G d hG j) (Iso.refl _) (Iso.refl _)
          (by simp [cohomologyConnectingMap, -cohomologyDeltaFunctor_functor])
          (by simp [-cohomologyDeltaFunctor_functor]))
        ((cohomologyDeltaFunctor X).scδ₂_exact hTex j)

end Cohomology

end Stacks.AlgebraicGeometry.HyperplaneTwistSequence

end
