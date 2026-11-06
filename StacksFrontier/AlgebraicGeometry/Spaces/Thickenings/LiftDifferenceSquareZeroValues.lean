module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSquareZeroIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalModuleInverseImageKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison

/-!
# The ideal in which the difference of two lifts takes its values

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X`, let `W₀ ⊆ W` be a closed subspace of a second algebraic space, with inclusion
`j : W₀ ⟶ W`, and let `e₀ : Z ⟶ W₀` be a morphism.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceRestrictedTarget.lean` reads the
comorphism of a morphism `c : X ⟶ W` with `i ≫ c = e₀ ≫ j` as a morphism of sheaves of rings

`j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`

on the small étale site of `W₀`.  Two such morphisms agree after the reduction
`i^{-1}𝒪_X ⟶ 𝒪_Z`, so their sectionwise difference takes its values in the direct image along
`e₀` of the conormal module `𝒞_{Z/X}` — which, by
`AlgebraicGeometry.Space.conormalInverseImageι`, is the kernel of that reduction.

This file assembles that module and its inclusion into the ambient sheaf of rings as a
`Stacks.Sites.SquareZeroValues`, the datum the descent of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean` consumes: an additive
injection of `(e₀)_*𝒞_{Z/X}` into `(e₀)_*(i^{-1}𝒪_X)` compatible with restriction, whose image
has square zero, in a sheaf of rings with commuting sections.

## Main definitions

* `AlgebraicGeometry.Space.restrictedSquareZeroValues`: **the ideal of values**, a
  `Stacks.Sites.SquareZeroValues` on `(e₀)_*𝒞_{Z/X}` with the sheaf of rings
  `AlgebraicGeometry.Space.restrictedThickeningLiftRingSheaf` for its ambient.
* `AlgebraicGeometry.Space.conormalSquareZeroValues`: **the same ideal of values with no direct
  image taken**, a `Stacks.Sites.SquareZeroValues` on `𝒞_{Z/X}` with `i^{-1}𝒪_X` itself for its
  ambient, on the small étale site of `Z`.
* `AlgebraicGeometry.Space.conormalDerivationActionHom`: **a morphism of sheaves of rings
  `φ : 𝒜 ⟶ i^{-1}𝒪_X` modified by a derivation with values in the conormal module**, again a
  morphism of sheaves of rings, on the small étale site of `Z`.  This is
  `Stacks.Sites.derivationActionHom`, which proves the statement at an arbitrary site,
  instantiated at the ideal of values above; no multiplicativity is re-proved.  Its derivation
  is one of `i^{-1}𝒪_X` pulled back along `φ`.
* `AlgebraicGeometry.Space.conormalSourceSquareZeroValues` and
  `AlgebraicGeometry.Space.conormalSourceDerivationActionHom`: the same with the derivation
  taken on the *source* sheaf of rings itself, valued in the conormal module viewed as a module
  over it through `φ`.  This is the more general of the two, being the form a bundled
  `PresheafOfModules.Derivation'` takes once unbundled, and the form
  `PresheafOfModules.Derivation'.precomp` produces.

## Main results

* `AlgebraicGeometry.Space.restrictedThickeningLiftRingSheaf_mul_comm`: the sections of the
  ambient sheaf of rings commute, which is
  `Stacks.Sheaves.ToposPullback.pullback_sections_mul_comm` applied twice over the
  commutativity of the sections of the structure sheaf of `X`.
* `AlgebraicGeometry.Space.preservesFiniteLimits_smallToposMorphismTypeU_pushforward`: the
  direct image of sheaves of sets on the small étale sites is left exact, being a right
  adjoint.  This is what carries the injectivity and the square-zero property of the conormal
  inclusion across the direct image along `e₀`.
* `AlgebraicGeometry.Space.restrictedSquareZeroValues_ι`: the inclusion of the ideal of values
  on sections, which is what the consumers compute with.
* `AlgebraicGeometry.Space.structureRingSheafInverseImage_mul_comm`,
  `AlgebraicGeometry.Space.neg_app_conormalInverseImageι` and
  `AlgebraicGeometry.Space.smul_app_conormalInverseImageι`: the three sectionwise facts about
  `i^{-1}𝒪_X` and the conormal inclusion that the ideal of values on the small étale site of `Z`
  and its derivation action consume — commuting sections, additivity at a negation, and
  linearity read as multiplication in `i^{-1}𝒪_X`.
* `AlgebraicGeometry.Space.conormalDerivationActionHom_app_apply` and
  `AlgebraicGeometry.Space.conormalDerivationActionHom_app_apply_add`: the values of the
  modified morphism, as `φ x − ι (D (φ x))` and, equivalently, as the sum of `φ x` with the
  image of the negated derivation.  `D ↦ −D` is a bijection of the derivation families, so the
  two readings are one statement; the subtraction is the sign convention of
  `Stacks.Sites.derivationActionHom`.
* `AlgebraicGeometry.Space.restrictedStructureSharpReduction_eq`: **the transported comorphism
  of `e₀ ≫ j` is the reduction `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}` followed by the comorphism of `e₀`**,
  so the reduction of the transported comorphism of a lift factors through `j^♯`.
* `Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans_id` and
  `Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans_hom_inv_id`: the morphism of
  inverse-image sheaves of rings induced by a natural transformation is functorial in it, so an
  isomorphism of transporting functors induces an isomorphism.

## Implementation notes

**The inclusion is the direct image of the conormal inclusion, with no transport.**  The direct
image of modules of Stacks 03LU along `e₀` is, by construction, the inverse image of sheaves of
modules of Stacks 03D2 along the direct image of sheaves of sets, followed by restriction of
scalars along the structure map; and restriction of scalars does not change the sections.  So
the sections of `(e₀)_*𝒞_{Z/X}` over an object of the small étale site of `W₀` are literally
those of `Stacks.Sheaves.ToposPullback.pullbackModuleObj` at the conormal module read over
`i^{-1}𝒪_X`, and the inclusion is literally
`Stacks.Sheaves.ToposPullback.pullbackModuleMap` of
`AlgebraicGeometry.Space.conormalInverseImageι`.  No comparison isomorphism of the two
presentations of the direct image is needed.

**Left exactness of the direct image is supplied by name.**  The two properties of the
conormal inclusion which have to cross the direct image — injectivity on sections and the
square-zero property — are transported by
`Stacks.Sheaves.ToposPullback.injective_app_pullbackModuleMap` and
`Stacks.Sheaves.ToposPullback.mul_app_pullbackModuleMap_eq_zero`, both of which ask the
transporting functor to be left exact.  Instance search does not find that for the direct image
of a morphism of topoi on its own, so the instance is registered here and introduced by name at
the one place it is used; this is the same precaution as the named invertibility arguments of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ConormalModuleInverseImageKernel.lean`.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts, whose ideal of values this is.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the direct image of
  modules.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), the morphism
  of small étale topoi.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this datum is
  an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{ww'})]
  {Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)} [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})

/-- The morphism induced by the identity transformation is the identity. -/
theorem pullbackRingSheafMapOfNatTrans_id :
    pullbackRingSheafMapOfNatTrans J O (𝟙 Φ) = 𝟙 (pullbackRingSheaf J Φ O) := by
  refine (CategoryTheory.sheafCompose J (CategoryTheory.forget RingCat.{ww})).map_injective ?_
  rw [ringSheafMap_pullbackRingSheafMapOfNatTrans, CategoryTheory.Functor.map_id]
  rfl

variable {Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)} [PreservesFiniteProducts Φ']

/-- The morphisms induced by the two directions of an isomorphism of transporting functors are
mutually inverse. -/
theorem pullbackRingSheafMapOfNatTrans_hom_inv_id (θ : Φ ≅ Φ') :
    pullbackRingSheafMapOfNatTrans J O θ.hom ≫ pullbackRingSheafMapOfNatTrans J O θ.inv =
      𝟙 (pullbackRingSheaf J Φ O) :=
  (pullbackRingSheafMapOfNatTrans_comp J O θ.hom θ.inv).trans
    ((congrArg (pullbackRingSheafMapOfNatTrans J O) θ.hom_inv_id).trans
      (pullbackRingSheafMapOfNatTrans_id J O))

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sites

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A O : Sheaf J RingCat.{u}} {q : A ⟶ O} {M : SheafOfModules.{u} O}
  (E : SquareZeroValues M) (f : A ⟶ E.ambient)
  (D : ∀ V : Cᵒᵖ, O.obj.obj V →+ M.val.obj V)
  (hmul : ∀ (V : Cᵒᵖ) (s t : O.obj.obj V), D V (s * t) = s • D V t + t • D V s)
  (hmap : ∀ (V W : Cᵒᵖ) (h : V ⟶ W) (s : O.obj.obj V),
    D W (O.obj.map h s) = M.val.map h (D V s))
  (ι_smul : ∀ (V : Cᵒᵖ) (x : A.obj.obj V) (m : M.val.obj V),
    E.ι (q.hom.app V x • m) = f.hom.app V x * E.ι m)

/-- **A section of the ideal of values is nilpotent.**  The ideal has square zero, so its
sections are nilpotent with exponent two.  This is the form the hypothesis of
`Stacks.Thickenings.SquareZeroPerturbation.isLocalHom_of_isNilpotent_sub` — a ring map differing
from a local one by nilpotents is local — asks for. -/
theorem isNilpotent_ι (V : Cᵒᵖ) (m : M.val.obj V) : IsNilpotent (E.ι m) :=
  ⟨2, (pow_two _).trans (E.mul_ι_eq_zero m m)⟩

/-- **The difference of the lift and the derivation-modified lift is nilpotent on sections.**
The difference is `ι (D (q x))`, a section of the square-zero ideal of values. -/
theorem isNilpotent_sub_derivationActionHom_app_apply (V : Cᵒᵖ) (x : A.obj.obj V) :
    IsNilpotent (f.hom.app V x -
      (derivationActionHom E f D hmul hmap ι_smul).hom.app V x) := by
  rw [derivationActionHom_app_apply, sub_sub_cancel]
  exact isNilpotent_ι E V _

/-- **A unit modulo the square-zero ideal of values is a unit.**  A section of `𝒜` is invertible
under the derivation-modified lift exactly when it is invertible under the original lift: the two
images differ by a section of the square-zero ideal, and a unit plus a nilpotent is a unit
(`IsNilpotent.isUnit_add_right_of_commute`, applicable because the sections of the ambient sheaf
of rings commute).

This is the sectionwise half of "the derivation sum is locally ringed".  It is *not* the locally
ringed condition itself, which by [Stacks Project, Tag 04HA] is cartesianness of the units square
and is read at the fibres of the site, not at its sections; that step is
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isNilpotent_sub_fSharpInverseImage`. -/
theorem isUnit_derivationActionHom_app_apply_iff (V : Cᵒᵖ) (x : A.obj.obj V) :
    IsUnit ((derivationActionHom E f D hmul hmap ι_smul).hom.app V x) ↔
      IsUnit (f.hom.app V x) := by
  have hn := isNilpotent_ι E V (D V (q.hom.app V x))
  rw [derivationActionHom_app_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using hn.isUnit_add_right_of_commute h (E.ambient_mul_comm _ _)
  · simpa [neg_add_eq_sub] using hn.neg.isUnit_add_right_of_commute h (E.ambient_mul_comm _ _)

section Transport

variable {M' : SheafOfModules.{u} O}

/-- **An invertible morphism of sheaves of rings is injective on sections.**  Its inverse is a
left inverse on the sections over every object.

Stated over an abstract site: the two steps are `rfl` at a composite and at an identity, and the
kernel checks them here once rather than at the geometric terms they are used at. -/
theorem injective_app_of_isIso {O₁ O₂ : Sheaf J RingCat.{u}} (u : O₁ ⟶ O₂) (hu : IsIso u)
    (V : Cᵒᵖ) : Function.Injective (u.hom.app V) :=
  Function.LeftInverse.injective (g := (inv u).hom.app V) fun y =>
    congrArg (fun g : O₁ ⟶ O₁ => g.hom.app V y) (IsIso.hom_inv_id u)

/-- **The ideal of values read in a larger ambient sheaf of rings.**  If the ambient sheaf of
rings of a `Stacks.Sites.SquareZeroValues` maps into a second sheaf of rings `𝒪'` by a morphism
`θ` which is injective on sections, and the sections of `𝒪'` commute, then the module of values
is a square-zero ideal of `𝒪'` as well, included by `θ ∘ ι`.

All four fields are formal: a composite of injections is an injection, `θ` commutes with
restriction because it is a morphism of sheaves, and `θ (ι m) * θ (ι m') = θ (ι m * ι m') = 0`
because `θ` is multiplicative.  Nothing is assumed of `θ` beyond injectivity on sections — in
particular `𝒪'` is *not* required to be the image of the ambient sheaf.

This is the transport an isomorphism of ringed topoi supplies: for `θ` the inverse of the unit
`𝒪_X ⟶ i_*i^{-1}𝒪_X` of a thickening it carries an ideal of `i_*i^{-1}𝒪_X` to an ideal of
`𝒪_X`, which is how the conormal ideal of a first order thickening becomes an ideal of the
structure sheaf of the ambient space; see
`AlgebraicGeometry.Space.conormalAmbientSquareZeroValues`. -/
def SquareZeroValues.ofInjectiveHom (E : SquareZeroValues M') {O' : Sheaf J RingCat.{u}}
    (θ : E.ambient ⟶ O') (hθ : ∀ V : Cᵒᵖ, Function.Injective (θ.hom.app V))
    (hcomm : ∀ {V : Cᵒᵖ} (s t : O'.obj.obj V), s * t = t * s) :
    SquareZeroValues M' where
  ambient := O'
  ambient_mul_comm {V} s t := hcomm s t
  ι {V} := (θ.hom.app V).hom.toAddMonoidHom.comp E.ι
  ι_injective {_} := fun _ _ h => E.ι_injective (hθ _ h)
  ι_map {V W} h m := by
    change θ.hom.app W (E.ι (M'.val.map h m)) = O'.obj.map h (θ.hom.app V (E.ι m))
    rw [E.ι_map]
    exact NatTrans.naturality_apply θ.hom h (E.ι m)
  mul_ι_eq_zero {V} m m' := by
    change (θ.hom.app V).hom (E.ι m) * (θ.hom.app V).hom (E.ι m') = 0
    rw [← map_mul, E.mul_ι_eq_zero, map_zero]

/-- The inclusion of `Stacks.Sites.SquareZeroValues.ofInjectiveHom` on sections. -/
theorem SquareZeroValues.ofInjectiveHom_ι (E : SquareZeroValues M') {O' : Sheaf J RingCat.{u}}
    (θ : E.ambient ⟶ O') (hθ : ∀ V : Cᵒᵖ, Function.Injective (θ.hom.app V))
    (hcomm : ∀ {V : Cᵒᵖ} (s t : O'.obj.obj V), s * t = t * s) {V : Cᵒᵖ} (m : M'.val.obj V) :
    (E.ofInjectiveHom θ hθ hcomm).ι m =
      (show ToType (O'.obj.obj V) from θ.hom.app V (E.ι m)) := rfl

/-- **The ideal of values read across an isomorphism of the ambient sheaf of rings.**  An
invertible morphism of sheaves of rings `u : 𝒪' ⟶ 𝒜` identifies `𝒪'` with the ambient sheaf of
rings of a `Stacks.Sites.SquareZeroValues`, and the module of values is then a square-zero ideal
of `𝒪'`, included by `u⁻¹ ∘ ι`.

This is `Stacks.Sites.SquareZeroValues.ofInjectiveHom` at the inverse of `u`, which is injective
on sections by `Stacks.Sites.injective_app_of_isIso`.  The inverse is formed *here*, over an
abstract site, so that no consumer has to: `CategoryTheory.inv` has no exposed body, so the
equation identifying a named inverse with `inv u` is not available downstream.

The hypothesis `hcomm` is not derived from the commutativity of the sections of `E.ambient`,
although it follows: in the geometric instance the sections of `𝒪'` are the sections of a
structure sheaf and their commutativity is proved. -/
def SquareZeroValues.ofIsoAmbient (E : SquareZeroValues M') {O' : Sheaf J RingCat.{u}}
    (u : O' ⟶ E.ambient) (hu : IsIso u)
    (hcomm : ∀ {V : Cᵒᵖ} (s t : O'.obj.obj V), s * t = t * s) :
    SquareZeroValues M' :=
  letI := hu
  E.ofInjectiveHom (inv u) (fun V => injective_app_of_isIso (inv u) inferInstance V) hcomm

/-- **The inclusion of `Stacks.Sites.SquareZeroValues.ofIsoAmbient`, characterised by the
isomorphism.**  Composing it with `u` returns the given inclusion, which pins it down since `u`
is injective on sections.  Stated this way rather than as `u⁻¹ ∘ ι` because `CategoryTheory.inv`
has no exposed body. -/
theorem SquareZeroValues.app_ofIsoAmbient_ι (E : SquareZeroValues M')
    {O' : Sheaf J RingCat.{u}} (u : O' ⟶ E.ambient) (hu : IsIso u)
    (hcomm : ∀ {V : Cᵒᵖ} (s t : O'.obj.obj V), s * t = t * s) {V : Cᵒᵖ}
    (m : M'.val.obj V) :
    u.hom.app V ((E.ofIsoAmbient u hu hcomm).ι m) = E.ι m :=
  congrArg (fun g : E.ambient ⟶ E.ambient => g.hom.app V (E.ι m)) (IsIso.inv_hom_id u)

/-- **The ideal of values read over a smaller base sheaf of rings.**  Restriction of scalars
along `ψ : 𝒪'' ⟶ 𝒪` does not change the sections of a sheaf of modules, nor its restriction
maps, so the four fields of a `Stacks.Sites.SquareZeroValues` on `M` are literally the four
fields of one on `(SheafOfModules.restrictScalars ψ).obj M`, with the same ambient sheaf of
rings and the same inclusion.

This is what lets a derivation of the *source* sheaf of rings of a lift act on it, the module of
values being viewed over that source through the lift. -/
def SquareZeroValues.restrictScalars (E : SquareZeroValues M') {O'' : Sheaf J RingCat.{u}}
    (ψ : O'' ⟶ O) : SquareZeroValues ((SheafOfModules.restrictScalars ψ).obj M') where
  ambient := E.ambient
  ambient_mul_comm {_} s t := E.ambient_mul_comm s t
  ι {_} := E.ι
  ι_injective {_} := E.ι_injective
  ι_map {_ _} h m := E.ι_map h m
  mul_ι_eq_zero {_} m m' := E.mul_ι_eq_zero m m'

/-- The inclusion of `Stacks.Sites.SquareZeroValues.restrictScalars` is the given one. -/
theorem SquareZeroValues.restrictScalars_ι (E : SquareZeroValues M') {O'' : Sheaf J RingCat.{u}}
    (ψ : O'' ⟶ O) {V : Cᵒᵖ}
    (m : ((SheafOfModules.restrictScalars ψ).obj M').val.obj V) :
    (E.restrictScalars ψ).ι m = E.ι m := rfl

end Transport

end Stacks.Sites

namespace AlgebraicGeometry.Space

/-- Cancelling the last two factors of a four-fold composite against their inverses. -/
private theorem comp_eq_of_cancel {C : Type*} [Category C] {P Q R₁ R₂ R₃ : C}
    (s : P ⟶ Q) (u : Q ⟶ R₁) (k : R₁ ⟶ R₂) (n : R₂ ⟶ R₃) (n' : R₃ ⟶ R₂) (k' : R₂ ⟶ R₁)
    (hn : n ≫ n' = 𝟙 R₂) (hk : k ≫ k' = 𝟙 R₁) :
    (s ≫ u ≫ k ≫ n) ≫ n' ≫ k' = s ≫ u := by
  simp [reassoc_of% hn, hk]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))


set_option synthInstance.maxHeartbeats 400000 in
/-- The sections of `i^{-1}𝒪_X` over any object of the small étale site of `Z` commute. -/
private theorem inverseImage_structureRingSheaf_mul_comm
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (s t : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)).obj.obj V) :
    s * t = t * s :=
  pullback_sections_mul_comm (R := structureRingSheaf B S hS X)
    (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage
    (ringSheaf_mul_comm_smallEtaleRingedSite B S hS X) V s t

/-- The sections of the ambient sheaf of rings commute. -/
theorem restrictedThickeningLiftRingSheaf_mul_comm
    {V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (s t : (restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀).obj.obj V) :
    s * t = t * s :=
  pullback_sections_mul_comm
    (R := structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
    (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
    (smallToposMorphismTypeU B S hS e₀).pushforward
    (inverseImage_structureRingSheaf_mul_comm B S hS Z) V s t

/-- **The transported comorphism of `e₀ ≫ j` is the reduction `j^♯` followed by the comorphism
of `e₀`.**  Both are morphisms `j^{-1}𝒪_W ⟶ (e₀)_*𝒪_Z`, and they are adjunct to one and the
same morphism `𝒪_W ⟶ j_*((e₀)_*𝒪_Z)`: for the first that is the defining one, and for the
second it is the comorphism of the composite `e₀ ≫ j`, by [Stacks Project, Tag 03G8]'s
compatibility with composition and the adjointness of the two forms of the structure map.

This is what identifies the reduction of the transported comorphism of a lift — which
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_reduction` computes as
`AlgebraicGeometry.Space.restrictedStructureSharpReduction` — with a morphism factoring through
the reduction `j^♯`, so that the `𝒪_{W₀}`-action on the ideal of values is the action through
the lift. -/
theorem restrictedStructureSharpReduction_eq :
    restrictedStructureSharpReduction B S hS Z W₀ e₀ =
      structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀) ≫
        structureSharp B S hS e₀ := by
  have h1 := ringImageAdjunction_homEquiv_apply
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
    (structureRingSheaf B S hS W)
    (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
      (smallToposMorphismTypeU B S hS e₀).pushforward
      (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)))
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀) ≫
      structureSharp B S hS e₀)
  have hA := congrArg (fun m => ringUnit (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS W W₀)) (structureRingSheaf B S hS W) ≫ m)
    ((pushforwardRingFunctor
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).map_comp
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀))
      (structureSharp B S hS e₀))
  have hC := congrArg (fun m => m ≫ (pushforwardRingFunctor
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).map
      (structureSharp B S hS e₀))
    (ringUnit_comp_map_structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS W W₀))
  have hD := (comp_eq_of_cancel _ _ _ _ _ _
      (pullbackRingSheafMapOfNatTrans_hom_inv_id
        (SmallEtale.topology B S hS W.1)
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
        (smallToposMorphismTypeU_comp B S hS e₀ (subspaceInclusion B S hS W W₀)))
      ((pullbackRingSheafComp (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS e₀).pushforward
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward
        (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).hom_inv_id)).symm.trans
    (congrArg (fun m => m ≫ pushforwardRingSheafCompInv B S hS e₀
        (subspaceInclusion B S hS W W₀)
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)))
      (structureSharp_comp B S hS e₀ (subspaceInclusion B S hS W W₀)))
  exact (Equiv.symm_apply_eq _).2
    (h1.trans (hA.trans ((Category.assoc _ _ _).symm.trans (hC.trans hD)))).symm


/-- **The direct image of sheaves of sets on the small étale sites is left exact**, being the
right adjoint half of the morphism of topoi of [Stacks Project, Tag 03G2], part (3). -/
instance preservesFiniteLimits_smallToposMorphismTypeU_pushforward
    {V₁ V₂ : AlgebraicSpaces B S hS} (f : V₁ ⟶ V₂) :
    PreservesFiniteLimits (smallToposMorphismTypeU B S hS f).pushforward :=
  haveI : PreservesLimitsOfSize.{0, 0} (smallToposMorphismTypeU B S hS f).pushforward :=
    (smallToposMorphismTypeU B S hS f).adj.rightAdjoint_preservesLimits
  ⟨fun _ _ _ => inferInstance⟩

variable (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- The ideal of values of the difference of two lifts. -/
def restrictedSquareZeroValues :
    Stacks.Sites.SquareZeroValues
      ((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)) :=
  haveI := preservesFiniteLimits_smallToposMorphismTypeU_pushforward B S hS e₀
  { ambient := restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀
    ambient_mul_comm := restrictedThickeningLiftRingSheaf_mul_comm B S hS Z W₀ e₀
    ι := fun {V} => ((pullbackModuleMap (SmallEtale.topology B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (smallToposMorphismTypeU B S hS e₀).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
        (conormalInverseImageι B S hS Z hZ)).val.app V).hom.toAddMonoidHom
    ι_injective := fun {V} =>
      injective_app_pullbackModuleMap
        (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (smallToposMorphismTypeU B S hS e₀).pushforward
        (conormalInverseImageι B S hS Z hZ) V
        (conormalInverseImageι_injective B S hS Z hZ)
    ι_map := fun {_ _} h m =>
      PresheafOfModules.naturality_apply
        (pullbackModuleMap (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
          (conormalInverseImageι B S hS Z hZ)).val h m
    mul_ι_eq_zero := fun {V} m m' =>
      mul_app_pullbackModuleMap_eq_zero
        (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (smallToposMorphismTypeU B S hS e₀).pushforward
        (conormalInverseImageι B S hS Z hZ) V
        (mul_app_conormalInverseImageι_eq_zero B S hS Z hZ) m m' }

/-- **The inclusion of the ideal of values on sections**: the direct image along `e₀` of the
inclusion of the conormal module into `i^{-1}𝒪_X`. -/
theorem restrictedSquareZeroValues_ι
    {V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (m : ((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)).val.obj V) :
    (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι m =
      ((pullbackModuleMap (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
          (conormalInverseImageι B S hS Z hZ)).val.app V).hom m :=
  rfl

/-! ### The conormal module as a square-zero ideal on the small étale site of the thickening -/

/-- **The sections of `i^{-1}𝒪_X` commute.**  This is
`Stacks.Sheaves.ToposPullback.pullback_sections_mul_comm` over the commutativity of the sections
of the structure sheaf of `X`; it is the inner half of
`AlgebraicGeometry.Space.restrictedThickeningLiftRingSheaf_mul_comm`, named here because the
ideal of values on the small étale site of `Z` itself needs it on its own. -/
theorem structureRingSheafInverseImage_mul_comm
    {V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (s t : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS X Z)).obj.obj V) :
    s * t = t * s :=
  inverseImage_structureRingSheaf_mul_comm B S hS Z V s t

/-- **The inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` carries a negation to a negation on sections.**  This
is the additivity of `AlgebraicGeometry.Space.conormalInverseImageι`, read at the sections of
`i^{-1}𝒪_X`.

It is stated on the conormal inclusion itself rather than derived from the ideal of values where
it is used: the additive map of `AlgebraicGeometry.Space.conormalSquareZeroValues` has the
ambient sheaf of rings behind a structure projection, and resolving the additive-group instance
through that projection is a `whnf` timeout at the sections of the small étale structure
sheaf. -/
theorem neg_app_conormalInverseImageι (hZ : IsFirstOrderThickening B S hS X Z.1)
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (m : ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)).val.obj V) :
    (show ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z)).obj.obj V) from
        (conormalInverseImageι B S hS Z hZ).val.app V (-m)) =
      -(show ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z)).obj.obj V) from
        (conormalInverseImageι B S hS Z hZ).val.app V m) :=
  map_neg ((conormalInverseImageι B S hS Z hZ).val.app V).hom m

/-- **The inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` is linear on sections**, read with the scalar action
written as multiplication in `i^{-1}𝒪_X`.  This is the `i^{-1}𝒪_X`-linearity of
`AlgebraicGeometry.Space.conormalInverseImageι` together with the fact that the scalar action on
`i^{-1}𝒪_X` as a module over itself is its multiplication. -/
theorem smul_app_conormalInverseImageι (hZ : IsFirstOrderThickening B S hS X Z.1)
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (r : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)).obj.obj V)
    (m : ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)).val.obj V) :
    (show ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z)).obj.obj V) from
        (conormalInverseImageι B S hS Z hZ).val.app V (r • m)) =
      r * (show ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z)).obj.obj V) from
        (conormalInverseImageι B S hS Z hZ).val.app V m) :=
  ((conormalInverseImageι B S hS Z hZ).val.app V).hom.map_smul r m

/-- **The conormal module of a first-order thickening, as a square-zero ideal of `i^{-1}𝒪_X` on
the small étale site of `Z`.**  This is the `Stacks.Sites.SquareZeroValues` datum of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean` assembled out of
`AlgebraicGeometry.Space.conormalInverseImageι` with **no** direct image taken: the ambient
sheaf of rings is `i^{-1}𝒪_X` itself, rather than its direct image along a further morphism as
in `AlgebraicGeometry.Space.restrictedSquareZeroValues`.

All four fields are proved statements about the conormal inclusion: it is injective on sections,
it commutes with restriction, and its image has square zero. -/
def conormalSquareZeroValues (hZ : IsFirstOrderThickening B S hS X Z.1) :
    Stacks.Sites.SquareZeroValues
      ((SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)) where
  ambient := structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)
  ambient_mul_comm := structureRingSheafInverseImage_mul_comm B S hS Z
  ι {V} := ((conormalInverseImageι B S hS Z hZ).val.app V).hom.toAddMonoidHom
  ι_injective {V} := conormalInverseImageι_injective B S hS Z hZ V
  ι_map {_ _} h m := conormalInverseImageι_val_app_map B S hS Z hZ h m
  mul_ι_eq_zero {V} m m' := mul_app_conormalInverseImageι_eq_zero B S hS Z hZ V m m'

/-- The inclusion of the ideal of values of
`AlgebraicGeometry.Space.conormalSquareZeroValues` is the conormal inclusion on sections. -/
theorem conormalSquareZeroValues_ι (hZ : IsFirstOrderThickening B S hS X Z.1)
    {V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (m : ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)).val.obj V) :
    (conormalSquareZeroValues B S hS Z hZ).ι m =
      (show ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z)).obj.obj V) from
        (conormalInverseImageι B S hS Z hZ).val.app V m) :=
  rfl

/-! ### A morphism of sheaves of rings plus a derivation into the conormal module -/

section DerivationAction

variable {A : Sheaf (SmallEtale.topology B S hS
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) RingCat.{u}}
  (hZ : IsFirstOrderThickening B S hS X Z.1)
  (φ : A ⟶ structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
  (D : ∀ V : (SmallEtale B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ,
    (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS X Z)).obj.obj V →+
      ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)).val.obj V)
  (hmul : ∀ (V : (SmallEtale B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (s t : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS X Z)).obj.obj V),
    D V (s * t) = s • D V t + t • D V s)
  (hmap : ∀ (V W : (SmallEtale B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ) (h : V ⟶ W)
    (s : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS X Z)).obj.obj V),
    D W ((structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS X Z)).obj.map h s) =
      ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj
        (conormalModule B S hS X Z)).val.map h (D V s))

/-- **A morphism of sheaves of rings into `i^{-1}𝒪_X`, modified by a derivation with values in
the conormal module, is again a morphism of sheaves of rings**, on the small étale site of `Z`.

For a morphism of sheaves of rings `φ : 𝒜 ⟶ i^{-1}𝒪_X` and a derivation `D` of `i^{-1}𝒪_X` with
values in `𝒞_{Z/X}`, the sectionwise combination `x ↦ φ x − ι (D (φ x))` is again a morphism of
sheaves of rings `𝒜 ⟶ i^{-1}𝒪_X`.  Multiplicativity is where the square-zero condition on the
conormal module is spent, on the cross term.  Since `D ↦ −D` is a bijection of the derivation
families, this is equally the statement that the *sum* of a morphism of sheaves of rings and a
derivation into a square-zero ideal is a morphism of sheaves of rings; that reading is
`AlgebraicGeometry.Space.conormalDerivationActionHom_app_apply_add`.

**Nothing about multiplicativity is proved here.**  `Stacks.Sites.derivationActionHom` proves
the statement at an *arbitrary* site, hence in particular at the small étale site of an
algebraic space; what this adds is the instantiation at the conormal module, which needs the
conormal inclusion of `AlgebraicGeometry.Space.conormalInverseImageι` to be a square-zero ideal
of `i^{-1}𝒪_X` on the small étale site of `Z`
(`AlgebraicGeometry.Space.conormalSquareZeroValues`) and its linearity read as multiplication in
`i^{-1}𝒪_X` (`AlgebraicGeometry.Space.smul_app_conormalInverseImageι`).  The quotient map and
the lift are both taken to be `φ`, so the derivation is pulled back along `φ` itself.

The sign convention is that of `Stacks.Sites.derivationActionHom`, namely `f − ι ∘ D ∘ q`, so
that the difference of a pair of lifts is `D ∘ q` on the nose.

**No `@[stacks]` attribute.**  The statement is a step inside the proofs of
[Stacks Project, Tag 02H5] and [Stacks Project, Tag 07XW] rather than a clause of either at the
tag's own hypotheses: it carries the extra data of a first-order thickening of algebraic spaces
presented as a closed subspace, of a morphism of sheaves of rings `φ` into `i^{-1}𝒪_X`, and of
the derivation as an explicit family rather than a bundled one. -/
def conormalDerivationActionHom :
    A ⟶ structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z) :=
  Stacks.Sites.derivationActionHom (q := φ) (conormalSquareZeroValues B S hS Z hZ) φ D hmul hmap
    (fun V x m => smul_app_conormalInverseImageι B S hS Z hZ V (φ.hom.app V x) m)

/-- **The value of `AlgebraicGeometry.Space.conormalDerivationActionHom` on sections.**  A
morphism of sheaves of rings whose type does not record its values asserts nothing by itself;
this is what pins it. -/
theorem conormalDerivationActionHom_app_apply
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : A.obj.obj V) :
    (conormalDerivationActionHom B S hS Z hZ φ D hmul hmap).hom.app V x =
      φ.hom.app V x -
        (show ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS X Z)).obj.obj V) from
          (conormalInverseImageι B S hS Z hZ).val.app V (D V (φ.hom.app V x))) :=
  rfl

/-- **The sum reading of `AlgebraicGeometry.Space.conormalDerivationActionHom`**: the modified
morphism is `φ` *plus* the image under the conormal inclusion of the derivation `−D` evaluated
at `φ x`.  As `D` ranges over the derivation families so does `−D`, so this is the statement
that a map of sheaves of rings plus a derivation with values in the square-zero conormal ideal
is again a map of sheaves of rings, on the small étale site of `Z`. -/
theorem conormalDerivationActionHom_app_apply_add
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : A.obj.obj V) :
    (conormalDerivationActionHom B S hS Z hZ φ D hmul hmap).hom.app V x =
      φ.hom.app V x +
        (show ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS X Z)).obj.obj V) from
          (conormalInverseImageι B S hS Z hZ).val.app V (-(D V (φ.hom.app V x)))) := by
  rw [neg_app_conormalInverseImageι B S hS Z hZ V (D V (φ.hom.app V x)), ← sub_eq_add_neg,
    conormalDerivationActionHom_app_apply]

/-- **A unit modulo the conormal ideal is a unit**, for
`AlgebraicGeometry.Space.conormalDerivationActionHom`.  A section of `𝒜` has invertible image
under the modified morphism exactly when it has invertible image under `φ`, the two differing by
a section of the square-zero conormal ideal.  This is
`Stacks.Sites.isUnit_derivationActionHom_app_apply_iff` instantiated at
`AlgebraicGeometry.Space.conormalSquareZeroValues`; no new algebra is involved. -/
theorem isUnit_conormalDerivationActionHom_app_apply_iff
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : A.obj.obj V) :
    IsUnit ((conormalDerivationActionHom B S hS Z hZ φ D hmul hmap).hom.app V x) ↔
      IsUnit (φ.hom.app V x) :=
  Stacks.Sites.isUnit_derivationActionHom_app_apply_iff (q := φ)
    (conormalSquareZeroValues B S hS Z hZ) φ D hmul hmap
    (fun W y m => smul_app_conormalInverseImageι B S hS Z hZ W (φ.hom.app W y) m) V x

end DerivationAction

/-! ### A derivation of the source sheaf of rings -/

section SourceDerivation

variable {A : Sheaf (SmallEtale.topology B S hS
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) RingCat.{u}}
  (hZ : IsFirstOrderThickening B S hS X Z.1)
  (φ : A ⟶ structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))

/-- **The conormal module as a square-zero ideal of `i^{-1}𝒪_X`, read over the source sheaf of
rings `𝒜` of a morphism `φ : 𝒜 ⟶ i^{-1}𝒪_X`.**  This is
`AlgebraicGeometry.Space.conormalSquareZeroValues` with one further restriction of scalars along
`φ`; restriction of scalars does not change the sections, so the four fields are the same
statements about the conormal inclusion.

It is what lets a derivation of `𝒜` itself — rather than one of `i^{-1}𝒪_X` pulled back along
`φ` — act on `φ`. -/
def conormalSourceSquareZeroValues :
    Stacks.Sites.SquareZeroValues
      ((SheafOfModules.restrictScalars φ).obj
        ((SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z))) :=
  (conormalSquareZeroValues B S hS Z hZ).restrictScalars φ

variable (D : ∀ V : (SmallEtale B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ,
    A.obj.obj V →+
      ((SheafOfModules.restrictScalars φ).obj
        ((SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj
          (conormalModule B S hS X Z))).val.obj V)
  (hmul : ∀ (V : (SmallEtale B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ) (s t : A.obj.obj V),
    D V (s * t) = s • D V t + t • D V s)
  (hmap : ∀ (V W : (SmallEtale B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ) (h : V ⟶ W) (s : A.obj.obj V),
    D W (A.obj.map h s) =
      ((SheafOfModules.restrictScalars φ).obj
        ((SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj
          (conormalModule B S hS X Z))).val.map h (D V s))

/-- **A morphism of sheaves of rings `φ : 𝒜 ⟶ i^{-1}𝒪_X` plus a derivation of `𝒜` with values in
the conormal module is again a morphism of sheaves of rings**, on the small étale site of `Z`.

Here `D` is a derivation of the *source* sheaf of rings `𝒜`, with values in `𝒞_{Z/X}` viewed as
an `𝒜`-module through `φ`; the Leibniz rule `hmul` is read with that action.  This is the form a
bundled `PresheafOfModules.Derivation'` of `𝒜` takes once unbundled, and in particular the form
produced by `PresheafOfModules.Derivation'.precomp` out of a derivation of `i^{-1}𝒪_X` or of
`𝒪_Z`.  It is more general than
`AlgebraicGeometry.Space.conormalDerivationActionHom`, whose derivation is one of `i^{-1}𝒪_X`
pulled back along `φ`: not every derivation of `𝒜` factors through one of `i^{-1}𝒪_X`.

As with `AlgebraicGeometry.Space.conormalDerivationActionHom`, no multiplicativity is proved
here; this is `Stacks.Sites.derivationActionHom` at an arbitrary site, instantiated at
`AlgebraicGeometry.Space.conormalSourceSquareZeroValues` with the quotient map taken to be the
identity of `𝒜`, so that the derivation is used as it stands. -/
def conormalSourceDerivationActionHom :
    A ⟶ structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z) :=
  Stacks.Sites.derivationActionHom (q := 𝟙 A) (conormalSourceSquareZeroValues B S hS Z hZ φ) φ
    D hmul hmap
    (fun V x m => smul_app_conormalInverseImageι B S hS Z hZ V (φ.hom.app V x) m)

/-- **The value of `AlgebraicGeometry.Space.conormalSourceDerivationActionHom` on sections.** -/
theorem conormalSourceDerivationActionHom_app_apply
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : A.obj.obj V) :
    (conormalSourceDerivationActionHom B S hS Z hZ φ D hmul hmap).hom.app V x =
      φ.hom.app V x -
        (show ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS X Z)).obj.obj V) from
          (conormalInverseImageι B S hS Z hZ).val.app V (D V x)) :=
  rfl

/-- **A unit modulo the conormal ideal is a unit**, for
`AlgebraicGeometry.Space.conormalSourceDerivationActionHom` — the variant whose derivation is one
of the *source* sheaf of rings `𝒜`.

**This is the variant [Stacks Project, Tag 07XW] needs.**  The modified structure map of
[Stacks Project, Tag 04D0] is `α = (a')^♯ + D` on `f^{-1}𝒪_{Y'}`, and `D = d_{Y/T} ∘ θ` is
evaluated on the sections of that source sheaf, not on the sections of the target `𝒪_{X'}`; as a
family indexed by the sections of `𝒜` it is a derivation of `𝒜` with values in `𝒞_{X/X'}` viewed
as an `𝒜`-module through `(a')^♯`, which is
`AlgebraicGeometry.Space.conormalSourceDerivationActionHom` and not
`AlgebraicGeometry.Space.conormalDerivationActionHom`, whose derivation is one of the target
pulled back along `φ`.  The target-derivation variant remains the one
[Stacks Project, Tag 0618] uses, where the derivation is one of `𝒪_Y` and `q` is the quotient
map. -/
theorem isUnit_conormalSourceDerivationActionHom_app_apply_iff
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : A.obj.obj V) :
    IsUnit ((conormalSourceDerivationActionHom B S hS Z hZ φ D hmul hmap).hom.app V x) ↔
      IsUnit (φ.hom.app V x) :=
  Stacks.Sites.isUnit_derivationActionHom_app_apply_iff (q := 𝟙 A)
    (conormalSourceSquareZeroValues B S hS Z hZ φ) φ D hmul hmap
    (fun W y m => smul_app_conormalInverseImageι B S hS Z hZ W (φ.hom.app W y) m) V x

end SourceDerivation

end AlgebraicGeometry.Space

end
