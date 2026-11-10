module

public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureStalkDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.StalkMilnorBoundary
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree-two Milnor K-chain group and the first differential of Stacks 0GU9

Let `(S, δ)` be the base situation of chapter 42 and `p : X ⟶ S` locally of finite type. Stacks
0GU9 displays the three locally finite groups

`⨁'_{δ(x) = k + 2} K₂ᴹ(κ(x)) ⟶ ⨁'_{δ(x) = k + 1} K₁ᴹ(κ(x)) ⟶ ⨁'_{δ(x) = k} K₀ᴹ(κ(x))`

and asserts that they form a complex. The second differential is the divisor differential
`Stacks.Chow.pointwiseDivisorDifferential` of Stacks 0GU3, already in the library. This file builds
the first group and the first differential.

The first differential is the one the tag describes as sending a family `ξ = ∑ₓ αₓ` to the family
whose coefficient at `x'` is

`∑_{x ⇝ x'} ∂_{𝒪_{Wₓ, x'}}(αₓ)`,

where `Wₓ = closure {x}` is the integral closed subscheme spanned by `x` and `∂` is the tame
symbol of Stacks 02Q1 descended to Milnor K-theory. Three things have to be checked for that
recipe to define a homomorphism of the locally finite direct sums of Stacks 0GU2, and all three
are proved here: the local component exists at all, the inner sum is finite, and the resulting
family is locally finite.

## How the local component is built

Fix `x` of `δ`-dimension `k + 2` and `x'` of `δ`-dimension `k + 1` with `x ⇝ x'`. On `W = Wₓ`,
which is integral and locally Noetherian, the drop of the relative dimension along `x ⇝ x'`
equals the Krull dimension of `𝒪_{W, x'}`
(`Stacks.Chow.relativeDimension_sub_eq_ringKrullDim_pointClosureStalk`), so that local ring is a
one-dimensional Noetherian local domain. Its fraction field is the function field of `W`, which
is `κ(x)` because `x` is the generic point of `W`; so the tame symbol of Stacks 02Q1, descended
along the presentation of Milnor K-theory, is a homomorphism `K₂ᴹ(κ(x)) ⟶ K₁ᴹ(κ_W(x'))`, namely
`Stacks.Chow.stalkMilnorBoundary`. Finally the closed immersion `W ⟶ X` identifies `κ_W(x')`
with `κ(x')`, and in degree one a Milnor K-group is the unit group of the field, so that
identification transports the target.

## What is carried

* Everything carries `[LocallyOfFiniteType p]`, which is the standing hypothesis of chapter 42
  and is what makes `closure {x}` locally Noetherian, hence its local rings Noetherian.
* `Stacks.Chow.relativeDimension_sub_eq_ringKrullDim_pointClosureStalk`, and so every statement
  below which computes a stalk dimension, carries the universal catenarity and local
  Noetherianness of the base. Both are part of `Stacks.Chow.ChowSituation`, so nothing extra is
  assumed here.
* **Nothing here asserts Stacks 0GUA**, and nothing here asserts that the three groups form a
  complex. The composite of the first differential with the divisor differential of Stacks 0GU3
  is not computed; in particular the first higher Chow group of Stacks 0GUA, which is the
  homology of that complex in the middle, is not defined. What is constructed here is the first
  chain group, the first differential, and the two finiteness statements which make the differential
  well defined.

## Main definitions

* `Stacks.Chow.PointwiseKTwoGroup` — the locally finite direct sum of the degree-two Milnor
  K-groups of the residue fields at the points of relative dimension `k + 2`.
* `Stacks.Chow.milnorKOneTransport` — transport of a degree-one Milnor K-group along a ring
  equivalence of fields.
* `Stacks.Chow.pointClosureFunctionFieldEquiv` — the function field of `closure {x}` is `κ(x)`.
* `Stacks.Chow.pointClosureResidueFieldEquiv` — the residue field of `closure {x}` at one of its
  points is the residue field of `X` there.
* `Stacks.Chow.pointClosureMilnorBoundary` — the local component `∂_{𝒪_{Wₓ, x'}}`.
* `Stacks.Chow.pointwiseMilnorBoundaryTerm`, `Stacks.Chow.pointwiseMilnorBoundaryCoeff` — the
  contribution of one point, and the coefficient of the differential at `x'`.
* `Stacks.Chow.pointwiseMilnorBoundary` — **the first differential**.

## Main results

* `Stacks.Chow.ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one` — a drop of
  one in the relative dimension makes the local ring of `closure {x}` one-dimensional.
* `Stacks.Chow.finite_support_pointwiseMilnorBoundaryTerm` — the inner sum is finite.
* `Stacks.Chow.finite_pointwiseMilnorBoundaryCoeff_ne_zero` — the resulting family is locally
  finite.

## References

* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-! ### Transport of a degree-one Milnor K-group along an equivalence of fields -/

/-- A ring equivalence of fields transports the degree-one Milnor K-group, which is the unit
group of the field read additively. -/
def milnorKOneTransport {k₁ k₂ : Type u} [Field k₁] [Field k₂] (φ : k₁ ≃+* k₂) :
    MilnorKTheory k₁ 1 →+ MilnorKTheory k₂ 1 :=
  (milnorKTheoryOneAddEquiv k₂).symm.toAddMonoidHom.comp
    (((Units.map (φ : k₁ →+* k₂).toMonoidHom).toAdditive).comp
      (milnorKTheoryOneAddEquiv k₁).toAddMonoidHom)

/-! ### The function field and the residue fields of the closure of a point -/

variable {X : Scheme.{u}}

/-- A point of `X` lying in the closure of `x`, read as a point of the integral closed
subscheme `closure {x}`. -/
def pointClosurePoint (x : X) {x' : X} (h : x' ∈ closure ({x} : Set X)) :
    (integralComponentAt x).subscheme := ⟨x', h⟩

/-- The inclusion of `closure {x}` into `X` sends `pointClosurePoint x h` to `x'`. -/
@[simp] theorem subschemeι_pointClosurePoint (x : X) {x' : X}
    (h : x' ∈ closure ({x} : Set X)) :
    (integralComponentAt x).subschemeι (pointClosurePoint x h) = x' :=
  (integralComponentAt x).subschemeι_apply (pointClosurePoint x h)

/-- **The function field of `closure {x}` is the residue field of `X` at `x`.** The rational
functions on an integral scheme are its function field, and for the integral closed subscheme
spanned by `x` they are also the residue field of `X` at `x`, by Stacks 01RV. -/
def pointClosureFunctionFieldEquiv (x : X) :
    ↥((integralComponentAt x).subscheme.functionField) ≃+* ↥(X.residueField x) :=
  (rationalFunctionsEquivFunctionField (integralComponentAt x).subscheme).1.symm.trans
    (rationalFunctionsEquivResidueFieldOfGenericPoint (integralComponentAt x)
      (isIntegral_integralComponentAt x) (genericPointOf_integralComponentAt x))

/-- **The residue field of `closure {x}` at one of its points is the residue field of `X`
there.** A closed immersion induces an isomorphism on residue fields. -/
def pointClosureResidueFieldEquiv (x : X) {x' : X} (h : x' ∈ closure ({x} : Set X)) :
    ↥((integralComponentAt x).subscheme.residueField (pointClosurePoint x h)) ≃+*
      ↥(X.residueField x') :=
  (RingEquiv.ofBijective
        ((integralComponentAt x).subschemeι.residueFieldMap (pointClosurePoint x h)).hom
        (bijective_residueFieldMap_of_isClosedImmersion _ _)).symm.trans
    (X.residueFieldCongr (subschemeι_pointClosurePoint x h)).commRingCatIsoToRingEquiv

/-! ### The stalk of the closure of a point is one-dimensional along a drop of one -/

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- **A drop of one in the relative dimension makes the local ring one-dimensional.** This is
`Stacks.Chow.relativeDimension_sub_eq_ringKrullDim_pointClosureStalk` read in the direction the
first differential of Stacks 0GU9 needs: a point `x` of `δ`-dimension `k + 2` specializing to a
point `x'` of `δ`-dimension `k + 1` has `dim 𝒪_{closure {x}, x'} = 1`, so the tame symbol of
Stacks 02Q1 is defined there. -/
theorem ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one {x x' : X}
    (hspec : x ⤳ x')
    (hdrop : relativeDimension C.dimensionFunction p x -
      relativeDimension C.dimensionFunction p x' = 1) :
    ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hspec))) = 1 := by
  obtain ⟨n, hdrop', hlocal⟩ := relativeDimension_drop_of_specialization
    C.isUniversallyCatenary C.dimensionFunction p hspec
  rw [hdrop] at hdrop'
  have hn : n = 1 := by omega
  rw [hn] at hlocal
  exact hlocal.trans (by norm_num)

/-! ### The local component of the first differential -/

/-- **The local component `∂_{𝒪_{Wₓ, x'}}` of the first differential of Stacks 0GU9.** For
`x ⇝ x'` with `dim 𝒪_{closure {x}, x'} = 1`, the tame symbol of that one-dimensional Noetherian
local domain, descended to Milnor K-theory and read through the identification of its fraction
field with `κ(x)` and of its residue field with `κ(x')`. -/
def pointClosureMilnorBoundary (x : X) {x' : X} (h : x' ∈ closure ({x} : Set X))
    (hdim : ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x h)) = 1) :
    MilnorKTheory ↥(X.residueField x) 2 →+ MilnorKTheory ↥(X.residueField x') 1 :=
  letI : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ p)
  (milnorKOneTransport (pointClosureResidueFieldEquiv x h)).comp
    (stalkMilnorBoundary (pointClosureFunctionFieldEquiv x) (pointClosurePoint x h) hdim)

/-- The local component sends a class killed by the tame-symbol boundary of `closure {x}` to
zero: it is that boundary followed by a homomorphism. -/
theorem pointClosureMilnorBoundary_eq_zero_of_stalkMilnorBoundary_eq_zero (x : X) {x' : X}
    (h : x' ∈ closure ({x} : Set X))
    (hdim : ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x h)) = 1)
    (α : MilnorKTheory ↥(X.residueField x) 2)
    (hα : let _ : IsLocallyNoetherian (integralComponentAt x).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ p)
      stalkMilnorBoundary (pointClosureFunctionFieldEquiv x) (pointClosurePoint x h) hdim α = 0) :
    pointClosureMilnorBoundary C p x h hdim α = 0 := by
  let _ : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ p)
  change milnorKOneTransport (pointClosureResidueFieldEquiv x h)
    (stalkMilnorBoundary (pointClosureFunctionFieldEquiv x) (pointClosurePoint x h) hdim α) = 0
  rw [hα, map_zero]

/-! ### The degree-two Milnor K-chain group -/

/-- **Stacks 0GU9.** The group of locally finite families of degree-two Milnor K-classes at the
points of relative dimension `k + 2`: the source of the first differential. -/
abbrev PointwiseKTwoGroup (k : ℤ) : Type u :=
  ↥(locallyFiniteDirectSum X (pointsOfDimension C p (k + 2))
    fun x ↦ MilnorKTheory (X.residueField x.1) 2)

omit [LocallyOfFiniteType p] in
/-- The closures of the points at which a Milnor K-chain is nonzero form a locally finite family:
every point of `X` has an affine, hence quasi-compact, open neighbourhood containing only
finitely many of those points, and the closure of a point meets an open set only if the point
itself does. Neither the relative dimension nor the degree plays any role. -/
theorem locallyFinite_closure_milnorChainSupport (m : ℤ) (n : ℕ)
    (ξ : ↥(locallyFiniteDirectSum X (pointsOfDimension C p m)
      fun x ↦ MilnorKTheory (X.residueField x.1) n)) :
    LocallyFinite fun j : {x : pointsOfDimension C p m // ξ.1 x ≠ 0} ↦
      closure ({j.1.1} : Set X) := by
  intro z
  obtain ⟨_, ⟨U, hUaff, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  refine ⟨(U : Set X), U.2.mem_nhds hzU, ?_⟩
  refine Set.Finite.of_finite_image
    (f := fun j : {x : pointsOfDimension C p m // ξ.1 x ≠ 0} ↦ j.1)
    ((ξ.2 U hUaff.isCompact).subset ?_) (Set.injOn_of_injective Subtype.val_injective)
  rintro _ ⟨j, ⟨w, hwcl, hwU⟩, rfl⟩
  exact ⟨(specializes_iff_mem_closure.mpr hwcl).mem_open U.2 hwU, j.2⟩

omit [LocallyOfFiniteType p] in
/-- The closures of the points at which a degree-two Milnor K-chain is nonzero form a locally
finite family: every point of `X` has an affine, hence quasi-compact, open neighbourhood
containing only finitely many of those points, and the closure of a point meets an open set only
if the point itself does. -/
theorem locallyFinite_closure_pointwiseKTwoSupport (k : ℤ) (ξ : PointwiseKTwoGroup C p k) :
    LocallyFinite fun j : {x : pointsOfDimension C p (k + 2) // ξ.1 x ≠ 0} ↦
      closure ({j.1.1} : Set X) :=
  locallyFinite_closure_milnorChainSupport C p (k + 2) 2 ξ

/-! ### The first differential -/

open Classical in
/-- The contribution of a point `x` of relative dimension `k + 2` to the coefficient at a point
`x'` of relative dimension `k + 1` of the first differential of Stacks 0GU9: the local component
`∂_{𝒪_{Wₓ, x'}}` applied to the class of the chain at `x`, and zero when `x` does not specialize
to `x'`. -/
def pointwiseMilnorBoundaryTerm (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (x : pointsOfDimension C p (k + 2)) (x' : pointsOfDimension C p (k + 1)) :
    MilnorKTheory ↥(X.residueField x'.1) 1 :=
  if h : (x.1 : X) ⤳ (x'.1 : X) then
    pointClosureMilnorBoundary C p x.1 (specializes_iff_mem_closure.mp h)
      (ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one C p h
        (by rw [(mem_pointsOfDimension C p).mp x.2, (mem_pointsOfDimension C p).mp x'.2]; ring))
      (ξ.1 x)
  else 0

open Classical in
/-- Where the chain vanishes, the point contributes nothing. -/
theorem pointwiseMilnorBoundaryTerm_of_eq_zero (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    {x : pointsOfDimension C p (k + 2)} (hx : ξ.1 x = 0)
    (x' : pointsOfDimension C p (k + 1)) :
    pointwiseMilnorBoundaryTerm C p k ξ x x' = 0 := by
  rw [pointwiseMilnorBoundaryTerm]
  split
  · rw [hx, map_zero]
  · rfl

open Classical in
/-- A point which does not specialize to `x'` contributes nothing to the coefficient there. -/
theorem pointwiseMilnorBoundaryTerm_of_not_specializes (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (x : pointsOfDimension C p (k + 2)) (x' : pointsOfDimension C p (k + 1))
    (hx : ¬ (x.1 : X) ⤳ (x'.1 : X)) :
    pointwiseMilnorBoundaryTerm C p k ξ x x' = 0 := by
  rw [pointwiseMilnorBoundaryTerm]
  split
  · rename_i hspec
    exact absurd hspec hx
  · rfl

open Classical in
/-- Where `x` specializes to `x'`, the contribution of `x` is the local component applied to the
class of the chain at `x`. -/
theorem pointwiseMilnorBoundaryTerm_of_specializes (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (x : pointsOfDimension C p (k + 2)) (x' : pointsOfDimension C p (k + 1))
    (hx : (x.1 : X) ⤳ (x'.1 : X))
    (hdim : ringKrullDim ((integralComponentAt x.1).subscheme.presheaf.stalk
      (pointClosurePoint x.1 (specializes_iff_mem_closure.mp hx))) = 1) :
    pointwiseMilnorBoundaryTerm C p k ξ x x' =
      pointClosureMilnorBoundary C p x.1 (specializes_iff_mem_closure.mp hx) hdim (ξ.1 x) := by
  rw [pointwiseMilnorBoundaryTerm]
  split
  · rfl
  · rename_i hno
    exact absurd hx hno

open Classical in
/-- The contribution of a point is additive in the chain. -/
theorem pointwiseMilnorBoundaryTerm_add (k : ℤ) (ξ η : PointwiseKTwoGroup C p k)
    (x : pointsOfDimension C p (k + 2)) (x' : pointsOfDimension C p (k + 1)) :
    pointwiseMilnorBoundaryTerm C p k (ξ + η) x x' =
      pointwiseMilnorBoundaryTerm C p k ξ x x' + pointwiseMilnorBoundaryTerm C p k η x x' := by
  rw [pointwiseMilnorBoundaryTerm, pointwiseMilnorBoundaryTerm, pointwiseMilnorBoundaryTerm]
  split
  · rw [show (ξ + η).1 x = ξ.1 x + η.1 x from rfl, map_add]
  · rw [add_zero]

/-- A point contributing a nonzero term carries a nonzero class and specializes to `x'`. -/
private theorem ne_zero_and_specializes_of_pointwiseMilnorBoundaryTerm_ne_zero (k : ℤ)
    (ξ : PointwiseKTwoGroup C p k) {x : pointsOfDimension C p (k + 2)}
    {x' : pointsOfDimension C p (k + 1)} (hx : pointwiseMilnorBoundaryTerm C p k ξ x x' ≠ 0) :
    ξ.1 x ≠ 0 ∧ (x.1 : X) ⤳ (x'.1 : X) :=
  ⟨fun h ↦ hx (pointwiseMilnorBoundaryTerm_of_eq_zero C p k ξ h x'),
    not_imp_comm.mp (pointwiseMilnorBoundaryTerm_of_not_specializes C p k ξ x x') hx⟩

/-- **The inner sum of the first differential is finite.** Only finitely many points of relative
dimension `k + 2` contribute to the coefficient at a fixed point `x'`: such a point must carry a
nonzero class of the chain and must specialize to `x'`, and the closures of the points carrying
the chain form a locally finite family. -/
theorem finite_support_pointwiseMilnorBoundaryTerm (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (x' : pointsOfDimension C p (k + 1)) :
    (Function.support fun x : pointsOfDimension C p (k + 2) ↦
      pointwiseMilnorBoundaryTerm C p k ξ x x').Finite := by
  obtain ⟨t, ht, hfin⟩ := locallyFinite_closure_milnorChainSupport C p (k + 2) 2 ξ x'.1
  refine (Set.Finite.image
    (fun j : {x : pointsOfDimension C p (k + 2) // ξ.1 x ≠ 0} ↦ j.1) hfin).subset ?_
  intro x hx
  obtain ⟨hax, hspec⟩ := ne_zero_and_specializes_of_pointwiseMilnorBoundaryTerm_ne_zero C p k ξ hx
  exact ⟨⟨x, hax⟩, ⟨x'.1, specializes_iff_mem_closure.mp hspec, mem_of_mem_nhds ht⟩, rfl⟩

/-- The coefficient at `x'` of the first differential of Stacks 0GU9: the locally finite sum,
over the points `x` of relative dimension `k + 2`, of the local tame-symbol boundaries of the
classes of the chain. -/
def pointwiseMilnorBoundaryCoeff (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (x' : pointsOfDimension C p (k + 1)) : MilnorKTheory ↥(X.residueField x'.1) 1 :=
  ∑ᶠ x : pointsOfDimension C p (k + 2), pointwiseMilnorBoundaryTerm C p k ξ x x'

/-- The coefficients of the first differential are additive in the chain. -/
theorem pointwiseMilnorBoundaryCoeff_add (k : ℤ) (ξ η : PointwiseKTwoGroup C p k)
    (x' : pointsOfDimension C p (k + 1)) :
    pointwiseMilnorBoundaryCoeff C p k (ξ + η) x' =
      pointwiseMilnorBoundaryCoeff C p k ξ x' + pointwiseMilnorBoundaryCoeff C p k η x' := by
  rw [pointwiseMilnorBoundaryCoeff, pointwiseMilnorBoundaryCoeff, pointwiseMilnorBoundaryCoeff,
    ← finsum_add_distrib (finite_support_pointwiseMilnorBoundaryTerm C p k ξ x')
      (finite_support_pointwiseMilnorBoundaryTerm C p k η x')]
  exact finsum_congr fun x ↦ pointwiseMilnorBoundaryTerm_add C p k ξ η x x'

/-- The coefficients of the first differential vanish on the zero chain. -/
theorem pointwiseMilnorBoundaryCoeff_zero (k : ℤ) (x' : pointsOfDimension C p (k + 1)) :
    pointwiseMilnorBoundaryCoeff C p k 0 x' = 0 := by
  rw [pointwiseMilnorBoundaryCoeff,
    finsum_congr fun x ↦ pointwiseMilnorBoundaryTerm_of_eq_zero C p k 0 (rfl) x']
  exact finsum_zero

/-- **A single point contributes at only finitely many points of a quasi-compact open.** The
intersection of `U` with `closure {x}` is a quasi-compact open of the integral locally Noetherian
scheme `closure {x}`, so `Stacks.Chow.finite_stalkMilnorBoundary_ne_zero` applies there. -/
theorem finite_pointwiseMilnorBoundaryTerm_ne_zero (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (x : pointsOfDimension C p (k + 2)) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    {x' : pointsOfDimension C p (k + 1) | (x'.1 : X) ∈ (U : Set X) ∧
      pointwiseMilnorBoundaryTerm C p k ξ x x' ≠ 0}.Finite := by
  classical
  let _ : IsLocallyNoetherian (integralComponentAt x.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x.1).subschemeι ≫ p)
  have hVcompact : IsCompact ((((integralComponentAt x.1).subschemeι ⁻¹ᵁ U) :
      Set (integralComponentAt x.1).subscheme) : Set (integralComponentAt x.1).subscheme) :=
    ((integralComponentAt x.1).subschemeι.isClosedEmbedding.isInducing.isCompact_preimage
      (integralComponentAt x.1).subschemeι.isClosedEmbedding.isClosed_range hU)
  have hfin := finite_stalkMilnorBoundary_ne_zero (pointClosureFunctionFieldEquiv x.1)
    ((integralComponentAt x.1).subschemeι ⁻¹ᵁ U) hVcompact (ξ.1 x)
  refine Set.Finite.of_finite_image (f := fun x' : pointsOfDimension C p (k + 1) ↦ (x'.1 : X))
    ((hfin.image fun z ↦ ((integralComponentAt x.1).subschemeι z.1 : X)).subset ?_)
    (Set.injOn_of_injective Subtype.val_injective)
  rintro _ ⟨x', ⟨hx'U, hx'ne⟩, rfl⟩
  by_cases hspec : (x.1 : X) ⤳ (x'.1 : X)
  · have hmem : (x'.1 : X) ∈ closure ({(x.1 : X)} : Set X) := specializes_iff_mem_closure.mp hspec
    have hdim := ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one C p hspec
      (by rw [(mem_pointsOfDimension C p).mp x.2, (mem_pointsOfDimension C p).mp x'.2]; ring)
    refine ⟨⟨pointClosurePoint x.1 hmem, hdim⟩, ⟨?_, ?_⟩, subschemeι_pointClosurePoint x.1 hmem⟩
    · change (integralComponentAt x.1).subschemeι (pointClosurePoint x.1 hmem) ∈ (U : Set X)
      rw [subschemeι_pointClosurePoint x.1 hmem]
      exact hx'U
    · intro hzero
      refine hx'ne ?_
      rw [pointwiseMilnorBoundaryTerm_of_specializes C p k ξ x x' hspec hdim]
      exact pointClosureMilnorBoundary_eq_zero_of_stalkMilnorBoundary_eq_zero C p x.1 hmem hdim
        (ξ.1 x) hzero
  · exact absurd (pointwiseMilnorBoundaryTerm_of_not_specializes C p k ξ x x' hspec) hx'ne

/-- **The family of coefficients of the first differential is locally finite.** On a
quasi-compact open `U` only finitely many points of relative dimension `k + 1` carry a nonzero
coefficient. Only the finitely many points `x` of `U` of relative dimension `k + 2` at which the
chain is nonzero can contribute, and each of them contributes at only finitely many points of
`U`, by the local finiteness of the tame-symbol boundary on the quasi-compact open `U ∩
closure {x}` of `closure {x}`. -/
theorem finite_pointwiseMilnorBoundaryCoeff_ne_zero (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    {x' : pointsOfDimension C p (k + 1) | (x'.1 : X) ∈ (U : Set X) ∧
      pointwiseMilnorBoundaryCoeff C p k ξ x' ≠ 0}.Finite := by
  classical
  have hF : {x : pointsOfDimension C p (k + 2) | (x.1 : X) ∈ (U : Set X) ∧
      ξ.1 x ≠ 0}.Finite := ξ.2 U hU
  refine (hF.biUnion (fun x _ ↦ finite_pointwiseMilnorBoundaryTerm_ne_zero C p k ξ x U hU)).subset
    ?_
  rintro x' ⟨hx'U, hx'ne⟩
  have hsupp : ∃ x : pointsOfDimension C p (k + 2),
      pointwiseMilnorBoundaryTerm C p k ξ x x' ≠ 0 := by
    by_contra hall
    refine hx'ne ?_
    rw [pointwiseMilnorBoundaryCoeff,
      finsum_congr fun x ↦ not_not.mp fun hne ↦ hall ⟨x, hne⟩]
    exact finsum_zero
  obtain ⟨x, hx⟩ := hsupp
  obtain ⟨hax, hspec⟩ := ne_zero_and_specializes_of_pointwiseMilnorBoundaryTerm_ne_zero C p k ξ hx
  exact Set.mem_biUnion (x := x) ⟨hspec.mem_open U.2 hx'U, hax⟩ ⟨hx'U, hx⟩

/-- **Stacks 0GU9.** The first differential of the complex of the tag: the homomorphism from the
locally finite direct sum of the degree-two Milnor K-groups at the points of relative dimension
`k + 2` to the locally finite direct sum of the degree-one Milnor K-groups at the points of
relative dimension `k + 1` whose coefficient at `x'` is the sum, over the points `x` of relative
dimension `k + 2` specializing to `x'`, of the tame-symbol boundaries
`∂_{𝒪_{closure {x}, x'}}` of the classes of the chain. -/
@[stacks 0GU9 "the first differential of the complex of the tag, as a homomorphism of the \
locally finite direct sums of Stacks 0GU2: the degree-two Milnor K-chain group at the points of \
relative dimension k + 2 maps to the degree-one chain group at the points of relative dimension \
k + 1 by the rule whose coefficient at a point x' is the sum, over the points x of relative \
dimension k + 2 specializing to x', of the tame-symbol boundary of the class at x along the \
one-dimensional local ring of the closure of x at x'; both the finiteness of that sum and the \
local finiteness of the resulting family are proved, so the rule is a well defined additive map",
  stacks 0EAY "the first of the two arrows of the remark's displayed diagram, in the case \
i = 1: the map ⊕_{δ(x) = j + 1} K^M_2(κ(x)) ⟶ ⊕_{δ(x) = j} K^M_1(κ(x)) which the remark builds \
out of the tame symbols ∂_A, taken here at the one-dimensional local rings 𝒪_{closure {x}, x'} \
of the Noetherian scheme X carrying the dimension function δ. For i ≥ 2 the same arrow needs the \
tame symbol in higher degrees at those local rings, which the remark takes from \
[Kato-Milnor-K]"]
def pointwiseMilnorBoundary (k : ℤ) :
    PointwiseKTwoGroup C p k →+ PointwiseKOneGroup C p k where
  toFun ξ := ⟨fun x' ↦ pointwiseMilnorBoundaryCoeff C p k ξ x', fun U hU ↦
    finite_pointwiseMilnorBoundaryCoeff_ne_zero C p k ξ U hU⟩
  map_zero' := Subtype.ext (funext fun x' ↦ pointwiseMilnorBoundaryCoeff_zero C p k x')
  map_add' ξ η := Subtype.ext (funext fun x' ↦
    pointwiseMilnorBoundaryCoeff_add C p k ξ η x')

/-- The coefficients of the first differential are the locally finite sums of the local
tame-symbol boundaries. -/
@[simp]
theorem pointwiseMilnorBoundary_apply (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (x' : pointsOfDimension C p (k + 1)) :
    (pointwiseMilnorBoundary C p k ξ).1 x' = pointwiseMilnorBoundaryCoeff C p k ξ x' := rfl

end Stacks.Chow

end
