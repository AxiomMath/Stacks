module

public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseMilnorBoundary
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.Stalk
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# The arrows of Stacks 0EAY

Let `X` be a locally Noetherian scheme and `δ : X → ℤ` a function strictly decreasing along
proper specializations (a dimension function has this property). For integers `j` and `n` write

`C_{j, n} = ⨁_{δ(x) = j} K^M_n(κ(x))`

for the group of families of degree-`n` Milnor K-classes at the points of `δ`-value `j` which are
locally finite (on a quasi-compact open only finitely many are nonzero; for `X` quasi-compact,
for instance Noetherian, this is the direct sum: `Stacks.Chow.mem_dimMilnorChainGroup_iff_finite`).

This file builds the arrow `∂ : C_{j + 1, i + 1} → C_{j, i}` of Stacks 0EAY in every degree. Its
coefficient at a point `x'` with `δ(x') = j` is

`∑_{x ⇝ x', δ(x) = j + 1} ∂_{𝒪_{W_x, x'}}(α_x)`, `W_x = closure {x}`,

where `∂_A` is the tame symbol of the one-dimensional Noetherian local domain
`A = 𝒪_{W_x, x'}` obtained by normalization and norm (`Stacks.Chow.stalkTameSymbol`). That the
ring `𝒪_{W_x, x'}` is one-dimensional is
`Stacks.Chow.ringKrullDim_pointClosureStalk_eq_one_of_eq_add_one`: a drop of one in `δ` along a
specialization makes it immediate. Then three things are checked: the inner sum is finite
(`Stacks.Chow.finite_support_dimMilnorChainBoundaryTerm`), the family of coefficients is again
locally finite (`Stacks.Chow.finite_dimMilnorChainBoundaryCoeff_ne_zero`), and the result is
additive.

The two arrows of the display of Stacks 0EAY are this one at `(i, j)` and at `(i - 1, j - 1)`.

## Main definitions

* `Stacks.Chow.DimMilnorChainGroup` — `⨁_{δ(x) = j} K^M_n(κ(x))`.
* `Stacks.Chow.pointClosureTameSymbol` — the local component `∂_{𝒪_{W_x, x'}}`.
* `Stacks.Chow.dimMilnorChainBoundary` — the arrow.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-! ### The chain groups -/

/-- **`⨁_{δ(x) = j} K^M_n(κ(x))`**: the locally finite families of degree-`n` Milnor K-classes at
the points of `X` where `δ` takes the value `j`. -/
abbrev DimMilnorChainGroup (X : Scheme.{u}) (δ : X → ℤ) (j : ℤ) (n : ℕ) : Type u :=
  ↥(locallyFiniteDirectSum X {x | δ x = j} fun x ↦ MilnorKTheory (X.residueField x.1) n)

/-- **On a quasi-compact scheme the locally finite families are the finitely supported ones**, so
that for a Noetherian `X` the group `Stacks.Chow.DimMilnorChainGroup` is the direct sum
`⨁_{δ(x) = j} K^M_n(κ(x))` of the source. -/
theorem mem_dimMilnorChainGroup_iff_finite {X : Scheme.{u}} [CompactSpace X] (δ : X → ℤ) (j : ℤ)
    (n : ℕ) (a : ∀ x : {x : X | δ x = j}, MilnorKTheory (X.residueField x.1) n) :
    a ∈ locallyFiniteDirectSum X {x | δ x = j} (fun x ↦ MilnorKTheory (X.residueField x.1) n) ↔
      {x | a x ≠ 0}.Finite := by
  constructor
  · intro ha
    refine (ha ⊤ (by simpa using isCompact_univ)).subset fun x hx ↦ ⟨trivial, hx⟩
  · intro ha U _
    exact ha.subset fun x hx ↦ hx.2

variable {X : Scheme.{u}}

/-- The closures of the points at which a locally finite family is nonzero form a locally finite
family of sets. -/
theorem locallyFinite_closure_support_of_mem_locallyFiniteDirectSum (T : Set X)
    (G : T → Type*) [∀ x, AddCommGroup (G x)] (ξ : ↥(locallyFiniteDirectSum X T G)) :
    LocallyFinite fun j : {x : T // ξ.1 x ≠ 0} ↦ closure ({j.1.1} : Set X) := by
  intro z
  obtain ⟨_, ⟨U, hUaff, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  refine ⟨(U : Set X), U.2.mem_nhds hzU, ?_⟩
  refine Set.Finite.of_finite_image (f := fun j : {x : T // ξ.1 x ≠ 0} ↦ j.1)
    ((ξ.2 U hUaff.isCompact).subset ?_) (Set.injOn_of_injective Subtype.val_injective)
  rintro _ ⟨j, ⟨w, hwcl, hwU⟩, rfl⟩
  exact ⟨(specializes_iff_mem_closure.mpr hwcl).mem_open U.2 hwU, j.2⟩

/-! ### A drop of one makes the local ring one-dimensional -/

/-- **A drop of one along a specialization is an immediate specialization**, for a function
strictly decreasing along proper specializations. -/
theorem isImmediateSpecialization_of_eq_add_one {δ : X → ℤ}
    (hδ : ∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → δ y < δ x) {x x' : X} (hspec : x ⤳ x')
    (hdrop : δ x = δ x' + 1) : IsImmediateSpecialization x x' := by
  refine ⟨hspec, fun h ↦ by rw [h] at hdrop; omega, fun z hxz hzx' ↦ ?_⟩
  by_contra hne
  push Not at hne
  have h1 := hδ hxz (Ne.symm hne.1)
  have h2 := hδ hzx' hne.2
  omega

/-- **The local ring of `closure {x}` at `x'` is one-dimensional when `x ⇝ x'` drops `δ` by
one.** -/
theorem ringKrullDim_pointClosureStalk_eq_one_of_eq_add_one {δ : X → ℤ}
    (hδ : ∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → δ y < δ x) {x x' : X} (hspec : x ⤳ x')
    (hdrop : δ x = δ x' + 1) :
    ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hspec))) = 1 := by
  have himm := isImmediateSpecialization_of_eq_add_one hδ hspec hdrop
  have key : ∀ a b : (integralComponentAt x).subscheme, a ⤳ b ↔ (a.1 : X) ⤳ b.1 := fun a b ↦
    (integralComponentAt x).subschemeι.isClosedEmbedding.isInducing.specializes_iff.symm
  have hcoh : Order.coheight (pointClosurePoint x (specializes_iff_mem_closure.mp hspec)) = 1 := by
    refine (coheight_eq_one_iff_isImmediateSpecialization_pointClosure x
      (pointClosurePoint x (specializes_iff_mem_closure.mp hspec))).mpr ⟨?_, ?_, fun z hz1 hz2 ↦ ?_⟩
    · exact (key _ _).mpr hspec
    · intro h
      exact himm.2.1 (congrArg Subtype.val h)
    · rcases himm.2.2 _ ((key _ z).mp hz1) ((key z _).mp hz2) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hcoh]
  rfl

/-! ### The local component -/

variable [IsLocallyNoetherian X] {N : MilnorKNormFamily.{u}}

/-- **The local component `∂_{𝒪_{W_x, x'}}` of the arrow of Stacks 0EAY.** For `x ⇝ x'` with
`dim 𝒪_{closure {x}, x'} = 1`, the normalization-and-norm tame symbol of that one-dimensional
Noetherian local domain, read through the identification of its fraction field with `κ(x)` and
of its residue field with `κ(x')`. -/
def pointClosureTameSymbol (hN : N.PreservesGrading) (x : X) {x' : X}
    (h : x' ∈ closure ({x} : Set X))
    (hdim : ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x h)) = 1) (i : ℕ) :
    MilnorKTheory ↥(X.residueField x) (i + 1) →+ MilnorKTheory ↥(X.residueField x') i :=
  letI : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  (milnorKTransport (pointClosureResidueFieldEquiv x h).toRingHom i).comp
    (stalkTameSymbol (pointClosureFunctionFieldEquiv x) hN (pointClosurePoint x h) hdim i)

/-! ### The contribution of a single point -/

variable (δ : X → ℤ) (hδ : ∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → δ y < δ x)

omit [IsLocallyNoetherian X] in
include hδ in
/-- The drop of one along `x ⇝ x'` between the two levels of the arrow. -/
theorem ringKrullDim_eq_one_of_mem (j : ℤ) {x : {x : X | δ x = j + 1}}
    {x' : {x : X | δ x = j}} (h : (x.1 : X) ⤳ (x'.1 : X)) :
    ringKrullDim ((integralComponentAt x.1).subscheme.presheaf.stalk
      (pointClosurePoint x.1 (specializes_iff_mem_closure.mp h))) = 1 :=
  ringKrullDim_pointClosureStalk_eq_one_of_eq_add_one hδ h (by rw [x.2, x'.2])

open Classical in
/-- The contribution of a point `x` with `δ(x) = j + 1` to the coefficient at a point `x'` with
`δ(x') = j`: the local component applied to the class of the chain at `x`, and zero when `x`
does not specialize to `x'`. -/
def dimMilnorChainBoundaryTerm (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x : {x : X | δ x = j + 1})
    (x' : {x : X | δ x = j}) : MilnorKTheory ↥(X.residueField x'.1) i :=
  if h : (x.1 : X) ⤳ (x'.1 : X) then
    pointClosureTameSymbol hN x.1 (specializes_iff_mem_closure.mp h)
      (ringKrullDim_eq_one_of_mem δ hδ j h) i (ξ.1 x)
  else 0

variable {δ hδ}

open Classical in
/-- When `x ⇝ x'`, the contribution of `x` at `x'` is the local tame symbol of the class of the
chain at `x`. -/
theorem dimMilnorChainBoundaryTerm_of_specializes (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x : {x : X | δ x = j + 1})
    (x' : {x : X | δ x = j}) (h : (x.1 : X) ⤳ (x'.1 : X)) :
    dimMilnorChainBoundaryTerm δ hδ hN i j ξ x x' =
      pointClosureTameSymbol hN x.1 (specializes_iff_mem_closure.mp h)
        (ringKrullDim_eq_one_of_mem δ hδ j h) i (ξ.1 x) := by
  rw [dimMilnorChainBoundaryTerm, dite_eq_left h]

open Classical in
/-- When `x` does not specialize to `x'`, the contribution of `x` at `x'` is zero. -/
theorem dimMilnorChainBoundaryTerm_of_not_specializes (hN : N.PreservesGrading) (i : ℕ)
    (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x : {x : X | δ x = j + 1})
    (x' : {x : X | δ x = j}) (h : ¬(x.1 : X) ⤳ (x'.1 : X)) :
    dimMilnorChainBoundaryTerm δ hδ hN i j ξ x x' = 0 := by
  rw [dimMilnorChainBoundaryTerm, dite_eq_right h]

open Classical in
/-- A point `x` at which the chain vanishes contributes zero at every `x'`. -/
theorem dimMilnorChainBoundaryTerm_of_eq_zero (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) {x : {x : X | δ x = j + 1}} (hx : ξ.1 x = 0)
    (x' : {x : X | δ x = j}) : dimMilnorChainBoundaryTerm δ hδ hN i j ξ x x' = 0 := by
  rw [dimMilnorChainBoundaryTerm]
  split
  · rw [hx, map_zero]
  · rfl

open Classical in
/-- The contribution of a point `x` at `x'` is additive in the chain. -/
theorem dimMilnorChainBoundaryTerm_add (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ η : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x : {x : X | δ x = j + 1})
    (x' : {x : X | δ x = j}) :
    dimMilnorChainBoundaryTerm δ hδ hN i j (ξ + η) x x' =
      dimMilnorChainBoundaryTerm δ hδ hN i j ξ x x' +
        dimMilnorChainBoundaryTerm δ hδ hN i j η x x' := by
  rw [dimMilnorChainBoundaryTerm, dimMilnorChainBoundaryTerm, dimMilnorChainBoundaryTerm]
  split
  · rw [show (ξ + η).1 x = ξ.1 x + η.1 x from rfl, map_add]
  · rw [add_zero]

/-- A point `x` contributing a nonzero term at `x'` carries a nonzero class and specializes
to `x'`. -/
private theorem ne_zero_and_specializes_of_dimMilnorChainBoundaryTerm_ne_zero
    (hN : N.PreservesGrading) (i : ℕ) (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1))
    {x : {x : X | δ x = j + 1}} {x' : {x : X | δ x = j}}
    (hx : dimMilnorChainBoundaryTerm δ hδ hN i j ξ x x' ≠ 0) :
    ξ.1 x ≠ 0 ∧ (x.1 : X) ⤳ (x'.1 : X) :=
  ⟨fun h ↦ hx (dimMilnorChainBoundaryTerm_of_eq_zero hN i j ξ h x'), by
    by_contra hnot
    exact hx (dimMilnorChainBoundaryTerm_of_not_specializes hN i j ξ x x' hnot)⟩

/-- **The inner sum is finite**: only finitely many points `x` with `δ(x) = j + 1` contribute to
the coefficient at a fixed `x'`. Such a point carries a nonzero class and specializes to `x'`,
and the closures of the points carrying the chain are locally finite. -/
theorem finite_support_dimMilnorChainBoundaryTerm (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x' : {x : X | δ x = j}) :
    (Function.support fun x : {x : X | δ x = j + 1} ↦
      dimMilnorChainBoundaryTerm δ hδ hN i j ξ x x').Finite := by
  obtain ⟨t, ht, hfin⟩ :=
    locallyFinite_closure_support_of_mem_locallyFiniteDirectSum _ _ ξ x'.1
  refine (Set.Finite.image
    (fun q : {x : {x : X | δ x = j + 1} // ξ.1 x ≠ 0} ↦ q.1) hfin).subset ?_
  intro x hx
  obtain ⟨hax, hspec⟩ := ne_zero_and_specializes_of_dimMilnorChainBoundaryTerm_ne_zero hN i j ξ hx
  exact ⟨⟨x, hax⟩, ⟨x'.1, specializes_iff_mem_closure.mp hspec, mem_of_mem_nhds ht⟩, rfl⟩

/-! ### The coefficient -/

variable (δ hδ) in
/-- The coefficient at `x'` of the arrow of Stacks 0EAY: the finite sum, over the points `x` with
`δ(x) = j + 1`, of the local tame symbols of the classes of the chain. -/
def dimMilnorChainBoundaryCoeff (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x' : {x : X | δ x = j}) :
    MilnorKTheory ↥(X.residueField x'.1) i :=
  ∑ᶠ x : {x : X | δ x = j + 1}, dimMilnorChainBoundaryTerm δ hδ hN i j ξ x x'

/-- The coefficient at `x'` is additive in the chain. -/
theorem dimMilnorChainBoundaryCoeff_add (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ η : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x' : {x : X | δ x = j}) :
    dimMilnorChainBoundaryCoeff δ hδ hN i j (ξ + η) x' =
      dimMilnorChainBoundaryCoeff δ hδ hN i j ξ x' +
        dimMilnorChainBoundaryCoeff δ hδ hN i j η x' := by
  rw [dimMilnorChainBoundaryCoeff, dimMilnorChainBoundaryCoeff, dimMilnorChainBoundaryCoeff,
    ← finsum_add_distrib (finite_support_dimMilnorChainBoundaryTerm hN i j ξ x')
      (finite_support_dimMilnorChainBoundaryTerm hN i j η x')]
  exact finsum_congr fun x ↦ dimMilnorChainBoundaryTerm_add hN i j ξ η x x'

/-- The coefficient at `x'` of the zero chain is zero. -/
theorem dimMilnorChainBoundaryCoeff_zero (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (x' : {x : X | δ x = j}) : dimMilnorChainBoundaryCoeff δ hδ hN i j 0 x' = 0 := by
  rw [dimMilnorChainBoundaryCoeff,
    finsum_congr fun x ↦ dimMilnorChainBoundaryTerm_of_eq_zero hN i j 0 rfl x']
  exact finsum_zero

/-! ### Local finiteness -/

/-- **A single point contributes at only finitely many points of a quasi-compact open.** The
intersection of `U` with `closure {x}` is a quasi-compact open of the integral locally Noetherian
scheme `closure {x}`, so `Stacks.Chow.finite_stalkTameSymbol_ne_zero` applies there. -/
theorem finite_dimMilnorChainBoundaryTerm_ne_zero (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x : {x : X | δ x = j + 1}) (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    {x' : {x : X | δ x = j} | (x'.1 : X) ∈ (U : Set X) ∧
      dimMilnorChainBoundaryTerm δ hδ hN i j ξ x x' ≠ 0}.Finite := by
  classical
  let _ : IsLocallyNoetherian (integralComponentAt x.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x.1).subschemeι
  have hVcompact : IsCompact ((((integralComponentAt x.1).subschemeι ⁻¹ᵁ U) :
      Set (integralComponentAt x.1).subscheme) : Set (integralComponentAt x.1).subscheme) :=
    ((integralComponentAt x.1).subschemeι.isClosedEmbedding.isInducing.isCompact_preimage
      (integralComponentAt x.1).subschemeι.isClosedEmbedding.isClosed_range hU)
  have hfin := finite_stalkTameSymbol_ne_zero (pointClosureFunctionFieldEquiv x.1) hN
    ((integralComponentAt x.1).subschemeι ⁻¹ᵁ U) hVcompact i (ξ.1 x)
  refine Set.Finite.of_finite_image (f := fun x' : {x : X | δ x = j} ↦ (x'.1 : X))
    ((hfin.image fun z ↦ ((integralComponentAt x.1).subschemeι z.1 : X)).subset ?_)
    (Set.injOn_of_injective Subtype.val_injective)
  rintro _ ⟨x', ⟨hx'U, hx'ne⟩, rfl⟩
  by_cases hspec : (x.1 : X) ⤳ (x'.1 : X)
  · have hmem : (x'.1 : X) ∈ closure ({(x.1 : X)} : Set X) :=
      specializes_iff_mem_closure.mp hspec
    refine ⟨⟨pointClosurePoint x.1 hmem, ringKrullDim_eq_one_of_mem δ hδ j hspec⟩, ⟨?_, ?_⟩,
      subschemeι_pointClosurePoint x.1 hmem⟩
    · change (integralComponentAt x.1).subschemeι (pointClosurePoint x.1 hmem) ∈ (U : Set X)
      rw [subschemeι_pointClosurePoint x.1 hmem]
      exact hx'U
    · intro hzero
      refine hx'ne ?_
      rw [dimMilnorChainBoundaryTerm_of_specializes hN i j ξ x x' hspec, pointClosureTameSymbol,
        AddMonoidHom.comp_apply]
      exact (congrArg (milnorKTransport (pointClosureResidueFieldEquiv x.1 hmem).toRingHom i)
        hzero).trans (map_zero _)
  · exact absurd (dimMilnorChainBoundaryTerm_of_not_specializes hN i j ξ x x' hspec) hx'ne

/-- **The family of coefficients is locally finite.** On a quasi-compact open `U` only finitely
many points with `δ = j` carry a nonzero coefficient: only the finitely many points `x` of `U`
with `δ(x) = j + 1` at which the chain is nonzero can contribute, and each contributes at only
finitely many points of `U`. -/
theorem finite_dimMilnorChainBoundaryCoeff_ne_zero (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    {x' : {x : X | δ x = j} | (x'.1 : X) ∈ (U : Set X) ∧
      dimMilnorChainBoundaryCoeff δ hδ hN i j ξ x' ≠ 0}.Finite := by
  classical
  have hF : {x : {x : X | δ x = j + 1} | (x.1 : X) ∈ (U : Set X) ∧ ξ.1 x ≠ 0}.Finite := ξ.2 U hU
  refine (hF.biUnion
    (fun x _ ↦ finite_dimMilnorChainBoundaryTerm_ne_zero (hδ := hδ) hN i j ξ x U hU)).subset ?_
  rintro x' ⟨hx'U, hx'ne⟩
  have hsupp : ∃ x : {x : X | δ x = j + 1}, dimMilnorChainBoundaryTerm δ hδ hN i j ξ x x' ≠ 0 := by
    by_contra hall
    refine hx'ne ?_
    rw [dimMilnorChainBoundaryCoeff, finsum_congr fun x ↦ not_not.mp fun hne ↦ hall ⟨x, hne⟩]
    exact finsum_zero
  obtain ⟨x, hx⟩ := hsupp
  obtain ⟨hax, hspec⟩ := ne_zero_and_specializes_of_dimMilnorChainBoundaryTerm_ne_zero hN i j ξ hx
  exact Set.mem_biUnion (show x ∈ {y : {x : X | δ x = j + 1} | (y.1 : X) ∈ (U : Set X) ∧
    ξ.1 y ≠ 0} from ⟨hspec.mem_open U.2 hx'U, hax⟩) (show x' ∈ {y' : {x : X | δ x = j} |
      (y'.1 : X) ∈ (U : Set X) ∧ dimMilnorChainBoundaryTerm δ hδ hN i j ξ x y' ≠ 0} from
      ⟨hx'U, hx⟩)

/-! ### The arrow -/

variable (δ hδ) in
/-- **The arrow `⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) → ⨁_{δ(x) = j} K^M_i(κ(x))` of Stacks 0EAY**,
for a function `δ` strictly decreasing along proper specializations: the coefficient at `x'` is
the sum over the points `x` with `δ(x) = j + 1` specializing to `x'` of the tame symbols
`∂_{𝒪_{closure {x}, x'}}` of the classes of the chain. -/
def dimMilnorChainBoundary (hN : N.PreservesGrading) (i : ℕ) (j : ℤ) :
    DimMilnorChainGroup X δ (j + 1) (i + 1) →+ DimMilnorChainGroup X δ j i where
  toFun ξ := ⟨fun x' ↦ dimMilnorChainBoundaryCoeff δ hδ hN i j ξ x', fun U hU ↦
    finite_dimMilnorChainBoundaryCoeff_ne_zero hN i j ξ U hU⟩
  map_zero' := Subtype.ext (funext fun x' ↦ dimMilnorChainBoundaryCoeff_zero hN i j x')
  map_add' ξ η := Subtype.ext (funext fun x' ↦ dimMilnorChainBoundaryCoeff_add hN i j ξ η x')

/-- The coefficient at `x'` of the image of a chain under the arrow is
`Stacks.Chow.dimMilnorChainBoundaryCoeff`. -/
@[simp]
theorem dimMilnorChainBoundary_apply (hN : N.PreservesGrading) (i : ℕ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x' : {x : X | δ x = j}) :
    (dimMilnorChainBoundary δ hδ hN i j ξ).1 x' = dimMilnorChainBoundaryCoeff δ hδ hN i j ξ x' :=
  rfl

end Stacks.Chow

end
