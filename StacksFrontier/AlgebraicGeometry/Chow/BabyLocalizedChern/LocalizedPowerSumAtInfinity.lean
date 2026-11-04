module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernGysinCommute
public import StacksCore.Tactic.StacksAttribute

/-!
# The classes `P'_p(Q)` of Stacks 0F9K

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let `Z ⊆ X` be a
closed subscheme, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let `Q ∈ D(𝒪_W)` be
a perfect object whose Chern classes are defined, and let `T ⊆ W_∞` be a closed subscheme
containing all points of `W_∞` over `X \ Z` such that `Q|_T` is zero. With `E = W_∞ ×_X Z` the
inverse image of `Z`, Stacks 0F9K defines

  `P'_p(Q) = (E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C ∈ A^p(Z ⟶ X)`,

where `C ∈ A⁰(W_∞ ⟶ X)` is the class of Stacks 0F9J and `P'_p(Q|_E) ∈ A^p(E ⟶ W_∞)` is the class
of Stacks 0F9H for the cover `W_∞ = T ∪ E`, and asserts
`(Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{X × {0}})`. This file proves that half of Stacks 0F9K; the half
for the Chern classes `c'_p(Q)` is
`Stacks.Chow.GysinAtInfinity.properPushforward_localizedChernClassAtInfinity`, and the source's
proof — "the exact same sequence of equations works to prove the property for `P'_p(Q)`" — is
followed verbatim.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.localizedPowerSumOnPreimage` — the class
  `P'_p(Q|_E) ∈ A^p(E ⟶ W_∞)` of Stacks 0F9H.
* `Stacks.Chow.GysinAtInfinity.localizedPowerSumClassAtInfinity` — the class
  `P'_p(Q) ∈ A^p(Z ⟶ X)` of Stacks 0F9K.

## Main results

* `Stacks.Chow.GysinAtInfinity.properPushforward_localizedPowerSumClassAtInfinity` —
  **Stacks 0F9K** for `P'_p`: `(Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{X × {0}})`.

## References

* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The classes `P_p` of a derived pullback -/

section PowerSum

variable (C : ChowSituation.{u})

/-- **`P_p(E)` depends only on the isomorphism class of `E`.** -/
theorem perfectPowerSumComponent_congr {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {E E' : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)
    (hE' : HasDefinedChernClasses E') (e : E ≅ E') (p : ℕ) :
    perfectPowerSumComponent C sX hE p = perfectPowerSumComponent C sX hE' p := by
  rw [perfectPowerSumComponent, perfectPowerSumComponent, perfectPowerSum_congr C sX hE hE' e p]

/-- The class `P_p` of a derived pullback operates as the class `P_p` of the object does, on the
composite test morphism. -/
theorem idRule_perfectPowerSumComponent_derivedPullback_heq {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (h : Y ⟶ X)
    [LocallyOfFiniteType h] (hs : h ≫ sX = sY) {E : DerivedCategory X.Modules}
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E)
    (hE' : HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E))
    (p : ℕ) {V : Scheme.{u}} (v : V ⟶ Y) [LocallyOfFiniteType v] (k : ℤ)
    (α : chowGroup C (v ≫ sY) k) (α' : chowGroup C ((v ≫ h) ≫ sX) k) (hα : α ≍ α') :
    (perfectPowerSumComponent C sY hE' p).idRule C sY (gysinSystemOfInvertible C) v k α ≍
      (perfectPowerSumComponent C sX hE p).idRule C sX (gysinSystemOfInvertible C) (v ≫ h) k
        α' :=
  idRule_heq_of_res_eq C sX h hs
    (res_perfectPowerSumTotal_derivedPullback C sX h hs perfect hE
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E perfect) hE') p v k α α' hα

end PowerSum

namespace GysinAtInfinity

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

/-! ### The class `P'_p(Q)` -/

section Construction

variable (C : ChowSituation.{u}) {X W Z V : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (jZ : Z ⟶ X) [IsClosedImmersion jZ]
  (iV : V ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iV]
  {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q)
  (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q) (p : ℕ)

omit [LocallyOfFiniteType f] [IsProper b] in
include perfect in
/-- `Q|_{W_∞}` is perfect. -/
theorem isPerfect_restrictionAtInfinity :
    RingedSpace.IsPerfect.{u, u + 1} (X := (modificationFibreAtInfinity f b).toRingedSpace)
      (restrictionAtInfinity f b Q) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q perfect

/-- The class `P_p(Q|_{W_∞}) ∈ A^p(W_∞)`. -/
abbrev powerSumAtInfinity :
    chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjectionAtInfinity f b ≫ f) (p : ℤ) :=
  perfectPowerSumComponent C (modificationProjectionAtInfinity f b ≫ f)
    (hasDefinedChernClasses_restrictionAtInfinity f b hQ) p

/-- The class `P_p(Q|_E) ∈ A^p(E)`. -/
abbrev powerSumOnPreimage :
    chowCohomologyComponent C (gysinSystemOfInvertible C)
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) (p : ℤ) :=
  perfectPowerSumComponent C (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
    (hasDefinedChernClasses_derivedPullback (preimageInclusion f b jZ)
      (hasDefinedChernClasses_restrictionAtInfinity f b hQ)) p

include perfect in
/-- `P_p(Q|_{W_∞})` restricts to `P_p(Q|_E)` on `E`. -/
theorem chowCohomologyRestriction_powerSumAtInfinity_preimage :
    chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f) (preimageInclusion f b jZ) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (powerSumAtInfinity C f b hQ p) =
      powerSumOnPreimage C f b jZ hQ p := by
  unfold powerSumAtInfinity powerSumOnPreimage
  rw [← perfectPowerSumTotal_apply, ← perfectPowerSumTotal_apply C
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
      (hasDefinedChernClasses_derivedPullback (preimageInclusion f b jZ)
        (hasDefinedChernClasses_restrictionAtInfinity f b hQ)) p,
    ← TotalChowClass.res_rfl_apply, res_perfectPowerSumTotal_derivedPullback C _ _ rfl
      (isPerfect_restrictionAtInfinity C f b perfect) _
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _
        (isPerfect_restrictionAtInfinity C f b perfect))
      (hasDefinedChernClasses_derivedPullback (preimageInclusion f b jZ)
        (hasDefinedChernClasses_restrictionAtInfinity f b hQ))]

include perfect in
/-- `P_p(Q|_T) = 0` when `Q|_T` is zero. -/
theorem chowCohomologyRestriction_powerSumAtInfinity_eq_zero
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f) iV (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (powerSumAtInfinity C f b hQ p) = 0 :=
  chowCohomologyRestriction_perfectPowerSumComponent_eq_zero C _
    (isPerfect_restrictionAtInfinity C f b perfect) _ iV hzero p

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion jZ] [IsClosedImmersion iV] in
/-- If `Q|_T` is zero, so is `(Q|_E)|_{T ∩ E}`. -/
theorem isZero_restrictionAtInfinity_intersection
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd iV (preimageInclusion f b jZ)).toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (preimageInclusion f b jZ).toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :=
  isZero_derivedPullback_of_comp_eq _ _ _ _ pullback.condition.symm _ hzero

include perfect in
/-- The restriction of `P_p(Q|_E)` to `T ∩ E` vanishes. -/
theorem chowCohomologyRestriction_powerSumOnPreimage_eq_zero
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
        (pullback.snd iV (preimageInclusion f b jZ)) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (powerSumOnPreimage C f b jZ hQ p) = 0 :=
  chowCohomologyRestriction_perfectPowerSumComponent_eq_zero C _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (preimageInclusion f b jZ).toLRSHom.toShHom (restrictionAtInfinity f b Q)
      (isPerfect_restrictionAtInfinity C f b perfect)) _ _
    (isZero_restrictionAtInfinity_intersection C f b jZ iV hzero) p

variable {f b iV p} in
/-- **The class `P'_p(Q|_E) ∈ A^p(E ⟶ W_∞)` of Stacks 0F9H** for the cover `W_∞ = T ∪ E`: the
localized class of `P_p(Q|_E)`, which on a test scheme sends `i'_{T,*} α_T + i'_{E,*} α_E` to
`P_p(Q|_E) ∩ α_E`. -/
def localizedPowerSumOnPreimage
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :
    BivariantClass C (gysinSystemOfInvertible C)
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f) (preimageInclusion f b jZ) rfl (p : ℤ) :=
  closedCoverLocalizedClass C (modificationProjectionAtInfinity f b ≫ f)
    (iV ≫ modificationProjectionAtInfinity f b ≫ f)
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) iV rfl
    (preimageInclusion f b jZ) rfl (range_union_range_preimageInclusion f b jZ iV hV)
    (powerSumOnPreimage C f b jZ hQ p)
    (chowCohomologyRestriction_powerSumOnPreimage_eq_zero C f b jZ iV hQ perfect p hzero)

variable {f b iV p} in
/-- **The class `P'_p(Q) ∈ A^p(Z ⟶ X)` of Stacks 0F9K**:
`P'_p(Q) = (E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C`, with `E = W_∞ ×_X Z`, `C ∈ A⁰(W_∞ ⟶ X)` the class of
Stacks 0F9J and `P'_p(Q|_E) ∈ A^p(E ⟶ W_∞)` the class of Stacks 0F9H; the composite is a class for
`E ⟶ W_∞ ⟶ X = E ⟶ Z ⟶ X` of degree `p + 0 = p`, pushed forward along the proper `E ⟶ Z` by
Stacks 0EPK. -/
def localizedPowerSumClassAtInfinity
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :
    BivariantClass C (gysinSystemOfInvertible C) (jZ ≫ f) f jZ rfl (p : ℤ) :=
  canonicalBivariantProperPushforward C
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) (jZ ≫ f) f
    (preimageProjection f b jZ) jZ (preimageProjection_comp C f b jZ) rfl (p : ℤ)
    (bivariantClassCongr C (gysinSystemOfInvertible C)
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) f
      pullback.condition
      (comp_comp_structureMorphism_eq rfl rfl)
      (comp_comp_structureMorphism_eq (preimageProjection_comp C f b jZ) rfl) (p : ℤ)
      (bivariantClassCongrDeg C (gysinSystemOfInvertible C)
        (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) f
        (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b)
        (comp_comp_structureMorphism_eq rfl rfl) (add_zero (p : ℤ))
        (bivariantCompositeOfInvertible C
          (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
          (modificationProjectionAtInfinity f b ≫ f) f (preimageInclusion f b jZ)
          (modificationProjectionAtInfinity f b) rfl rfl (p : ℤ) 0
          (localizedPowerSumOnPreimage C jZ hQ perfect hV hzero)
          (gysinAtInfinityClass C f b hA))))

variable {f b iV p} in
/-- The class `(Z ⟶ X)_* ∘ P'_p(Q) ∈ A^p(X)`: the pushforward of `P'_p(Q)` along the closed
immersion `Z ⟶ X` by Stacks 0EPK, a class for the identity of `X`. -/
def properPushforwardLocalizedPowerSumClassAtInfinity
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) f (p : ℤ) :=
  canonicalBivariantProperPushforward C (jZ ≫ f) f f jZ (𝟙 X) rfl (Category.id_comp f) (p : ℤ)
    (bivariantClassCongr C (gysinSystemOfInvertible C) (jZ ≫ f) f (Category.comp_id jZ).symm rfl
      (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) (p : ℤ)
      (localizedPowerSumClassAtInfinity C hA jZ hQ perfect hV hzero))

/-- The class `P_p(Q|_{X × {0}}) ∈ A^p(X)` of the restriction of `Q` along the section at zero
`i_0 : X ⟶ W`. -/
abbrev powerSumAtZero :
    chowCohomologyComponent C (gysinSystemOfInvertible C) f (p : ℤ) :=
  haveI := hA
  perfectPowerSumComponent C f
    (hasDefinedChernClasses_derivedPullback (modificationSectionAtZero f b inferInstance) hQ) p

/-- The class `P_p(Q) ∈ A^p(W)`. -/
abbrev powerSumOnModification :
    chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f)
      (p : ℤ) :=
  perfectPowerSumComponent C (modificationProjection f b ≫ f) hQ p

include perfect in
/-- For `v : V' ⟶ X` and equal classes `α`, `α' ∈ A_k(V')`, the class `P_p(Q|_{X × {0}})` applied
to `α` along `v` equals the class `P_p(Q)` applied to `α'` along `v ≫ i_0 : V' ⟶ W`. -/
theorem idRule_powerSumAtZero_heq {V' : Scheme.{u}} (v : V' ⟶ X) [LocallyOfFiniteType v]
    (k : ℤ) (α : chowGroup C (v ≫ f) k)
    (α' : chowGroup C ((v ≫ modificationSectionAtZero f b (haveI := hA; inferInstance)) ≫
      (modificationProjection f b ≫ f)) k) (hα : α ≍ α') :
    (powerSumAtZero C f b hA hQ p).idRule C f (gysinSystemOfInvertible C) v k α ≍
      (powerSumOnModification C f b hQ p).idRule C _ (gysinSystemOfInvertible C)
        (v ≫ modificationSectionAtZero f b (haveI := hA; inferInstance)) k α' := by
  have := hA
  exact idRule_perfectPowerSumComponent_derivedPullback_heq C (modificationProjection f b ≫ f) f
    (modificationSectionAtZero f b inferInstance)
    (by rw [← Category.assoc, modificationSectionAtZero_comp, Category.id_comp]) perfect hQ _ p
    v k α α' hα

include perfect in
/-- For `v : V' ⟶ W_∞` and equal classes `α`, `α' ∈ A_k(V')`, the class `P_p(Q|_{W_∞})` applied to
`α` along `v` equals the class `P_p(Q)` applied to `α'` along `v ≫ (W_∞ ⟶ W) : V' ⟶ W`. -/
theorem idRule_powerSumAtInfinity_heq {V' : Scheme.{u}}
    (v : V' ⟶ modificationFibreAtInfinity f b) [LocallyOfFiniteType v] (k : ℤ)
    (α : chowGroup C (v ≫ (modificationProjectionAtInfinity f b ≫ f)) k)
    (α' : chowGroup C ((v ≫ modificationInclusionAtInfinity f b) ≫
      (modificationProjection f b ≫ f)) k) (hα : α ≍ α') :
    (powerSumAtInfinity C f b hQ p).idRule C _ (gysinSystemOfInvertible C) v k α ≍
      (powerSumOnModification C f b hQ p).idRule C _ (gysinSystemOfInvertible C)
        (v ≫ modificationInclusionAtInfinity f b) k α' :=
  idRule_perfectPowerSumComponent_derivedPullback_heq C (modificationProjection f b ≫ f)
    (modificationProjectionAtInfinity f b ≫ f) (modificationInclusionAtInfinity f b)
    (Category.assoc _ _ _).symm perfect hQ _ p v k α α' hα

variable {f b iV p} in
/-- **Stacks 0F9K, for the classes `P'_p`.** Let `X` be locally of finite type over the base of
chapter 42, let `Z ⊆ X` be a closed subscheme, let `b : W ⟶ 𝐏¹_X` be a proper morphism which is
an isomorphism over `𝐀¹_X` (assumption (A1)), and let `Q ∈ D(𝒪_W)` be a perfect object whose
Chern classes are defined (assumption (A0)). Let `T ⊆ W_∞` be a closed subscheme containing all
points of `W_∞` lying over `X \ Z` such that `Q|_T` is zero (assumption (A2)). Then the class
`P'_p(Q) = (E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C ∈ A^p(Z ⟶ X)` satisfies

  `(Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{X × {0}})`

in `A^p(X)`, where `X × {0}` is identified with `X` by the section at zero and `(Z ⟶ X)_* ∘ -` is
the pushforward of Stacks 0EPK. -/
@[stacks 0F9K "the classes P'_p: the class P'_p(Q) = (E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C in A^p(Z ⟶ X), \
for Q|_T zero, satisfies (Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{X × {0}})"]
theorem properPushforward_localizedPowerSumClassAtInfinity
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :
    properPushforwardLocalizedPowerSumClassAtInfinity C hA jZ hQ perfect hV hzero =
      powerSumAtZero C f b hA hQ p := by
  have := hA
  refine BivariantClass.eq_of_idRule_eq C f (gysinSystemOfInvertible C) _ _ fun g _ k α ↦ ?_
  -- the pieces of `P'_p(Q)`
  set a := localizedPowerSumOnPreimage C jZ hQ perfect hV hzero
  set comp := bivariantCompositeOfInvertible C
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
    (modificationProjectionAtInfinity f b ≫ f) f (preimageInclusion f b jZ)
    (modificationProjectionAtInfinity f b) rfl rfl (p : ℤ) 0 a (gysinAtInfinityClass C f b hA)
  set c4 := bivariantClassCongrDeg C (gysinSystemOfInvertible C)
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) f
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b)
    (comp_comp_structureMorphism_eq rfl rfl) (add_zero (p : ℤ)) comp
  -- step 1: unfold the two pushforwards of Stacks 0EPK down to the projection to `T`
  have e1 : (properPushforwardLocalizedPowerSumClassAtInfinity C hA jZ hQ perfect hV hzero).idRule
        C f (gysinSystemOfInvertible C) g k α =
      chowPush C (pullback.fst (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b) g ≫
          (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)) (g ≫ f)
        (pullback.snd (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b) g)
        (pullbackSnd_comp_structureMorphism_eq C _ f _ (comp_comp_structureMorphism_eq rfl rfl) g)
        (k - p) (c4.cap g k α) := by
    rw [BivariantClass.idRule_apply]
    change chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _) = _
    rw [chowPush_comp C _ _ _ _ _ _ (bivariantPushforwardBaseChange_snd jZ (𝟙 X) g) _ _
        (pullbackSnd_comp_structureMorphism_eq C (jZ ≫ f) f (jZ ≫ 𝟙 X)
          (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) g),
      chowPush_snd_bivariantClassCongr C (gysinSystemOfInvertible C) (jZ ≫ f) f
        (Category.comp_id jZ).symm rfl]
    change chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _) = _
    rw [chowPush_comp C _ _ _ _ _ _ (bivariantPushforwardBaseChange_snd
        (preimageProjection f b jZ) jZ g) _ _
        (pullbackSnd_comp_structureMorphism_eq C _ f _
          (comp_comp_structureMorphism_eq (preimageProjection_comp C f b jZ) rfl) g),
      chowPush_snd_bivariantClassCongr C (gysinSystemOfInvertible C) _ f pullback.condition]
  rw [e1]
  -- step 2: the composite caps by `C` then by `P'_p(Q|_E)`
  set y := (gysinAtInfinityClass C f b hA).cap g k α
  set z := a.cap (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0) y
  have e2 : c4.cap g k α ≍ properChowPushforward C _ _
      (pullbackRightPullbackFstIso (modificationProjectionAtInfinity f b) g
        (preimageInclusion f b jZ)).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp _ _ _ g) (k - 0 - p)
      (properPushforwardDescends C _ _ _ _ _) z := by
    rw [bivariantClassCongrDeg_cap]
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    exact chowGroupDegreeEquiv_heq C _ _ _
  -- step 3: Stacks 0F9I, then push forward to `T`
  have e3 : chowPush C _ (g ≫ f)
        (pullback.snd (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b) g)
        (pullbackSnd_comp_structureMorphism_eq C _ f _ (comp_comp_structureMorphism_eq rfl rfl) g)
        (k - 0 - p)
        (properChowPushforward C _ _
          (pullbackRightPullbackFstIso (modificationProjectionAtInfinity f b) g
            (preimageInclusion f b jZ)).hom
          (pullbackRightPullbackFstIso_hom_comp_fst_comp _ _ _ g) (k - 0 - p)
          (properPushforwardDescends C _ _ _ _ _) z) =
      chowPush C (pullback.fst (modificationProjectionAtInfinity f b) g ≫
          (modificationProjectionAtInfinity f b ≫ f)) (g ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) g)
        (pullbackSnd_comp_structureMorphism_eq C _ f _ rfl g) (k - 0 - p)
        ((powerSumAtInfinity C f b hQ p).idRule C _ (gysinSystemOfInvertible C)
          (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0) y) := by
    rw [← chowPush_closedCoverLocalizedClass_cap C (modificationProjectionAtInfinity f b ≫ f) iV
      (preimageInclusion f b jZ) (range_union_range_preimageInclusion f b jZ iV hV)
      (powerSumAtInfinity C f b hQ p) (powerSumOnPreimage C f b jZ hQ p)
      (chowCohomologyRestriction_powerSumOnPreimage_eq_zero C f b jZ iV hQ perfect p hzero)
      (chowCohomologyRestriction_powerSumAtInfinity_preimage C f b jZ hQ perfect p)
      (chowCohomologyRestriction_powerSumAtInfinity_eq_zero C f b iV hQ perfect p hzero)]
    change chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ z) =
      chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ z)
    rw [chowPush_comp C _ _ _ _ _ _ rfl, chowPush_comp C _ _ _ _ _ _ rfl]
    · exact chowPush_congr C _ _ (pullbackRightPullbackFstIso_hom_snd _ _ _) _ _ _ _
    all_goals
      (try rw [pullbackRightPullbackFstIso_hom_snd])
      rw [Category.assoc, ← pullback.condition_assoc, ← pullback.condition_assoc]
  -- step 4: a lift `β` of `α`, the Gysin map at infinity, and the bivariance of `P_p(Q)`
  obtain ⟨β, hβ⟩ := exists_isLift C f (modificationProjection f b) (chartInclusion f b)
    (relativeDimension_chartInclusion_comp f b) g k α
  have hy : y ≍ infinityGysin C f b g k β := by
    rw [show y = _ from gysinAtInfinityClass_cap_eq_of_isLift C f b hA g hβ, infinityGysin_apply]
    exact chowGroupDegreeEquiv_heq C _ _ _
  refine eq_of_heq ((properChowPushforward_heq C _ _ _ _ (by ring : k - p = k - 0 - p) _
    (properPushforwardDescends C _ _ _ _ _) e2).trans ?_)
  refine (heq_of_eq e3).trans ?_
  rw [← properChowPushforward_infinityGysin_idRule C f b g
    (powerSumOnModification C f b hQ p) (powerSumAtZero C f b hA hQ p)
    (idRule_powerSumAtZero_heq C f b hA hQ perfect p) hβ]
  refine properChowPushforward_heq C _ _ _ _ (by ring : k - 0 - p = k - p) _
    (properPushforwardDescends C _ _ _ _ _) ?_
  refine (IdentityCapRule.heq_congr C _ ((powerSumAtInfinity C f b hQ p).idRule C _
    (gysinSystemOfInvertible C)) rfl (sub_zero k) hy).trans ?_
  exact idRule_infinityGysin_heq C f b g (powerSumOnModification C f b hQ p)
    (powerSumAtInfinity C f b hQ p) (idRule_powerSumAtInfinity_heq C f b hQ perfect p) k β

end Construction

end GysinAtInfinity

end Stacks.Chow

end

-- Stacks 0F9K for the Chern classes: the class `c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C` in
-- `A^p(Z ⟶ X)`, for `Q|_T` finite locally free of rank `< p` in degree `0`, satisfies
-- `(Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{X × {0}})`.
add_to_stacks 0F9K "the classes c'_p: the class c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C in \
A^p(Z ⟶ X), for Q|_T finite locally free of rank < p in degree 0, satisfies \
(Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{X × {0}})"
  Stacks.Chow.GysinAtInfinity.properPushforward_localizedChernClassAtInfinity
