module

public import StacksFrontier.AlgebraicGeometry.Algebraization.StrictDepthMixedComponents
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPointsDepth
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsAlgebraizationII
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternativeProof

/-!
# Recovering the sections of a coherent module from its adic reductions

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. Let `A` be `I`-adically complete with a dualizing
complex and `cd(A, I) ≤ d` for some `d ≥ 1`, and let `ℱ` be a coherent `𝒪_U`-module whose
completion along `I𝒪_U` satisfies the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3].
If moreover `depth(ℱ_x) ≥ 2` at every `x ∈ U` whose closure meets `Y` only inside `Z`, then

`H⁰(U, ℱ) ⟶ lim H⁰(U, ℱ/Iⁿℱ)`

is an isomorphism. This is [Stacks, Tag 0EJ6].

## Main results

* `Stacks.Algebraization.isIso_globalToFormalSections_of_satisfiesStrictDepthInequalities` —
  **Stacks Tag 0EJ6**.
* `Stacks.Algebraization.associatedPointsClosureDimensionBound_of_satisfiesStrictDepthInequalities`
  — its content: condition (2) of [Stacks, Tag 0EIG] follows from the strict inequalities.

## Implementation notes

### The shape of the proof

[Stacks, Tag 0EIG] — `Stacks.Algebraization.FormalSectionsII.isIso_globalToFormalSections` —
already makes the displayed arrow an isomorphism under three conditions, of which (1) and (3)
are hypotheses of [Stacks, Tag 0EJ6] verbatim. All the work is condition (2),
`Stacks.Algebraization.AssociatedPointsClosureDimensionBound`: for `x ∈ Ass(ℱ)` outside `Y`
whose closure `W = \overline{\{x\}}` meets `Y` outside `Z`, and for every `z ∈ W ∩ Z`,
`dim(𝒪_{W, z}) > cd(A, I) + 1`. It is deduced in three steps.

* Since `x` is an associated point, `depth(ℱ_x) = 0`
  (`Stacks.Divisors.notMem_associatedPoints_of_one_le_depth`), so
  [Stacks, Tag 0EJ5] rules out the mixed-components configuration at `x`: the irreducible
  component of `W ∩ Y` through `z` cannot lie inside `Z`, because `W ∩ Y ⊄ Z` already supplies
  a component that does not. This is
  `Stacks.Algebraization.notSubset_closedSubsetZ_irreducibleComponent_of_mem_associatedPoints`.
* That component therefore has a generic point outside `Z` specializing to `z`, so
  [Stacks, Tag 02IM] produces an immediate generalization `r ⤳ z` inside `W ∩ Y` and outside
  `Z`, at distance exactly `1` from `Z`. This is
  `Stacks.Algebraization.exists_distanceToZ_eq_one_lt_of_notSubset_closedSubsetZ`.
* At the point `y ∈ U` that `r` determines, `dim(𝒪_{W, y}) > d`
  (`Stacks.Algebraization.lt_height_map_quotient_of_mem_associatedPoints`): were it at most
  `d`, the prime of `𝒪_{U,y}^∧` of [Stacks, Tag 0EHW] would make the strict inequalities force
  `depth(ℱ_x) ≥ 1`, which an associated point does not have. Since `𝔭_y < 𝔭_z` strictly,
  `dim(𝒪_{W, z}) > 1 + d ≥ cd(A, I) + 1`.

### Stacks 0EIF

[Stacks, Tag 0EIF] enters twice: through [Stacks, Tag 0EJ5], and as the first input of
`Stacks.Algebraization.FormalSectionsII.isIso_globalToFormalSections`. Both are supplied by
`Stacks.Algebraization.serreOneAlternativeComparison`, so no hypothesis beyond the source's
conditions (1), (2) and (3) is made.

### Relative dimension as a height

`Stacks.Algebraization.closureLocalDimension A 𝔭 𝔮`, the invariant condition (2) is phrased
with, is the dimension of the interval of primes between `𝔭` and `𝔮`, and it is the height of
the image of `𝔮` in `A/𝔭`: that is
`Stacks.Algebraization.closureLocalDimension_eq_height_map_quotient`, the composite of
`Stacks.Algebraization.closureLocalDimension_eq_ringKrullDim_quotient_localizationAtPrime`
with [Stacks, Tag 0EHW]. Heights are the currency the inputs speak — the prime of the completed
local ring comes from a height bound in `A/𝔭_x` — and the step from `y` to `z` is then
`Ideal.height_le_iff`, applied to the strict inclusion `𝔭_y < 𝔭_z`.

## References

* [Stacks Project, Tag 0EJ6](https://stacks.math.columbia.edu/tag/0EJ6)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0EIG](https://stacks.math.columbia.edu/tag/0EIG), the criterion applied.
* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5), the depth-one bound.
* [Stacks Project, Tag 02IM](https://stacks.math.columbia.edu/tag/02IM), the immediate
  generalization.
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW), the relative dimension.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Depth zero at an associated point -/

/-- **An associated point of a coherent module has no positive depth.** The stalk of `ℱ` at an
associated point carries an element annihilated by exactly the maximal ideal, so no element of
the maximal ideal acts regularly on it. The depth is taken in the
`Stacks.Algebraization.stalkModuleFunctor` spelling, which is the one
[Stacks, Tag 0EJ5] concludes in; it agrees with the spelling of
`Stacks.Divisors.associatedPoints` by
`Stacks.Algebraization.depth_stalkModuleFunctor_eq_depth_stalkModule`. -/
public theorem not_one_le_depth_stalkModuleFunctor_of_mem_associatedPoints {X : Scheme.{u}}
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (x : X)
    (hx : x ∈ Stacks.Divisors.associatedPoints F.obj) :
    ¬ 1 ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      ((stalkModuleFunctor x).obj F.obj) := by
  have : F.obj.IsCoherent := F.property
  intro hone
  exact Stacks.Divisors.notMem_associatedPoints_of_one_le_depth F.obj x
    (hone.trans_eq (depth_stalkModuleFunctor_eq_depth_stalkModule F.obj x)) hx

/-! ### The relative dimension as a height -/

/-- **The dimension of the interval of primes between `𝔭` and `𝔮` is the height of the image of
`𝔮` in `A/𝔭`.** Both compute the Krull dimension of the spectrum of the local ring of
`V(𝔭)` at `𝔮`: on the left as the interval itself, on the right through the localized
quotient of [Stacks, Tag 0EHW]. -/
public theorem closureLocalDimension_eq_height_map_quotient {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    closureLocalDimension A p q =
      (((q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height : ℕ∞) : WithBot ℕ∞) :=
  (closureLocalDimension_eq_ringKrullDim_quotient_localizationAtPrime p q).trans
    (Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime p.asIdeal
      q.asIdeal hpq)

/-- Taking the image in `A/𝔭` is injective on the ideals containing `𝔭`: the quotient map is
surjective, so an ideal containing `𝔭` is recovered from its image by contraction. -/
private theorem comap_map_quotientMk {A : Type u} [CommRing A] {p q : Ideal A} (hpq : p ≤ q) :
    (q.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = q := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.mpr hpq

/-- An integer bounded by a natural number `n` is, in the extended integers, strictly below the
image of any extended natural number that is not at most `n`. -/
private theorem intCast_lt_enatToEInt {h : ℕ∞} {n : ℕ} {m : ℤ} (hmn : m ≤ (n : ℤ))
    (hnh : ¬ h ≤ (n : ℕ∞)) : ((m : ℤ) : EInt) < enatToEInt h := by
  induction h using ENat.recTopCoe with
  | top =>
    refine lt_of_lt_of_le ?_ (le_of_eq (show (⊤ : EInt) = enatToEInt (⊤ : ℕ∞) from rfl))
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (m : ℤ))
  | coe k =>
    have hk : n < k := by
      by_contra hc
      exact hnh (Nat.cast_le.mpr (Nat.le_of_not_lt hc))
    refine WithBotTop.coe_lt_coe.mpr ?_
    omega

/-- **The relative dimension exceeds an integer bound once the height does.** If the height of
the image of `𝔮` in `A/𝔭` is not at most `n`, then `dim((A/𝔭)_𝔮)` is more than any integer `m`
bounded by `n`. -/
private theorem lt_krullDimToEInt_closureLocalDimension {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) {n : ℕ} {m : ℤ} (hmn : m ≤ (n : ℤ))
    (h : ¬ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height ≤ (n : ℕ∞)) :
    ((m : ℤ) : EInt) < krullDimToEInt (closureLocalDimension A p q) := by
  rw [closureLocalDimension_eq_height_map_quotient p q hpq,
    show krullDimToEInt
          ((((q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height : ℕ∞) : WithBot ℕ∞)) =
        enatToEInt (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height from by
      cases (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height using ENat.recTopCoe <;> rfl]
  exact intCast_lt_enatToEInt hmn h

/-! ### The immediate generalization inside the closed fibre -/

/-- **[Stacks, Tag 02IM] inside the closed fibre of a closure.** Let `x ∈ U` and let `z` be a
point of `Y` lying over `closure {x}` and inside `Z`. Suppose the irreducible component through
`z` of the closed fibre `W = Y ∩ \overline{\{x\}}` is not contained in `Z`. Then there is a
point `y ∈ U`, lying over a point `r` of `Y` at distance exactly `1` from `Z`, with `x ⤳ y` and
`𝔭_y < 𝔭_z`.

The component through `z` has a generic point, which lies outside `Z` — otherwise the whole
component, being its closure, would lie in the closed set `Z` — and which specializes to `z`.
So the locally closed set `W ∖ Z` meets every neighbourhood of `z` along a generalization, and
[Stacks, Tag 02IM] produces an immediate generalization `r` of `z` inside it;
`Stacks.Algebraization.distanceFunction_eq_one_of_isImmediateSpecialization_of_notMem` then
puts `r` at distance exactly `1`. -/
public theorem exists_distanceToZ_eq_one_lt_of_notSubset_closedSubsetZ
    (S : AlgebraizationSituation.{u})
    (hYcat : IrreducibleClosedsCodim.IsCatenarySpace S.Y)
    (x : S.U.toScheme) (z : S.Y)
    (hzW : z ∈ S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X))
    (hzZ : z ∈ (S.closedSubsetZ : Set S.Y))
    (hcomp : ¬ irreducibleComponent
        (⟨z, hzW⟩ : ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X))) ⊆
      {w | w.1 ∈ (S.closedSubsetZ : Set S.Y)}) :
    ∃ (y : S.U.toScheme) (r : S.Y), S.U.ι.base y = S.Yι.base r ∧ S.distanceToZ r = 1 ∧
      x ⤳ y ∧ (S.U.ι.base y).asIdeal < (S.Yι.base z).asIdeal := by
  classical
  have hWclosed : IsClosed (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) :=
    isClosed_closure.preimage S.Yι.continuous
  let _ : QuasiSober ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) :=
    hWclosed.isClosedEmbedding_subtypeVal.quasiSober
  have hCcomp : irreducibleComponent
      (⟨z, hzW⟩ : ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X))) ∈
    irreducibleComponents ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) :=
    irreducibleComponent_mem_irreducibleComponents _
  let η := genericPoints.ofComponent (⟨_, hCcomp⟩ :
    irreducibleComponents ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)))
  have hηgen : IsGenericPoint η.1 (irreducibleComponent
      (⟨z, hzW⟩ : ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)))) :=
    genericPoints.isGenericPoint_ofComponent _
  have hηnotZ : η.1.1 ∉ (S.closedSubsetZ : Set S.Y) := by
    intro hmem
    refine hcomp ?_
    rw [← hηgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hmem)
      (S.closedSubsetZ.isClosed.preimage continuous_subtype_val)
  have hηz : η.1.1 ⤳ z :=
    (hηgen.specializes mem_irreducibleComponent).map continuous_subtype_val
  have hne : η.1.1 ≠ z := fun h => hηnotZ (h ▸ hzZ)
  have hE : IsLocallyClosed ((S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) \
      (S.closedSubsetZ : Set S.Y)) := by
    rw [Set.sdiff_eq]
    exact hWclosed.isLocallyClosed.inter
      S.closedSubsetZ.isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨r, hrE, hrimm⟩ :=
    AlgebraicGeometry.exists_isImmediateSpecialization_mem_of_isLocallyClosed S.Y hE
      ⟨η.1.2, hηnotZ⟩ hηz hne
  have hrange : Set.range S.Zι.base = PrimeSpectrum.zeroLocus (S.a : Set S.A) := by
    have h := _root_.range_comap_of_surjective (S.A ⧸ S.a) (Ideal.Quotient.mk S.a)
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at h
    exact h
  have hrU : S.Yι.base r ∈ S.U := by
    have hnot : S.Yι.base r ∉ Set.range S.Zι.base := fun hmem =>
      hrE.2 ((mem_closedSubsetZ_iff_mem_range_Zι S r).mpr hmem)
    rw [hrange] at hnot
    exact hnot
  refine ⟨⟨S.Yι.base r, hrU⟩, r, rfl,
    distanceFunction_eq_one_of_isImmediateSpecialization_of_notMem S.Y S.closedSubsetZ hYcat
      hrimm hzZ hrE.2, ?_, ?_⟩
  · exact S.U.ι.isOpenEmbedding.isEmbedding.specializes_iff.mp
      (specializes_iff_mem_closure.mpr hrE.1)
  · refine lt_of_le_of_ne
      ((PrimeSpectrum.le_iff_specializes _ _).mpr (hrimm.1.map S.Yι.continuous))
      fun heq => hrimm.2.1 ?_
    exact S.Yι.isClosedEmbedding.injective (PrimeSpectrum.ext heq)

/-! ### The component through a point of `W ∩ Z` is not inside `Z` -/

/-- **[Stacks, Tag 0EJ5] rules out a component inside `Z` at an associated point.** Let `ℱ` be a
coherent `𝒪_U`-module whose completion satisfies the strict `(1, 1 + d)`-inequalities, let
`x ∈ Ass(ℱ)` and suppose the closed fibre `W ∩ Y` of `W = \overline{\{x\}}` has a point outside
`Z`. Then no irreducible component of `W ∩ Y` lies inside `Z`.

Were there one, the closed fibre would have components on both sides of `Z` and
`Stacks.Algebraization.one_le_depth_stalk_of_mixed_irreducibleComponents` would give
`depth(ℱ_x) ≥ 1`, which an associated point does not have. -/
public theorem notSubset_closedSubsetZ_irreducibleComponent_of_mem_associatedPoints
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : cohomologicalDimension S.A S.I S.I.fg_of_isNoetherianRing ≤ d)
    (hstrict : SatisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) 1 (1 + d))
    (x : S.U.toScheme) (hxass : x ∈ Stacks.Divisors.associatedPoints F.obj)
    (w : S.Y) (hwW : w ∈ S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X))
    (hwZ : w ∉ (S.closedSubsetZ : Set S.Y))
    (C : Set ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)))
    (hC : C ∈ irreducibleComponents ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X))) :
    ¬ C ⊆ {v | v.1 ∈ (S.closedSubsetZ : Set S.Y)} := by
  intro hCZ
  have hZeq : {v : ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) |
        S.Yι.base v.1 ∈ Set.range S.Zι.base} =
      {v | v.1 ∈ (S.closedSubsetZ : Set S.Y)} := by
    ext v
    exact (mem_closedSubsetZ_iff_mem_range_Zι S v.1).symm
  refine not_one_le_depth_stalkModuleFunctor_of_mem_associatedPoints F x hxass
    (one_le_depth_stalk_of_mixed_irreducibleComponents S F d hd K hK hcd hstrict x ?_)
  refine ⟨⟨C, hC, hZeq ▸ hCZ⟩, irreducibleComponent
      (⟨w, hwW⟩ : ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X))),
    irreducibleComponent_mem_irreducibleComponents _, fun hsub => hwZ ?_⟩
  exact (hZeq ▸ hsub) mem_irreducibleComponent

/-! ### The relative dimension at the immediate generalization -/

/-- **The relative codimension of `y` in `\overline{\{x\}}` exceeds `d`.** Let `x ∈ Ass(ℱ)` with
`I ⊄ 𝔭_x`, and let `y ∈ U` be a point of `Y` at distance exactly `1` from `Z` with `x ⤳ y`.
Then the height of `𝔭_y` in `A/𝔭_x` is more than `d`.

Were it at most `d`, the prime `𝔭` of `𝒪_{U,y}^∧` of
`Stacks.Algebraization.exists_primeSpectrum_completedLocalRing_of_specializes` would have
`dim(𝒪_{U,y}^∧/𝔭) ≤ d`, so the strict `(1, 1 + d)`-inequalities would give
`depth((ℱ_y^∧)_𝔭) ≥ 1`, which is `depth(ℱ_x)` by [Stacks, Tag 0338] and [Stacks, Tag 0EHW];
an associated point has no positive depth. -/
public theorem lt_height_map_quotient_of_mem_associatedPoints
    (S : AlgebraizationSituation.{u})
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (d : ℤ) (hd : 1 ≤ d) (hcat : Ring.IsUniversallyCatenary S.A)
    (hstrict : SatisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) 1 (1 + d))
    (x : S.U.toScheme) (hxass : x ∈ Stacks.Divisors.associatedPoints F.obj)
    (hxnotI : ¬ S.I ≤ (S.U.ι.base x).asIdeal)
    (y : S.U.toScheme) (r : S.Y) (hyr : S.U.ι.base y = S.Yι.base r)
    (hdist : S.distanceToZ r = 1) (hxy : x ⤳ y) :
    ¬ ((S.U.ι.base y).asIdeal.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)).height
      ≤ (d.toNat : ℕ∞) := by
  intro hheight
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  let _ : Algebra (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x) :=
    (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.toAlgebra
  obtain ⟨P, hover, hmin, hJnot, hdimP⟩ :=
    exists_primeSpectrum_completedLocalRing_of_specializes S x y hxy r hyr hcat hxnotI d
      (by omega) hheight
  let _ := hover
  exact not_one_le_depth_stalkModuleFunctor_of_mem_associatedPoints F x hxass
    (one_le_depth_stalk_of_one_le_completedStalkDepth (idealOnOpen S) F hxy P hmin
      (one_le_completedStalkDepth_of_satisfiesStrictDepthInequalities S
        ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) d hstrict y r hyr hdist P
        hJnot hdimP))

/-! ### Condition (2) of Stacks 0EIG -/

/-- **The strict `(1, 1 + d)`-inequalities give condition (2) of [Stacks, Tag 0EIG].** Let `A`
be `I`-adically complete with a dualizing complex and `cd(A, I) ≤ d`, `d ≥ 1`, and let `ℱ` be a
coherent `𝒪_U`-module whose completion along `I𝒪_U` satisfies the strict
`(1, 1 + d)`-inequalities. Then for every associated point `x` of `ℱ` outside `Y` whose closure
meets `Y` outside `Z`, every point `z` of `\overline{\{x\}} ∩ Z` has
`dim(𝒪_{\overline{\{x\}}, z}) > cd(A, I) + 1`.

The component of the closed fibre through `z` is not inside `Z`, so an immediate generalization
`r ⤳ z` sits in the closed fibre outside `Z`, at distance one; the relative codimension of the
point `y ∈ U` it determines is more than `d`, and `𝔭_y < 𝔭_z` raises that by one more. -/
public theorem associatedPointsClosureDimensionBound_of_satisfiesStrictDepthInequalities
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : cohomologicalDimension S.A S.I S.I.fg_of_isNoetherianRing ≤ d)
    (hstrict : SatisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) 1 (1 + d)) :
    AssociatedPointsClosureDimensionBound S.A S.I S.a F.obj := by
  intro x hxass hxnotI hnotSub z hxz haz
  have hrangeY : Set.range S.Yι.base = PrimeSpectrum.zeroLocus (S.I : Set S.A) := by
    have h := _root_.range_comap_of_surjective (S.A ⧸ S.I) (Ideal.Quotient.mk S.I)
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at h
    exact h
  have hrangeZ : Set.range S.Zι.base = PrimeSpectrum.zeroLocus (S.a : Set S.A) := by
    have h := _root_.range_comap_of_surjective (S.A ⧸ S.a) (Ideal.Quotient.mk S.a)
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at h
    exact h
  obtain ⟨zY, hzY⟩ : z ∈ Set.range S.Yι.base := by
    rw [hrangeY]
    exact (PrimeSpectrum.mem_zeroLocus z (S.I : Set S.A)).mpr (S.I_le_a.trans haz)
  obtain ⟨w, hxw, hwI, hwa⟩ := hnotSub
  obtain ⟨wY, hwY⟩ : w ∈ Set.range S.Yι.base := by
    rw [hrangeY]
    exact (PrimeSpectrum.mem_zeroLocus w (S.I : Set S.A)).mpr hwI
  have hzW : zY ∈ S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X) := by
    rw [Set.mem_preimage, hzY]
    exact specializes_iff_mem_closure.mp ((PrimeSpectrum.le_iff_specializes _ _).mp hxz)
  have hwW : wY ∈ S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X) := by
    rw [Set.mem_preimage, hwY]
    exact specializes_iff_mem_closure.mp ((PrimeSpectrum.le_iff_specializes _ _).mp hxw)
  have hzZ : zY ∈ (S.closedSubsetZ : Set S.Y) := by
    refine (mem_closedSubsetZ_iff_mem_range_Zι S zY).mpr ?_
    rw [hrangeZ, hzY]
    exact (PrimeSpectrum.mem_zeroLocus z (S.a : Set S.A)).mpr haz
  have hwZ : wY ∉ (S.closedSubsetZ : Set S.Y) := by
    intro hmem
    refine hwa ?_
    have hmem' := (mem_closedSubsetZ_iff_mem_range_Zι S wY).mp hmem
    rw [hrangeZ, hwY] at hmem'
    exact (PrimeSpectrum.mem_zeroLocus w (S.a : Set S.A)).mp hmem'
  obtain ⟨y, r, hyr, hdist, hxy, hlt⟩ :=
    exists_distanceToZ_eq_one_lt_of_notSubset_closedSubsetZ S
      (isCatenarySpace_of_isCatenary
        (Dualizing.isUniversallyCatenary_of_isDualizingComplex hK (S.A ⧸ S.I))) x zY hzW hzZ
      (notSubset_closedSubsetZ_irreducibleComponent_of_mem_associatedPoints S F d hd K hK hcd
        hstrict x hxass wY hwW hwZ _
        (irreducibleComponent_mem_irreducibleComponents
          (⟨zY, hzW⟩ : ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)))))
  rw [hzY] at hlt
  have hynot := lt_height_map_quotient_of_mem_associatedPoints S F d hd
    (Dualizing.isUniversallyCatenary_of_isDualizingComplex hK) hstrict x hxass hxnotI y r hyr
    hdist hxy
  have hxyle : (S.U.ι.base x).asIdeal ≤ (S.U.ι.base y).asIdeal :=
    baseIdeal_le_underlyingPrime_of_specializes S x y hxy
  have hznot : ¬ (z.asIdeal.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)).height
      ≤ ((d.toNat + 1 : ℕ) : ℕ∞) := by
    intro hle
    refine hynot ?_
    have : z.asIdeal.IsPrime := z.2
    have : (S.U.ι.base y).asIdeal.IsPrime := (S.U.ι.base y).2
    have : (z.asIdeal.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime (hxyle.trans hlt.le)
    have hpy : ((S.U.ι.base y).asIdeal.map
        (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hxyle
    have hmaplt : (S.U.ι.base y).asIdeal.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) <
        z.asIdeal.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) := by
      refine lt_of_le_of_ne (Ideal.map_mono hlt.le) fun heq => hlt.ne ?_
      rw [← comap_map_quotientMk hxyle, heq, comap_map_quotientMk (hxyle.trans hlt.le)]
    exact (ENat.lt_add_one_iff (ENat.natCast_ne_top d.toNat)).mp
      (by simpa using (Ideal.height_le_iff.mp hle) _ hpy hmaplt)
  exact lt_krullDimToEInt_closureLocalDimension (S.U.ι.base x) z hxz (by omega) hznot

/-! ### Stacks 0EJ6 -/

/-- **Stacks Project, Tag 0EJ6.** Let `A` be a Noetherian ring with ideals `I ⊆ 𝔞`, write
`X = Spec(A)`, `Y = V(I)`, `Z = V(𝔞)`, `U = X ∖ Z`, and let `ℱ` be a coherent `𝒪_U`-module and
`d ≥ 1`. Assume

1. `A` is `I`-adically complete, has a dualizing complex, and `cd(A, I) ≤ d`,
2. the completion `ℱ^∧` of `ℱ` along `I𝒪_U` satisfies the strict `(1, 1 + d)`-inequalities of
   [Stacks, Tag 0EJ3], and
3. `depth(ℱ_x) ≥ 2` for every `x ∈ U` with `\overline{\{x\}} ∩ Y ⊆ Z`.

Then

  `H⁰(U, ℱ) ⟶ lim H⁰(U, ℱ/Iⁿℱ)`

is an isomorphism. That arrow is
`Stacks.Algebraization.FormalSectionsII.globalToFormalSections`, whose `n`-th component is
reduction modulo `Iⁿ` by
`Stacks.Algebraization.FormalSectionsII.globalToFormalSections_proj`.

[Stacks, Tag 0EIG] supplies the conclusion from conditions (1), (3) and its own condition (2),
the dimension bound at the associated points of `ℱ`; that bound is
`Stacks.Algebraization.associatedPointsClosureDimensionBound_of_satisfiesStrictDepthInequalities`,
which is where condition (2) here and [Stacks, Tag 0EJ5] are consumed. -/
@[stacks 0EJ6 "H^0(U,F) = lim H^0(U,F/I^nF) under the strict (1,1+d)-inequalities and depth \
two off the formal locus"]
public theorem isIso_globalToFormalSections_of_satisfiesStrictDepthInequalities
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : cohomologicalDimension S.A S.I S.I.fg_of_isNoetherianRing ≤ d)
    (hstrict : SatisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) 1 (1 + d))
    (hdepth : FormalSectionsII.DepthTwoOffFormalLocus S.A S.I S.a F.obj) :
    IsIso (FormalSectionsII.globalToFormalSections S.A S.I S.a F.obj) :=
  @FormalSectionsII.isIso_globalToFormalSections S.A _ S.I S.a F.obj _ F.property
    S.I_le_a inferInstance ⟨K, hK⟩
    (associatedPointsClosureDimensionBound_of_satisfiesStrictDepthInequalities S F d hd K hK
      hcd hstrict)
    hdepth serreOneAlternativeComparison middleComparisonOfShortExact
    (associatedPointSplitting S.A S.I S.a)

end Stacks.Algebraization

end
