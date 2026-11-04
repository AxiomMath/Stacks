module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexPowerSum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectTwist
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristicRank
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksCore.Tactic.StacksAttribute
/-!
# The classes `P_p(E)` of a perfect object: Stacks 0GUD for the power sums

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E ∈ D(𝒪_X)` be an object whose Chern classes are defined: some
envelope `f : Y ⟶ X` has `Lf^*E` represented by a locally bounded complex `𝓔^•` of finite
locally free modules (Stacks 0F9E (1)). The rank `r(E)`, the classes `P_p(E) ∈ A^p(X)` and
`ch_p(E) ∈ A^p(X) ⊗ 𝐐` of Definition 0F9E (2) are `Stacks.Chow.perfectRankClass`,
`Stacks.Chow.perfectPowerSumComponent` and `Stacks.Chow.perfectChernCharacterComponent`.
**Stacks 0GUD** asserts that `P_p(E)` is the unique class whose restriction along every such
envelope is the class `P_p(𝓔^•)` of Lemma 0ESZ, and likewise for `ch_p(E)` and `c(E)`; this file
registers those statements and computes the classes for a perfect object.

* In degree `0`, `r(E)` is, on the open and closed subscheme where the Euler characteristic
  `χ(E ⊗^L κ(x))` of the derived fibres equals `n`, the class `n` times the unit
  (`Stacks.Chow.perfectRankClass_eq_glue_eulerLoci`): on a rank locus of a presentation `𝓔^•`
  this Euler characteristic is `∑ (-1)^n rank(𝓔^n)`.
* In degree `p ≥ 1`, `P_p(E)` is the power sum `P_p(c_1(E), …, c_p(E))` of the Chern classes,
  the rank not entering Newton's recursion in positive degrees
  (`Stacks.Chow.perfectPowerSumComponent_succ`).

## Main definitions

* `Stacks.Chow.eulerLocus` — the open and closed subscheme where the derived-fibre Euler
  characteristic of `E` is `n`.
* `Stacks.Chow.perfectPowerSumTotal` — the family `(P_p(E))_p` as one total class.

## Main results

* `Stacks.Chow.existsUnique_perfectPowerSum` — **Stacks 0GUD for the power sums**.
* `Stacks.Chow.existsUnique_perfectChernCharacter` — **Stacks 0GUD for the Chern character**.
* The total Chern class part of Stacks 0GUD is
  `Stacks.Chow.existsUnique_forall_res_eq_complexChern`, registered here.
* `Stacks.Chow.chowCohomologyRestriction_perfectPowerSumComponent_eq_zero` — if `E|_Z` is zero,
  then the restriction of `P_p(E)` to `Z` vanishes.

## References

* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The rank of a perfect object -/

section Rank

variable {X : Scheme.{u}} {E : DerivedCategory X.Modules}
  (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)

/-- **The locus where the derived-fibre Euler characteristic of a perfect object is `n`**, an
open subscheme, the Euler characteristic being locally constant (Stacks 0BDJ). -/
def eulerLocus (n : ℤ) : X.Opens :=
  ⟨{x | DerivedFibreBetti.chiDerivedFibre X E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect) x = n},
    (DerivedFibreBetti.isLocallyConstant_chiDerivedFibre X E perfect).isOpen_fiber n⟩

/-- A point lies in `eulerLocus n` exactly when the derived-fibre Euler characteristic of `E` at
it is `n`. -/
theorem mem_eulerLocus {n : ℤ} {x : X} :
    x ∈ eulerLocus perfect n ↔ DerivedFibreBetti.chiDerivedFibre X E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect) x = n :=
  Iff.rfl

/-- The family of the loci `eulerLocus n`, indexed in the universe of the scheme. -/
abbrev eulerLoci : ULift.{u} ℤ → X.Opens := fun n ↦ eulerLocus perfect n.down

/-- The loci where the Euler characteristic takes a given value decompose `X` into open and
closed subschemes. -/
theorem isClopenDecomposition_eulerLoci : IsClopenDecomposition (eulerLoci perfect) where
  disjoint i j hij := Opens.coe_disjoint.mp <| Set.disjoint_left.mpr fun _ hx hy ↦
    hij (congrArg ULift.up (((mem_eulerLocus perfect).mp hx).symm.trans
      ((mem_eulerLocus perfect).mp hy)))
  iSup_eq_top := by
    apply top_le_iff.mp
    intro x _
    simp only [Opens.mem_iSup]
    exact ⟨ULift.up _, (mem_eulerLocus perfect).mpr rfl⟩

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The derived-fibre Euler characteristic of a zero object vanishes. -/
theorem chiDerivedFibre_eq_zero_of_isZero {Z : Scheme.{u}} {F : DerivedCategory Z.Modules}
    (hF : IsZero F) (hpc : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace) F) (z : Z) :
    DerivedFibreBetti.chiDerivedFibre Z F hpc z = 0 := by
  rw [DerivedFibreBetti.chiDerivedFibre_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
  have := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
    (Z.fromSpecResidueField z).toLRSHom.toShHom).right_adjoint_additive
  have := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
    (Z.fromSpecResidueField z).toLRSHom.toShHom).left_adjoint_additive
  have := ModuleCat.subsingleton_of_isZero
    (Functor.map_isZero (moduleSpecΓFunctor (R := Z.residueField z))
      (Functor.map_isZero (DerivedCategory.homologyFunctor (Spec (Z.residueField z)).Modules i)
        (Functor.map_isZero (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (Z.fromSpecResidueField z).toLRSHom.toShHom) hF)))
  rw [DerivedFibreBetti.derivedFiberBetti_apply, Module.finrank_zero_of_subsingleton]
  simp

/-- **The Euler characteristic on a rank locus of a presentation** is the alternating sum of the
ranks of the terms of the presenting complex. -/
theorem chiDerivedFibre_eq_sum_of_mem_complexRankLocus (H : EnvelopePresentation E) (ρ : ℤ →₀ ℕ)
    (y : complexRankLocus H.locallyBounded ρ) :
    DerivedFibreBetti.chiDerivedFibre X E
        (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect)
        (H.f.base ((complexRankLocus H.locallyBounded ρ).ι.base y)) =
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ) := by
  have hpc := DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect
  have hrank := isFiniteLocallyFreeOfRank_complexRankLocus H.locallyBounded ρ
  have e := H.pullbackRepresentation (complexRankLocus H.locallyBounded ρ).ι
  have hpcf := DerivedFibreBetti.isPseudoCoherent_derivedPullback
    ((complexRankLocus H.locallyBounded ρ).ι ≫ H.f) E hpc
  have hpcP : RingedSpace.IsPseudoCoherent (X := (complexRankLocus H.locallyBounded
      ρ).toScheme.toRingedSpace)
      (DerivedCategory.Q.obj (pullbackComplex (complexRankLocus H.locallyBounded ρ).ι H.P)) := by
    obtain ⟨K, hK, ⟨w⟩⟩ := hpcf
    exact ⟨K, hK, ⟨w ≪≫ e⟩⟩
  have hbounded : {i : ℤ | ¬ IsZero ((pullbackComplex (complexRankLocus H.locallyBounded ρ).ι
      H.P).X i)}.Finite := by
    refine ρ.support.finite_toSet.subset fun i hi ↦ ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    have := hrank i
    rw [h0] at this
    exact hi (isZero_of_isFiniteLocallyFreeOfRank_zero _)
  have h1 := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback ((complexRankLocus
      H.locallyBounded ρ).ι ≫ H.f) E hpc) y
  have h2 := congrFun (DerivedFibreBetti.chiDerivedFibre_congr (complexRankLocus H.locallyBounded
      ρ).toScheme hpcf hpcP e) y
  have h3 := DerivedFibreBetti.chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank
      (complexRankLocus H.locallyBounded ρ).toScheme
    (pullbackComplex (complexRankLocus H.locallyBounded ρ).ι H.P) hbounded ρ hrank hpcP y
  exact h1.symm.trans (h2.trans h3)

/-- The class glued from `n` times the unit on the locus where the Euler characteristic is `n`
restricts, along a morphism landing in the locus where it is `m`, to `m` times the unit. -/
theorem res_glue_eulerLoci_of_range {Z : Scheme.{u}} (h : Z ⟶ X) [LocallyOfFiniteType h]
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (hs : h ≫ sX = sZ) (m : ℤ)
    (hrange : Set.range h.base ⊆ (eulerLocus perfect m : Set X)) :
    TotalChowClass.res h hs (TotalChowClass.glue (C := C) (sY := sX)
      (isClopenDecomposition_eulerLoci perfect) fun n ↦ (n.down : ℤ) • 1) = m • 1 := by
  subst hs
  set h' := IsOpenImmersion.lift (eulerLocus perfect m).ι h
    (by rwa [Scheme.Opens.range_ι])
  have hh : h' ≫ (eulerLocus perfect m).ι = h := IsOpenImmersion.lift_fac _ _ _
  have : LocallyOfFiniteType (h' ≫ (eulerLocus perfect m).ι) := by rw [hh]; infer_instance
  have : LocallyOfFiniteType h' := locallyOfFiniteType_of_comp h' (eulerLocus perfect m).ι
  rw [TotalChowClass.res_congr hh.symm rfl (by rw [hh]), ← TotalChowClass.res_res
    (eulerLocus perfect m).ι rfl h' (by rw [← Category.assoc, hh]),
    TotalChowClass.res_glue (isClopenDecomposition_eulerLoci perfect) _ (ULift.up m), map_zsmul,
    map_one]

/-- **The rank `r(E)` of a perfect object whose Chern classes are defined, by Euler
characteristics**: on the open and closed subscheme where the Euler characteristic of the
derived fibres of `E` is `n`, the class `r(E)` of Definition 0F9E (2) is `n` times the unit. On
a rank locus of a presentation `𝓔^•` this Euler characteristic is `∑ (-1)^n rank(𝓔^n)`, the
value of the alternating rank class there. -/
theorem perfectRankClass_eq_glue_eulerLoci (hE : HasDefinedChernClasses E) :
    perfectRankClass C sX hE = TotalChowClass.glue (C := C) (sY := sX)
      (isClopenDecomposition_eulerLoci perfect) fun n ↦ (n.down : ℤ) • 1 := by
  refine (eq_perfectRankClass C sX hE hE.some ?_).symm
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci
    hE.some.locallyBounded) fun ρ ↦ ?_
  show TotalChowClass.res (complexRankLocus hE.some.locallyBounded ρ.down).ι rfl _ =
    TotalChowClass.res (complexRankLocus hE.some.locallyBounded ρ.down).ι rfl _
  rw [res_complexRankClass_complexRankLocus, TotalChowClass.res_res,
    res_glue_eulerLoci_of_range perfect C sX _ _
      (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ.down n : ℤ))]
  rintro _ ⟨z, rfl⟩
  exact (mem_eulerLocus perfect).mpr
    (chiDerivedFibre_eq_sum_of_mem_complexRankLocus perfect hE.some ρ.down z)

/-- **The restriction of the rank along a morphism landing in one Euler locus**: if
`h : Z ⟶ X` lands in the locus where the Euler characteristic of `E` is `m`, the restriction of
`r(E)` to `Z` is `m` times the unit. -/
theorem res_perfectRankClass_of_range (hE : HasDefinedChernClasses E) {Z : Scheme.{u}}
    (h : Z ⟶ X) [LocallyOfFiniteType h] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
    (hs : h ≫ sX = sZ) (m : ℤ) (hrange : Set.range h.base ⊆ (eulerLocus perfect m : Set X)) :
    TotalChowClass.res h hs (perfectRankClass C sX hE) = m • 1 := by
  rw [perfectRankClass_eq_glue_eulerLoci perfect C sX hE]
  exact res_glue_eulerLoci_of_range perfect C sX h hs m hrange

include perfect in
/-- **The rank vanishes where the object does**: if `Lh^*E` is zero for `h : Z ⟶ X`, the
restriction of `r(E)` to `Z` is zero, `h` landing in the locus where the Euler characteristic of
`E` is `0`. -/
theorem res_perfectRankClass_eq_zero (hE : HasDefinedChernClasses E) {Z : Scheme.{u}}
    (h : Z ⟶ X) [LocallyOfFiniteType h]
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      h.toLRSHom.toShHom).obj E)) :
    TotalChowClass.res h rfl (perfectRankClass C sX hE) = 0 := by
  rw [res_perfectRankClass_of_range perfect C sX hE h rfl 0 ?_, zero_smul]
  rintro _ ⟨z, rfl⟩
  have hchi := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback h E
    (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect)) z
  exact (mem_eulerLocus perfect).mpr (hchi.symm.trans (chiDerivedFibre_eq_zero_of_isZero hzero _ z))

end Rank

/-! ### The classes `P_p(E)` -/

section PowerSum

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules}
  (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
  (hE : HasDefinedChernClasses E)

/-- **The family `(P_p(E))_p` as one total class**: the class whose degree-`p` component is the
class `P_p(E) ∈ A^p(X)` of Definition 0F9E (2). -/
def perfectPowerSumTotal : TotalChowClass C sX := fun p ↦ perfectPowerSumComponent C sX hE p

/-- The degree-`p` component of `perfectPowerSumTotal` is `P_p(E)`. -/
theorem perfectPowerSumTotal_apply (p : ℕ) :
    perfectPowerSumTotal C sX hE p = perfectPowerSumComponent C sX hE p :=
  rfl

/-- **`P_0(E)` is the rank** `r(E)`. -/
theorem perfectPowerSumComponent_zero :
    perfectPowerSumComponent C sX hE 0 = perfectRankClass C sX hE 0 := by
  rw [perfectPowerSumComponent, perfectPowerSum_zero]

/-- **`P_p(E)` for `p ≥ 1` is the power sum `P_p(c_1(E), …, c_p(E))`** of the Chern classes of
`E`: the rank does not enter Newton's recursion in positive degrees. -/
theorem perfectPowerSumComponent_succ (p : ℕ) :
    perfectPowerSumComponent C sX hE (p + 1) =
      TotalChowClass.newtonComponents (perfectChernClass C sX hE) (p + 1) (p + 1) := by
  rw [perfectPowerSumComponent, perfectPowerSum,
    AlgebraicGeometry.newtonPowerSum_eq_of_pos _ 0 _ (p + 1) p.succ_pos]

/-- **The characterization of `P_p(E)`**: along the envelope of every presentation `(f, 𝓔^•)`
of `E` it restricts to `P_p(𝓔^•)`. -/
theorem chowCohomologyRestriction_perfectPowerSumComponent (p : ℕ) (H : EnvelopePresentation E) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sX H.f (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (perfectPowerSumComponent C sX hE p) =
      complexPowerSumComponent C (H.f ≫ sX) H.locallyBounded p := by
  rw [← res_perfectPowerSumComponent C sX hE H p, TotalChowClass.res_rfl_apply,
    perfectPowerSumComponent]

include perfect hE in
/-- **Uniqueness of the power sums.** Let `E` be a perfect object of `D(𝒪_X)` whose Chern
classes are defined. For every `p` there is a unique class `P_p(E) ∈ A^p(X)` whose restriction
along the envelope `f : Y ⟶ X` of every presentation `(f, 𝓔^•)` of `E` is the class `P_p(𝓔^•)`
of Lemma 0ESZ, which on the locus where the terms have constant ranks is `∑ (-1)^n P_p(𝓔^n)`
(`Stacks.Chow.res_complexPowerSum_complexRankLocus`). The class is
`Stacks.Chow.perfectPowerSumComponent`. -/
@[stacks 0GUD "P_p(E): the unique class of A^p(X) restricting along the envelope of every \
presentation (f, E^bullet) of E to P_p(E^bullet), independent of f and E^bullet"]
theorem existsUnique_perfectPowerSum (p : ℕ) :
    ∃! x : chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ),
      ∀ H : EnvelopePresentation E,
        chowCohomologyRestriction C (gysinSystemOfInvertible C) sX H.f (p : ℤ)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) x =
          complexPowerSumComponent C (H.f ≫ sX) H.locallyBounded p := by
  refine ⟨perfectPowerSumComponent C sX hE p,
    fun H ↦ chowCohomologyRestriction_perfectPowerSumComponent C sX hE p H, fun x hx ↦ ?_⟩
  refine chowCohomologyRestriction_injective_of_isEnvelope C (gysinSystemOfInvertible C) sX
    hE.some.f (p : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) hE.some.envelope ?_
  rw [hx hE.some, chowCohomologyRestriction_perfectPowerSumComponent]

include perfect in
/-- **`P_p(E)` vanishes where `E` does**: if `Lh^*E` is zero for `h : Z ⟶ X`, the restriction
of `P_p(E)` to `Z` is zero. For `p = 0` this is the vanishing of the Euler characteristic, and for
`p ≥ 1` the restricted Chern classes `c_i(E)|_Z = c_i(Lh^*E)` of positive degree vanish. -/
theorem chowCohomologyRestriction_perfectPowerSumComponent_eq_zero {Z : Scheme.{u}} (h : Z ⟶ X)
    [LocallyOfFiniteType h]
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      h.toLRSHom.toShHom).obj E)) (p : ℕ) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sX h (p : ℤ)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (perfectPowerSumComponent C sX hE p) = 0 := by
  rcases p with _ | p
  · rw [perfectPowerSumComponent_zero, ← TotalChowClass.res_rfl_apply,
      res_perfectRankClass_eq_zero perfect C sX hE h hzero, TotalChowClass.zero_apply]
  · rw [perfectPowerSumComponent_succ]
    have hE' := hasDefinedChernClasses_of_derivedPullback h _ E hE (Iso.refl _)
    have hc : (fun i : ℕ+ ↦ TotalChowClass.res h rfl
        (TotalChowClass.homComponent (i : ℕ) (perfectChernClass C sX hE))) = 0 := by
      funext i
      rw [TotalChowClass.res_homComponent, res_perfectChernClass_derivedPullback C sX h hE hE']
      refine TotalChowClass.ext fun q ↦ ?_
      rw [TotalChowClass.homComponent_apply]
      split_ifs with hq
      · subst hq
        exact perfectChernClass_apply_eq_zero_of_isZero C _ hE' hzero i.pos
      · rfl
    rw [← TotalChowClass.res_rfl_apply]
    have hres := map_newtonPowerSum (TotalChowClass.res h rfl) 0 (fun i ↦
      TotalChowClass.homComponent (i : ℕ) (perfectChernClass C sX hE)) (p + 1)
    rw [hc, map_zero, newtonPowerSum_zero_family] at hres
    rw [TotalChowClass.newtonComponents, hres, TotalChowClass.zero_apply]

/-! ### The Chern character -/

/-- **The characterization of `ch_p(E) = P_p(E)/p!`**: along the envelope of every presentation
`(f, 𝓔^•)` of `E` it restricts to `ch_p(𝓔^•)`. -/
theorem rationalChowCohomologyRestriction_perfectChernCharacterComponent (p : ℕ)
    (H : EnvelopePresentation E) :
    rationalChowCohomologyRestriction C (gysinSystemOfInvertible C) sX H.f (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (perfectChernCharacterComponent C sX hE p) =
      complexChernCharacterComponent C (H.f ≫ sX) H.locallyBounded p := by
  rw [perfectChernCharacterComponent, complexChernCharacterComponent,
    rationalChowCohomologyRestriction_tmul, chowCohomologyRestriction_perfectPowerSumComponent]

include perfect hE in
/-- **Uniqueness of the Chern character.** Let `E` be a perfect object of `D(𝒪_X)` whose Chern
classes are defined. For every `p` there is a unique class `ch_p(E) ∈ A^p(X) ⊗ 𝐐` whose rational
restriction along the envelope `f : Y ⟶ X` of every presentation `(f, 𝓔^•)` of `E` is the
component `ch_p(𝓔^•) = P_p(𝓔^•)/p!` of the Chern character of `𝓔^•` (Lemma 0ESZ). The class is
`Stacks.Chow.perfectChernCharacterComponent`, and the family `(ch_p(E))_p` is
`ch(E) ∈ ∏_{p ≥ 0} A^p(X) ⊗ 𝐐`. -/
@[stacks 0GUD "ch(E): for every p the unique class of A^p(X) ⊗ Q restricting along the envelope \
of every presentation (f, E^bullet) of E to ch_p(E^bullet) = P_p(E^bullet)/p!, independent of f \
and E^bullet"]
theorem existsUnique_perfectChernCharacter (p : ℕ) :
    ∃! x : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ),
      ∀ H : EnvelopePresentation E,
        rationalChowCohomologyRestriction C (gysinSystemOfInvertible C) sX H.f (p : ℤ)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) x =
          complexChernCharacterComponent C (H.f ≫ sX) H.locallyBounded p := by
  refine ⟨perfectChernCharacterComponent C sX hE p,
    fun H ↦ rationalChowCohomologyRestriction_perfectChernCharacterComponent C sX hE p H,
    fun x hx ↦ ?_⟩
  refine rationalChowCohomologyRestriction_injective_of_isEnvelope C (gysinSystemOfInvertible C)
    sX hE.some.f (p : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    hE.some.envelope ?_
  rw [hx hE.some, rationalChowCohomologyRestriction_perfectChernCharacterComponent]

end PowerSum

-- Stacks 0GUD for the total Chern class: `c(E) ∈ ∏_{p ≥ 0} A^p(X)` is the unique total class
-- restricting along the envelope of every presentation `(f, 𝓔^•)` of `E` to `c(𝓔^•)`.
add_to_stacks 0GUD "c(E): the unique class of the product of the A^p(X), p ≥ 0, restricting along \
the envelope of every presentation (f, E^bullet) of E to c(E^bullet), independent of f and \
E^bullet" Stacks.Chow.existsUnique_forall_res_eq_complexChern

end Stacks.Chow

end
