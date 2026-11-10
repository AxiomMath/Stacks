module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericMeromorphicStalkFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingUniverseComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericMeromorphicGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing

/-!
# The canonical ratio `s / s_ξ` of Stacks 0EPR

Let `X` be a decent, locally Noetherian, integral algebraic space over `S`, let `Z ⊆ X` be a
prime divisor with generic point `ξ` and let `ℒ` be an *invertible* `𝒪_X`-module.  Fix a free
generator `t_ξ` of `ℒ_ξ`, which
`AlgebraicGeometry.Space.PrimeDivisor.exists_ne_zero_span_genericModuleStalk_eq_top` produces.
By `AlgebraicGeometry.Space.PrimeDivisor.bijective_smul_toMeromorphicSectionValue` the image of
`t_ξ` generates `𝒦_X(ℒ)_ξ` freely over `K = 𝒦(Spec(𝒪^h_{X, ξ}))`, so the germ at `ξ` of a
meromorphic section `s` of `ℒ` is `k · t_ξ` for exactly one `k ∈ K`.  That `k` is **the ratio
`s / s_ξ`** of Stacks 0EPR.

This file shows that the ratio exists and is unique, that it is a unit of `K` when `s` is
regular, and that `K` is isomorphic to the total ring of fractions in which the order of vanishing
reads the ratio.

## Main results

* `PrimeDivisor.existsUnique_smul_toMeromorphicSectionValue_eq_genericMeromorphicGerm`:
  the ratio exists and is unique.
* `PrimeDivisor.isUnit_of_smul_toMeromorphicSectionValue_eq_genericMeromorphicGerm`:
  the ratio of a *regular* meromorphic section is a unit of `K`.
* `PrimeDivisor.exists_ringEquiv_genericTotalFractionRing`: `K` is isomorphic to
  `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRing`, the total ring of fractions of
  the `CommRingCat.{u + 1}` in which `AlgebraicGeometry.Space.orderOfVanishingSection` reads the
  ratio, compatibly with the comparison of the two base rings.
* `PrimeDivisor.exists_ringEquiv_forall_smul_eq_genericMeromorphicGerm`: the canonical ratio,
  read in `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRing`, characterised by the
  equation it satisfies and a unit at every regular section.

## References

* [Stacks Project, Tag 08HT](https://stacks.math.columbia.edu/tag/08HT)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]
  (hR : B.Contains (Spec (.of R)))

/-! ### The ratio exists and is unique -/

include hX hdec hInt hN Z in
/-- The ratio `s / s_ξ` of Stacks 0EPR exists and is unique: the germ at `ξ` of a meromorphic
section `s` of `ℒ` is a unique multiple of the image of a free generator `t_ξ` of `ℒ_ξ`. -/
theorem PrimeDivisor.existsUnique_smul_toMeromorphicSectionValue_eq_genericMeromorphicGerm
    (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L)
    (t : Z.genericModuleStalk B S hS hX hdec R hR L)
    (ht : Function.Bijective fun r : R => r • t)
    (s : MeromorphicSection.{u, u} B S hS X hX L) :
    ∃! k : meromorphicChartRing B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianChart B S hS hX hdec R hR),
      k • toMeromorphicSectionValue B S hS
          (Z.genericHenselianSpace B S hS hX hdec R hR).obj
          (Z.genericHenselianSpace B S hS hX hdec R hR).property
          (Z.genericHenselianPullback B S hS hX hdec R hR L)
          (Z.genericHenselianChart B S hS hX hdec R hR) t =
        Z.genericMeromorphicGerm B S hS hX hdec R hR L s :=
  (Z.bijective_smul_toMeromorphicSectionValue B S hS hX hdec hInt hN R hR L hL t ht).existsUnique
    (Z.genericMeromorphicGerm B S hS hX hdec R hR L s)

/-! ### The ratio of a regular section is a unit -/

include hX hdec hInt hN Z in
/-- If `s` is a *regular* meromorphic section of `ℒ`, then its ratio `s / s_ξ` of Stacks 0EPR
against a free generator of `ℒ_ξ` is a unit of `K = 𝒦(Spec(𝒪^h_{X, ξ}))`. -/
theorem PrimeDivisor.isUnit_of_smul_toMeromorphicSectionValue_eq_genericMeromorphicGerm
    (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L)
    (t : Z.genericModuleStalk B S hS hX hdec R hR L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (k : meromorphicChartRing B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianChart B S hS hX hdec R hR))
    (hk : k • toMeromorphicSectionValue B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianPullback B S hS hX hdec R hR L)
        (Z.genericHenselianChart B S hS hX hdec R hR) t =
      Z.genericMeromorphicGerm B S hS hX hdec R hR L s) :
    IsUnit k := by
  let : Algebra R (meromorphicChartRing B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianChart B S hS hX hdec R hR)) :=
    (Z.genericToMeromorphicFunctions B S hS hX hdec R hR).toAlgebra
  have : IsFractionRing R (meromorphicChartRing B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianChart B S hS hX hdec R hR)) :=
    Z.isFractionRing_genericMeromorphicChartRing B S hS hX hdec R hR
      (Z.isReduced_genericHenselization B S hS hX hdec hInt hN R)
      (Z.isNoetherianRing_genericHenselization B S hS hX hdec hInt hN R)
  have hreg := isRegularMeromorphicSection_pullbackMeromorphicSection B S hS
    (Z.genericHenselianMorphism B S hS hX hdec R hR)
    (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) s hs
  have hinj := hreg (Z.genericHenselianChart B S hS hX hdec R hR)
  have hgerm : (pullbackMeromorphicSection B S hS
        (Z.genericHenselianMorphism B S hS hX hdec R hR) L
        (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR) s).eval
        (op (Z.genericHenselianChart B S hS hX hdec R hR)) =
      k • toMeromorphicSectionValue B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianPullback B S hS hX hdec R hR L)
        (Z.genericHenselianChart B S hS hX hdec R hR) t := hk.symm
  have hknz : k ∈ nonZeroDivisors (meromorphicChartRing B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianChart B S hS hX hdec R hR)) := by
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx => ?_
    refine hinj ?_
    change x • _ = (0 : meromorphicChartRing B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianChart B S hS hX hdec R hR)) • _
    have key : ∀ y : meromorphicChartRing B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianChart B S hS hX hdec R hR),
        y • (k • toMeromorphicSectionValue B S hS
            (Z.genericHenselianSpace B S hS hX hdec R hR).obj
            (Z.genericHenselianSpace B S hS hX hdec R hR).property
            (Z.genericHenselianPullback B S hS hX hdec R hR L)
            (Z.genericHenselianChart B S hS hX hdec R hR) t) =
          (y * k) • toMeromorphicSectionValue B S hS
            (Z.genericHenselianSpace B S hS hX hdec R hR).obj
            (Z.genericHenselianSpace B S hS hX hdec R hR).property
            (Z.genericHenselianPullback B S hS hX hdec R hR L)
            (Z.genericHenselianChart B S hS hX hdec R hR) t :=
      fun y => (mul_smul y k _).symm
    rw [hgerm]
    refine Eq.trans (key x) (Eq.trans ?_ (key 0).symm)
    rw [hx, zero_mul]
  rwa [IsFractionRing.nonZeroDivisors_eq_isUnit R (meromorphicChartRing B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR).obj
    (Z.genericHenselianSpace B S hS hX hdec R hR).property
    (Z.genericHenselianChart B S hS hX hdec R hR))] at hknz

/-! ### The comparison of the two fraction rings -/

variable [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec)]

omit [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec)] in
include hX hdec hInt hN Z in
/-- `K = 𝒦(Spec(𝒪^h_{X, ξ}))`, in which the ratio `s / s_ξ` of Stacks 0EPR lives, is isomorphic
to `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRing`, in which
`AlgebraicGeometry.Space.orderOfVanishingSection` reads it, through an isomorphism extending an
isomorphism `e` of the two henselian local rings at `ξ`. -/
theorem PrimeDivisor.exists_ringEquiv_genericTotalFractionRing :
    ∃ (e : R ≃+* ↥(Z.genericHenselianLocalRing B S hS hX hdec))
      (ψ : meromorphicChartRing B S hS
          (Z.genericHenselianSpace B S hS hX hdec R hR).obj
          (Z.genericHenselianSpace B S hS hX hdec R hR).property
          (Z.genericHenselianChart B S hS hX hdec R hR) ≃+*
        Z.genericTotalFractionRing B S hS hX hdec),
      ∀ v : R, ψ (Z.genericToMeromorphicFunctions B S hS hX hdec R hR v) =
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec) (e v) := by
  let : Algebra R (meromorphicChartRing B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianChart B S hS hX hdec R hR)) :=
    (Z.genericToMeromorphicFunctions B S hS hX hdec R hR).toAlgebra
  have : IsFractionRing R (meromorphicChartRing B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianChart B S hS hX hdec R hR)) :=
    Z.isFractionRing_genericMeromorphicChartRing B S hS hX hdec R hR
      (Z.isReduced_genericHenselization B S hS hX hdec hInt hN R)
      (Z.isNoetherianRing_genericHenselization B S hS hX hdec hInt hN R)
  obtain ⟨e⟩ := Z.exists_ringEquiv_genericHenselianLocalRing B S hS hX hdec R
  exact ⟨e, IsFractionRing.ringEquivOfRingEquiv e,
    fun v => IsFractionRing.ringEquivOfRingEquiv_algebraMap e v⟩

/-! ### The canonical ratio -/

omit [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec)] in
include hX hdec hInt hN Z in
/-- The canonical ratio `s / s_ξ` of Stacks 0EPR, read in the total ring of fractions of
`𝒪^h_{X, ξ}`.  For a free generator `t_ξ` of `ℒ_ξ` there are an isomorphism `e` of the two
henselian local rings at `ξ`, an isomorphism `ψ` extending it of the meromorphic functions of
`Spec(𝒪^h_{X, ξ})` with `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRing`, and a map
`f` on meromorphic sections of `ℒ` such that `ψ⁻¹(f s) · t_ξ` is the germ of `s` at `ξ` and such
that `f s` is a *unit* whenever `s` is regular. -/
theorem PrimeDivisor.exists_ringEquiv_forall_smul_eq_genericMeromorphicGerm
    (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L)
    (t : Z.genericModuleStalk B S hS hX hdec R hR L)
    (ht : Function.Bijective fun r : R => r • t) :
    ∃ (e : R ≃+* ↥(Z.genericHenselianLocalRing B S hS hX hdec))
      (ψ : meromorphicChartRing B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianChart B S hS hX hdec R hR) ≃+*
      Z.genericTotalFractionRing B S hS hX hdec)
      (f : MeromorphicSection.{u, u} B S hS X hX L →
        Z.genericTotalFractionRing B S hS hX hdec),
      (∀ s : MeromorphicSection.{u, u} B S hS X hX L,
        ψ.symm (f s) • toMeromorphicSectionValue B S hS
            (Z.genericHenselianSpace B S hS hX hdec R hR).obj
            (Z.genericHenselianSpace B S hS hX hdec R hR).property
            (Z.genericHenselianPullback B S hS hX hdec R hR L)
            (Z.genericHenselianChart B S hS hX hdec R hR) t =
          Z.genericMeromorphicGerm B S hS hX hdec R hR L s) ∧
        (∀ s : MeromorphicSection.{u, u} B S hS X hX L,
          IsRegularMeromorphicSection.{u, u} B S hS X hX L s → IsUnit (f s)) ∧
        ∀ v : R, ψ (Z.genericToMeromorphicFunctions B S hS hX hdec R hR v) =
          algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
            (Z.genericTotalFractionRing B S hS hX hdec) (e v) := by
  obtain ⟨e, ψ, hev⟩ :=
    Z.exists_ringEquiv_genericTotalFractionRing B S hS hX hdec hInt hN R hR
  refine ⟨e, ψ, fun s => ψ
    ((Z.existsUnique_smul_toMeromorphicSectionValue_eq_genericMeromorphicGerm
      B S hS hX hdec hInt hN R hR L hL t ht s).choose), fun s => ?_, fun s hs => ?_, hev⟩
  · rw [ψ.symm_apply_apply]
    exact (Z.existsUnique_smul_toMeromorphicSectionValue_eq_genericMeromorphicGerm
      B S hS hX hdec hInt hN R hR L hL t ht s).choose_spec.1
  · exact (Z.isUnit_of_smul_toMeromorphicSectionValue_eq_genericMeromorphicGerm
      B S hS hX hdec hInt hN R hR L hL t s hs _
      ((Z.existsUnique_smul_toMeromorphicSectionValue_eq_genericMeromorphicGerm
        B S hS hX hdec hInt hN R hR L hL t ht s).choose_spec.1)).map ψ

end Generic

end AlgebraicGeometry.Space

end
