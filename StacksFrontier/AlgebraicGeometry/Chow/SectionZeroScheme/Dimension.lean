module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Base
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ClosedFibreGenericPoint
public import StacksFrontier.Topology.Sober.Generization

/-!
# `δ`-dimension bounds at points

Let `(S, δ)` be the base situation of chapter 42 and `X` locally of finite type over `S`. This
file proves pointwise facts about the dimension function `δ_X`.

## Main results

* `Stacks.Chow.SectionZeroScheme.relativeDimension_le_sub_one_of_specializes`: a point with a
  proper generization has `δ` strictly below `dim_δ(X)`.
* `Stacks.Chow.SectionZeroScheme.exists_specializes_ne_of_mem_maximalIdeal`: a point whose local
  ring has a nonzerodivisor in its maximal ideal has a proper generization.
* `Stacks.Chow.SectionZeroScheme.mem_genericPoints_of_relativeDimension_eq`: a point of a closed
  subscheme `Z` with `δ = dim_δ(Z)` is a generic point of `Z`.
* `Stacks.Chow.SectionZeroScheme.relativeDimension_comp_le_add`: along a morphism of relative
  dimension `d`, `δ` grows by at most `d`.
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow.SectionZeroScheme

variable (C : ChowSituation.{u})

/-- **A point with a proper generization lies strictly below the `δ`-dimension.** -/
theorem relativeDimension_le_sub_one_of_specializes {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] {N : ℤ} (hX : schemeDeltaDimension C q ≤ (N : EInt)) {η ξ : X}
    (hηξ : η ⤳ ξ) (hne : η ≠ ξ) :
    relativeDimension C.dimensionFunction q ξ ≤ N - 1 := by
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction q
  have hlt := d.strictAnti_specializes hηξ hne
  have hη := relativeDimension_le_of_schemeDeltaDimension_le' C q hX η
  rw [hd ξ, hd η] at hlt
  omega

/-- **A nonzerodivisor in the maximal ideal of the local ring rules out a generic point.** If the
maximal ideal of `𝒪_{X, ξ}` contains a nonzerodivisor, then `ξ` has a proper generization. -/
theorem exists_specializes_ne_of_mem_maximalIdeal {X : Scheme.{u}} {ξ : X}
    (a : X.presheaf.stalk ξ) (ha : a ∈ nonZeroDivisors (X.presheaf.stalk ξ))
    (hm : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ)) :
    ∃ η : X, η ⤳ ξ ∧ η ≠ ξ := by
  by_contra h
  push Not at h
  have hgen : ξ ∈ genericPoints X :=
    (mem_genericPoints_iff_forall_specializes_eq ξ).2 fun η hη => h η hη
  rw [← Stacks.ClosedFibreGenericPoint.radical_bot_stalk_eq_maximalIdeal hgen] at hm
  obtain ⟨k, hk⟩ := hm
  have hk' : a ^ k ∈ nonZeroDivisors (X.presheaf.stalk ξ) := pow_mem ha k
  rw [Ideal.mem_bot.mp hk] at hk'
  exact zero_notMem_nonZeroDivisors hk'

/-- The kernel of a local homomorphism of local rings lies in the maximal ideal. -/
theorem ker_le_maximalIdeal {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    RingHom.ker f ≤ IsLocalRing.maximalIdeal A := by
  intro a ha hu
  exact not_isUnit_zero (RingHom.mem_ker.mp ha ▸ hu.map f)

/-- **A point of a closed subscheme at the top `δ`-dimension is a generic point of it.** -/
theorem mem_genericPoints_of_relativeDimension_eq {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (I : X.IdealSheafData) {k : ℤ}
    (hI : schemeDeltaDimension C (I.subschemeι ≫ q) ≤ (k : EInt)) (z : I.subscheme)
    (hz : relativeDimension C.dimensionFunction q (I.subschemeι z) = k) :
    z ∈ genericPoints I.subscheme := by
  refine (mem_genericPoints_iff_forall_specializes_eq z).2 fun w hw => ?_
  by_contra hne
  have hlt := relativeDimension_le_sub_one_of_specializes C (I.subschemeι ≫ q) hI hw hne
  rw [relativeDimension_comp_closedImmersion C.dimensionFunction I.subschemeι q z, hz] at hlt
  omega

/-- **Along a morphism of relative dimension `d`, `δ` grows by at most `d`.** -/
theorem relativeDimension_comp_le_add {X Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    (π : X ⟶ Y) [LocallyOfFiniteType π] (d : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π d)
    (x : X) :
    relativeDimension C.dimensionFunction (π ≫ q) x ≤
      relativeDimension C.dimensionFunction q (π x) + d := by
  rw [relativeDimension_comp_eq_add_trdeg C.dimensionFunction q π x]
  have := toNat_residueTrdeg_le_of_relativeDimension π d hπ x
  omega

end Stacks.Chow.SectionZeroScheme

end
