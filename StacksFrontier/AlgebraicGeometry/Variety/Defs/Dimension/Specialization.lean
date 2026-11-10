module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Topology.Inseparable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Dimension along a specialization

The local Krull dimension of a topological space cannot decrease when a point is specialized. On
a scheme locally of finite type over a field more is true: a nontrivial specialization strictly
increases the Krull dimension of the local ring, and the local dimension at a point is the
minimum of the dimensions of the local rings at its closed specializations.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_le_of_specialization`: local dimension is monotone
  under specialization.
* `AlgebraicGeometry.krullDimOfRing_stalk_lt_of_specialization`: the strict dimension inequality
  along a nontrivial specialization.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_iInf_closedSpecializations` computes the local
  dimension using closed specializations.

## Implementation notes

The specialization relation is Mathlib's `Specializes`, written `x ⤳ x'`.

The monotonicity statement is proved for arbitrary topological spaces and arbitrary
specializations: its proof is purely topological and uses neither nontriviality nor the scheme
hypotheses under which the source states it. A locally algebraic `k`-scheme is represented by
its structure morphism to `Spec k`, equipped with Mathlib's `LocallyOfFiniteType` instance, and
the dimension of a local ring is expressed by `ringKrullDim`. The minimum over closed
specializations is written as an infimum indexed by the subtype of closed specializations of the
given point.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Local Krull dimension cannot decrease along a specialization. -/
@[stacks 0A21 "specialization_local_dimension"]
theorem topologicalKrullDimAt_le_of_specialization {X : Type*} [TopologicalSpace X] {x x' : X}
    (h : x ⤳ x') :
    topologicalKrullDimAt X x ≤ topologicalKrullDimAt X x' := by
  obtain ⟨U, hx', hU, hdim⟩ := (topologicalKrullDimAt_isLeast X x').1
  exact (topologicalKrullDimAt_isLeast X x).2 ⟨U, h.mem_open hU hx', hU, hdim⟩

/-- A nontrivial specialization on a scheme locally of finite type over a field strictly
increases the Krull dimension of the local ring. -/
@[stacks 0A21 "specialization_stalk_dimension"]
theorem krullDimOfRing_stalk_lt_of_specialization
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {x x' : X} (hxx' : x ⤳ x') (hne : x ≠ x') :
    ringKrullDim (X.presheaf.stalk x) < ringKrullDim (X.presheaf.stalk x') := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  have hlt : x' < x := ⟨Scheme.le_iff_specializes.mpr hxx',
    fun hle => hne (hxx'.antisymm (Scheme.le_iff_specializes.mp hle)).eq⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hfin : Order.coheight x < ⊤ := by
    simpa only [ringKrullDim_stalk_eq_coheight, ← WithBot.coe_top, WithBot.coe_lt_coe] using
      (ringKrullDim_lt_top (R := X.presheaf.stalk x))
  exact_mod_cast Order.coheight_strictAnti hlt hfin

/-- The stalk of `Spec S` at a prime `p` has Krull dimension the height of `p`. -/
private theorem ringKrullDim_stalk_spec_eq_height {S : Type u} [CommRing S] (p : Spec (.of S)) :
    ringKrullDim ((Spec (.of S)).presheaf.stalk p) = (p.asIdeal.height : WithBot ℕ∞) := by
  have : p.asIdeal.IsPrime := p.isPrime
  let : Algebra S ((Spec (.of S)).presheaf.stalk p) := StructureSheaf.stalkAlgebra S p
  have : IsLocalization.AtPrime ((Spec (.of S)).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of S) p
  exact IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal _

/-- On the spectrum of a finitely generated algebra over a field, the local dimension at a point
is the minimum of the dimensions of the local rings at its closed specializations. -/
private theorem affine_localDimension_eq_iInf_closedSpecializations
    (k : Type u) [Field k] (S : Type u) [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (x : Spec (.of S)) :
    topologicalKrullDimAt (Spec (.of S)) x =
      ⨅ (x' : {x' : Spec (.of S) // x ⤳ x' ∧
        IsClosed ({x'} : Set (Spec (.of S)))}),
        ringKrullDim ((Spec (.of S)).presheaf.stalk x') := by
  rw [TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
    show TopologicalSpace.localKrullDim (Spec (.of S)) x =
      TopologicalSpace.localKrullDim (PrimeSpectrum S) (show PrimeSpectrum S from x) from rfl,
    (PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k
      (show PrimeSpectrum S from x)).2]
  apply le_antisymm
  · refine le_iInf fun ⟨x', hx', hclosed⟩ => ?_
    have hmem : (show PrimeSpectrum S from x') ∈
        closure ({show PrimeSpectrum S from x} : Set (PrimeSpectrum S)) :=
      specializes_iff_mem_closure.mp hx'
    rw [PrimeSpectrum.closure_singleton] at hmem
    apply iInf_le_of_le x'.asIdeal
    apply iInf_le_of_le ⟨(PrimeSpectrum.isClosed_singleton_iff_isMaximal x').mp hclosed, hmem⟩
    exact (ringKrullDim_stalk_spec_eq_height x').ge
  · refine le_iInf fun m => le_iInf fun ⟨hm, hxm⟩ => ?_
    let y : Spec (.of S) := (⟨m, hm.isPrime⟩ : PrimeSpectrum S)
    refine iInf_le_of_le (⟨y, ?_, ?_⟩ :
      {x' : Spec (.of S) // x ⤳ x' ∧
        IsClosed ({x'} : Set (Spec (.of S)))}) ?_
    · refine specializes_iff_mem_closure.mpr ?_
      change (show PrimeSpectrum S from y) ∈
        closure ({show PrimeSpectrum S from x} : Set (PrimeSpectrum S))
      rwa [PrimeSpectrum.closure_singleton]
    · exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm
    change ringKrullDim ((Spec (.of S)).presheaf.stalk y) ≤ (m.height : WithBot ℕ∞)
    exact (ringKrullDim_stalk_spec_eq_height y).le

/-- For a scheme locally of finite type over a field, its local dimension at a point is the
minimum of the dimensions of the local rings at the closed specializations of that point. -/
@[stacks 0A21 "local_dimension_closed_specializations"]
theorem topologicalKrullDimAt_eq_iInf_closedSpecializations
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDimAt X x =
      ⨅ (x' : {x' : X // x ⤳ x' ∧ IsClosed ({x'} : Set X)}),
        ringKrullDim (X.presheaf.stalk x') := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  apply le_antisymm
  · exact le_iInf fun ⟨x', hxx', hx'closed⟩ =>
      (topologicalKrullDimAt_le_of_specialization hxx').trans_eq
        (topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f x' hx'closed)
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let g := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V (by simp)
    let : Algebra k Γ(X, V) := g.hom.toAlgebra
    have : Algebra.FiniteType k Γ(X, V) := by
      change RingHom.FiniteType g.hom
      apply RingHom.FiniteType.comp
      · exact f.finiteType_appLE (isAffineOpen_top _) hV (by simp)
      · exact RingHom.FiniteType.of_surjective _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2
    let e : Spec Γ(X, V) ⟶ X := hV.fromSpec
    have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
    let y : Spec Γ(X, V) := hV.isoSpec.hom ⟨x, hxV⟩
    have hey : e y = x := by
      change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨x, hxV⟩ = x
      rw [hV.isoSpec_hom_fromSpec]
      rfl
    rw [← hey, hV.fromSpec.isOpenEmbedding.topologicalKrullDimAt_eq y,
      affine_localDimension_eq_iInf_closedSpecializations k Γ(X, V) y]
    refine le_iInf fun ⟨y', hyy', hy'closed⟩ => ?_
    refine iInf_le_of_le (⟨e y', ?_, ?_⟩ :
      {x' : X // e y ⤳ x' ∧ IsClosed ({x'} : Set X)}) ?_
    · exact hV.fromSpec.continuous.specialization_monotone hyy'
    · rw [← mem_closedPoints_iff]
      change y' ∈ hV.fromSpec ⁻¹' closedPoints X
      rwa [hV.fromSpec.isOpenEmbedding.preimage_closedPoints]
    simp only [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast (Topology.IsOpenEmbedding.coheight_eq hV.fromSpec
      hV.fromSpec.isOpenEmbedding (x := y')).le

end AlgebraicGeometry

end
