module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Catenary.Defs
public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.CohenMacaulay.Catenary
public import StacksFrontier.Topology.Dimension.Catenary
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Noetherian.CatenaryOpenCovering

/-!
# Catenarity of a scheme locally of finite type over a field

A scheme locally of finite type over a field has a catenary underlying topological space: a
field is universally catenary, so the section ring of every affine open is a catenary ring, and
catenarity of a topological space is local on an open cover.

## Main results

* `AlgebraicGeometry.isCatenarySpace_of_locallyOfFiniteType_over_field`: a locally algebraic
  scheme over a field is catenary.

## Implementation notes

A locally algebraic `k`-scheme is represented by a scheme `X`, its structure morphism
`f : X ⟶ Spec k`, and the typeclass assumption `LocallyOfFiniteType f`. Catenarity is expressed
by the canonical topological predicate `IrreducibleClosedsCodim.IsCatenarySpace X`, which is
bridged to the order-theoretic `Catenary.IsCatenaryOrder` of a prime spectrum.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open IrreducibleClosedsCodim

universe u

namespace AlgebraicGeometry

/-- A module with an element whose annihilator in the ring is trivial has full support. -/
private lemma support_eq_univ_of_smul_eq_zero_imp {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (m : M) (h : ∀ r : R, r • m = 0 → r = 0) : Module.support R M = Set.univ :=
  Set.eq_univ_of_forall fun _ => Module.mem_support_iff'.mpr
    ⟨m, fun r hr hr0 => hr (by simp [h r hr0])⟩

/-- The prime spectrum of a catenary ring is a catenary topological space. -/
@[ega "IV 5.1.1" "5.1.1.4"]
private lemma isCatenarySpace_of_ring_isCatenary {R : Type*} [CommRing R]
    (hR : Ring.IsCatenary R) :
    IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum R) := by
  have hOrder : Catenary.IsCatenaryOrder (IrreducibleCloseds (PrimeSpectrum R)) :=
    (Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum R).mp hR.isCatenaryOrder
  intro Y Z hYZ
  obtain ⟨⟨N, hN⟩, hlen⟩ := hOrder Y Z hYZ
  have hfin : topCodim Y Z ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top N)
    rw [topCodim_le_iff]
    intro s hs ht
    exact_mod_cast hN s hs ht
  refine ⟨hfin, ?_⟩
  intro s hs
  obtain ⟨t, ht, htdim⟩ := exists_maximalChain_length_eq_topCodim Y Z hYZ hfin
  let s' : RelSeries {(a, b) : IrreducibleCloseds (PrimeSpectrum R) ×
      IrreducibleCloseds (PrimeSpectrum R) | a ⋖ b} :=
    ⟨s.length, s.toFun, hs.2.2⟩
  let t' : RelSeries {(a, b) : IrreducibleCloseds (PrimeSpectrum R) ×
      IrreducibleCloseds (PrimeSpectrum R) | a ⋖ b} :=
    ⟨t.length, t.toFun, ht.2.2⟩
  have h := hlen s' t' hs.1 hs.2.1 ht.1 ht.2.1
  exact (congrArg (fun n : ℕ => (n : ℕ∞)) h).trans htdim

/-- The underlying topological space of a scheme locally of finite type over a field is
catenary. -/
@[stacks 0A21 "catenary"]
theorem isCatenarySpace_of_locallyOfFiniteType_over_field
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    IrreducibleClosedsCodim.IsCatenarySpace X := by
  have hk : Ring.IsUniversallyCatenary k := by
    apply Ring.IsUniversallyCatenary.of_isCohenMacaulay_of_support_eq_univ (M := k)
    · intro p hp
      have hp' : p = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
      subst p
      have hd : Module.depth (Localization.AtPrime (⊥ : Ideal k)) ⊥
          (LocalizedModule (⊥ : Ideal k).primeCompl k) = 0 :=
        Module.depth_bot_eq_zero (R := Localization.AtPrime (⊥ : Ideal k))
          (LocalizedModule (⊥ : Ideal k).primeCompl k)
      have hm : IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal k)) = ⊥ := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        simp
      have hs := support_eq_univ_of_smul_eq_zero_imp
        (R := Localization.AtPrime (⊥ : Ideal k))
        (1 : LocalizedModule (⊥ : Ideal k).primeCompl k) fun r h => by simpa [smul_eq_mul] using h
      have hdepth : Module.depth (Localization.AtPrime (⊥ : PrimeSpectrum k).asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : PrimeSpectrum k).asIdeal))
          (LocalizedModule (⊥ : PrimeSpectrum k).asIdeal.primeCompl k) = 0 := by
        simpa [hm] using hd
      have hs' : Module.support (Localization.AtPrime (⊥ : PrimeSpectrum k).asIdeal)
          (LocalizedModule (⊥ : PrimeSpectrum k).asIdeal.primeCompl k) = Set.univ := by
        simpa using hs
      rw [hdepth]
      simp only [Module.supportDim]
      rw [hs']
      symm
      apply Order.krullDim_eq_zero
    · exact support_eq_univ_of_smul_eq_zero_imp (1 : k) fun r h => by simpa [smul_eq_mul] using h
  apply CatenaryTopologicalSpace.isCatenary_of_hasOpenCoveringByCatenarySpaces
  refine ⟨X.affineOpens, fun U => U.1, fun U => U.1.isOpen, ?_, fun U => ?_⟩
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨⟨U, hU⟩, hxU⟩
  let : Algebra k Γ(X, U.1) :=
    ((f.appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, U.1) :=
    (f.finiteType_appLE (isAffineOpen_top (Spec (.of k))) U.2 (by simp)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  exact CatenaryTopologicalSpace.isCatenary_of_homeomorph U.2.isoSpec.symm.schemeIsoToHomeo
    (isCatenarySpace_of_ring_isCatenary (hk _))

end AlgebraicGeometry

end
