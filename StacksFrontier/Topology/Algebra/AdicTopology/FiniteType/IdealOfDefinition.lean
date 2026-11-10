module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Defs.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Nilpotent.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.QuotientDiagram
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType.RestrictedPowerSeries

/-!
# Finite type modulo an ideal of definition

For a pre-admissible source, finite type modulo every weak ideal of definition is equivalent to
finite type modulo some ideal of definition, with tautness in both conditions.

## References

* [Stacks Project, Tag 0CB6](https://stacks.math.columbia.edu/tag/0CB6)
-/

@[expose] public section

namespace TopologicalRing

section

private lemma idealClosure_mono {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {I J : Ideal R} (h : I ≤ J) :
    Ideal.closure I ≤ Ideal.closure J := by
  change closure (I : Set R) ⊆ closure (J : Set R)
  exact closure_mono h

/-- For a pre-admissible source, finite type modulo every weak ideal of definition is equivalent
to finite type modulo some ideal of definition, with tautness in both conditions. -/
@[stacks 0CB6]
public lemma finiteTypeModuloEveryWeakIdeal_iff_exists_idealOfDefinition
    {B A : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (φ : B →+* A) (hB : TopologicalRing.IsPreAdmissible B) :
    TopologicalRing.FiniteTypeModuloEveryWeakIdeal φ ↔
      (RingHom.IsTaut φ ∧
        ∃ J : Ideal B, TopologicalRing.IsIdealOfDefinition J ∧
          (Ideal.quotientMap (I := J) (Ideal.closure (J.map φ)) φ
            (Ideal.map_le_iff_le_comap.mp subset_closure)).FiniteType) := by
  constructor
  · rintro ⟨htaut, hft⟩
    obtain ⟨J, hJ⟩ := hB
    refine ⟨htaut, J, hJ, ?_⟩
    exact hft J ⟨hJ.1, fun x hx => topologicallyNilpotent_of_mem_idealOfDefinition J hJ hx⟩
  · rintro ⟨htaut, J, hJ, hJft⟩
    refine ⟨htaut, fun K hK => ?_⟩
    -- The ideal of definition can be replaced by its intersection with `K`.
    let L : Ideal B := J ⊓ K
    have hLopen : IsOpen (L : Set B) := hJ.1.inter hK.1
    obtain ⟨n₀, hn₀⟩ := hJ.2 (K : Set B) (hK.1.mem_nhds (zero_mem K))
    let n : ℕ := n₀ + 1
    have hpow : J ^ n ≤ L := by
      refine le_inf ?_ ?_
      · simpa using Ideal.pow_le_pow_right (I := J) (show 1 ≤ n by simp [n])
      · exact fun x hx => hn₀ (Ideal.pow_le_pow_right (I := J) (show n₀ ≤ n by simp [n]) hx)
    let IL : Ideal A := Ideal.closure (L.map φ)
    let IJ : Ideal A := Ideal.closure (J.map φ)
    have hLmap : L.map φ ≤ IL := subset_closure
    have hJmap : J.map φ ≤ IJ := subset_closure
    have hILopen : IsOpen (IL : Set A) := htaut.1 L hLopen
    have hIle : IL ≤ IJ := idealClosure_mono (Ideal.map_mono inf_le_left)
    let qL : B ⧸ L →+* B ⧸ J := Ideal.Quotient.factor (show L ≤ J from inf_le_left)
    let qA : A ⧸ IL →+* A ⧸ IJ := Ideal.Quotient.factor hIle
    let fL : B ⧸ L →+* A ⧸ IL :=
      Ideal.quotientMap IL φ (Ideal.map_le_iff_le_comap.mp hLmap)
    let fJ : B ⧸ J →+* A ⧸ IJ :=
      Ideal.quotientMap IJ φ (Ideal.map_le_iff_le_comap.mp hJmap)
    let N : Ideal (B ⧸ L) := J.map (Ideal.Quotient.mk L)
    have hNnil : IsNilpotent N := by
      refine ⟨n, ?_⟩
      change (J.map (Ideal.Quotient.mk L)) ^ n = ⊥
      rw [← Ideal.map_pow]
      exact Ideal.map_mk_eq_bot_of_le hpow
    have hsumClosed : IsClosed ((J.map φ ⊔ IL : Ideal A) : Set A) :=
      (J.map φ ⊔ IL).toAddSubgroup.isClosed_of_isOpen
        (Ideal.isOpen_of_isOpen_subideal le_sup_right hILopen)
    have hIJle : IJ ≤ J.map φ ⊔ IL := by
      intro x hx
      change x ∈ closure (J.map φ : Set A) at hx
      exact closure_minimal (fun _ hx => Ideal.mem_sup_left hx) hsumClosed hx
    have hmapIJ : (J.map φ).map (Ideal.Quotient.mk IL) =
        IJ.map (Ideal.Quotient.mk IL) := by
      apply le_antisymm
      · exact Ideal.map_mono hJmap
      · calc
          IJ.map (Ideal.Quotient.mk IL) ≤
              (J.map φ ⊔ IL).map (Ideal.Quotient.mk IL) := Ideal.map_mono hIJle
          _ = (J.map φ).map (Ideal.Quotient.mk IL) := by
            rw [Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq]
    have hkerA : RingHom.ker qA = N.map fL := by
      have hker : RingHom.ker qA = IJ.map (Ideal.Quotient.mk IL) := by
        simpa [qA, Ideal.Quotient.factor, Ideal.mk_ker] using
          (Ideal.ker_quotient_lift (I := IL) (f := Ideal.Quotient.mk IJ)
            (show IL ≤ RingHom.ker (Ideal.Quotient.mk IJ) from by simpa using hIle))
      rw [hker]
      change IJ.map (Ideal.Quotient.mk IL) =
        (J.map (Ideal.Quotient.mk L)).map
          (Ideal.quotientMap IL φ (Ideal.map_le_iff_le_comap.mp hLmap))
      have hfLmk : (Ideal.quotientMap IL φ (Ideal.map_le_iff_le_comap.mp hLmap)).comp
          (Ideal.Quotient.mk L) = (Ideal.Quotient.mk IL).comp φ := by
        ext b
        simp [Ideal.quotientMap_mk]
      calc
        IJ.map (Ideal.Quotient.mk IL) = (J.map φ).map (Ideal.Quotient.mk IL) := hmapIJ.symm
        _ = J.map ((Ideal.Quotient.mk IL).comp φ) := by rw [Ideal.map_map]
        _ = J.map ((Ideal.quotientMap IL φ (Ideal.map_le_iff_le_comap.mp hLmap)).comp
            (Ideal.Quotient.mk L)) := by rw [hfLmk]
        _ = (J.map (Ideal.Quotient.mk L)).map
            (Ideal.quotientMap IL φ (Ideal.map_le_iff_le_comap.mp hLmap)) := by rw [Ideal.map_map]
    let qbar : (B ⧸ L) ⧸ N →+* (A ⧸ IL) ⧸ N.map fL :=
      Ideal.quotientMap (N.map fL) fL (Ideal.le_comap_map)
    let eB' : (B ⧸ L) ⧸ N ≃+* B ⧸ J :=
      DoubleQuot.quotQuotEquivQuotOfLE inf_le_left
    let eA' : (A ⧸ IL) ⧸ N.map fL ≃+* A ⧸ IJ :=
      (Ideal.quotEquivOfEq hkerA.symm).trans
        (qA.quotientKerEquivOfSurjective (Ideal.Quotient.factor_surjective hIle))
    have eB'_mk (x : B ⧸ L) : eB' (Ideal.Quotient.mk N x) = qL x := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk x inf_le_left
    have eA'_mk (x : A ⧸ IL) : eA' (Ideal.Quotient.mk (N.map fL) x) = qA x := by
      simp [eA', qA]
    have hqbarft : qbar.FiniteType := by
      have hcomm : eA'.toRingHom.comp qbar = fJ.comp eB'.toRingHom := by
        ext b
        simp [qbar, fL, fJ, eA'_mk, eB'_mk, qA, qL, Ideal.quotientMap_mk]
      have hqbarEq : qbar =
          eA'.symm.toRingHom.comp (fJ.comp eB'.toRingHom) := by
        calc
          qbar = eA'.symm.toRingHom.comp (eA'.toRingHom.comp qbar) := by
            ext x
            simp
          _ = eA'.symm.toRingHom.comp (fJ.comp eB'.toRingHom) := by rw [hcomm]
      rw [hqbarEq]
      exact (RingHom.FiniteType.of_surjective _ eA'.symm.surjective).comp
        (hJft.comp (RingHom.FiniteType.of_surjective _ eB'.surjective))
    have hLft : fL.FiniteType := by
      let : Algebra (B ⧸ L) (A ⧸ IL) := fL.toAlgebra
      exact RingHom.finiteType_algebraMap.mpr (finiteType_of_isNilpotent_quotient_finiteType
        (B ⧸ L) N (A ⧸ IL) hNnil (RingHom.finiteType_algebraMap.mp hqbarft))
    -- Passing from `L` to `K` is a quotient of the source and target.
    let IK : Ideal A := Ideal.closure (K.map φ)
    have hKmap : K.map φ ≤ IK := subset_closure
    have hILK : IL ≤ IK := idealClosure_mono (Ideal.map_mono inf_le_right)
    let qBK : B ⧸ L →+* B ⧸ K := Ideal.Quotient.factor (show L ≤ K from inf_le_right)
    let qAK : A ⧸ IL →+* A ⧸ IK := Ideal.Quotient.factor hILK
    let fK : B ⧸ K →+* A ⧸ IK :=
      Ideal.quotientMap IK φ (Ideal.map_le_iff_le_comap.mp hKmap)
    have hcomm : qAK.comp fL = fK.comp qBK := by
      ext x
      simp [qAK, qBK, fL, fK, Ideal.quotientMap_mk]
    apply RingHom.FiniteType.of_comp_finiteType (f := qBK)
    rw [← hcomm]
    exact hLft.comp_surjective (Ideal.Quotient.factor_surjective _)

end

end TopologicalRing

end
