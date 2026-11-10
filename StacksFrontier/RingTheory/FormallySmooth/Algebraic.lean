module

public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.RingTheory.FormallySmooth.Adic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Algebraic formal smoothness and adic topologies

An algebraically formally smooth homomorphism is topologically formally smooth when the target
topology is adic.  Continuity of the lift follows by squaring a power of the ideal that is killed
after passage to the square-zero quotient.

## References

* [Stacks Project, Tag 07EC](https://stacks.math.columbia.edu/tag/07EC)
-/

@[expose] public section

namespace RingHom.FormallySmoothTop

/-- Algebraic formal smoothness implies topological formal smoothness for an adic target. -/
@[stacks 07EC, ega "0 19.3.8" "discrete topologies"]
theorem of_formallySmooth_of_isAdic.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsTopologicalRing S]
    (phi : R →+* S) (n : Ideal S) (hn : IsAdic n)
    (hphi : @Algebra.FormallySmooth R S _ _ phi.toAlgebra) :
    RingHom.FormallySmoothTop.{u, v, w} phi := by
  intro A _ tA _ J hJ f _ gbar hgbarCont hcomm
  let : Algebra R S := phi.toAlgebra
  let : Algebra R A := f.toAlgebra
  let gbarAlg : S →ₐ[R] A ⧸ J :=
    { gbar with
      commutes' := fun r ↦ by
        change gbar (phi r) = Ideal.Quotient.mk J (f r)
        exact DFunLike.congr_fun hcomm r }
  let : Algebra.FormallySmooth R S := hphi
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ gbarAlg
  have hgbarEq : (Ideal.Quotient.mk J).comp g.toRingHom = gbar :=
    congrArg AlgHom.toRingHom hg
  have hcont : Continuous g := by
    let : DiscreteTopology (A ⧸ J) :=
      QuotientAddGroup.discreteTopology (isOpen_discrete (J : Set A))
    have hA : tA = (⊥ : Ideal A).adicTopology :=
      (is_bot_adic_iff (A := A)).2 (inferInstance : DiscreteTopology A)
    have hQ : (inferInstance : TopologicalSpace (A ⧸ J)) =
        (⊥ : Ideal (A ⧸ J)).adicTopology :=
      (is_bot_adic_iff (A := A ⧸ J)).2 (inferInstance : DiscreteTopology (A ⧸ J))
    rw [hn, hA]
    apply (RingHom.continuous_adic_iff g.toRingHom n ⊥).2
    obtain ⟨k, hk, hkmap⟩ :=
      (RingHom.continuous_adic_iff gbar n ⊥).1 (by
        change @Continuous S (A ⧸ J) n.adicTopology
          (⊥ : Ideal (A ⧸ J)).adicTopology gbar
        rw [← hn, ← hQ]
        exact hgbarCont)
    refine ⟨k * 2, by omega, fun x hx => ?_⟩
    have hmap : Ideal.map g.toRingHom (n ^ k) ≤ J :=
      Ideal.map_le_iff_le_comap.mpr fun y hy => (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
        ((DFunLike.congr_fun hgbarEq y).trans (by simpa using hkmap y hy))
    have hxmap : g x ∈ Ideal.map g.toRingHom (n ^ (k * 2)) :=
      Ideal.mem_map_of_mem g.toRingHom hx
    rw [pow_mul, Ideal.map_pow] at hxmap
    simpa [hJ] using Ideal.pow_right_mono hmap 2 hxmap
  exact ⟨g.toRingHom, hcont, RingHom.ext g.commutes, hgbarEq⟩

end RingHom.FormallySmoothTop
