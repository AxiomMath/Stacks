module

public import StacksFrontier.RingTheory.Etale.LiftSmoothMap
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Residue-field points of smooth algebras over a henselian local ring lift

Let `R` be a henselian local ring and `B` a smooth `R`-algebra. Every `R`-algebra map
`B → κ(R)` is the reduction of an `R`-algebra map `B → R`.

## Main results

* `HenselianLocalRing.exists_algHom_residue_of_smooth`: the lifting statement.

## References

* [Stacks Project, Tag 07M7](https://stacks.math.columbia.edu/tag/07M7)
* [Stacks Project, Tag 08HQ](https://stacks.math.columbia.edu/tag/08HQ)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

/-- **A residue-field point of a smooth algebra over a henselian local ring lifts.** If `R` is
henselian local and `B` is a smooth `R`-algebra, every `R`-algebra map `B → κ(R)` is the reduction
of an `R`-algebra map `B → R`. -/
@[ega "IV 18.6.2" "partial", sga "3 X 8.9" "special case"]
theorem HenselianLocalRing.exists_algHom_residue_of_smooth {R : Type u} {B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] [HenselianLocalRing R] [Algebra.Smooth R B]
    (ψ : B →ₐ[R] ResidueField R) :
    ∃ σ : B →ₐ[R] R, ∀ b, residue R (σ b) = ψ b := by
  let e : (R ⧸ maximalIdeal R) ≃ₐ[R] ResidueField R := AlgEquiv.refl
  obtain ⟨A', _, _, hA', hq, f', hf'⟩ :=
    exists_etale_lift_of_smooth (maximalIdeal R) (e.symm.toAlgHom.comp ψ)
  set J := (maximalIdeal R).map (algebraMap R A')
  set q : (R ⧸ maximalIdeal R) →+* (A' ⧸ J) :=
    Ideal.quotientMap J (algebraMap R A') Ideal.le_comap_map
  let qe : (R ⧸ maximalIdeal R) ≃+* (A' ⧸ J) := RingEquiv.ofBijective q hq
  let ψ' : A' →ₐ[R] ResidueField R :=
    { toRingHom := qe.symm.toRingHom.comp (Ideal.Quotient.mk J)
      commutes' r := qe.injective <| (qe.apply_symm_apply _).trans
        (Ideal.quotientMap_mk (I := J) (J := maximalIdeal R) (f := algebraMap R A')
          (H := Ideal.le_comap_map) (x := r)).symm }
  obtain ⟨g, hg, -⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale ψ'
  refine ⟨g.comp f', fun b ↦ ?_⟩
  rw [AlgHom.comp_apply, hg]
  exact qe.injective <| (qe.apply_symm_apply _).trans (RingHom.congr_fun hf' b).symm

end
