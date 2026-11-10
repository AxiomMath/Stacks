module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Laurent
public import StacksFrontier.AlgebraicGeometry.Constructions.CoherentMulSections

/-!
# The powers of the Laurent unit named by a Veronese section

Let `L` be an invertible module on a scheme `Y`, `ψ` a family of Veronese sections of `L` for a
graded ring `𝒜` and a degree `d`, and `f ∈ 𝒜_d`. If the global section `ψ(f)` of `L`, placed in
degree one of the ring `⨁_{n ∈ ℤ} Γ(Y, L^{⊗ n})` of global Laurent sections, is a unit `w`, then
the natural powers of `w` are the Veronese powers: `w^n` is `ψ(f^n)` in degree `n`.

The Veronese powers are multiplicative
(`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.mulSections_pow`), and the
multiplication of the Laurent algebra is the product of honest sections read through the
comparison of the iterated with the integral tensor powers
(`Stacks.AlgebraicGeometry.CoherentMulSections.mulSections_mulBilinear`). So `n ↦ ψ(f^n)` in degree
`n` is multiplicative in the Laurent ring; at `n = 0` it is idempotent against the unit `w`, hence
`1`, and the identity follows by induction.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections.pw_natCast_eq_powCompare`: **the
  degree-`n` component of `w^n` is `ψ(f^n)`.**
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.RingedSpace Stacks.AlgebraicGeometry.ProjChartFromRatios

universe u w

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

attribute [local instance] gcommRing

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ}
  {Y : Scheme.{u}} {L : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace)}
  [hL : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf (isSheafStruct Y) L]

/-- The invertible module, in the spelling of `Stacks.Ample.IsInvertibleModule`. -/
theorem isInvertibleModule_of_isInvertible : Stacks.Ample.IsInvertibleModule Y L :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL

attribute [local instance] isInvertibleModule_of_isInvertible

variable (ψ : VeroneseSections 𝒜 d L) {f : A} (hf : f ∈ 𝒜 d)

/-- The Veronese power `ψ(f^n)`, placed in degree `n` of the ring of global Laurent sections. -/
def veronesePow (n : ℕ) : Ring L (op ⊤) :=
  DirectSum.of ((laurent L).sectionsPiece (op ⊤)) (n : ℤ)
    ((CoherentMulSections.powCompare L n).hom.app ⊤ (ψ.pow hf n))

/-- **The Veronese powers are multiplicative in the ring of global Laurent sections.** -/
theorem veronesePow_add (n m : ℕ) :
    veronesePow ψ hf (n + m) = veronesePow ψ hf n * veronesePow ψ hf m := by
  refine Eq.trans ?_ (of_mul_of (op ⊤) (n : ℤ) (m : ℤ) _ _).symm
  refine congrArg (DirectSum.of ((laurent L).sectionsPiece (op ⊤)) ((n + m : ℕ) : ℤ)) ?_
  set x := (CoherentMulSections.powCompare L n).hom.app ⊤ (ψ.pow hf n) with hx
  set y := (CoherentMulSections.powCompare L m).hom.app ⊤ (ψ.pow hf m) with hy
  have hmul : mulSections L (ψ.pow hf n) (ψ.pow hf m) =
      (CoherentMulSections.powCompare L (n + m)).inv.app ⊤
        ((Stacks.SheafOfModules.TensorPower.mulBilinear Y.presheaf (CoherentMulSections.hStruct Y) L
          (n : ℤ) (m : ℤ)).app (op ⊤) x y) :=
    (congrArg₂ (mulSections L) (CoherentMulSections.powCompare_inv_app_hom_app L n _)
      (CoherentMulSections.powCompare_inv_app_hom_app L m _)).symm.trans
      (CoherentMulSections.mulSections_mulBilinear L n m x y)
  refine (congrArg (fun z => (CoherentMulSections.powCompare L (n + m)).hom.app ⊤ z)
    ((ψ.mulSections_pow hf n m).symm.trans hmul)).trans ?_
  exact CoherentMulSections.powCompare_hom_app_inv_app L (n + m) _

variable (w : (Ring L (op ⊤))ˣ)
  (hw : (w : Ring L (op ⊤)) = DirectSum.of ((laurent L).sectionsPiece (op ⊤)) 1
    ((CoherentMulSections.powCompare L 1).hom.app ⊤ (ψ.pow hf 1)))

include hw in
/-- **The Veronese powers are the natural powers of the unit `w`.** -/
theorem veronesePow_eq_pow (n : ℕ) :
    veronesePow ψ hf n = ((w ^ n : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) := by
  have h1 : veronesePow ψ hf 1 = w := hw.symm
  have h0 : veronesePow ψ hf 0 = 1 := by
    have e : veronesePow ψ hf 0 * w = 1 * w := by
      rw [← h1, ← veronesePow_add, one_mul]
    exact (Units.mul_left_inj w).mp e
  induction n with
  | zero => rw [h0, pow_zero, Units.val_one]
  | succ n ih => rw [veronesePow_add, ih, h1, pow_succ, Units.val_mul]

include hw in
/-- **The degree-`n` component of `w^n` is the Veronese power `ψ(f^n)`.** -/
theorem pw_natCast_eq_powCompare (n : ℕ) :
    pw w (n : ℤ) = (CoherentMulSections.powCompare L n).hom.app ⊤ (ψ.pow hf n) := by
  have e := veronesePow_eq_pow ψ hf w hw n
  change ((w ^ (n : ℤ) : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) (n : ℤ) = _
  rw [zpow_natCast]
  exact (congrArg (fun z : Ring L (op ⊤) => z (n : ℤ)) e.symm).trans (DirectSum.of_eq_same _ _)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

end
