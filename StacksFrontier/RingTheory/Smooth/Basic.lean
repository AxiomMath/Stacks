module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

/-!
# Smooth and formally smooth ring maps

Base change and composition of smooth, standard smooth and formally smooth ring maps are all
Mathlib's. This file records their Stacks tags, and their EGA and SGA references, on the Mathlib
declarations. That a polynomial ring is formally smooth over its base (Stacks 10.138.4, tag
`00TK`) is Mathlib's instance as well. The file proves Proposition 10.138.13 (tag `00TN`): a ring
map is of finite presentation and has the infinitesimal lifting property if and only if it is
smooth, `Algebra.finitePresentation_and_lifting_iff_smooth`.

## Conventions

* An ideal `I` of a commutative ring `A` is of *square zero* if `I ^ 2 = 0`, i.e.
  `x * y = 0` for all `x, y ∈ I`.
* An `R`-algebra `S` is *formally smooth* over `R` if for every commutative `R`-algebra `A`,
  every square-zero ideal `I ⊆ A` and every `R`-algebra map `g : S → A ⧸ I` there is an
  `R`-algebra map `f : S → A` with `π ∘ f = g`, where `π : A → A ⧸ I` is the projection.
  This is Stacks 10.138.1 (tag `00TI`). Mathlib's `Algebra.FormallySmooth R S` is defined
  instead by the cotangent condition (`Ω[S⁄R]` projective and `H¹(L_{S/R}) = 0`); the two agree
  by `Algebra.FormallySmooth.iff_comp_surjective`.
-/

-- The former @[stacks 00T4] declaration is now the Mathlib theorem.
add_to_stacks 00T4 "smoothness is stable under base change" Algebra.Smooth.baseChange
add_to_sga "1 II 4.13" "affine ascent" Algebra.Smooth.baseChange
add_to_sga "3 VIB 10.1" "smoothness, special case" Algebra.Smooth.baseChange
add_to_sga "3 VIB 2.1.2" "special case" Algebra.Smooth.baseChange
add_to_sga "6 VIII 1.6" "special case" Algebra.Smooth.baseChange
add_to_sga "6 VIII 1.8" "affine case" Algebra.Smooth.baseChange
add_to_sga "6 X 7.13.3" "special case" Algebra.Smooth.baseChange
add_to_ega "0 19.3.5" "(iii), special case" Algebra.Smooth.baseChange
add_to_ega "0 19.4.2" "Necessity, special case" Algebra.Smooth.baseChange
add_to_ega "0 19.4.6" "special case" Algebra.Smooth.baseChange
add_to_ega "IV 17.3.3" "(iii), special case" Algebra.Smooth.baseChange
add_to_ega "IV 17.7.3" "(ii)" Algebra.Smooth.baseChange
add_to_ega "IV 6.8.2" "special case" Algebra.Smooth.baseChange
add_to_ega "IV 6.8.3" "(iii), special case" Algebra.Smooth.baseChange
add_to_sga "1 II 1.3" "(ii), affine case" Algebra.Smooth.baseChange

-- The former @[stacks 00T9] declaration is now the Mathlib theorem.
add_to_stacks 00T9 "standard smoothness is stable under composition"
  RingHom.IsStandardSmooth.comp
add_to_sga "1 II 1.3" "(iii), special case" RingHom.IsStandardSmooth.comp

-- The former @[stacks 00TD] declaration is now the Mathlib theorem.
add_to_stacks 00TD "smoothness is stable under composition" RingHom.Smooth.comp
add_to_sga "1 II 1.3" "(iii), special case" RingHom.Smooth.comp
add_to_ega "IV 17.3.3" "(ii), special case" RingHom.Smooth.comp
add_to_ega "IV 6.8.3" "special case" RingHom.Smooth.comp

-- The former @[stacks 00TJ] declaration is now the Mathlib instance.
add_to_stacks 00TJ "formal smoothness is stable under base change"
  Algebra.FormallySmooth.instTensorProduct
add_to_ega "0 19.3.5" "(iii), special case" Algebra.FormallySmooth.instTensorProduct
add_to_ega "0 19.4.2" "Necessity, special case" Algebra.FormallySmooth.instTensorProduct
add_to_ega "0 19.4.6" "special case" Algebra.FormallySmooth.instTensorProduct
add_to_ega "0 19.9.3" "discrete topology" Algebra.FormallySmooth.instTensorProduct

add_to_ega "IV 17.3.1" "smooth case, ring maps" Algebra.smooth_iff
add_to_ega "IV 17.3.2" "(ii), smooth case" Algebra.smooth_iff

-- The former @[stacks 031H] declaration is now the Mathlib theorem.
add_to_stacks 031H "formal smoothness is stable under composition" Algebra.FormallySmooth.comp
add_to_ega "0 19.3.5" "(ii), special case" Algebra.FormallySmooth.comp
add_to_ega "0 19.5.4.4" "partial" Algebra.FormallySmooth.comp
add_to_ega "IV 17.1.3" "(ii), special case" Algebra.FormallySmooth.comp

@[expose] public section

universe u v w

namespace Algebra

/-- A lift of an `R`-algebra map `S → B ⧸ I` along `B → B ⧸ I` exists as soon as such lifts exist
for every ideal of the universe lift `ULift B`. -/
theorem exists_lift_of_uLift {R : Type*} {S : Type*} {B : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing B] [Algebra R B]
    (H : ∀ I : Ideal (ULift.{w} B), I ^ 2 = ⊥ →
      ∀ g : S →ₐ[R] ULift.{w} B ⧸ I, ∃ f : S →ₐ[R] ULift.{w} B, (Ideal.Quotient.mkₐ R I).comp f = g)
    (I : Ideal B) (hI : I ^ 2 = ⊥) (g : S →ₐ[R] B ⧸ I) :
    ∃ f : S →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  let e : ULift.{w} B ≃ₐ[R] B := ULift.algEquiv
  let I' : Ideal (ULift.{w} B) := I.comap (e : ULift.{w} B →+* B)
  have hI' : I'.map (e : ULift.{w} B →+* B) = I :=
    Ideal.map_comap_of_surjective _ e.surjective I
  have hsq : I' ^ 2 = ⊥ := le_bot_iff.mp <| (Ideal.le_comap_pow _ 2).trans <| by
    rw [hI]
    exact (Ideal.comap_bot_of_injective _ fun a b h ↦ e.injective h).le
  let q : (ULift.{w} B ⧸ I') ≃ₐ[R] B ⧸ I := Ideal.quotientEquivAlg I' I e hI'.symm
  obtain ⟨f, hf⟩ := H I' hsq (q.symm.toAlgHom.comp g)
  refine ⟨e.toAlgHom.comp f, AlgHom.ext fun s ↦ ?_⟩
  have h := congr(q ($hf s))
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at h
  rw [← h]
  rfl

/-- **Stacks 00TN.** Let `R → S` be a ring map. Then `R → S` is of finite presentation and formally
smooth in the sense of Stacks 00TI (every `R`-algebra map `S → B ⧸ I`, for `I` an ideal of square
zero in an `R`-algebra `B`, lifts to an `R`-algebra map `S → B`) if and only if `R → S` is smooth
in the sense of Stacks 00T2. -/
@[stacks 00TN "The lifting property (Definition 00TI) is spelled out, not Mathlib's
`FormallySmooth`, which is defined by the cotangent condition. The test rings `B` range over
`Type (max u w)` for an arbitrary universe `w`, with `R : Type u`: every universe containing
`R`'s. `Algebra.Smooth` is Definition 00T2: finite presentation, `Ω[S⁄R]` projective (finite by
finite presentation) and `H¹(L_{S/R}) = 0`."]
theorem finitePresentation_and_lifting_iff_smooth {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] :
    (FinitePresentation R S ∧ ∀ (B : Type (max u w)) [CommRing B] [Algebra R B] (I : Ideal B),
      I ^ 2 = ⊥ → ∀ g : S →ₐ[R] B ⧸ I, ∃ f : S →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g) ↔
      Smooth R S := by
  refine ⟨fun ⟨_, H⟩ ↦ ?_, fun h ↦ ⟨h.finitePresentation, fun B _ _ I hI g ↦
    FormallySmooth.comp_surjective R S I hI g⟩⟩
  obtain ⟨n, f, hf⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := S)).mp inferInstance
  have : FormallySmooth R S := by
    rw [FormallySmooth.iff_split_surjection f hf]
    have surj : Function.Surjective f.kerSquareLift :=
      Ideal.Quotient.lift_surjective_of_surjective _ _ hf
    have sqz : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = ⊥ := by
      rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
    dsimp only [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom] at sqz
    obtain ⟨g, hg⟩ := exists_lift_of_uLift
      (B := MvPolynomial (Fin n) R ⧸ RingHom.ker f.toRingHom ^ 2)
      (fun I hI g ↦ H (ULift.{w} _) I hI g) _ sqz
      (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom
    exact ⟨g, AlgHom.ext fun x ↦ congr(f.kerSquareLift.kerLift ($hg x)).trans
      ((Ideal.quotientKerAlgEquivOfSurjective surj).apply_symm_apply x)⟩
  exact {}

end Algebra

end
