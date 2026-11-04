module

public import StacksFrontier.RingTheory.FormsTrace.Descent
public import StacksFrontier.RingTheory.FormsTrace.BaseChange

/-!
# Comparing descended trace maps through a common refinement

Let `B/A` and `B'/A'` be finite projective algebras, with a map of pairs `(A, B) → (A', B')`.
Suppose `B/A` is the base change of a finite projective `S/R` along a surjection `R → A`, and
likewise `B'/A'` of `S'/R'` along `R' → A'`, and that trace maps `Θ_R`, `Θ_{R'}` on the forms of
`S`, `S'` are given; they descend to `Θ_A`, `Θ_{A'}` (`Stacks.FormsTrace.descendForms`).

If both presentations map, compatibly with everything, to a third one `U/T` of `B'/A'`, over
which some family with property (1) of Stacks, Lemma 0FLB exists, and the pushout squares from
`S/R` and `S'/R'` to `U/T` satisfy the hypotheses of
`Stacks.FormsTrace.IsFormsTrace.formsMap_comm_of_isPushout` (a power of an element of `R`, resp.
`R'`, kills the relative differentials, and its image in `T` is a nonzerodivisor on the forms of
`T`), then `Θ_{A'} ∘ g^* = f^* ∘ Θ_A`.

This is the shape of the argument showing that the trace maps constructed from the universal
charts are independent of the chart and compatible with base change: the third presentation is
the polynomial ring over the scheme of changes of basis.

## Main results

* `Stacks.FormsTrace.descendForms_eq_of_refinement`: the descended map does not change when the
  presentation is replaced by a refinement.
* `Stacks.FormsTrace.descendForms_formsMap_of_refinement`: `Θ_{A'} ∘ g^* = f^* ∘ Θ_A`.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u

namespace Stacks.FormsTrace

/-- **A descended map is unchanged by passing to a refinement of the presentation.** If the
presentation `S'/R'` of `B'/A'` maps to a presentation `U/T` by a pushout square satisfying the
hypotheses of `IsFormsTrace.formsMap_comm_of_isPushout`, the maps descended from `S'/R'` and from
`U/T` agree. -/
theorem descendForms_eq_of_refinement {R' S' A' B' T U : Type u} [CommRing R'] [CommRing S']
    [CommRing A'] [CommRing B'] [CommRing T] [CommRing U]
    [Algebra R' S'] [Algebra R' A'] [Algebra A' B'] [Algebra S' B'] [Algebra R' B']
    [IsScalarTower R' A' B'] [IsScalarTower R' S' B'] [Algebra.IsPushout R' S' A' B']
    [Algebra T U] [Algebra T A'] [Algebra U B'] [Algebra T B']
    [IsScalarTower T A' B'] [IsScalarTower T U B'] [Algebra.IsPushout T U A' B']
    [Algebra R' T] [Algebra S' U] [Algebra R' U] [IsScalarTower R' T U] [IsScalarTower R' S' U]
    [Algebra.IsPushout R' S' T U] [IsScalarTower R' T A'] [IsScalarTower S' U B']
    [Module.Finite R' S'] [Module.Projective R' S'] [Module.Finite T U] [Module.Projective T U]
    [Module.Finite A' B'] [Module.Projective A' B']
    (hR' : Function.Surjective (algebraMap R' A')) (hT : Function.Surjective (algebraMap T A'))
    {h : R'} {N : ℕ} (hN : ∀ x : Ω[S'⁄R'], h ^ N • x = 0)
    (hreg : ∀ p, IsSMulRegular (⋀[T]^p Ω[T⁄ℤ]) (algebraMap R' T h))
    {Θ' : ∀ p : ℕ, ⋀[S']^p Ω[S'⁄ℤ] →ₗ[R'] ⋀[R']^p Ω[R'⁄ℤ]} (htr' : IsFormsTrace R' S' Θ')
    (hw' : IsWedgeLinear R' S' Θ')
    {ΘT : ∀ p : ℕ, ⋀[U]^p Ω[U⁄ℤ] →ₗ[T] ⋀[T]^p Ω[T⁄ℤ]} (htrT : IsFormsTrace T U ΘT)
    (hwT : IsWedgeLinear T U ΘT) :
    descendForms R' S' A' B' hR' Θ' hw' = descendForms T U A' B' hT ΘT hwT := by
  refine eq_of_formsMap_comp_eq (algebraMap_surjective_of_isPushout R' S' A' B' hR') fun p η => ?_
  rw [descendForms_formsMap, ← formsMap_formsMap (A := S') (B := U) (C := B'),
    descendForms_formsMap, htr'.formsMap_comm_of_isPushout hN hreg htrT,
    formsMap_formsMap (A := R') (B := T) (C := A')]

/-- **Descended trace maps are compatible with a map of pairs**, given a common refinement of the
two presentations: `Θ_{A'}(g^* x) = f^* Θ_A(x)`. -/
theorem descendForms_formsMap_of_refinement
    {R S A B R' S' A' B' T U : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [CommRing R'] [CommRing S'] [CommRing A'] [CommRing B'] [CommRing T] [CommRing U]
    -- the first presentation
    [Algebra R S] [Algebra R A] [Algebra A B] [Algebra S B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    -- the second presentation
    [Algebra R' S'] [Algebra R' A'] [Algebra A' B'] [Algebra S' B'] [Algebra R' B']
    [IsScalarTower R' A' B'] [IsScalarTower R' S' B'] [Algebra.IsPushout R' S' A' B']
    -- the refinement
    [Algebra T U] [Algebra T A'] [Algebra U B'] [Algebra T B']
    [IsScalarTower T A' B'] [IsScalarTower T U B'] [Algebra.IsPushout T U A' B']
    [Algebra R T] [Algebra S U] [Algebra R U] [IsScalarTower R T U] [IsScalarTower R S U]
    [Algebra.IsPushout R S T U]
    [Algebra R' T] [Algebra S' U] [Algebra R' U] [IsScalarTower R' T U] [IsScalarTower R' S' U]
    [Algebra.IsPushout R' S' T U] [IsScalarTower R' T A'] [IsScalarTower S' U B']
    -- the map of pairs, and the compatibilities
    [Algebra A A'] [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']
    [Algebra R A'] [IsScalarTower R T A'] [IsScalarTower R A A']
    [Algebra S B'] [IsScalarTower S U B'] [IsScalarTower S B B']
    [Module.Finite R S] [Module.Projective R S] [Module.Finite R' S'] [Module.Projective R' S']
    [Module.Finite T U] [Module.Projective T U] [Module.Finite A B] [Module.Projective A B]
    [Module.Finite A' B'] [Module.Projective A' B']
    (hR : Function.Surjective (algebraMap R A)) (hR' : Function.Surjective (algebraMap R' A'))
    (hT : Function.Surjective (algebraMap T A'))
    {h : R} {N : ℕ} (hN : ∀ x : Ω[S⁄R], h ^ N • x = 0)
    (hreg : ∀ p, IsSMulRegular (⋀[T]^p Ω[T⁄ℤ]) (algebraMap R T h))
    {h' : R'} {N' : ℕ} (hN' : ∀ x : Ω[S'⁄R'], h' ^ N' • x = 0)
    (hreg' : ∀ p, IsSMulRegular (⋀[T]^p Ω[T⁄ℤ]) (algebraMap R' T h'))
    {Θ : ∀ p : ℕ, ⋀[S]^p Ω[S⁄ℤ] →ₗ[R] ⋀[R]^p Ω[R⁄ℤ]} (htr : IsFormsTrace R S Θ)
    (hw : IsWedgeLinear R S Θ)
    {Θ' : ∀ p : ℕ, ⋀[S']^p Ω[S'⁄ℤ] →ₗ[R'] ⋀[R']^p Ω[R'⁄ℤ]} (htr' : IsFormsTrace R' S' Θ')
    (hw' : IsWedgeLinear R' S' Θ')
    {ΘT : ∀ p : ℕ, ⋀[U]^p Ω[U⁄ℤ] →ₗ[T] ⋀[T]^p Ω[T⁄ℤ]} (htrT : IsFormsTrace T U ΘT)
    (hwT : IsWedgeLinear T U ΘT) (p : ℕ) (x : ⋀[B]^p Ω[B⁄ℤ]) :
    descendForms R' S' A' B' hR' Θ' hw' p (formsMap B B' p x) =
      formsMap A A' p (descendForms R S A B hR Θ hw p x) := by
  rw [descendForms_eq_of_refinement hR' hT hN' hreg' htr' hw' htrT hwT]
  obtain ⟨η, rfl⟩ := DescentAux.formsMap_surjective
    (algebraMap_surjective_of_isPushout R S A B hR) p x
  rw [formsMap_formsMap (A := S) (B := B) (C := B'),
    ← formsMap_formsMap (A := S) (B := U) (C := B'), descendForms_formsMap,
    htr.formsMap_comm_of_isPushout hN hreg htrT, formsMap_formsMap (A := R) (B := T) (C := A'),
    descendForms_formsMap, formsMap_formsMap (A := R) (B := A) (C := A')]

end Stacks.FormsTrace

end
