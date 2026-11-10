module

public import StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Basic

/-!
# The evaluation at a closed point over an algebraically closed field

The sibling file `Basic.lean` proves that the evaluation `V → ℒ_x/𝔪_x²ℒ_x` of a generating
linear system defining an immersion is surjective, under the hypothesis that `x` is a
`k`-rational point, spelled as: every element of `𝒪_{X,x}` agrees with a constant modulo
`𝔪_x`. This file discharges that hypothesis in the situation of the proof of
[Stacks, Tag 0FD6], where the base field has been enlarged to an algebraically closed one and
`x` is a closed point of a scheme locally of finite type over it.

The residue field extension at such a point is an isomorphism, which is
`AlgebraicGeometry.isIso_residueFieldMap_of_isClosed`; what has to be added is that the residue
field of `Spec k` itself is `k`, so that the composite `k → 𝒪_{X,x} → κ(x)` — and not merely
`κ(f x) → κ(x)` — is surjective.

## Main results

* `IsLocalization.AtPrime.surjective_algebraMap_of_field`: a localization of a field at a prime
  is the field, in the sense that its structure map is surjective.
* `Ideal.surjective_algebraMap_residueField_of_field`: likewise for the residue field.
* `AlgebraicGeometry.surjective_residue_germ_Spec_of_field`: every element of the residue field
  of a point of `Spec k`, for `k` a field, is the class of a constant.
* `AlgebraicGeometry.surjective_residue_baseGerm` and
  `AlgebraicGeometry.exists_sub_baseGerm_mem_maximalIdeal`: **a closed point of a scheme
  locally of finite type over an algebraically closed field is `k`-rational.**
* `Stacks.ImmersionEvaluationSurjective.surjective_evalQuotient_of_isClosed`: **the detail
  [Stacks, Tag 0FD6] omits, in the situation of its proof.**

## Implementation notes

The comparison `κ(f x) → κ(x)` is produced by `Scheme.evaluation_naturality_apply` at the top
open, which is what expresses the composite `k → 𝒪_{X,x} → κ(x)` through the residue field of
the base; `Spec.algebraMap_residueFieldIso_inv` is what reads the residue field of a point of
`Spec k` as `Ideal.ResidueField` of the corresponding prime, where the surjectivity is the
elementary ring statement above.

**No `@[stacks]` attribute is attached**, for the same reason as in the sibling file: this is
the proof of a step omitted inside the proof of Tag 0FD6.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

/-- **The structure map of a localization of a field at a prime is surjective**: every element of
the localization is a fraction with invertible denominator. -/
theorem IsLocalization.AtPrime.surjective_algebraMap_of_field {R : Type*} [Field R]
    (S : Type*) [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime S p] : Function.Surjective (algebraMap R S) := by
  intro y
  obtain ⟨⟨a, b⟩, hb⟩ := IsLocalization.surj p.primeCompl y
  have hb0 : (b : R) ≠ 0 := fun h => b.2 (h ▸ p.zero_mem)
  refine ⟨a * (b : R)⁻¹, ?_⟩
  have h1 : algebraMap R S (a * (b : R)⁻¹) * algebraMap R S (b : R) =
      y * algebraMap R S (b : R) := by
    rw [← map_mul, inv_mul_cancel_right₀ hb0, hb]
  exact (IsUnit.mul_left_inj (IsLocalization.map_units S b)).1 h1

/-- **The residue field of a field at a prime is the field itself**, in the sense that the
structure map onto it is surjective. -/
theorem Ideal.surjective_algebraMap_residueField_of_field {R : Type*} [Field R]
    (p : Ideal R) [p.IsPrime] : Function.Surjective (algebraMap R p.ResidueField) := by
  rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime p) p.ResidueField]
  simp only [RingHom.coe_comp]
  refine Function.Surjective.comp ?_
    (IsLocalization.AtPrime.surjective_algebraMap_of_field _ p)
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

namespace AlgebraicGeometry

/-- **Every element of the residue field of a point of `Spec k`, for `k` a field, is the class of
a constant.** -/
theorem surjective_residue_germ_Spec_of_field {R : Type u} [Field R]
    (x : Spec (CommRingCat.of R)) :
    Function.Surjective fun r : R =>
      ((Spec (CommRingCat.of R)).residue x).hom
        (((Spec (CommRingCat.of R)).presheaf.germ ⊤ x trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  let : Field (CommRingCat.of R) := ‹Field R›
  have : x.asIdeal.IsPrime := x.isPrime
  have h := (CategoryTheory.ConcreteCategory.bijective_of_isIso
    (Scheme.Spec.residueFieldIso (CommRingCat.of R) x).inv).2.comp
    (Ideal.surjective_algebraMap_residueField_of_field x.asIdeal)
  exact fun y => let ⟨r, hr⟩ := h y
    ⟨r, (CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of R) x) r).symm.trans hr⟩

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

open Stacks.ImmersionEvaluationSurjective in
/-- **At a closed point of a scheme locally of finite type over an algebraically closed field
the residue field is the base field**: every residue is the residue of a constant. -/
theorem surjective_residue_baseGerm [LocallyOfFiniteType f] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    Function.Surjective fun c : k => X.residue x (baseGerm f x c) := by
  have : LocallyOfFiniteType (f ≫ 𝟙 (Spec (CommRingCat.of k))) := by
    rw [Category.comp_id]; infer_instance
  have : IsIso (f.residueFieldMap x) := isIso_residueFieldMap_of_isClosed f (𝟙 _) x hx
  have h := (CategoryTheory.ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)).2.comp
    (surjective_residue_germ_Spec_of_field (f x))
  exact fun y => let ⟨c, hc⟩ := h y
    ⟨c, (Scheme.evaluation_naturality_apply f (V := ⊤) x trivial _).symm.trans hc⟩

open Stacks.ImmersionEvaluationSurjective in
/-- **A closed point of a scheme locally of finite type over an algebraically closed field is
`k`-rational**, in the form the evaluation statement consumes: every element of the stalk agrees
with a constant modulo the maximal ideal. -/
theorem exists_sub_baseGerm_mem_maximalIdeal [LocallyOfFiniteType f] {x : X}
    (hx : IsClosed ({x} : Set X)) (a : X.presheaf.stalk x) :
    ∃ c : k, a - baseGerm f x c ∈ maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨c, hc⟩ := surjective_residue_baseGerm f hx (X.residue x a)
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  change X.residue x (a - baseGerm f x c) = 0
  rw [map_sub]
  exact sub_eq_zero_of_eq hc.symm

end AlgebraicGeometry

/-! ### The evaluation at a closed point over an algebraically closed field -/

namespace Stacks.ImmersionEvaluationSurjective

open Stacks.ModuleStalk Stacks.ProjectiveFromSections

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} {X : Scheme.{u}} {L : X.Modules}
  [Stacks.Ample.IsInvertibleModule X L] (s : Fin (n + 1) → Γ(L, ⊤))
  (hs : GeneratesStalks s) (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {V : Type u} [AddCommGroup V] [Module k V]

/-- **The detail [Stacks, Tag 0FD6] omits, in the situation of its proof.** The base field is
algebraically closed, `X` is of finite type over it and `x` is a closed point; `ψ : V → Γ(X, ℒ)`
sends a basis of `V` to a family generating the invertible module `ℒ`, and the morphism
`φ_{ℒ,ψ} : X ⟶ 𝐏(V)` of [Stacks, Tag 0FCY] is an immersion. Then the evaluation
`V ⟶ ℒ_x/𝔪_x²ℒ_x` is surjective. -/
theorem surjective_evalQuotient_of_isClosed (b : Module.Basis (Fin (n + 1)) k V)
    [AlgebraicGeometry.IsImmersion (AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f)]
    {x : X} (hx : IsClosed ({x} : Set X)) :
    Function.Surjective fun c : Fin (n + 1) → k =>
      Submodule.Quotient.mk (p := maximalSqSmul L x)
        (∑ j, baseGerm f x (c j) • (L.presheaf.Γgerm x).hom (s j)) :=
  surjective_evalQuotient_of_isImmersion s hs f b
    (AlgebraicGeometry.exists_sub_baseGerm_mem_maximalIdeal f hx)

end Stacks.ImmersionEvaluationSurjective

end
