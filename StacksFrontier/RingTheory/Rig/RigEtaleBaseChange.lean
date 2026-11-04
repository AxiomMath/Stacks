module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeSmulId
public import StacksFrontier.RingTheory.Rig.RigSmoothDefs

/-!
# Rig-étaleness is preserved by completed base change

Let `A₁ → A₂` be a map of Noetherian rings, let `Iᵢ ⊆ Aᵢ` be ideals with `V(I₁ A₂) = V(I₂)`,
let `B₁` be adically of finite type over `(A₁, I₁)` and let `B₂ = (B₁ ⊗_{A₁} A₂)^∧_{I₂}` be
its completed base change. If `B₁` is rig-étale over `(A₁, I₁)` then `B₂` is rig-étale over
`(A₂, I₂)`. The hypothesis `V(I₁ A₂) = V(I₂)` is an equality of zero loci in `Spec A₂`.

## Main definitions

* `Rig.annihilatorIdeal` — the ideal of scalars of the base whose image annihilates every
  endomorphism of an object of the derived category of the algebra.

## Main results

* `Rig.isRigEtale_of_completedBaseChange` — the statement for an arbitrary realization of the
  completed base change, the identification of `B₂` with `(B₁ ⊗_{A₁} A₂)^∧_{I₂}` taken as data.
* `Rig.isRigEtale_completedBaseChangeFunctor` — the same for any
  `Rig.CompletedBaseChange` functor.
* `Rig.isRigEtale_completedBaseChangeOfIsNoetherianRing` — the statement for the completed base
  change `Rig.completedBaseChangeOfIsNoetherianRing` of Remark 0AL5.
* `Rig.exists_pos_pow_map_le_of_zeroLocus_eq` and `Rig.le_radical_map_pow_of_zeroLocus_eq` — if
  `V(I₁ A₂) = V(I₂)`, then a positive power of `I₁` extends into `I₂`, and `I₂` lies in the
  radical of the extension of every power of `I₁`.

## References

* [Stacks Project, Tag 0GB2](https://stacks.math.columbia.edu/tag/0GB2)
* [Stacks Project, Tag 0AK2](https://stacks.math.columbia.edu/tag/0AK2)
* [Stacks Project, Tag 0AL5](https://stacks.math.columbia.edu/tag/0AL5)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u₁ u₂ v w

attribute [local instance] HasDerivedCategory.standard

section ZeroLocus

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
  {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂}

omit [IsNoetherianRing A₁] in
/-- If `I₁ A₂` and `I₂` cut out the same closed subset of `Spec A₂`, then a positive power of
`I₁` extends into `I₂`. -/
public theorem exists_pos_pow_map_le_of_zeroLocus_eq
    (hV : PrimeSpectrum.zeroLocus ((I₁.map (algebraMap A₁ A₂) : Ideal A₂) : Set A₂) =
      PrimeSpectrum.zeroLocus (I₂ : Set A₂)) :
    ∃ c : ℕ, 0 < c ∧ (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂ := by
  have hle : I₁.map (algebraMap A₁ A₂) ≤ I₂.radical :=
    Ideal.le_radical.trans (PrimeSpectrum.zeroLocus_eq_iff.mp hV).le
  obtain ⟨n, hn⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hle (I₁.map (algebraMap A₁ A₂)).fg_of_isNoetherianRing
  refine ⟨n + 1, n.succ_pos, ?_⟩
  rw [Ideal.map_pow]
  exact (Ideal.pow_le_pow_right n.le_succ).trans hn

omit [IsNoetherianRing A₁] [IsNoetherianRing A₂] in
/-- If `I₁ A₂` and `I₂` cut out the same closed subset of `Spec A₂`, then `I₂` is contained in
the radical of the extension of every power of `I₁`. -/
public theorem le_radical_map_pow_of_zeroLocus_eq
    (hV : PrimeSpectrum.zeroLocus ((I₁.map (algebraMap A₁ A₂) : Ideal A₂) : Set A₂) =
      PrimeSpectrum.zeroLocus (I₂ : Set A₂)) (c : ℕ) :
    I₂ ≤ ((I₁ ^ c).map (algebraMap A₁ A₂)).radical := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [pow_zero, Ideal.one_eq_top, Ideal.map_top, Ideal.radical_top]
    exact le_top
  · rw [Ideal.map_pow, Ideal.radical_pow _ hc.ne', PrimeSpectrum.zeroLocus_eq_iff.mp hV]
    exact Ideal.le_radical

end ZeroLocus

section Annihilator

variable {A : Type u₁} [CommRing A] {I : Ideal A}

/-- The ideal of scalars of `A` whose image in `B` annihilates every endomorphism of an object
`X` of `D(B)`: the pullback along `A → B` of the annihilator of `End X`. -/
public def annihilatorIdeal (B : AdicFiniteTypeAlgebra.{u₁, v} A I)
    (X : DerivedCategory (ModuleCat.{max u₁ v} B.carrier)) : Ideal A :=
  (Module.annihilator B.carrier (End X)).comap (algebraMap A B.carrier)

/-- A scalar lies in `Rig.annihilatorIdeal` as soon as its image kills the identity of `X`. -/
public theorem mem_annihilatorIdeal_of_smul_id_eq_zero
    {B : AdicFiniteTypeAlgebra.{u₁, v} A I}
    {X : DerivedCategory (ModuleCat.{max u₁ v} B.carrier)} {a : A}
    (h : (algebraMap A B.carrier a) • 𝟙 X = 0) : a ∈ annihilatorIdeal B X := by
  refine Module.mem_annihilator.mpr fun f ↦ ?_
  calc (algebraMap A B.carrier a) • f
      = ((algebraMap A B.carrier a) • 𝟙 X) ≫ f := by simp
    _ = 0 := by rw [h]; simp

/-- Membership in `Rig.annihilatorIdeal` in particular kills the identity of `X`. -/
public theorem smul_id_eq_zero_of_mem_annihilatorIdeal
    {B : AdicFiniteTypeAlgebra.{u₁, v} A I}
    {X : DerivedCategory (ModuleCat.{max u₁ v} B.carrier)} {a : A}
    (h : a ∈ annihilatorIdeal B X) : (algebraMap A B.carrier a) • 𝟙 X = 0 :=
  Module.mem_annihilator.mp h (𝟙 X)

end Annihilator

section BaseChange

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
  {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂}
  {B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁} {B₂ : AdicFiniteTypeAlgebra.{u₂, w} A₂ I₂}
  [Algebra B₁.carrier B₂.carrier] [Algebra A₁ B₂.carrier]
  [IsScalarTower A₁ A₂ B₂.carrier] [IsScalarTower A₁ B₁.carrier B₂.carrier]

/-- To show `B'` rig-étale from `B` rig-étale it suffices to deduce, from an exponent `d` killing
the identity of the cotangent complex of `B`, that the image of `I₁ ^ d` kills those of `B'`. -/
private theorem isRigEtale_of_forall_smul_id_eq_zero_of_mem_pow
    (hV : PrimeSpectrum.zeroLocus ((I₁.map (algebraMap A₁ A₂) : Ideal A₂) : Set A₂) =
      PrimeSpectrum.zeroLocus (I₂ : Set A₂))
    {B : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁} {B' : AdicFiniteTypeAlgebra.{u₂, w} A₂ I₂}
    (hB : IsRigEtale B)
    (h : ∀ d : ℕ, (∀ x : A₁, x ∈ I₁ ^ d → algebraMap A₁ B.carrier x • 𝟙
        (derivedCompletedNaiveCotangentComplex B
          (completedPolynomialPresentation I₁ I₁.fg_of_isNoetherianRing B)) = 0) →
      ∀ (P : CompletedPolynomialPresentation I₂ B') (x : A₁), x ∈ I₁ ^ d →
        algebraMap A₂ B'.carrier (algebraMap A₁ A₂ x) •
          𝟙 (derivedCompletedNaiveCotangentComplex B' P) = 0) :
    IsRigEtale B' := by
  obtain ⟨d, hd⟩ := hB (completedPolynomialPresentation I₁ I₁.fg_of_isNoetherianRing B)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (le_radical_map_pow_of_zeroLocus_eq hV d) I₂.fg_of_isNoetherianRing
  intro P
  refine ⟨n, fun a ha ↦ smul_id_eq_zero_of_mem_annihilatorIdeal ?_⟩
  have hle : (I₁ ^ d).map (algebraMap A₁ A₂) ≤
      annihilatorIdeal B' (derivedCompletedNaiveCotangentComplex B' P) := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun x hx ↦ mem_annihilatorIdeal_of_smul_id_eq_zero (h d hd P x hx)
  exact hle (hn ha)

/-- Let `A₁ → A₂` be a map of Noetherian rings, let `Iᵢ ⊆ Aᵢ` be ideals with `V(I₁ A₂) = V(I₂)`,
let `B₁` be adically of finite type over `(A₁, I₁)` and let `B₂` be its completed base change
`(B₁ ⊗_{A₁} A₂)^∧_{I₂}`, the identification being the data `e`, `heA`, `heB`. If `B₁` is
rig-étale over `(A₁, I₁)` then `B₂` is rig-étale over `(A₂, I₂)`. -/
public theorem isRigEtale_of_completedBaseChange
    (hV : PrimeSpectrum.zeroLocus ((I₁.map (algebraMap A₁ A₂) : Ideal A₂) : Set A₂) =
      PrimeSpectrum.zeroLocus (I₂ : Set A₂))
    (e : B₂.carrier ≃+* completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
    (heA : ∀ a : A₂, e (algebraMap A₂ B₂.carrier a) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedRight A₂ B₁ a))
    (heB : ∀ b : B₁.carrier, e (algebraMap B₁.carrier B₂.carrier b) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedLeft A₂ B₁ b))
    (hB₁ : IsRigEtale B₁) : IsRigEtale B₂ := by
  obtain ⟨c, hc, hmap⟩ := exists_pos_pow_map_le_of_zeroLocus_eq hV
  refine isRigEtale_of_forall_smul_id_eq_zero_of_mem_pow hV hB₁ fun d hd P₂ x hx ↦ ?_
  have h₂ := smul_id_of_completedBaseChange hc hmap e heA heB _ P₂
    (algebraMap A₁ B₁.carrier x) (hd x hx)
  have hscal : algebraMap A₂ B₂.carrier (algebraMap A₁ A₂ x) =
      algebraMap B₁.carrier B₂.carrier (algebraMap A₁ B₁.carrier x) := by
    rw [← IsScalarTower.algebraMap_apply A₁ A₂ B₂.carrier x,
      IsScalarTower.algebraMap_apply A₁ B₁.carrier B₂.carrier x]
  exact (congrArg (fun r : B₂.carrier ↦
    r • 𝟙 (derivedCompletedNaiveCotangentComplex B₂ P₂)) hscal).trans h₂

end BaseChange

section Functor

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
  {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂}

omit [IsNoetherianRing A₁] [IsNoetherianRing A₂] in
/-- The image in the completed base change of a scalar coming from `A₁` is the image of its
own image in `A₂`. -/
private theorem scalar_algebraMap_eq
    (C : CompletedBaseChange (A₁ := A₁) (A₂ := A₂) (I₁ := I₁) (I₂ := I₂))
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (x : A₁) :
    C.scalar B₁ (algebraMap A₁ B₁.carrier x) =
      algebraMap A₂ (C.functor.obj B₁).carrier (algebraMap A₁ A₂ x) := by
  have hleft : baseChangedLeft A₂ B₁ (algebraMap A₁ B₁.carrier x) =
      baseChangedRight A₂ B₁ (algebraMap A₁ A₂ x) := by
    simp only [baseChangedLeft, baseChangedRight, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply]
    rw [Algebra.algebraMap_eq_smul_one (R := A₁) (A := B₁.carrier),
      Algebra.algebraMap_eq_smul_one (R := A₁) (A := A₂), TensorProduct.smul_tmul]
  refine (C.completedTensorProductEquiv B₁).injective ?_
  rw [C.algebraMap_completedTensorProductEquiv, CompletedBaseChange.scalar,
    RingEquiv.apply_symm_apply]
  exact congrArg (AdicCompletion.of (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁)
    (baseChangedAlgebra (A₂ := A₂) B₁)) hleft

/-- Rig-étaleness is preserved by any realization `C` of the completed base change
`B₁ ↦ (B₁ ⊗_{A₁} A₂)^∧_{I₂}` of Stacks Remark 0AL5, along a map of Noetherian rings with
`V(I₁ A₂) = V(I₂)`. -/
public theorem isRigEtale_completedBaseChangeFunctor
    (hV : PrimeSpectrum.zeroLocus ((I₁.map (algebraMap A₁ A₂) : Ideal A₂) : Set A₂) =
      PrimeSpectrum.zeroLocus (I₂ : Set A₂))
    (C : CompletedBaseChange (A₁ := A₁) (A₂ := A₂) (I₁ := I₁) (I₂ := I₂))
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (hB₁ : IsRigEtale B₁) :
    IsRigEtale (C.functor.obj B₁) := by
  obtain ⟨c, hc, hmap⟩ := exists_pos_pow_map_le_of_zeroLocus_eq hV
  refine isRigEtale_of_forall_smul_id_eq_zero_of_mem_pow hV hB₁ fun d hd P₂ x hx ↦ ?_
  have h₂ := smul_id_of_completedBaseChangeFunctor C hc hmap B₁ _ P₂
    (algebraMap A₁ B₁.carrier x) (hd x hx)
  exact (congrArg (fun r : (C.functor.obj B₁).carrier ↦
    r • 𝟙 (derivedCompletedNaiveCotangentComplex (C.functor.obj B₁) P₂))
    (scalar_algebraMap_eq C B₁ x)).symm.trans h₂

/-- Let `A₁ → A₂` be a map of Noetherian rings and let `Iᵢ ⊆ Aᵢ` be ideals with
`V(I₁ A₂) = V(I₂)`. Let `B₁` be adically of finite type over `(A₁, I₁)` and let
`B₂ = (B₁ ⊗_{A₁} A₂)^∧_{I₂}` be its base change as in Stacks Remark 0AL5, the functor
`Rig.completedBaseChangeOfIsNoetherianRing`. If `B₁` is rig-étale over `(A₁, I₁)`, then `B₂` is
rig-étale over `(A₂, I₂)`. -/
@[stacks 0GB2 "preservation of rig-étaleness"]
public theorem isRigEtale_completedBaseChangeOfIsNoetherianRing
    (hV : PrimeSpectrum.zeroLocus ((I₁.map (algebraMap A₁ A₂) : Ideal A₂) : Set A₂) =
      PrimeSpectrum.zeroLocus (I₂ : Set A₂))
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (hB₁ : IsRigEtale B₁) :
    IsRigEtale ((completedBaseChangeOfIsNoetherianRing
      (exists_pos_pow_map_le_of_zeroLocus_eq hV)).functor.obj B₁) :=
  isRigEtale_completedBaseChangeFunctor hV _ B₁ hB₁

end Functor

end Rig

end
