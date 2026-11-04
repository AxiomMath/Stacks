module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeExt
public import StacksFrontier.RingTheory.Rig.RigSmoothDefs

/-!
# Rig-smoothness is preserved by completed base change (Stacks 0GAM)

Let `A₁ → A₂` be a map of Noetherian rings and let `I₁ ⊆ A₁`, `I₂ ⊆ A₂` be ideals cutting out
the same closed subset of `Spec A₂` after extension of scalars, that is, with
`(I₁ A₂)^rad = I₂^rad`.  Let `B₁` be an `I₁`-adically complete `A₁`-algebra of finite type
modulo `I₁` and let `B₂ = (B₁ ⊗_{A₁} A₂)^∧_{I₂}` be its completed base change.  If `B₁` is
rig-smooth over `(A₁, I₁)` then `B₂` is rig-smooth over `(A₂, I₂)`.

## Main results

* `Rig.isRigSmooth_completedBaseChange`: **Stacks 0GAM**, for a `Rig.CompletedBaseChange`
  functor, which is the form the source states — `B₂` *is* the base change.
* `Rig.isRigSmooth_of_completedBaseChange`: the same, as the general *engine*, taking the
  identification of `B₂` with `(B₁ ⊗_{A₁} A₂)^∧_{I₂}` as data rather than reading `B₂` off a
  functor.  This is the shape `Rig.isRigEtale_of_completedBaseChange` has for Stacks 0GB2, and
  the shape in which the base change can be applied to an algebra that merely *happens* to be
  one, which is what transport of rig-smoothness along an isomorphism needs
  (`Rig.isRigSmooth_of_algEquiv`).

## Implementation notes

Equality of the closed subsets `V(I₁ A₂)` and `V(I₂)` is expressed as equality of the radicals
of the two ideals, which is the same condition by `PrimeSpectrum.zeroLocus_eq_iff`.  Over a
Noetherian ring that single hypothesis supplies both halves of the comparison, and no further
input is needed: the inclusion `I₁ A₂ ≤ I₂^rad` gives an exponent `c ≥ 1` with
`I₁^c A₂ ≤ I₂`, which is the condition of Stacks Remark 0AL5 under which the base change
exists and the hypothesis that `Rig.smul_ext_one_of_completedBaseChangeFunctor` asks for; and
the reverse inclusion `I₂ ≤ (I₁ A₂)^rad` gives an exponent `d` with `I₂^d ≤ I₁ A₂`, which is
what converts the annihilating power of `I₁` into an annihilating power of `I₂`.

The base change is taken to be any `Rig.CompletedBaseChange`, so the statement applies to any
realization of the functor rather than only to the model `Rig.completedBaseChange`.  The
exponent produced is `d * n` for `n` the exponent witnessing rig-smoothness of `B₁`, since
`I₂^(d*n) = (I₂^d)^n ≤ (I₁ A₂)^n = I₁^n A₂`.

The engine form drops the functor altogether: `B₂` is an arbitrary object of the category
attached to `(A₂, I₂)`, carrying algebra structures over `B₁` and over `A₁` that make the two
routes from `A₁` into it agree, and the identification with the completion of the tensor
product is the hypothesis `e` together with its compatibilities `heA`, `heB`.  That is exactly
the data `Rig.smul_ext_one_of_completedBaseChange` consumes, so the proof is the functor form's
with `Rig.algebraMap_baseChange_eq_scalar` — which reads the structural map of `A₂` off the
functor — replaced by the scalar-tower identity
`algebraMap A₂ B₂ ∘ algebraMap A₁ A₂ = algebraMap B₁ B₂ ∘ algebraMap A₁ B₁`.  Neither form is
derivable from the other without redoing that plumbing, so both are proved directly, as they
are for Stacks 0GB2 in `StacksFrontier/RingTheory/Rig/RigEtaleBaseChange.lean`.

Rig-smoothness asserts the annihilation of *all* `Ext¹` classes out of the completed naive
cotangent complex by every element of a power of the ideal, while Stacks 0GAL transports the
annihilation by one scalar at a time.  The passage from one to the other is the observation
that the scalars annihilating a fixed class form an ideal, `Ideal.torsionOf`: the elements
of `I₁^n A₂` that 0GAL reaches directly are the images of elements of `I₁^n`, and the ideal
they generate then contains the whole of `I₂^(d*n)`.

## References

* [Stacks Project, Tag 0GAM](https://stacks.math.columbia.edu/tag/0GAM)
* [Stacks Project, Tag 0GAI](https://stacks.math.columbia.edu/tag/0GAI)
* [Stacks Project, Tag 0GAL](https://stacks.math.columbia.edu/tag/0GAL)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u₁ u₂ v w

attribute [local instance] HasDerivedCategory.standard

/-- The structural map `A₂ → B₂` of a completed base change sends the image of `a ∈ A₁` to the
image of the image of `a` in `B₁`: in `B₁ ⊗_{A₁} A₂` the elements `a · 1 ⊗ 1` and `1 ⊗ a · 1`
agree. -/
private theorem algebraMap_baseChange_eq_scalar
    {A₁ : Type u₁} [CommRing A₁] {A₂ : Type u₂} [CommRing A₂] [Algebra A₁ A₂]
    {I₁ : Ideal A₁} {I₂ : Ideal A₂}
    (C : CompletedBaseChange (A₁ := A₁) (A₂ := A₂) (I₁ := I₁) (I₂ := I₂))
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (b : A₁) :
    algebraMap A₂ (C.functor.obj B₁).carrier (algebraMap A₁ A₂ b) =
      C.scalar B₁ (algebraMap A₁ B₁.carrier b) := by
  refine (C.completedTensorProductEquiv B₁).injective ?_
  rw [C.algebraMap_completedTensorProductEquiv, RingEquiv.apply_symm_apply]
  refine congrArg _ ?_
  simp only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]
  rw [Algebra.algebraMap_eq_smul_one (R := A₁) (A := B₁.carrier),
    Algebra.algebraMap_eq_smul_one (R := A₁) (A := A₂), TensorProduct.smul_tmul]

/-- One inclusion of radicals: a positive power of `I₁` extends into `I₂`. -/
private theorem exists_pos_pow_map_le_of_radical_eq
    {A₁ : Type u₁} [CommRing A₁] {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂]
    [Algebra A₁ A₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂}
    (hV : (I₁.map (algebraMap A₁ A₂)).radical = I₂.radical) :
    ∃ c : ℕ, 0 < c ∧ (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂ := by
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (Ideal.le_radical.trans hV.le) (Ideal.fg_of_isNoetherianRing _)
  refine ⟨m + 1, m.succ_pos, ?_⟩
  rw [Ideal.map_pow]
  exact (Ideal.pow_le_pow_right m.le_succ).trans hm

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
  {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂}

/-! ## The two arithmetic consequences of `V(I₁ A₂) = V(I₂)` -/

omit [IsNoetherianRing A₁] in
/-- The reverse inclusion of radicals, in the form that converts an annihilating power of `I₁`
into an annihilating power of `I₂`: for every `n` some power of `I₂` is contained in the
extension of `I₁ ^ n`.  The exponent produced is `d * n`, since
`I₂ ^ (d * n) = (I₂ ^ d) ^ n ≤ (I₁ A₂) ^ n = I₁ ^ n · A₂`. -/
private theorem exists_pow_le_map_pow_of_radical_eq
    (hV : (I₁.map (algebraMap A₁ A₂)).radical = I₂.radical) (n : ℕ) :
    ∃ d : ℕ, I₂ ^ (d * n) ≤ (I₁ ^ n).map (algebraMap A₁ A₂) := by
  obtain ⟨d, hd⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (Ideal.le_radical.trans hV.symm.le) (Ideal.fg_of_isNoetherianRing I₂)
  refine ⟨d, ?_⟩
  calc I₂ ^ (d * n) = (I₂ ^ d) ^ n := by rw [← pow_mul]
    _ ≤ (I₁.map (algebraMap A₁ A₂)) ^ n := pow_le_pow_left' hd n
    _ = (I₁ ^ n).map (algebraMap A₁ A₂) := by rw [Ideal.map_pow]

/-! ## Stacks 0GAM -/

/-- **Stacks Project, Tag 0GAM.** Rig-smoothness is preserved by completed base change along a
map of Noetherian rings whose source and target ideals define the same closed subset of the
target spectrum. -/
@[stacks 0GAM]
public theorem isRigSmooth_completedBaseChange
    (hV : (I₁.map (algebraMap A₁ A₂)).radical = I₂.radical)
    (C : CompletedBaseChange (A₁ := A₁) (A₂ := A₂) (I₁ := I₁) (I₂ := I₂))
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (hB₁ : IsRigSmooth B₁) :
    IsRigSmooth (C.functor.obj B₁) := by
  obtain ⟨P₁, n, hn⟩ := hB₁
  -- one inclusion of radicals: a positive power of `I₁` extends into `I₂` (Remark 0AL5)
  obtain ⟨c, hc, hcmap⟩ := exists_pos_pow_map_le_of_radical_eq hV
  obtain ⟨d, hpow⟩ := exists_pow_le_map_pow_of_radical_eq hV n
  let P₂ : CompletedPolynomialPresentation I₂ (C.functor.obj B₁) :=
    completedPolynomialPresentation I₂ (Ideal.fg_of_isNoetherianRing I₂) (C.functor.obj B₁)
  refine ⟨P₂, d * n, fun N ξ a ha ↦ ?_⟩
  -- Stacks 0GAL annihilates `ξ` by the image of each element of `I₁ ^ n`.
  have hkill : ((I₁ ^ n).map (algebraMap A₁ A₂)).map
      (algebraMap A₂ (C.functor.obj B₁).carrier) ≤
      Ideal.torsionOf (C.functor.obj B₁).carrier _ ξ := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    refine (congrArg (fun r : (C.functor.obj B₁).carrier ↦ r • ξ)
      (algebraMap_baseChange_eq_scalar C B₁ b)).trans ?_
    exact smul_ext_one_of_completedBaseChangeFunctor C hc hcmap B₁ P₁ P₂
      (algebraMap A₁ B₁.carrier b) (fun N₁ ξ₁ ↦ hn N₁ ξ₁ b hb) N ξ
  exact hkill (Ideal.mem_map_of_mem _ (hpow ha))

/-! ## Stacks 0GAM, the engine form -/

section Engine

variable {B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁} {B₂ : AdicFiniteTypeAlgebra.{u₂, w} A₂ I₂}
  [Algebra B₁.carrier B₂.carrier] [Algebra A₁ B₂.carrier]
  [IsScalarTower A₁ A₂ B₂.carrier] [IsScalarTower A₁ B₁.carrier B₂.carrier]

/-- **Stacks 0GAM, the engine form.**  Let `A₁ → A₂` be a map of Noetherian rings, let
`Iᵢ ⊆ Aᵢ` be ideals with `V(I₁ A₂) = V(I₂)`, let `B₁` be adically of finite type over
`(A₁, I₁)` and let `B₂` be *identified* with its completed base change
`(B₁ ⊗_{A₁} A₂)^∧_{I₂}` by `e`.  If `B₁` is rig-smooth over `(A₁, I₁)` then so is `B₂` over
`(A₂, I₂)`.

The tag sits on `Rig.isRigSmooth_completedBaseChange`, which is the form Stacks states — `B₂`
*is* the value of a base-change functor — while this one takes the identification as data, so
that it applies to an algebra which merely happens to be a completed base change.  It is the
rig-smooth counterpart of `Rig.isRigEtale_of_completedBaseChange`. -/
public theorem isRigSmooth_of_completedBaseChange
    (hV : (I₁.map (algebraMap A₁ A₂)).radical = I₂.radical)
    (e : B₂.carrier ≃+* completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
    (heA : ∀ a : A₂, e (algebraMap A₂ B₂.carrier a) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedRight A₂ B₁ a))
    (heB : ∀ b : B₁.carrier, e (algebraMap B₁.carrier B₂.carrier b) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedLeft A₂ B₁ b))
    (hB₁ : IsRigSmooth B₁) : IsRigSmooth B₂ := by
  obtain ⟨P₁, n, hn⟩ := hB₁
  -- one inclusion of radicals: a positive power of `I₁` extends into `I₂` (Remark 0AL5)
  obtain ⟨c, hc, hcmap⟩ := exists_pos_pow_map_le_of_radical_eq hV
  obtain ⟨d, hpow⟩ := exists_pow_le_map_pow_of_radical_eq hV n
  let P₂ : CompletedPolynomialPresentation I₂ B₂ :=
    completedPolynomialPresentation I₂ (Ideal.fg_of_isNoetherianRing I₂) B₂
  refine ⟨P₂, d * n, fun N ξ a ha ↦ ?_⟩
  -- Stacks 0GAL annihilates `ξ` by the image of each element of `I₁ ^ n`.
  have hkill : ((I₁ ^ n).map (algebraMap A₁ A₂)).map (algebraMap A₂ B₂.carrier) ≤
      Ideal.torsionOf B₂.carrier _ ξ := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    -- The two routes from `A₁` into `B₂` agree, so `0GAL`'s conclusion is the goal.
    have hscal : algebraMap A₂ B₂.carrier (algebraMap A₁ A₂ b) =
        algebraMap B₁.carrier B₂.carrier (algebraMap A₁ B₁.carrier b) := by
      rw [← IsScalarTower.algebraMap_apply A₁ A₂ B₂.carrier b,
        IsScalarTower.algebraMap_apply A₁ B₁.carrier B₂.carrier b]
    refine (congrArg (fun r : B₂.carrier ↦ r • ξ) hscal).trans ?_
    exact smul_ext_one_of_completedBaseChange hc hcmap e heA heB P₁ P₂
      (algebraMap A₁ B₁.carrier b) (fun N₁ ξ₁ ↦ hn N₁ ξ₁ b hb) N ξ
  exact hkill (Ideal.mem_map_of_mem _ (hpow ha))

end Engine

end Rig

end
