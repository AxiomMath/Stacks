module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Sum
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RelativeDifference

/-!
# The sum of two relative effective Cartier divisors

Let `f : X ⟶ S` be a morphism of schemes.  The sum `D₁ + D₂` of two closed subschemes of `X`,
presented by their ideal sheaves, is cut out by the product `ℐ_{D₁} · ℐ_{D₂}`.  If both summands
are relative effective Cartier divisors over `S`, so is the sum.

## The argument

Being an effective Cartier divisor is preserved by the sum, which is Tag 01WU.  What is left is
flatness of `D₁ + D₂ ⟶ S`, and flatness is local on source and target, so it may be checked on
an affine chart: an affine open `V ⊆ S` and an affine open `U ⊆ f⁻¹(V)` around the point of the
sum under consideration.  Writing `A = Γ(S, V)` and `B = Γ(X, U)`, flatness over the chart is
flatness of `A → B ⧸ ℐ(U)`.

Tag 01WS shrinks the chart so that `ℐ_{D₁}(U) = (a)` for a nonzerodivisor `a ∈ B`; off the
support of `D₁` the ideal is the unit ideal and `a = 1` serves.  The remaining question is
purely ring-theoretic: given `A → B` with `B ⧸ (a)` and `B ⧸ J` flat over `A` and `a` a
nonzerodivisor, `B ⧸ (a)·J` is flat, because multiplication by `a` fits the three quotients
into a short exact sequence `0 → B/J → B/(a)J → B/(a) → 0` of `A`-modules.

## Main results

* `AlgebraicGeometry.exists_affineOpen_chart_of_isEffectiveCartierDivisor`: the principal chart
  around an arbitrary point, over a prescribed affine open of the base.
* `AlgebraicGeometry.flat_quotient_mul_of_isRegular`: the ring-theoretic step.
* `AlgebraicGeometry.isRelativeEffectiveCartierDivisor_mul`: **Stacks Tag 0B8U.**

## Implementation notes

The ring-theoretic step is the exact converse of
`Stacks.Divisors.flat_quotient_cancel_mul_of_isRegular`, which cancels the principal factor
instead of introducing it;  both read the same short exact sequence, this one concluding
flatness of the middle term rather than of the kernel.

## References

* [Stacks Project, Tag 0B8U](https://stacks.math.columbia.edu/tag/0B8U)
* [Stacks Project, Tag 01WU](https://stacks.math.columbia.edu/tag/01WU)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- **A principal chart for an effective Cartier divisor around an arbitrary point.**  Given an
effective Cartier divisor `I` on `X`, a point `x` of `X` and an affine open `V` of `S` whose
preimage contains `x`, there is an affine open `U ∋ x` inside `f⁻¹(V)` on which `I` is generated
by a single nonzerodivisor.  On the support of `I` this is Tag 01WS; off it the ideal is already
the unit ideal on a small enough basic open, and `1` is the generator. -/
theorem exists_affineOpen_chart_of_isEffectiveCartierDivisor {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I) (x : X) (V : S.affineOpens)
    (hxV : x ∈ f ⁻¹ᵁ (V : S.Opens)) :
    ∃ (U : X.affineOpens) (a : Γ(X, U)),
      x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens) ∧
        IsRegular a ∧ I.ideal U = Ideal.span {a} := by
  by_cases hxI : x ∈ I.supportSet
  · obtain ⟨U₀open, hU₀open, hxU₀, a₀, ha₀, eI, heI⟩ :=
      (isEffectiveCartierDivisor_iff_affineLocal I).1 hI x hxI
    let U₀ : X.affineOpens := ⟨U₀open, hU₀open⟩
    obtain ⟨b, hb, hxb⟩ := U₀.2.exists_basicOpen_le ⟨x, hxV⟩ hxU₀
    let U : X.affineOpens := X.affineBasicOpen b
    have hUU₀ : U ≤ U₀ := X.affineBasicOpen_le b
    refine ⟨U, (X.presheaf.map (homOfLE hUU₀).op).hom a₀, ?_, ?_, ?_, ?_⟩
    · simpa [U] using hxb
    · simpa [U] using hb
    · exact isRegular_res_basicOpen hUU₀ b a₀ rfl ha₀
    · exact ideal_eq_span_res_of_chart I hUU₀ a₀ eI heI
  · obtain ⟨-, ⟨U₀open, hU₀open, rfl⟩, hxU₀, hU₀V⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ (V : S.Opens)).isOpen
    let U₀ : X.affineOpens := ⟨U₀open, hU₀open⟩
    obtain ⟨b, hxb, htop⟩ := exists_basicOpen_ideal_eq_top I U₀ x hxU₀ hxI
    let U : X.affineOpens := X.affineBasicOpen b
    refine ⟨U, 1, ?_, ?_, isRegular_one, ?_⟩
    · simpa [U] using hxb
    · exact le_trans (X.affineBasicOpen_le b) hU₀V
    · simp [U, htop]

/-- Cancelling a nonzerodivisor `a` from `a * b ∈ (a) * J` gives `b ∈ J`. -/
private theorem mem_of_mul_mem_span_singleton_mul {B : Type*} [CommRing B] {a b : B} {J : Ideal B}
    (ha : IsRegular a) (h : a * b ∈ Ideal.span {a} * J) : b ∈ J := by
  obtain ⟨d, hd, hdeq⟩ :=
    Ideal.mem_mul_span_singleton.1 (by simpa [mul_comm] using h : a * b ∈ J * Ideal.span {a})
  obtain rfl : d = b := ha.right (by simpa [mul_comm] using hdeq)
  exact hd

/-- **Multiplying a flat quotient by a principal factor.**  Let `φ : A → B` be a ring
homomorphism, `a ∈ B` a nonzerodivisor and `J ⊆ B` an ideal.  If `B ⧸ J` and `B ⧸ (a)` are flat
over `A`, then so is `B ⧸ (a) * J`:  multiplication by `a` presents `B ⧸ J` as the kernel of
`B ⧸ (a) * J ↠ B ⧸ (a)`, and flatness of the middle term of a short exact sequence follows from
flatness of the two outer ones. -/
theorem flat_quotient_mul_of_isRegular {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : B) (J : Ideal B) (ha : IsRegular a)
    (hJ : ((Ideal.Quotient.mk J).comp φ).Flat)
    (hP : ((Ideal.Quotient.mk (Ideal.span {a})).comp φ).Flat) :
    ((Ideal.Quotient.mk (Ideal.span {a} * J)).comp φ).Flat := by
  let P : Ideal B := Ideal.span {a}
  let K : Ideal B := P * J
  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra A (B ⧸ J) := ((Ideal.Quotient.mk J).comp φ).toAlgebra
  let _ : Algebra A (B ⧸ P) := ((Ideal.Quotient.mk P).comp φ).toAlgebra
  let _ : Algebra A (B ⧸ K) := ((Ideal.Quotient.mk K).comp φ).toAlgebra
  let FB : (B ⧸ J) →ₗ[B] (B ⧸ K) :=
    J.liftQ (K.mkQ.comp (LinearMap.mulLeft B a)) (by
      intro b hb
      apply LinearMap.mem_ker.mpr
      show K.mkQ (a * b) = 0
      apply (Submodule.Quotient.eq K).2
      simpa [K, P] using Ideal.mul_mem_mul (Ideal.mem_span_singleton_self a) hb)
  let GB : (B ⧸ K) →ₗ[B] (B ⧸ P) := K.factor (show K ≤ P from Ideal.mul_le_left)
  let F : (B ⧸ J) →ₗ[A] (B ⧸ K) := FB.restrictScalars A
  let G : (B ⧸ K) →ₗ[A] (B ⧸ P) := GB.restrictScalars A
  have hF_apply (x : B) : F (J.mkQ x) = K.mkQ (a * x) := rfl
  have hG_apply (x : B) : G (K.mkQ x) = P.mkQ x := rfl
  have hF : Function.Injective F := by
    intro x y hxy
    obtain ⟨b, rfl⟩ := J.mkQ_surjective x
    obtain ⟨c, rfl⟩ := J.mkQ_surjective y
    have hbc : a * b - a * c ∈ K :=
      (Submodule.Quotient.eq K).1 ((hF_apply b).symm.trans (hxy.trans (hF_apply c)))
    exact (Submodule.Quotient.eq J).2
      (mem_of_mul_mem_span_singleton_mul ha (by simpa [mul_sub] using hbc))
  have hFG : Function.Exact F G := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro x hx
      obtain ⟨b, rfl⟩ := K.mkQ_surjective x
      have hbp : P.mkQ b = P.mkQ 0 := by
        rw [← hG_apply b]
        simpa using LinearMap.mem_ker.mp hx
      have hb : b ∈ P := by simpa using (Submodule.Quotient.eq P).1 hbp
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
      refine ⟨J.mkQ c, ?_⟩
      rw [hF_apply, hc]
    · rintro _ ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := J.mkQ_surjective x
      rw [LinearMap.mem_ker, hF_apply, hG_apply]
      exact (Submodule.Quotient.eq P).2
        (by simpa using P.mul_mem_right b (Ideal.mem_span_singleton_self a))
  have hG : Function.Surjective G := fun x => by
    obtain ⟨b, rfl⟩ := P.mkQ_surjective x
    exact ⟨K.mkQ b, hG_apply b⟩
  let _ : Module.Flat A (B ⧸ J) := hJ
  let _ : Module.Flat A (B ⧸ P) := hP
  exact flat_of_flat_of_flat F G hF hFG hG

/-- **The sum of two closed subschemes flat over the base is flat over the base**, provided the
first summand is an effective Cartier divisor. -/
theorem flat_mul_of_isEffectiveCartierDivisor {X S : Scheme.{u}} (f : X ⟶ S)
    (I J : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I)
    (hflatI : Flat (I.subschemeι ≫ f)) (hflatJ : Flat (J.subschemeι ≫ f)) :
    Flat ((I * J).subschemeι ≫ f) := by
  let K : X.IdealSheafData := I * J
  let g : K.subscheme ⟶ S := K.subschemeι ≫ f
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  have : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat) (Q := RingHom.Flat)
  have : MorphismProperty.RespectsRight (@Flat : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.Respects (@Flat : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).toRespectsRight
  refine (IsZariskiLocalAtSource.iff_exists_resLE (P := @Flat)).2 fun z => ?_
  let x : X := K.subschemeι z
  let V : S.affineOpens :=
    ⟨(S.affineCover.f (S.affineCover.idx (f x))).opensRange,
      isAffineOpen_opensRange (S.affineCover.f (S.affineCover.idx (f x)))⟩
  obtain ⟨U, a, hxU, hUV, ha, hIspan⟩ :=
    exists_affineOpen_chart_of_isEffectiveCartierDivisor f I hI x V (S.affineCover.covers (f x))
  have hIflat : (Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE V U hUV).hom |>.Flat := by
    rw [← hIspan]
    exact flat_quotient_map_of_flat_subscheme f I hflatI U V hUV
  have hKflat : (Ideal.Quotient.mk (K.ideal U)).comp (f.appLE V U hUV).hom |>.Flat := by
    rw [show K.ideal U = Ideal.span {a} * J.ideal U by
      simp [K, Scheme.IdealSheafData.ideal_mul, hIspan]]
    exact flat_quotient_mul_of_isRegular (f.appLE V U hUV).hom a (J.ideal U) ha
      (flat_quotient_map_of_flat_subscheme f J hflatJ U V hUV) hIflat
  let T : K.subscheme.Opens := K.subschemeι ⁻¹ᵁ (U : X.Opens)
  have hTV : T ≤ g ⁻¹ᵁ (V : S.Opens) := by
    show K.subschemeι.base ⁻¹' (U : Set X) ⊆ K.subschemeι.base ⁻¹' (f.base ⁻¹' (V : Set S))
    exact Set.preimage_mono hUV
  refine ⟨V.1, T, hxU, hTV, ?_⟩
  let _ : IsAffine T.toScheme := U.2.preimage K.subschemeι
  let _ : IsAffine V.1.toScheme := V.2
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  exact (RingHom.Flat.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso g V.1 T hTV)).mpr (flat_appLE_of_flat_quotient_map f K U V hUV hKflat)

/-- **Stacks Project, Tag 0B8U.**  The sum of two relative effective Cartier divisors on `X`
over `S` is a relative effective Cartier divisor over `S`. -/
@[stacks 0B8U]
theorem isRelativeEffectiveCartierDivisor_mul {X S : Scheme.{u}} (f : X ⟶ S)
    (I J : X.IdealSheafData)
    (hI : IsRelativeEffectiveCartierDivisor f I)
    (hJ : IsRelativeEffectiveCartierDivisor f J) :
    IsRelativeEffectiveCartierDivisor f (I * J) :=
  ⟨isEffectiveCartierDivisor_mul I J hI.1 hJ.1,
    flat_mul_of_isEffectiveCartierDivisor f I J hI.1 hI.2 hJ.2⟩

end AlgebraicGeometry

end
