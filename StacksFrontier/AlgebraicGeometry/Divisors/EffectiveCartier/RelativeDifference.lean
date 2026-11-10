module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Regular.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
public import StacksFrontier.RingTheory.Flat.ShortExact

/-!
# The difference of two relative effective Cartier divisors

Let `f : X ⟶ S` be a morphism of schemes and let `D₁ ⊆ D₂ ⊆ X` be relative effective Cartier
divisors over `S`, so that `D₂ = D₁ + E` for an effective Cartier divisor `E` on `X` — in the
ideal-sheaf presentation, `I(D₂) = I(D₁) * I(E)`. This file proves
[Stacks, Tag 0B8V](https://stacks.math.columbia.edu/tag/0B8V): `E` is again *relative* over `S`,
that is, its structure morphism `E ⟶ S` is flat.

## The argument

Being relative adds flatness to being an effective Cartier divisor, and flatness is local on
source and target, so it suffices to check it on an affine chart: an affine open `V ⊆ S` and an
affine open `U ⊆ f⁻¹(V)` meeting the point of `E` under consideration. On such a chart, with
`A = Γ(S, V)` and `B = Γ(X, U)`, flatness of `D ⟶ S` over the chart is flatness of
`A → B / I(D)(U)` (`Stacks.Divisors.flat_quotient_map_of_flat_subscheme`, and its converse
`Stacks.Divisors.flat_appLE_of_flat_quotient_map`).

Tag 01WS (`Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal`) shrinks the chart further
so that `I(D₁)(U) = (a)` for a nonzerodivisor `a ∈ B`; off the support of `D₁` the ideal is the
unit ideal and `a = 1` does the same job. The question then becomes purely ring-theoretic: given
`A → B` with `B / (a)·J` and `B / (a)` flat over `A` and `a` a nonzerodivisor, is `B / J` flat?
It is, because multiplication by `a` fits `B/J` and `B/(a)` into a short exact sequence
`0 → B/J → B/(a)J → B/(a) → 0` of `A`-modules — injectivity of the first map is exactly the
regularity of `a` — and `Stacks.RingTheory.flat_of_flat_of_flat_quotient` concludes.

## Main results

* `Stacks.Divisors.flat_quotient_cancel_mul_of_isRegular`: the ring-theoretic cancellation.
* `Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_mul_eq`: **Tag 0B8V**.

## References

* [Stacks Project, Tag 0B8V](https://stacks.math.columbia.edu/tag/0B8V)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-! ### Flatness of a closed subscheme over an affine chart -/

/-- The preimage of `U` under a closed subscheme inclusion lies over `V` if `U` lies over `V`. -/
private theorem preimage_subschemeι_le {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
    {U : X.Opens} {V : S.Opens} (hUV : U ≤ f ⁻¹ᵁ V) :
    I.subschemeι ⁻¹ᵁ U ≤ (I.subschemeι ≫ f) ⁻¹ᵁ V := by
  change (I.subschemeι.base ⁻¹' (U : Set X)) ⊆ I.subschemeι.base ⁻¹' (f.base ⁻¹' (V : Set S))
  exact Set.preimage_mono hUV

/-- The ring map of a closed subscheme over a chart is the quotient map composed with an
isomorphism. -/
private theorem hom_appLE_subschemeι_comp {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)) :
    ((I.subschemeι ≫ f).appLE V (I.subschemeι ⁻¹ᵁ (U : X.Opens))
      (preimage_subschemeι_le f I hUV)).hom =
      ((I.subschemeObjIso U).inv.hom).comp
        ((Ideal.Quotient.mk (I.ideal U)).comp (f.appLE V U hUV).hom) := by
  have happ : (I.subschemeι ≫ f).appLE V (I.subschemeι ⁻¹ᵁ (U : X.Opens))
      (preimage_subschemeι_le f I hUV) = f.appLE V U hUV ≫ I.subschemeι.app U.1 := by
    trans f.appLE V U hUV ≫ I.subschemeι.appLE U.1 (I.subschemeι ⁻¹ᵁ (U : X.Opens)) le_rfl
    · exact (Scheme.Hom.appLE_comp_appLE I.subschemeι f V U _ hUV le_rfl).symm
    · congr 1
      simpa using Scheme.Hom.appLE_eq_app (f := I.subschemeι) (U := U.1)
  rw [happ, Scheme.IdealSheafData.subschemeι_app]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc]

/-- **Flatness of the closed subscheme, read on an affine chart.** If the structure morphism of
the closed subscheme cut out by `I` is flat over `S`, then on an affine open `U ⊆ f⁻¹(V)` the
induced ring map `Γ(S, V) → Γ(X, U) ⧸ I.ideal U` is flat. -/
theorem flat_quotient_map_of_flat_subscheme {X S : Scheme.{u}}
    (f : X ⟶ S) (I : X.IdealSheafData) (hI : Flat (I.subschemeι ≫ f))
    (U : X.affineOpens) (V : S.affineOpens) (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)) :
    (Ideal.Quotient.mk (I.ideal U)).comp (f.appLE V U hUV).hom |>.Flat := by
  have hflat := Flat.flat_appLE (I.subschemeι ≫ f) V.2 (U.2.preimage I.subschemeι)
    (preimage_subschemeι_le f I hUV)
  rw [hom_appLE_subschemeι_comp f I U V hUV] at hflat
  exact (RingHom.Flat.comp_iff_of_bijective_left
      (ConcreteCategory.bijective_of_isIso (I.subschemeObjIso U).inv)).mp hflat

/-- **The converse chart statement.** Flatness of `Γ(S, V) → Γ(X, U) ⧸ I.ideal U` is flatness of
the structure morphism of the closed subscheme over the chart. -/
theorem flat_appLE_of_flat_quotient_map {X S : Scheme.{u}}
    (f : X ⟶ S) (I : X.IdealSheafData)
    (U : X.affineOpens) (V : S.affineOpens)
    (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens))
    (hflat : (Ideal.Quotient.mk (I.ideal U)).comp (f.appLE V U hUV).hom |>.Flat) :
    ((I.subschemeι ≫ f).appLE V (I.subschemeι ⁻¹ᵁ (U : X.Opens))
      (by
        change (I.subschemeι.base ⁻¹' (U : Set X)) ⊆
          I.subschemeι.base ⁻¹' (f.base ⁻¹' (V : Set S))
        exact Set.preimage_mono hUV)).hom.Flat := by
  rw [hom_appLE_subschemeι_comp f I U V hUV]
  exact RingHom.Flat.comp hflat
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (I.subschemeObjIso U).inv))

/-! ### Restricting a local generator to a basic open -/

/-- A nonzerodivisor of `Γ(X, U)` stays a nonzerodivisor after restriction to a basic open of the
affine open `U`, because that restriction is a localization. -/
theorem isRegular_res_basicOpen {X : Scheme.{u}} {U W : X.affineOpens}
    (hUW : (W : X.Opens) ≤ (U : X.Opens)) (g f : Γ(X, U))
    (e : W.1 = X.basicOpen g) (hf : IsRegular f) :
    IsRegular ((X.presheaf.map (homOfLE hUW).op).hom f) := by
  let _ : Algebra (Γ(X, U)) (Γ(X, W)) :=
    (X.presheaf.map (homOfLE hUW).op).hom.toAlgebra
  let _ : IsLocalization.Away g (Γ(X, W)) :=
    U.2.isLocalization_of_eq_basicOpen g (homOfLE hUW) e
  have hseq : RingTheory.Sequence.IsWeaklyRegular (Γ(X, W))
      [algebraMap (Γ(X, U)) (Γ(X, W)) f] :=
    ((RingTheory.Sequence.isWeaklyRegular_singleton_iff (Γ(X, U)) f).2
      hf.isSMulRegular).of_isLocalization (Γ(X, W)) (.powers g)
  have hsmul : IsSMulRegular (Γ(X, W)) ((X.presheaf.map (homOfLE hUW).op).hom f) :=
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).1 hseq
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply hsmul
    simpa [Algebra.smul_def] using hab
  · intro a b hab
    apply hsmul
    simpa [Algebra.smul_def, mul_comm] using hab

/-- On a smaller affine open, the ideal of a closed subscheme charted by a principal ideal is
generated by the restriction of the generator. -/
theorem ideal_eq_span_res_of_chart {X : Scheme.{u}} (I : X.IdealSheafData)
    {U W : X.affineOpens} (hWU : W ≤ U) (f : Γ(X, U))
    (e : pullback I.subschemeι U.1.ι ≅ Spec (.of (Γ(X, U.1) ⧸ Ideal.span {f})))
    (he : pullback.snd I.subschemeι U.1.ι ≫ U.2.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) :
    I.ideal W = Ideal.span {((X.presheaf.map (homOfLE hWU).op).hom f)} := by
  rw [← I.map_ideal hWU, ideal_eq_quotient_of_chart I U.1 U.2 (Ideal.span {f}) e he,
    Ideal.map_span]
  simp

/-- **Cancelling a principal factor from a flat quotient.** Let `φ : A → B` be a ring
homomorphism, `a ∈ B` a nonzerodivisor and `J ⊆ B` an ideal. If `B ⧸ (a) * J` and `B ⧸ (a)` are
flat over `A`, then so is `B ⧸ J`: multiplication by `a` presents `B ⧸ J` as the kernel of
`B ⧸ (a) * J ↠ B ⧸ (a)`, and flatness of a module follows from flatness of the two others in a
short exact sequence of this shape. -/
theorem flat_quotient_cancel_mul_of_isRegular {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : B) (J : Ideal B) (ha : IsRegular a)
    (hK : ((Ideal.Quotient.mk (Ideal.span {a} * J)).comp φ).Flat)
    (hP : ((Ideal.Quotient.mk (Ideal.span {a})).comp φ).Flat) :
    ((Ideal.Quotient.mk J).comp φ).Flat := by
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
      change K.mkQ (a * b) = 0
      apply (Submodule.Quotient.eq K).2
      simpa [K, P, mul_comm] using Ideal.mul_mem_mul (Ideal.mem_span_singleton_self a) hb)
  let GB : (B ⧸ K) →ₗ[B] (B ⧸ P) := K.factor (show K ≤ P from Ideal.mul_le_left)
  let F : (B ⧸ J) →ₗ[A] (B ⧸ K) := FB.restrictScalars A
  let G : (B ⧸ K) →ₗ[A] (B ⧸ P) := GB.restrictScalars A
  have hF_apply (x : B) : F (J.mkQ x) = K.mkQ (a * x) := rfl
  have hG_apply (x : B) : G (K.mkQ x) = P.mkQ x := rfl
  have hF : Function.Injective F := by
    intro x y hxy
    obtain ⟨b, rfl⟩ := J.mkQ_surjective x
    obtain ⟨c, rfl⟩ := J.mkQ_surjective y
    apply (Submodule.Quotient.eq J).2
    have hbc : a * b - a * c ∈ K := (Submodule.Quotient.eq K).1 hxy
    have hab : a * (b - c) ∈ J * P := by
      rw [mul_comm J]
      simpa [mul_sub] using hbc
    obtain ⟨d, hd, hda⟩ := Ideal.mem_mul_span_singleton.1 hab
    have hdb : d = b - c := ha.right (by simpa [mul_comm] using hda)
    simpa [hdb] using hd
  have hFG : Function.Exact F G := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro x hx
      obtain ⟨b, rfl⟩ := K.mkQ_surjective x
      have hbp : P.mkQ b = P.mkQ 0 := by
        simpa using (hG_apply b).symm.trans (LinearMap.mem_ker.mp hx)
      have hb : b ∈ P := by simpa using (Submodule.Quotient.eq P).1 hbp
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
      refine ⟨J.mkQ c, ?_⟩
      rw [hF_apply]
      apply (Submodule.Quotient.eq K).2
      rw [hc]
      simp [P, K, mul_comm]
    · refine LinearMap.range_le_ker_iff.mpr (LinearMap.ext fun x => ?_)
      obtain ⟨b, rfl⟩ := J.mkQ_surjective x
      change G (F (J.mkQ b)) = 0
      rw [hF_apply, hG_apply]
      exact (Submodule.Quotient.eq P).2 (by
        simpa using P.mul_mem_right b (Ideal.mem_span_singleton_self a))
  have hG : Function.Surjective G := fun x => by
    obtain ⟨b, rfl⟩ := P.mkQ_surjective x
    exact ⟨K.mkQ b, hG_apply b⟩
  let _ : Module.Flat A (B ⧸ K) := hK
  let _ : Module.Flat A (B ⧸ P) := hP
  exact flat_of_flat_of_flat_quotient F G hF hFG hG

/-! ### Tag 0B8V -/

/-- **The difference of two relative effective Cartier divisors is relative.** If the closed
subscheme cut out by `I` is an effective Cartier divisor flat over `S`, and so is the one cut out
by `I * E`, then the one cut out by `E` is flat over `S`. -/
theorem flat_of_mul_eq {X S : Scheme.{u}} (f : X ⟶ S) (I E : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I)
    (hflatI : Flat (I.subschemeι ≫ f))
    (hflatIE : Flat ((I * E).subschemeι ≫ f)) : Flat (E.subschemeι ≫ f) := by
  let g : E.subscheme ⟶ S := E.subschemeι ≫ f
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  have : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat) (Q := RingHom.Flat)
  have : MorphismProperty.RespectsRight (@Flat : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.Respects (@Flat : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).toRespectsRight
  refine (IsZariskiLocalAtSource.iff_exists_resLE (P := @Flat)).2 fun z => ?_
  let x : X := E.subschemeι z
  let V : S.affineOpens :=
    ⟨(S.affineCover.f (S.affineCover.idx (f x))).opensRange,
      isAffineOpen_opensRange (S.affineCover.f (S.affineCover.idx (f x)))⟩
  have hxV : f x ∈ (V : S.Opens) := S.affineCover.covers (f x)
  have hxPreV : x ∈ f ⁻¹ᵁ (V : S.Opens) := hxV
  have hlocal : ∃ (U : X.affineOpens) (a : Γ(X, U)),
      x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens) ∧
        IsRegular a ∧ I.ideal U = Ideal.span {a} := by
    by_cases hxI : x ∈ I.supportSet
    · obtain ⟨U₀open, hU₀open, hxU₀, a₀, ha₀, eI, heI⟩ :=
        (isEffectiveCartierDivisor_iff_affineLocal I).1 hI x hxI
      let U₀ : X.affineOpens := ⟨U₀open, hU₀open⟩
      obtain ⟨b, hb, hxb⟩ := U₀.2.exists_basicOpen_le ⟨x, hxPreV⟩ hxU₀
      let U : X.affineOpens := X.affineBasicOpen b
      have hUU₀ : U ≤ U₀ := X.affineBasicOpen_le b
      refine ⟨U, (X.presheaf.map (homOfLE hUU₀).op).hom a₀, ?_, ?_, ?_, ?_⟩
      · simpa [U] using hxb
      · simpa [U] using hb
      · exact isRegular_res_basicOpen hUU₀ b a₀ rfl ha₀
      · exact ideal_eq_span_res_of_chart I hUU₀ a₀ eI heI
    · obtain ⟨-, ⟨U₀open, hU₀open, rfl⟩, hxU₀, hU₀V⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hxPreV
          (f ⁻¹ᵁ (V : S.Opens)).isOpen
      let U₀ : X.affineOpens := ⟨U₀open, hU₀open⟩
      obtain ⟨b, hxb, htop⟩ := exists_basicOpen_ideal_eq_top I U₀ x hxU₀ hxI
      let U : X.affineOpens := X.affineBasicOpen b
      refine ⟨U, 1, ?_, ?_, isRegular_one, ?_⟩
      · simpa [U] using hxb
      · exact le_trans (X.affineBasicOpen_le b) hU₀V
      · simp [U, htop]
  obtain ⟨U, a, hxU, hUV, ha, hIspan⟩ := hlocal
  have hIflat : (Ideal.Quotient.mk (Ideal.span {a})).comp
      (f.appLE V U hUV).hom |>.Flat :=
    hIspan ▸ flat_quotient_map_of_flat_subscheme f I hflatI U V hUV
  have hEflat : (Ideal.Quotient.mk (E.ideal U)).comp
      (f.appLE V U hUV).hom |>.Flat := by
    have hprod : (I * E).ideal U = Ideal.span {a} * E.ideal U := by
      simp [Scheme.IdealSheafData.ideal_mul, hIspan]
    exact flat_quotient_cancel_mul_of_isRegular (f.appLE V U hUV).hom a (E.ideal U)
      ha (hprod ▸ flat_quotient_map_of_flat_subscheme f (I * E) hflatIE U V hUV) hIflat
  let T : E.subscheme.Opens := E.subschemeι ⁻¹ᵁ (U : X.Opens)
  have hTV : T ≤ g ⁻¹ᵁ (V : S.Opens) := preimage_subschemeι_le f E hUV
  refine ⟨V.1, T, hxU, hTV, ?_⟩
  have _ : IsAffine T.toScheme := U.2.preimage E.subschemeι
  have _ : IsAffine V.1.toScheme := V.2
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  exact (RingHom.Flat.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso g V.1 T hTV)).mpr (flat_appLE_of_flat_quotient_map f E U V hUV hEflat)

/-- **Stacks Project, Tag 0B8V.** An effective Cartier divisor which is the difference of two
relative effective Cartier divisors is itself relative. -/
@[stacks 0B8V]
theorem isRelativeEffectiveCartierDivisor_of_mul_eq
    {X S : Scheme.{u}} (f : X ⟶ S) (D₁ D₂ E : X.IdealSheafData)
    (hD₁ : IsRelativeEffectiveCartierDivisor f D₁)
    (hD₂ : IsRelativeEffectiveCartierDivisor f D₂)
    (hE : IsEffectiveCartierDivisor E)
    (h : D₂ = D₁ * E) :
    IsRelativeEffectiveCartierDivisor f E :=
  ⟨hE, flat_of_mul_eq f D₁ E hD₁.1 hD₁.2 (h ▸ hD₂.2)⟩

end Stacks.Divisors

end
