module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RelativeDifference
import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FibrePrincipalDictionary
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.SpreadingOut

/-!
# Base change of a relative effective Cartier divisor

Let `f : X ⟶ S` be a morphism of schemes and `D ⊆ X` an effective Cartier divisor whose
structure morphism `D ⟶ S` is flat.  Then for every `g : S' ⟶ S` the inverse image of `D` in
`X' = S' ×_S X` is again an effective Cartier divisor.

## Main results

* `AlgebraicGeometry.isRegular_includeRight_of_flat_quotient`: a nonzerodivisor `a ∈ B` with
  `B ⧸ (a)` flat over `A` stays a nonzerodivisor in `A' ⊗_A B`.
* `AlgebraicGeometry.ker_algebraMap_eq_map_ker_of_pushout` and
  `AlgebraicGeometry.ker_eq_map_ker_of_pushout`: the kernel of a pushout of a surjection.
* `AlgebraicGeometry.isEffectiveCartierDivisor_comap_pullback`: a relative effective Cartier
  divisor stays effective Cartier under arbitrary base change.

## References

* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Divisors Stacks.RingTheory.SpreadingOut
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The nonzerodivisor of the divisor stays one after base change.**  If `a ∈ B` is a
nonzerodivisor and `B ⧸ (a)` is flat over `A`, then the image of `a` in `A' ⊗_A B` is a
nonzerodivisor for every `A`-algebra `A'`. -/
theorem isRegular_includeRight_of_flat_quotient
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    (b : B) (hb : IsRegular b) [Module.Flat A (B ⧸ Ideal.span {b})] :
    IsRegular ((Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B) b) := by
  have hsmul := isSMulRegular_tmul_of_flat_quotient (A := A) (B := B) b hb.left
    (inferInstance : Module.Flat A (B ⧸ Ideal.span {b})) A'
  have hleft : IsLeftRegular
      ((Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B) b) := by
    simpa only [IsSMulRegular, IsLeftRegular, smul_eq_mul,
      Algebra.TensorProduct.includeRight_apply] using hsmul
  exact (Commute.isRegular_iff fun x => mul_comm _ x).2 hleft

/-- **The kernel of a pushout of a surjection.**  If `P = B ⊗_R C` with `R → C` surjective, the
kernel of `B → P` is the extension of the kernel of `R → C`. -/
theorem ker_algebraMap_eq_map_ker_of_pushout
    (R B C P : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R B] [Algebra R C] [Algebra B P] [Algebra C P] [Algebra R P]
    [IsScalarTower R B P] [IsScalarTower R C P] [Algebra.IsPushout R B C P]
    (hC : Function.Surjective (algebraMap R C)) :
    RingHom.ker (algebraMap B P) =
      (RingHom.ker (algebraMap R C)).map (algebraMap R B) := by
  let e : B ⊗[R] C ≃ₐ[B] P := Algebra.IsPushout.equiv R B C P
  have h1 : algebraMap B P = e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := B) (B := C)).toRingHom := by
    ext b
    simp [e]
  rw [h1, RingHom.ker_comp_of_injective _ e.toRingEquiv.injective]
  let g : R →ₐ[R] C := Algebra.ofId R C
  have h2 :
      (Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := B) (B := C)).toRingHom =
        (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom.comp
          (Algebra.TensorProduct.includeLeft
            (R := R) (S := R) (A := B) (B := R)).toRingHom := by
    ext b
    simp [g]
  have h3 : RingHom.ker
      (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom =
      (RingHom.ker (algebraMap R C)).map
        (Algebra.TensorProduct.includeRight
          (R := R) (A := B) (B := R)).toRingHom := by
    have h := Algebra.TensorProduct.lTensor_ker (A := B) g hC
    simp only [g] at h
    exact h
  rw [h2, ← RingHom.comap_ker, h3]
  let r : B ⊗[R] R ≃ₐ[R] B := Algebra.TensorProduct.rid R R B
  have h4 : (Algebra.TensorProduct.includeLeft
      (R := R) (S := R) (A := B) (B := R)).toRingHom =
      (r.toRingEquiv.symm : B →+* B ⊗[R] R) := by
    ext b
    apply r.toRingEquiv.injective
    simp [r]
  have h5 : algebraMap R B = (r.toRingEquiv : B ⊗[R] R →+* B).comp
      (Algebra.TensorProduct.includeRight
        (R := R) (A := B) (B := R)).toRingHom := by
    ext x
    simp [r, Algebra.smul_def]
  rw [h4, h5, ← Ideal.map_map, Ideal.comap_coe, Ideal.map_coe, Ideal.comap_symm]

/-- **The kernel of a pushout square of commutative rings**, in the categorical spelling. -/
theorem ker_eq_map_ker_of_pushout {R B C P : CommRingCat.{u}}
    {f : R ⟶ B} {g : R ⟶ C} {inl : B ⟶ P} {inr : C ⟶ P}
    (h : IsPushout f g inl inr) (hg : Function.Surjective g.hom) :
    RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have hw : inl.hom.comp f.hom = inr.hom.comp g.hom := by
    simpa only [CommRingCat.hom_comp] using
      congrArg (fun k : R ⟶ P => k.hom) h.w
  let _ : IsScalarTower R C P := .of_algebraMap_eq' hw
  let _ : Algebra.IsPushout R B C P := CommRingCat.isPushout_iff_isPushout.mp h
  exact ker_algebraMap_eq_map_ker_of_pushout R B C P hg

/-- A relative effective Cartier divisor stays effective Cartier under arbitrary base
change. -/
@[stacks 056Q, ega "IV 21.15.9" "partial"]
theorem isEffectiveCartierDivisor_comap_pullback {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I)
    [Flat (I.subschemeι ≫ f)] :
    IsEffectiveCartierDivisor
      (I.comap (pullback.snd g f)) := by
  classical
  let p : pullback g f ⟶ X := pullback.snd g f
  let J := I.comap p
  apply (isEffectiveCartierDivisor_iff_affineLocal J).2
  intro x hx
  obtain ⟨z', hz'⟩ : x ∈ Set.range J.subschemeι := by
    simpa only [Scheme.IdealSheafData.range_subschemeι] using
      show x ∈ (J.support : Set _) from J.mem_supportSet_iff_mem_support.mpr hx
  let z : I.subscheme :=
    pullback.snd p I.subschemeι ((I.comapIso p).hom z')
  have hfst : J.subschemeι z' =
      pullback.fst p I.subschemeι ((I.comapIso p).hom z') :=
    (congrArg (fun k => k z') (Scheme.IdealSheafData.comapIso_hom_fst (I := I) p)).symm
  have hpb : p (pullback.fst p I.subschemeι ((I.comapIso p).hom z')) =
      I.subschemeι z := by
    have hh := congrArg (fun k => k ((I.comapIso p).hom z'))
      (pullback.condition (f := p) (g := I.subschemeι))
    simpa [z] using hh
  have hzx : p x = I.subschemeι z := by
    calc
      p x = p (J.subschemeι z') := congrArg p hz'.symm
      _ = p (pullback.fst p I.subschemeι ((I.comapIso p).hom z')) := congrArg p hfst
      _ = I.subschemeι z := hpb
  have hxI_support : p x ∈ (I.support : Set _) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, hzx.symm⟩
  have hxI : p x ∈ I.supportSet := I.mem_supportSet_iff_mem_support.mpr hxI_support
  obtain ⟨U₀, hU₀, hxU₀, a, ha, e, he⟩ :=
    (isEffectiveCartierDivisor_iff_affineLocal I).1 hI (p x) hxI
  let U₀a : X.affineOpens := ⟨U₀, hU₀⟩
  let s : S' := pullback.fst g f x
  have hs : g s = f (p x) := by
    have hh := congrArg (fun k => k x) (pullback.condition (f := g) (g := f))
    simpa [s, Scheme.Hom.comp_apply] using hh
  obtain ⟨V₀, hV₀, hfxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f (p x)) (by simp)
  let V : S.affineOpens := ⟨V₀, hV₀⟩
  obtain ⟨V'₀, hV'₀, hsV', hV'sub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S') (U := g ⁻¹ᵁ V.1) (x := s)
      (by simpa [hs] using hfxV)
  let V' : S'.affineOpens := ⟨V'₀, hV'₀⟩
  have hV'V : V'.1 ≤ g ⁻¹ᵁ V.1 := fun y hy => hV'sub hy
  have hpV : p x ∈ f ⁻¹ᵁ V.1 := hfxV
  obtain ⟨b, hb, hxb⟩ := U₀a.2.exists_basicOpen_le ⟨p x, hpV⟩ hxU₀
  let U : X.affineOpens := X.affineBasicOpen b
  have hUU₀ : U ≤ U₀a := X.affineBasicOpen_le b
  have hUV : U.1 ≤ f ⁻¹ᵁ V.1 := by simpa [U] using hb
  have hxU : p x ∈ U.1 := by simpa [U] using hxb
  let rU : Γ(X, U₀a.1) →+* Γ(X, U.1) :=
    (X.presheaf.map (CategoryTheory.homOfLE hUU₀).op).hom
  let aU : Γ(X, U.1) := rU a
  have haU : IsRegular aU := isRegular_res_basicOpen hUU₀ b a rfl ha
  have hspanU : I.ideal U = Ideal.span {aU} :=
    ideal_eq_span_res_of_chart I hUU₀ a e he
  let Y := pullback g f
  let W : Y.Opens := pullback.fst g f ⁻¹ᵁ V'.1 ⊓ pullback.snd g f ⁻¹ᵁ U.1
  have hPB : IsPullback
      ((pullback.fst g f).resLE V'.1 W (by simp [W]))
      ((pullback.snd g f).resLE U.1 W (by simp [W]))
      (g.resLE V.1 V'.1 hV'V) (f.resLE V.1 U.1 hUV) := by
    simpa [W] using Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback g f)
      (US := V.1) (UT := U.1) (UX := V'.1) hUV hV'V (UY := W) (by rfl)
  let _ : IsAffine V'.1.toScheme := V'.2
  let _ : IsAffine V.1.toScheme := V.2
  let _ : IsAffine U.1.toScheme := U.2
  let Waff : Y.affineOpens := ⟨W, by
    change IsAffine W.toScheme
    let _ : IsAffineHom (g.resLE V.1 V'.1 hV'V) := inferInstance
    exact IsAffine.of_isPullback hPB.flip⟩
  have hxW : x ∈ W := by
    change pullback.fst g f x ∈ V'.1 ∧ pullback.snd g f x ∈ U.1
    exact ⟨hsV', hxU⟩
  have hWU : W ≤ p ⁻¹ᵁ U.1 := fun y hy => hy.2
  let a' : Γ(Y, W) := (p.appLE U Waff hWU).hom aU
  have hJideal : J.ideal Waff = Ideal.span {a'} := by
    rw [Stacks.IdealSheaf.ideal_comap_appLE I p U Waff hWU, hspanU, Ideal.map_span,
      Set.image_singleton]
  let A := Γ(S, V.1)
  let B := Γ(X, U.1)
  let Q := B ⧸ Ideal.span {aU}
  let fVU := (f.appLE V U hUV).hom
  let q : B →+* Q := Ideal.Quotient.mk (Ideal.span {aU})
  let qA : A →+* Q := q.comp fVU
  have hFlatB : (Ideal.Quotient.mk (I.ideal U)).comp fVU |>.Flat :=
    flat_quotient_map_of_flat_subscheme f I inferInstance U V hUV
  have hFlatQ : qA.Flat := by
    rwa [hspanU] at hFlatB
  let _ : Algebra A B := fVU.toAlgebra
  let _ : Algebra A Q := qA.toAlgebra
  have hQflat : Module.Flat A Q := RingHom.flat_algebraMap_iff.mp hFlatQ
  let rBtoD := (p.appLE U Waff hWU).hom
  algebraize [(f.appLE V U hUV).hom, (g.appLE V V' hV'V).hom,
    (p.appLE U Waff hWU).hom,
    ((pullback.fst g f).appLE V' Waff (by intro y hy; exact hy.1)).hom,
    (p.appLE U Waff hWU).hom.comp (f.appLE V U hUV).hom]
  have hPush : IsPushout
      (f.appLE V U hUV) (g.appLE V V' hV'V) (p.appLE U Waff hWU)
      ((pullback.fst g f).appLE V' Waff (by intro y hy; exact hy.1)) := by
    let _ : IsAffine W.toScheme := Waff.2
    let hp := isPushout_appTop_of_isPullback hPB.flip
    let eTop := arrowResLEAppIso f V.1 U.1 hUV
    let eLeft := arrowResLEAppIso g V.1 V'.1 hV'V
    let eRight := arrowResLEAppIso p U.1 W inf_le_right
    let eBottom := arrowResLEAppIso (pullback.fst g f) V'.1 W inf_le_left
    exact CategoryTheory.IsPushout.of_iso hp
      V.1.topIso U.1.topIso V'.1.topIso W.topIso
      eTop.hom.w.symm eLeft.hom.w.symm eRight.hom.w.symm eBottom.hom.w.symm
  let ePush : B ⊗[A] Γ(S', V'.1) ≃+* Γ(Y, W) :=
    ((CommRingCat.isPushout_tensorProduct A B Γ(S', V'.1)).isoIsPushout
      B Γ(S', V'.1) hPush).commRingCatIsoToRingEquiv
  have hTensorReg : IsRegular
      (Algebra.TensorProduct.includeRight (R := A) (A := Γ(S', V'.1)) aU) :=
    isRegular_includeRight_of_flat_quotient (A := A) (B := B) (A' := Γ(S', V'.1)) aU haU
  let cSwap : (Γ(S', V'.1) ⊗[A] B) ≃+* (B ⊗[A] Γ(S', V'.1)) :=
    (Algebra.TensorProduct.comm A Γ(S', V'.1) B).toRingEquiv
  have hSwap : cSwap (Algebra.TensorProduct.includeRight
      (R := A) (A := Γ(S', V'.1)) aU) =
      Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B)
        (B := Γ(S', V'.1)) aU := by
    simp [cSwap]
  have hTensorReg' : IsRegular
      (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B)
        (B := Γ(S', V'.1)) aU) := by
    rw [← hSwap]
    exact isRegular_ringEquiv cSwap hTensorReg
  have ha' : IsRegular a' := by
    have hImage := isRegular_ringEquiv ePush hTensorReg'
    have hMap : ePush.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B)) = rBtoD := by
      let hTensorPush := CommRingCat.isPushout_tensorProduct A B Γ(S', V'.1)
      have hIso : CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B)) ≫
          (hTensorPush.isoIsPushout B Γ(S', V'.1) hPush).hom = p.appLE U Waff hWU :=
        CategoryTheory.IsPushout.inl_isoIsPushout_hom
          (h := hTensorPush) (h' := hPush)
      have hIso' := congrArg CommRingCat.Hom.hom hIso
      change (CommRingCat.Hom.hom
          (hTensorPush.isoIsPushout B Γ(S', V'.1) hPush).hom).comp
          (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B)) = rBtoD
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using hIso'
    have hePush : ePush (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := Γ(S', V'.1)) aU) = a' := by
      change ePush.toRingHom
          ((Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B)) aU) = _
      exact congrArg (fun k : B →+* Γ(Y, W) => k aU) hMap
    rwa [hePush] at hImage
  obtain ⟨eJ, heJ⟩ := exists_quotient_chart_of_ideal_span J W Waff.2 a' hJideal
  exact ⟨W, Waff.2, hxW, a', ha', eJ, heJ⟩

end AlgebraicGeometry

end
