module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.RingTheory.TensorProduct.UnderLimits

/-!
# Sections of a fibre product over an arbitrary cover

Mathlib's descent of the comparison map
`Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ Uₜ)` along a cover of `Uₓ`
(`AlgebraicGeometry.mono_pushoutSection_of_iSup_eq` and
`AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq`) carries `[Finite ι]` on the index of the
cover. That finiteness is what forces the quasi-compactness and quasi-separatedness hypotheses
on every consequence Mathlib draws from it.

The finiteness is used in exactly two places, and both are mathematically removable once
`Γ(T, Uₜ)` is a *finitely presented* `Γ(S, Uₛ)`-module:

* in the injectivity argument, to invert the comparison
  `Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ) ⟶ ∏ᵢ Γ(T, Uₜ) ⊗ Γ(X, Vᵢ)`, which for a finitely presented left
  factor is bijective for every index type by Stacks Tag 059K;
* in the surjectivity argument, to know that base change along `Γ(S, Uₛ) ⟶ Γ(T, Uₜ)`
  preserves the limit of the `Pairwise`-indexed diagram of the cover, which for a flat and
  finitely presented ring map holds for limits of every shape.

This file carries out the first of the two.

## Main results

* `Stacks.Tag0CKW.mono_pushoutSection_of_iSup_eq`: the injectivity descent, with no finiteness
  hypothesis on the index of the cover.
* `Stacks.Tag0CKW.mono_pushoutSection_of_isAffineOpen_base`: injectivity for an *arbitrary*
  open of an arbitrary scheme, obtained by covering it by all of the affine opens it contains.
* `Stacks.Tag0CKW.mono_globalSectionsBaseChange_of_flat_of_finitePresentation`: the same at the
  top open of an arbitrary scheme over an affine base, which is the injectivity half of the
  degree-zero assertion of Stacks Tag 0CKW.

## Implementation notes

The two descent proofs follow Mathlib's, with `Algebra.TensorProduct.piRight` replaced by
`Algebra.TensorProduct.piRightOfFinitePresentation` and
`CommRingCat.Under.preservesFiniteLimits_of_flat` by
`CommRingCat.Under.preservesLimits_pushout`. Mathlib states its injectivity lemma under
`backward.isDefEq.respectTransparency false`; that option is not used here.

The second result takes the cover of an arbitrary open `UX` by *all* affine opens contained in
it. The index type is `X.affineOpens` restricted to `UX`, which is a type in the same universe
as the scheme, so no finiteness or smallness side condition arises; on each member the
comparison is bijective by `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`.

Only the injectivity half of the descent is proved here. The bijectivity half —
`AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` with `[Finite ι]` traded for finite
presentation, which is what `CommRingCat.Under.preservesLimits_pushout` was proved for — is not
in this file.

## References

* [Stacks Project, Tag 0CKW](https://stacks.math.columbia.edu/tag/0CKW)
* [Stacks Project, Tag 059K](https://stacks.math.columbia.edu/tag/059K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Tag0CKW

open AlgebraicGeometry

variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
  (H : IsPullback g iY iX f)
  {US : S.Opens} {UT : T.Opens}
  {UX : X.Opens} (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
  {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)

/-- The comparison map of Mathlib's `AlgebraicGeometry.pushoutSection` is injective after
descent along an arbitrary cover of `Uₓ`, provided `Γ(T, Uₜ)` is a flat and finitely presented
`Γ(S, Uₛ)`-module. This is `AlgebraicGeometry.mono_pushoutSection_of_iSup_eq` with the
finiteness of the index traded for finite presentation. -/
lemma mono_pushoutSection_of_iSup_eq {ι : Type u} (VX : ι → X.Opens) (hVU : iSup VX = UX)
    (hV : ∀ i, Mono (pushoutSection H hUST (show VX i ≤ _ by aesop) rfl))
    (hT : (f.appLE US UT hUST).hom.Flat)
    (hTfp : letI := (f.appLE US UT hUST).hom.toAlgebra
      Module.FinitePresentation ↑Γ(S, US) ↑Γ(T, UT)) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  have (i : _) : VX i ≤ iX ⁻¹ᵁ US := by
    clear hV
    aesop
  classical
  algebraize [(iX.appLE US UX hUSX).hom, (f.appLE US UT hUST).hom]
  have : Module.FinitePresentation ↑Γ(S, US) ↑Γ(T, UT) := hTfp
  let (i : _) := (iX.appLE US (VX i) (by aesop)).hom.toAlgebra
  -- This is the map `Γ(X ×ₛ T, U ∩ Uₜ) ⟶ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)` on the bottom.
  let ψY : Γ(Y, UY) →+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) := RingHom.pi fun i ↦
      (Y.presheaf.map (homOfLE (by subst hUY hVU; gcongr; exact le_iSup _ _)).op).hom
  -- The map `Γ(X, U) ⟶ ∏ᵢ Γ(X, Vᵢ)`
  let ψ : Γ(X, UX) →ₐ[Γ(S, US)] Π i, Γ(X, VX i) := AlgHom.pi fun i ↦
    ⟨(X.presheaf.map (homOfLE (hVU ▸ le_iSup VX i)).op).hom, fun r ↦ by
      dsimp [RingHom.algebraMap_toAlgebra]
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]⟩
  -- ... is injective by the sheaf axiom,
  have hψ : Function.Injective ψ := by
    intro s t est
    apply X.IsSheaf.section_ext fun x hx ↦ ?_
    simp only [← hVU, Opens.mem_iSup] at hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨_, _, hxi, congr($est i)⟩
  -- ... and remains injective after tensoring with `Γ(T, Uₜ)` by the flatness assumption.
  have hψ' : Function.Injective (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ.toLinearMap hψ
  simp_rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback] at hV ⊢
  -- And the map at the right
  let φ : (Γ(T, UT) ⊗[Γ(S, US)] Π i, Γ(X, VX i)) →+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) :=
    (RingHom.pi fun i ↦ (pushoutSection H hUST (show VX i ≤ _ by aesop) rfl).hom.comp
      ((CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.hom.hom.comp
      (by exact Pi.evalRingHom _ _))).comp
      (Algebra.TensorProduct.piRightOfFinitePresentation _ Γ(S, US) _ _).toRingHom
  -- ... is also injective by our hypotheses on `Vᵢ`.
  have hφ : Function.Injective φ := by
    dsimp [φ]
    refine .comp ?_ (Algebra.TensorProduct.piRightOfFinitePresentation
      _ Γ(S, US) _ _).injective
    exact .piMap fun i ↦ (hV _).comp <| CommRingCat.isPushout_tensorProduct _ _ _
      |>.flip.isoPushout.commRingCatIsoToRingEquiv.injective
  let e : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ≅
      .of (Γ(T, UT) ⊗[Γ(S, US)] Γ(X, UX)) :=
    (CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.symm
  -- It remains to check that the square indeed commutes, and we may conclude that the map
  -- at the left is also injective.
  suffices (ψY.comp (pushoutSection H hUST hUSX hUY).hom).comp e.inv.hom = φ.comp
      (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ).toRingHom by
    refine .of_comp (f := ψY) ?_
    convert (hφ.comp hψ').comp e.commRingCatIsoToRingEquiv.injective
    ext1 x
    simpa using! congr($this (e.hom x))
  ext1
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeLeftRingHom =
        (pushout.inr (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inr_isoPushout_hom).hom)
    have H₂ (x j) : φ (x ⊗ₜ[↑Γ(S, US)] 1) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inr (C := CommRingCat) _ _ x) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inr_isoPushout_hom) x))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, -CommRingCat.hom_comp, ← CategoryTheory.comp_apply, pushoutSection,
      Scheme.Hom.appLE_map]
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeRight.toRingHom =
        (pushout.inl (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inl_isoPushout_hom).hom)
    have H₂ (x j) : φ (1 ⊗ₜ[↑Γ(S, US)] x) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inl (C := CommRingCat) _ _ (x j)) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inl_isoPushout_hom) (x j)))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, -CommRingCat.hom_comp, ← CategoryTheory.comp_apply, pushoutSection, ψ,
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- **Injectivity of the comparison map over an arbitrary open, with no compactness
hypothesis.** When `Uₛ` and `Uₜ` are affine and `Γ(T, Uₜ)` is a flat, finitely presented
`Γ(S, Uₛ)`-module, the canonical map
`Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ Uₜ)` is injective for *every*
open `Uₓ`. Mathlib's `AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_right` is the
same statement for a compact `Uₓ`; the compactness is what the finite presentation replaces.

The proof covers `Uₓ` by all of the affine opens it contains — an index type with no finiteness
and no smallness condition — and uses that the comparison is bijective on each of them. -/
lemma mono_pushoutSection_of_isAffineOpen_base
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hT : (f.appLE US UT hUST).hom.Flat)
    (hTfp : letI := (f.appLE US UT hUST).hom.toAlgebra
      Module.FinitePresentation ↑Γ(S, US) ↑Γ(T, UT)) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  refine mono_pushoutSection_of_iSup_eq H hUST hUSX hUY
    (ι := { V : X.affineOpens // (V : X.Opens) ≤ UX }) (fun V ↦ (V.1 : X.Opens)) ?_ ?_ hT hTfp
  · refine le_antisymm (iSup_le fun V ↦ V.2) fun x hx ↦ ?_
    obtain ⟨V, hVmem, hxV, hVU⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := UX) (x := x) hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hVmem⟩, hVU⟩, hxV⟩
  · intro V
    have := isIso_pushoutSection_of_isAffineOpen H hUST
      (show (V.1 : X.Opens) ≤ _ from V.2.trans hUSX) rfl hUS hUT V.1.2
    infer_instance

/-- **Injectivity of the degree-zero base-change map on global functions, for an arbitrary
scheme.** For a cartesian square with `S` and `S'` affine and `Γ(S', ⊤)` a flat, finitely
presented `Γ(S, ⊤)`-module, the canonical ring map
`Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤) ⟶ Γ(X ×_S S', ⊤)` is injective. No quasi-compactness or
quasi-separatedness hypothesis is imposed on `X`.

This is the injectivity half of the degree-zero assertion of [Stacks, Tag 0CKW]. The tag's own
hypothesis on `g` is that it be finite locally free, which over an affine base is exactly
flatness together with finite presentation of the global sections as a module; that equivalence
is `Stacks.Morphisms.sheafOfModules_isFiniteLocallyFree_iff_module` composed with
`Module.isFiniteLocallyFree_iff`, both of which are stated for a target of the form `Spec R`. -/
lemma mono_globalSectionsBaseChange_of_flat_of_finitePresentation
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {fX : X ⟶ S} {g : S' ⟶ S}
    (h : IsPullback g' f' fX g) [IsAffine S] [IsAffine S']
    (hflat : (g.appLE ⊤ ⊤ (by simp)).hom.Flat)
    (hfp : letI := (g.appLE ⊤ ⊤ (by simp : (⊤ : S'.Opens) ≤ g ⁻¹ᵁ ⊤)).hom.toAlgebra
      Module.FinitePresentation ↑Γ(S, ⊤) ↑Γ(S', ⊤)) :
    Mono (AlgebraicGeometry.pushoutSection h (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
      (by simp) (by simp) (by simp)) :=
  mono_pushoutSection_of_isAffineOpen_base h (by simp) (by simp) (by simp)
    (isAffineOpen_top S) (isAffineOpen_top S') hflat hfp

end Stacks.Tag0CKW

end
