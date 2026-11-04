module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.SmoothReduction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalKernelLocalRings
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Noetherian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.StructureSheaf

/-!
# `f_*𝒪_X = 𝒪_Y` spreads from a dense open for a flat proper morphism to a normal base

Let `f : X ⟶ Y` be flat, proper and surjective, with `Y` a normal Noetherian scheme, and suppose
that `Γ(Y, W) ⟶ Γ(X, f⁻¹W)` is an isomorphism for every open `W` of a dense open `V ⊆ Y`. Then
`f_*𝒪_X = 𝒪_Y`.

## Main results

* `Stacks.SteinFactorization.isIso_app_of_flat_of_isIntegral`: the affine statement over an
  integral normal base.
* `Stacks.SteinFactorization.isIso_c_of_flat_of_isNormal`: the main statement.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.SteinFactorization

variable {X Y : Scheme.{u}}

/-- Sections over an empty open of a scheme form a subsingleton. -/
private theorem subsingleton_sections_of_isEmpty (U : X.Opens) (h : IsEmpty U) :
    Subsingleton Γ(X, U) := by
  have hU0 : U = ⊥ := by
    ext x
    exact ⟨fun hx ↦ (h.false ⟨x, hx⟩).elim, fun hx ↦ hx.elim⟩
  exact CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU0)

/-- **Over an integral base, the image of a nonzero section over an affine open is a
nonzerodivisor on the sections over its preimage, for a flat morphism.** -/
theorem eq_zero_of_mul_eq_zero_of_flat (f : X ⟶ Y) [Flat f] [IsIntegral Y] {U : Y.Opens}
    (hU : IsAffineOpen U) {a : Γ(Y, U)} (ha : a ≠ 0) {b : Γ(X, f ⁻¹ᵁ U)}
    (hab : f.app U a * b = 0) : b = 0 := by
  have hne : Nonempty U := by
    by_contra h
    exact ha (@Subsingleton.elim _ (subsingleton_sections_of_isEmpty U (not_nonempty_iff.mp h)) _ _)
  refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  have hreg : IsSMulRegular Γ(Y, U) a := (IsRegular.of_ne_zero ha).left.isSMulRegular
  let _ : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVle).hom.toAlgebra
  have : Module.Flat Γ(Y, U) Γ(X, V) := f.flat_appLE hU hV hVle
  have hreg' : IsSMulRegular Γ(X, V) (algebraMap Γ(Y, U) Γ(X, V) a) := hreg.of_flat
  let ρ := X.presheaf.map (homOfLE hVle).op
  have hres : ρ b = 0 := by
    apply hreg'
    show (f.appLE U V hVle) a * ρ b = (f.appLE U V hVle) a * 0
    rw [mul_zero]
    show ρ (f.app U a) * ρ b = 0
    rw [← map_mul, hab, map_zero]
  show X.presheaf.germ _ x hx b = X.presheaf.germ _ x hx 0
  rw [← X.presheaf.germ_res_apply (homOfLE hVle) x hxV b, map_zero]
  show X.presheaf.germ V x hxV (ρ b) = 0
  rw [hres, map_zero]

/-- **`Γ(Y, U) ⟶ Γ(X, f⁻¹U)` is an isomorphism on affine opens, for `f` flat, proper and
surjective onto an integral normal locally Noetherian scheme, as soon as it is one on all opens
inside a nonempty open `V`.** -/
theorem isIso_app_of_flat_of_isIntegral (f : X ⟶ Y) [Flat f] [IsProper f] [Surjective f]
    [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] (V : Y.Opens) [Nonempty V]
    (hV : ∀ W : Y.Opens, W ≤ V → IsIso (f.app W)) (U : Y.Opens) (hU : IsAffineOpen U) :
    IsIso (f.app U) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨f.app_injective U, fun b ↦ ?_⟩
  by_cases hUe : IsEmpty U
  · have := subsingleton_sections_of_isEmpty (f ⁻¹ᵁ U) ⟨fun ⟨x, hx⟩ ↦ hUe.false ⟨f x, hx⟩⟩
    exact ⟨0, Subsingleton.elim _ _⟩
  have : Nonempty U := not_isEmpty_iff.mp hUe
  let R := Γ(Y, U)
  have hRint : IsIntegrallyClosed R := isIntegrallyClosed_sections Y U hU
  have hfin : (f.app U).hom.Finite := finite_app_of_isProper f U hU
  obtain ⟨y, hyV, hyU⟩ : ((V : Set Y) ∩ U).Nonempty :=
    nonempty_preirreducible_inter V.isOpen U.isOpen
      (Set.nonempty_coe_sort.mp ‹Nonempty V›) (Set.nonempty_coe_sort.mp ‹Nonempty U›)
  obtain ⟨a, hDle, hya⟩ := hU.exists_basicOpen_le (V := V) ⟨y, hyV⟩ hyU
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hya
  let D := Y.basicOpen a
  have hDiso : IsIso (f.app D) := hV D hDle
  have hlocY : IsLocalization.Away a Γ(Y, D) := hU.isLocalization_basicOpen a
  let a' := f.app U a
  have hpre : f ⁻¹ᵁ D = X.basicOpen a' := Scheme.preimage_basicOpen f a
  have hlocX : IsLocalization.Away a' Γ(X, X.basicOpen a') :=
    isLocalization_basicOpen_of_qcqs
      (QuasiCompact.isCompact_preimage (f := f) _ U.isOpen hU.isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _) a'
  let φD := f.appLE D (X.basicOpen a') hpre.ge
  have hφD : IsIso φD := by
    have h2 : φD = f.app D ≫ X.presheaf.map (eqToHom hpre.symm).op := rfl
    rw [h2]
    infer_instance
  have hcomm : ∀ r : R, φD (algebraMap R Γ(Y, D) r) =
      algebraMap Γ(X, f ⁻¹ᵁ U) Γ(X, X.basicOpen a') (f.app U r) := by
    intro r
    show (Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op ≫ φD) r =
      (f.app U ≫ X.presheaf.map (homOfLE (X.basicOpen_le a')).op) r
    rw [Scheme.Hom.map_appLE]
    rfl
  have hφDbij := (ConcreteCategory.isIso_iff_bijective φD).mp hφD
  obtain ⟨c, hc⟩ := hφDbij.2 (algebraMap Γ(X, f ⁻¹ᵁ U) Γ(X, X.basicOpen a') b)
  obtain ⟨P, hPm, hPb⟩ := hfin.to_isIntegral b
  have hPc : Polynomial.eval₂ (algebraMap R Γ(Y, D)) c P = 0 := by
    apply hφDbij.1
    rw [map_zero, Polynomial.hom_eval₂, hc]
    have hcomp : φD.hom.comp (algebraMap R Γ(Y, D)) =
        (algebraMap Γ(X, f ⁻¹ᵁ U) Γ(X, X.basicOpen a')).comp (f.app U).hom :=
      RingHom.ext hcomm
    rw [hcomp, ← Polynomial.hom_eval₂, hPb, map_zero]
  have hcint : IsIntegral R c := ⟨P, hPm, hPc⟩
  let K := FractionRing R
  have hunit : ∀ y : Submonoid.powers a, IsUnit (algebraMap R K y) := by
    rintro ⟨_, n, rfl⟩
    exact (pow_ne_zero n ha |> fun h ↦ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero h)).isUnit)
  let g : Γ(Y, D) →ₐ[R] K := IsLocalization.liftAlgHom (M := Submonoid.powers a)
    (f := Algebra.ofId R K) hunit
  have hle : Submonoid.powers a ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ha
  have hinj : Function.Injective (algebraMap R Γ(Y, D)) :=
    IsLocalization.injective Γ(Y, D) hle
  have hg : Function.Injective g :=
    (IsLocalization.lift_injective_iff (M := Submonoid.powers a) (S := Γ(Y, D)) hunit).mpr
      fun x y ↦ ⟨fun h ↦ by rw [hinj h], fun h ↦ by rw [IsFractionRing.injective R K h]⟩
  have hcl : IsIntegrallyClosedIn R Γ(Y, D) :=
    AlgHom.isIntegrallyClosedIn g hg
      ((isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp hRint)
  obtain ⟨u, hu⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := R) (A := Γ(Y, D))).mp hcint
  refine ⟨u, ?_⟩
  have hres : algebraMap Γ(X, f ⁻¹ᵁ U) Γ(X, X.basicOpen a') (b - f.app U u) = 0 := by
    rw [map_sub, ← hc, ← hcomm, hu, sub_self]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a') _ _).mp hres
  have hk' : f.app U (a ^ k) * (b - f.app U u) = 0 := by
    rwa [map_pow]
  exact (sub_eq_zero.mp (eq_zero_of_mul_eq_zero_of_flat f hU (pow_ne_zero k ha) hk')).symm

/-- **`f_*𝒪_X = 𝒪_Y` spreads from a dense open, for `f` flat, proper and surjective onto a normal
Noetherian scheme.** If `Γ(Y, W) ⟶ Γ(X, f⁻¹W)` is an isomorphism for every open `W` inside a dense
open `V`, then `f_*𝒪_X = 𝒪_Y`. -/
theorem isIso_c_of_flat_of_isNormal (f : X ⟶ Y) [Flat f] [IsProper f] [Surjective f]
    [IsNoetherian Y] [IsNormal Y] (V : Y.Opens) (hVd : Dense (V : Set Y))
    (hV : ∀ W : Y.Opens, W ≤ V → IsIso (f.app W)) : IsIso f.c := by
  obtain ⟨ι, -, Z, -, hZint, -, -, hcov⟩ := Stacks.EtaleCohomology.exists_integral_isCompl_cover Y
  have hrestr : ∀ (i : ι) (W' : (Z i).toScheme.Opens),
      IsIso ((f ∣_ Z i).app W') ↔ IsIso (f.app ((Z i).ι ''ᵁ W')) := by
    intro i W'
    rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
    have h := morphismRestrict_app f (Z i) W'
    let ρ := X.presheaf.map (eqToHom (image_morphismRestrict_preimage f (Z i) W')).op
    have hρ : Function.Bijective ρ := (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    have h' : ⇑((f ∣_ Z i).app W') = ρ ∘ f.app ((Z i).ι ''ᵁ W') := funext fun x ↦
      congrArg (fun φ : Γ(Y, (Z i).ι ''ᵁ W') ⟶ Γ(X, (f ⁻¹ᵁ Z i).ι ''ᵁ (f ∣_ Z i) ⁻¹ᵁ W') ↦ φ x) h
    rw [h']
    exact Function.Bijective.of_comp_iff' hρ _
  refine Stacks.AlgebraicGeometry.isIso_c_of_isIso_app_basicOpen f
    (ι := Σ i, (Z i).toScheme.affineOpens)
    (fun p ↦ (Z p.1).ι ''ᵁ p.2.1) (fun p ↦ p.2.2.image_of_isOpenImmersion _) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    obtain ⟨U, hU, hyU, -⟩ := Opens.isBasis_iff_nbhd.mp (Z i).toScheme.isBasis_affineOpens
      (show (⟨y, hi⟩ : Z i) ∈ (⊤ : (Z i).toScheme.Opens) from trivial)
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨U, hU⟩⟩, (Scheme.Opens.mem_ι_image_iff (x := ⟨y, hi⟩)).mpr hyU⟩
  · rintro ⟨i, U⟩ r
    have := hZint i
    have : IsNormal (Z i).toScheme := isNormal_of_isOpenImmersion (Z i).ι
    have : Surjective (f ∣_ Z i) :=
      MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict f (Z i)).flip
        ‹_›
    have hVi : Nonempty ((Z i).ι ⁻¹ᵁ V) := by
      obtain ⟨z⟩ : Nonempty (Z i).toScheme := inferInstance
      obtain ⟨y, hyZ, hyV⟩ := hVd.inter_open_nonempty (Z i) (Z i).isOpen ⟨z.1, z.2⟩
      exact ⟨⟨⟨y, hyZ⟩, hyV⟩⟩
    let B := Y.basicOpen r
    have hBle : B ≤ Z i := (Y.basicOpen_le r).trans (Scheme.Opens.ι_image_le _ _)
    let B' := (Z i).ι ⁻¹ᵁ B
    have hB' : (Z i).ι ''ᵁ B' = B := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hBle]
    have hBaff : IsAffineOpen B' := by
      rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (Z i).ι, hB']
      exact (U.2.image_of_isOpenImmersion _).basicOpen r
    have key := isIso_app_of_flat_of_isIntegral (f ∣_ Z i) ((Z i).ι ⁻¹ᵁ V)
      (fun W' hW' ↦ (hrestr i W').mpr (hV _ (by
        rintro y ⟨w, hw, rfl⟩
        exact hW' hw))) B' hBaff
    rwa [hrestr, hB'] at key

end Stacks.SteinFactorization

end
