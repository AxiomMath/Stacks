module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SectionDivisor
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.NormalizedSection
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChangeDescent
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponents

/-!
# Divisors with the same normalized invertible sheaf

Let `X` be a geometrically irreducible smooth proper curve over a field `k` covered by two
affine opens, `A` a `k`-algebra and `X_A ⟶ Spec A` a base change of `X`. If two closed subschemes
`D₁, D₂ ⊂ X_A`, finite locally free over `A` and effective Cartier, have isomorphic invertible
sheaves `𝒪(D₁) ≅ 𝒪(D₂)`, and every fibre of `𝒪(D₁)` has `H¹ = 0` and `dim H⁰ = 1`, then
`D₁ = D₂`. This is the uniqueness half of the proof of [Stacks, Tag 0B9X]: the canonical
section of `𝒪(D₁)` generates `H⁰(X_A, 𝒪(D₁))` freely, so the canonical section of `𝒪(D₂)`
corresponds to a unit multiple of it, and zero schemes of unit multiples agree.

## Main results

* `Stacks.PicardCurve.zeroScheme_smul_of_isUnit`.
* `Stacks.PicardCurve.pullbackGlobalSections_canonicalSection_ne_zero`.
* `Stacks.PicardCurve.eq_of_invertibleSheaf_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Divisors (IsEffectiveCartierDivisor IsRelativeEffectiveCartierDivisor invertibleSheaf'
  canonicalSection')
open Stacks.FibreCohomology (fibreCohomology)

universe u

namespace Stacks.PicardCurve

/-- **The zero scheme of a unit multiple of a section is the zero scheme of the section.** -/
theorem zeroScheme_smul_of_isUnit {Y : Scheme.{u}} (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] (s : Γ(M, ⊤))
    {v : Γ(Y, ⊤)} (hv : IsUnit v) : zeroScheme Y M (v • s) = zeroScheme Y M s := by
  refine congrArg Scheme.IdealSheafData.ofIdeals (funext fun U => congrArg Ideal.span ?_)
  obtain ⟨w, rfl⟩ := hv
  set vU : Γ(Y, U.1) := Y.presheaf.map (homOfLE le_top).op (w : Γ(Y, ⊤))
  set wU : Γ(Y, U.1) := Y.presheaf.map (homOfLE le_top).op ((w⁻¹ : (Γ(Y, ⊤))ˣ) : Γ(Y, ⊤))
  have hvw : wU * vU = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hmap : M.presheaf.map (homOfLE le_top).op ((w : Γ(Y, ⊤)) • s) =
      vU • M.presheaf.map (homOfLE le_top).op s := Scheme.Modules.map_smul _ _ _ _
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [hmap]
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨vU • φ, by rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨wU • φ, by rw [LinearMap.smul_apply, LinearMap.map_smul, smul_smul, hvw, one_smul]⟩

/-- **The kernel of the residue map at a point of `Spec A` is the point.** -/
theorem ker_preimage_fromSpecResidueField {A : Type u} [CommRing A] (t : Spec (.of A)) :
    RingHom.ker (Spec.preimage ((Spec (.of A)).fromSpecResidueField t)).hom = t.asIdeal := by
  set φ := Spec.preimage ((Spec (.of A)).fromSpecResidueField t)
  have hφ : Spec.map φ = (Spec (.of A)).fromSpecResidueField t := Spec.map_preimage _
  let c : Spec ((Spec (.of A)).residueField t) :=
    IsLocalRing.closedPoint ((Spec (.of A)).residueField t)
  have h1 : Spec.map φ c = t := by rw [hφ, Scheme.fromSpecResidueField_apply]
  have h2 : (Spec.map φ c).asIdeal = Ideal.comap φ.hom c.asIdeal := rfl
  have hc : c.asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
  rw [congrArg PrimeSpectrum.asIdeal h1.symm, h2, hc, RingHom.ker_eq_comap_bot]

/-- **A section nonzero on the scheme-theoretic fibre at a point is nonzero at a field point
over that prime.** -/
theorem nonzeroAtFieldPoint_of_fiberι {A : Type u} [CommRing A] {XT : Scheme.{u}}
    (fT : XT ⟶ Spec (.of A)) (L : XT.Modules) (s : Γ(L, ⊤)) (t : Spec (.of A))
    (hs : pullbackGlobalSections (fT.fiberι t) L s ≠ 0) :
    Stacks.TwoAffineCech.NonzeroAtFieldPoint fT L s t := by
  set φ := Spec.preimage ((Spec (.of A)).fromSpecResidueField t)
  refine ⟨(Spec (.of A)).residueField t, inferInstance, φ.hom, ker_preimage_fromSpecResidueField t,
    fT.fiber t, fT.fiberToSpecResidueField t, fT.fiberι t, ?_, hs⟩
  have hφ : Spec.map (CommRingCat.ofHom φ.hom) = (Spec (.of A)).fromSpecResidueField t :=
    Spec.map_preimage _
  rw [hφ]
  exact IsPullback.of_hasPullback _ _

/-- The zero ideal sheaf is not an effective Cartier divisor on a nonempty scheme. -/
theorem not_isEffectiveCartierDivisor_bot {Y : Scheme.{u}} [Nonempty Y] :
    ¬ IsEffectiveCartierDivisor (⊥ : Y.IdealSheafData) := by
  intro h
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨U, hU, hyU, b, hb, hgen⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor _ h y
  obtain rfl : b = 0 := by
    have : b ∈ (⊥ : Y.IdealSheafData).ideal ⟨U, hU⟩ := by
      rw [hgen]
      exact Ideal.mem_span_singleton_self b
    exact (Submodule.mem_bot _).1 this
  have hnt : Nontrivial Γ(Y, U) := (Y.presheaf.germ U y hyU).hom.domain_nontrivial
  exact not_subsingleton _ (isRegular_iff_subsingleton.1 hb)

open Stacks.Divisors (divisorSheaf divisorSheafGlobalSection) in
/-- **The canonical section of a relative effective Cartier divisor is nonzero on every
fibre**, when the family is surjective: its zero scheme on the fibre is the fibre of the
divisor, an effective Cartier divisor on a nonempty scheme ([Stacks, Tag 056Q]). -/
theorem pullbackGlobalSections_canonicalSection_ne_zero {T XT : Scheme.{u}} (fT : XT ⟶ T)
    [Surjective fT] (D : XT.IdealSheafData) (hD : IsRelativeEffectiveCartierDivisor fT D)
    (t : T) :
    pullbackGlobalSections (fT.fiberι t) (divisorSheaf D) (divisorSheafGlobalSection D) ≠ 0 := by
  have : IsEffectiveCartierDivisor D := hD.1
  have : Flat (D.subschemeι ≫ fT) := hD.2
  have hsnd : IsEffectiveCartierDivisor (D.comap (pullback.snd (T.fromSpecResidueField t) fT)) :=
    isEffectiveCartierDivisor_comap_pullback fT _ D hD.1
  have hfib : fT.fiberι t = (pullbackSymmetry fT (T.fromSpecResidueField t)).hom ≫
      pullback.snd (T.fromSpecResidueField t) fT := (pullbackSymmetry_hom_comp_snd _ _).symm
  have hcomap : IsEffectiveCartierDivisor (D.comap (fT.fiberι t)) := by
    have h := Stacks.Divisors.isPullbackDefined_of_flat
      (pullbackSymmetry fT (T.fromSpecResidueField t)).hom _ hsnd
    unfold Stacks.Divisors.IsPullbackDefined at h
    rwa [← Scheme.IdealSheafData.comap_comp, ← hfib] at h
  obtain ⟨x, hx⟩ := fT.surjective t
  have : Nonempty (fT.fiber t) := by
    obtain ⟨y, -⟩ : x ∈ Set.range (fT.fiberι t) := by
      rwa [Scheme.Hom.range_fiberι]
    exact ⟨y⟩
  intro h0
  have hz := Stacks.Divisors.zeroScheme_pullback (fT.fiberι t) (divisorSheaf D)
    (divisorSheafGlobalSection D)
  rw [h0] at hz
  have hz' : AlgebraicGeometry.zeroScheme (fT.fiber t)
      ((Scheme.Modules.pullback (fT.fiberι t)).obj (divisorSheaf D)) 0 = D.comap (fT.fiberι t) :=
    hz.trans (congrArg (fun I => I.comap (fT.fiberι t))
      (Stacks.Divisors.zeroScheme_canonicalSection D))
  rw [AlgebraicGeometry.zeroScheme_zero] at hz'
  rw [← hz'] at hcomap
  exact not_isEffectiveCartierDivisor_bot hcomap

/-- The canonical section of a relative effective Cartier divisor over a surjective affine family
is nonzero at every field point of the base. -/
theorem nonzeroAtFieldPoint_canonicalSection {A : Type u} [CommRing A] {XT : Scheme.{u}}
    (fT : XT ⟶ Spec (.of A)) [Surjective fT] (D : XT.IdealSheafData)
    (hD : IsRelativeEffectiveCartierDivisor fT D) (p : PrimeSpectrum A) :
    Stacks.TwoAffineCech.NonzeroAtFieldPoint fT (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.divisorSheafGlobalSection D) p :=
  nonzeroAtFieldPoint_of_fiberι fT _ _ p (pullbackGlobalSections_canonicalSection_ne_zero fT D hD p)

section Chart

open Stacks.Divisors (divisorSheaf divisorSheafGlobalSection)

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k))
  [IsCurve k fX] [GeometricallyIrreducible fX] [Smooth fX] [IsProper fX]
  (U : Stacks.TwoAffineCech.Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))
  {A : Type u} [CommRing A] [Algebra k A] {XT : Scheme.{u}} (gT : XT ⟶ X)
  (fT : XT ⟶ Spec (.of A))
  (hT : IsPullback gT fT fX (Spec.map (CommRingCat.ofHom (algebraMap k A))))

omit [GeometricallyIrreducible fX] [Smooth fX] in
include hU hUaff hT in
/-- **Two relative effective Cartier divisors with isomorphic normalized invertible sheaves are
equal.** Over an affine base change of the curve, if `𝒪(D₂) ≅ 𝒪(D₁)` and every fibre of
`𝒪(D₁)` has `H¹ = 0` and `dim H⁰ = 1`, then `D₁ = D₂`. -/
theorem eq_of_divisorSheaf_iso (D₁ D₂ : XT.IdealSheafData)
    (hD₁ : IsRelativeEffectiveCartierDivisor fT D₁) (hD₂ : IsRelativeEffectiveCartierDivisor fT D₂)
    (e : divisorSheaf D₂ ≅ divisorSheaf D₁)
    (h1 : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology fT (divisorSheaf D₁) x 1) = 0)
    (h0 : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology fT (divisorSheaf D₁) x 0) = 1) :
    D₁ = D₂ := by
  have := hD₁.1
  have := hD₂.1
  have := surjective_of_isPullback fX _ gT fT hT
  have : Stacks.Ample.IsInvertibleModule XT (divisorSheaf D₁) :=
    Stacks.Divisors.isInvertible_divisorSheaf D₁
  have : Stacks.Ample.IsInvertibleModule XT (divisorSheaf D₂) :=
    Stacks.Divisors.isInvertible_divisorSheaf D₂
  have hs₁ := nonzeroAtFieldPoint_canonicalSection fT D₁ hD₁
  have hs₂ := nonzeroAtFieldPoint_canonicalSection fT D₂ hD₂
  have h1' := fun x => (finrank_fibreCohomology_congr fT e x 1).trans (h1 x)
  have h0' := fun x => (finrank_fibreCohomology_congr fT e x 0).trans (h0 x)
  set σ₁ := divisorSheafGlobalSection D₁
  set σ₂ := divisorSheafGlobalSection D₂
  set β := (Stacks.Cech.baseRingHom fT ⊤).hom
  obtain ⟨r, hr, -⟩ := Stacks.TwoAffineCech.existsUnique_smul_eq_of_fibres fX U hU hUaff gT fT hT
    (divisorSheaf D₁) h1 h0 σ₁ hs₁ (e.hom.app ⊤ σ₂)
  obtain ⟨r', hr', -⟩ := Stacks.TwoAffineCech.existsUnique_smul_eq_of_fibres fX U hU hUaff gT fT hT
    (divisorSheaf D₂) h1' h0' σ₂ hs₂ (e.inv.app ⊤ σ₁)
  have key : σ₂ = β (r * r') • σ₂ :=
    calc σ₂ = e.inv.app ⊤ (e.hom.app ⊤ σ₂) := (Scheme.Modules.app_inv_app e ⊤ σ₂).symm
      _ = e.inv.app ⊤ (β r • σ₁) := by rw [← hr]
      _ = β r • e.inv.app ⊤ σ₁ := Scheme.Modules.Hom.app_smul _ _ _
      _ = β r • (β r' • σ₂) := by rw [← hr']
      _ = β (r * r') • σ₂ := by rw [smul_smul, map_mul]
  obtain ⟨a, -, ha⟩ := Stacks.TwoAffineCech.existsUnique_smul_eq_of_fibres fX U hU hUaff gT fT hT
    (divisorSheaf D₂) h1' h0' σ₂ hs₂ σ₂
  have hrr : r * r' = 1 := (ha _ key).trans (ha 1 (by rw [map_one, one_smul] : σ₂ = β 1 • σ₂)).symm
  have hunit : IsUnit (β r) := IsUnit.of_mul_eq_one (β r') (by rw [← map_mul, hrr, map_one])
  have hiso := zeroScheme_eq_of_iso e (s := σ₂) (t := e.hom.app ⊤ σ₂) rfl
  rw [hr, zeroScheme_smul_of_isUnit _ _ hunit,
    Stacks.Divisors.zeroScheme_canonicalSection,
    Stacks.Divisors.zeroScheme_canonicalSection] at hiso
  exact hiso.symm

end Chart

end Stacks.PicardCurve
