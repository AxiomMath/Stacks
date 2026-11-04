module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientSections
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.AssemblyStructureSheaf

/-!
# Sections of `𝒪 / Jᵐ𝒪` on a base change of a proper scheme with `Γ = k`

Let `k` be a field, `f : X ⟶ Spec k` proper with `k ≅ Γ(X, 𝒪_X)`, and `F = X ×_k Spec R` for a
ring `R` with a map `Spec R ⟶ Spec k`. For every ideal `J ⊆ R` and exponent `m`, every global
section of `𝒪_F / Jᵐ𝒪_F` lifts to a global function on `F`.

This is the face input of the thickening induction of the cube proof (step
1(a)): on a face `A × Spec R` on which the invertible module is trivial, sections of
`ℒ / Iⁿ⁺¹ℒ` lift to `ℒ / Iⁿ⁺²ℒ`.

## Main results

* `Stacks.CubeOpenAtUnit.surjective_appTop_pullback_fst_quotient`: the restriction
  `Γ(F, 𝒪) ⟶ Γ(F ×_R Spec (R / J), 𝒪)` is surjective.
* `Stacks.CubeOpenAtUnit.surjective_quoπ_unit_app_top`: the projection
  `Γ(F, 𝒪) ⟶ Γ(F, 𝒪 / Jᵐ𝒪)` is surjective.

## Implementation notes

`Γ(F, 𝒪 / Jᵐ𝒪)` is the ring of functions on the closed subscheme cut out by `(J𝒪_F)ᵐ`
(`Stacks.Cohomology.FormalFunctions.idealPowerQuotientSectionsIso_hom_app_top_π`), which is
`F ×_R Spec (R / Jᵐ)` (`Stacks.Cohomology.FormalFunctions.idealPowerSubschemeIsoPullback`). That
fibre product is the base change of `f` along the flat `Spec (R / Jᵐ) ⟶ Spec k`, so its functions
are `Γ(Spec (R / Jᵐ), 𝒪) = R / Jᵐ` (`Stacks.Groupoids.isIso_app_pullback_snd_of_isIso_appTop`,
flat base change in degree zero), and `R ⟶ R / Jᵐ` is onto.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace Stacks.CubeOpenAtUnit

/-- The map on global functions `Γ(Spec R, 𝒪) ⟶ Γ(Spec (R / J), 𝒪)` is surjective. -/
theorem surjective_appTop_specMap_quotient {R : Type u} [CommRing R] (J : Ideal R) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have hbij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom
  intro y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom y)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv r, hbij.1 ?_⟩
  rwa [← CommRingCat.comp_apply, h, CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- The map on global functions induced by an isomorphism of schemes is surjective. -/
private theorem surjective_appTop_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Function.Surjective f.appTop :=
  have : IsIso f.appTop := inferInstanceAs (IsIso (f.app ⊤))
  (ConcreteCategory.bijective_of_isIso f.appTop).2

/-- For `F = X ×_k Spec R` with `f : X ⟶ Spec k` quasi-compact and quasi-separated and
`k ≅ Γ(X, 𝒪)`, the restriction `Γ(F, 𝒪) ⟶ Γ(F ×_R Spec (R / J), 𝒪)` is surjective. -/
theorem surjective_appTop_pullback_fst_quotient {k : Type u} [Field k] {X F : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X] [IsIso fX.appTop]
    {R : Type u} [CommRing R] (s : Spec (.of R) ⟶ Spec (.of k))
    (p : F ⟶ X) (g : F ⟶ Spec (.of R)) (hsq : IsPullback p g fX s) (J : Ideal R) :
    Function.Surjective
      (pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).appTop := by
  set πs := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have H : IsPullback (pullback.fst g πs ≫ p) (pullback.snd g πs) fX (πs ≫ s) :=
    (IsPullback.of_hasPullback g πs).paste_horiz hsq
  have hflat : Flat (πs ≫ s) := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mpr
    (RingHom.Flat.of_isField (MulEquiv.isField (Field.toIsField k)
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv) _)
  have hiso : IsIso (pullback.snd fX (πs ≫ s)).appTop :=
    Stacks.Groupoids.isIso_app_pullback_snd_of_isIso_appTop fX (πs ≫ s) ⊤
      (by simpa using isCompact_univ)
      (by simpa using isQuasiSeparated_univ)
  have hsnd : Function.Surjective (pullback.snd g πs).appTop := by
    rw [← H.isoPullback_hom_snd, Scheme.Hom.comp_appTop]
    exact (surjective_appTop_of_isIso H.isoPullback.hom).comp
      (ConcreteCategory.bijective_of_isIso (pullback.snd fX (πs ≫ s)).appTop).2
  intro y
  obtain ⟨c, rfl⟩ := hsnd y
  obtain ⟨a, rfl⟩ := surjective_appTop_specMap_quotient J c
  refine ⟨g.appTop a, ?_⟩
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, pullback.condition]

/-- **Sections of `𝒪_F / Jᵐ𝒪_F` lift to `F`.** For `F = X ×_k Spec R` with `X` proper over the
field `k` and `k ≅ Γ(X, 𝒪_X)`, every global section of `𝒪_F / Jᵐ𝒪_F` is the image of a global
function on `F`, for every ideal `J ⊆ R` and exponent `m`. -/
theorem surjective_quoπ_unit_app_top {k : Type u} [Field k] {X F : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) [IsProper fX] [IsIso fX.appTop]
    {R : Type u} [CommRing R] (s : Spec (.of R) ⟶ Spec (.of k))
    (p : F ⟶ X) (g : F ⟶ Spec (.of R)) (hsq : IsPullback p g fX s) (J : Ideal R) (m : ℕ) :
    Function.Surjective ((cokernel.π (C := F.Modules)
      (Stacks.Algebraization.idealPowerMultiple (baseIdealSheaf R J g) m
        (SheafOfModules.unit F.ringCatSheaf)).ι).app ⊤) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated fX
  -- the closed subscheme cut out by `(J𝒪_F)ᵐ` is `F ×_R Spec (R / Jᵐ)`
  have he : (Stacks.Cohomology.FormalFunctions.idealPowerSubschemeIsoPullback R g J m).hom ≫
      pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ m)))) =
        (baseIdealSheaf R J g ^ m).subschemeι := by
    simp only [Stacks.Cohomology.FormalFunctions.idealPowerSubschemeIsoPullback, Iso.trans_hom,
      eqToIso.hom, Category.assoc]
    rw [Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback_hom_fst]
    exact Stacks.PuncturedSpectrumPicard.subscheme_eqToHom_comp_subschemeι _ _
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf_pow R J g m).symm
  have hι : Function.Surjective (baseIdealSheaf R J g ^ m).subschemeι.appTop := by
    rw [← he, Scheme.Hom.comp_appTop, ConcreteCategory.coe_comp]
    exact (surjective_appTop_of_isIso
      (Stacks.Cohomology.FormalFunctions.idealPowerSubschemeIsoPullback R g J m).hom).comp
      (surjective_appTop_pullback_fst_quotient fX s p g hsq (J ^ m))
  -- `Γ(F, 𝒪 / Jᵐ𝒪)` is the ring of functions on that subscheme
  let e := Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeIso
    (baseIdealSheaf R J g) m
  have hinj : Function.Injective (e.hom.app ⊤) :=
    Function.LeftInverse.injective (g := e.inv.app ⊤) fun c => by
      show (e.hom ≫ e.inv).app ⊤ c = c
      rw [e.hom_inv_id]
      rfl
  intro q
  obtain ⟨x, hx⟩ := hι (e.hom.app ⊤ q)
  exact ⟨x, hinj <|
    (Stacks.Cohomology.FormalFunctions.idealPowerQuotientSectionsIso_hom_app_top_π R g J m x).trans
      hx⟩

/-- Surjectivity of `Γ(M) ⟶ Γ(M / 𝓘ᵐM)` is invariant under isomorphism of modules. -/
theorem surjective_π_app_top_of_iso {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    {M M' : Y.Modules} (e : M ≅ M')
    (h : Function.Surjective ((cokernel.π (C := Y.Modules)
      (Stacks.Algebraization.idealPowerMultiple I m M').ι).app ⊤)) :
    Function.Surjective ((cokernel.π (C := Y.Modules)
      (Stacks.Algebraization.idealPowerMultiple I m M).ι).app ⊤) := by
  let φ := Stacks.Algebraization.idealPowerQuotientMap I I m m le_rfl e.hom
  let ψ := Stacks.Algebraization.idealPowerQuotientMap I I m m le_rfl e.inv
  intro y
  obtain ⟨x', hx'⟩ := h (φ.app ⊤ y)
  refine ⟨e.inv.app ⊤ x', ?_⟩
  calc (cokernel.π (C := Y.Modules)
        (Stacks.Algebraization.idealPowerMultiple I m M).ι).app ⊤ (e.inv.app ⊤ x')
      = (e.inv ≫ cokernel.π (C := Y.Modules)
          (Stacks.Algebraization.idealPowerMultiple I m M).ι).app ⊤ x' := rfl
    _ = (cokernel.π (C := Y.Modules)
          (Stacks.Algebraization.idealPowerMultiple I m M').ι ≫ ψ).app ⊤ x' := by
        rw [Stacks.Algebraization.idealPowerQuotientMap_π]
    _ = ψ.app ⊤ (φ.app ⊤ y) := by
        rw [← hx']
        rfl
    _ = (φ ≫ ψ).app ⊤ y := rfl
    _ = y := by
        rw [← Stacks.Algebraization.idealPowerQuotientMap_comp, e.hom_inv_id,
          Stacks.Algebraization.idealPowerQuotientMap_id]
        rfl

/-- **Sections of a trivial module lift through the thickenings of a face.** For `F` as in
`surjective_quoπ_unit_app_top` and a module `G'` on `F` isomorphic to `𝒪_F`, the map
`Γ(F, G' / Jⁿ⁺²G') ⟶ Γ(F, G' / Jⁿ⁺¹G')` is surjective. -/
theorem surjective_quoDrop_app_top_of_iso_unit {k : Type u} [Field k] {X F : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) [IsProper fX] [IsIso fX.appTop]
    {R : Type u} [CommRing R] (s : Spec (.of R) ⟶ Spec (.of k))
    (p : F ⟶ X) (g : F ⟶ Spec (.of R)) (hsq : IsPullback p g fX s) (J : Ideal R)
    (G' : F.Modules) (e : G' ≅ SheafOfModules.unit F.ringCatSheaf) (n : ℕ) :
    Function.Surjective ((Stacks.Algebraization.idealPowerQuotientDrop (baseIdealSheaf R J g)
      (Nat.le_succ (n + 1)) G').app ⊤) := by
  intro y
  obtain ⟨x, rfl⟩ := surjective_π_app_top_of_iso (baseIdealSheaf R J g) (n + 1) e
    (surjective_quoπ_unit_app_top fX s p g hsq J (n + 1)) y
  refine ⟨(cokernel.π (C := F.Modules)
    (Stacks.Algebraization.idealPowerMultiple (baseIdealSheaf R J g) (n + 1 + 1) G').ι).app ⊤ x,
    ?_⟩
  show (cokernel.π (C := F.Modules)
    (Stacks.Algebraization.idealPowerMultiple (baseIdealSheaf R J g) (n + 1 + 1) G').ι ≫
      Stacks.Algebraization.idealPowerQuotientDrop (baseIdealSheaf R J g)
        (Nat.le_succ (n + 1)) G').app ⊤ x = _
  rw [Stacks.Algebraization.idealPowerQuotientDrop_π]

end Stacks.CubeOpenAtUnit

end
