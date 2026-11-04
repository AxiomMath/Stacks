module

public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeAcyclic
public import StacksFrontier.AlgebraicGeometry.Conormal.AffineSections
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic

/-!
# Global sections over an affine open of the base, restricted to the fibres

Let `π : Y ⟶ T` be proper and flat, `V ⊆ T` an affine open and `ℒ` an invertible `𝒪_Y`-module
with no higher cohomology on `π⁻¹(V)`. Read `π⁻¹(V)` as a scheme over `Spec Γ(T, V)`. For a point
`t ∈ V` the fibre `Y_t` is the base change of `π⁻¹(V)` along `Spec κ(t) ⟶ Spec Γ(T, V)`
(`AlgebraicGeometry.isPullback_fiberιOfMem`), so cohomology and base change
(`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.cohomologyBaseChange_of_vanishing`) applies:
`Γ(π⁻¹(V), ℒ) ⊗ κ(t) ≅ Γ(Y_t, ℒ_t)` and `ℒ_t` has no higher cohomology.

The consequence used in the proof of [Stacks, Tag 0B9X]: if the restriction to `π⁻¹(V)` of a
global section `s` of `ℒ` is sent to `1` by a `Γ(T, V)`-linear form on `Γ(π⁻¹(V), ℒ)`, then `s`
does not vanish identically on any fibre over `V`; and if that linear form is bijective, every
fibre over `V` has `h⁰(ℒ_t) = 1`.

## Main results

* `AlgebraicGeometry.isPullback_fiberιOfMem`: the fibre square over `Spec Γ(T, V)`.
* `AlgebraicGeometry.map_baseRingHom_morphismRestrict`: the `Γ(T, V)`-module structure of the
  sections over `π⁻¹(V)` is the one through `π^♯`.
* `AlgebraicGeometry.pullbackGlobalSections_fiberι_ne_zero`: nonvanishing on the fibres.
* `AlgebraicGeometry.cohomologyOverField_fiber_of_bijective`: the cohomology of the fibres.

No Stacks tag is attached; these are steps of the proof of [Stacks, Tag 0B9X].

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

section FibreSquare

variable {Y T : Scheme.{u}} (π : Y ⟶ T) {V : T.Opens} (hV : IsAffineOpen V) (t : T) (ht : t ∈ V)

/-- The ring map `Γ(T, V) ⟶ κ(t)` for a point `t` of an open `V`. -/
abbrev residueOfMem : Γ(T, V) ⟶ T.residueField t :=
  T.presheaf.germ V t ht ≫ T.residue t

/-- The point `Spec κ(t) ⟶ T` of a point of an affine open `V` factors through `Spec Γ(T, V)`. -/
theorem fromSpecResidueField_eq_of_mem :
    T.fromSpecResidueField t = Spec.map (residueOfMem t ht) ≫ hV.isoSpec.inv ≫ V.ι := by
  rw [IsAffineOpen.isoSpec_inv_ι, Scheme.fromSpecResidueField,
    ← hV.fromSpecStalk_eq_fromSpecStalk ht, IsAffineOpen.fromSpecStalk, Spec.map_comp,
    Category.assoc]

/-- The lift of the inclusion of the fibre over a point `t ∈ V` into `π⁻¹(V)`. -/
def fiberιOfMem : π.fiber t ⟶ (π ⁻¹ᵁ V).toScheme :=
  IsOpenImmersion.lift (π ⁻¹ᵁ V).ι (π.fiberι t) (by
    rw [Scheme.Hom.range_fiberι, Scheme.Opens.range_ι]
    intro y hy
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
    change π y ∈ V
    rw [hy]
    exact ht)

/-- Composing `fiberιOfMem` with the inclusion `π⁻¹(V) ⟶ Y` gives the inclusion of the fibre. -/
@[reassoc (attr := simp)]
theorem fiberιOfMem_ι : fiberιOfMem π t ht ≫ (π ⁻¹ᵁ V).ι = π.fiberι t :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The fibre over a point of an affine open is the base change of `π⁻¹(V) ⟶ Spec Γ(T, V)`
along `Spec κ(t) ⟶ Spec Γ(T, V)`.** -/
theorem isPullback_fiberιOfMem :
    IsPullback (fiberιOfMem π t ht) (π.fiberToSpecResidueField t) ((π ∣_ V) ≫ hV.isoSpec.hom)
      (Spec.map (residueOfMem t ht)) := by
  have hbig : IsPullback (π.fiberι t) (π.fiberToSpecResidueField t) π
      (T.fromSpecResidueField t) := IsPullback.of_hasPullback _ _
  have hright := (isPullback_morphismRestrict π V).flip
  have hleft : IsPullback (fiberιOfMem π t ht) (π.fiberToSpecResidueField t) (π ∣_ V)
      (Spec.map (residueOfMem t ht) ≫ hV.isoSpec.inv) := by
    refine IsPullback.of_right ?_ ?_ hright
    · simpa [fromSpecResidueField_eq_of_mem hV t ht] using hbig
    · rw [← cancel_mono V.ι]
      simp only [Category.assoc, morphismRestrict_ι, fiberιOfMem_ι_assoc, Scheme.Hom.fiber_fac]
      rw [fromSpecResidueField_eq_of_mem hV t ht]
  exact hleft.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) hV.isoSpec (by simp) (by simp)
    (by simp) (by simp)



end FibreSquare


/-- A base change of a module sends an element on which some linear form takes the value `1`
to a nonzero element, as soon as the new ring is nontrivial. -/
theorem ne_zero_of_isBaseChange_of_eq_one {A B M N : Type*} [CommRing A] [CommRing B]
    {_ : Algebra A B} [Nontrivial B] [AddCommGroup M] {_ : Module A M} [AddCommGroup N]
    {_ : Module A N} {_ : Module B N} {_ : IsScalarTower A B N} {φ : M →ₗ[A] N}
    (hφ : IsBaseChange B φ) (ℓ : M →ₗ[A] A) {m : M} (hm : ℓ m = 1) : φ m ≠ 0 := by
  intro h
  have := hφ.lift_eq ((Algebra.linearMap A B) ∘ₗ ℓ) m
  rw [h, map_zero] at this
  simp [hm] at this

/-- A base change of a free module of rank one is free of rank one. -/
theorem finrank_eq_one_of_isBaseChange {A B M N : Type*} [CommRing A] [Field B]
    {_ : Algebra A B} [AddCommGroup M] {_ : Module A M} [AddCommGroup N]
    {_ : Module A N} {_ : Module B N} {_ : IsScalarTower A B N} {φ : M →ₗ[A] N}
    (hφ : IsBaseChange B φ) (ℓ : M ≃ₗ[A] A) : Module.finrank B N = 1 := by
  rw [(hφ.equiv.symm.trans ((LinearEquiv.baseChange A B _ _ ℓ).trans
    (Algebra.TensorProduct.rid A B B).toLinearEquiv)).finrank_eq, Module.finrank_self]

variable {Y T : Scheme.{u}} (π : Y ⟶ T) {V : T.Opens} (hV : IsAffineOpen V)

/-- The structural ring map of `π⁻¹(V) ⟶ Spec Γ(T, V)`, read in `Γ(Y, π⁻¹(V))`, is `π^♯`. -/
theorem map_baseRingHom_morphismRestrict (a : Γ(T, V)) :
    Y.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op
      (((π ⁻¹ᵁ V).ι.appIso ⊤).inv
        ((Stacks.Cech.baseRingHom ((π ∣_ V) ≫ hV.isoSpec.hom) ⊤).hom a)) = π.app V a := by
  have key := congr($(Stacks.Immersion.appLE_eq_ΓSpecIso_inv_comp_appTop π V hV) a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
  have h2 : (Stacks.Cech.baseRingHom ((π ∣_ V) ≫ hV.isoSpec.hom) ⊤).hom a =
      (((π ∣_ V) ≫ hV.isoSpec.hom).appTop).hom ((Scheme.ΓSpecIso Γ(T, V)).inv.hom a) := by
    simp only [Stacks.Cech.baseRingHom, Stacks.Cech.globalRingHom, CommRingCat.hom_comp,
      RingHom.comp_apply]
    exact congr($((↑(π ⁻¹ᵁ V) : Scheme).presheaf.map_id (op ⊤)) _)
  rw [h2, ← key, Scheme.Opens.ι_appIso]
  show (Y.presheaf.map _ ≫ Y.presheaf.map _) (π.app V a) = _
  rw [← Functor.map_comp]
  exact congr($((Y.presheaf.map_id _).symm.trans (congrArg _ (Subsingleton.elim _ _))) _).symm

/-- **A linear form taking the value `1` on the restriction of a section.** Let `V` be an
affine open of `T` and `λ : Γ(π⁻¹(V), L) ⟶ Γ(T, V)` a `Γ(T, V)`-linear form sending the restriction
of a global section `s` of `L` to `1`. Then on the open subscheme `π⁻¹(V)`, viewed over
`Spec Γ(T, V)`, the pullback of `s` is sent to `1` by a linear form. -/
theorem exists_linearMap_pullbackGlobalSections_eq_one (L : Y.Modules) (s : Γ(L, ⊤))
    (lam : Γ(L, π ⁻¹ᵁ V) →+ Γ(T, V))
    (hlam : ∀ (a : Γ(T, V)) (z : Γ(L, π ⁻¹ᵁ V)), lam (π.app V a • z) = a * lam z)
    (hs : lam (L.presheaf.map (homOfLE le_top).op s) = 1) :
    letI := Stacks.Cech.sectionsModule ((π ∣_ V) ≫ hV.isoSpec.hom)
      ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) ⊤
    ∃ ℓ : Γ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L, ⊤) →ₗ[Γ(T, V)] Γ(T, V),
      ℓ (pullbackGlobalSections (π ⁻¹ᵁ V).ι L s) = 1 ∧
        (Function.Bijective lam → Function.Bijective ℓ) := by
  let := Stacks.Cech.sectionsModule ((π ∣_ V) ≫ hV.isoSpec.hom)
    ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) ⊤
  let ρ : Γ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L, ⊤) →+ Γ(L, π ⁻¹ᵁ V) :=
    (L.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op).hom.comp
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L)
        ⊤).hom
  refine ⟨{
    toFun := fun x => lam (ρ x)
    map_add' := fun x y => by rw [map_add, map_add]
    map_smul' := fun a x => ?_ }, ?_, fun hb => hb.comp ?_⟩
  · show lam (L.presheaf.map _
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L)
        ⊤ ((Stacks.Cech.baseRingHom ((π ∣_ V) ≫ hV.isoSpec.hom) ⊤).hom a • x))) = a * lam (ρ x)
    rw [Scheme.Modules.Hom.app_smul]
    show lam (L.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op
      ((((π ⁻¹ᵁ V).ι.appIso ⊤).inv
          ((Stacks.Cech.baseRingHom ((π ∣_ V) ≫ hV.isoSpec.hom) ⊤).hom a) •
        (show Γ(L, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) from Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L) ⊤ x) :
          Γ(L, (π ⁻¹ᵁ V).ι ''ᵁ ⊤)))) = _
    rw [Scheme.Modules.map_smul, map_baseRingHom_morphismRestrict π hV a]
    exact hlam a _
  · have hpb : pullbackGlobalSections (π ⁻¹ᵁ V).ι L s =
        Scheme.Modules.pullbackSection (π ⁻¹ᵁ V).ι L ⊤ ⊤ le_top s := by
      unfold pullbackGlobalSections Scheme.Modules.pullbackSection
      exact congrArg (fun i => ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L).presheaf.map i _)
        (Subsingleton.elim _ _)
    have hres := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection (π ⁻¹ᵁ V).ι L ⊤ ⊤
      le_top le_top s
    have h4 : ρ (pullbackGlobalSections (π ⁻¹ᵁ V).ι L s) =
        L.presheaf.map (homOfLE le_top).op s := by
      show L.presheaf.map _ (Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L) ⊤
        (pullbackGlobalSections (π ⁻¹ᵁ V).ι L s)) = _
      rw [hpb, show Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L) ⊤
          (Scheme.Modules.pullbackSection (π ⁻¹ᵁ V).ι L ⊤ ⊤ le_top s) =
          L.presheaf.map (homOfLE (le_top : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ ≤ ⊤)).op s from hres]
      have hcomp : ∀ {W₁ W₂ W₃ : Y.Opens} (i : op W₂ ⟶ op W₃) (j : op W₁ ⟶ op W₂) (z : Γ(L, W₁)),
          L.presheaf.map i (L.presheaf.map j z) = L.presheaf.map (j ≫ i) z := fun i j z => by
        rw [Functor.map_comp]; rfl
      exact (hcomp _ _ s).trans (congrArg (fun k => L.presheaf.map k s) (Subsingleton.elim _ _))
    show lam (ρ _) = 1
    rw [h4, hs]
  · refine (ConcreteCategory.bijective_of_isIso
      (L.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op)).comp ?_
    exact ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L) ⊤)

/-- The pullback of an invertible module on `Y` to `π⁻¹(V)` is quasi-coherent and flat over
`Spec Γ(T, V)`. -/
private theorem isQuasicoherent_and_isFlatOver_pullback_restrict [Flat π] (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L).IsQuasicoherent ∧
      IsFlatOver ((π ∣_ V) ≫ hV.isoSpec.hom).toLRSHom.toShHom
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) := by
  have hF : Stacks.SheafOfModules.IsInvertible (π ⁻¹ᵁ V).toScheme.presheaf
      (π ⁻¹ᵁ V).toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of (π ⁻¹ᵁ V).ι.toLRSHom.toShHom L hL
  exact ⟨Stacks.Picard.isQuasicoherent_of_isInvertible _ hF,
    (ProperFlatFibreEulerCharacteristic.isFinitePresentation_and_isFlatOver_of_isInvertible
      _ _ hF).2⟩

include hV in
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic in
/-- **A section which is a free generator over an affine open of the base is nonzero on the fibres
over that open.** Let `π : Y ⟶ T` be proper and flat and `L` an invertible `𝒪_Y`-module without
higher cohomology over an affine open `V` of `T`. If the restriction of a global section `s` of `L`
to `π⁻¹(V)` is sent to `1` by a `Γ(T, V)`-linear form, then `s` does not vanish identically on the
fibre over any point of `V`. This is cohomology and base change in degree zero. -/
theorem pullbackGlobalSections_fiberι_ne_zero [IsProper π] [Flat π] (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    (hvan : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)))
    (s : Γ(L, ⊤)) (lam : Γ(L, π ⁻¹ᵁ V) →+ Γ(T, V))
    (hlam : ∀ (a : Γ(T, V)) (z : Γ(L, π ⁻¹ᵁ V)), lam (π.app V a • z) = a * lam z)
    (hs : lam (L.presheaf.map (homOfLE le_top).op s) = 1) (t : T) (ht : t ∈ V) :
    pullbackGlobalSections (π.fiberι t) L s ≠ 0 := by
  set ι := (π ⁻¹ᵁ V).ι
  set F := (Scheme.Modules.pullback ι).obj L
  set f := (π ∣_ V) ≫ hV.isoSpec.hom
  obtain ⟨_, hflat⟩ := isQuasicoherent_and_isFlatOver_pullback_restrict π hV L hL
  obtain ⟨-, hbc⟩ :=
    Stacks.AlgebraicGeometry.ProperFlatGlobalSections.cohomologyBaseChange_of_vanishing
      f F hflat hvan (residueOfMem t ht).hom (isPullback_fiberιOfMem π hV t ht)
  obtain ⟨ℓ, hℓ, -⟩ := exists_linearMap_pullbackGlobalSections_eq_one π hV L s lam hlam hs
  have h1 := ne_zero_of_isBaseChange_of_eq_one hbc ℓ hℓ
  rw [Stacks.AlgebraicGeometry.ProperFlatGlobalSections.pullbackSectionsBaseₗ_top_apply] at h1
  have h2 : pullbackSectionHom (fiberιOfMem π t ht) F ⊤ (fiberιOfMem π t ht ⁻¹ᵁ ⊤) le_rfl
      (pullbackGlobalSections (π ⁻¹ᵁ V).ι L s) =
      pullbackGlobalSections (fiberιOfMem π t ht) F (pullbackGlobalSections (π ⁻¹ᵁ V).ι L s) := by
    unfold pullbackSectionHom pullbackGlobalSections
    rfl
  rw [h2] at h1
  rw [← fiberιOfMem_ι π t ht, ← SectionsEqualizer.pullbackGlobalSections_comp]
  intro h3
  apply h1
  have h4 := congrArg (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp (fiberιOfMem π t ht)
    (π ⁻¹ᵁ V).ι).inv.app L) ⊤) h3
  rw [map_zero] at h4
  exact (congrArg (fun k => Scheme.Modules.Hom.app k ⊤ _)
    ((Scheme.Modules.pullbackComp (fiberιOfMem π t ht) (π ⁻¹ᵁ V).ι).hom_inv_id_app L)).symm.trans h4

include hV in
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic in
/-- **The cohomology of a fibre, under the hypotheses of `pullbackGlobalSections_fiberι_ne_zero`,
when the linear form is an isomorphism.** The restriction of `L` to the fibre over a point of `V`
has no higher cohomology and a one-dimensional space of global sections. -/
theorem cohomologyOverField_fiber_of_bijective [IsProper π] [Flat π] (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    (hvan : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)))
    (s : Γ(L, ⊤)) (lam : Γ(L, π ⁻¹ᵁ V) →+ Γ(T, V))
    (hlam : ∀ (a : Γ(T, V)) (z : Γ(L, π ⁻¹ᵁ V)), lam (π.app V a • z) = a * lam z)
    (hs : lam (L.presheaf.map (homOfLE le_top).op s) = 1) (hbij : Function.Bijective lam)
    (t : T) (ht : t ∈ V) :
    (∀ p : ℕ, 0 < p → Subsingleton (cohomologyOverField (T.residueField t)
      (π.fiberToSpecResidueField t) ((Scheme.Modules.pullback (π.fiberι t)).obj L) p)) ∧
    Module.finrank (T.residueField t) (cohomologyOverField (T.residueField t)
      (π.fiberToSpecResidueField t) ((Scheme.Modules.pullback (π.fiberι t)).obj L) 0) = 1 := by
  set ι := (π ⁻¹ᵁ V).ι
  set F := (Scheme.Modules.pullback ι).obj L
  set f := (π ∣_ V) ≫ hV.isoSpec.hom
  obtain ⟨_, hflat⟩ := isQuasicoherent_and_isFlatOver_pullback_restrict π hV L hL
  obtain ⟨hvan', hbc⟩ :=
    Stacks.AlgebraicGeometry.ProperFlatGlobalSections.cohomologyBaseChange_of_vanishing
      f F hflat hvan (residueOfMem t ht).hom (isPullback_fiberιOfMem π hV t ht)
  obtain ⟨ℓ, -, hℓ⟩ := exists_linearMap_pullbackGlobalSections_eq_one π hV L s lam hlam hs
  let eG : (Scheme.Modules.pullback (π.fiberι t)).obj L ≅
      (Scheme.Modules.pullback (fiberιOfMem π t ht)).obj F :=
    (Scheme.Modules.pullbackCongr (fiberιOfMem_ι π t ht)).symm.app L ≪≫
      ((Scheme.Modules.pullbackComp (fiberιOfMem π t ht) ι).app L).symm
  refine ⟨fun p hp => (ModuleCat.subsingleton_of_isZero
    ((@ModuleCat.isZero_of_subsingleton _ _ _ (hvan' p hp)).of_iso
      (((AlgebraicGeometry.moduleGlobalSections (π.fiber t)).rightDerived p).mapIso eG)) :), ?_⟩
  rw [(cohomologyOverFieldZeroLinearIso (T.residueField t) (π.fiberToSpecResidueField t)
    _).toLinearEquiv.finrank_eq, ((restrictScalarsOverBase (T.residueField t)
      (π.fiberToSpecResidueField t)).mapIso
      ((SheafOfModules.evaluation (π.fiber t).ringCatSheaf (op ⊤)).mapIso
        eG)).toLinearEquiv.finrank_eq]
  exact finrank_eq_one_of_isBaseChange hbc (LinearEquiv.ofBijective ℓ (hℓ hbij))

end AlgebraicGeometry

end
