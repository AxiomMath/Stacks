module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.ProperSmoothLocalModel
public import StacksFrontier.AlgebraicGeometry.QuasicoherentAlgebraEqualizer.FiniteEtale
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Basic
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image of the structure sheaf of a proper smooth morphism

Let `f : X ⟶ S` be a proper smooth morphism of schemes. This file proves that the
quasi-coherent `𝒪_S`-algebra `f_*𝒪_X` is finite étale: the structure morphism of its relative
spectrum is finite and étale.

## Main results

* `AlgebraicGeometry.isQuasicoherent_pushforwardAlgebra_of_quasiCompact`: for a quasi-compact
  quasi-separated `f`, the `𝒪_S`-algebra `f_*𝒪_X` is quasi-coherent ([Stacks, Tag 01LC]).
* `AlgebraicGeometry.etale_and_finite_app_of_isPullback`: over an affine open `V` of `S`, the
  structure map `Γ(S, V) ⟶ Γ(X, f⁻¹V)` is étale and finite as soon as the global functions of the
  base change of `X` to `Spec Γ(S, V)` are.
* `AlgebraicGeometry.isFinite_and_etale_relativeSpecToBase_pushforwardAlgebra`: **`f_*𝒪_X` is a
  finite étale `𝒪_S`-algebra** for `f` proper and smooth.

## Implementation notes

Finiteness and étaleness of the relative spectrum are local on `S`
(`AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top`,
`AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`), so they are checked over the affine
opens of a cover, which are chosen inside the neighbourhoods of
`exists_nhds_globalFunctions_finiteEtale_and_split` in the namespace
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections`. Over such an affine open `V` the relative
spectrum restricts to the spectrum of `Γ(X, f⁻¹V)`
(`Stacks.QuasicoherentAlgebraEqualizer.respectsIso_app_relativeSpecToBase`), and `Γ(X, f⁻¹V)` is
identified with the global functions of the base change of `X` to `Spec Γ(S, V)` through the open
immersion of that base change into `X`.

## References

* [Stacks Project, Tag 0G7Y](https://stacks.math.columbia.edu/tag/0G7Y)
* [Stacks Project, Tag 0G8H](https://stacks.math.columbia.edu/tag/0G8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace AlgebraicGeometry

/-- **The direct image of the structure sheaf along a quasi-compact quasi-separated morphism is a
quasi-coherent algebra** ([Stacks, Tag 01LC]). -/
@[ega "I 9.2.2" "special case",
  ega "II 3.7.9" "(ii), special case",
  ega "IV 21.12.1",
  ega "IV 3.1.10.2" "special case",
  sga "3 III 0.13" "F = O_X for qcqs f",
  sga "3 VIB 11.0" "special case"]
theorem isQuasicoherent_pushforwardAlgebra_of_quasiCompact {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f) :=
  AlgebraicGeometry.pushforward_isQuasicoherent f (SheafOfModules.unit X.ringCatSheaf)

/-- If `X'` is the base change of `X` along `Spec Γ(S, V) ⟶ S` for an affine open `V`, then the
preimage of `V` in `X` lies in the range of `X' ⟶ X`. -/
private theorem le_opensRange_of_isPullback {X S X' : Scheme.{u}} {f : X ⟶ S} {V : S.Opens}
    (hV : IsAffineOpen V) {f' : X' ⟶ Spec Γ(S, V)} {j : X' ⟶ X} [IsOpenImmersion j]
    (hsq : IsPullback j f' f hV.fromSpec) : f ⁻¹ᵁ V ≤ j.opensRange := by
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range (pullback.fst f hV.fromSpec) := by
    rwa [Scheme.Pullback.range_fst, hV.range_fromSpec]
  exact ⟨hsq.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_fst]⟩

/-- Let `V` be an affine open of `S` and let `X'` be the base change of `X` along
`Spec Γ(S, V) ⟶ S`, with structure morphism `f'`. Any ring-hom property respecting isomorphisms
that holds for `Γ(S, V) ⟶ Γ(X', 𝒪_{X'})` holds for `Γ(S, V) ⟶ Γ(X, f⁻¹V)`. -/
private theorem respectsIso_app_of_isPullback {X S X' : Scheme.{u}} {f : X ⟶ S} {V : S.Opens}
    (hV : IsAffineOpen V) {f' : X' ⟶ Spec Γ(S, V)} {j : X' ⟶ X}
    (hsq : IsPullback j f' f hV.fromSpec)
    (P : ∀ {R T : Type u} [CommRing R] [CommRing T], (R →+* T) → Prop)
    (hP : RingHom.RespectsIso @P) (hglob : P (Stacks.Cech.globalRingHom f').hom) :
    P (f.app V).hom := by
  have : IsOpenImmersion j :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  have hjapp := Scheme.Hom.isIso_app j (f ⁻¹ᵁ V) (le_opensRange_of_isPullback hV hsq)
  have := Scheme.Hom.isIso_app hV.fromSpec V hV.opensRange_fromSpec.ge
  have hpre : hV.fromSpec ⁻¹ᵁ V = ⊤ := hV.fromSpec_preimage_self
  have hle' : (⊤ : X'.Opens) ≤ (f' ≫ hV.fromSpec) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage, hpre]
    exact le_rfl
  have hle : (⊤ : X'.Opens) ≤ (j ≫ f) ⁻¹ᵁ V := hsq.w ▸ hle'
  have hcomm : (j ≫ f).appLE V ⊤ hle = (f' ≫ hV.fromSpec).appLE V ⊤ hle' := by
    have : ∀ (k : X' ⟶ S) (_ : k = f' ≫ hV.fromSpec) (h₁ : (⊤ : X'.Opens) ≤ k ⁻¹ᵁ V),
        k.appLE V ⊤ h₁ = (f' ≫ hV.fromSpec).appLE V ⊤ hle' := by
      rintro k rfl h₁
      rfl
    exact this _ hsq.w hle
  rw [Scheme.Hom.comp_appLE, Scheme.Hom.comp_appLE] at hcomm
  have hpre' : (⊤ : (Spec Γ(S, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := hpre.ge
  have h3 : f'.appLE (hV.fromSpec ⁻¹ᵁ V) ⊤ hle' =
      (Spec Γ(S, V)).presheaf.map (homOfLE hpre').op ≫ f'.appLE ⊤ ⊤ le_top :=
    (Scheme.Hom.map_appLE f' le_top (homOfLE hpre').op).symm
  have h4 : f'.appLE ⊤ ⊤ le_top = f'.appTop := Scheme.Hom.appLE_eq_app (f := f') (U := ⊤)
  have : IsIso (homOfLE hle) := isIso_homOfLE (le_antisymm hle le_top)
  have : IsIso (homOfLE hpre') := isIso_homOfLE hpre.symm
  have : IsIso (j.appLE (f ⁻¹ᵁ V) ⊤ hle) := by
    change IsIso (j.app (f ⁻¹ᵁ V) ≫ X'.presheaf.map (homOfLE hle).op)
    have : IsIso (X'.presheaf.map (homOfLE hle).op) := inferInstance
    exact IsIso.comp_isIso' hjapp this
  refine (hP.cancel_right_isIso (f.app V) (j.appLE (f ⁻¹ᵁ V) ⊤ hle)).mp ?_
  rw [← CommRingCat.hom_comp, hcomm, CommRingCat.hom_comp]
  refine (hP.cancel_left_isIso _ _).mpr ?_
  rw [h3, CommRingCat.hom_comp]
  refine (hP.cancel_left_isIso _ _).mpr ?_
  rw [h4]
  exact (hP.cancel_left_isIso (toSpecΓ Γ(S, V)) f'.appTop).mp hglob

/-- **Global functions over an affine open, from a base change.** Let `V` be an affine open of
`S` and let `X'` be the base change of `X` along `Spec Γ(S, V) ⟶ S`, with structure morphism
`f'`. If `Γ(X', 𝒪_{X'})` is étale (respectively finite) over `Γ(S, V)`, then so is
`Γ(X, f⁻¹V)`. -/
theorem etale_and_finite_app_of_isPullback {X S X' : Scheme.{u}} {f : X ⟶ S} {V : S.Opens}
    (hV : IsAffineOpen V) {f' : X' ⟶ Spec Γ(S, V)} {j : X' ⟶ X}
    (hsq : IsPullback j f' f hV.fromSpec)
    (hEt : RingHom.Etale (Stacks.Cech.globalRingHom f').hom)
    (hFin : RingHom.Finite (Stacks.Cech.globalRingHom f').hom) :
    RingHom.Etale (f.app V).hom ∧ RingHom.Finite (f.app V).hom :=
  ⟨respectsIso_app_of_isPullback hV hsq _ RingHom.Etale.respectsIso hEt,
    respectsIso_app_of_isPullback hV hsq _ RingHom.finite_respectsIso hFin⟩

/-- For `f : X ⟶ S` proper and smooth, every point of `S` has an affine open neighbourhood `V`
over which `Γ(S, V) ⟶ Γ(X, f⁻¹V)` is étale and finite. -/
private theorem exists_isAffineOpen_mem_etale_and_finite_app {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] (s : S) :
    ∃ (V : S.Opens) (_ : IsAffineOpen V), s ∈ V ∧
      RingHom.Etale (f.app V).hom ∧ RingHom.Finite (f.app V).hom := by
  open Stacks.AlgebraicGeometry.ProperFlatGlobalSections in
  obtain ⟨G, hsG, r, b, H⟩ := exists_nhds_globalFunctions_finiteEtale_and_split f s
  obtain ⟨V, hV, hsV, hVG⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := G) hsG
  obtain ⟨X', f', j, hsq, ⟨hEt, hFin⟩, -⟩ := H V hV hVG
  exact ⟨V, hV, hsV, etale_and_finite_app_of_isPullback hV hsq hEt hFin⟩

/-- **The direct image of the structure sheaf of a proper smooth morphism is a finite étale
algebra.** For `f : X ⟶ S` proper and smooth, the structure morphism of the relative spectrum of
the quasi-coherent `𝒪_S`-algebra `f_*𝒪_X` is finite and étale. -/
theorem isFinite_and_etale_relativeSpecToBase_pushforwardAlgebra {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] :
    letI := isQuasicoherent_pushforwardAlgebra_of_quasiCompact f
    IsFinite (relativeSpecToBase (pushforwardAlgebra f)) ∧
      Etale (relativeSpecToBase (pushforwardAlgebra f)) := by
  let := isQuasicoherent_pushforwardAlgebra_of_quasiCompact f
  choose V hV hsV hP using exists_isAffineOpen_mem_etale_and_finite_app f
  let Uaff : S → S.affineOpens := fun s => ⟨V s, hV s⟩
  have hcover : ⨆ s, (Uaff s : S.Opens) = ⊤ :=
    eq_top_iff.2 fun s _ => Opens.mem_iSup.2 ⟨s, hsV s⟩
  have hrest : ∀ (s : S) (Q : ∀ {R T : Type u} [CommRing R] [CommRing T], (R →+* T) → Prop),
      RingHom.RespectsIso @Q → Q (f.app (V s)).hom →
        Q ((relativeSpecToBase (pushforwardAlgebra f) ∣_ V s).appTop).hom := by
    intro s Q hQ h
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    refine (hQ.arrow_mk_iso_iff (arrowResLEAppIso _ _ _ _)).mpr ?_
    rw [Scheme.Hom.appLE_eq_app]
    exact (Stacks.QuasicoherentAlgebraEqualizer.respectsIso_app_relativeSpecToBase
      (pushforwardAlgebra f) hQ (Uaff s)).mpr h
  have haff : ∀ s, IsAffine (relativeSpecToBase (pushforwardAlgebra f) ⁻¹ᵁ V s) := fun s =>
    (hV s).preimage _
  have : HasAffineProperty @Etale (sourceAffineLocally RingHom.Etale) :=
    HasRingHomProperty.HasAffineProperty @Etale
  have hfinaff : HasAffineProperty @IsFinite.{u}
      (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom) := by
    set_option backward.isDefEq.respectTransparency.types false in infer_instance
  refine ⟨(@HasAffineProperty.iff_of_iSup_eq_top @IsFinite _ hfinaff _ _
      (relativeSpecToBase (pushforwardAlgebra f)) _ Uaff hcover).2 fun s =>
    ⟨haff s, hrest s _ RingHom.finite_respectsIso (hP s).2⟩,
    (HasAffineProperty.iff_of_iSup_eq_top (P := @Etale) (Q := sourceAffineLocally RingHom.Etale)
      Uaff hcover).2 fun s => ?_⟩
  have := haff s
  have : IsAffine (V s : Scheme.{u}) := hV s
  exact (HasAffineProperty.iff_of_isAffine (P := @Etale)).1
    ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).2
      (hrest s _ RingHom.Etale.respectsIso (hP s).1))

end AlgebraicGeometry

end
