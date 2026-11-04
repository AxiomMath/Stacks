module

public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.BoundedCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardBounds
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering

/-!
# The amplitude of `Rf_*` from the vanishing of higher direct images above a degree

Let `f : X ⟶ Y` be quasi-compact and quasi-separated and suppose `Rⁱ f_* F = 0` for every
`i > d` and every quasi-coherent `F` — the hypothesis (2) of [Stacks, Tag 0EX3]. Then for every
object `E` of `D(𝒪_X)` with quasi-coherent cohomology sheaves living in degrees `≤ b`, the
derived direct image `Rf_* E` lives in degrees `≤ b + d`; and consequently the canonical map
`Hⁱ(Rf_* E) ⟶ Hⁱ(Rf_*(τ_{≥ b} E))` is an isomorphism for every `i ≥ b + d`.

No quasi-compactness is asked of `Y`: the bound is read off over the affine opens `V ⊆ Y`, where
`Hᵖ(f⁻¹V, F)` is the module of sections of `Rᵖ f_* F` restricted to `V` ([Stacks, Tag 01XK]
along `f ∣_ V`, with [Stacks, Tag 01E5] for the restriction), so it vanishes for `p > d`; and
[Stacks, Tag 08D4] bounds the hypercohomology over `f⁻¹ V`, which is
`AlgebraicGeometry.isZero_homology_derivedPushforward_of_isBasis`.

This is the input that lets the top-degree conclusions (b) and (c) of [Stacks, Tag 0EX3] be read
in the derived category: it shows that `Hᵈ(Rf_* -)` only sees `τ_{≥ 0}` of a complex living in
degrees `≤ 0`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_homology_derivedPushforward_of_isLE`:
  `Hᵐ(Rf_* E) = 0` for `m > b + d`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_homology_derivedPushforward_truncGEπ`:
  `Hⁱ(Rf_* E) ⟶ Hⁱ(Rf_*(τ_{≥ b} E))` is an isomorphism for `i ≥ b + d`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit)

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnboundedHigherDirectImage.isGrothendieckAbelian_moduleSheaves

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Cohomology over the inverse image of an affine open vanishes above `d`.** If the higher
direct images of quasi-coherent modules along `f` vanish above `d`, then for an affine open
`V ⊆ Y` and a quasi-coherent `M` the higher right derived functors of sections over `f⁻¹ V`
vanish at `M` above `d`. -/
theorem isZero_rightDerivedPlus_secF_preimage_of_vanishing [QuasiCompact f] [QuasiSeparated f]
    (d : ℕ) (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (V : Y.Opens) (hV : IsAffineOpen V) (M : X.Modules) (hM : M.IsQuasicoherent)
    (p : ℤ) (hp : ((d + 1 : ℕ) : ℤ) ≤ p) :
    IsZero (((secF X.ringCatSheaf (f ⁻¹ᵁ V)).rightDerivedPlus p).obj M) := by
  have : M.IsQuasicoherent := hM
  have : (secF X.ringCatSheaf (f ⁻¹ᵁ V)).Additive := secFAdditive X.ringCatSheaf (f ⁻¹ᵁ V)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p = (k : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (secF X.ringCatSheaf (f ⁻¹ᵁ V)) hk M).2 ?_
  have : IsAffine V.toScheme := hV
  have : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ V).ι M
  have h1 : IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (k : ℤ)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) :=
    IsZero.of_iso ((Scheme.Modules.restrictFunctor V.ι).map_isZero (hvan k (by omega) M hM))
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f V k M)
  have h2 := isZero_cohomology_of_isZero_rightDerivedPlus_pushforward (f ∣_ V) (k : ℤ) _ h1
  have h3 := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (f ⁻¹ᵁ V).toScheme.ringCatSheaf ⊤ k _).1
    ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (f ⁻¹ᵁ V).toScheme) k _).2 h2)
  exact h3.of_iso (Stacks.LocalCohomology.hgroupRestrictIso X (f ⁻¹ᵁ V) k M)

/-- **The amplitude of `Rf_*` on `D_QCoh`.** If `f` is quasi-compact and quasi-separated and the
higher direct images of quasi-coherent modules along `f` vanish above `d`, then for `E` with
quasi-coherent cohomology sheaves living in degrees `≤ b`, `Hᵐ(Rf_* E) = 0` for `m > b + d`. -/
theorem isZero_homology_derivedPushforward_of_isLE [QuasiCompact f] [QuasiSeparated f]
    (d : ℕ) (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) (m : ℤ) (hm : b + d < m) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) m).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj E)) :=
  AlgebraicGeometry.isZero_homology_derivedPushforward_of_isBasis f (N := d + 1)
    Y.isBasis_affineOpens
    (fun V hV M hM p hp ↦
      isZero_rightDerivedPlus_secF_preimage_of_vanishing f d hvan V hV M hM p hp)
    E hcoh b hE m (by push_cast; omega)

/-- **`Rf_*` does not see a truncation from below in high degrees.** Under the hypotheses of
`isZero_homology_derivedPushforward_of_isLE`, for `E` with quasi-coherent cohomology sheaves the
canonical map `Hⁱ(Rf_* E) ⟶ Hⁱ(Rf_*(τ_{≥ b} E))` is an isomorphism for every `i ≥ b + d`.

The truncation triangle `τ_{≤ b-1} E ⟶ E ⟶ τ_{≥ b} E` goes to a distinguished triangle under
`Rf_*`, whose first vertex lives in degrees `≤ b - 1 + d`. -/
theorem isIso_homology_derivedPushforward_truncGEπ [QuasiCompact f] [QuasiSeparated f]
    (d : ℕ) (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (b i : ℤ) (hi : b + d ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
        ((derivedPushforward f.toLRSHom.toShHom).map
          ((DerivedCategory.TStructure.t.truncGEπ b).app E))) := by
  have hP := AlgebraicGeometry.containsZero_isQuasicoherent X
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X.toRingedSpace)
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f.toLRSHom.toShHom).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated
      (RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom) _
      (derivedPushforwardUnit f.toLRSHom.toShHom)
  let T := (derivedPushforward f.toLRSHom.toShHom).mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E)
  have hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :=
    (derivedPushforward f.toLRSHom.toShHom).map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E)
  have hcoh₁ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
        ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E)).IsQuasicoherent :=
    @Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj _ _ _ _
      (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)) _ hP E hcoh (b - 1)
  have hle : ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E).IsLE (b - 1) :=
    DerivedCategory.TStructure.t.isLE_truncLE_obj E (b - 1) (b - 1) le_rfl
  have hz : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj T.obj₁) :=
    isZero_homology_derivedPushforward_of_isLE f d hvan _ hcoh₁ (b - 1) hle i (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (i + 1)).obj T.obj₁) :=
    isZero_homology_derivedPushforward_of_isLE f d hvan _ hcoh₁ (b - 1) hle (i + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing Y.toRingedSpace)) 0).homologySequence_mono_shift_map_mor₂_iff
      T hT i).2 (hz.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing Y.toRingedSpace)) 0).homologySequence_epi_shift_map_mor₂_iff
      T hT i (i + 1) rfl).2 (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₂)

/-- **`Hⁱ(Rf_* -)` for `i ≥ d` only sees `H⁰` of a complex living in degrees `≤ 0`.** Under the
hypotheses of `isZero_homology_derivedPushforward_of_isLE`, let `E` have quasi-coherent
cohomology sheaves and live in degrees `≤ 0`, let `M` be a module and `φ : E ⟶ M[0]` a morphism
inducing an isomorphism on `H⁰`. Then `Hⁱ(Rf_* φ)` is an isomorphism for every `i ≥ d`.

`φ` is the truncation `E ⟶ τ_{≥ 0} E` followed by an isomorphism, because `τ_{≥ 0} E` and `M[0]`
both have their cohomology in degree `0` alone, and `isIso_homology_derivedPushforward_truncGEπ`
handles the truncation. -/
theorem isIso_homology_derivedPushforward_map_of_isIso_homology_zero
    [QuasiCompact f] [QuasiSeparated f]
    (d : ℕ) (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (hE : E.IsLE 0) (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (φ : E ⟶ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)
    (hφ : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).map φ))
    (i : ℤ) (hi : (d : ℤ) ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
        ((derivedPushforward f.toLRSHom.toShHom).map φ)) := by
  let t :=
    DerivedCategory.TStructure.t (C := SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  have hsq := t.truncGEπ_naturality 0 φ
  have hπM : IsIso ((t.truncGEπ 0).app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) :=
    (t.isGE_iff_isIso_truncGEπ_app 0 _).1 inferInstance
  have hτ : IsIso ((t.truncGE 0).map φ) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    by_cases hn : 0 ≤ n
    · have h1 := DerivedCategory.isIso_homologyMap_truncGEπ_app 0 n hn E
      have h2 := DerivedCategory.isIso_homologyMap_truncGEπ_app 0 n hn
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)
      have hφn : IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).map φ) := by
        rcases hn.eq_or_lt with rfl | hlt
        · exact hφ
        · exact ⟨0, (DerivedCategory.isZero_of_isLE E 0 n hlt).eq_of_src _ _,
            (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)
              0 n hlt).eq_of_src _ _⟩
      have := congrArg (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).map hsq
      simp only [Functor.map_comp] at this
      have h3 : IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).map
          ((t.truncGEπ 0).app E) ≫
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).map
              ((t.truncGE 0).map φ)) := by
        rw [this]; infer_instance
      exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).map ((t.truncGEπ 0).app E)) _
    · push Not at hn
      exact ⟨0, (DerivedCategory.isZero_of_isGE ((t.truncGE 0).obj E) 0 n hn).eq_of_src _ _,
        (DerivedCategory.isZero_of_isGE ((t.truncGE 0).obj _) 0 n hn).eq_of_src _ _⟩
  have hπE := isIso_homology_derivedPushforward_truncGEπ f d hvan E hcoh 0 i (by omega)
  have hπM' : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
      ((derivedPushforward f.toLRSHom.toShHom).map
        ((t.truncGEπ 0).app ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)))) :=
    inferInstance
  have hsq' := congrArg (fun k => (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
      ((derivedPushforward f.toLRSHom.toShHom).map k)) hsq
  simp only [Functor.map_comp] at hsq'
  have h4 : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
      ((derivedPushforward f.toLRSHom.toShHom).map φ) ≫
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
      ((derivedPushforward f.toLRSHom.toShHom).map
        ((t.truncGEπ 0).app ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)))) := by
    rw [← hsq']; infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
      ((derivedPushforward f.toLRSHom.toShHom).map
        ((t.truncGEπ 0).app ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M))))

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
