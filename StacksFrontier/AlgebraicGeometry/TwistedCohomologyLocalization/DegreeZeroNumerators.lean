module

public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.NumeratorCriterion
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
import all StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
import all StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionInjective

/-!
# The numerator statements of the twisted localization map in degree zero

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)` a global section and `ℱ` a
quasi-coherent `𝒪_X`-module. Through the degree-zero comparison `H⁰(U, -) ≅ Γ(U, -)` (`HzeroIso`),
natural in the module and in the open, the numerator statements
`Stacks.Cohomology.TwistedLocalizationMap.RestrictKernelTorsion` and
`Stacks.Cohomology.TwistedLocalizationMap.RestrictPowerSurjective` become statements about
twisted sections. Under it:

* the action of `sᵏ` on cohomology is multiplication of sections by `sᵏ`, up to the reindexing
  comparison between the degrees `k + n` and `n + k`;
* the restriction maps and the untwisting isomorphism `s^{-n}` are the restriction of sections
  and multiplication of sections by `sⁿ`.

In degree zero the kernel statement holds over every quasi-compact open, and the surjectivity
statement over every affine open on which `ℒ` is trivial.

## Main results

* `Stacks.Cohomology.TwistedLocalizationMap.sectionPowerAction_comp_twistedPowerAddIso`:
  multiplying a twist by `sᵐ` is the graded action of `sᵐ`.
* `Stacks.Cohomology.TwistedLocalizationMap.toSection`: the degree-zero comparison, with its
  compatibility with restriction, with the maps induced by morphisms of modules, and with
  untwisting.
* `Stacks.Cohomology.TwistedLocalizationMap.restrictKernelTorsion_zero_of_isCompact`: the kernel
  statement in degree zero over a quasi-compact open.
* `Stacks.Cohomology.TwistedLocalizationMap.exists_twistedSection_of_isAffineOpen`: on an affine
  open trivializing `ℒ`, every section of `ℱ` over `A ∩ X_s` times some `sᴺ` extends to `A`.
* `Stacks.Cohomology.TwistedLocalizationMap.restrictPowerSurjective_zero_of_generator`: the
  surjectivity statement in degree zero over an affine open on which `ℒ` is trivial.

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules DirectSum
open Stacks.Cohomology.TwistedGradedModule
open Stacks.SheafOfModules.TwistAction

universe u

namespace Stacks.Cohomology.TwistedLocalizationMap

attribute [local instance] Stacks.SheafOfModules.sectionDegreeVAdd

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

variable (s : L.sections) (F : X.Modules)

/-- The degree-`n` component of the `n`-th power of the homogeneous section attached to `s` is
the value on the unit global section of the morphism `𝒪_X ⟶ ℒ^{⊗ n}` representing `sⁿ`. -/
theorem sectionPower_eq_powerSectionValue (n : ℕ) :
    sectionPower X L s n = PowerSection.powerSectionValue X L s n := by
  rw [sectionPower, ← Stacks.Cohomology.PowerSection.of_powerSectionValue X L s n,
    DirectSum.of_eq_same]

/-- Composing two reindexing comparisons of tensor powers is the reindexing along the composite
equality of degrees. -/
theorem tensorPowerReindex_app_trans {i j k : ℤ} (h₁ : i = j) (h₂ : j = k)
    (U : Opens X.toRingedSpace)
    (z : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L i).val.obj
      (op U)) :
    (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
          h₂).hom.val.app (op U)
        ((TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
          h₁).hom.val.app (op U) z) =
      (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
        (h₁.trans h₂)).hom.val.app (op U) z := by
  subst h₁ h₂
  rfl

/-- Multiplying a twisted section over an open by `sᵐ` is the value there of a morphism of
sheaves: multiplication by the global section `sᵐ`, followed by the coherence isomorphism
`(ℱ ⊗ ℒ^{⊗ n}) ⊗ ℒ^{⊗ m} ≅ ℱ ⊗ ℒ^{⊗ (n + m)}`. -/
private theorem twistSectionByPower_eq_app (n m : ℕ)
    (U : Opens X.toRingedSpace)
    (a : (twist X L F (n : ℤ)).val.obj (op U)) :
    twistSectionByPower X L F s n m U a =
      ((sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L
            (twist X L F (n : ℤ)) (m : ℤ)
            (globalSectionHom (sectionSiteRing X) (sectionSiteSheaf X) _
              (sectionPower X L s m)) ≫
          (twistedPowerAddIso X L F n m).hom).val.app (op U)) a := by
  have hsp := SectionPower.sectionPowerAction_app (sectionSiteRing X) (sectionSiteSheaf X) L
    (twist X L F (n : ℤ)) (m : ℤ)
    (globalSectionHom (sectionSiteRing X) (sectionSiteSheaf X)
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ))
      (sectionPower X L s m)) (op U) a
  rw [globalSectionHom_app] at hsp
  exact congrArg (fun z => (twistedPowerAddIso X L F n m).hom.val.app (op U) z) hsp.symm

/-- The two spellings of the degree of `sᵐ · ξ` for `ξ` of degree `n`. -/
theorem degree_add_swap (n m : ℕ) : (m : ℤ) + (n : ℤ) = ((n + m : ℕ) : ℤ) := by push_cast; ring

/-- The two multiplications by `sᵐ`, `sectionPowerAction` followed by `twistedPowerAddIso` and
`actionOf` followed by the reindexing, agree on a pure tensor `x ⊗ y`. -/
private theorem sectionPowerAction_twistedPowerAddIso_pure (n m : ℕ)
    (U : Opens X.toRingedSpace) (x : F.val.obj (op U))
    (y : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op U)) :
    ((sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L
            (twist X L F (n : ℤ)) (m : ℤ)
            (globalSectionHom (sectionSiteRing X) (sectionSiteSheaf X) _
              (sectionPower X L s m)) ≫
          (twistedPowerAddIso X L F n m).hom).val.app (op U))
        (tensorSectionAtOpen X L F U n x y) =
      ((actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (m : ℤ) (n : ℤ)
            (PowerSection.powerSectionValue X L s m) ≫
          reindexTwist X L F (degree_add_swap n m)).val.app (op U))
        (tensorSectionAtOpen X L F U n x y) := by
  have hL := (twistSectionByPower_eq_app X L s F n m U
      (tensorSectionAtOpen X L F U n x y)).symm.trans
    (twistSectionByPower_tensorSectionAtOpen X L F s n m U x y)
  have hR := twistActionHom_pure (sectionSiteRing X) (sectionSiteSheaf X) L F (m : ℤ) (n : ℤ)
    (globalSectionHom (sectionSiteRing X) (sectionSiteSheaf X)
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ))
      (PowerSection.powerSectionValue X L s m)) (op U) x y
  rw [globalSectionHom_app] at hR
  have hRHS : ((actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (m : ℤ) (n : ℤ)
            (PowerSection.powerSectionValue X L s m) ≫
          reindexTwist X L F (degree_add_swap n m)).val.app (op U))
        (tensorSectionAtOpen X L F U n x y) =
      tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) F
        (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L ((n + m : ℕ) : ℤ)) x
        ((TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
            (degree_add_swap n m)).hom.val.app (op U)
          (tensorPowerMulSectionAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) L
            (m : ℤ) (n : ℤ)
            ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
              (m : ℤ)).val.map (terminal.from U).op
              (PowerSection.powerSectionValue X L s m)) y)) := by
    change (reindexTwist X L F (degree_add_swap n m)).val.app (op U)
      ((twistActionHom (sectionSiteRing X) (sectionSiteSheaf X) L F (m : ℤ) (n : ℤ)
        (globalSectionHom (sectionSiteRing X) (sectionSiteSheaf X)
          (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ))
          (PowerSection.powerSectionValue X L s m))).val.app (op U)
        (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) F
          (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) x y)) = _
    rw [hR]
    exact tensorSections_tensorProductIsoAt (sectionSiteRing X) (sectionSiteSheaf X) (op U)
      F F (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
        ((m : ℤ) + (n : ℤ)))
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L ((n + m : ℕ) : ℤ))
      (Iso.refl F)
      (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
        (degree_add_swap n m))
      x _
  rw [hL, sectionPower_eq_powerSectionValue X L s m, hRHS,
    tensorPowerMulSectionAt_comm (sectionSiteRing X) (sectionSiteSheaf X) (op U) L
      (m : ℤ) (n : ℤ)
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.map
        (terminal.from U).op (PowerSection.powerSectionValue X L s m)) y,
    tensorPowerReindex_app_trans]
  rfl

/-- Multiplying a twist by `sᵐ` is the graded action `actionOf` of `sᵐ`, up to the reindexing
comparison between the two spellings `m + n` and `n + m` of the resulting degree. -/
theorem sectionPowerAction_comp_twistedPowerAddIso (n m : ℕ) :
    sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L
          (twist X L F (n : ℤ)) (m : ℤ)
          (globalSectionHom (sectionSiteRing X) (sectionSiteSheaf X) _
            (sectionPower X L s m)) ≫
        (twistedPowerAddIso X L F n m).hom =
      actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (m : ℤ) (n : ℤ)
          (PowerSection.powerSectionValue X L s m) ≫
        reindexTwist X L F (degree_add_swap n m) :=
  tensorSheaf_hom_ext (sectionSiteRing X) (sectionSiteSheaf X) fun U x y =>
    sectionPowerAction_twistedPowerAddIso_pure X L s F n m U.unop x y

/-! ### The degree-zero comparison -/

/-- An isomorphism of sheaves of modules is injective on the sections over every open. -/
private theorem iso_val_app_injective {M N : X.Modules} (e : M ≅ N)
    (U : (Opens X.toRingedSpace)ᵒᵖ)
    {a b : M.val.obj U} (hab : e.hom.val.app U a = e.hom.val.app U b) : a = b := by
  have h1 : (e.hom ≫ e.inv).val.app U a = (e.hom ≫ e.inv).val.app U b :=
    congrArg (e.inv.val.app U) hab
  rwa [e.hom_inv_id] at h1

/-- The degree-zero comparison `H⁰(U, 𝒢) ⟶ Γ(U, 𝒢)` (the isomorphism `HzeroIso`), read on a
cohomology class. -/
abbrev toSection (G : X.Modules) (U : X.Opens)
    (ξ : (Hgroup X.ringCatSheaf U 0 G : Type u)) : G.val.obj (op U) :=
  ConcreteCategory.hom ((HzeroIso X.ringCatSheaf U).hom.app G) ξ

/-- The degree-zero comparison is bijective. -/
theorem bijective_toSection (G : X.Modules) (U : X.Opens) :
    Function.Bijective (toSection X G U) :=
  bijective_Hzero X.ringCatSheaf U G

/-- The degree-zero comparison is natural in the module: the map induced on `H⁰` by a morphism of
sheaves becomes the map it induces on sections. -/
theorem toSection_map (U : X.Opens) {G G' : X.Modules} (φ : G ⟶ G')
    (ξ : (Hgroup X.ringCatSheaf U 0 G : Type u)) :
    toSection X G' U (ConcreteCategory.hom ((Hfunctor X.ringCatSheaf U 0).map φ) ξ) =
      φ.val.app (op U) (toSection X G U ξ) :=
  Hzero_map X.ringCatSheaf U φ ξ

/-- The degree-zero comparison is natural in the open: restriction of degree-zero classes becomes
restriction of sections. -/
theorem toSection_Hrestrict {U V : X.Opens} (h : U ≤ V) (G : X.Modules)
    (ξ : (Hgroup X.ringCatSheaf V 0 G : Type u)) :
    toSection X G U (ConcreteCategory.hom (Hrestrict X.ringCatSheaf h 0 G) ξ) =
      G.val.map (homOfLE h).op (toSection X G V ξ) :=
  Hzero_Hrestrict X.ringCatSheaf h G ξ

/-- Undoing the twist by `sⁿ` is, in degree zero, multiplication of sections by `sⁿ`. -/
theorem toSection_untwist (U : X.Opens) (n : ℕ)
    (y : (Hgroup X.ringCatSheaf (U ⊓ nonvanishingOpen L s) 0 F : Type u)) :
    toSection X (twist X L F (n : ℤ)) (U ⊓ nonvanishingOpen L s)
        (ConcreteCategory.hom
          (untwistIso X L s F 0 U n).hom y) =
      tensorSectionAtOpen X L F (U ⊓ nonvanishingOpen L s) n
        (toSection X F (U ⊓ nonvanishingOpen L s) y)
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
          (terminal.from (U ⊓ nonvanishingOpen L s)).op (sectionPower X L s n)) := by
  refine Eq.trans (toSection_map X (U ⊓ nonvanishingOpen L s)
    (sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ)
      (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n)) y) ?_
  have hsp := SectionPower.sectionPowerAction_app (sectionSiteRing X) (sectionSiteSheaf X) L F
    (n : ℤ) (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n)
    (op (U ⊓ nonvanishingOpen L s)) (toSection X F (U ⊓ nonvanishingOpen L s) y)
  have hu := unitHom_app_eq_map (sectionSiteRing X) (sectionSiteSheaf X)
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
    (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n)
    (op (U ⊓ nonvanishingOpen L s))
  refine hsp.trans ?_
  rw [hu, sectionPower_eq_powerSectionValue X L s n]
  rfl

/-- Multiplication of a twisted section by `sᵐ` is the graded action of `sᵐ`, read on sections
over an open, up to the reindexing comparison of the degree. -/
theorem twistSectionByPower_eq_actionOf (n m : ℕ) (U : Opens X.toRingedSpace)
    (a : (twist X L F (n : ℤ)).val.obj (op U)) :
    twistSectionByPower X L F s n m U a =
      (reindexTwist X L F (degree_add_swap n m)).val.app (op U)
        ((actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (m : ℤ) (n : ℤ)
          (PowerSection.powerSectionValue X L s m)).val.app (op U) a) := by
  rw [twistSectionByPower_eq_app X L s F n m U a,
    sectionPowerAction_comp_twistedPowerAddIso X L s F n m]
  rfl

/-- Restricting a degree-zero class along `restrictTwist` is restricting its section to
`A ∩ X_s`. -/
private theorem toSection_restrictTwist (A : X.Opens) (n : ℕ)
    (ξ : (Hgroup X.ringCatSheaf A 0 (twist X L F (n : ℤ)) : Type u)) :
    toSection X (twist X L F (n : ℤ)) (A ⊓ nonvanishingOpen L s)
        (ConcreteCategory.hom (restrictTwist X L s F 0 A (n : ℤ)) ξ) =
      (twist X L F (n : ℤ)).val.map
        (homOfLE (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A)).op
        (toSection X (twist X L F (n : ℤ)) A ξ) :=
  toSection_Hrestrict X inf_le_left (twist X L F (n : ℤ)) ξ

/-- The kernel statement in degree zero, over a quasi-compact open: a section of `ℱ ⊗ ℒ^{⊗ n}`
over a quasi-compact open `A` whose restriction to `A ∩ X_s` vanishes is killed by a power of
`s`. -/
theorem restrictKernelTorsion_zero_of_isCompact [F.IsQuasicoherent] (A : X.Opens)
    (hA : IsCompact (A : Set X)) :
    RestrictKernelTorsion X L s F 0 A := by
  intro n ξ hξ
  have h0 : (twist X L F (n : ℤ)).val.map
      (homOfLE (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A)).op
      (toSection X (twist X L F (n : ℤ)) A ξ) = 0 := by
    rw [← toSection_restrictTwist X L s F A n ξ, hξ]
    exact map_zero _
  obtain ⟨k, hk⟩ := hasTwistedCompactAnnihilation X L F s A hA n
    (toSection X (twist X L F (n : ℤ)) A ξ) 0 (by rw [map_zero]; exact h0)
  have hzero : twistSectionByPower X L F s n k A 0 = 0 := by
    rw [twistSectionByPower_eq_app X L s F n k A 0, map_zero]
  have hkk := (hk k le_rfl).trans hzero
  rw [twistSectionByPower_eq_actionOf X L s F n k A] at hkk
  have hact := iso_val_app_injective X
    (Invertible.tensorProductIso (sectionSiteRing X) (sectionSiteSheaf X) (Iso.refl F)
      (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
        (degree_add_swap n k))) (op A)
    (a := (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
      (PowerSection.powerSectionValue X L s k)).val.app (op A)
        (toSection X (twist X L F (n : ℤ)) A ξ)) (b := 0)
    (by rw [hkk, map_zero])
  exact ⟨k, (bijective_toSection X (twist X L F ((k : ℤ) + (n : ℤ))) A).1 <|
    (toSection_map X A (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
      (PowerSection.powerSectionValue X L s k)) ξ).trans (hact.trans (map_zero _).symm)⟩

/-- Restricting a section along `V ≤ V` does nothing. -/
private theorem res_self
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {V : Opens X.toRingedSpace} (h : V ≤ V) (z : M.val.obj (op V)) :
    M.val.map (homOfLE h).op z = z := by
  refine Eq.trans (congrArg (fun φ => M.val.presheaf.map φ z)
    (Subsingleton.elim (homOfLE h).op (𝟙 (op V)))) ?_
  rw [M.val.presheaf.map_id]
  rfl

/-- Let `A` be an affine open inside an open `W₀` on which `ℒ` has a frame `g`, and let `t` be a
section of `ℱ` over `A ∩ X_s`. Then for some `N` there is a section of `ℱ ⊗ ℒ^{⊗ N}` over `A`
restricting on `A ∩ X_s` to `t ⊗ sᴺ`. -/
theorem exists_twistedSection_of_isAffineOpen [F.IsQuasicoherent] {W₀ : Opens X.toRingedSpace}
    (g : GeneratorSections X.toRingedSpace L W₀) {A : Opens X.toRingedSpace}
    (hAaff : IsAffineOpen A) (hAW₀ : A ≤ W₀)
    (t : F.val.obj (op (A ⊓ nonvanishingOpen L s))) :
    ∃ (N : ℕ) (a : (twist X L F (N : ℤ)).val.obj (op A)),
      (twist X L F (N : ℤ)).val.map
          (homOfLE (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A)).op a =
        tensorSectionAtOpen X L F (A ⊓ nonvanishingOpen L s) N t
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
            (N : ℤ)).val.map
            (terminal.from (A ⊓ nonvanishingOpen L s)).op (sectionPower X L s N)) := by
  obtain ⟨r, hs, hAr⟩ := exists_scalar_section_inf_eq_basicOpen X L s
    (generatorRestrict L hAW₀ g)
  have hr1 : A ⊓ nonvanishingOpen L s ≤ X.basicOpen r := le_of_eq hAr
  have hr2 : X.basicOpen r ≤ A ⊓ nonvanishingOpen L s := le_of_eq hAr.symm
  obtain ⟨e, c, hc⟩ := Stacks.ModuleSectionExtension.exists_pow_smul_eq_res F hAaff r
    (F.val.map (homOfLE hr2).op t)
  obtain ⟨q, hq⟩ := sectionPower_restrict_dvd_smul X L s A r
    (generatorRestrict L hAW₀ g).val hs e
  refine ⟨e, tensorSectionAtOpen X L F A e (r ^ (e - e) • c) q, ?_⟩
  have hbase : (twist X L F (e : ℤ)).val.map (homOfLE (X.basicOpen_le r)).op
          (tensorSectionAtOpen X L F A e (r ^ (e - e) • c) q) =
        tensorSectionAtOpen X L F (X.basicOpen r) e (F.val.map (homOfLE hr2).op t)
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (e : ℤ)).val.map
            (terminal.from (X.basicOpen r)).op (sectionPower X L s e)) := by
    have hring : Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ e) =
        Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ (e - e)) *
          Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) r ^ e := by
      rw [Stacks.ModuleSectionExtension.resR, Stacks.ModuleSectionExtension.resR,
        Stacks.ModuleSectionExtension.resR, map_pow, map_pow, ← pow_add,
        Nat.sub_add_cancel (le_refl e)]
    have hmod : Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ e) •
          Stacks.ModuleSectionExtension.res F hr2 t =
        Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ (e - e)) •
          Stacks.ModuleSectionExtension.res F (X.basicOpen_le r) c := by
      rw [hring, mul_smul]
      exact congrArg
        (fun z => Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ (e - e)) • z) hc
    have e1 := PresheafOfModules.map_smul F.val (homOfLE (X.basicOpen_le r)).op
      (r ^ (e - e)) c
    have e2 := (res_terminal_comp X (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (e : ℤ)) (X.basicOpen_le r) (sectionPower X L s e)).symm
    have e3 := congrArg (fun z => (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (e : ℤ)).val.map (homOfLE (X.basicOpen_le r)).op z) hq
    have e4 := PresheafOfModules.map_smul (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (e : ℤ)).val (homOfLE (X.basicOpen_le r)).op (r ^ e) q
    refine (tensorSectionAtOpen_res X L F e (X.basicOpen_le r) (r ^ (e - e) • c) q).trans ?_
    refine (congrArg (fun y => tensorSectionAtOpen X L F (X.basicOpen r) e y
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (e : ℤ)).val.map
        (homOfLE (X.basicOpen_le r)).op q)) (e1.trans hmod.symm)).trans ?_
    refine (tensorSectionsAt_smul_comm X F (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (e : ℤ)) (op (X.basicOpen r)) _ _ _).trans ?_
    exact congrArg (fun z => tensorSectionAtOpen X L F (X.basicOpen r) e
      (F.val.map (homOfLE hr2).op t) z) (e2.trans (e3.trans e4)).symm
  have step1 : ∀ z : (twist X L F (e : ℤ)).val.obj (op A),
      (twist X L F (e : ℤ)).val.map
          (homOfLE (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A)).op z =
        (twist X L F (e : ℤ)).val.map (homOfLE hr1).op
          ((twist X L F (e : ℤ)).val.map (homOfLE (X.basicOpen_le r)).op z) := by
    intro z
    refine Eq.trans ?_ (res_comp X (twist X L F (e : ℤ)) (X.basicOpen_le r) hr1 z).symm
    exact congrArg (fun φ => (twist X L F (e : ℤ)).val.presheaf.map φ z)
      (Subsingleton.elim _ _)
  have ht2 : F.val.map (homOfLE hr1).op (F.val.map (homOfLE hr2).op t) = t :=
    (res_comp X F hr2 hr1 t).trans (res_self X F (hr1.trans hr2) t)
  have hs2 := res_terminal_comp X (TensorPower.tensorPower (sectionSiteRing X)
    (sectionSiteSheaf X) L (e : ℤ)) hr1 (sectionPower X L s e)
  refine ((step1 _).trans (congrArg (fun z =>
    (twist X L F (e : ℤ)).val.map (homOfLE hr1).op z) hbase)).trans ?_
  exact (tensorSectionAtOpen_res X L F e hr1 (F.val.map (homOfLE hr2).op t)
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (e : ℤ)).val.map
        (terminal.from (X.basicOpen r)).op (sectionPower X L s e))).trans
    (congrArg₂ (fun y z => tensorSectionAtOpen X L F (A ⊓ nonvanishingOpen L s) e y z) ht2 hs2)

/-- The surjectivity statement in degree zero, over an affine open trivializing `ℒ`: every
section of `ℱ` over `A ∩ X_s` becomes, after multiplication by some `sᴺ`, the restriction of a
section of `ℱ ⊗ ℒ^{⊗ N}` over `A`. -/
theorem restrictPowerSurjective_zero_of_generator [F.IsQuasicoherent] {W₀ : Opens X.toRingedSpace}
    (g : GeneratorSections X.toRingedSpace L W₀) {A : Opens X.toRingedSpace}
    (hAaff : IsAffineOpen A) (hAW₀ : A ≤ W₀) :
    RestrictPowerSurjective X L s F 0 A := by
  intro y
  obtain ⟨N, a, ha⟩ := exists_twistedSection_of_isAffineOpen X L s F g hAaff hAW₀
    (toSection X F (A ⊓ nonvanishingOpen L s) y)
  obtain ⟨ξ, hξ⟩ := (bijective_toSection X (twist X L F (N : ℤ)) A).2 a
  refine ⟨N, ξ, (bijective_toSection X (twist X L F (N : ℤ)) (A ⊓ nonvanishingOpen L s)).1 ?_⟩
  rw [toSection_untwist X L s F A N y]
  rw [toSection_restrictTwist X L s F A N ξ, hξ]
  exact ha

end Stacks.Cohomology.TwistedLocalizationMap

end
