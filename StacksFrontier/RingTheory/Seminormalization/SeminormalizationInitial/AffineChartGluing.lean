module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ResidueFieldMapIsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Factorization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeSeminormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.SeminormalizationLocalization
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import StacksFrontier.AlgebraicGeometry.Morphisms.PullbackRestrictTransport

/-!
# Gluing the affine charts of the relative seminormalization

The relative seminormalization of a dominant map of rings gives an affine subintegral
factorization, unique up to unique comparison. For a quasi-compact, quasi-separated, dominant
morphism of schemes, these affine charts over the small affine site of the target, together with
their localization transitions, form a coequifibered diagram, and this file glues them into the
scheme `AlgebraicGeometry.relativeSeminormalizationMiddle` over the target.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

public noncomputable def affineSubintegralFactorization
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    SubintegralFactorization
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := by
  let S := relativeSeminormalization A B hdom
  letI : Algebra S B := S.toAlgebra
  refine ⟨Spec (CommRingCat.of S), ?_, ?_, ?_, ?_, ?_⟩
  · exact Scheme.Spec.map (CommRingCat.ofHom (algebraMap S B)).op
  · exact Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S)).op
  · have hcomp : CommRingCat.ofHom (algebraMap A S) ≫
        CommRingCat.ofHom (algebraMap S B) = CommRingCat.ofHom (algebraMap A B) := by
      rw [← CommRingCat.ofHom_comp]
      apply CommRingCat.hom_ext
      ext a
      rfl
    simpa only [CategoryTheory.op_comp, Scheme.Spec.map_comp] using
      congrArg (fun q => Scheme.Spec.map q.op) hcomp
  · simpa [S] using
      (relativeSeminormalization_universalHomeomorphism A B hdom)
  · simpa [S] using
      (relativeSeminormalization_residueFieldMap_isIso A B hdom)

/-- The map from an affine intermediate subintegral algebra into `B` factors
through the relative seminormalization. This is the ring-level bridge used to
construct the morphism between affine factorizations. -/
public noncomputable def affineSubintegralFactorization_lift
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (φ : C →ₐ[A] B)
    (hUH : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op))
    (hres : ∀ x, IsIso ((Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A C)).op).residueFieldMap x)) :
    C →ₐ[A] relativeSeminormalization A B hdom := by
  letI : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := hUH
  let E := relativeSeminormalization A B hdom
  refine ⟨φ.toRingHom.codRestrict E (fun c => ?_), ?_⟩
  · exact map_mem_relativeSeminormalization A B hdom φ hres c
  · exact fun a => Subtype.ext (φ.commutes a)

public noncomputable def affineSubintegralFactorization_target
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    (_hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (φ : C →ₐ[A] B)
    (hUH : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op))
    (hres : ∀ x, IsIso ((Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A C)).op).residueFieldMap x)) :
    SubintegralFactorization
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := by
  letI : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := hUH
  refine ⟨Spec (CommRingCat.of C),
    Scheme.Spec.map (CommRingCat.ofHom φ.toRingHom).op,
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op, ?_, hUH, hres⟩
  have hcomp : CommRingCat.ofHom (algebraMap A C) ≫
      CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom (algebraMap A B) := by
    rw [← CommRingCat.ofHom_comp]
    apply CommRingCat.hom_ext
    ext a
    exact φ.commutes a
  simpa only [CategoryTheory.op_comp, Scheme.Spec.map_comp] using
    congrArg (fun q => Scheme.Spec.map q.op) hcomp

/-- The preceding algebra map gives the unique comparison morphism between the
affine relative seminormalization and any affine subintegral factorization. -/
public noncomputable def affineSubintegralFactorization_hom
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (φ : C →ₐ[A] B)
    (hUH : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op))
    (hres : ∀ x, IsIso ((Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A C)).op).residueFieldMap x)) :
    SubintegralFactorization.Hom (affineSubintegralFactorization A B hdom)
      (affineSubintegralFactorization_target A B C hdom φ hUH hres) := by
  letI : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := hUH
  let E := relativeSeminormalization A B hdom
  let ψ := affineSubintegralFactorization_lift A B C hdom φ hUH hres
  refine ⟨Scheme.Spec.map (CommRingCat.ofHom ψ.toRingHom).op, ?_, ?_⟩
  · change Scheme.Spec.map (CommRingCat.ofHom (algebraMap E B)).op ≫
        Scheme.Spec.map (CommRingCat.ofHom ψ.toRingHom).op =
      Scheme.Spec.map (CommRingCat.ofHom φ.toRingHom).op
    have hring : CommRingCat.ofHom ψ.toRingHom ≫
        CommRingCat.ofHom (algebraMap E B) = CommRingCat.ofHom φ.toRingHom := by
      rw [← CommRingCat.ofHom_comp]
      apply CommRingCat.hom_ext
      ext c
      rfl
    simpa only [CategoryTheory.op_comp, Scheme.Spec.map_comp] using
      congrArg (fun q => Scheme.Spec.map q.op) hring
  · change Scheme.Spec.map (CommRingCat.ofHom ψ.toRingHom).op ≫
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap A E)).op
    have hring : CommRingCat.ofHom (algebraMap A C) ≫
        CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap A E) := by
      rw [← CommRingCat.ofHom_comp]
      apply CommRingCat.hom_ext
      exact ψ.comp_algebraMap
    simpa only [CategoryTheory.op_comp, Scheme.Spec.map_comp] using
      congrArg (fun q => Scheme.Spec.map q.op) hring

/-- The comparison between two affine factorizations is unique: after applying
the map to `B`, it is the inclusion of the intermediate subalgebra. -/
public theorem affineSubintegralFactorization_hom_unique
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (φ : C →ₐ[A] B)
    (hUH : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op))
    (hres : ∀ x, IsIso ((Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A C)).op).residueFieldMap x))
    (m : SubintegralFactorization.Hom
      (affineSubintegralFactorization A B hdom)
      (affineSubintegralFactorization_target A B C hdom φ hUH hres)) :
    m = affineSubintegralFactorization_hom A B C hdom φ hUH hres := by
  let E := relativeSeminormalization A B hdom
  let ψ := affineSubintegralFactorization_lift A B C hdom φ hUH hres
  let g := Spec.preimage m.hom
  have hring : g ≫ CommRingCat.ofHom (algebraMap E B) =
      CommRingCat.ofHom φ.toRingHom := by
    simpa [g, affineSubintegralFactorization, affineSubintegralFactorization_target,
      Spec.preimage_comp] using congrArg Spec.preimage m.toMiddle_hom
  have hψ : CommRingCat.ofHom ψ.toRingHom ≫
      CommRingCat.ofHom (algebraMap E B) = CommRingCat.ofHom φ.toRingHom := by
    rw [← CommRingCat.ofHom_comp]
    apply CommRingCat.hom_ext
    ext c
    rfl
  have hg : g = CommRingCat.ofHom ψ.toRingHom := by
    apply CommRingCat.hom_ext
    ext c
    have h₁ := congrArg (fun q => q.hom c) hring
    have h₂ := congrArg (fun q => q.hom c) hψ
    exact h₁.trans h₂.symm
  apply SubintegralFactorization.Hom.ext
  show m.hom = Scheme.Spec.map (CommRingCat.ofHom ψ.toRingHom).op
  have hgm : Scheme.Spec.map g.op = m.hom := by
    simpa [g, Spec.map] using Spec.map_preimage m.hom
  rw [← hgm]
  exact congrArg
    (fun q : CommRingCat.of C ⟶
      CommRingCat.of (relativeSeminormalization A B hdom) =>
        Scheme.Spec.map q.op)
    (by simpa only [g] using hg)



/-- The ring map on an affine chart of `f` is dominant. -/
public theorem affineChart_app_isDominant
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    IsDominant (AlgebraicGeometry.Spec.map (f.app U)) := by
  let fU := f ∣_ U
  let : IsDominant fU := IsZariskiLocalAtTarget.restrict (‹IsDominant f›) U
  let : IsAffine U.toScheme := hU
  let : IsIso U.toSpecΓ := by
    rw [← hU.isoSpec_hom]
    infer_instance
  have hcomp : IsDominant (fU ≫ U.toSpecΓ) := inferInstance
  have hspec : IsDominant ((f ⁻¹ᵁ U).toSpecΓ ≫ AlgebraicGeometry.Spec.map (f.app U)) := by
    rw [Scheme.Opens.toSpecΓ_naturality f U]
    exact hcomp
  exact IsDominant.of_comp ((f ⁻¹ᵁ U).toSpecΓ)
    (AlgebraicGeometry.Spec.map (f.app U))

/-- The affine chart algebra of the relative seminormalization over an affine
open of the target. -/
public noncomputable def affineSemiNormalizationAlgebra
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens) (hU : IsAffineOpen U) : CommRingCat.{u} := by
  letI := (f.app U).hom.toAlgebra
  exact CommRingCat.of (relativeSeminormalization
    Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (affineChart_app_isDominant f U hU))

/-- The first leg of the relative-seminormalization chart factorization. -/
public noncomputable def affineSemiNormalizationFromSource
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens) (hU : IsAffineOpen U) :
    (f ⁻¹ᵁ U).toScheme ⟶ Spec (affineSemiNormalizationAlgebra f U hU) := by
  letI := (f.app U).hom.toAlgebra
  exact (f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((relativeSeminormalization Γ(X, U) Γ(Y, f ⁻¹ᵁ U)
      (affineChart_app_isDominant f U hU)).val.toRingHom))

/-- The second leg of the relative-seminormalization chart factorization. -/
public noncomputable def affineSemiNormalizationToBase
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens) (hU : IsAffineOpen U) :
    Spec (affineSemiNormalizationAlgebra f U hU) ⟶ U.toScheme := by
  letI := (f.app U).hom.toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
      (relativeSeminormalization Γ(X, U) Γ(Y, f ⁻¹ᵁ U)
        (affineChart_app_isDominant f U hU)))) ≫ hU.isoSpec.inv

/-- The two affine chart maps factor the restriction of `f`. -/
public theorem affineSemiNormalization_fac
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens) (hU : IsAffineOpen U) :
    affineSemiNormalizationFromSource f U hU ≫ affineSemiNormalizationToBase f U hU =
      f ∣_ U := by
  let := (f.app U).hom.toAlgebra
  dsimp [affineSemiNormalizationFromSource, affineSemiNormalizationToBase,
    affineSemiNormalizationAlgebra]
  rw [Category.assoc, ← Spec.map_comp_assoc]
  show (f ⁻¹ᵁ U).toSpecΓ ≫ AlgebraicGeometry.Spec.map (f.app U) ≫
      hU.isoSpec.inv = _
  rw [← Category.assoc, Scheme.Opens.toSpecΓ_naturality f U]
  simp [hU.toSpecΓ_isoSpec_inv]

/-- The affine chart map to the base is subintegral. -/
public theorem affineSemiNormalizationToBase_subintegral
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.Opens) (hU : IsAffineOpen U) :
    UniversalHomeomorphism (affineSemiNormalizationToBase f U hU) ∧
      ∀ x, IsIso ((affineSemiNormalizationToBase f U hU).residueFieldMap x) := by
  let := (f.app U).hom.toAlgebra
  let E := relativeSeminormalization Γ(X, U) Γ(Y, f ⁻¹ᵁ U)
    (affineChart_app_isDominant f U hU)
  let q := Scheme.Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) E)).op
  have hq : UniversalHomeomorphism q :=
    relativeSeminormalization_universalHomeomorphism Γ(X, U)
      Γ(Y, f ⁻¹ᵁ U) (affineChart_app_isDominant f U hU)
  have hIso : UniversalHomeomorphism hU.isoSpec.inv := by
    apply (universalHomeomorphism_iff_integral_universallyInjective_surjective
      hU.isoSpec.inv).mpr
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hcomp := universalHomeomorphism_comp q hU.isoSpec.inv hq hIso
  have hfac : q ≫ hU.isoSpec.inv = affineSemiNormalizationToBase f U hU := by
    rfl
  let : IsOpenImmersion hU.isoSpec.inv := inferInstance
  refine ⟨?_, ?_⟩
  · rw [← hfac]
    exact hcomp
  · intro x
    dsimp [affineSemiNormalizationAlgebra] at x
    have hx : IsIso ((q ≫ hU.isoSpec.inv).residueFieldMap x) := by
      rw [Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' (show IsIso
        ((hU.isoSpec.inv).residueFieldMap (q x)) from inferInstance)
        (relativeSeminormalization_residueFieldMap_isIso
          Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (affineChart_app_isDominant f U hU) x)
    simpa [affineSemiNormalizationToBase, affineSemiNormalizationAlgebra, E, q] using hx


/-- Restriction to a localization carries the relative seminormalization into
the relative seminormalization of the localized map. This is the affine chart
compatibility needed when gluing the local factorizations. -/
public theorem relativeSeminormalization_localization_map_mem
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (S : Submonoid A)
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (S.map (algebraMap A B)) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op))
    {b : B} (hb : b ∈ relativeSeminormalization A B hdom) :
    algebraMap B Bₛ b ∈ relativeSeminormalization Aₛ Bₛ hdomₛ := by
  rw [mem_relativeSeminormalization_localization_iff
    A B Aₛ Bₛ S hdom hdomₛ]
  refine ⟨b, hb, 1, ?_⟩
  rw [← IsLocalization.mk'_one (M := S.map (algebraMap A B))]
  congr 1
  apply Subtype.ext
  simp


/-- Restriction of sections induces the chart map between the two affine
relative-seminormalization spectra for a localization of the base. -/
public noncomputable def relativeSeminormalization_localization_algHom
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (S : Submonoid A)
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (S.map (algebraMap A B)) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op)) :
    relativeSeminormalization A B hdom →ₐ[A]
      relativeSeminormalization Aₛ Bₛ hdomₛ := by
  let E := relativeSeminormalization A B hdom
  let Eₛ := relativeSeminormalization Aₛ Bₛ hdomₛ
  let φ : E →+* Eₛ := ((algebraMap B Bₛ).comp E.val).codRestrict Eₛ (fun x =>
    relativeSeminormalization_localization_map_mem
      A B Aₛ Bₛ S hdom hdomₛ x.2)
  refine { toRingHom := φ, commutes' := ?_ }
  intro a
  apply Subtype.ext
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe, RingHom.codRestrict_apply, RingHom.coe_comp, RingHom.coe_coe,
    Subalgebra.coe_val, Function.comp_apply, SubalgebraClass.coe_algebraMap,
    Subalgebra.coe_algebraMap, Eₛ, E, φ]
  rw [← IsScalarTower.algebraMap_apply A B Bₛ a]

/-- The chart map just defined is the restriction of the localization map on
the ambient algebra. -/
public theorem relativeSeminormalization_localization_algHom_val
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (S : Submonoid A)
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (S.map (algebraMap A B)) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op))
    (x : relativeSeminormalization A B hdom) :
    ((relativeSeminormalization_localization_algHom
      A B Aₛ Bₛ S hdom hdomₛ x :
        relativeSeminormalization Aₛ Bₛ hdomₛ) : Bₛ) =
      algebraMap B Bₛ x := by
  rfl

/-- The scheme morphism on affine charts induced by localizing the base. -/
public noncomputable def relativeSeminormalization_localization_specMap
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (S : Submonoid A)
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (S.map (algebraMap A B)) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op)) :
    Spec (CommRingCat.of (relativeSeminormalization Aₛ Bₛ hdomₛ)) ⟶
      Spec (CommRingCat.of (relativeSeminormalization A B hdom)) :=
  Scheme.Spec.map (CommRingCat.ofHom
    (relativeSeminormalization_localization_algHom
      A B Aₛ Bₛ S hdom hdomₛ).toRingHom).op

/-- The localization transition commutes with the maps from the ambient
algebra on the source side. -/
public theorem relativeSeminormalization_localization_algHom_comp_val
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (S : Submonoid A)
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (S.map (algebraMap A B)) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op)) :
    ((relativeSeminormalization Aₛ Bₛ hdomₛ).val.toRingHom).comp
        (relativeSeminormalization_localization_algHom
          A B Aₛ Bₛ S hdom hdomₛ).toRingHom =
      (algebraMap B Bₛ : B →+* Bₛ).comp
        (relativeSeminormalization A B hdom).val.toRingHom := by
  ext x
  exact relativeSeminormalization_localization_algHom_val
    A B Aₛ Bₛ S hdom hdomₛ x

/-- The localization transition is over the base ring map. -/
public theorem relativeSeminormalization_localization_algHom_base
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (S : Submonoid A)
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (S.map (algebraMap A B)) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op)) :
        (relativeSeminormalization_localization_algHom
          A B Aₛ Bₛ S hdom hdomₛ).toRingHom.comp
        (algebraMap A (relativeSeminormalization A B hdom)) =
        (algebraMap Aₛ (relativeSeminormalization Aₛ Bₛ hdomₛ)).comp
        (algebraMap A Aₛ) := by
  ext a
  exact (IsScalarTower.algebraMap_apply A B Bₛ a).symm.trans
    (IsScalarTower.algebraMap_apply A Aₛ Bₛ a)

/-- The affine chart comparison is the ordinary localization of the original
relative seminormalization. This identifies its scheme map as an open
immersion and gives the pullback square for a basic localization. -/
public theorem relativeSeminormalization_localization_isLocalization
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (S : Submonoid A)
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (S.map (algebraMap A B)) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op)) :
    let E := relativeSeminormalization A B hdom
    let Eₛ := relativeSeminormalization Aₛ Bₛ hdomₛ
    let j : E →+* Eₛ :=
      (relativeSeminormalization_localization_algHom A B Aₛ Bₛ S hdom hdomₛ).toRingHom
    letI : Algebra E Eₛ := j.toAlgebra
    let T := S.map (algebraMap A E)
    IsLocalization T Eₛ := by
  classical
  let E := relativeSeminormalization A B hdom
  let Eₛ := relativeSeminormalization Aₛ Bₛ hdomₛ
  let T : Submonoid E := S.map (algebraMap A E)
  let j : E →+* Eₛ :=
    (relativeSeminormalization_localization_algHom A B Aₛ Bₛ S hdom hdomₛ).toRingHom
  let : Algebra E Eₛ := j.toAlgebra
  have hjbase : j.comp (algebraMap A E) =
      (algebraMap Aₛ Eₛ).comp (algebraMap A Aₛ) :=
    relativeSeminormalization_localization_algHom_base
      A B Aₛ Bₛ S hdom hdomₛ
  have hjunits : ∀ t : T, IsUnit (j t.1) := by
    intro t
    obtain ⟨s, hs, ht⟩ := Submonoid.mem_map.mp t.2
    rw [← ht]
    rw [show j (algebraMap A E s) =
      algebraMap Aₛ Eₛ (algebraMap A Aₛ s) from congrArg (fun k : A →+* Eₛ => k s) hjbase]
    exact (IsLocalization.map_units Aₛ ⟨s, hs⟩).map (algebraMap Aₛ Eₛ)
  let φ : Localization T →+* Eₛ := IsLocalization.lift hjunits
  let hT : T.map E.val.toRingHom = S.map (algebraMap A B) := by
    ext x
    simp [T]
  let : Algebra E B := E.val.toRingHom.toAlgebra
  let : IsLocalization (T.map E.val.toRingHom) Bₛ := hT ▸ inferInstance
  let q : Localization T →+* Bₛ :=
    IsLocalization.map (M := T) Bₛ E.val.toRingHom (T.le_comap_map)
  have hq : q = Eₛ.val.toRingHom.comp φ := by
    apply IsLocalization.ringHom_ext T
    ext x
    have hφBase (a : E) : φ (algebraMap E (Localization T) a) = j a :=
      IsLocalization.lift_eq (M := T) (S := Localization T) hjunits a
    calc
      q (algebraMap E (Localization T) x) = algebraMap B Bₛ (x : B) :=
        IsLocalization.map_eq (M := T) (S := Localization T)
          (g := E.val.toRingHom) (T := T.map E.val.toRingHom)
          (Q := Bₛ) (T.le_comap_map) x
      _ = Eₛ.val (j x) :=
        (relativeSeminormalization_localization_algHom_val
          A B Aₛ Bₛ S hdom hdomₛ x).symm
      _ = (Eₛ.val.toRingHom.comp φ) (algebraMap E (Localization T) x) := by
        show Eₛ.val (j x) = Eₛ.val (φ (algebraMap E (Localization T) x))
        exact congrArg Eₛ.val (hφBase x).symm
  have hqinj : Function.Injective q :=
    IsLocalization.map_injective_of_injective T (Localization T)
      (Q := Bₛ) (g := E.val.toRingHom) (fun _ _ h => Subtype.ext h)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hqinj
    rw [hq]
    exact congrArg (fun z : Eₛ => (z : Bₛ)) hxy
  have hφsurj : Function.Surjective φ := by
    intro x
    have hx := (mem_relativeSeminormalization_localization_iff
      A B Aₛ Bₛ S hdom hdomₛ x.1).mp x.2
    obtain ⟨b, hb, s, hxEq⟩ := hx
    let t : T := ⟨algebraMap A E s.1,
      Submonoid.mem_map.mpr ⟨s.1, s.2, rfl⟩⟩
    let tB : S.map (algebraMap A B) :=
      ⟨algebraMap A B s.1, Submonoid.mem_map.mpr ⟨s.1, s.2, rfl⟩⟩
    let y : Localization T := IsLocalization.mk' (Localization T) ⟨b, hb⟩ t
    refine ⟨y, ?_⟩
    apply Subtype.val_injective
    show (Eₛ.val.toRingHom.comp φ) y = x.1
    rw [← hq]
    calc
      q y = IsLocalization.mk' Bₛ b tB := by
        show IsLocalization.map Bₛ E.val.toRingHom T.le_comap_map
          (IsLocalization.mk' (Localization T) ⟨b, hb⟩ t) = _
        rw [IsLocalization.map_mk']
        rfl
      _ = x.1 := hxEq.symm
  have hLoc : IsLocalization T (Localization T) := inferInstance
  let φAlg : Localization T →ₐ[E] Eₛ :=
    { toRingHom := φ
      commutes' := fun x => congrArg (fun k : E →+* Eₛ => k x)
        (IsLocalization.lift_comp hjunits) }
  have hEquiv : Localization T ≃ₐ[E] Eₛ :=
    AlgEquiv.ofBijective φAlg ⟨hφinj, hφsurj⟩
  have hTarget : IsLocalization T Eₛ :=
    (IsLocalization.isLocalization_iff_of_algEquiv T hEquiv).mp hLoc
  simpa [E, Eₛ, T, j] using hTarget

/-- The affine chart algebra becomes a localization when the base is localized
away from one element. -/
public theorem relativeSeminormalization_localization_away
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (r : A)
    [Algebra A Aₛ] [IsLocalization.Away r Aₛ]
    [Algebra B Bₛ] [IsLocalization.Away ((algebraMap A B) r) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op)) :
    let E := relativeSeminormalization A B hdom
    let Eₛ := relativeSeminormalization Aₛ Bₛ hdomₛ
    let j := (relativeSeminormalization_localization_algHom
      A B Aₛ Bₛ (Submonoid.powers r) hdom hdomₛ).toRingHom
    letI : Algebra E Eₛ := j.toAlgebra
    IsLocalization.Away (algebraMap A E r) Eₛ := by
  let S : Submonoid A := Submonoid.powers r
  let E := relativeSeminormalization A B hdom
  let Eₛ := relativeSeminormalization Aₛ Bₛ hdomₛ
  let j := (relativeSeminormalization_localization_algHom
    A B Aₛ Bₛ S hdom hdomₛ).toRingHom
  let : Algebra E Eₛ := j.toAlgebra
  have hloc : IsLocalization (S.map (algebraMap A E)) Eₛ :=
    relativeSeminormalization_localization_isLocalization
      A B Aₛ Bₛ S hdom hdomₛ
  simpa [S, E, Eₛ, j, Submonoid.map_powers] using hloc

/-- Passing from an affine open `U` to the basic open `D(r)` localizes the chart rings, and the
chart algebra structures form scalar towers. -/
private theorem basicOpen_chart_localization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (U : X.AffineZariskiSite) (r : Γ(X, U.1)) :
    let : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    let : Algebra Γ(X, U.1) Γ(X, (U.basicOpen r).1) := (X.presheaf.map
      (homOfLE (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r))).op).hom.toAlgebra
    let : Algebra Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ (U.basicOpen r).1) := (Y.presheaf.map
      (homOfLE (f.preimage_mono
        (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r)))).op).hom.toAlgebra
    let : Algebra Γ(X, (U.basicOpen r).1) Γ(Y, f ⁻¹ᵁ (U.basicOpen r).1) :=
      (f.app (U.basicOpen r).1).hom.toAlgebra
    let : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ (U.basicOpen r).1) :=
      (f.appLE U.1 (f ⁻¹ᵁ (U.basicOpen r).1) (f.preimage_mono
        (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r)))).hom.toAlgebra
    IsLocalization.Away r Γ(X, (U.basicOpen r).1) ∧
      IsLocalization.Away (algebraMap Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) r)
        Γ(Y, f ⁻¹ᵁ (U.basicOpen r).1) ∧
      IsScalarTower Γ(X, U.1) Γ(X, (U.basicOpen r).1) Γ(Y, f ⁻¹ᵁ (U.basicOpen r).1) := by
  intro _ _ inst _ _
  refine ⟨U.2.isLocalization_basicOpen r, ?_, ?_⟩
  · let : Algebra Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, Y.basicOpen ((f.app U.1) r)) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le ((f.app U.1) r))).op).hom.toAlgebra
    dsimp +instances [inst, Scheme.AffineZariskiSite.basicOpen]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs
      (f.isCompact_preimage U.2.isCompact)
      (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) ((f.app U.1) r)
  · apply IsScalarTower.of_algebraMap_eq'
    have hnat := f.naturality
      (homOfLE (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r))).op
    exact congrArg CommRingCat.Hom.hom hnat.symm

/-- Restriction along an arrow in the small affine site preserves the local
relative seminormalization subalgebra. -/
public theorem relativeSeminormalization_restriction_mem
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U V : X.AffineZariskiSite) (i : V ≤ U) :
    letI := (f.app U.1).hom.toAlgebra
    let E := relativeSeminormalization Γ(X, U.1)
      Γ(Y, f ⁻¹ᵁ U.1) (affineChart_app_isDominant f U.1 U.2)
    letI := (f.app V.1).hom.toAlgebra
    let E' := relativeSeminormalization Γ(X, V.1)
      Γ(Y, f ⁻¹ᵁ V.1) (affineChart_app_isDominant f V.1 V.2)
    ∀ b : E, (Y.presheaf.map (homOfLE (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono i))).op).hom b.1 ∈ E' := by
  intro E E' b
  let := (f.app U.1).hom.toAlgebra
  let := (f.app V.1).hom.toAlgebra
  obtain ⟨r, hr⟩ := i
  have hV : V = U.basicOpen r := Subtype.ext hr.symm
  subst V
  let A := Γ(X, U.1)
  let B := Γ(Y, f ⁻¹ᵁ U.1)
  let Uₛ := U.basicOpen r
  let Aₛ := Γ(X, Uₛ.1)
  let Bₛ := Γ(Y, f ⁻¹ᵁ Uₛ.1)
  let : Algebra A B := (f.app U.1).hom.toAlgebra
  let : Algebra A Aₛ := (X.presheaf.map
    (homOfLE (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r))).op).hom.toAlgebra
  let inst : Algebra B Bₛ := (Y.presheaf.map
    (homOfLE (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r)))).op).hom.toAlgebra
  let : Algebra Aₛ Bₛ := (f.app Uₛ.1).hom.toAlgebra
  let : Algebra A Bₛ := (f.appLE U.1 (f ⁻¹ᵁ Uₛ.1)
    (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r)))).hom.toAlgebra
  let := inst
  obtain ⟨_, hB, _⟩ := basicOpen_chart_localization f U r
  let : IsLocalization ((Submonoid.powers r).map (algebraMap A B)) Bₛ := by
    simpa [Submonoid.map_powers] using hB
  let : IsScalarTower A B Bₛ := .of_algebraMap_eq' rfl
  exact relativeSeminormalization_localization_map_mem A B Aₛ Bₛ
    (Submonoid.powers r) (affineChart_app_isDominant f U.1 U.2)
    (affineChart_app_isDominant f Uₛ.1 Uₛ.2) b.2

/-- The presheaf of relative-seminormalization algebras on the small affine
site of the base. -/
public noncomputable def relativeSeminormalizationDiagram
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U :=
    let U := U.unop
    letI := (f.app U.1).hom.toAlgebra
    CommRingCat.of (relativeSeminormalization Γ(X, U.1)
      Γ(Y, f ⁻¹ᵁ U.1) (affineChart_app_isDominant f U.1 U.2))
  map {i j} h :=
    let U := j.unop
    let V := i.unop
    letI := (f.app V.1).hom.toAlgebra
    letI := (f.app U.1).hom.toAlgebra
    CommRingCat.ofHom ((Y.presheaf.map (homOfLE (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono h.unop.le))).op).hom.restrict
        (relativeSeminormalization Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1)
          (affineChart_app_isDominant f V.1 V.2))
        (relativeSeminormalization Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)
          (affineChart_app_isDominant f U.1 U.2))
        (fun b hb => relativeSeminormalization_restriction_mem f _ _ h.unop.le ⟨b, hb⟩))
  map_id U := by simp; rfl
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono j.unop.le))
      (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.unop.le)), op_comp]
    simp_rw [Y.presheaf.map_comp]
    rfl

/-- The structure algebra map on the affine site. -/
public noncomputable def relativeSeminormalizationDiagramMap
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] :
    (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶
      relativeSeminormalizationDiagram f where
  app U :=
    let U := U.unop
    letI := (f.app U.1).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(X, U.1)
      (relativeSeminormalization Γ(X, U.1)
        Γ(Y, f ⁻¹ᵁ U.1) (affineChart_app_isDominant f U.1 U.2)))
  naturality {U V} i := by
    ext a
    exact Subtype.ext congr($(f.naturality
      ((Scheme.AffineZariskiSite.toOpensFunctor X).op.map i)) a)

/-- The relative-seminormalization algebra diagram is compatible with
localization on the affine site, hence can be glued into a scheme over `X`. -/
public theorem relativeSeminormalizationDiagramMap_coequifibered
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] :
    (relativeSeminormalizationDiagramMap f).Coequifibered := by
  apply Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let A := Γ(X, U.1)
  let B := Γ(Y, f ⁻¹ᵁ U.1)
  let U' := U.basicOpen r
  let A' := Γ(X, U'.1)
  let B' := Γ(Y, f ⁻¹ᵁ U'.1)
  let : Algebra A B := (f.app U.1).hom.toAlgebra
  let : Algebra A A' := (X.presheaf.map
    (homOfLE (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r))).op).hom.toAlgebra
  let inst : Algebra B B' := (Y.presheaf.map
    (homOfLE (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r)))).op).hom.toAlgebra
  let : Algebra A' B' := (f.app U'.1).hom.toAlgebra
  let : Algebra A B' := (f.appLE U.1 (f ⁻¹ᵁ U'.1)
    (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r)))).hom.toAlgebra
  let := inst
  obtain ⟨_, _, _⟩ := basicOpen_chart_localization f U r
  let : IsScalarTower A B B' := .of_algebraMap_eq' rfl
  exact relativeSeminormalization_localization_away A B A' B' r
    (affineChart_app_isDominant f U.1 U.2)
    (affineChart_app_isDominant f U'.1 U'.2)

/-- The scheme obtained by gluing the affine relative seminormalization charts. -/
public noncomputable def relativeSeminormalizationGlueData
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] :=
  Scheme.AffineZariskiSite.relativeGluingData (X := X)
    (relativeSeminormalizationDiagramMap_coequifibered f)

public noncomputable def relativeSeminormalizationMiddle
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : Scheme.{u} :=
  (relativeSeminormalizationGlueData f).glued

public noncomputable def relativeSeminormalizationToBase
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : relativeSeminormalizationMiddle f ⟶ X :=
  (relativeSeminormalizationGlueData f).toBase

public noncomputable def relativeSeminormalizationOpenCover
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : (relativeSeminormalizationMiddle f).OpenCover :=
  (relativeSeminormalizationGlueData f).cover

/-- The chart transition is compatible with the maps from the localized source
algebra. This is the scheme-level square needed when restricting the local
factorizations along an affine-open inclusion. -/
public theorem relativeSeminormalization_localization_specMap_source
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (S : Submonoid A)
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (S.map (algebraMap A B)) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op)) :
    Scheme.Spec.map (CommRingCat.ofHom
        ((relativeSeminormalization Aₛ Bₛ hdomₛ).val.toRingHom)).op ≫
        relativeSeminormalization_localization_specMap
          A B Aₛ Bₛ S hdom hdomₛ =
      Scheme.Spec.map (CommRingCat.ofHom
          (algebraMap B Bₛ : B →+* Bₛ)).op ≫
        Scheme.Spec.map (CommRingCat.ofHom
          ((relativeSeminormalization A B hdom).val.toRingHom)).op := by
  have h := relativeSeminormalization_localization_algHom_comp_val
    A B Aₛ Bₛ S hdom hdomₛ
  have h' : CommRingCat.ofHom
        (relativeSeminormalization_localization_algHom
          A B Aₛ Bₛ S hdom hdomₛ).toRingHom ≫
      CommRingCat.ofHom
        ((relativeSeminormalization Aₛ Bₛ hdomₛ).val.toRingHom) =
    CommRingCat.ofHom
        ((relativeSeminormalization A B hdom).val.toRingHom) ≫
      CommRingCat.ofHom (algebraMap B Bₛ) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom h
  have h'' := congrArg (fun q => q.op) h'
  simpa only [CategoryTheory.op_comp, Scheme.Spec.map_comp,
    relativeSeminormalization_localization_specMap] using
      congrArg (fun q => Scheme.Spec.map q) h''

end AlgebraicGeometry

end
