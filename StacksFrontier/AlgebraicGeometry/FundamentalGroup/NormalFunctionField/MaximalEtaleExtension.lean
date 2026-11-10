module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.FieldTheory.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.BaseChangeExactSequence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleNormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FiniteEtaleCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# The maximal extension of the function field in which a normal scheme is unramified

Let `X` be an integral normal scheme and let `sbar` be an algebraic geometric point of
`X` lying over the generic point `η`. Write `K = κ(η)` for the function field of `X` and
`Ω = κ(sbar)` for the algebraically closed residue field of the geometric point. Inside `Ω` there
is a largest subextension `M` of `K` with the property that `X` is unramified in every finite
subextension of `M`, i.e. that the normalization of `X` in that subextension is finite étale over
`X`; and the étale fundamental group `π₁(X, sbar)` is the Galois group `Gal(M/K)`.

This file constructs `M`; the identification of `π₁(X, sbar)` with `Gal(M/K)` is in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalFunctionField.FundamentalGroupIso`.

## Main definitions

* `AlgebraicGeometry.FiniteEtaleNormalization` — an intermediate field is finite over the function
  field and the normalization of `X` in it is finite étale over `X`.
* `AlgebraicGeometry.maximalEtaleExtension` — the compositum `M` of all intermediate fields with
  that property.

## Main results

* `AlgebraicGeometry.le_maximalEtaleExtension` — `M` is the largest such subextension.
* `AlgebraicGeometry.normal_maximalEtaleExtension` — `M` is normal, hence Galois, over `K`.

## Implementation notes

The function field is spelled as the residue field `X.residueField (genericPoint X)` at the
generic point, and the normalization of `X` in an intermediate field `E` is the relative
normalization of the morphism `Spec E ⟶ X` through the generic point.

## References

* [Stacks Project, Tag 03VG](https://stacks.math.columbia.edu/tag/03VG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The morphism to `X` from the spectrum of an intermediate field of an extension of the
function field of `X`. -/
private def genericFieldExtensionHom (X : Scheme.{u}) [IrreducibleSpace X]
    {L : Type u} [Field L] [Algebra (X.residueField (genericPoint X)) L]
    (E : IntermediateField (X.residueField (genericPoint X)) L) :
    Spec (.of E) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) E)) ≫
    X.fromSpecResidueField (genericPoint X)

/-- `X` is unramified in an intermediate field of an extension of its function field if its
relative normalization there is an unramified morphism. -/
private def IsUnramifiedIn (X : Scheme.{u}) [IrreducibleSpace X]
    {L : Type u} [Field L] [Algebra (X.residueField (genericPoint X)) L]
    (E : IntermediateField (X.residueField (genericPoint X)) L) : Prop :=
  ∃ hqc : QuasiCompact (genericFieldExtensionHom (L := L) X E),
    ∃ _hqs : QuasiSeparated (genericFieldExtensionHom (L := L) X E),
      letI := hqc
      Unramified (genericFieldExtensionHom (L := L) X E).fromNormalization

variable (X : Scheme.{u}) (sbar : GeometricPoint X)

/-- The residue field of the geometric point `sbar` as an algebra over the residue field of `X`
at its image. -/
local instance : Algebra (X.residueField (sbar.hom default)) sbar.residueField :=
  GeometricPoint.residueFieldAlgebra sbar

private theorem unramified_normalization_iff_finite_etale_normalization
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y] [IsIntegral X]
    [IsNormal X] [QuasiCompact f] [QuasiSeparated f] [IsDominant f] :
    Unramified f.fromNormalization ↔
      (IsFinite f.fromNormalization ∧ Etale f.fromNormalization) := by
  constructor
  · intro h
    have he : Etale f.fromNormalization :=
      (AlgebraicGeometry.unramified_normalization_iff_etale f).mp h
    exact ⟨(AlgebraicGeometry.etale_normalization_iff_finite_etale f).mp he |>.1, he⟩
  · rintro ⟨_, he⟩
    exact (AlgebraicGeometry.unramified_normalization_iff_etale f).mpr he

private theorem genericFieldExtensionHom_isDominant
    [IrreducibleSpace X] {Ω : Type u} [Field Ω]
    [Algebra ((X.residueField (genericPoint X))) Ω]
    (E : IntermediateField ((X.residueField (genericPoint X))) Ω) :
    IsDominant (genericFieldExtensionHom X E) := by
  constructor
  change Dense (Set.range (genericFieldExtensionHom X E))
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  have hη : genericPoint X ∈ Set.range (genericFieldExtensionHom X E) := by
    refine ⟨default, ?_⟩
    change X.fromSpecResidueField (genericPoint X)
      ((Spec.map (CommRingCat.ofHom
        (algebraMap ((X.residueField (genericPoint X))) E))) default) = genericPoint X
    exact Scheme.fromSpecResidueField_apply _ _
  have hclosure : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  rw [← hclosure]
  exact closure_mono (Set.singleton_subset_iff.mpr hη)

/-- A normal irreducible scheme is integral. -/
private theorem isIntegral_of_isNormal (X : Scheme.{u}) [IrreducibleSpace X] [IsNormal X] :
    IsIntegral X :=
  have : IsReduced X := isReduced_of_isReduced_stalk X
  (isIntegral_iff_irreducibleSpace_and_isReduced X).2 ⟨inferInstance, inferInstance⟩

private theorem quasiCompact_genericFieldExtensionHom
    (X : Scheme.{u}) [IrreducibleSpace X]
    {L : Type u} [Field L] [Algebra (X.residueField (genericPoint X)) L]
    (E : IntermediateField (X.residueField (genericPoint X)) L) :
    QuasiCompact (genericFieldExtensionHom X E) := by
  dsimp [genericFieldExtensionHom]; infer_instance

private theorem quasiSeparated_genericFieldExtensionHom
    (X : Scheme.{u}) [IrreducibleSpace X]
    {L : Type u} [Field L] [Algebra (X.residueField (genericPoint X)) L]
    (E : IntermediateField (X.residueField (genericPoint X)) L) :
    QuasiSeparated (genericFieldExtensionHom X E) := by
  dsimp [genericFieldExtensionHom]; infer_instance

/-- Cancellation of a restriction isomorphism, in the shape in which the comparison of section
maps below produces it. Stated abstractly so that the cancellation happens in a context where the
objects are opaque. -/
private theorem comp_inv_restriction_cancel {A B C D F : CommRingCat.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (i : D ≅ C) (ρ : D ⟶ F) [IsIso ρ] :
    a ≫ (b ≫ i.inv ≫ ρ) ≫ (inv ρ ≫ i.hom) = a ≫ b := by
  simp

/-- Sections over an open `U` containing the generic point pull back along the morphism
`Spec E ⟶ X` through the generic point by evaluating at the generic point and then including
the function field into `E`. Stated at the spelling in which it is used below, where the
preimage of `U` is the whole of `Spec E`. -/
private theorem app_genericFieldExtensionHom
    (X : Scheme.{u}) [IrreducibleSpace X]
    {L : Type u} [Field L] [Algebra (X.residueField (genericPoint X)) L]
    (E : IntermediateField (X.residueField (genericPoint X)) L)
    (U : X.Opens) (hηU : genericPoint X ∈ U)
    (hpre : genericFieldExtensionHom X E ⁻¹ᵁ U = ⊤) :
    (genericFieldExtensionHom X E).app U =
      X.evaluation U (genericPoint X) hηU ≫
        CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) E) ≫
          (Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
            (Spec (.of E)).presheaf.map (eqToHom hpre).op := by
  simp [genericFieldExtensionHom, Scheme.Hom.comp_app, Scheme.fromSpecResidueField,
    Scheme.fromSpecStalk_app hηU, Scheme.evaluation, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- The `Spec`-section comparison of `app_genericFieldExtensionHom`, with the restriction
isomorphism cancelled: this is the form in which the scalar tower below needs it. -/
private theorem app_genericFieldExtensionHom_comp
    (X : Scheme.{u}) [IrreducibleSpace X]
    {L : Type u} [Field L] [Algebra (X.residueField (genericPoint X)) L]
    (E : IntermediateField (X.residueField (genericPoint X)) L)
    (U : X.Opens) (hηU : genericPoint X ∈ U)
    (hpre : genericFieldExtensionHom X E ⁻¹ᵁ U = ⊤) :
    (genericFieldExtensionHom X E).app U ≫
        inv ((Spec (.of E)).presheaf.map (eqToHom hpre).op) ≫
          (Scheme.ΓSpecIso (CommRingCat.of E)).hom =
      X.evaluation U (genericPoint X) hηU ≫
        CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) E) := by
  rw [app_genericFieldExtensionHom X E U hηU hpre]
  exact comp_inv_restriction_cancel _ _ (Scheme.ΓSpecIso (CommRingCat.of E)) _

private theorem genericFieldExtensionHom_toNormalization_mono
    (X : Scheme.{u}) [IrreducibleSpace X] [IsNormal X]
    {L : Type u} [Field L] [Algebra (X.residueField (genericPoint X)) L]
    (E : IntermediateField (X.residueField (genericPoint X)) L)
    [Module.Finite (X.residueField (genericPoint X)) E] :
    Mono (genericFieldExtensionHom X E).toNormalization := by
  let f := genericFieldExtensionHom X E
  let : QuasiCompact f := quasiCompact_genericFieldExtensionHom X E
  let : QuasiSeparated f := quasiSeparated_genericFieldExtensionHom X E
  have := isIntegral_of_isNormal X
  let i := X.affineCover.idx (genericPoint X)
  obtain ⟨y, hy⟩ := X.affineCover.covers (genericPoint X)
  let U : X.Opens := (X.affineCover.f i).opensRange
  have hUaff : IsAffineOpen U := isAffineOpen_opensRange _
  let U' : X.affineOpens := ⟨U, hUaff⟩
  have hηU : genericPoint X ∈ U := ⟨y, hy⟩
  let : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  have hpre : f ⁻¹ᵁ U = ⊤ := by
    ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    change f z ∈ U
    obtain rfl : z = genericPoint (Spec (.of E)) := Subsingleton.elim _ _
    dsimp [f, genericFieldExtensionHom]
    change X.fromSpecResidueField (genericPoint X)
      ((Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) E)))
        (genericPoint (Spec (.of E)))) ∈ U
    have h : (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) E)))
        (genericPoint (Spec (.of E))) =
          genericPoint (Spec (.of (X.residueField (genericPoint X)))) :=
      Subsingleton.elim _ _
    rw [h, Scheme.fromSpecResidueField_apply]
    exact hηU
  let A := Γ(X, U)
  let B := Γ(Spec (.of E), f ⁻¹ᵁ U)
  let er : B ≅ .of E :=
    (asIso ((Spec (.of E)).presheaf.map (eqToHom hpre).op)).symm ≪≫
      Scheme.ΓSpecIso (.of E)
  let e : B ≃+* E := er.commRingCatIsoToRingEquiv
  let : Algebra A B := (f.app U').hom.toAlgebra
  let : Field B := (e.isField (Field.toIsField E)).toField
  let C := integralClosure A B
  let : Algebra A (X.residueField (genericPoint X)) :=
    (X.evaluation U (genericPoint X) hηU).hom.toAlgebra
  let : Algebra (X.residueField (genericPoint X)) B :=
    RingHom.toAlgebra ((e.symm : E →+* B).comp
      (algebraMap (X.residueField (genericPoint X)) E))
  let : IsScalarTower A (X.residueField (genericPoint X)) B := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change (f.app U).hom a =
      e.symm (algebraMap (X.residueField (genericPoint X)) E
        ((X.evaluation U _ hηU).hom a))
    apply e.injective
    rw [e.apply_symm_apply]
    change (f.app U ≫ er.hom) a =
      (X.evaluation U _ hηU ≫ CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) E)) a
    have heq : f.app U ≫ er.hom =
        X.evaluation U _ hηU ≫
          CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) E) := by
      dsimp only [er, Iso.trans_hom, Iso.symm_hom, asIso_inv]
      exact app_genericFieldExtensionHom_comp X E U hηU hpre
    exact ConcreteCategory.congr_hom heq a
  let : IsFractionRing A X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hUaff
  let eη : X.functionField ≃+* (X.residueField (genericPoint X)) := RingEquiv.ofBijective
    (X.residue (genericPoint X)).hom
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩
  let eηA : X.functionField ≃ₐ[A] (X.residueField (genericPoint X)) :=
    { eη with commutes' _ := rfl }
  let : IsFractionRing A (X.residueField (genericPoint X)) := IsFractionRing.of_algEquiv eηA
  let eF : B ≃ₐ[(X.residueField (genericPoint X))] E :=
    AlgEquiv.ofRingEquiv (f := e) (by intro x; exact e.apply_symm_apply _)
  let : Module.Finite (X.residueField (genericPoint X)) B :=
    Module.Finite.equiv eF.toLinearEquiv.symm
  let : Algebra C B := C.val.toAlgebra
  let : IsFractionRing C B :=
    integralClosure.isFractionRing_of_finite_extension
      (X.residueField (genericPoint X)) B
  let : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap C B))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors C)
  let : IsPreimmersion
      (Spec.map (CommRingCat.ofHom (integralClosure A B).val.toRingHom)) :=
    IsPreimmersion.of_isLocalization (R := C) (nonZeroDivisors C)
  have haff : IsAffineOpen (f ⁻¹ᵁ U) := by rw [hpre]; exact isAffineOpen_top _
  have : IsIso (f ⁻¹ᵁ U).toSpecΓ := by rw [← haff.isoSpec_hom]; infer_instance
  have : IsPreimmersion ((f ⁻¹ᵁ U).ι ≫ f.toNormalization) := by
    rw [f.ι_toNormalization U']
    have h1 : IsPreimmersion (f ⁻¹ᵁ (U' : X.Opens)).toSpecΓ := inferInstance
    have h2 : IsPreimmersion (Spec.map (CommRingCat.ofHom
        (integralClosure Γ(X, (U' : X.Opens))
          Γ(Spec (.of E), f ⁻¹ᵁ (U' : X.Opens))).val.toRingHom)) := inferInstance
    have h3o : IsOpenImmersion ((Scheme.Hom.normalizationOpenCover f).f U') :=
      (Scheme.Hom.normalizationOpenCover f).map_prop U'
    have h3 : IsPreimmersion ((Scheme.Hom.normalizationOpenCover f).f U') := inferInstance
    exact @IsPreimmersion.comp _ _ _ _ _ h1 (@IsPreimmersion.comp _ _ _ _ _ h2 h3)
  have : IsIso (f ⁻¹ᵁ U).ι := by
    rw [hpre]
    change IsIso (Spec (.of E)).topIso.hom
    infer_instance
  have : Mono ((f ⁻¹ᵁ U).ι ≫ f.toNormalization) := inferInstance
  have : Mono (inv (f ⁻¹ᵁ U).ι ≫ ((f ⁻¹ᵁ U).ι ≫ f.toNormalization)) := inferInstance
  simpa [Category.assoc] using this

public theorem finiteExtension_toNormalization_mono_at_generic
    [IsIntegral X] [IsNormal X]
    (x : X) (hx : x = genericPoint X)
    {Ω : Type u} [Field Ω] [Algebra (X.residueField x) Ω]
    (E : IntermediateField (X.residueField x) Ω)
    [FiniteDimensional (X.residueField x) E] :
    let f : Spec (.of E) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) E)) ≫
        X.fromSpecResidueField x
    Mono f.toNormalization := by
  subst x
  exact genericFieldExtensionHom_toNormalization_mono X E

private theorem isUnramifiedIn_iff_finite_etale_normalization
    [IsIntegral X] [IsNormal X] {Ω : Type u} [Field Ω]
    [Algebra ((X.residueField (genericPoint X))) Ω]
    (E : IntermediateField ((X.residueField (genericPoint X))) Ω) :
    IsUnramifiedIn X E ↔
      let f := genericFieldExtensionHom X E
      letI : QuasiCompact f := quasiCompact_genericFieldExtensionHom X E
      letI : QuasiSeparated f := quasiSeparated_genericFieldExtensionHom X E
      IsFinite f.fromNormalization ∧ Etale f.fromNormalization := by
  let f := genericFieldExtensionHom X E
  let : QuasiCompact f := quasiCompact_genericFieldExtensionHom X E
  let : QuasiSeparated f := quasiSeparated_genericFieldExtensionHom X E
  let : IsDominant f := genericFieldExtensionHom_isDominant X E
  change (∃ _ : QuasiCompact f, ∃ _ : QuasiSeparated f,
    Unramified f.fromNormalization) ↔ _
  constructor
  · rintro ⟨_, _, h⟩
    exact (unramified_normalization_iff_finite_etale_normalization X f).mp h
  · intro h
    exact ⟨inferInstance, inferInstance,
      (unramified_normalization_iff_finite_etale_normalization X f).mpr h⟩

/-- The normalization of `X` in a finite intermediate field is finite étale. -/
public def FiniteEtaleNormalization
    (E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField) : Prop :=
  FiniteDimensional (X.residueField (sbar.hom default)) E ∧
    let f : Spec (.of E) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (sbar.hom default)) E)) ≫
        X.fromSpecResidueField (sbar.hom default)
    IsFinite f.fromNormalization ∧ Etale f.fromNormalization

/-- The compositum of all finite extensions giving finite étale normalizations. -/
@[stacks 03VG "maximal extension"]
public def maximalEtaleExtension :
    IntermediateField (X.residueField (sbar.hom default)) sbar.residueField :=
  sSup { E | FiniteEtaleNormalization X sbar E }

private noncomputable def intermediateExtensionSpecIso
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) (σ : Ω →ₐ[K] Ω) :
    Spec (.of E) ≅ Spec (.of (IntermediateField.map σ E)) :=
  Scheme.Spec.mapIso (E.equivMap σ).toRingEquiv.symm.toCommRingCatIso.op

-- Normalization extensionality unfolds several layers of scheme structure here.
private theorem genericFieldExtensionHom_map_hom
    (E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField)
    (σ : sbar.residueField →ₐ[X.residueField (sbar.hom default)] sbar.residueField) :
    (intermediateExtensionSpecIso E σ).hom ≫
        (Spec.map (CommRingCat.ofHom
          (algebraMap (X.residueField (sbar.hom default)) (IntermediateField.map σ E))) ≫
          X.fromSpecResidueField (sbar.hom default)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.residueField (sbar.hom default)) E)) ≫
          X.fromSpecResidueField (sbar.hom default) := by
  simp only [intermediateExtensionSpecIso, Functor.mapIso_hom, Scheme.Spec_map,
    Scheme.Spec_map]
  rw [← Spec.map_comp_assoc]
  congr 1
  rw [Spec.map_injective.eq_iff]
  apply CommRingCat.hom_ext
  ext x
  simp

private noncomputable def normalizationIsoOfSpecIso
    {Y Z X : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (i : Y ≅ Z) (h : i.hom ≫ g = f) :
    f.normalization ≅ g.normalization := by
  let φ := f.normalizationDesc (i.hom ≫ g.toNormalization) g.fromNormalization (by
    rw [Category.assoc, g.toNormalization_fromNormalization]
    exact h.symm)
  let ψ := g.normalizationDesc (i.inv ≫ f.toNormalization) f.fromNormalization (by
    have hi : i.inv ≫ f = g := by
      calc
        i.inv ≫ f = i.inv ≫ (i.hom ≫ g) := by rw [h]
        _ = g := by simp
    rw [Category.assoc, f.toNormalization_fromNormalization]
    exact hi.symm)
  refine ⟨φ, ψ, ?_, ?_⟩
  · apply Scheme.Hom.normalization.hom_ext f (φ ≫ ψ) (𝟙 _) f.fromNormalization ?_ ?_ ?_
    · simp [φ, ψ, Scheme.Hom.toNormalization_normalizationDesc]
    · simp [φ, ψ, Scheme.Hom.normalizationDesc_comp]
    · simp
  · apply Scheme.Hom.normalization.hom_ext g (ψ ≫ φ) (𝟙 _) g.fromNormalization ?_ ?_ ?_
    · simp [φ, ψ, Scheme.Hom.toNormalization_normalizationDesc]
    · simp [φ, ψ, Scheme.Hom.normalizationDesc_comp]
    · simp

/-- The isomorphism of normalizations commutes with the maps to `X`. -/
private theorem normalizationIsoOfSpecIso_hom_comp_fromNormalization
    {Y Z X : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (i : Y ≅ Z) (h : i.hom ≫ g = f) :
    (normalizationIsoOfSpecIso f g i h).hom ≫ g.fromNormalization = f.fromNormalization := by
  simp [normalizationIsoOfSpecIso, Scheme.Hom.normalizationDesc_comp]

-- The comparison uses the same normalization extensionality as the bridge above.
private theorem finiteEtaleNormalization_map
    (E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField)
    (hE : FiniteEtaleNormalization X sbar E)
    (σ : sbar.residueField →ₐ[X.residueField (sbar.hom default)] sbar.residueField) :
    FiniteEtaleNormalization X sbar (IntermediateField.map σ E) := by
  let K := X.residueField (sbar.hom default)
  let Ω := sbar.residueField
  let E' := IntermediateField.map σ E
  let f : Spec (.of E) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ X.fromSpecResidueField (sbar.hom default)
  let g : Spec (.of E') ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap K E')) ≫ X.fromSpecResidueField (sbar.hom default)
  have : QuasiCompact f := by dsimp [f]; infer_instance
  have : QuasiSeparated f := by dsimp [f]; infer_instance
  have : QuasiCompact g := by dsimp [g]; infer_instance
  have : QuasiSeparated g := by dsimp [g]; infer_instance
  have hfg : (intermediateExtensionSpecIso E σ).hom ≫ g = f := by
    simpa [f, g, E'] using genericFieldExtensionHom_map_hom X sbar E σ
  let j := normalizationIsoOfSpecIso f g (intermediateExtensionSpecIso E σ) hfg
  have hj : j.hom ≫ g.fromNormalization = f.fromNormalization :=
    normalizationIsoOfSpecIso_hom_comp_fromNormalization f g _ hfg
  have hNorm : FiniteDimensional K E ∧
      IsFinite f.fromNormalization ∧ Etale f.fromNormalization := by
    simpa [FiniteEtaleNormalization, f] using hE
  rcases hNorm with ⟨hdim, hFinite, hEtale⟩
  let : FiniteDimensional K E := hdim
  have hg : g.fromNormalization = inv j.hom ≫ f.fromNormalization := by
    rw [← hj, IsIso.inv_hom_id_assoc]
  have hEtale_g : Etale g.fromNormalization := by rw [hg]; infer_instance
  have hFinite_g : IsFinite g.fromNormalization := by rw [hg]; infer_instance
  have hE' : FiniteEtaleNormalization X sbar E' := by
    let : FiniteDimensional K E' := Module.Finite.equiv (E.equivMap σ).toLinearEquiv
    refine ⟨inferInstance, ?_⟩
    simpa [FiniteEtaleNormalization, g] using
      ⟨hFinite_g, hEtale_g⟩
  exact hE'

public theorem exists_integral_finiteEtale_factor
    (X : Scheme.{u}) [IrreducibleSpace X] [IsNormal X]
    (Y : FiniteEtaleOver X) {L : Type u} [Field L]
    (p : Spec (.of L) ⟶ Y.left) :
    ∃ Z : FiniteEtaleOver X, IsIntegral Z.left ∧
      ∃ (i : Z ⟶ Y) (q : Spec (.of L) ⟶ Z.left), Mono i.left ∧ q ≫ i.left = p := by
  let g : Y.left ⟶ X := Y.hom
  have : Etale g := Y.prop.2
  have : IsFinite g := Y.prop.1
  have : IsNormal Y.left := AlgebraicGeometry.isNormal_of_etale g
  have hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
    intro U _
    have : PreirreducibleSpace U := U.isOpenEmbedding.preirreducibleSpace
    classical
    by_cases h : Nonempty U
    · let := h
      let : IrreducibleSpace U := ⟨inferInstance⟩
      rw [irreducibleComponents_eq_singleton]
      exact Set.finite_singleton _
    · let : IsEmpty U := not_nonempty_iff.mp h
      apply Set.finite_empty.subset
      intro s hs
      exact isEmptyElim hs.1.nonempty.some
  obtain ⟨ι, Z, hnormal, hintegral, ⟨e⟩⟩ :=
    (AlgebraicGeometry.isNormal_iff_exists_iso_coproduct
      (AlgebraicGeometry.finite_irreducibleComponents_of_smooth g hX)).mp inferInstance
  obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk Z).surjective (e.hom (p (IsLocalRing.closedPoint L)))
  have hz' : (Sigma.ι Z i ≫ e.inv) z = p (IsLocalRing.closedPoint L) := by
    simpa using congrArg e.inv hz
  let j := Sigma.ι Z i ≫ e.inv
  have : IsClosedImmersion (Sigma.ι Z i) := by
    apply IsClosedImmersion.of_isPreimmersion
    have hclosed := (sigmaMk Z).isClosedMap _ (isClosed_range_sigmaMk (i := i))
    rw [← Set.range_comp] at hclosed
    simpa only [Function.comp_def, sigmaMk_mk] using hclosed
  have : IsClosedImmersion j := by dsimp [j]; infer_instance
  have hjopen : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hrange : Set.range p ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    exact ⟨z, hz'.trans (congrArg p (Subsingleton.elim _ _))⟩
  let W : FiniteEtaleOver X :=
    MorphismProperty.Over.mk _ (j ≫ Y.hom) ⟨inferInstance, inferInstance⟩
  let q : Spec (.of L) ⟶ Z i := @IsOpenImmersion.lift _ _ _ j p hjopen hrange
  have hq : q ≫ j = p := @IsOpenImmersion.lift_fac _ _ _ j p hjopen hrange
  exact ⟨W, hintegral i, MorphismProperty.Over.homMk j (by rfl), q,
    (show Mono j from inferInstance), hq⟩

private theorem eq_genericPoint_of_image_eq_genericPoint
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : Y ⟶ X) [LocallyQuasiFinite f] (y : Y) (hy : f y = genericPoint X) :
    y = genericPoint Y := by
  have hspec : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes (Set.mem_univ y)
  have hfgen : f (genericPoint Y) = genericPoint X :=
    ((hspec.map f.continuous).trans (by rw [hy])).antisymm
      ((genericPoint_spec X).specializes (Set.mem_univ _)) |>.eq
  have : DiscreteTopology (f ⁻¹' {genericPoint X}) :=
    (f.isDiscrete_preimage_singleton _).to_subtype
  have heq : (⟨genericPoint Y, hfgen⟩ : f ⁻¹' {genericPoint X}) = ⟨y, hy⟩ :=
    specializes_iff_eq.mp ((subtype_specializes_iff _ _).mpr hspec)
  exact (congrArg Subtype.val heq).symm

private theorem etale_normalization_residueField
    {X Y : Scheme.{u}} [IsIntegral X] [IsNormal X]
    (f : Y ⟶ X) [IsFinite f] [Etale f] [IsIntegral Y] :
    Etale (Y.fromSpecResidueField (genericPoint Y) ≫ f).fromNormalization := by
  have : IsIso (Y.residue (genericPoint Y)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(Y.residue (genericPoint Y)).hom.injective, Y.residue_surjective _⟩
  let a := Y.fromSpecResidueField (genericPoint Y) ≫ f
  let b := Y.fromSpecStalk (genericPoint Y) ≫ f
  let i : Spec (Y.residueField (genericPoint Y)) ≅ Spec Y.functionField :=
    Scheme.Spec.mapIso (asIso (Y.residue (genericPoint Y))).op
  let j : a.normalization ≅ b.normalization :=
    normalizationIsoOfSpecIso a b i rfl
  let k := b.normalizationDesc (Y.fromSpecStalk (genericPoint Y)) f rfl
  have : IsIso k := AlgebraicGeometry.normalizationDesc_isIso_of_finite_etale_connected f
  have h : j.hom ≫ k ≫ f = a.fromNormalization := by
    rw [Scheme.Hom.normalizationDesc_comp]
    exact normalizationIsoOfSpecIso_hom_comp_fromNormalization a b i rfl
  rw [← h]
  infer_instance

private theorem exists_unramified_intermediate_factor
    (X : Scheme.{u}) [IrreducibleSpace X] [IsNormal X]
    (L : Type u) [Field L] [Algebra ((X.residueField (genericPoint X))) L]
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X) [IsFinite g] [Etale g]
    (p : Spec (.of L) ⟶ Y)
    (hp : p ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ((X.residueField (genericPoint X))) L)) ≫
      X.fromSpecResidueField (genericPoint X)) :
    ∃ E : IntermediateField ((X.residueField (genericPoint X))) L,
      Module.Finite ((X.residueField (genericPoint X))) E ∧ IsUnramifiedIn X E ∧
        ∃ j : Spec (.of E) ⟶ Y, Mono j ∧
          Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫ j = p := by
  have := isIntegral_of_isNormal X
  let F := (X.residueField (genericPoint X))
  let η := X.fromSpecResidueField (genericPoint X)
  let y := p (IsLocalRing.closedPoint L)
  have hgy : g y = genericPoint X := by
    have h := congrArg (fun k : Spec (.of L) ⟶ X => k (IsLocalRing.closedPoint L)) hp
    change g y = X.fromSpecResidueField (genericPoint X) _ at h
    exact h.trans (Scheme.fromSpecResidueField_apply ..)
  have hy : y = genericPoint Y := eq_genericPoint_of_image_eq_genericPoint g y hgy
  let K := Y.residueField y
  let r : K ⟶ .of L := Y.descResidueField (Scheme.stalkClosedPointTo p)
  have hr : Spec.map r ≫ Y.fromSpecResidueField y = p :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L Y p
  let a : F ⟶ K := (X.residueFieldCongr hgy.symm).hom ≫ g.residueFieldMap y
  let : Algebra F K := a.hom.toAlgebra
  have ha : Spec.map a ≫ η = Y.fromSpecResidueField y ≫ g := by
    simp [a, η, Spec.map_comp, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have har : a ≫ r = CommRingCat.ofHom (algebraMap F L) := by
    apply Spec.map_injective
    apply (cancel_mono η).1
    rw [Spec.map_comp, Category.assoc, ha, ← Category.assoc, hr]
    exact hp
  let α : K →ₐ[F] L := { __ := r.hom, commutes' x := ConcreteCategory.congr_hom har x }
  let E := α.fieldRange
  let e : K ≃ₐ[F] E := α.equivFieldRange
  have : LocallyQuasiFinite (Spec.map a ≫ η) := by rw [ha]; infer_instance
  have : LocallyQuasiFinite (Spec.map a) := LocallyQuasiFinite.of_comp _ η
  have : Algebra.QuasiFinite F K :=
    (RingHom.quasiFinite_algebraMap).mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp inferInstance)
  have : Module.Finite F K := Module.Finite.of_quasiFinite
  have : Module.Finite F E := Module.Finite.equiv e.toLinearEquiv
  let i : Spec (.of E) ≅ Spec K := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let j : Spec (.of E) ⟶ Y := i.hom ≫ Y.fromSpecResidueField y
  have hj : j ≫ g = genericFieldExtensionHom X E := by
    rw [show j ≫ g = i.hom ≫ (Y.fromSpecResidueField y ≫ g) by simp [j], ← ha]
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map a ≫ η = _
    rw [← Spec.map_comp_assoc]
    change Spec.map _ ≫ η = Spec.map _ ≫ η
    have hea : a ≫ CommRingCat.ofHom e.toRingHom =
        CommRingCat.ofHom (algebraMap F E) :=
      CommRingCat.hom_ext (RingHom.ext e.commutes)
    exact congrArg (fun k => Spec.map k ≫ η) hea
  let f := genericFieldExtensionHom X E
  let b := Y.fromSpecResidueField y ≫ g
  have : QuasiCompact f := quasiCompact_genericFieldExtensionHom X E
  have : QuasiSeparated f := quasiSeparated_genericFieldExtensionHom X E
  let n : f.normalization ≅ b.normalization := normalizationIsoOfSpecIso f b i hj
  have : Etale b.fromNormalization := by
    dsimp only [b]
    rw [hy]
    exact etale_normalization_residueField g
  have hnb : n.hom ≫ b.fromNormalization = f.fromNormalization :=
    normalizationIsoOfSpecIso_hom_comp_fromNormalization f b i hj
  have : Etale f.fromNormalization := by rw [← hnb]; infer_instance
  refine ⟨E, inferInstance, ⟨inferInstance, inferInstance, ?_⟩, j, inferInstance, ?_⟩
  · have : IsDominant f := genericFieldExtensionHom_isDominant X E
    exact (AlgebraicGeometry.unramified_normalization_iff_etale f).mpr inferInstance
  · change Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecResidueField y = p
    rw [← Spec.map_comp_assoc]
    have hei : CommRingCat.ofHom e.toRingHom ≫
        CommRingCat.ofHom (algebraMap E L) = r :=
      CommRingCat.hom_ext (RingHom.ext (AlgHom.equivFieldRange_apply_coe α))
    rw [hei]
    exact hr

private theorem exists_finiteEtale_intermediate_factor
    [IrreducibleSpace X] [IsNormal X]
    (Ω : Type u) [Field Ω] [Algebra ((X.residueField (genericPoint X))) Ω]
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X) [IsFinite g] [Etale g]
    (p : Spec (.of Ω) ⟶ Y)
    (hp : p ≫ g = Spec.map (CommRingCat.ofHom
      (algebraMap ((X.residueField (genericPoint X))) Ω)) ≫
        X.fromSpecResidueField (genericPoint X)) :
    ∃ E : IntermediateField ((X.residueField (genericPoint X))) Ω,
      FiniteDimensional ((X.residueField (genericPoint X))) E ∧
        (let f := genericFieldExtensionHom X E
         IsFinite f.fromNormalization ∧ Etale f.fromNormalization) ∧
        ∃ j : Spec (.of E) ⟶ Y, Mono j ∧
          Spec.map (CommRingCat.ofHom (algebraMap E Ω)) ≫ j = p := by
  have := isIntegral_of_isNormal X
  obtain ⟨E, hfinite, hunramified, j, hjmono, hj⟩ :=
    exists_unramified_intermediate_factor X Ω g p hp
  exact ⟨E, hfinite,
    (isUnramifiedIn_iff_finite_etale_normalization X E).mp hunramified, j, hjmono, hj⟩

public theorem exists_finiteEtale_intermediate_factor_at
    [IsIntegral X] [IsNormal X]
    (x : X) (hx : x = genericPoint X)
    (Ω : Type u) [Field Ω] [Algebra (X.residueField x) Ω]
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X) [IsFinite g] [Etale g]
    (p : Spec (.of Ω) ⟶ Y)
    (hp : p ≫ g = Spec.map (CommRingCat.ofHom
      (algebraMap (X.residueField x) Ω)) ≫ X.fromSpecResidueField x) :
    ∃ E : IntermediateField (X.residueField x) Ω,
      FiniteDimensional (X.residueField x) E ∧
        (let f : Spec (.of E) ⟶ X :=
           Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) E)) ≫
             X.fromSpecResidueField x
         IsFinite f.fromNormalization ∧ Etale f.fromNormalization) ∧
        ∃ j : Spec (.of E) ⟶ Y, Mono j ∧
          Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ j = p := by
  subst x
  exact exists_finiteEtale_intermediate_factor X Ω g p hp

public theorem geometricPoint_factorization :
    Spec.map (CommRingCat.ofHom (GeometricPoint.residueFieldHom sbar)) ≫
      X.fromSpecResidueField (sbar.hom default) = sbar.hom := by
  let e := X.SpecToEquivOfField sbar.residueField
  let a := e sbar.hom
  let hpa : sbar.hom default = a.1 := by
    simp only
    exact congrArg sbar.hom (Subsingleton.elim _ _)
  have hfac : Spec.map a.2 ≫ X.fromSpecResidueField a.1 = sbar.hom :=
    e.symm_apply_apply sbar.hom
  change Spec.map ((X.residueFieldCongr hpa).hom ≫ a.2) ≫
    X.fromSpecResidueField (sbar.hom default) = sbar.hom
  rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField hpa]
  exact hfac

public theorem galoisToFundamentalGroup_restrict_apply
    [IrreducibleSpace X] (L Ω : Type u) [Field L] [Field Ω]
    [Algebra ((X.residueField (genericPoint X))) L]
    [IsSepClosure ((X.residueField (genericPoint X))) L]
    [Algebra L Ω] [Algebra ((X.residueField (genericPoint X))) Ω]
    [IsScalarTower ((X.residueField (genericPoint X))) L Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic ((X.residueField (genericPoint X))) Ω]
    (σ : Gal(Ω/(X.residueField (genericPoint X))))
    (Y : FiniteEtaleOver X)
    (p : finiteEtaleFiber
      ((algebraicClosureGeometricPoint ((X.residueField (genericPoint X))) Ω).map
        (X.fromSpecResidueField (genericPoint X))) Y) :
    ((((AlgebraicGeometry.galoisToFundamentalGroup X L Ω)
      (AlgEquiv.restrictNormalHom L σ)).asIso.app Y).hom p).1 =
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ p.1 := by
  let K := (X.residueField (genericPoint X))
  let j := X.fromSpecResidueField (genericPoint X)
  let t := algebraicClosureGeometricPoint K Ω
  let Z := (finiteEtaleBaseChange j).obj Y
  let q : finiteEtaleFiber t Z :=
    ⟨Limits.pullback.lift p.1 t.hom p.2, Limits.pullback.lift_snd _ _ _⟩
  have hq : finiteEtaleFiberProjection j t Y q = p :=
    Subtype.ext (Limits.pullback.lift_fst _ _ _)
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
    ((AlgebraicGeometry.finiteEtaleFiberIso K L Ω).hom.app Z)).2 q
  let r := (AlgebraicGeometry.separableFiberEquiv K L Ω Z a).1
  have hr : q.1 = Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ r := by
    rw [← ha]
    exact AlgebraicGeometry.finiteEtaleFiberIso_apply K L Ω Z a
  have hact := AlgebraicGeometry.galoisEquivEtaleFundamentalGroup_apply K L Ω Z
    (AlgEquiv.restrictNormalHom L σ) q r hr
  have hc :
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        Spec.map (CommRingCat.ofHom (AlgEquiv.restrictNormalHom L σ).toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L Ω)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact AlgEquiv.restrictNormal_commutes σ L x
  have hact' :
      (((AlgebraicGeometry.galoisEquivEtaleFundamentalGroup K L Ω
        (AlgEquiv.restrictNormalHom L σ)).asIso.app Z).hom q).1 =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ q.1 := by
    rw [hact, hr]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ r) hc).trans (Category.assoc _ _ _))
  have hproj := etaleFundamentalGroupMap_finiteEtaleFiberProjection j t Y
    (AlgebraicGeometry.galoisEquivEtaleFundamentalGroup K L Ω (AlgEquiv.restrictNormalHom L σ)) q
  rw [hq] at hproj
  change (((etaleFundamentalGroupMap j t
      (AlgebraicGeometry.galoisEquivEtaleFundamentalGroup K L Ω
        (AlgEquiv.restrictNormalHom L σ))).asIso.app Y).hom p).1 = _
  rw [← hproj]
  change (((AlgebraicGeometry.galoisEquivEtaleFundamentalGroup K L Ω
    (AlgEquiv.restrictNormalHom L σ)).asIso.app Z).hom q).1 ≫
      Limits.pullback.fst Y.hom j = _
  exact (congrArg (fun f : t.source ⟶ Z.left => f ≫ Limits.pullback.fst Y.hom j) hact').trans
    ((Category.assoc _ _ _).trans (congrArg
      (fun f => Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ f)
      (congrArg Subtype.val hq)))

/-- The maximal finite-étale extension is normal over the function field. -/
@[stacks 03VG "Galois extension"]
public theorem normal_maximalEtaleExtension
    [IsIntegral X] [IsNormal X]
    (hs : GeometricPoint.IsAlgebraic sbar) :
    Normal (X.residueField (sbar.hom default)) (maximalEtaleExtension X sbar) := by
  let K := X.residueField (sbar.hom default)
  let Ω := sbar.residueField
  let S : Set (IntermediateField K Ω) :=
    {E | FiniteEtaleNormalization X sbar E}
  change Normal K (@sSup (IntermediateField K Ω) inferInstance S)
  apply (IntermediateField.normal_iff_forall_map_le).2
  intro σ
  apply (IntermediateField.map_le_iff_le_comap).2
  apply sSup_le
  intro E hE
  have hσE : FiniteEtaleNormalization X sbar (IntermediateField.map σ E) :=
    finiteEtaleNormalization_map X sbar E (by simpa [S] using hE) σ
  exact (IntermediateField.map_le_iff_le_comap).1
    (le_sSup (Set.mem_ofPred.mpr hσE))

/-- The extension is largest among extensions with finite étale normalizations of all finite
subextensions. -/
@[stacks 03VG "maximality"]
public theorem le_maximalEtaleExtension
    [IsIntegral X] [IsNormal X]
    (hs : GeometricPoint.IsAlgebraic sbar)
    (M : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField)
    (hM : ∀ L : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField,
      L ≤ M → FiniteDimensional (X.residueField (sbar.hom default)) L →
        FiniteEtaleNormalization X sbar L) :
    M ≤ maximalEtaleExtension X sbar := by
  let K := X.residueField (sbar.hom default)
  let Ω := sbar.residueField
  have hAlg : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  intro x hx
  let E : IntermediateField K Ω := IntermediateField.adjoin K ({x} : Set Ω)
  have hxE : x ∈ E :=
    (IntermediateField.subset_adjoin K ({x} : Set Ω)) (Set.mem_singleton x)
  have hEM : E ≤ M :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  have hEfinite : FiniteDimensional K E := by
    simpa [E] using
      (IntermediateField.adjoin.finiteDimensional
        (IsAlgebraic.isIntegral (hAlg.isAlgebraic x)))
  exact le_sSup (Set.mem_ofPred.mpr (hM E hEM hEfinite)) hxE

end AlgebraicGeometry
