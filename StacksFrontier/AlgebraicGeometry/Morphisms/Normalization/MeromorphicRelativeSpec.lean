module

public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralClosureAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Glueing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of a reduced scheme is a relative spectrum

Let `X` be a reduced scheme whose quasi-compact opens have finitely many irreducible
components. The integral closure `𝒪'` of `𝒪_X` in the sheaf `K_X` of meromorphic functions is
a quasi-coherent sheaf of `𝒪_X`-algebras, and the normalization morphism `ν : X^ν ⟶ X` is the
structure morphism of the relative spectrum of `𝒪'`.

## Main definitions

* `AlgebraicGeometry.Scheme.meromorphicIntegralClosure` is `𝒪'`, and
  `AlgebraicGeometry.Scheme.meromorphicIntegralClosureSituation` presents it as a relative
  spectrum situation.
* `AlgebraicGeometry.Scheme.normalizationGluedSpectrum` presents the normalization of `X` as a
  relative spectrum of `𝒪'`, and `AlgebraicGeometry.Scheme.normalizationIsoMeromorphicSpectrum` is
  the resulting comparison isomorphism with the glued relative spectrum.

## Main results

* `AlgebraicGeometry.Scheme.normalizationIsoMeromorphicSpectrum_hom_toBase`: the comparison
  isomorphism carries the structure morphism of the relative spectrum to the normalization
  morphism, so `ν : X^ν ⟶ X` *is* `Spec_X(𝒪') ⟶ X`.

## Implementation notes

The normalization of `X` is the relative normalization of `X` in the canonical morphism `f`
from the coproduct of the spectra of the residue fields at the generic points, so over an
affine open `U` its sections are the integral closure of `Γ(X, U)` in `Γ(f ⁻¹ᵁ U)`. On the
other side `K_X(U)` is the total ring of fractions of `Γ(X, U)` by part (5) of [Stacks, Tag
02OW], and so is `Γ(f ⁻¹ᵁ U)` by the affine description of the normalization; the two are
therefore identified over `Γ(X, U)`, and the identification carries the sections of `𝒪'` to the
sections of the normalization. Those identifications are natural in `U`, which makes the
normalization carry the chart data of a relative spectrum of `𝒪'`; the comparison isomorphism
is then the uniqueness assertion of [Stacks, Tag 01LP].

The comparison is stated as an isomorphism of source schemes commuting with the two morphisms
to `X`, since an equality of morphisms with different sources is not well-typed.

## References

* [Stacks Project, Tag 035T](https://stacks.math.columbia.edu/tag/035T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeSpec

universe u

namespace AlgebraicGeometry.Scheme

/-! ### The integral closure of the structure sheaf in the meromorphic functions -/

/-- The sheaf `K_X` of meromorphic functions, as a sheaf of `𝒪_X`-algebras. -/
abbrev meromorphicAlgebra (X : Scheme.{u}) : X.QuasicoherentAlgebra :=
  Under.mk X.toTotalQuotientSheaf

/-- The integral closure `𝒪'` of the structure sheaf in the sheaf of meromorphic functions. -/
def meromorphicIntegralClosure (X : Scheme.{u}) : X.QuasicoherentAlgebra :=
  QuasicoherentAlgebra.integralClosureAlgebra X.meromorphicAlgebra

/-- On a reduced scheme whose quasi-compact opens have finitely many irreducible components the
sheaf of meromorphic functions is a quasi-coherent `𝒪_X`-algebra. -/
theorem isQuasicoherent_meromorphicAlgebra (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    QuasicoherentAlgebra.IsQuasicoherent X.meromorphicAlgebra :=
  Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.meromorphicFunctions_isQuasicoherent X
    hfinite

/-- The integral closure of the structure sheaf in the sheaf of meromorphic functions is a
quasi-coherent `𝒪_X`-algebra. -/
@[ega "II 6.3.4" "special case"]
theorem isQuasicoherent_meromorphicIntegralClosure (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    QuasicoherentAlgebra.IsQuasicoherent X.meromorphicIntegralClosure :=
  let := isQuasicoherent_meromorphicAlgebra X hfinite
  QuasicoherentAlgebra.isQuasicoherent_integralClosureAlgebra X.meromorphicAlgebra

/-- The relative spectrum situation of the integral closure of the structure sheaf in the sheaf
of meromorphic functions. -/
def meromorphicIntegralClosureSituation (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    RelativeSpecSituation.{u} where
  base := X
  algebra := X.meromorphicIntegralClosure
  isQuasicoherent := isQuasicoherent_meromorphicIntegralClosure X hfinite

namespace MeromorphicNormalization

/-! ### The sections over an affine open -/

/-- The `Γ(X, U)`-algebra structure on the meromorphic functions over `U`. -/
abbrev algMero (X : Scheme.{u}) (U : X.Opens) :
    Algebra Γ(X, U) (X.totalQuotientSheaf.presheaf.obj (op U)) :=
  (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra

/-- The `Γ(X, U)`-algebra structure on the sections of `𝒪'` over `U`. -/
abbrev algClosure (X : Scheme.{u}) (U : X.Opens) :
    Algebra Γ(X, U) (X.meromorphicIntegralClosure.right.presheaf.obj (op U)) :=
  (X.meromorphicIntegralClosure.hom.hom.app (op U)).hom.toAlgebra

/-- The `Γ(X, U)`-algebra structure on the sections of the generic-point residue spectrum over
the preimage of `U`. -/
abbrev algGeneric (X : Scheme.{u}) (U : X.Opens) :
    Algebra Γ(X, U)
      Γ(X.genericPointResidueSpectrum, X.fromGenericPointResidueFields ⁻¹ᵁ U) :=
  (X.fromGenericPointResidueFields.app U).hom.toAlgebra

attribute [local instance] algMero algClosure algGeneric

/-- Over an affine open the sections of `𝒪'` are the integral closure of `Γ(X, U)` in the
meromorphic functions over `U`. -/
@[ega "II 6.3.4" "special case"]
def closureSectionsAlgEquiv (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    X.meromorphicIntegralClosure.right.presheaf.obj (op U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) (X.totalQuotientSheaf.presheaf.obj (op U)) := by
  letI := isQuasicoherent_meromorphicAlgebra X hfinite
  let A := X.meromorphicAlgebra
  let ι := (QuasicoherentAlgebra.integralClosureAlgebraι A).right.hom.app (op U)
  have hrange :=
    QuasicoherentAlgebra.range_integralClosureAlgebraι_app_of_isAffineOpen A U hU
  have hw : X.meromorphicIntegralClosure.hom ≫
      (QuasicoherentAlgebra.integralClosureAlgebraι A).right = X.toTotalQuotientSheaf :=
    Under.w _
  refine AlgEquiv.ofBijective
    { toRingHom := ι.hom.codRestrict _ fun r => hrange.le ⟨r, rfl⟩
      commutes' := fun a => Subtype.ext ?_ } ⟨fun x y hxy => ?_, fun y => ?_⟩
  · exact congrArg (fun g : X.sheaf ⟶ X.totalQuotientSheaf => (g.hom.app (op U)).hom a) hw
  · have hval := Subtype.ext_iff.mp hxy
    exact QuasicoherentAlgebra.injective_integralClosureAlgebraι_app A U hval
  · obtain ⟨x, hx⟩ := hrange.ge y.2
    exact ⟨x, Subtype.ext hx⟩

/-- Over an affine open the meromorphic functions and the sections of the generic-point residue
spectrum are both the total ring of fractions of `Γ(X, U)`, hence identified over it. -/
def meroGenericAlgEquiv (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    X.totalQuotientSheaf.presheaf.obj (op U) ≃ₐ[Γ(X, U)]
      Γ(X.genericPointResidueSpectrum, X.fromGenericPointResidueFields ⁻¹ᵁ U) := by
  have : IsLocalization (nonZeroDivisors Γ(X, U)) (X.totalQuotientSheaf.presheaf.obj (op U)) :=
    isLocalization_totalQuotientSheaf_obj
      (weaklyAssociatedPointsOfScheme_eq_genericPoints X).le hfinite hU
  have : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hfinite U hU.isCompact)).to_subtype
  have : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_injective (genericPointsInOpenEquiv X U) (genericPointsInOpenEquiv X U).injective
  exact (IsLocalization.algEquiv (nonZeroDivisors Γ(X, U))
      (X.totalQuotientSheaf.presheaf.obj (op U)) (FractionRing Γ(X, U))).trans
    (genericPreimageSectionsAlgEquivFractionRing U hU).symm

/-- The identification of the meromorphic functions over an affine open with the sections of the
generic-point residue spectrum is one of `Γ(X, U)`-algebras. -/
lemma meroGenericAlgEquiv_comp_algebraMap (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    X.toTotalQuotientSheaf.hom.app (op U) ≫
        CommRingCat.ofHom (meroGenericAlgEquiv X hfinite U hU).toRingHom =
      X.fromGenericPointResidueFields.app U := by
  ext x
  exact (meroGenericAlgEquiv X hfinite U hU).commutes x

/-- The identifications of the meromorphic functions with the sections of the generic-point
residue spectrum are natural in the affine open. -/
lemma meroGenericAlgEquiv_naturality (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    X.totalQuotientSheaf.presheaf.map (homOfLE h).op ≫
        CommRingCat.ofHom (meroGenericAlgEquiv X hfinite U hU).toRingHom =
      CommRingCat.ofHom (meroGenericAlgEquiv X hfinite V hV).toRingHom ≫
        X.genericPointResidueSpectrum.presheaf.map
          (homOfLE (X.fromGenericPointResidueFields.preimage_mono h)).op := by
  have : IsLocalization (nonZeroDivisors Γ(X, V)) (X.totalQuotientSheaf.presheaf.obj (op V)) :=
    isLocalization_totalQuotientSheaf_obj
      (weaklyAssociatedPointsOfScheme_eq_genericPoints X).le hfinite hV
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (nonZeroDivisors Γ(X, V))
  change (X.toTotalQuotientSheaf.hom.app (op V) ≫
      X.totalQuotientSheaf.presheaf.map (homOfLE h).op ≫
      CommRingCat.ofHom (meroGenericAlgEquiv X hfinite U hU).toRingHom).hom =
    (X.toTotalQuotientSheaf.hom.app (op V) ≫
      CommRingCat.ofHom (meroGenericAlgEquiv X hfinite V hV).toRingHom ≫
      X.genericPointResidueSpectrum.presheaf.map
        (homOfLE (X.fromGenericPointResidueFields.preimage_mono h)).op).hom
  congr 1
  rw [← X.toTotalQuotientSheaf.hom.naturality_assoc,
    meroGenericAlgEquiv_comp_algebraMap, ← Category.assoc,
    meroGenericAlgEquiv_comp_algebraMap]
  exact X.fromGenericPointResidueFields.naturality (homOfLE h).op

/-- Over an affine open the sections of `𝒪'` are the integral closure of `Γ(X, U)` in the
sections of the generic-point residue spectrum over the preimage of `U`. -/
def closureGenericAlgEquiv (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    X.meromorphicIntegralClosure.right.presheaf.obj (op U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U)
        Γ(X.genericPointResidueSpectrum, X.fromGenericPointResidueFields ⁻¹ᵁ U) :=
  (closureSectionsAlgEquiv X hfinite U hU).trans
    (meroGenericAlgEquiv X hfinite U hU).mapIntegralClosure

/-- The identifications of the sections of `𝒪'` with the integral closures in the sections of
the generic-point residue spectrum are natural in the affine open. -/
lemma closureGenericAlgEquiv_naturality (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    X.meromorphicIntegralClosure.right.presheaf.map (homOfLE h).op ≫
        CommRingCat.ofHom (closureGenericAlgEquiv X hfinite U hU).toRingHom =
      CommRingCat.ofHom (closureGenericAlgEquiv X hfinite V hV).toRingHom ≫
        X.fromGenericPointResidueFields.normalizationDiagram.map (homOfLE h).op := by
  let ι := (QuasicoherentAlgebra.integralClosureAlgebraι X.meromorphicAlgebra).right.hom
  let ρ := X.meromorphicIntegralClosure.right.presheaf.map (homOfLE h).op
  ext x
  change (meroGenericAlgEquiv X hfinite U hU) ((ι.app (op U)).hom (ρ.hom x)) = _
  have hi := congrArg (fun g => g x) (ι.naturality (homOfLE h).op)
  exact (congrArg (meroGenericAlgEquiv X hfinite U hU).toRingHom hi).trans
    (congrArg (fun g => g ((ι.app (op V)).hom x))
      (meroGenericAlgEquiv_naturality X hfinite U V hU hV h))

/-! ### The sections of the normalization over an affine open -/

/-- The identifications of the sections of a relative normalization over the preimages of the
affine opens with the integral closures of the sections are natural in the affine open. -/
lemma normalizationObjIso_naturality {Y Z : Scheme.{u}} (f : Y ⟶ Z) [QuasiCompact f]
    [QuasiSeparated f] (U V : Z.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    f.normalization.presheaf.map (homOfLE (f.fromNormalization.preimage_mono h)).op ≫
        (f.normalizationObjIso hU).hom =
      (f.normalizationObjIso hV).hom ≫ f.normalizationDiagram.map (homOfLE h).op := by
  let := (f.app U).hom.toAlgebra
  let := (f.app V).hom.toAlgebra
  let vU := CommRingCat.ofHom (integralClosure Γ(Z, U) Γ(Y, f ⁻¹ᵁ U)).val.toRingHom
  let vV := CommRingCat.ofHom (integralClosure Γ(Z, V) Γ(Y, f ⁻¹ᵁ V)).val.toRingHom
  have hv2 : ((f.normalizationObjIso hV).hom ≫
        f.normalizationDiagram.map (homOfLE h).op) ≫ vU =
      ((f.normalizationObjIso hV).hom ≫ vV) ≫
        Y.presheaf.map (homOfLE (f.preimage_mono h)).op := rfl
  have : Mono vU := (ConcreteCategory.mono_iff_injective_of_preservesPullback vU).mpr
    Subtype.val_injective
  apply (cancel_mono vU).mp
  refine Eq.trans ?_ hv2.symm
  rw [f.normalizationObjIso_hom_val hV, Category.assoc,
    f.normalizationObjIso_hom_val hU]
  simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- The preimage of an affine open under the normalization morphism is affine. -/
lemma isAffineOpen_preimage_normalization (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (X.normalization hfinite ⁻¹ᵁ U) :=
  let := X.quasiCompactFromGenericPointResidueFields hfinite
  let := X.quasiSeparatedFromGenericPointResidueFields
  hU.preimage (X.normalization hfinite)

/-- Over an affine open the sections of `𝒪'` are the sections of the normalization over the
preimage of that open. -/
def normalizationSectionsIso (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    X.meromorphicIntegralClosure.right.presheaf.obj (op U) ≅
      Γ(X.normalizationScheme hfinite, X.normalization hfinite ⁻¹ᵁ U) :=
  letI := X.quasiCompactFromGenericPointResidueFields hfinite
  letI := X.quasiSeparatedFromGenericPointResidueFields
  (closureGenericAlgEquiv X hfinite U hU).toRingEquiv.toCommRingCatIso ≪≫
    (X.fromGenericPointResidueFields.normalizationObjIso hU).symm

/-- The identifications of the sections of `𝒪'` with the sections of the normalization are
natural in the affine open. -/
lemma normalizationSectionsIso_naturality (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    X.meromorphicIntegralClosure.right.presheaf.map (homOfLE h).op ≫
        (normalizationSectionsIso X hfinite U hU).hom =
      (normalizationSectionsIso X hfinite V hV).hom ≫
        (X.normalizationScheme hfinite).presheaf.map
          (homOfLE ((X.normalization hfinite).preimage_mono h)).op := by
  let := X.quasiCompactFromGenericPointResidueFields hfinite
  let := X.quasiSeparatedFromGenericPointResidueFields
  change X.meromorphicIntegralClosure.right.presheaf.map (homOfLE h).op ≫
      (closureGenericAlgEquiv X hfinite U hU).toRingEquiv.toCommRingCatIso.hom ≫
        (X.fromGenericPointResidueFields.normalizationObjIso hU).symm.hom =
    (closureGenericAlgEquiv X hfinite V hV).toRingEquiv.toCommRingCatIso.hom ≫
      (X.fromGenericPointResidueFields.normalizationObjIso hV).symm.hom ≫
        X.fromGenericPointResidueFields.normalization.presheaf.map
          (homOfLE
            (X.fromGenericPointResidueFields.fromNormalization.preimage_mono h)).op
  apply (cancel_mono (X.fromGenericPointResidueFields.normalizationObjIso hU).hom).mp
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [normalizationObjIso_naturality X.fromGenericPointResidueFields U V hU hV h]
  exact (closureGenericAlgEquiv_naturality X hfinite U V hU hV h).trans
    (congrArg (CategoryStruct.comp
        (closureGenericAlgEquiv X hfinite V hV).toRingEquiv.toCommRingCatIso.hom)
      (Iso.inv_hom_id_assoc (X.fromGenericPointResidueFields.normalizationObjIso hV)
        (X.fromGenericPointResidueFields.normalizationDiagram.map (homOfLE h).op)).symm)

/-- The identification of the sections of `𝒪'` with the sections of the normalization carries
the structure map of `𝒪'` to the normalization morphism. -/
lemma algebraMap_normalizationSectionsIso (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    X.meromorphicIntegralClosure.hom.hom.app (op U) ≫
        (normalizationSectionsIso X hfinite U hU).hom = (X.normalization hfinite).app U := by
  let := X.quasiCompactFromGenericPointResidueFields hfinite
  let := X.quasiSeparatedFromGenericPointResidueFields
  rw [X.fromGenericPointResidueFields.fromNormalization_app hU]
  dsimp only [normalizationSectionsIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc]
  congr 1
  ext x
  exact congrArg Subtype.val ((closureGenericAlgEquiv X hfinite U hU).commutes x)

/-! ### The charts of the relative spectrum -/

/-- Each chart of the normalization exhibits the spectrum of the sections of `𝒪'` over an affine
open as the preimage of that open. -/
lemma chart_isPullback (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (W : X.affineOpens) :
    IsPullback
      (Spec.map (normalizationSectionsIso X hfinite W.1 W.2).inv ≫
        (isAffineOpen_preimage_normalization X hfinite W.2).fromSpec)
      (specSectionsToOpen (X.meromorphicIntegralClosureSituation hfinite) W)
      (X.normalization hfinite) W.1.ι := by
  have hN := isAffineOpen_preimage_normalization X hfinite W.2
  let e := normalizationSectionsIso X hfinite W.1 W.2
  let E : Spec (X.meromorphicIntegralClosure.right.presheaf.obj (op W.1)) ≅
      (X.normalization hfinite ⁻¹ᵁ W.1).toScheme :=
    Scheme.Spec.mapIso e.symm.op ≪≫ hN.isoSpec.symm
  have hc : E.hom ≫ X.normalization hfinite ∣_ W.1 =
      specSectionsToOpen (X.meromorphicIntegralClosureSituation hfinite) W := by
    apply (cancel_mono W.1.ι).mp
    change Spec.map e.inv ≫ hN.isoSpec.inv ≫ (X.normalization hfinite ∣_ W.1) ≫ W.1.ι = _
    rw [morphismRestrict_ι]
    change Spec.map e.inv ≫ hN.fromSpec ≫ X.normalization hfinite = _
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec (X.normalization hfinite) W.2 hN le_rfl,
      ← Spec.map_comp_assoc]
    have ha : (X.normalization hfinite).appLE W.1 (X.normalization hfinite ⁻¹ᵁ W.1) le_rfl ≫
        e.inv = X.meromorphicIntegralClosure.hom.hom.app (op W.1) := by
      rw [← Scheme.Hom.app_eq_appLE, ← algebraMap_normalizationSectionsIso X hfinite W.1 W.2]
      exact e.comp_inv_eq.mpr rfl
    rw [ha]
    rfl
  refine (isPullback_morphismRestrict (X.normalization hfinite) W.1).flip.of_iso
    E.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change (X.normalization hfinite ⁻¹ᵁ W.1).ι ≫ 𝟙 _ =
      E.inv ≫ E.hom ≫ (X.normalization hfinite ⁻¹ᵁ W.1).ι
    simp only [Category.comp_id, Iso.inv_hom_id_assoc]
  · exact (Category.comp_id _).trans
      ((E.inv_hom_id_assoc _).symm.trans (congrArg (CategoryStruct.comp E.inv) hc))
  all_goals exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The charts of the normalization are compatible with restriction of the sections of `𝒪'`
along an inclusion of affine opens. -/
lemma chart_naturality (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (W W' : X.affineOpens) (h : W.1 ≤ W'.1) :
    Spec.map (X.meromorphicIntegralClosure.right.presheaf.map (homOfLE h).op) ≫
        Spec.map (normalizationSectionsIso X hfinite W'.1 W'.2).inv ≫
          (isAffineOpen_preimage_normalization X hfinite W'.2).fromSpec =
      Spec.map (normalizationSectionsIso X hfinite W.1 W.2).inv ≫
        (isAffineOpen_preimage_normalization X hfinite W.2).fromSpec := by
  let e := normalizationSectionsIso X hfinite W.1 W.2
  let e' := normalizationSectionsIso X hfinite W'.1 W'.2
  have hei : e'.inv ≫ X.meromorphicIntegralClosure.right.presheaf.map (homOfLE h).op =
      (X.normalizationScheme hfinite).presheaf.map
          (homOfLE ((X.normalization hfinite).preimage_mono h)).op ≫ e.inv := by
    apply (cancel_epi e'.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← normalizationSectionsIso_naturality X hfinite W.1 W'.1 W.2 W'.2 h,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Spec.map_comp_assoc, hei, Spec.map_comp, Category.assoc, IsAffineOpen.map_fromSpec]

end MeromorphicNormalization

/-! ### The comparison with the relative spectrum -/

/-- **Stacks Project, Tag 035T.** The normalization of a reduced scheme whose quasi-compact
opens have finitely many irreducible components, carrying the charts that present it as a
relative spectrum of the integral closure of `𝒪_X` in the sheaf of meromorphic functions. -/
@[stacks 035T "the normalization carries the charts of the relative spectrum",
  ega "II 7.4.6" "special case"]
def normalizationGluedSpectrum (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    GluedSpectrum (X.meromorphicIntegralClosureSituation hfinite) where
  scheme := X.normalizationScheme hfinite
  toBase := X.normalization hfinite
  chart W := Spec.map (MeromorphicNormalization.normalizationSectionsIso X hfinite W.1 W.2).inv ≫
    (MeromorphicNormalization.isAffineOpen_preimage_normalization X hfinite W.2).fromSpec
  chart_isPullback W := MeromorphicNormalization.chart_isPullback X hfinite W
  chart_naturality h := MeromorphicNormalization.chart_naturality X hfinite _ _ h

/-- **Stacks Project, Tag 035T.** For a reduced scheme whose quasi-compact opens have finitely
many irreducible components, the normalization is the relative spectrum of the integral closure
`𝒪'` of `𝒪_X` in the sheaf of meromorphic functions. -/
@[stacks 035T "the comparison isomorphism", ega "II 7.4.6" "special case"]
def normalizationIsoMeromorphicSpectrum (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    X.normalizationScheme hfinite ≅
      (gluedSpectrum (X.meromorphicIntegralClosureSituation hfinite)).scheme :=
  (existsUnique_gluedSpectrumIso _ (normalizationGluedSpectrum X hfinite)
    (gluedSpectrum _)).choose

/-- **Stacks Project, Tag 035T.** The comparison isomorphism lies over `X`: the normalization
morphism `ν : X^ν ⟶ X` is the structure morphism of the relative spectrum of `𝒪'`. -/
@[stacks 035T "the normalization is the structure morphism of the relative spectrum"]
theorem normalizationIsoMeromorphicSpectrum_hom_toBase (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    (normalizationIsoMeromorphicSpectrum X hfinite).hom ≫
        (gluedSpectrum (X.meromorphicIntegralClosureSituation hfinite)).toBase =
      X.normalization hfinite :=
  ((existsUnique_gluedSpectrumIso _ (normalizationGluedSpectrum X hfinite)
    (gluedSpectrum _)).choose_spec.1).1

end AlgebraicGeometry.Scheme

end
