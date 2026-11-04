module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMorphism
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraHomComparison
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.PairComposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralClosureAlgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.IntegralClosureSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of one scheme in another, as a relative spectrum

Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of schemes. Then `f_* 𝒪_Y` is a
quasi-coherent `𝒪_X`-algebra, and the integral closure `𝒪' ⊆ f_* 𝒪_Y` of `𝒪_X` in it is again
quasi-coherent ([Stacks, Tag 035F]). The *normalization of `X` in `Y`* is the relative spectrum
`ν : X' = Spec_X(𝒪') ⟶ X` ([Stacks, Tag 035H]), and it comes with a factorization
`Y ⟶ X' ⟶ X` of `f`, whose first map `f'` is the canonical morphism `Y ⟶ Spec_X(f_* 𝒪_Y)`
([Stacks, Tag 01LY]) followed by the morphism of relative spectra induced by `𝒪' ⊆ f_* 𝒪_Y`.

We show that `ν` is integral, `f'` is dominant, and the factorization is initial among the
factorizations of `f` through an integral morphism ([Stacks, Tag 035I]). In particular `X'` is
uniquely isomorphic, compatibly with both maps, to the relative normalization
`AlgebraicGeometry.Scheme.Hom.normalization`, which is built by gluing the spectra of the
integral closures over the affine opens of `X`.

## Main definitions

* `Stacks.RelativeNormalization.integralClosurePushforward`: the integral closure `𝒪'` of `𝒪_X`
  in `f_* 𝒪_Y`.
* `Stacks.RelativeNormalization.integralClosureSpectrum`: its relative spectrum `X'`, with
  structure morphism `ν`.
* `Stacks.RelativeNormalization.toIntegralClosureSpectrum`: the morphism `f' : Y ⟶ X'`.
* `Stacks.RelativeNormalization.integralClosureSpectrumIsoNormalization`: the isomorphism of
  `X'` with `f.normalization`.

## Main results

* `Stacks.RelativeNormalization.integralClosureSpectrum_isRelativeNormalization`: `f = ν ∘ f'`,
  the morphism `f'` is the canonical morphism to `Spec_X(f_* 𝒪_Y)` followed by the map of
  relative spectra induced by `𝒪' ⊆ f_* 𝒪_Y`, `ν` is integral, `f'` is dominant, every
  factorization of `f` through an integral morphism receives a unique compatible morphism from
  `X'`, and `X'` is uniquely isomorphic to `f.normalization` over `X` and under `Y`.

## References

* [Stacks Project, Section 0BAK](https://stacks.math.columbia.edu/tag/0BAK)
* [Stacks Project, Tag 035F](https://stacks.math.columbia.edu/tag/035F)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
* [Stacks Project, Tag 035I](https://stacks.math.columbia.edu/tag/035I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec
open AlgebraicGeometry.Scheme.QuasicoherentAlgebra

universe u

namespace Stacks.RelativeNormalization

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- The integral closure `𝒪'` of `𝒪_X` in the `𝒪_X`-algebra `f_* 𝒪_Y`, as a sheaf of
`𝒪_X`-algebras. -/
@[ega "IV 8.12.3" "the O_Y-algebra C"]
abbrev integralClosurePushforward : X.QuasicoherentAlgebra :=
  integralClosureAlgebra (pushforwardAlgebra f)

variable [QuasiCompact f] [QuasiSeparated f]

/-- For `f` quasi-compact and quasi-separated, the integral closure `𝒪'` of `𝒪_X` in
`f_* 𝒪_Y` is quasi-coherent. -/
@[ega "IV 18.12.14" "partial"]
instance isQuasicoherent_integralClosurePushforward :
    AlgebraSheaf.IsQuasicoherent (integralClosurePushforward f) :=
  have : (underlyingModule (pushforwardAlgebra f)).IsQuasicoherent :=
    AlgebraSheaf.isQuasicoherent_pushforwardAlgebra f
  isQuasicoherent_integralClosureAlgebra (pushforwardAlgebra f)

/-- The relative-spectrum situation given by the quasi-coherent `𝒪_X`-algebra `𝒪'`. -/
@[ega "IV 18.12.14" "partial"]
abbrev integralClosureSituation : RelativeSpecSituation.{u} :=
  situation (integralClosurePushforward f)

/-- The relative spectrum `X' = Spec_X(𝒪')` of the integral closure of `𝒪_X` in `f_* 𝒪_Y`,
together with its structure morphism `ν : X' ⟶ X` and its affine charts: the normalization of
`X` in `Y`. -/
@[ega "II 7.4.6" "more general", ega "IV 18.12.14", ega "IV 8.12.3"]
abbrev integralClosureSpectrum : GluedSpectrum (integralClosureSituation f) :=
  gluedSpectrum (integralClosureSituation f)

/-- The relative-spectrum pair over `Y` consisting of `f` and the inclusion
`𝒪' ⊆ f_* 𝒪_Y`. -/
def integralClosurePair : RelativeSpecPair (integralClosureSituation f) Y :=
  ⟨f, algebraHomAsUnder (integralClosureAlgebraι (pushforwardAlgebra f))⟩

/-- The morphism `f' : Y ⟶ X'` of the factorization `f = ν ∘ f'`: the morphism classified by
`f` together with the inclusion `𝒪' ⊆ f_* 𝒪_Y`. -/
@[ega "IV 18.12.14"]
def toIntegralClosureSpectrum : Y ⟶ (integralClosureSpectrum f).scheme :=
  pairToHom (integralClosurePair f)

/-- The factorization `f = ν ∘ f'`. -/
theorem toIntegralClosureSpectrum_toBase :
    toIntegralClosureSpectrum f ≫ (integralClosureSpectrum f).toBase = f :=
  pairToHom_toBase (integralClosurePair f)

/-- Over an affine open `U` of `X`, the sections of `𝒪'` are integral over `Γ(X, U)`. -/
theorem isIntegral_integralClosurePushforward_app (U : X.Opens) (hU : IsAffineOpen U) :
    ((integralClosurePushforward f).hom.hom.app (op U)).hom.IsIntegral := by
  have : (underlyingModule (pushforwardAlgebra f)).IsQuasicoherent :=
    AlgebraSheaf.isQuasicoherent_pushforwardAlgebra f
  intro x
  set ι := (integralClosureAlgebraι (pushforwardAlgebra f)).right.hom.app (op U)
  let : Algebra Γ(X, U) ((pushforwardAlgebra f).right.presheaf.obj (op U)) :=
    ((pushforwardAlgebra f).hom.hom.app (op U)).hom.toAlgebra
  have hx : ι x ∈ integralClosure Γ(X, U) ((pushforwardAlgebra f).right.presheaf.obj (op U)) := by
    rw [← SetLike.mem_coe, ← range_integralClosureAlgebraι_app_of_isAffineOpen _ U hU]
    exact ⟨x, rfl⟩
  obtain ⟨P, hPm, hP⟩ := hx
  refine ⟨P, hPm, injective_integralClosureAlgebraι_app (pushforwardAlgebra f) U ?_⟩
  have hw : ι.hom.comp ((integralClosurePushforward f).hom.hom.app (op U)).hom =
      algebraMap Γ(X, U) ((pushforwardAlgebra f).right.presheaf.obj (op U)) :=
    congrArg (fun k => (k.hom.app (op U)).hom)
      (Under.w (integralClosureAlgebraι (pushforwardAlgebra f)))
  refine (Polynomial.hom_eval₂ P _ ι.hom x).trans ?_
  exact (congrArg (fun φ => Polynomial.eval₂ φ (ι.hom x) P) hw).trans
    (hP.trans (map_zero ι.hom).symm)

/-- The structure morphism `ν : X' ⟶ X` is integral. -/
instance isIntegralHom_toBase : IsIntegralHom (integralClosureSpectrum f).toBase := by
  have _ : IsAffineHom (integralClosureSpectrum f).toBase := isAffineHom_relativeSpecToBase _
  have _ : (RingHom.toMorphismProperty RingHom.IsIntegral).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  refine ⟨fun U hU => ?_⟩
  have _ := isIso_universalAlgebraMap_app (integralClosureSituation f) ⟨U, hU⟩
  rw [toBase_app]
  exact MorphismProperty.RespectsIso.postcomp
    (RingHom.toMorphismProperty RingHom.IsIntegral) _ _
    (isIntegral_integralClosurePushforward_app f U hU)

/-- The morphism from the relative normalization of `f` to `X'` given by the universal
property of the former, applied to the integral factorization `f = ν ∘ f'`. -/
def normalizationToIntegralClosureSpectrum :
    f.normalization ⟶ (integralClosureSpectrum f).scheme :=
  f.normalizationDesc (toIntegralClosureSpectrum f) (integralClosureSpectrum f).toBase
    (toIntegralClosureSpectrum_toBase f).symm

/-- The comparison morphism lies over `X`. -/
theorem normalizationToIntegralClosureSpectrum_toBase :
    normalizationToIntegralClosureSpectrum f ≫ (integralClosureSpectrum f).toBase =
      f.fromNormalization :=
  f.normalizationDesc_comp _ _ (toIntegralClosureSpectrum_toBase f).symm

/-- The comparison morphism lies under `Y`. -/
theorem toNormalization_normalizationToIntegralClosureSpectrum :
    f.toNormalization ≫ normalizationToIntegralClosureSpectrum f = toIntegralClosureSpectrum f :=
  f.toNormalization_normalizationDesc _ _ (toIntegralClosureSpectrum_toBase f).symm

/-- The comparison morphism is integral. -/
instance isIntegralHom_normalizationToIntegralClosureSpectrum :
    IsIntegralHom (normalizationToIntegralClosureSpectrum f) :=
  inferInstanceAs (IsIntegralHom (f.normalizationDesc (toIntegralClosureSpectrum f)
    (integralClosureSpectrum f).toBase (toIntegralClosureSpectrum_toBase f).symm))

/-- `f'` is the canonical morphism `Y ⟶ Spec_X(f_* 𝒪_Y)` followed by the morphism of relative
spectra induced by the inclusion `𝒪' ⊆ f_* 𝒪_Y`. -/
theorem toRelativeSpec_comp_relativeSpectrumMapOfAlgebraHom :
    toRelativeSpec f ≫ relativeSpectrumMapOfAlgebraHom (integralClosureSituation f)
        (pushforwardAlgebra f) (AlgebraSheaf.isQuasicoherent_pushforwardAlgebra f)
        (integralClosureAlgebraι (pushforwardAlgebra f)) =
      toIntegralClosureSpectrum f := by
  have hnat := NatTrans.naturality_apply
    (relativeSpecFunctorMapOfAlgebraHom (integralClosureSituation f) (pushforwardAlgebra f)
      (AlgebraSheaf.isQuasicoherent_pushforwardAlgebra f)
      (integralClosureAlgebraι (pushforwardAlgebra f)))
    (toRelativeSpec f).op (universalRelativeSpecPair (pushforwardSituation f))
  have hpb : RelativeSpecPair.pullback (toRelativeSpec f)
      (universalRelativeSpecPair (pushforwardSituation f)) = pushforwardPair f :=
    pullback_universalRelativeSpecPair_pairToHom (pushforwardPair f)
  refine (comp_pairToHom (toRelativeSpec f) _).trans (congrArg pairToHom ?_)
  refine hnat.symm.trans ((congrArg (fun p => (relativeSpecFunctorMapOfAlgebraHom
    (integralClosureSituation f) (pushforwardAlgebra f)
    (AlgebraSheaf.isQuasicoherent_pushforwardAlgebra f)
    (integralClosureAlgebraι (pushforwardAlgebra f))).app (op Y) p) hpb).trans ?_)
  exact Sigma.ext rfl (heq_of_eq (Category.comp_id _))

/-- On sections over an affine open `U`, the universal algebra map followed by `f'` is the
inclusion `𝒪' ⊆ f_* 𝒪_Y`. -/
private theorem universalAlgebraMap_comp_appLE (U : X.affineOpens)
    (e : f ⁻¹ᵁ U.1 ≤ toIntegralClosureSpectrum f ⁻¹ᵁ ((integralClosureSpectrum f).toBase ⁻¹ᵁ U.1)) :
    (universalAlgebraMap (integralClosureSituation f)).right.app (op U.1) ≫
      (toIntegralClosureSpectrum f).appLE ((integralClosureSpectrum f).toBase ⁻¹ᵁ U.1)
        (f ⁻¹ᵁ U.1) e =
      (integralClosureAlgebraι (pushforwardAlgebra f)).right.hom.app (op U.1) :=
  pairToHom_appLE (integralClosurePair f) U e

/-- Over an affine open `U` of `X`, the map on sections of `f'` from `Γ(X', ν⁻¹U)` to
`Γ(Y, f⁻¹U)` is injective. -/
theorem injective_toIntegralClosureSpectrum_appLE (U : X.affineOpens)
    (e : f ⁻¹ᵁ U.1 ≤ toIntegralClosureSpectrum f ⁻¹ᵁ ((integralClosureSpectrum f).toBase ⁻¹ᵁ U.1)) :
    Function.Injective ((toIntegralClosureSpectrum f).appLE
      ((integralClosureSpectrum f).toBase ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) e) := by
  have _ := isIso_universalAlgebraMap_app (integralClosureSituation f) U
  have h := universalAlgebraMap_comp_appLE f U e
  intro a b hab
  obtain ⟨a', rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((universalAlgebraMap (integralClosureSituation f)).right.app (op U.1))).2 a
  obtain ⟨b', rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((universalAlgebraMap (integralClosureSituation f)).right.app (op U.1))).2 b
  have ha := ConcreteCategory.congr_hom h a'
  have hb := ConcreteCategory.congr_hom h b'
  rw [ConcreteCategory.comp_apply] at ha hb
  have hab' := ha.symm.trans (hab.trans hb)
  exact congrArg _ (injective_integralClosureAlgebraι_app (pushforwardAlgebra f) U.1 hab')

/-- Over an affine open `U`, every section of `f.normalization` over the preimage of `U` is
carried by `f.toNormalization` into the image of the sections of `f'`. -/
theorem toNormalization_appLE_mem_range (U : X.affineOpens)
    (e : f ⁻¹ᵁ U.1 ≤ toIntegralClosureSpectrum f ⁻¹ᵁ ((integralClosureSpectrum f).toBase ⁻¹ᵁ U.1))
    (y : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U.1)) :
    f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (IntegralClosure.SheafLevel.preimage_toNormalization_fromNormalization f U.1).ge y ∈
      Set.range ((toIntegralClosureSpectrum f).appLE
        ((integralClosureSpectrum f).toBase ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) e) := by
  have : (underlyingModule (pushforwardAlgebra f)).IsQuasicoherent :=
    AlgebraSheaf.isQuasicoherent_pushforwardAlgebra f
  let := (f.app U.1).hom.toAlgebra
  have hy : f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (IntegralClosure.SheafLevel.preimage_toNormalization_fromNormalization f U.1).ge y =
      (((f.normalizationObjIso U.2).hom y : integralClosure Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)) :
        Γ(Y, f ⁻¹ᵁ U.1)) :=
    (ConcreteCategory.congr_hom
      (IntegralClosure.SheafLevel.normalizationAlgebraι_app f U.1).symm y).trans
      (IntegralClosure.SheafLevel.normalizationAlgebraι_app_apply f U.2 y)
  have hmem := ((f.normalizationObjIso U.2).hom y).2
  rw [← hy, ← SetLike.mem_coe] at hmem
  obtain ⟨z, hz⟩ := (Set.ext_iff.mp
    (range_integralClosureAlgebraι_app_of_isAffineOpen (pushforwardAlgebra f) U.1 U.2) _).mpr hmem
  have _ := isIso_universalAlgebraMap_app (integralClosureSituation f) U
  have h := universalAlgebraMap_comp_appLE f U e
  refine ⟨(universalAlgebraMap (integralClosureSituation f)).right.app (op U.1) z, ?_⟩
  rwa [← ConcreteCategory.comp_apply, h]

/-- The comparison morphism from `f.normalization` to `X'` is an isomorphism. -/
instance isIso_normalizationToIntegralClosureSpectrum :
    IsIso (normalizationToIntegralClosureSpectrum f) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme) fun y ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((integralClosureSpectrum f).toBase y)) isOpen_univ
  refine ⟨(integralClosureSpectrum f).toBase ⁻¹ᵁ U, hyU,
    (isIso_morphismRestrict_iff_isIso_app (normalizationToIntegralClosureSpectrum f)
      (hU.preimage _)).2 ?_⟩
  have hV : normalizationToIntegralClosureSpectrum f ⁻¹ᵁ
      ((integralClosureSpectrum f).toBase ⁻¹ᵁ U) = f.fromNormalization ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, normalizationToIntegralClosureSpectrum_toBase]
  have e : f ⁻¹ᵁ U ≤
      toIntegralClosureSpectrum f ⁻¹ᵁ ((integralClosureSpectrum f).toBase ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, toIntegralClosureSpectrum_toBase]
  have e₂ := (IntegralClosure.SheafLevel.preimage_toNormalization_fromNormalization f U).ge
  have hcomp : (normalizationToIntegralClosureSpectrum f).appLE
        ((integralClosureSpectrum f).toBase ⁻¹ᵁ U) (f.fromNormalization ⁻¹ᵁ U) hV.ge ≫
      f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U) e₂ =
      (toIntegralClosureSpectrum f).appLE ((integralClosureSpectrum f).toBase ⁻¹ᵁ U)
        (f ⁻¹ᵁ U) e := by
    rw [Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact toNormalization_normalizationToIntegralClosureSpectrum f
  have hm := injective_toIntegralClosureSpectrum_appLE f ⟨U, hU⟩ e
  have hg : Function.Injective
      (f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U) e₂) := fun a b hab ↦
    IntegralClosure.SheafLevel.injective_normalizationAlgebraι_app f U <|
      (ConcreteCategory.congr_hom
        (IntegralClosure.SheafLevel.normalizationAlgebraι_app f U) a).trans
        (hab.trans (ConcreteCategory.congr_hom
          (IntegralClosure.SheafLevel.normalizationAlgebraι_app f U) b).symm)
  have hk : Function.Bijective ((normalizationToIntegralClosureSpectrum f).appLE
      ((integralClosureSpectrum f).toBase ⁻¹ᵁ U) (f.fromNormalization ⁻¹ᵁ U) hV.ge) := by
    refine ⟨fun a b hab => hm ?_, fun t => ?_⟩
    · rw [← hcomp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hab]
    · obtain ⟨x, hx⟩ := toNormalization_appLE_mem_range f ⟨U, hU⟩ e t
      refine ⟨x, hg ?_⟩
      rw [← ConcreteCategory.comp_apply, hcomp, hx]
  have hiso : IsIso ((normalizationToIntegralClosureSpectrum f).appLE
      ((integralClosureSpectrum f).toBase ⁻¹ᵁ U) (f.fromNormalization ⁻¹ᵁ U) hV.ge) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hk
  have hh : IsIso (homOfLE hV.ge : f.fromNormalization ⁻¹ᵁ U ⟶ _) :=
    CategoryTheory.homOfLE_isIso_of_eq _ hV.symm
  rw [Scheme.Hom.appLE] at hiso
  exact (isIso_comp_right_iff _ _).mp hiso

/-- The relative spectrum `X'` of the integral closure of `𝒪_X` in `f_* 𝒪_Y` is isomorphic to
the relative normalization of `f`. -/
def integralClosureSpectrumIsoNormalization :
    (integralClosureSpectrum f).scheme ≅ f.normalization :=
  (asIso (normalizationToIntegralClosureSpectrum f)).symm

/-- The isomorphism `X' ≅ f.normalization` lies under `Y`. -/
theorem toIntegralClosureSpectrum_integralClosureSpectrumIsoNormalization_hom :
    toIntegralClosureSpectrum f ≫ (integralClosureSpectrumIsoNormalization f).hom =
      f.toNormalization := by
  simp only [integralClosureSpectrumIsoNormalization, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq,
    toNormalization_normalizationToIntegralClosureSpectrum]

/-- The isomorphism `X' ≅ f.normalization` lies over `X`. -/
theorem integralClosureSpectrumIsoNormalization_hom_fromNormalization :
    (integralClosureSpectrumIsoNormalization f).hom ≫ f.fromNormalization =
      (integralClosureSpectrum f).toBase := by
  simp only [integralClosureSpectrumIsoNormalization, Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq,
    normalizationToIntegralClosureSpectrum_toBase]

/-- The morphism `f' : Y ⟶ X'` is dominant. -/
instance isDominant_toIntegralClosureSpectrum : IsDominant (toIntegralClosureSpectrum f) := by
  rw [← toNormalization_normalizationToIntegralClosureSpectrum]
  infer_instance

/-- The relative spectrum `X'` is isomorphic to `f.normalization` by a unique isomorphism that
is compatible with the maps from `Y` and the maps to `X`. -/
theorem existsUnique_integralClosureSpectrum_iso_normalization :
    ∃! e : (integralClosureSpectrum f).scheme ≅ f.normalization,
      toIntegralClosureSpectrum f ≫ e.hom = f.toNormalization ∧
        e.hom ≫ f.fromNormalization = (integralClosureSpectrum f).toBase := by
  refine ⟨integralClosureSpectrumIsoNormalization f,
    ⟨toIntegralClosureSpectrum_integralClosureSpectrumIsoNormalization_hom f,
      integralClosureSpectrumIsoNormalization_hom_fromNormalization f⟩, ?_⟩
  rintro e ⟨he₁, he₂⟩
  have hinv : e.inv = (integralClosureSpectrumIsoNormalization f).inv := by
    refine Scheme.Hom.normalization.hom_ext (f := f) _ _ (integralClosureSpectrum f).toBase
      ?_ ?_ (normalizationToIntegralClosureSpectrum_toBase f)
    · exact ((Iso.comp_inv_eq e).mpr he₁.symm).trans
        (toNormalization_normalizationToIntegralClosureSpectrum f).symm
    · exact (Iso.inv_comp_eq e).mpr he₂.symm
  exact Iso.ext ((Iso.inv_eq_inv _ _).mp hinv)

/-- **Relative normalization.** Let `f : Y ⟶ X` be a
quasi-compact and quasi-separated morphism of schemes, let `𝒪' ⊆ f_* 𝒪_Y` be the integral
closure of `𝒪_X` in `f_* 𝒪_Y`, and let `ν : X' = Spec_X(𝒪') ⟶ X` be its relative spectrum, the
normalization of `X` in `Y`. Then:

* `f` factors as `f = ν ∘ f'`, where `f' : Y ⟶ X'` is the canonical morphism
  `Y ⟶ Spec_X(f_* 𝒪_Y)` followed by the morphism of relative spectra induced by the inclusion
  `𝒪' ⊆ f_* 𝒪_Y`;
* `ν` is integral and `f'` is dominant;
* for every factorization `f = π ∘ g` with `π : Z ⟶ X` integral there is a unique
  `h : X' ⟶ Z` with `h ∘ f' = g` and `π ∘ h = ν`;
* consequently `X'` is uniquely isomorphic, under `Y` and over `X`, to the relative
  normalization `f.normalization`. -/
@[stacks 0BAK, ega "IV 18.10.10" "more general", ega "IV 18.12.14" "partial", ega "IV 8.12.3"]
theorem integralClosureSpectrum_isRelativeNormalization :
    toIntegralClosureSpectrum f ≫ (integralClosureSpectrum f).toBase = f ∧
    toRelativeSpec f ≫ relativeSpectrumMapOfAlgebraHom (integralClosureSituation f)
        (pushforwardAlgebra f) (AlgebraSheaf.isQuasicoherent_pushforwardAlgebra f)
        (integralClosureAlgebraι (pushforwardAlgebra f)) = toIntegralClosureSpectrum f ∧
    IsIntegralHom (integralClosureSpectrum f).toBase ∧
    IsDominant (toIntegralClosureSpectrum f) ∧
    (∀ (Z : Scheme.{u}) (g : Y ⟶ Z) (π : Z ⟶ X), IsIntegralHom π → g ≫ π = f →
      ∃! h : (integralClosureSpectrum f).scheme ⟶ Z,
        toIntegralClosureSpectrum f ≫ h = g ∧ h ≫ π = (integralClosureSpectrum f).toBase) ∧
    ∃! e : (integralClosureSpectrum f).scheme ≅ f.normalization,
      toIntegralClosureSpectrum f ≫ e.hom = f.toNormalization ∧
        e.hom ≫ f.fromNormalization = (integralClosureSpectrum f).toBase :=
  ⟨toIntegralClosureSpectrum_toBase f, toRelativeSpec_comp_relativeSpectrumMapOfAlgebraHom f,
    inferInstance, inferInstance,
    (Scheme.Hom.normalization_universalProperty_iff_existsUnique_iso f _ _
      (toIntegralClosureSpectrum_toBase f)).mpr
        (existsUnique_integralClosureSpectrum_iso_normalization f),
    existsUnique_integralClosureSpectrum_iso_normalization f⟩

end Stacks.RelativeNormalization

end
