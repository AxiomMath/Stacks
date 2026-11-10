module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient
public import StacksFrontier.AlgebraicGeometry.GenericPointProduct.Comparison
public import StacksFrontier.AlgebraicGeometry.GenericPointProduct.Decomposition
public import StacksFrontier.AlgebraicGeometry.GenericPointSheaf.StalkUnits
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.MeromorphicRelativeSpec
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic

/-!
# Meromorphic functions on a reduced scheme as a pushforward from its generic points

Let `X` be a scheme such that every quasi-compact open has finitely many irreducible components,
and let `f : Y ⟶ X` be the canonical morphism from the coproduct `Y` of the spectra of the residue
fields at the generic points of `X`; the normalization of `X` is the relative normalization of `X`
in `f`. If `X` is reduced, the sheaf of meromorphic functions `𝒦_X` of `X` is `f_* 𝒪_Y`, as a sheaf
of `𝒪_X`-algebras.

The other assertions of [Stacks, Section 035E] are attached to the declarations proving them: the
morphism `f` is quasi-compact and quasi-separated, a locally Noetherian scheme satisfies the
finiteness hypothesis, the normalization of `X` is the normalization of its reduction, and for
reduced `X` the normalization is the relative spectrum of the integral closure of `𝒪_X` in `𝒦_X`.

## Main definitions

* `AlgebraicGeometry.Scheme.totalQuotientSheafToGenericPointPushforward`: the comparison
  morphism `𝒦_X ⟶ f_* 𝒪_Y`.

## Main results

* `AlgebraicGeometry.Scheme.exists_totalQuotientSheaf_iso_pushforward`: on a reduced scheme whose
  quasi-compact opens have finitely many irreducible components, `𝒦_X ≅ f_* 𝒪_Y` as sheaves of
  `𝒪_X`-algebras.

## References

* [Stacks Project, Section 035E](https://stacks.math.columbia.edu/tag/035E)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 035T](https://stacks.math.columbia.edu/tag/035T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})

open Stacks.AlgebraicGeometry.GenericPointProduct Stacks.AlgebraicGeometry.GenericPointSheaf

/-! ### The sheaf of meromorphic functions of a reduced scheme -/

/-- A section of `𝒪_X` whose germs are nonzerodivisors becomes a unit in `f_* 𝒪_Y`, where
`f : Y ⟶ X` is the canonical morphism from the generic-point residue spectrum. -/
theorem isUnit_fromGenericPointResidueFields_app (U : (Opens X)ᵒᵖ)
    (y : (nzdSubmonoidPresheaf X).obj U) :
    IsUnit ((fromGenericPointResidueFields X).app U.unop y.1) := by
  refine (genericPointResidueSpectrum X).toRingedSpace.isUnit_of_isUnit_germ _ _
    fun s hs ↦ ?_
  change IsUnit ((genericPointResidueSpectrum X).presheaf.germ _ s hs _)
  rw [← Scheme.Hom.germ_stalkMap_apply (fromGenericPointResidueFields X) U.unop s hs]
  exact .map _ <| isUnit_of_mem_nonZeroDivisors_stalk
    (mem_genericPoints_fromGenericPointResidueFields X s) (Submonoid.mem_iInf.mp y.2 ⟨_, hs⟩)

/-- The component over an open `U` of the comparison from the presheaf of total quotient rings
to `f_* 𝒪_Y`: the extension of `f^♯` along the objectwise localization. -/
def totalQuotientToGenericPointPushforwardApp (U : (Opens X)ᵒᵖ) :
    X.presheaf.totalQuotientPresheaf.obj U ⟶
      ((fromGenericPointResidueFields X).base _* (genericPointResidueSpectrum X).presheaf).obj U :=
  CommRingCat.ofHom (IsLocalization.lift (M := (nzdSubmonoidPresheaf X).obj U)
    (S := (nzdSubmonoidPresheaf X).localizationPresheaf.obj U)
    (g := ((fromGenericPointResidueFields X).c.app U).hom)
    (isUnit_fromGenericPointResidueFields_app X U))

/-- On the image of a section `r` of `𝒪_X` in the total quotient presheaf, the comparison over
`U` agrees with `f^♯` applied to `r`. -/
@[simp]
theorem totalQuotientToGenericPointPushforwardApp_apply (U : (Opens X)ᵒᵖ)
    (r : X.presheaf.obj U) :
    totalQuotientToGenericPointPushforwardApp X U (X.presheaf.toTotalQuotientPresheaf.app U r) =
      (fromGenericPointResidueFields X).c.app U r :=
  IsLocalization.lift_eq (S := (nzdSubmonoidPresheaf X).localizationPresheaf.obj U)
    (isUnit_fromGenericPointResidueFields_app X U) r

/-- The comparison morphism from the presheaf of total quotient rings of `X` to `f_* 𝒪_Y`. -/
def totalQuotientToGenericPointPushforward :
    X.presheaf.totalQuotientPresheaf ⟶
      (fromGenericPointResidueFields X).base _* (genericPointResidueSpectrum X).presheaf where
  app := totalQuotientToGenericPointPushforwardApp X
  naturality {U V} i := by
    refine hom_ext_totalQuotient X fun r ↦ ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, toTotalQuotientPresheaf_map,
      totalQuotientToGenericPointPushforwardApp_apply,
      totalQuotientToGenericPointPushforwardApp_apply]
    exact ConcreteCategory.congr_hom ((fromGenericPointResidueFields X).c.naturality i) r

/-- On an affine open of a reduced scheme whose quasi-compact opens have finitely many
irreducible components, the comparison from the total quotient presheaf to `f_* 𝒪_Y` is an
isomorphism. -/
theorem isIso_totalQuotientToGenericPointPushforward_app [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    IsIso ((totalQuotientToGenericPointPushforward X).app (op U)) := by
  classical
  have : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hX U hU.isCompact)).to_subtype
  have : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_injective (Scheme.genericPointsInOpenEquiv X U)
      (Scheme.genericPointsInOpenEquiv X U).injective
  let M := (nzdSubmonoidPresheaf X).obj (op U)
  let S := Γ(genericPointResidueSpectrum X, fromGenericPointResidueFields X ⁻¹ᵁ U)
  let := algebraTotalQuotientObj X (op U)
  let := isLocalizationTotalQuotientObj X (op U)
  let : Algebra Γ(X, U) S := ((fromGenericPointResidueFields X).app U).hom.toAlgebra
  have hM : M = Γ(X, U)⁰ := submonoidPresheafOfStalk_obj_eq_nonZeroDivisors X U hU
  have : IsLocalization M S := by
    rw [hM]
    exact IsLocalization.isLocalization_of_algEquiv Γ(X, U)⁰
      (genericPreimageSectionsAlgEquivFractionRing U hU).symm
  let e := IsLocalization.algEquiv M (X.presheaf.totalQuotientPresheaf.obj (op U)) S
  have he : (totalQuotientToGenericPointPushforward X).app (op U) =
      CommRingCat.ofHom e.toRingEquiv.toRingHom := by
    refine hom_ext_totalQuotient X fun r ↦ ?_
    change totalQuotientToGenericPointPushforwardApp X (op U)
      (X.presheaf.toTotalQuotientPresheaf.app (op U) r) = _
    rw [totalQuotientToGenericPointPushforwardApp_apply]
    exact (e.commutes r).symm
  rw [he]
  exact (e.toRingEquiv.toCommRingCatIso).isIso_hom

/-- The comparison morphism from the sheaf of total quotient rings of `X` to `f_* 𝒪_Y`, the
sheafification of `AlgebraicGeometry.Scheme.totalQuotientToGenericPointPushforward`. -/
def totalQuotientSheafToGenericPointPushforward :
    X.totalQuotientSheaf.presheaf ⟶
      (fromGenericPointResidueFields X).base _* (genericPointResidueSpectrum X).presheaf :=
  sheafifyLift (Opens.grothendieckTopology X) (totalQuotientToGenericPointPushforward X)
    ((TopCat.Sheaf.pushforward CommRingCat (fromGenericPointResidueFields X).base).obj
      (genericPointResidueSpectrum X).sheaf).property

/-- The comparison morphism `𝒦_X ⟶ f_* 𝒪_Y` is a morphism of `𝒪_X`-algebras. -/
@[reassoc (attr := simp)]
theorem toTotalQuotientSheaf_comp_totalQuotientSheafToGenericPointPushforward :
    X.toTotalQuotientSheaf.hom ≫ totalQuotientSheafToGenericPointPushforward X =
      (fromGenericPointResidueFields X).c := by
  ext U r
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_sheafifyLift
    (Opens.grothendieckTopology X) (totalQuotientToGenericPointPushforward X)
    ((TopCat.Sheaf.pushforward CommRingCat (fromGenericPointResidueFields X).base).obj
      (genericPointResidueSpectrum X).sheaf).property) U)
    (X.presheaf.toTotalQuotientPresheaf.app U r)
  exact h.trans (totalQuotientToGenericPointPushforwardApp_apply X U r)

/-- On a reduced scheme whose quasi-compact opens have finitely many irreducible components, the
comparison morphism `𝒦_X ⟶ f_* 𝒪_Y` is an isomorphism. -/
theorem isIso_totalQuotientSheafToGenericPointPushforward [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsIso (totalQuotientSheafToGenericPointPushforward X) :=
  isIso_sheafifyLift_of_isIso_basis
    (G := (TopCat.Sheaf.pushforward CommRingCat (fromGenericPointResidueFields X).base).obj
      (genericPointResidueSpectrum X).sheaf)
    (isBasis_range_affineOpens X) (totalQuotientToGenericPointPushforward X)
    (fun V ↦ isIso_totalQuotientToGenericPointPushforward_app X hX V.2)

/-- Let `X` be a reduced scheme whose quasi-compact opens have finitely many irreducible
components, and let `f : Y ⟶ X` be the canonical morphism from the coproduct of the spectra of the
residue fields at the generic points of `X`. Then the sheaf of meromorphic functions of `X` is
`f_* 𝒪_Y`, as a sheaf of `𝒪_X`-algebras. -/
@[stacks 035E "K_X = f_* O_Y for X reduced", ega "II 6.3.6" "special case"]
theorem exists_totalQuotientSheaf_iso_pushforward [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∃ e : X.totalQuotientSheaf.presheaf ≅
        (fromGenericPointResidueFields X).base _* (genericPointResidueSpectrum X).presheaf,
      X.toTotalQuotientSheaf.hom ≫ e.hom = (fromGenericPointResidueFields X).c :=
  let := isIso_totalQuotientSheafToGenericPointPushforward X hX
  ⟨asIso (totalQuotientSheafToGenericPointPushforward X),
    toTotalQuotientSheaf_comp_totalQuotientSheafToGenericPointPushforward X⟩

/-! ### Further properties of the morphism from the generic points and of the normalization -/

add_to_stacks 035E "the morphism (035M) is quasi-compact"
  AlgebraicGeometry.Scheme.quasiCompactFromGenericPointResidueFields
add_to_stacks 035E "the morphism (035M) is quasi-separated"
  AlgebraicGeometry.Scheme.quasiSeparatedFromGenericPointResidueFields
add_to_stacks 035E "a locally Noetherian scheme has locally finitely many irreducible components"
  Stacks.AlgebraicGeometry.GenericPointProduct.finiteComponentsOnCompactOpens_of_isLocallyNoetherian
add_to_stacks 035E "the normalization of X is the normalization of X_red"
  AlgebraicGeometry.Scheme.existsUnique_iso_normalizationScheme_reduction
add_to_stacks 035E "for X reduced, the normalization is the relative spectrum of the integral \
    closure of O_X in K_X"
  AlgebraicGeometry.Scheme.normalizationIsoMeromorphicSpectrum_hom_toBase

end Scheme

end AlgebraicGeometry
