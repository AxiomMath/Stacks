module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGeometricallyReducedConnectedOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.AlgebraicClosureSite

/-!
# `Curves^{grc,1} ⊂ Curves^{h0,1}`

Stacks 0E6L: the open substack of `Curves` of families whose geometric fibres are reduced,
connected and of dimension `1` lies in the open substack `Curves^{h0,1}` of families with
`f_*𝒪_X = 𝒪_S` universally and fibres of dimension `1`.

The proof in the source: the fibre `X_k` of such a family over a field-valued point `Spec k → S`
is a proper algebraic space over `k` which is geometrically reduced and geometrically connected,
so `k = H⁰(X_k, 𝒪_{X_k})` (Stacks 0DMY (7), the algebraic-space form of Stacks 0BUG (7)); and a
family of curves whose fibres over fields have `k = H⁰(X_k, 𝒪_{X_k})` has `f_*𝒪_X = 𝒪_S`
universally (Stacks 0E6I, through Stacks 0E6B (a)).

## Main results

* `AlgebraicGeometry.Space.isGeometricallyConnected_fibreOverFieldValuedPoint`: if every
  geometric fibre of `f : X ⟶ Y` has one connected component (the function of Stacks 0E1B is
  `1`), then the fibre over every field-valued point is geometrically connected (Stacks 0A0Z).
* `AlgebraicGeometry.Space.isProper_toYonedaId_fibreOverFieldValuedPoint`: the fibre of a proper
  morphism over a field-valued point is proper over the field.
* `AlgebraicGeometry.Space.isGeometricallyReduced_fibreOverFieldValuedPoint`: the fibre over a
  field-valued point at which the fibre is geometrically reduced (Stacks 0E08) is a geometrically
  reduced algebraic space over the field (Stacks 0DMQ).
* `AlgebraicGeometry.isGrc1CurveFamily_le_isH01CurveFamily_of`: the inclusion
  `Curves^{grc,1} ⊂ Curves^{h0,1}`, from the statement of Stacks 0DMY (7) for algebraic spaces and
  the input of Stacks 0E6I that `k = H⁰(X_k, 𝒪_{X_k})` on all fibres over fields gives
  `f_*𝒪_X = 𝒪_S` universally; `isGrc1CurveFamily_le_isH01CurveFamily_of_structureSharp` takes
  the statement of Stacks 0E6B (a) instead of the second input.
* `AlgebraicGeometry.CurveFamily.firstHigherDirectImage_of_isGrc1CurveFamily_of`: for such a
  family `R¹f_*𝒪_X` is finite locally free and its formation commutes with arbitrary base
  change, from parts (2) and (3) of Stacks 0E1J.

## Implementation notes

The statements of Stacks 0DMY (7) for algebraic spaces, of Stacks 0E6I (through Stacks 0E6B (a))
and of parts (2) and (3) of Stacks 0E1J enter as the explicit hypotheses `hconst`, `hpush` (or
`hstruct`), `hR1` and `hR1bc`.

## References

* [Stacks Project, Tag 0E6L](https://stacks.math.columbia.edu/tag/0E6L)
* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E1I](https://stacks.math.columbia.edu/tag/0E1I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The fibre over a field-valued point -/

/-- **The fibre over a field-valued point is geometrically connected when the geometric fibres
are connected.** If at every point of `Y` the geometric fibre of `f : X ⟶ Y` has exactly one
connected component (Stacks 0E1B), then for every field-valued point `Spec k ⟶ Y` the fibre
`X_k` is geometrically connected over `k` (Stacks 0A0Z). Over an algebraic closure `K` of `k`
the base change of `X_k` is the fibre over the geometric point `Spec K ⟶ Spec k ⟶ Y`, which is
connected; this is geometric connectedness of `X_K` over the separably closed `K` (Stacks 0A12),
hence of `X_k` over `k` (Stacks 0A10). -/
theorem isGeometricallyConnected_fibreOverFieldValuedPoint (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (h : ∀ y, numberGeometricConnectedComponents B S hS f y = 1)
    (p : FieldValuedPoint B S hS Y) :
    IsGeometricallyConnected B p.carrier p.contained (fibreOverFieldValuedPoint B S hS f p) := by
  let K := AlgebraicClosure p.carrier
  have hK : B.Contains (Spec (.of K)) := B.contains_spec_algebraicClosure p.carrier p.contained
  let g : B.obj hK ⟶ B.obj p.contained := fieldExtensionMap B p.carrier K p.contained hK
  let q : FieldValuedPoint B S hS Y :=
    { carrier := K
      contained := hK
      toBase := (g ≫ (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS)).hom
      value := Y.map (Over.homMk g rfl : Over.mk (g ≫ (⟨p.toBase⟩ : B.obj p.contained ⟶
        B.obj hS)) ⟶ p.siteObject).op p.value }
  have hXp : IsAlgebraicSpace B (Spec (.of p.carrier)) p.contained
      (fiberOverField B S hS f p) := fiberOverField_isAlgebraicSpace B S hS hX hY f p
  change IsGeometricallyConnected B p.carrier p.contained (fiberOverField B S hS f p)
  rw [isGeometricallyConnected_iff_relocalizeRestrict B p.carrier K p.contained hK _ hXp,
    isGeometricallyConnected_iff_connectedSpace_of_isSepClosed B K hK _
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of p.carrier)) hK
        p.contained g _ hXp)]
  let e := fiberOverFieldBaseChangeIso B S hS f p q g rfl rfl
  have h1 := numberGeometricConnectedComponents_eq B S hS hX hY f
    (⟨q, inferInstanceAs (IsAlgClosed K)⟩ : GeometricPoint B S hS Y)
  rw [h, geometricFiberComponentCount_eq_overField B S hS hX hY f q] at h1
  have hc : @ConnectedSpace (points B (Spec (.of K)) hK (fiberOverField B S hS f q))
      (pointTopology B (Spec (.of K)) hK _) :=
    (@connectedSpace_iff_cardinalMk_connectedComponents_eq_one _
      (pointTopology B (Spec (.of K)) hK _)).mpr (Cardinal.toENat_eq_one.mp h1.symm)
  exact connectedSpace_points_of_iso B (Spec (.of K)) hK e.symm hc

/-- The structural morphism of the fibre over a field-valued point, viewed again over `S`, is the
second projection of the fibre product: the comparison
`AlgebraicGeometry.Space.extendFiberOverFieldIso` lies over the point. -/
theorem extendFiberOverFieldIso_hom_snd (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    (extendFiberOverFieldIso B S hS f p).hom ≫ pullback.snd f (yonedaEquiv.symm p.value) =
      OverShriek.relocalizeToYoneda p.siteObject.hom (fiberOverField B S hS f p) := by
  unfold extendFiberOverFieldIso
  refine (IsPullback.isoPullback_hom_snd _).trans ?_
  ext V x
  exact Over.OverMorphism.ext ((Category.comp_id _).symm.trans (Over.w (
    (pullback.snd ((OverShriek.relocalizeRestrict p.siteObject.hom).map f) _).app _ x.1.2)))

/-- **The fibre of a proper morphism over a field-valued point is proper over the field.** Its
lower-shriek extension to `S` is the base change of `f` along `Spec k ⟶ Y`, and properness of
the structural morphism of a lower-shriek extension does not depend on the base. -/
theorem isProper_toYonedaId_fibreOverFieldValuedPoint (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (hf : IsProper B S hS f)
    (p : FieldValuedPoint B S hS Y) :
    IsProper B (Spec (.of p.carrier)) p.contained
      (toYonedaId B (Spec (.of p.carrier)) p.contained (fibreOverFieldValuedPoint B S hS f p)) := by
  have hXp : IsAlgebraicSpace B (Spec (.of p.carrier)) p.contained
      (fiberOverField B S hS f p) := fiberOverField_isAlgebraicSpace B S hS hX hY f p
  change IsProper B (Spec (.of p.carrier)) p.contained
    (toYonedaId B (Spec (.of p.carrier)) p.contained (fiberOverField B S hS f p))
  rw [← isProper_relocalizeToYoneda_iff B (Spec (.of p.carrier)) S p.contained hS
      p.siteObject.hom _ hXp, ← extendFiberOverFieldIso_hom_snd,
    isProper_isIso_comp_iff, ← pullbackSymmetry_hom_comp_fst, isProper_isIso_comp_iff]
  exact isProper_pullback_fst B S hS hX hY (isAlgebraicSpace_yoneda B S hS _) f _ hf

/-- **The fibre over a point with geometrically reduced fibre is geometrically reduced.** If the
fibre of `f` at the point of `|Y|` represented by a field-valued point `p` is geometrically
reduced (Stacks 0E08), then the fibre over `p` is a geometrically reduced algebraic space over
the field of `p` (Stacks 0DMQ). -/
theorem isGeometricallyReduced_fibreOverFieldValuedPoint (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (p : FieldValuedPoint B S hS Y)
    (h : IsGeometricallyReducedFibreAt B S hS f hX hY (p.class B S hS Y)) :
    IsGeometricallyReduced p.carrier B p.contained (fibreOverFieldValuedPoint B S hS f p)
      (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY p) :=
  (isGeometricallyReducedFibreAt_class_iff B S hS f hX hY p).mp h

end Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

section Inputs

-- Stacks 0DMY, part (7), for algebraic spaces: a proper algebraic space over a field `k` which is
-- geometrically reduced (Stacks 0DMQ) and geometrically connected (Stacks 0A0Z) has
-- `k = H⁰(X, 𝒪_X)`.
variable (hconst : ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))), Space.IsProper B (Spec (.of k)) hk f →
      Space.IsGeometricallyReduced k B hk X hX → Space.IsGeometricallyConnected B k hk X →
      Function.Bijective (algebraMap k (Space.globalFunctions B (Spec (.of k)) hk X)))

include hconst

/-- **`k = H⁰(X_k, 𝒪_{X_k})` on the fibres of a family in `Curves^{grc,1}`, from Stacks 0DMY (7).**
If the geometric fibres of a family of curves `f : X → S` are reduced and connected, then for
every field-valued point `Spec k → S` the fibre `X_k`, formed over `Spec k`, is proper,
geometrically reduced and geometrically connected over `k`, so its global functions are `k`. -/
theorem CurveFamily.bijective_algebraMap_fibre_of_isGrc1CurveFamily_of {X : CurveFamily B hZ}
    (hX : IsGrc1CurveFamily B hZ X)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    Function.Bijective (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier))
      p.contained (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom p))) :=
  hconst p.carrier p.contained _
    (Space.isAlgebraicSpace_fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom X.total.2
      (schemeSpace X.base).2 p) _
    (Space.isProper_toYonedaId_fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom X.total.2
      (schemeSpace X.base).2 X.proper p)
    (Space.isGeometricallyReduced_fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom
      X.total.2 (schemeSpace X.base).2 p (hX.1 _))
    (Space.isGeometricallyConnected_fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom
      X.total.2 (schemeSpace X.base).2 hX.2.1 p)

/-- **`k = H⁰(X_k, 𝒪_{X_k})` on the fibres of a family in `Curves^{grc,1}`, read on the fibre
product.** This is `CurveFamily.bijective_algebraMap_fibre_of_isGrc1CurveFamily_of` transported
along `AlgebraicGeometry.Space.bijective_algebraMap_fibreOverFieldValuedPoint_iff`: the fibre
formed over `Spec k` and the fibre product `X ×_S Spec k` have the same global functions. -/
theorem CurveFamily.hasBijectiveGlobalFunctionsOnFieldFibres_of_isGrc1CurveFamily_of
    {X : CurveFamily B hZ} (hX : IsGrc1CurveFamily B hZ X) :
    CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X := fun p =>
  (Space.bijective_algebraMap_fibreOverFieldValuedPoint_iff B integerBase hZ X.toBase.hom p
    X.total.2 (schemeSpace X.base).2).1
    (CurveFamily.bijective_algebraMap_fibre_of_isGrc1CurveFamily_of hconst hX p)

/-- **Stacks 0E6L, the inclusion `Curves^{grc,1} ⊂ Curves^{h0,1}`, from its inputs.** Given
Stacks 0DMY (7) for algebraic spaces (`hconst`) and the input `hpush` of Stacks 0E6I (that
`k = H⁰(X_k, 𝒪_{X_k})` on all fibres over fields gives `f_*𝒪_X = 𝒪_S` universally, Stacks 0E6B
(a)), every family of curves whose geometric fibres are reduced, connected and of dimension `1`
has `f_*𝒪_X = 𝒪_S`, this holding after arbitrary base change, and fibres of dimension `1`. -/
theorem isGrc1CurveFamily_le_isH01CurveFamily_of
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X) :
    IsGrc1CurveFamily B hZ ≤ IsH01CurveFamily B hZ := fun X hX =>
  ⟨hpush X (CurveFamily.hasBijectiveGlobalFunctionsOnFieldFibres_of_isGrc1CurveFamily_of hconst hX),
    hX.2.2⟩

/-- **Stacks 0E6L, the inclusion, from the statements of Stacks 0DMY (7) and 0E6B (a).** This is
`isGrc1CurveFamily_le_isH01CurveFamily_of` with `hpush` supplied by
`CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres`
from the statement `hstruct` of Stacks 0E6B (a) for algebraic spaces over `Spec(ℤ)`. -/
theorem isGrc1CurveFamily_le_isH01CurveFamily_of_structureSharp
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g))) :
    IsGrc1CurveFamily B hZ ≤ IsH01CurveFamily B hZ :=
  isGrc1CurveFamily_le_isH01CurveFamily_of hconst fun _ hX =>
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
      hstruct hX

/-- **Stacks 0E6L, final statement, from its inputs.** For a family of curves whose geometric
fibres are reduced, connected and of dimension `1`, `R¹f_*𝒪_X` is a finite locally free
`𝒪_S`-module whose formation commutes with arbitrary base change: the family lies in
`Curves^{h0,1}` (`isGrc1CurveFamily_le_isH01CurveFamily_of`), so `κ(s) = H⁰(X_s, 𝒪_{X_s})` for
every point `s` of the base, and parts (2) and (3) of Stacks 0E1J apply (`hR1`, `hR1bc`, their
statements). -/
theorem CurveFamily.firstHigherDirectImage_of_isGrc1CurveFamily_of
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X)
    (hR1 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (hR1bc : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange)
    {X : CurveFamily B hZ} (hX : IsGrc1CurveFamily B hZ X) :
    X.HasFiniteLocallyFreeFirstHigherDirectImage ∧
      X.FirstHigherDirectImageCommutesWithBaseChange :=
  have h := CurveFamily.hasResidueFieldGlobalFunctions_of_hasUniversallyBijectiveGlobalFunctions
    (isGrc1CurveFamily_le_isH01CurveFamily_of hconst hpush X hX).1
  ⟨hR1 X h, hR1bc X h⟩

end Inputs

end AlgebraicGeometry

end
