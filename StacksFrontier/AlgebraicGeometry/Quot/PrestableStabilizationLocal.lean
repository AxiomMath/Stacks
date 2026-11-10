module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocalContraction
public import StacksFrontier.AlgebraicGeometry.Quot.UniversalStructureContractionNearPoint
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationResidueFibre
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOverFieldOfContraction
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationTransitions
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackOfAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueFieldFactor
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenCharts
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenEtaleImage
public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesAmpleFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleDescent

/-!
# The stabilization exists étale locally on the base

Let `f : X ⟶ S` be a prestable family of curves of genus `g ≥ 2` and `s ∈ S`. This file builds the
local step of the proof of Stacks 0E8A: an étale morphism `W ⟶ S` whose image contains `s`, through
which every field-valued point of `S` lying over `s` lifts over the same field, a stable family of
curves `Y ⟶ W` and a morphism `c : X_W ⟶ Y` over `W` satisfying conditions (1) and (2) of
Stacks 0E8A.

The proof is the source's. Let `c₀ : X_s ⟶ Y₀` be the contraction of rational tails and bridges
of the fibre (Stacks 0E7Q). By Stacks 0E7C it extends to `h : X_U ⟶ Y'` over an elementary étale
neighbourhood `(U, u)` of `(S, s)`. By Stacks 0E88 condition (1) holds for `h` over an open
neighbourhood `Wn` of `u`. Since `ω_{Y₀}` is ample, the fibre of `Y'` at `u` is a stable family
over `Spec κ(s)`. Over `Wn` intersected with the open at-worst-nodal locus, `Y'` is prestable
(`f_*𝒪 = 𝒪` universally along the universal structure contraction). On an affine étale scheme
chart at `u` the fibre at the point of the chart is a fibre of that stable family, so by the
openness of stable fibres on scheme charts
(`AlgebraicGeometry.CurveFamily.exists_mem_forall_isStableCurveFamily_of_isPullback`, the
content of Stacks 0E74 and 0E76) the family is stable over an open of the chart, hence over its
image `W` in `U`. Over `W`, condition (2) follows from condition (1) and the stability of the
target.

Every family of curves has an étale scheme chart at every point of its base (Stacks 0E6F,
`AlgebraicGeometry.CurveFamily.hasEtaleSchemeChartAt`). This gives Stacks 0E88 for the contraction
(`AlgebraicGeometry.CurveFamily.hasUniversalStructureContractionNear_of_hasEtaleSchemeChartAt`)
and the chart on which stability is opened; stability passes from an open of the chart to its
image (`AlgebraicGeometry.CurveFamily.isStableCurveFamily_of_range_subset_image_of_etale`).

## Main results

* `AlgebraicGeometry.CurveFamily.exists_local_stabilization`: the local stabilization at `s`.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- A cartesian square over the structure morphism of a family is one over the structure
morphism transported along `rfl`. -/
theorem isPullback_toBase_comp_eqToHom_refl (Y : CurveFamily B hZ)
    {Y' T : AlgebraicSpaces B integerBase hZ} {p : Y' ⟶ Y.total} {f : Y' ⟶ T}
    {g : T ⟶ schemeSpace Y.base} (h : IsPullback p f Y.toBase g) :
    IsPullback p f (Y.toBase ≫ eqToHom (congrArg schemeSpace (rfl : Y.base = Y.base))) g := by
  simpa only [eqToHom_refl, Category.comp_id] using h

/-- The converse of `AlgebraicGeometry.CurveFamily.isPullback_toBase_comp_eqToHom_refl`. -/
theorem isPullback_toBase_of_comp_eqToHom_refl (Y : CurveFamily B hZ)
    {Y' T : AlgebraicSpaces B integerBase hZ} {p : Y' ⟶ Y.total} {f : Y' ⟶ T}
    {g : T ⟶ schemeSpace Y.base}
    (h : IsPullback p f (Y.toBase ≫ eqToHom (congrArg schemeSpace (rfl : Y.base = Y.base))) g) :
    IsPullback p f Y.toBase g := by
  simpa only [eqToHom_refl, Category.comp_id] using h

/-- A morphism `Spec K ⟶ X` sending the closed point to `z` factors through `Spec κ(z)`. -/
private theorem _root_.AlgebraicGeometry.Scheme.exists_comp_fromSpecResidueField_eq_of_closedPoint
    {X : Scheme.{u}} {K : Type u} [Field K] (t : Spec (.of K) ⟶ X) {z : X}
    (hz : t.base (IsLocalRing.closedPoint K) = z) :
    ∃ d : Spec (.of K) ⟶ Spec (.of (X.residueField z)), d ≫ X.fromSpecResidueField z = t := by
  subst hz
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ _ _⟩

/-- **Lifting a field-valued point along a factorization.** If the value `p.value : Spec K ⟶ S`
of a field-valued point of `S` factors as `w ≫ φ` through `φ : W ⟶ S`, then `p` is the image of a
field-valued point of `W` over the same field. -/
theorem exists_map_eq_of_comp_eq {W S : BigFppfOver B integerBase hZ} (φ : W ⟶ S)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace S).obj) (w : p.siteObject ⟶ W)
    (hw : w ≫ φ = p.value) :
    ∃ p' : Space.FieldValuedPoint B integerBase hZ (schemeSpace W).obj,
      Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ).hom p' = p := by
  obtain ⟨K, hK, tb, val⟩ := p
  refine ⟨⟨K, hK, tb, w⟩, ?_⟩
  simp only [Space.FieldValuedPoint.map, Space.FieldValuedPoint.mk.injEq, heq_eq_eq, true_and]
  exact hw

/-- A morphism of the site is determined by its image in schemes. -/
private theorem hom_ext_of_map_eq {A A' : BigFppfOver B integerBase hZ} {f g : A ⟶ A'}
    (h : (𝒯).map f = (𝒯).map g) : f = g :=
  (BigFppfOver.fullyFaithfulToScheme B integerBase hZ specULiftZIsTerminal).map_injective h

/-- If a cartesian square factors through a second one, the induced map is cartesian over the
factor. -/
private theorem exists_isPullback_lift_of_isPullback_comp {C : Type*} [Category C]
    {P A Z R T V : C} {fst : P ⟶ A} {snd : P ⟶ Z} {f : A ⟶ R} {g : Z ⟶ R}
    (sq : IsPullback fst snd f g) {pX : V ⟶ A} {fX : V ⟶ T} {b : T ⟶ Z}
    (outer : IsPullback pX fX f (b ≫ g)) :
    ∃ l : V ⟶ P, l ≫ fst = pX ∧ l ≫ snd = fX ≫ b ∧ IsPullback l fX snd b := by
  have hw : pX ≫ f = (fX ≫ b) ≫ g := outer.w.trans (Category.assoc _ _ _).symm
  have h₁ := sq.lift_fst pX (fX ≫ b) hw
  have h₂ := sq.lift_snd pX (fX ≫ b) hw
  refine ⟨_, h₁, h₂, IsPullback.of_right ?_ h₂ sq⟩
  rwa [h₁]

/-- **A universal structure contraction over an open restricts to a stabilization datum.** Let
`h : X_U ⟶ Y'` be a morphism over `U` from the base change `X_U` of `X` along `e : U ⟶ S` to a
family of curves `Y'` over `U`, satisfying condition (1) of Stacks 0E8A over an open `Wn ⊆ U`.
For every `j : W ⟶ U` landing in `Wn` the induced morphism `X ×_S W ⟶ Y' ×_U W` satisfies
condition (1) over `W`. -/
theorem exists_contraction_baseChangeAlong_of_le {X Y' : CurveFamily B hZ}
    (e : Y'.base ⟶ X.base) {T : AlgebraicSpaces B integerBase hZ} {pXU' : T ⟶ X.total}
    {fXU' : T ⟶ schemeSpace Y'.base}
    (sqXU' : IsPullback pXU' fXU' X.toBase (schemeSpaceMap e)) (h' : T ⟶ Y'.total)
    (hh' : h' ≫ Y'.toBase = fXU') {Wn : Y'.base.left.1.Opens}
    (hover : IsUniversalStructureContractionOver (X.ofIsPullback B hZ e pXU' fXU' sqXU') Y' rfl
      h' Wn)
    {W₁ : BigFppfOver B integerBase hZ} (j : W₁ ⟶ Y'.base)
    (hjW : ∀ y, ((𝒯).map j).base y ∈ Wn) :
    ∃ ci : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (j ≫ e)) ⟶
        (Y'.baseChangeAlong j).total,
      ci ≫ (Y'.baseChangeAlong j).toBase ≫
          eqToHom (congrArg schemeSpace (rfl : (Y'.baseChangeAlong j).base = W₁)) =
        ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (j ≫ e)).hom) ∧
      (X.baseChangeAlong (j ≫ e)).IsUniversalStructureContraction B hZ (Y'.baseChangeAlong j)
        rfl ci := by
  let XUf := X.ofIsPullback B hZ e _ _ sqXU'
  let Yi := Y'.baseChangeAlong j
  have sqYj := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ Y'.toBase (schemeSpaceMap j)
  let fstX : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (j ≫ e)) ⟶
      X.total := ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap (j ≫ e)).hom)
  let sndX : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (j ≫ e)) ⟶
      schemeSpace W₁ :=
    ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (j ≫ e)).hom)
  let fstY : AlgebraicSpaces.fiberProduct B integerBase hZ Y'.toBase (schemeSpaceMap j) ⟶
      Y'.total := ObjectProperty.homMk (pullback.fst Y'.toBase.hom (schemeSpaceMap j).hom)
  obtain ⟨m, hm₁, hm₂, hmj⟩ := exists_isPullback_lift_of_isPullback_comp sqXU'
    (fX := sndX) (pX := fstX) (b := schemeSpaceMap j) (by
      rw [← schemeSpaceMap_comp]
      exact AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
        (schemeSpaceMap (j ≫ e)))
  let ci : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (j ≫ e)) ⟶
      Yi.total := sqYj.lift (m ≫ h') sndX
        ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) hh').trans hm₂))
  have hci₁ : ci ≫ fstY = m ≫ h' := sqYj.lift_fst _ _ _
  have hci : ci ≫ Yi.toBase ≫ eqToHom (congrArg schemeSpace (rfl : Yi.base = W₁)) =
      ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (j ≫ e)).hom) :=
    (Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans (sqYj.lift_snd _ _ _))
  have h1 : (X.baseChangeAlong (j ≫ e)).IsUniversalStructureContraction B hZ Yi rfl ci := by
    intro T t X'' Y'' pX fX pY fY c' s₁ s₂ e₁ e₂
    have S₁ : IsPullback (pX ≫ m) fX XUf.toBase (schemeSpaceMap (t ≫ j)) :=
      (congrArg (IsPullback (pX ≫ m) fX XUf.toBase) (schemeSpaceMap_comp t j)).mpr
        (s₁.paste_horiz hmj)
    have S₂ : IsPullback (pY ≫ fstY) fY Y'.toBase (schemeSpaceMap (t ≫ j)) :=
      (congrArg (IsPullback (pY ≫ fstY) fY Y'.toBase) (schemeSpaceMap_comp t j)).mpr
        ((Yi.isPullback_toBase_of_comp_eqToHom_refl s₂).paste_horiz sqYj)
    refine hover T (t ≫ j) (fun x => ?_) X'' Y'' _ fX _ fY c' S₁
      (Y'.isPullback_toBase_comp_eqToHom_refl S₂) ?_ e₂
    · exact hjW _
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ fstY) e₁).trans
        ((Category.assoc _ _ _).trans ((congrArg (pX ≫ ·) hci₁).trans
          (Category.assoc _ _ _).symm)))
  exact ⟨ci, hci, h1⟩

/-- **Field-valued points over `s` lift to an open of an étale neighbourhood.** Let
`ū : Spec κ(s) ⟶ U` lift the residue field of `s` along `e : U ⟶ S` and land in an open `O` of
`U`. Every field-valued point of `S` meeting `s` is the image of a field-valued point of `O`. -/
private theorem exists_map_eq_of_mem_range_residueField {S U : BigFppfOver B integerBase hZ}
    {s : S.left.1} (e : U ⟶ S) (ū : (residueFieldValuedPoint B hZ S s).siteObject ⟶ U)
    (hū : ū ≫ e = (residueFieldValuedPoint B hZ S s).value) (O : U.left.1.Opens)
    (hO : B.Contains O.toScheme) (hūO : ∀ y, ū.left.1 y ∈ O)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace S).obj)
    (hp : s ∈ Set.range ((𝒯).map (p.value : p.siteObject ⟶ S))) :
    ∃ p' : Space.FieldValuedPoint B integerBase hZ (schemeSpace (ofScheme O.toScheme hO)).obj,
      Space.FieldValuedPoint.map B integerBase hZ _
        (schemeSpaceMap ((homOfScheme O.ι : ofScheme O.toScheme hO ⟶ U) ≫ e)).hom p' = p := by
  let p₀ := residueFieldValuedPoint B hZ S s
  obtain ⟨w₀, hw₀⟩ : ∃ w : p₀.siteObject ⟶ S, w = p₀.value := ⟨_, rfl⟩
  have hūw : ū ≫ e = w₀ := hū.trans hw₀.symm
  have hw₀𝒯 : (𝒯).map w₀ = S.left.1.fromSpecResidueField s := by
    rw [hw₀]
    rfl
  let W₁ : BigFppfOver B integerBase hZ := ofScheme O.toScheme hO
  let j : W₁ ⟶ U := homOfScheme O.ι
  obtain ⟨wp, hwp⟩ : ∃ w : p.siteObject ⟶ S, w = p.value := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := hp
  let t : Spec (.of p.carrier) ⟶ S.left.1 := (𝒯).map wp
  have hsubK : Subsingleton (Spec (.of p.carrier)) := inferInstance
  have hyt : t.base (IsLocalRing.closedPoint p.carrier) = s := by
    have e1 : t.base (IsLocalRing.closedPoint p.carrier) = ((𝒯).map p.value).base y := by
      rw [← hwp]
      exact congrArg t.base (@Subsingleton.elim _ hsubK _ _)
    exact e1.trans hy
  obtain ⟨r, hr⟩ := Scheme.exists_comp_fromSpecResidueField_eq_of_closedPoint t hyt
  let rS : p.siteObject ⟶ p₀.siteObject := homOfScheme r
  have hrS : rS ≫ w₀ = wp := by
    apply hom_ext_of_map_eq
    rw [Functor.map_comp, hw₀𝒯]
    exact hr
  let r' : (𝒯).obj p.siteObject ⟶ U.left.1 := (𝒯).map (rS ≫ ū)
  have hsub : Set.range r'.base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hūO _
  let lft := IsOpenImmersion.lift O.ι r' hsub
  have hlft : lft ≫ O.ι = r' := IsOpenImmersion.lift_fac _ _ _
  have hval : (homOfScheme lft : p.siteObject ⟶ W₁) ≫ j ≫ e = wp := by
    apply hom_ext_of_map_eq
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc]
    change (lft ≫ O.ι) ≫ _ = _
    rw [hlft, ← Functor.map_comp, Category.assoc, hūw, hrS]
  exact exists_map_eq_of_comp_eq (j ≫ e) p (homOfScheme lft) (hval.trans hwp)

/-- **Factoring through a residually trivial point.** Let `ū : Spec κ(s) ⟶ U` induce an
isomorphism on residue fields at the closed point. Every morphism `Spec κ(v) ⟶ U` sending the
closed point to the image of the closed point under `ū` factors through `ū`. -/
private theorem exists_comp_eq_of_isIso_residueFieldMap {S U V : BigFppfOver B integerBase hZ}
    {s : S.left.1} (ū : (residueFieldValuedPoint B hZ S s).siteObject ⟶ U)
    (hres : IsIso (ū.left.1.residueFieldMap (IsLocalRing.closedPoint (S.left.1.residueField s))))
    {v : V.left.1} (k : (residueFieldValuedPoint B hZ V v).siteObject ⟶ U)
    (hk : ((𝒯).map k).base (IsLocalRing.closedPoint (V.left.1.residueField v)) =
      ū.left.1 (IsLocalRing.closedPoint (S.left.1.residueField s))) :
    ∃ r : (residueFieldValuedPoint B hZ V v).siteObject ⟶
      (residueFieldValuedPoint B hZ S s).siteObject, r ≫ ū = k := by
  let p₀ := residueFieldValuedPoint B hZ S s
  let pt : p₀.siteObject.left.1 := IsLocalRing.closedPoint (S.left.1.residueField s)
  let t : Spec (.of (V.left.1.residueField v)) ⟶ U.left.1 := (𝒯).map k
  obtain ⟨d, hd⟩ := Scheme.exists_comp_fromSpecResidueField_eq_of_closedPoint t hk
  have := hres
  let ι₀ := Space.residueFieldObjectMap B integerBase hZ p₀.siteObject U ū pt
  have : IsIso ι₀ := Space.isIso_residueFieldObjectMap B integerBase hZ p₀.siteObject U ū pt
  let rP := Space.residueFieldMap B integerBase hZ p₀.siteObject pt
    (B.residueField_spec_contains p₀.siteObject.left.property pt)
  have hcompι := Space.residueFieldObjectMap_comp B integerBase hZ p₀.siteObject U ū pt
  have e₁ : (inv ι₀ ≫ rP) ≫ ū = Space.residueFieldMap B integerBase hZ U (ū.left.1 pt)
      (B.residueField_spec_contains U.left.property (ū.left.1 pt)) := by
    rw [Category.assoc, ← hcompι, IsIso.inv_hom_id_assoc]
  refine ⟨homOfScheme (d ≫ (𝒯).map (inv ι₀ ≫ rP)), ?_⟩
  apply hom_ext_of_map_eq
  refine (Functor.map_comp _ _ _).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (d ≫ ·) ((Functor.map_comp _ _ _).symm.trans
    (congrArg (𝒯).map e₁))).trans hd)

/-- **Affine étale scheme charts.** Every family of curves has, at every point of its base, an
étale scheme chart whose source is affine. -/
private theorem exists_isAffine_etale_schemeChart (Y : CurveFamily B hZ) (y : Y.base.left.1) :
    ∃ (Uc Zc : BigFppfOver B integerBase hZ) (φ : Uc ⟶ Y.base) (pc : schemeSpace Zc ⟶ Y.total)
      (qc : Zc ⟶ Uc), IsAffine ((𝒯).obj Uc) ∧ Etale ((𝒯).map φ) ∧
      IsPullback pc (schemeSpaceMap qc) Y.toBase (schemeSpaceMap φ) ∧
      ∃ uc : (𝒯).obj Uc, ((𝒯).map φ).base uc = y := by
  obtain ⟨Uc, φc, uc, hφc, huc, Z, pZ, qZ, sqZ⟩ := hasEtaleSchemeChartAt Y y
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hucV, -⟩ :=
    ((𝒯).obj Uc).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ uc) isOpen_univ
  let V : ((𝒯).obj Uc).Opens := V₀
  let Uc' : BigFppfOver B integerBase hZ :=
    ofScheme V.toScheme (Scheme.size_lt_of_isOpenImmersion V.ι Uc.left.property)
  let gV : Uc' ⟶ Uc := homOfScheme V.ι
  let φ' : Uc' ⟶ Y.base := homOfScheme (V.ι ≫ (𝒯).map φc)
  have hφ'eq : gV ≫ φc = φ' :=
    hom_ext_of_map_eq (by rw [Functor.map_comp]; rfl)
  refine ⟨Uc', _, φ', schemeSpaceMap (pullback.fst qZ gV) ≫ pZ, pullback.snd qZ gV,
    (hV : IsAffineOpen V), ?_, ?_, ⟨uc, hucV⟩, huc⟩
  · have := hφc
    have : Etale V.ι := inferInstance
    exact Etale.etale_comp ((𝒯).map φc) (f := V.ι)
  · exact (congrArg (IsPullback (schemeSpaceMap (pullback.fst qZ gV) ≫ pZ)
      (schemeSpaceMap (pullback.snd qZ gV)) Y.toBase)
      ((schemeSpaceMap_comp gV φc).symm.trans (congrArg schemeSpaceMap hφ'eq)).symm).mpr
      ((isPullback_schemeSpaceMap_fst_snd qZ gV).paste_horiz sqZ)

/-- **The fibre of a chart over a point of a stable fibre is stable.** Let the fibre of `Y'` over
`ū : Spec κ(s) ⟶ U` be stable, with `ū` residually trivial at the closed point, and let
`Zc ⟶ Uc` be an étale scheme chart of the base change of `Y'` to `W₂`, with a point `uc` lying
over the image of the closed point under `ū`. The fibre of the chart at `uc` has bijective
global functions and no rational tails or bridges. -/
private theorem exists_isPullback_bijective_appTop_of_isStableCurveFamily_fibre
    {S : BigFppfOver B integerBase hZ} {s : S.left.1} {Y' : CurveFamily B hZ}
    (ū : (residueFieldValuedPoint B hZ S s).siteObject ⟶ Y'.base)
    (hres : IsIso (ū.left.1.residueFieldMap (IsLocalRing.closedPoint (S.left.1.residueField s))))
    {G : BigFppfOver B integerBase hZ} {tG : G ⟶ (residueFieldValuedPoint B hZ S s).siteObject}
    {jG : schemeSpace G ⟶ Y'.total}
    (sqG₀ : IsPullback jG (schemeSpaceMap tG) Y'.toBase (schemeSpaceMap ū))
    (hstF : IsStableCurveFamily B hZ (Y'.ofIsPullback B hZ ū jG (schemeSpaceMap tG) sqG₀))
    {W₂ : BigFppfOver B integerBase hZ} (j₂ : W₂ ⟶ Y'.base)
    (hY₂ : IsPrestableCurveFamily B hZ (Y'.baseChangeAlong j₂))
    {Zc Uc : BigFppfOver B integerBase hZ} {pc : schemeSpace Zc ⟶ (Y'.baseChangeAlong j₂).total}
    {qc : Zc ⟶ Uc} {φ' : Uc ⟶ W₂}
    (sq' : IsPullback pc (schemeSpaceMap qc) (Y'.baseChangeAlong j₂).toBase (schemeSpaceMap φ'))
    (uc : Uc.left.1)
    (huc : ((𝒯).map j₂).base (((𝒯).map φ').base uc) =
      ū.left.1 (IsLocalRing.closedPoint (S.left.1.residueField s))) :
    ∃ (C₀ : Scheme.{u}) (h₀ : C₀ ⟶ (𝒯).obj Zc)
      (g₀ : C₀ ⟶ Spec (.of (((𝒯).obj Uc).residueField uc))),
      IsPullback h₀ g₀ ((𝒯).map qc) (((𝒯).obj Uc).fromSpecResidueField uc) ∧
        Function.Bijective g₀.appTop ∧
        HasGenusTwoNoRationalTailNoRationalBridge (((𝒯).obj Uc).residueField uc) g₀ := by
  have sqY₂ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ Y'.toBase
    (schemeSpaceMap j₂)
  -- the fibre of the chart at `uc` is stable: it is a fibre of the stable family `F_Y`
  let pRes := residueFieldValuedPoint B hZ Uc uc
  let c : pRes.siteObject ⟶ Uc := Space.residueFieldMap B integerBase hZ Uc uc
    (B.residueField_spec_contains Uc.left.property uc)
  let pG := Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ').hom pRes
  have hpres := isPullback_presentation_of_factors sq' pG c rfl
  obtain ⟨-, hH0c, -, -⟩ := fibre_standing_of_isPrestableCurveFamily hY₂ hpres
  -- the point `Spec κ(uc) ⟶ Spec κ(s)` over `U`
  have ht : ((𝒯).map (c ≫ φ' ≫ j₂)).base (IsLocalRing.closedPoint (Uc.left.1.residueField uc)) =
      ū.left.1 (IsLocalRing.closedPoint (S.left.1.residueField s)) := by
    have h₁ : ((𝒯).map c).base (IsLocalRing.closedPoint (Uc.left.1.residueField uc)) = uc :=
      Scheme.fromSpecResidueField_apply _ _
    have h₂ : ((𝒯).map (c ≫ φ' ≫ j₂)).base
        (IsLocalRing.closedPoint (Uc.left.1.residueField uc)) =
        ((𝒯).map j₂).base (((𝒯).map φ').base
          (((𝒯).map c).base (IsLocalRing.closedPoint (Uc.left.1.residueField uc)))) := by
      simp only [Functor.map_comp]
      rfl
    rw [h₂, h₁]
    exact huc
  obtain ⟨r, hr⟩ := exists_comp_eq_of_isIso_residueFieldMap (V := Uc) (v := uc) ū hres
    (c ≫ φ' ≫ j₂) ht
  -- the field-valued point of `Spec κ(s)` given by `r`
  let P : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (residueFieldValuedPoint B hZ S s).siteObject).obj :=
    { carrier := pRes.carrier
      contained := pRes.contained
      toBase := pRes.toBase
      value := r }
  obtain ⟨V₁, v₁, q₁, hq₁, hgen₁⟩ := hstF.2 P
  -- the chart's fibre presents the fibre of `F_Y` at `P`
  have big := ((isPullback_schemeSpaceMap_fst_snd qc c).paste_horiz sq').paste_horiz sqY₂
  let fstY₂ : AlgebraicSpaces.fiberProduct B integerBase hZ Y'.toBase (schemeSpaceMap j₂) ⟶
      Y'.total := ObjectProperty.homMk (pullback.fst Y'.toBase.hom (schemeSpaceMap j₂).hom)
  let fb := (schemeSpaceMap (pullback.fst qc c) ≫ pc) ≫ fstY₂
  have hrc : schemeSpaceMap r ≫ schemeSpaceMap ū =
      (schemeSpaceMap c ≫ schemeSpaceMap φ') ≫ schemeSpaceMap j₂ := by
    rw [← schemeSpaceMap_comp, hr, schemeSpaceMap_comp, schemeSpaceMap_comp, Category.assoc]
  obtain ⟨ℓ, -, -, hℓ⟩ := exists_isPullback_lift_of_isPullback_comp sqG₀ (pX := fb)
    (fX := schemeSpaceMap (pullback.snd qc c)) (b := schemeSpaceMap r) (by rw [hrc]; exact big)
  have hq₂ := AlgebraicSpaces.isPullback_hom B integerBase hZ hℓ
  have hPr : yonedaEquiv.symm P.value = yoneda.map r :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map r).symm
  have hgenc : HasGenusTwoNoRationalTailNoRationalBridge P.carrier
      ((𝒯).map (pullback.snd qc c)) :=
    hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of_isPullback_self hstF.1 hq₁
      (q' := ℓ.hom) ((congrArg (IsPullback ℓ.hom (yoneda.map (pullback.snd qc c))
        (schemeSpaceMap tG).hom) hPr).mpr hq₂) hgen₁
  have hglobc : Function.Bijective ((𝒯).map (pullback.snd qc c)).appTop := by
    have : IsIso ((Scheme.ΓSpecIso (.of pG.carrier)).inv ≫
        ((𝒯).map (pullback.snd qc c)).appTop) := hH0c
    have : IsIso ((𝒯).map (pullback.snd qc c)).appTop :=
      IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of pG.carrier)).inv _
    exact ConcreteCategory.bijective_of_isIso _
  exact ⟨_, _, _, (IsPullback.of_hasPullback qc c).map (𝒯), hglobc, hgenc⟩

/-- **Stability over the image of an open immersion.** Let `j₂ : W₂ ⟶ U` be an open immersion
and `Ω` an open of `W₂` over which the base change of `Y'` along `j₂` is stable. Every family of
curves mapping to `Y'` over the image of `Ω` is stable. -/
private theorem isStableCurveFamily_of_forall_mem_image_of_isOpenImmersion {Y' : CurveFamily B hZ}
    {W₂ : BigFppfOver B integerBase hZ} (j₂ : W₂ ⟶ Y'.base) (hj₂ : IsOpenImmersion ((𝒯).map j₂))
    (Ω : ((𝒯).obj (Y'.baseChangeAlong j₂).base).Opens)
    (hΩ : ∀ (F : CurveFamily B hZ) (a : F ⟶ Y'.baseChangeAlong j₂),
      Set.range ((𝒯).map a.baseMap) ⊆ Ω → IsStableCurveFamily B hZ F)
    {F : CurveFamily B hZ} (a : F ⟶ Y')
    (ha : ∀ x, ((𝒯).map a.baseMap).base x ∈
      ((𝒯).map j₂).base '' (Ω : Set ((𝒯).obj (Y'.baseChangeAlong j₂).base))) :
    IsStableCurveFamily B hZ F := by
  have sqY₂ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ Y'.toBase
    (schemeSpaceMap j₂)
  -- a family over the image of `Ω` factors through `Y'.baseChangeAlong j₂`
  have hsubF : Set.range ((𝒯).map a.baseMap).base ⊆ Set.range ((𝒯).map j₂).base := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, -, hy⟩ := ha x
    exact ⟨y, hy⟩
  let lftF := IsOpenImmersion.lift ((𝒯).map j₂) ((𝒯).map a.baseMap) hsubF
  have hlftF : lftF ≫ (𝒯).map j₂ = (𝒯).map a.baseMap := IsOpenImmersion.lift_fac _ _ _
  let b₂ : F.base ⟶ W₂ := homOfScheme lftF
  have hb₂ : b₂ ≫ j₂ = a.baseMap :=
    hom_ext_of_map_eq ((Functor.map_comp _ _ _).trans hlftF)
  have hb₂s : schemeSpaceMap b₂ ≫ schemeSpaceMap j₂ = schemeSpaceMap a.baseMap :=
    (schemeSpaceMap_comp b₂ j₂).symm.trans (congrArg schemeSpaceMap hb₂)
  obtain ⟨tF, -, -, htF⟩ := exists_isPullback_lift_of_isPullback_comp sqY₂
    (b := schemeSpaceMap b₂) (by rw [hb₂s]; exact a.cartesian)
  refine hΩ F (⟨b₂, tF, htF⟩ : F ⟶ Y'.baseChangeAlong j₂) ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hyO, hy⟩ := ha x
  obtain rfl : y = lftF.base x := ((𝒯).map j₂).isOpenEmbedding.injective (by
    rw [hy, ← hlftF]
    rfl)
  exact hyO

/-- **Stability spreads from a fibre to a neighbourhood.** Let `h : X_U ⟶ Y'` satisfy condition
(1) of Stacks 0E8A over an open `Wn ⊆ U` containing `u`, and let the fibre of `Y'` over
`ū : Spec κ(s) ⟶ U`, which sends the closed point to `u` and is residually trivial there, be
stable. There is an open `O ∋ u` inside `Wn` over which every family of curves mapping to `Y'` is
stable. -/
private theorem exists_mem_forall_isStableCurveFamily_of_fibre {X Y' : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) (e : Y'.base ⟶ X.base)
    {T : AlgebraicSpaces B integerBase hZ} {pXU' : T ⟶ X.total} {fXU' : T ⟶ schemeSpace Y'.base}
    (sqXU' : IsPullback pXU' fXU' X.toBase (schemeSpaceMap e)) (h' : T ⟶ Y'.total)
    (hh' : h' ≫ Y'.toBase = fXU') {Wn : Y'.base.left.1.Opens}
    (hover : IsUniversalStructureContractionOver (X.ofIsPullback B hZ e pXU' fXU' sqXU') Y' rfl
      h' Wn)
    {s : X.base.left.1} (ū : (residueFieldValuedPoint B hZ X.base s).siteObject ⟶ Y'.base)
    {u : Y'.base.left.1}
    (hu : ū.left.1 (IsLocalRing.closedPoint (X.base.left.1.residueField s)) = u) (huWn : u ∈ Wn)
    (hres : IsIso (ū.left.1.residueFieldMap
      (IsLocalRing.closedPoint (X.base.left.1.residueField s))))
    {G : BigFppfOver B integerBase hZ}
    {tG : G ⟶ (residueFieldValuedPoint B hZ X.base s).siteObject} {jG : schemeSpace G ⟶ Y'.total}
    (sqG₀ : IsPullback jG (schemeSpaceMap tG) Y'.toBase (schemeSpaceMap ū))
    (hstF : IsStableCurveFamily B hZ (Y'.ofIsPullback B hZ ū jG (schemeSpaceMap tG) sqG₀)) :
    ∃ O : Y'.base.left.1.Opens, u ∈ O ∧ O ≤ Wn ∧ ∀ (F : CurveFamily B hZ) (a : F ⟶ Y'),
      (∀ x, ((𝒯).map a.baseMap).base x ∈ O) → IsStableCurveFamily B hZ F := by
  let pt : (residueFieldValuedPoint B hZ X.base s).siteObject.left.1 :=
    IsLocalRing.closedPoint (X.base.left.1.residueField s)
  -- the at-worst-nodal locus of `Y'` contains `u`
  obtain ⟨ΩN, hΩN, hΩNP⟩ :=
    (isOpenCurvesLocus_isAtWorstNodal B hZ).exists_isOpen_range_subset Y'
  have huΩN : u ∈ ΩN := (hΩNP (Y'.homOfIsPullback B hZ ū jG _ sqG₀)).1 hstF.1.1 ⟨pt, hu⟩
  -- over `U₂ = Wn ∩ ΩN` the family `Y'` is prestable
  let U₂ : Y'.base.left.1.Opens := Wn ⊓ ⟨ΩN, hΩN⟩
  have hU₂ : B.Contains U₂.toScheme :=
    Scheme.size_lt_of_isOpenImmersion U₂.ι Y'.base.left.property
  let W₂ : BigFppfOver B integerBase hZ := ofScheme U₂.toScheme hU₂
  let j₂ : W₂ ⟶ Y'.base := homOfScheme U₂.ι
  have hj₂ : IsOpenImmersion ((𝒯).map j₂) := inferInstanceAs (IsOpenImmersion U₂.ι)
  have hj₂W : ∀ y, ((𝒯).map j₂).base y ∈ U₂ := fun y => y.2
  let Y₂ := Y'.baseChangeAlong j₂
  have sqY₂ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ Y'.toBase
    (schemeSpaceMap j₂)
  obtain ⟨c₂, hc₂, h1₂⟩ := exists_contraction_baseChangeAlong_of_le (Y' := Y') e sqXU' h' hh'
    hover j₂ fun y => (hj₂W y).1
  have sqX₂ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
    (schemeSpaceMap (j₂ ≫ e))
  have hX₂ : IsPrestableCurveFamily B hZ (X.baseChangeAlong (j₂ ≫ e)) :=
    isPrestableCurveFamily_of_hom (X.homOfIsPullback B hZ (j₂ ≫ e) _ _ sqX₂) hX
  have hY₂ : IsPrestableCurveFamily B hZ Y₂ :=
    ⟨(hΩNP (Y'.homOfIsPullback B hZ j₂ _ _ sqY₂)).2 (by
        rintro _ ⟨y, rfl⟩
        exact (hj₂W y).2),
      hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp_baseChange
        (X := X.baseChangeAlong (j₂ ≫ e)) rfl c₂ hc₂
        (fun T t X' Y'' pX' fX' pY' fY' c' a b e₁ e₂ =>
          (h1₂ T t X' Y'' pX' fX' pY' fY' c' a b e₁ e₂).1) hX₂.2⟩
  -- an affine étale scheme chart of `Y₂` at `u`
  let u₂ : U₂.toScheme := ⟨u, huWn, huΩN⟩
  obtain ⟨Uc, Zc, φ', pc, qc, hUc, hφ', sq', uc, huc⟩ := exists_isAffine_etale_schemeChart Y₂ u₂
  -- the chart lemma, with the descent of stability from an étale chart: `Y₂` is stable over
  -- the image of an open neighbourhood of `uc`
  obtain ⟨Ω, huΩ, hΩ⟩ := exists_mem_forall_isStableCurveFamily_of_isPullback_of_etale hY₂ sq' hφ'
    uc (exists_isPullback_bijective_appTop_of_isStableCurveFamily_fibre ū hres sqG₀ hstF j₂ hY₂
      sq' uc ((congrArg (fun z => ((𝒯).map j₂).base z) huc).trans hu.symm))
  -- the image `O` of `Ω` in `U`
  refine ⟨⟨((𝒯).map j₂).base '' (Ω : Set ((𝒯).obj Y₂.base)),
      ((𝒯).map j₂).isOpenEmbedding.isOpenMap _ Ω.2⟩,
    ⟨_, huΩ, congrArg (fun z => ((𝒯).map j₂).base z) huc⟩, ?_, fun F a ha =>
      isStableCurveFamily_of_forall_mem_image_of_isOpenImmersion j₂ hj₂ Ω hΩ a ha⟩
  rintro _ ⟨y, -, rfl⟩
  exact (hj₂W y).1

/-- **The stabilization exists étale locally on the base.** Let `X ⟶ S` be a prestable family of
curves of genus `g ≥ 2` and `s ∈ S`. There are an étale morphism
`φ : W ⟶ S` whose image contains `s`, through which every field-valued point of `S` lying over
`s` lifts over the same field, a stable family of curves `Y` over `W` and a morphism
`c : X ×_S W ⟶ Y` over `W` satisfying conditions (1) and (2) of Stacks 0E8A. -/
theorem exists_local_stabilization
    {X : CurveFamily B hZ} (hX : IsPrestableCurveFamily B hZ X) {g : ℕ} (hg : 2 ≤ g)
    (hgen : X.HasFibresOfGenus g) (s : X.base.left.1) :
    ∃ (W : BigFppfOver B integerBase hZ) (φ : W ⟶ X.base), Etale ((𝒯).map φ) ∧
      s ∈ Set.range ((𝒯).map φ) ∧
      (∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
        s ∈ Set.range ((𝒯).map (p.value : p.siteObject ⟶ X.base)) →
        ∃ p' : Space.FieldValuedPoint B integerBase hZ (schemeSpace W).obj,
          Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ).hom p' = p) ∧
      ∃ (Y : CurveFamily B hZ) (hY : Y.base = W), IsStableCurveFamily B hZ Y ∧
        ∃ c : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap φ) ⟶
            Y.total,
          c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hY) =
            ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap φ).hom) ∧
          (X.baseChangeAlong φ).IsUniversalStructureContraction B hZ Y hY c ∧
          (X.baseChangeAlong φ).HasStableContractionFibres B hZ Y hY c := by
  classical
  -- the fibre at `s` and its stable contraction (Stacks 0E7Q)
  let p₀ := residueFieldValuedPoint B hZ X.base s
  obtain ⟨VX, vX, qX, hqX⟩ := exists_isPullback_fieldValuedPoint B hZ X p₀
  have hqX' := isPullback_yoneda_of_isPullback_schemeSpace X.toBase p₀ hqX
  obtain ⟨w₀, hw₀⟩ : ∃ w : p₀.siteObject ⟶ X.base, w = p₀.value := ⟨_, rfl⟩
  have hqX₀ : IsPullback qX (schemeSpaceMap vX) X.toBase (schemeSpaceMap w₀) := by
    rw [hw₀]
    exact hqX
  obtain ⟨hprop, hH0, hdim, hnodal⟩ := fibre_standing_of_isPrestableCurveFamily hX hqX'
  have := hprop
  have := hH0
  have hgenus : 2 ≤ genus ((𝒯).map vX) := ((hgen p₀).genus_eq vX qX.hom hqX').symm ▸ hg
  obtain ⟨Y₀, gY₀, c₀, hst₀⟩ := (Stacks.Curves.StableModel.existsUnique_isStableContraction
    ((𝒯).map vX) hdim hgenus hnodal).1
  have : IsProper gY₀ := hst₀.isProper
  -- its extension over an elementary étale neighbourhood (Stacks 0E7C)
  obtain ⟨U, e, ū, he, hū, -, Yp, XU, gp, pXU, fXU, h, hYalg, hXUalg, hfl, hpr, hfp, hrd, sqXU,
    hhg, iXU, G, tG, iG, φ, a, hiXU, hiXUp, hiG, hφ, hat, hcomp, ha⟩ :=
    X.exists_elementaryEtale_extension_of_fibre s vX qX hqX gY₀ c₀ hst₀.comp_eq
      hst₀.isIso_unitToPushforwardObjUnit hst₀.isZero_rightDerived_one
  -- the two families over `U` and the morphism `h` between them
  let Y' : CurveFamily B hZ :=
    { base := U, total := ⟨Yp, hYalg⟩, toBase := ObjectProperty.homMk gp, flat := hfl,
      proper := hpr, finitePresentation := hfp, relativeDimensionLE := hrd }
  let pXU' : (⟨XU, hXUalg⟩ : AlgebraicSpaces B integerBase hZ) ⟶ X.total :=
    ObjectProperty.homMk pXU
  let fXU' : (⟨XU, hXUalg⟩ : AlgebraicSpaces B integerBase hZ) ⟶ schemeSpace U :=
    ObjectProperty.homMk fXU
  have sqXU' : IsPullback pXU' fXU' X.toBase (schemeSpaceMap e) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sqXU
  let XUf := X.ofIsPullback B hZ e _ _ sqXU'
  let h' : XUf.total ⟶ Y'.total := ObjectProperty.homMk h
  have hh' : h' ≫ Y'.toBase = XUf.toBase := ObjectProperty.hom_ext _ hhg
  have hc' : h' ≫ Y'.toBase ≫ eqToHom (congrArg schemeSpace (rfl : Y'.base = XUf.base)) =
      XUf.toBase := (Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans hh')
  -- the fibre of `h` over `ū` is a stable contraction
  have hstA : Stacks.Curves.StableModel.IsStableContraction ((𝒯).map vX) ((𝒯).map tG)
      ((𝒯).map a) := by
    have := hst₀.of_iso φ ((𝒯).map a) ha
    rwa [hφ] at this
  have : IsProper ((𝒯).map tG) := hstA.isProper
  have : IsProper ((𝒯).map a) := by
    have : IsProper ((𝒯).map a ≫ (𝒯).map tG) := by
      rw [← Functor.map_comp, hat]
      exact hprop
    exact IsProper.of_comp ((𝒯).map a) ((𝒯).map tG)
  have hA : Space.IsStructureContraction B integerBase hZ (schemeSpaceMap a) :=
    (isStructureContraction_schemeSpaceMap_iff_unit a).2
      ⟨hstA.isIso_unitToPushforwardObjUnit, hstA.isZero_rightDerived_one⟩
  -- the point `u` of `U` and the fibre there
  let pt : p₀.siteObject.left.1 := IsLocalRing.closedPoint (X.base.left.1.residueField s)
  obtain ⟨u, hu⟩ : ∃ u : U.left.1, ū.left.1 pt = u := ⟨_, rfl⟩
  have hpt : IsIso (p₀.siteObject.left.1.fromSpecResidueField pt) :=
    isIso_fromSpecResidueField_of_field (X.base.left.1.residueField s) pt
  have h𝒯 : ū.left.1 ≫ e.left.1 = X.base.left.1.fromSpecResidueField s :=
    congrArg (fun m => m.left.1) hū
  have hres : IsIso (ū.left.1.residueFieldMap pt) := by
    refine isIso_residueFieldMap_left_of_isIso_residueFieldMap_comp ū.left.1 e.left.1 pt ?_
    rw [h𝒯]
    exact isIso_residueFieldMap_fromSpecResidueField _ s pt
  let jX : schemeSpace VX ⟶ XUf.total := ObjectProperty.homMk iXU
  let jG : schemeSpace G ⟶ Y'.total := ObjectProperty.homMk iG
  have sqV : IsPullback jX (schemeSpaceMap vX) XUf.toBase (schemeSpaceMap ū) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hiXU
  have sqG₀ : IsPullback jG (schemeSpaceMap tG) Y'.toBase (schemeSpaceMap ū) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hiG
  have sqG := Y'.isPullback_toBase_comp_eqToHom_refl sqG₀
  have haG : schemeSpaceMap a ≫ jG = jX ≫ h' := ObjectProperty.hom_ext _ hcomp.symm
  have hs : Space.IsStructureContraction B integerBase hZ
      (Space.structureContractionBaseChange B integerBase hZ h' hc'
        (schemeSpaceMap (Space.residueFieldMap B integerBase hZ XUf.base u
          (B.residueField_spec_contains XUf.base.left.property u)))) :=
    isStructureContraction_residueFieldMap_of_fibre XUf Y' rfl h' hc' ū pt u hu hpt hres vX tG
      jX jG sqV sqG a haG hat hA
  -- Stacks 0E88 for families with étale scheme charts
  obtain ⟨Wn, huWn, hover⟩ := hasUniversalStructureContractionNear_of_hasEtaleSchemeChartAt XUf Y'
    rfl h' hc' u (hasEtaleSchemeChartAt _ _) (hasEtaleSchemeChartAt _ _) hs
  -- every point of `Spec κ(s)` maps to `u`
  have hsub : Subsingleton (Spec (.of (X.base.left.1.residueField s))) := inferInstance
  have hū_pt : ∀ y : p₀.siteObject.left.1, ū.left.1 y = u := fun y =>
    (congrArg ū.left.1 (@Subsingleton.elim _ hsub y pt)).trans hu
  -- the fibre of `Y'` at `u` is stable
  have h1F : (X.ofIsPullback B hZ w₀ qX (schemeSpaceMap vX)
      hqX₀).IsUniversalStructureContraction B hZ
      (Y'.ofIsPullback B hZ ū jG (schemeSpaceMap tG) sqG₀) rfl (schemeSpaceMap a) := by
    intro T t X'' Y'' pX fX pY fY c' s₁ s₂ e₁ e₂
    have S₁ : IsPullback (pX ≫ jX) fX XUf.toBase (schemeSpaceMap (t ≫ ū)) :=
      (congrArg (IsPullback (pX ≫ jX) fX XUf.toBase) (schemeSpaceMap_comp t ū)).mpr
        (s₁.paste_horiz sqV)
    have S₂ : IsPullback (pY ≫ jG) fY Y'.toBase (schemeSpaceMap (t ≫ ū)) :=
      (congrArg (IsPullback (pY ≫ jG) fY Y'.toBase) (schemeSpaceMap_comp t ū)).mpr
        (((Y'.ofIsPullback B hZ ū jG (schemeSpaceMap tG)
          sqG₀).isPullback_toBase_of_comp_eqToHom_refl s₂).paste_horiz sqG₀)
    refine hover T (t ≫ ū) (fun x => ?_) X'' Y'' _ fX _ fY c' S₁
      (Y'.isPullback_toBase_comp_eqToHom_refl S₂) ?_ e₂
    · have hmem : ū.left.1 (((𝒯).map t).base x) ∈ Wn := (hū_pt _).symm ▸ huWn
      exact hmem
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jG) e₁).trans
        ((Category.assoc _ _ _).trans ((congrArg (pX ≫ ·) haG).trans
          (Category.assoc _ _ _).symm)))
  have hstF := isStableCurveFamily_ofIsPullback_of_isStableContraction p₀ (Z := X) (Y := Y')
    w₀ ū vX tG qX jG hqX₀ sqG₀ hX a hat h1F hstA
  obtain ⟨O, huO, hOWn, hOst⟩ := exists_mem_forall_isStableCurveFamily_of_fibre (Y' := Y') hX e
    sqXU' h' hh' hover ū hu huWn hres sqG₀ hstF
  let U₁ : U.left.1.Opens := O
  have huU₁ : u ∈ U₁ := huO
  have hU₁ : B.Contains U₁.toScheme := Scheme.size_lt_of_isOpenImmersion U₁.ι U.left.property
  let W₁ : BigFppfOver B integerBase hZ := ofScheme U₁.toScheme hU₁
  let j : W₁ ⟶ U := homOfScheme U₁.ι
  have hj𝒯 : (𝒯).map j = U₁.ι := rfl
  have hjW : ∀ y, ((𝒯).map j).base y ∈ U₁ := fun y => y.2
  refine ⟨W₁, j ≫ e, ?_, ?_, ?_, ?_⟩
  · rw [Functor.map_comp, hj𝒯]
    have : Etale U₁.ι := inferInstance
    have := he
    exact Etale.etale_comp ((𝒯).map e) (f := U₁.ι)
  · refine ⟨⟨u, huU₁⟩, ?_⟩
    change ((𝒯).map e).base u = s
    rw [← hu]
    change (ū.left.1 ≫ e.left.1).base pt = s
    rw [h𝒯]
    exact Scheme.fromSpecResidueField_apply _ _
  · -- field-valued points over `s` lift
    exact fun p hp => exists_map_eq_of_mem_range_residueField e ū hū U₁ hU₁
      (fun y => by rw [hū_pt y]; exact huU₁) p hp
  -- the local stabilization over `W`
  let Yi := Y'.baseChangeAlong j
  have sqYj := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ Y'.toBase (schemeSpaceMap j)
  have hYi : IsStableCurveFamily B hZ Yi := hOst _ (Y'.homOfIsPullback B hZ j _ _ sqYj) hjW
  obtain ⟨ci, hci, h1⟩ := exists_contraction_baseChangeAlong_of_le (Y' := Y') e sqXU' h' hh'
    hover j fun y => hOWn (hjW y)
  have sqXφ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
    (schemeSpaceMap (j ≫ e))
  have hXi : IsPrestableCurveFamily B hZ (X.baseChangeAlong (j ≫ e)) :=
    isPrestableCurveFamily_of_hom (X.homOfIsPullback B hZ (j ≫ e) _ _ sqXφ) hX
  exact ⟨Yi, rfl, hYi, ci, hci, h1,
    hasStableContractionFibres_of_isUniversalStructureContraction hci hXi hYi h1⟩

end CurveFamily

end AlgebraicGeometry

end
