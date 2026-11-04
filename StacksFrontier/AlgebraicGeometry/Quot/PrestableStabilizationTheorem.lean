module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationLocal
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationExistence
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.StableFamilySemistable
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.StableReductionOfStabilization

/-!
# The stabilization of a prestable family of curves and stable reduction

Let `f : X ⟶ S` be a prestable family of curves of genus `g ≥ 2`. Then `f` factors as
`X ⟶ Y ⟶ S` with `Y ⟶ S` a stable family of curves and `c : X ⟶ Y` satisfying conditions (1) and
(2), uniquely up to unique isomorphism. As a consequence, a smooth projective curve of genus
`g ≥ 2` over the fraction field of a discrete valuation ring has semistable reduction exactly when
it is the generic fibre of a stable family of curves.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_stabilization_and_existsUnique_iso`: existence and
  uniqueness of the stabilization of a prestable family of curves of genus `g ≥ 2`.
* `Stacks.Models.hasSemistableReduction_iff_exists_isStableCurveFamily`: a curve of genus `g ≥ 2`
  has semistable reduction exactly when it is the generic fibre of a stable family of curves.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E8D](https://stacks.math.columbia.edu/tag/0E8D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- Let `X ⟶ S` be a prestable family of curves of genus `g ≥ 2`. Then there are a stable family
of curves `Y ⟶ S` and a morphism `c : X ⟶ Y` over `S` such that

1. `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, and this remains true after base change by any morphism
   `S' ⟶ S`, and
2. for every field-valued point `s` of `S` the morphism `c_s : X_s ⟶ Y_s` is the contraction of
   rational tails and bridges (it satisfies the conditions of Stacks 0E7Q characterizing it).

Moreover `c` is unique up to unique isomorphism: for any two morphisms `cᵢ : X ⟶ Yᵢ` over `S` to
families of curves satisfying (1) and (2) there is exactly one isomorphism `e : Y₁ ≅ Y₂` over `S`
with `c₁ ≫ e = c₂`. -/
@[stacks 0E8A "Existence and uniqueness in one statement. `X ⟶ S` is a prestable family of \
curves whose fibres over all field-valued points have genus `g ≥ 2` (`HasFibresOfGenus`, the \
genus of a prestable family, Stacks 0E6V). The factorization `X ⟶ Y ⟶ S` is a family of curves \
`Y` over `S` (same base, `hb`) with `c ≫ g = f`. Condition (1) is \
`IsUniversalStructureContraction`: for every scheme `S' ⟶ S` of the site and the base change \
`c' : X' ⟶ Y'`, `𝒪_{Y'} ⟶ c'_*𝒪_{X'}` is an isomorphism and `R¹c'_*𝒪_{X'} = 0` (S' = S gives \
the condition for c). Condition (2) is `HasStableContractionFibres`, asserted at every \
field-valued point of `S` (so at every `s ∈ S` through `Spec κ(s)`): the fibre `c_s` satisfies \
the three conditions of Stacks 0E7Q, which characterize the contraction of rational tails and \
bridges of Section 0E7N up to unique isomorphism \
(`exists_isStableContraction_comp_tails_bridges`). \
Uniqueness up to unique isomorphism: for any two such `cᵢ : X ⟶ Yᵢ` (the targets need not be \
assumed stable) there is exactly one isomorphism `e : Y₁ ≅ Y₂` over `S` with `c₁ ≫ e = c₂`."]
theorem exists_stabilization_and_existsUnique_iso
    {X : CurveFamily B hZ} (hX : IsPrestableCurveFamily B hZ X) {g : ℕ} (hg : 2 ≤ g)
    (hgen : X.HasFibresOfGenus g) :
    (∃ (Y : CurveFamily B hZ) (hb : Y.base = X.base) (c : X.total ⟶ Y.total),
      IsStableCurveFamily B hZ Y ∧ c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase ∧
      X.IsUniversalStructureContraction B hZ Y hb c ∧ X.HasStableContractionFibres B hZ Y hb c) ∧
    ∀ (Y₁ Y₂ : CurveFamily B hZ) (hb₁ : Y₁.base = X.base) (hb₂ : Y₂.base = X.base)
      (c₁ : X.total ⟶ Y₁.total) (c₂ : X.total ⟶ Y₂.total),
      c₁ ≫ Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) = X.toBase →
      c₂ ≫ Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) = X.toBase →
      X.IsUniversalStructureContraction B hZ Y₁ hb₁ c₁ →
      X.IsUniversalStructureContraction B hZ Y₂ hb₂ c₂ →
      X.HasStableContractionFibres B hZ Y₁ hb₁ c₁ → X.HasStableContractionFibres B hZ Y₂ hb₂ c₂ →
      ∃! e : Y₁.total ≅ Y₂.total, c₁ ≫ e.hom = c₂ ∧
        e.hom ≫ Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) =
          Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) := by
  refine ⟨?_, fun Y₁ Y₂ hb₁ hb₂ c₁ c₂ hc₁ hc₂ h1₁ h1₂ h2₁ h2₂ => ?_⟩
  · choose W φ hφ hs hlift Y hY hYst c hc h1 h2 using
      fun s => exists_local_stabilization hX hg hgen s
    refine exists_stabilization_of_etale hX hg hgen φ hφ (fun x => ⟨x, hs x⟩)
      (fun p => ?_) hY hYst c hc h1 h2
    obtain ⟨wp, hwp⟩ : ∃ w : p.siteObject ⟶ X.base, w = p.value := ⟨_, rfl⟩
    let idK : Spec (.of p.carrier) ⟶ (𝒯).obj p.siteObject := 𝟙 _
    let x := idK.base (IsLocalRing.closedPoint p.carrier)
    exact ⟨_, hlift _ p ⟨x, by rw [← hwp]⟩⟩
  · obtain ⟨e, he, heb, hu⟩ := existsUnique_iso_of_hasStableContractionFibres hX hg hgen hc₁ hc₂
      h1₁ h1₂ h2₁ h2₂
    exact ⟨e, ⟨he, heb⟩, fun e' ⟨he', heb'⟩ => hu e' he' heb'⟩

end CurveFamily

end AlgebraicGeometry

open AlgebraicGeometry

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth projective curve
over `K` with `H⁰(C, 𝒪_C) = K` of genus `g ≥ 2`. Then `C` has semistable reduction (Stacks 0CDH)
exactly when it is the generic fibre of a stable family of curves over `R`: a stable family `F`
over `Spec R` with a morphism of families of curves from `C ⟶ Spec K` to `F` lying over
`Spec K ⟶ Spec R`. -/
@[stacks 0E8D "`C ⟶ Spec K` is smooth, projective, a curve (`IsCurve`), with `H⁰(C, 𝒪_C) = K` \
and genus `≥ 2`. (1) is `HasSemistableReduction R c hc` (Semistable Reduction, Definition \
0CDH). (2), a stable family of curves over `R` with generic fibre `C`, is a stable family of \
curves `F` (Stacks 0E75) whose base is identified with `Spec R` (`ψ`), with a morphism of \
families of curves (a cartesian square) from the family `C ⟶ Spec K` to `F` lying over \
`Spec K ⟶ Spec R`."]
theorem hasSemistableReduction_iff_exists_isStableCurveFamily
    (B : BigFppfSite.{u}) (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R)))
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hg : 2 ≤ genus c) :
    HasSemistableReduction R c hc ↔
      ∃ (F : CurveFamily B hZ) (ψ : F.base ≅ integerSiteObject B hZ hR)
        (φ : @curveFamilyOfScheme K _ (Over.mk c) hc.isProper B hZ
          (contains_spec_of_isFractionRing hR)
          (IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)).le ⟶ F),
        IsStableCurveFamily B hZ F ∧
          φ.baseMap ≫ ψ.hom = integerSiteMap B hZ (contains_spec_of_isFractionRing hR) hR
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : IsProper c := hc.isProper
  constructor
  · intro h
    obtain ⟨Y, hY, q, hflat, hproper, hlfp, hfib, hpre, hgen, φ, hφ⟩ :=
      exists_isPrestableCurveFamily_of_hasSemistableReduction B hZ hR c hc h
    have hgenX : (curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hR q) hflat hproper
        hlfp hfib).HasFibresOfGenus (genus c) := fun p => by
      obtain ⟨V, v, q', hq'⟩ := CurveFamily.exists_isPullback_fieldValuedPoint B hZ _ p
      have hq'' := CurveFamily.isPullback_yoneda_of_isPullback_schemeSpace _ p hq'
      exact ⟨V, v, q'.hom, hq'', hgen p V v q'.hom hq''⟩
    obtain ⟨⟨Y', hb, c', hYst, hc', -, h2⟩, -⟩ :=
      CurveFamily.exists_stabilization_and_existsUnique_iso hpre hg hgenX
    exact exists_isStableCurveFamily_of_stabilization B hZ hR c hg (Iso.refl _) φ
      ((Category.comp_id _).trans hφ) hb c' hc' hYst h2
  · rintro ⟨F, ψ, φ, hF, hφ⟩
    exact hasSemistableReduction_of_isStableCurveFamily B hZ hR c hc F ψ φ hφ hF

end Stacks.Models

end
