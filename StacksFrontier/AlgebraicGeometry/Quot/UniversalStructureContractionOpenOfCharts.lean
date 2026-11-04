module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageAssociatedModule

/-!
# Stacks 0E88 from étale scheme charts of the two families

Let `S` be a scheme, `s ∈ S`, and let `c : X ⟶ Y` be a morphism over `S` of families of curves
(Stacks 0D4Z). Stacks 0E88 says: if `c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and `R¹c_{s,*}𝒪_{X_s} = 0`, then
after replacing `S` by an open neighbourhood of `s` we have `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`,
and this remains true after base change by any morphism `S' ⟶ S`.

The proof in the source first makes `X` and `Y` schemes over an étale neighbourhood of `s`
(Stacks 0E6F) and then applies Stacks 0E7L. This file proves the statement from the pointwise
conclusion of Stacks 0E6F for the two families, in the form of étale scheme charts
(`AlgebraicGeometry.CurveFamily.HasEtaleSchemeChartAt`): an étale morphism `φ : U ⟶ S` of the
site through `s` and a scheme `Z` of the site with a cartesian square exhibiting `schemeSpace Z`
as `X ×_S U`. The two charts are combined into one (Stacks 055U, through
`AlgebraicGeometry.CurveFamily.exists_affine_etale_sections_of_smooth`), and the chart form of
the statement is `AlgebraicGeometry.CurveFamily.exists_isOpen_isStructureContraction_of_chart`,
whose input on higher direct images of represented morphisms (the separated case of Stacks
071N) is, in the namespace `AlgebraicGeometry.Space`,
`nonempty_rightDerived_modulePushforward_representedAssociatedModule_of_isSeparated`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasEtaleSchemeChartAt`: over an étale neighbourhood of `s` the
  total space of the family is a scheme.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isOpen_isStructureContraction_of_hasEtaleSchemeChartAt`:
  the statement of Stacks 0E88 for families having étale scheme charts at `s`.

## Implementation notes

The conclusion is stated in the vocabulary of
`AlgebraicGeometry.Space.IsStructureContraction`: an open `W ∋ s` of the base such that for
every scheme `T` of the site over `S` landing in `W`, and every pair of cartesian squares
exhibiting `X'` and `Y'` as `X ×_S T` and `Y ×_S T`, the induced `c' : X' ⟶ Y'` is a structure
contraction. Taking `T = W` gives the statement for `c` over `W`, and the quantification over
`T` is the persistence under base change. The two families share their base through
`hb : Y.base = X.base`.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **An étale scheme chart of a family of curves at a point of its base.** There are an étale
morphism `φ : U ⟶ S` of the site whose image contains `s` and a scheme `Z` of the site with a
cartesian square exhibiting `schemeSpace Z` as the base change `X ×_S U`. This is the pointwise
conclusion of Stacks 0E6F. -/
def HasEtaleSchemeChartAt (X : CurveFamily B hZ) (s : (𝒯).obj X.base) : Prop :=
  ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ X.base) (u : (𝒯).obj U),
    Etale ((𝒯).map φ) ∧ (𝒯).map φ u = s ∧
      ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ X.total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)

/-- `AlgebraicGeometry.CurveFamily.HasEtaleSchemeChartAt` read over a scheme equal to the base
of the family. -/
theorem HasEtaleSchemeChartAt.of_base_eq {X : CurveFamily B hZ} {S : BigFppfOver B integerBase hZ}
    (h : X.base = S) (s : (𝒯).obj S) (hX : X.HasEtaleSchemeChartAt (cast (by rw [h]) s)) :
    ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ S),
      Etale ((𝒯).map π) ∧ s ∈ Set.range ((𝒯).map π) ∧
      ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ X.total) (q : Z ⟶ T'),
        IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap (π ≫ eqToHom h.symm)) := by
  subst h
  obtain ⟨U, φ, u, hφ, hu, Z, p, q, hsq⟩ := hX
  exact ⟨U, φ, hφ, ⟨u, hu⟩, Z, p, q, by simpa using hsq⟩

/-- **The base change of a scheme chart.** If `X ×_S T'` is the scheme `Z` through `π : T' ⟶ S`,
then for every `g : U ⟶ T'` the base change `X ×_S U` along `g ≫ π` is the scheme `Z ×_{T'} U`. -/
theorem exists_isPullback_of_schemeChart (X : CurveFamily B hZ)
    {S T' Z U : BigFppfOver B integerBase hZ} (hS : X.base = S) {π : T' ⟶ S}
    {p : schemeSpace Z ⟶ X.total} {q : Z ⟶ T'}
    (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap (π ≫ eqToHom hS.symm)))
    (g : U ⟶ T') :
    ∃ (Z' : BigFppfOver B integerBase hZ) (p' : schemeSpace Z' ⟶ X.total) (q' : Z' ⟶ U),
      IsPullback p' (schemeSpaceMap q') X.toBase (schemeSpaceMap ((g ≫ π) ≫ eqToHom hS.symm)) := by
  refine ⟨pullback q g, schemeSpaceMap (pullback.fst q g) ≫ p, pullback.snd q g, ?_⟩
  rw [Category.assoc, schemeSpaceMap_comp]
  exact (isPullback_schemeSpaceMap_fst_snd q g).paste_horiz hsq

/-- **Common étale scheme charts.** If finitely many families of curves over a common base `S`
have étale scheme charts at `s`, then one étale morphism `φ : U ⟶ S` through `s`, with `U`
affine, is a scheme chart for all of them. -/
theorem exists_etale_isPullback_of_hasEtaleSchemeChartAt {ι : Type*} [Finite ι]
    {S : BigFppfOver B integerBase hZ} (X : ι → CurveFamily B hZ) (hX : ∀ i, (X i).base = S)
    (s : (𝒯).obj S) (hch : ∀ i, (X i).HasEtaleSchemeChartAt (cast (by rw [hX i]) s)) :
    ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ S) (u : (𝒯).obj U),
      Etale ((𝒯).map φ) ∧ (𝒯).map φ u = s ∧
      ∀ i, ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ (X i).total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) (X i).toBase
          (schemeSpaceMap (φ ≫ eqToHom (hX i).symm)) := by
  choose T' π hπ hs Z p q hsq using fun i => (hch i).of_base_eq (hX i) s
  obtain ⟨U, φ, u, hφ, -, hu, hg⟩ :=
    exists_affine_etale_sections_of_smooth s T' π (fun i => inferInstance) (fun i => hs i)
  refine ⟨U, φ, u, hφ, hu, fun i => ?_⟩
  obtain ⟨g, rfl⟩ := hg i
  exact exists_isPullback_of_schemeChart (X i) (hX i) (hsq i) g

open Stacks.AlgebraicGeometry.TopDegreeBaseChange Space in
/-- **Stacks 0E88 for families with étale scheme charts.** Let `c : X ⟶ Y` be a morphism over
`S` of families of curves and `s ∈ S` a point at which both families have étale scheme charts.
If `c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and `R¹c_{s,*}𝒪_{X_s} = 0`, there is an open neighbourhood `W` of
`s` such that for every scheme `T ⟶ S` landing in `W` and every base change `c' : X_T ⟶ Y_T` of
`c`, `𝒪_{Y_T} = c'_*𝒪_{X_T}` and `R¹c'_*𝒪_{X_T} = 0`. -/
theorem exists_isOpen_isStructureContraction_of_hasEtaleSchemeChartAt
    (X Y : CurveFamily B hZ) (hb : Y.base = X.base) (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase) (s : X.base.left.1)
    (hXs : X.HasEtaleSchemeChartAt s) (hYs : Y.HasEtaleSchemeChartAt (cast (by rw [hb]; rfl) s))
    (hs : Space.IsStructureContraction B integerBase hZ
      (Space.structureContractionBaseChange B integerBase hZ c hc
        (schemeSpaceMap (Space.residueFieldMap B integerBase hZ X.base s
          (B.residueField_spec_contains X.base.left.property s))))) :
    ∃ W : X.base.left.1.Opens, s ∈ W ∧
      ∀ (T : BigFppfOver B integerBase hZ) (h : T ⟶ X.base),
        (∀ t, ((𝒯).map h).base t ∈ W) →
        ∀ (X' Y' : AlgebraicSpaces B integerBase hZ) (pX' : X' ⟶ X.total)
          (fX' : X' ⟶ schemeSpace T) (pY' : Y' ⟶ Y.total) (fY' : Y' ⟶ schemeSpace T)
          (c' : X' ⟶ Y'),
          IsPullback pX' fX' X.toBase (schemeSpaceMap h) →
          IsPullback pY' fY' (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap h) →
          c' ≫ pY' = pX' ≫ c → c' ≫ fY' = fX' →
          Space.IsStructureContraction B integerBase hZ c' := by
  have hX : ∀ i, (![X, Y] i).base = X.base := Fin.forall_fin_two.2 ⟨rfl, hb⟩
  obtain ⟨U, φ, u, hφ, rfl, hsq⟩ :=
    exists_etale_isPullback_of_hasEtaleSchemeChartAt ![X, Y] hX s (Fin.forall_fin_two.2 ⟨hXs, hYs⟩)
  obtain ⟨ZX, pX, qX, sqX⟩ := hsq 0
  obtain ⟨ZY, pY, qY, sqY⟩ := hsq 1
  have sqX₀ : IsPullback pX (schemeSpaceMap qX) X.toBase
      (schemeSpaceMap (φ ≫ eqToHom (rfl : X.base = X.base))) := sqX
  have sqX' : IsPullback pX (schemeSpaceMap qX) X.toBase (schemeSpaceMap φ) := by
    simpa using sqX₀
  exact exists_isOpen_isStructureContraction_of_chart X Y hb c hc φ hφ u hs pX qX sqX' pY qY sqY
    (fun g hqc hsep F hF k =>
      Space.nonempty_rightDerived_modulePushforward_representedAssociatedModule_of_isSeparated
        B integerBase hZ g hqc hsep F hF k)

end CurveFamily

end AlgebraicGeometry

end
