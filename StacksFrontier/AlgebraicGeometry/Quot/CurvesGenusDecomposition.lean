module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyResidueFieldFirstHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFieldFibreGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibreBettiZeroGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksCore.Tactic.StacksAttribute

/-!
# The decomposition `Curves^{h0,1} = ∐_g Curves_g` (Stacks 0E6K)

The open substack `Curves^{h0,1} ⊂ Curves` of Stacks 0E6I (families `f : X → S` with
`f_*𝒪_X = 𝒪_S` universally and fibres of dimension `1`) is the disjoint union of the open and
closed substacks `Curves_g`, `g ≥ 0`, of the families for which moreover `R¹f_*𝒪_X` is locally free
of rank `g`.

## Main results

* `AlgebraicGeometry.isGenusCurveFamily_of_hom`: `Curves_g` is stable under base change.
* `AlgebraicGeometry.isGenusCurveFamily_curveFamilyOfScheme_iff`: condition (2)(b) for a proper
  scheme of dimension at most one over a field.
* `AlgebraicGeometry.curvesGenus_isOpenSubstack_and_factors_iff_and_decomposition`:
  **Stacks 0E6K**.

## Implementation notes

`Curves_g` is the strictly full subcategory of `AlgebraicGeometry.IsGenusCurveFamily g`; open
substacks of `Curves` are as in Section 0E0E (`AlgebraicGeometry.IsOpenCurvesLocus`). The
decomposition "into open and closed substacks" is stated on every scheme-valued point
`S → Curves^{h0,1}`: the base changes of the `Curves_g` are open and closed subsets of `|S|`,
pairwise disjoint and covering `|S|`, which is what it means for the monomorphisms
`Curves_g → Curves^{h0,1}` to form a decomposition into open and closed substacks.

Condition (o) for `Curves_g` and the decomposition over a family in `Curves^{h0,1}` are the base's
`AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of` and
`AlgebraicGeometry.curvesGenus_decomposition_of`, at their four inputs, all proved: the openness of
`k = H⁰(X_k, 𝒪_{X_k})` is
`AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres`,
Stacks 0E6B (a) is
`AlgebraicGeometry.CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres`, the openness
of `Curves^{h0,1}` is
`AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily` (Stacks 0E0R at `i = 0` and
0E6B (a)), and parts (2), (3) of Stacks 0E1J are
`CurveFamily.hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions`
and
`CurveFamily.firstHigherDirectImageCommutesWithBaseChange_of_hasResidueFieldGlobalFunctions`.

## References

* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}


/-- Condition (o) for `Curves_g`, with its four inputs supplied. -/
private theorem isOpenCurvesLocus_isGenusCurveFamily (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsGenusCurveFamily B hZ g) :=
  isOpenCurvesLocus_isGenusCurveFamily_of
    CurveFamily.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres
    (fun _ =>
      CurveFamily.hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions)
    (fun _ =>
      CurveFamily.firstHigherDirectImageCommutesWithBaseChange_of_hasResidueFieldGlobalFunctions)
    g

open CurveFamily in
/-- **`Curves_g` is stable under morphisms of families of curves**, i.e. under base change:
condition (o) of Stacks 0E0E for `Curves_g` is the base's
`AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of`, whose four inputs are proved here:
the openness of `k = H⁰(X_k, 𝒪_{X_k})` (Stacks 0E0R at `i = 0`,
`AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres`),
Stacks 0E6B (a)
(`AlgebraicGeometry.CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres`), and
parts (2), (3) of Stacks 0E1J. -/
theorem isGenusCurveFamily_of_hom (g : ℕ) {F G : CurveFamily B hZ} (a : F ⟶ G)
    (hG : IsGenusCurveFamily B hZ g G) : IsGenusCurveFamily B hZ g F :=
  (isOpenCurvesLocus_isGenusCurveFamily g).prop_of_hom a hG

/-! ### Part (2): a proper scheme of dimension at most one over a field -/

/-- **Condition (2)(b) of Stacks 0E6K.** The family of curves of a proper scheme `X` of dimension
at most one over a field `k` is in `Curves_n` exactly when `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and the
genus of `X` (Stacks 0BY7) is `n`. -/
theorem isGenusCurveFamily_curveFamilyOfScheme_iff
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) (n : ℕ) :
    IsGenusCurveFamily B hZ n (curveFamilyOfScheme X B hZ hk hdim) ↔
      (topologicalKrullDim X.left = 1 ∧ Function.Bijective X.hom.appTop) ∧ genus X.hom = n := by
  let g := integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk
    X.hom
  have hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom :=
    Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g
      (inferInstanceAs (QuasiCompact X.hom))
  have hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom :=
    (Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 (inferInstanceAs (IsSeparated X.hom))
  have hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom :=
    (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2
      (inferInstanceAs (QuasiSeparated X.hom))
  have hstruct := fun {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y) hf hfl hfp h =>
    Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ f hf
      hfl hfp h
  have h := CurveFamily.isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff
    (fun Y hY =>
      CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
        hstruct hY)
    g k rfl (inferInstanceAs (Flat X.hom)) (inferInstanceAs (IsProper X.hom))
    (inferInstanceAs (LocallyOfFinitePresentation X.hom)) hqc hsep hqsep hdim n
  exact h.trans (and_congr_left' and_comm)

/-! ### Stacks 0E6K -/

open CurveFamily in
/-- **Stacks 0E6K.** There is a decomposition into open and closed substacks
`Curves^{h0,1} = ∐_{g ≥ 0} Curves_g`, where
(1) the classifying morphism of a family of curves `f : X → S` factors through `Curves_g` exactly
when `f_*𝒪_X = 𝒪_S`, this holds after arbitrary base change, the fibres of `f` have dimension `1`,
and `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g`; and
(2) for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the classifying morphism
`Spec(k) → Curves` factors through `Curves_g` exactly when `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and the
genus of `X` is `g`.

In the statement: `Curves^{h0,1}` and each `Curves_g` are open substacks of `Curves` (strictly full
subcategories whose inclusions are representable by algebraic spaces and open immersions), each
`Curves_g` lies in `Curves^{h0,1}`, parts (1) and (2) are the factorization criteria, and the
decomposition is read on every family `G` over a scheme `S` in `Curves^{h0,1}`: the loci in `|S|`
of the `Curves_g` are open and closed, pairwise disjoint and cover `|S|`. -/
@[stacks 0E6K]
theorem curvesGenus_isOpenSubstack_and_factors_iff_and_decomposition :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          CurveFamily.isOpenCurvesLocus_isH01CurveFamily.prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          CurveFamily.isOpenCurvesLocus_isH01CurveFamily.prop_of_hom)) ∧
    (∀ g : ℕ,
      (ObjectProperty.IsClosedUnderIsomorphisms (IsGenusCurveFamily B hZ g) ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsGenusCurveFamily B hZ g)
            (isGenusCurveFamily_of_hom g)).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsGenusCurveFamily B hZ g)
            (isGenusCurveFamily_of_hom g))) ∧
      (∀ X : CurveFamily B hZ, IsGenusCurveFamily B hZ g X → IsH01CurveFamily B hZ X) ∧
      (∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsGenusCurveFamily B hZ g),
            z ⋙ ObjectProperty.ι (IsGenusCurveFamily B hZ g) = y) ↔
          IsGenusCurveFamily B hZ g (y.obj (Over.mk (𝟙 U.left))))) ∧
      (∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
        (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
        (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsGenusCurveFamily B hZ g),
            z ⋙ ObjectProperty.ι (IsGenusCurveFamily B hZ g) = y) ↔
          (topologicalKrullDim X.left = 1 ∧ Function.Bijective X.hom.appTop) ∧
            genus X.hom = g))) ∧
    ∀ G : CurveFamily B hZ, IsH01CurveFamily B hZ G →
      ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          (⋃ g, Ω g) = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsGenusCurveFamily B hZ g F ↔
              Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
                (schemeSpaceMap a.baseMap).hom) ⊆ Ω g :=
  have hP := isOpenCurvesLocus_isGenusCurveFamily (B := B) (hZ := hZ)
  ⟨isOpenImmersion_curvesSubstackInclusion CurveFamily.isOpenCurvesLocus_isH01CurveFamily,
    fun g => ⟨isOpenImmersion_curvesSubstackInclusion (hP g),
      fun _ h => h.1,
      fun U y hy => factors_curvesSubstack_iff (hP g) U y hy,
      fun k _ hk X _ hdim U y hy e => by
        rw [factors_curvesSubstack_iff_of_iso (hP g) U y hy _ e]
        exact isGenusCurveFamily_curveFamilyOfScheme_iff k hk X hdim g⟩,
    curvesGenus_decomposition_of
      CurveFamily.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres
      CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres
      (fun _ => hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions)
      (fun _ => firstHigherDirectImageCommutesWithBaseChange_of_hasResidueFieldGlobalFunctions)⟩

end AlgebraicGeometry
