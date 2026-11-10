module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverFromAffineChartsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeAlgebraIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartAffineOpenCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpensOfOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecAffineChartExists
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence

/-!
# The relative spectrum of a bounded quasi-coherent algebra on an algebraic space

Let `X` be an algebraic space over a scheme `S` of a big fppf site and `𝒜` a quasi-coherent sheaf
of commutative `𝒪_X`-algebras with fewer than `B.cutoff` sections over every étale chart.  This
file assembles the relative spectrum `\underline{Spec}_X(𝒜)` of Stacks 081W from its functor of
points `P = AlgebraicGeometry.Space.relativeSpecPoints 𝒜`:

* `P` is an algebraic space and `π : P ⟶ X` is representable and affine, by the criterion
  `AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_isAffineHom_of_atlas`: over every affine
  open `V` of an atlas of `X` the fibre is `Spec 𝒜(V)`
  (`AlgebraicGeometry.Space.isPullback_affineChartSpec`), and these spectra have a uniform size
  bound because the sections of `𝒜` over all affine opens of the atlas are dominated by the
  sections over one chart (`AlgebraicGeometry.Space.AlgebraSheaf.exists_dominatingChart`);
* the universal morphism `𝒜 ⟶ π_* 𝒪_P` (`AlgebraicGeometry.Space.relativeSpecUniversalMap`) is an
  isomorphism, because it is bijective over every affine chart, where it is `𝒜(V) ≅ Γ(Spec 𝒜(V))`.

The chart reading `AlgebraicGeometry.Space.chartEval` at an affine chart is injective
(`AlgebraicGeometry.Space.algebraHom_ext_of_chartEval`) and reaches every `Γ(V)`-algebra map
(`AlgebraicGeometry.Space.exists_chartEval_eq`); the remaining input, that the functor of points is
an fppf sheaf, is the section variable `hsheaf`, discharged where the unconditional statements are
made.

## Main definitions

* `AlgebraicGeometry.Space.relativeSpecAffineOverOf`: the relative spectrum as an algebraic space
  affine over `X`.
* `AlgebraicGeometry.Space.pushforwardAlgebraRelativeSpecAffineOverOfIso`: the identification of
  the direct image of its structure sheaf with `𝒜`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_isAffineHom_relativeSpecPoints`
* `AlgebraicGeometry.Space.bijective_relativeSpecUniversalMapApp_of_isAffine`
* `AlgebraicGeometry.Space.isIso_relativeSpecUniversalMap`

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Assembly

variable {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
  (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A)
  (hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (relativeSpecPoints B S hS A))
  (hAq : A.IsQuasicoherent)

include hAq in
/-- The chart reading at an affine chart is injective
(`AlgebraicGeometry.Space.algebraHom_ext_of_chartEval`). -/
theorem injective_chartEval_of_isAffine (V : SmallEtale B S hS X.1) [hV : IsAffine (chartScheme V)]
    {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom) :
    Function.Injective (AlgebraicGeometry.Space.chartEval B S hS A V v x hxv) :=
  fun _ _ h => algebraHom_ext_of_chartEval B S hS hAq hV v x hxv h

include hA hAq hsheaf in
/-- **The functor of points of the relative spectrum is an algebraic space, representable and
affine over `X`.** -/
theorem isAlgebraicSpace_and_presheaf_isAffineHom_relativeSpecPoints :
    IsAlgebraicSpace B S hS (relativeSpecPoints B S hS A) ∧
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf
          (relativeSpecPointsπ B S hS A) := by
  obtain ⟨U, a, hs, he⟩ := X.2.exists_atlas
  let Uc : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a, he⟩
  obtain ⟨V', hV'⟩ := AlgebraSheaf.exists_dominatingChart B S hS A Uc
  refine isAlgebraicSpace_and_presheaf_isAffineHom_of_atlas B S hS X.2 hsheaf
    (relativeSpecPointsπ B S hS A) hs he
    (μ := max ℵ₀ #(A.right.obj.obj (op V'))) (max_lt B.aleph0_lt_cutoff (hA V')) ?_
  intro V u hu hVaff
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u) := hu
  let Vc : SmallEtale B S hS X.1 :=
    etaleChartOfIsEtale B S hS (yoneda.map u ≫ Uc.obj.hom)
      (isEtale_yoneda_map_comp_of_isOpenImmersion B S hS Uc u)
  have : IsAffine (chartScheme Vc) := hVaff
  refine ⟨affineChartSpec B S hS A hA Vc,
    affineChartSpecToPoints B S hS A hA Vc (exists_chartEval_eq B S hS A hAq Vc),
    affineChartSpecHom B S hS A hA Vc,
    isPullback_affineChartSpec B S hS A hA Vc (injective_chartEval_of_isAffine B S hS A hAq Vc)
      (exists_chartEval_eq B S hS A hAq Vc), ?_, ?_⟩
  · change IsAffine (Spec (A.right.obj.obj (op Vc)))
    infer_instance
  · change (Spec (A.right.obj.obj (op Vc))).size ≤ _
    rw [Scheme.size_Spec]
    refine max_le_max le_rfl ?_
    let W : (chartScheme Uc).affineOpens :=
      ⟨((BigFppfOver.toScheme B S hS).map u).opensRange,
        isAffineOpen_opensRange ((BigFppfOver.toScheme B S hS).map u)⟩
    obtain ⟨k, hk⟩ := hV' W
    calc #(A.right.obj.obj (op Vc))
        = #(A.right.obj.obj (op ((chartOpens B S hS Uc).obj
            ((BigFppfOver.toScheme B S hS).map u).opensRange))) :=
          mk_congr ((CategoryTheory.forget CommRingCat).mapIso
            (A.right.obj.mapIso
              (etaleChartIsoChartOpensOfIsOpenImmersion B S hS Uc u).op)).toEquiv.symm
      _ ≤ #(A.right.obj.obj (op V')) := mk_le_of_surjective hk

include hA hAq in
/-- **The universal morphism `𝒜 ⟶ π_* 𝒪_P` is bijective at every affine chart.**  Over an affine
chart `V` the fibre `P ×_X V` is `Spec 𝒜(V)` (`isPullback_affineChartSpec`), and under that
identification the chart reading of the universal point is `𝒜(V) ≅ Γ(Spec 𝒜(V))`. -/
theorem bijective_relativeSpecUniversalMapApp_of_isAffine
    (hP : IsAlgebraicSpace B S hS (relativeSpecPoints B S hS A))
    (hπ : yoneda.relativelyRepresentable (relativeSpecPointsπ B S hS A))
    (V : SmallEtale B S hS X.1) [IsAffine (chartScheme V)] :
    Function.Bijective (relativeSpecUniversalMapApp B S hS A hP hπ V).hom := by
  have hpb := isPullback_affineChartSpec B S hS A hA V
    (injective_chartEval_of_isAffine B S hS A hAq V) (exists_chartEval_eq B S hS A hAq V)
  -- the two representing objects of the fibre are isomorphic over `P` and `V`
  let ε : hπ.pullback V.obj.hom ≅ affineChartSpec B S hS A hA V :=
    Functor.preimageIso yoneda ((hπ.isPullback V.obj.hom).isoIsPullback _ _ hpb)
  have hε₂ : ε.inv ≫ hπ.snd V.obj.hom = affineChartSpecHom B S hS A hA V := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, Functor.preimageIso_inv, Functor.map_preimage]
    exact (hπ.isPullback V.obj.hom).isoIsPullback_inv_snd _ _ hpb
  have hε₁ : yoneda.map ε.inv ≫ hπ.fst V.obj.hom =
      affineChartSpecToPoints B S hS A hA V (exists_chartEval_eq B S hS A hAq V) := by
    rw [Functor.preimageIso_inv, Functor.map_preimage]
    exact (hπ.isPullback V.obj.hom).isoIsPullback_inv_fst _ _ hpb
  have hpt : (relativeSpecUniversalPoint B S hS A hπ V).map B S hS ε.inv =
      affineChartSpecPoint B S hS A hA V (exists_chartEval_eq B S hS A hAq V) := by
    unfold relativeSpecUniversalPoint
    rw [← relativeSpecPointsEquiv_map, yonedaEquiv_naturality, hε₁, affineChartSpecToPoints,
      Equiv.apply_symm_apply]
    exact Equiv.apply_symm_apply _ _
  have key : (relativeSpecUniversalPoint B S hS A hπ V).chartEval B S hS V (hπ.snd V.obj.hom)
      (relativeSpecUniversalPoint_pt B S hS A hπ V) ≫
        ((BigFppfOver.toScheme B S hS).map ε.inv).appTop =
      (Scheme.ΓSpecIso (A.right.obj.obj (op V))).inv := by
    rw [← RelativeSpecPoint.chartEval_map B S hS V ε.inv _ _ _
      (by rw [hpt, hε₂]; exact yonedaEquiv_symm_affineChartSpecPt B S hS A hA V),
      ← affineChartSpecPoint_chartEval B S hS A hA V (exists_chartEval_eq B S hS A hAq V)]
    exact RelativeSpecPoint.chartEval_congr B S hS V hε₂ hpt _ _
  have hiso : IsIso ((relativeSpecUniversalPoint B S hS A hπ V).chartEval B S hS V
      (hπ.snd V.obj.hom) (relativeSpecUniversalPoint_pt B S hS A hπ V)) := by
    have : IsIso ((relativeSpecUniversalPoint B S hS A hπ V).chartEval B S hS V
        (hπ.snd V.obj.hom) (relativeSpecUniversalPoint_pt B S hS A hπ V) ≫
          ((BigFppfOver.toScheme B S hS).map ε.inv).appTop) := by
      rw [key]
      infer_instance
    have : IsIso (((BigFppfOver.toScheme B S hS).map ε.inv).appTop) :=
      inferInstanceAs (IsIso (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ε.inv).op))
    exact IsIso.of_isIso_comp_right _ (((BigFppfOver.toScheme B S hS).map ε.inv).appTop)
  unfold relativeSpecUniversalMapApp
  exact ConcreteCategory.bijective_of_isIso _

include hA hAq hsheaf in
/-- The functor of points of the relative spectrum is an algebraic space. -/
theorem isAlgebraicSpace_relativeSpecPoints :
    IsAlgebraicSpace B S hS (relativeSpecPoints B S hS A) :=
  (isAlgebraicSpace_and_presheaf_isAffineHom_relativeSpecPoints B S hS A hA hsheaf hAq).1

include hA hAq hsheaf in
/-- The projection of the relative spectrum to `X` is representable. -/
theorem relativelyRepresentable_relativeSpecPointsπ :
    yoneda.relativelyRepresentable (relativeSpecPointsπ B S hS A) :=
  (isAlgebraicSpace_and_presheaf_isAffineHom_relativeSpecPoints B S hS A hA hsheaf hAq).2.rep

/-- **The relative spectrum as an algebraic space affine over `X`.** -/
def relativeSpecAffineOverOf : AffineOver B S hS X :=
  ⟨relativeSpecOver B S hS A (isAlgebraicSpace_relativeSpecPoints B S hS A hA hsheaf hAq),
    isAffineHom_of_presheaf
      (isAlgebraicSpace_and_presheaf_isAffineHom_relativeSpecPoints B S hS A hA hsheaf hAq).2⟩

include hA hAq in
/-- **The universal morphism `𝒜 ⟶ π_* 𝒪_P` is an isomorphism.** -/
theorem isIso_relativeSpecUniversalMap
    (hP : IsAlgebraicSpace B S hS (relativeSpecPoints B S hS A))
    (hπ : yoneda.relativelyRepresentable (relativeSpecPointsπ B S hS A)) :
    IsIso (relativeSpecUniversalMap B S hS A hP hπ) :=
  AlgebraSheaf.isIso_of_bijective_affineChartDiagram B S hS (𝟙 X) _ fun d hU _ => by
    have : IsAffine (chartScheme d.U) := hU
    exact bijective_relativeSpecUniversalMapApp_of_isAffine B S hS A hA hAq hP hπ d.U

/-- **The direct image of the structure sheaf of the relative spectrum is `𝒜`.** -/
def pushforwardAlgebraRelativeSpecAffineOverOfIso :
    pushforwardAlgebra B S hS (relativeSpecAffineOverOf B S hS A hA hsheaf hAq).obj ≅ A :=
  have := isIso_relativeSpecUniversalMap B S hS A hA hAq
    (isAlgebraicSpace_relativeSpecPoints B S hS A hA hsheaf hAq)
    (relativelyRepresentable_relativeSpecPointsπ B S hS A hA hsheaf hAq)
  (asIso (relativeSpecUniversalMap B S hS A
    (isAlgebraicSpace_relativeSpecPoints B S hS A hA hsheaf hAq)
    (relativelyRepresentable_relativeSpecPointsπ B S hS A hA hsheaf hAq))).symm

end Assembly

end AlgebraicGeometry.Space

end
