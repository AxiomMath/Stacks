module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExactOnCoveringObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CoheratorDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageCartesianChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCriteria
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionwiseHomology

/-!
# The direct image along an affine morphism commutes with the cohomology of a K-injective
complex with quasi-coherent cohomology

Let `h : Y ⟶ A` be an affine morphism of algebraic spaces over a scheme `S` and let `I` be a
K-injective complex of `𝒪_Y`-modules whose cohomology sheaves are quasi-coherent.  Then the
comparison `H^q(h_*I) ⟶ h_*H^q(I)` is an isomorphism in every degree.

This is the computation behind Derived Categories of Spaces, Lemma 08GY, that `Rh_*` of an
object of `D_QCoh(𝒪_Y)` has cohomology `h_*H^q`, and it is proved here directly on the small
étale sites rather than by reduction to schemes.  Exactness of sheaves of modules on `A` is
tested on the affine étale charts `V` of `A`
(`Stacks.SheafOfModules.EpiMono.exact_and_epi_of_hasEnoughObjects`).  Over such a `V` the
sections of `h_*M` are the sections of `M` over the base change `V ×_A Y`
(`AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_of_isPullback`), which is an
affine étale chart of `Y` because `h` is affine; and over an affine étale chart of `Y` the
sequence `I^{q-1} ⟶ Z^q(I) ⟶ H^q(I) ⟶ 0` of sections is exact, by Stacks 0BKZ read on the
complex of sections
(`Stacks.Cohomology.HypercohomologyEdge.exact_and_epi_sections_of_acyclic_cover`)
and the vanishing of the higher cohomology of a quasi-coherent module on an affine étale chart.

## Main results

* `AlgebraicGeometry.Space.isAffineChart_smallBaseChange_of_isAffineHom`: the base change of an
  affine étale chart along an affine morphism is an affine étale chart.
* `AlgebraicGeometry.Space.isIso_homologyComparison_modulePushforward_of_isAffineHom`: the
  comparison `H^q(h_*I) ⟶ h_*H^q(I)` is an isomorphism.
* `AlgebraicGeometry.Space.qcohDerivedProp_derivedPushforward_of_isAffineHom`: every right
  derived functor of `h_*` carries `D_QCoh(𝒪_Y)` into `D_QCoh(𝒪_A)`.

## References

* [Stacks Project, Tag 08GY](https://stacks.math.columbia.edu/tag/08GY)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.HypercohomologyEdge Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe u

namespace AlgebraicGeometry.Space

-- A universe-polymorphic `Abelian` instance for sheaves of modules, in scope through the
-- imports, leaves universes undetermined; everything below is at the universe of the schemes.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The base change of an affine étale chart along an affine morphism is an affine étale
chart.**  The chart `V ×_A Y` and the affine scheme that affineness of `h` produces over `V` are
two pullbacks of the same cospan of presheaves, hence isomorphic. -/
theorem isAffineChart_smallBaseChange_of_isAffineHom {Y A : AlgebraicSpaces B S hS} (h : Y ⟶ A)
    (hh : IsAffineHom B S hS h.hom) (hr : yoneda.relativelyRepresentable h.hom)
    (V : SmallEtale B S hS A.1) (hV : IsAffineChart B S hS A.1 V) :
    IsAffineChart B S hS Y.1 ((smallBaseChange B S hS h hr).obj V) := by
  obtain ⟨W, p, q, hpb⟩ := hh ⟨V.1.left, hV⟩ V.1.hom
  let e : yoneda.obj (hr.pullback V.1.hom) ≅ yoneda.obj W.obj :=
    (hr.isPullback V.1.hom).isoIsPullback _ _ hpb
  let e' : hr.pullback V.1.hom ≅ W.obj := Yoneda.fullyFaithful.preimageIso e
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W.obj) := W.property
  exact @IsAffine.of_isIso _ _ ((BigFppfOver.toScheme B S hS).mapIso e').hom (Iso.isIso_hom _) this

/-- The chart diagram formed by an étale chart `V` of `A` and its base change along a
representable morphism `h : Y ⟶ A`. -/
abbrev smallBaseChangeChartDiagram {Y A : AlgebraicSpaces B S hS} (h : Y ⟶ A)
    (hr : yoneda.relativelyRepresentable h.hom) (V : SmallEtale B S hS A.1) :
    ChartDiagram B S hS Y.1 A.1 h.hom where
  U := (smallBaseChange B S hS h hr).obj V
  V := V
  g := hr.snd V.1.hom
  comm := hr.w V.1.hom

/-- **The direct image along an affine morphism commutes with the cohomology of a K-injective
complex with quasi-coherent cohomology sheaves**: the comparison `H^q(h_*I) ⟶ h_*H^q(I)` is an
isomorphism. -/
theorem isIso_homologyComparison_modulePushforward_of_isAffineHom {Y A : AlgebraicSpaces B S hS}
    (h : Y ⟶ A) (hh : IsAffineHom B S hS h.hom)
    (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (hI : I.IsKInjective)
    (hqc : ∀ m, (I.homology m).IsQuasicoherentOnSite) (q : ℤ) :
    IsIso (homologyComparison (modulePushforward B S hS h) I q) := by
  have hr := relativelyRepresentable_of_isAffineHom B S hS h hh
  have := isGrothendieckAbelian_modules B S hS Y.1 Y.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  rw [isIso_homologyComparison_iff]
  refine Stacks.SheafOfModules.EpiMono.exact_and_epi_of_hasEnoughObjects
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS A.1 A.2).O)
    (IsAffineChart B S hS A.1) (hasEnoughObjects_isAffineChart B S hS A.1)
    (cyclesHomologyShortComplex (modulePushforward B S hS h) I q) fun V hV => ?_
  let d := smallBaseChangeChartDiagram B S hS h hr V
  have hd : IsPullback d.U.1.hom (yoneda.map d.g) h.hom d.V.1.hom := hr.isPullback V.1.hom
  obtain ⟨hex, hepi⟩ := exact_and_epi_sections_of_acyclic_cover
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) I hI
    (IsAffineChart B S hS Y.1) (hasEnoughObjects_isAffineChart B S hS Y.1)
    (fun W hW p hp m => isZero_rightDerived_evaluation_of_isAffineChart B S hS Y.1 Y.2 _
      (hqc m) W hW p hp) (isAffineChart_smallBaseChange_of_isAffineHom B S hS h hh hr V hV) q
  let c := fun M : Modules.{u, u} B S hS Y.1 Y.2 => modulePushforwardCounitApp B S hS h M d
  have hc : ∀ M, Function.Bijective (c M) := fun M =>
    bijective_modulePushforwardCounitApp_of_isPullback B S hS h M d hd
  have hpre : ∀ {M M' : Modules.{u, u} B S hS Y.1 Y.2} (a : M ⟶ M') x y,
      ((modulePushforward B S hS h).map a).val.app (op V) x = y ↔
        a.val.app (op d.U) (c M x) = c M' y := fun a x y => by
    rw [← modulePushforwardCounitApp_map B S hS h a d x]
    exact (hc _).1.eq_iff.symm
  have hc0 : ∀ M, c M 0 = 0 := fun M => by
    simpa using modulePushforwardCounitApp_add B S hS h M d 0 0
  have hex' : ∀ z : (I.cycles q).val.obj (op d.U), (I.homologyπ q).val.app (op d.U) z = 0 →
      ∃ y : (I.X (q - 1)).val.obj (op d.U), (I.toCycles (q - 1) q).val.app (op d.U) y = z :=
    (ShortComplex.ab_exact_iff _).1 hex
  have hsurj' : ∀ w : (I.homology q).val.obj (op d.U),
      ∃ z : (I.cycles q).val.obj (op d.U), (I.homologyπ q).val.app (op d.U) z = w :=
    (AddCommGrpCat.epi_iff_surjective _).1 hepi
  have g1 : ∀ x : ((modulePushforward B S hS h).obj (I.cycles q)).val.obj (op V),
      ((modulePushforward B S hS h).map (I.homologyπ q)).val.app (op V) x = 0 →
      ∃ y : ((modulePushforward B S hS h).obj (I.X (q - 1))).val.obj (op V),
        ((modulePushforward B S hS h).map (I.toCycles (q - 1) q)).val.app (op V) y = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hex' (c _ x) (((hpre _ x 0).1 hx).trans (hc0 _))
    obtain ⟨y', rfl⟩ := (hc _).2 y
    exact ⟨y', (hpre _ y' x).2 hy⟩
  have g2 : ∀ z : ((modulePushforward B S hS h).obj (I.homology q)).val.obj (op V),
      ∃ w : ((modulePushforward B S hS h).obj (I.cycles q)).val.obj (op V),
        ((modulePushforward B S hS h).map (I.homologyπ q)).val.app (op V) w = z := by
    intro z
    obtain ⟨w, hw⟩ := hsurj' (c _ z)
    obtain ⟨w', rfl⟩ := (hc _).2 w
    exact ⟨w', (hpre _ w' z).2 hw⟩
  exact ⟨(ShortComplex.ab_exact_iff _).2 g1, (AddCommGrpCat.epi_iff_surjective _).2 g2⟩

attribute [local instance] HasDerivedCategory.standard

/-- **The derived direct image along an affine morphism preserves quasi-coherence of
cohomology.**  For an affine morphism `h : Y ⟶ A` of algebraic spaces and any right derived
functor `R` of `h_*`, `R` carries `D_QCoh(𝒪_Y)` into `D_QCoh(𝒪_A)`: on a K-injective
representative `I` the cohomology of `R I = h_*I` is `h_*H^q(I)`
(`AlgebraicGeometry.Space.isIso_homologyComparison_modulePushforward_of_isAffineHom`), and the
direct image of a quasi-coherent module along the quasi-compact quasi-separated morphism `h` is
quasi-coherent (Stacks 03M9). -/
theorem qcohDerivedProp_derivedPushforward_of_isAffineHom {Y A : AlgebraicSpaces B S hS}
    (h : Y ⟶ A) (hh : IsAffineHom B S hS h.hom)
    (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS A.1 A.2))
    (α : (modulePushforward B S hS h).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (hL : qcohDerivedProp B S hS Y L) :
    qcohDerivedProp B S hS A (R.obj L) := by
  obtain ⟨I, f, hI, hf⟩ := exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2
    (DerivedCategory.Q.objPreimage L)
  have : IsIso (DerivedCategory.Q.map f) := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  let e : L ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso L).symm ≪≫ asIso (DerivedCategory.Q.map f)
  have hIqc : ∀ m, (I.homology m).IsQuasicoherentOnSite := fun m =>
    (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      ((DerivedCategory.homologyFunctor _ m).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ m).app I) (hL m)
  have hα : IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    isIso_app_of_isKInjective_modulePushforward B S hS h DerivedCategory.Qh R α I hI
  let J := ((modulePushforward B S hS h).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let eR : R.obj L ≅ DerivedCategory.Q.obj J :=
    R.mapIso (e ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm) ≪≫
      (asIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
      DerivedCategory.Qh.mapIso
        (((modulePushforward B S hS h).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
      (DerivedCategory.quotientCompQhIso _).app J
  intro n
  have hcomp := isIso_homologyComparison_modulePushforward_of_isAffineHom B S hS h hh I hI hIqc n
  refine (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
    (((DerivedCategory.homologyFunctor _ n).mapIso eR ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app J ≪≫
      @asIso _ _ _ _ (homologyComparison (modulePushforward B S hS h) I n) hcomp).symm) ?_
  exact isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS h
    (isQuasiCompact_of_isAffineHom' B S hS h.hom Y.2 A.2 hh)
    (isQuasiSeparated_of_isAffineHom B S hS h.hom Y.2 A.2 hh) _ (hIqc n)

end AlgebraicGeometry.Space

end
