module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.DatumTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.AffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PointTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.DescendingProperties.SeparatedDescentConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfFiniteSurjection
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.Topology.C1573Port.Sober.GenericPointsImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573
namespace CategoryTheory.Limits.IsPullback.C1573
end CategoryTheory.Limits.IsPullback.C1573

/-!
# A Chow datum over `Spec ℤ`, by Noetherian approximation

Let `f : X ⟶ Y` be a morphism of finite presentation of algebraic spaces over `Spec ℤ`, with `Y`
quasi-compact and separated and `X` separated, quasi-compact and locally Noetherian. Then `f` has
a Chow datum. Writing `Y = lim Y_i` with `Y_i` of finite type over `ℤ` (Stacks 07SU) and `f` as
the base change of some `X_i ⟶ Y_i` (Stacks 07SK), it is the base change of the Chow datum over
the affine Noetherian base `Spec ℤ` of `X̄_i ⟶ Y_i` for large `i`, where `X̄_i` is the
scheme-theoretic image of `X ⟶ X_i` (Stacks 082Z).

## Main results

* `AlgebraicGeometry.Space.C1573.exists_stage_pointsMap_incomparable`: points of a limit none of
  which specializes to another keep this property at late stages.
* `CategoryTheory.Limits.IsPullback.C1573.of_comp_mono`: a cartesian square stays cartesian after
  cancelling a monomorphism.
* `AlgebraicGeometry.Space.C1573.exists_chowDatum_of_isFinitePresentation`: the statement above.

## References

* [Stacks Project, Tag 088U](https://stacks.math.columbia.edu/tag/088U)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 086V](https://stacks.math.columbia.edu/tag/086V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

open _root_.C1573 _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.Limits.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Generic points stay apart at a late stage of an inverse system.** For a cofiltered inverse
system of algebraic spaces with affine transition morphisms satisfying the chapter's convention,
a finite set of points of the limit, none in the closure of another, maps at every late enough
stage to a set of points none of which lies in the closure of another (Stacks 086V). -/
theorem C1573.exists_stage_pointsMap_incomparable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {E : Set (points B S hS (limit D))} (hEf : E.Finite)
    (hE : ∀ a ∈ E, ∀ b ∈ E, a ∈ @closure _ (pointTopology B S hS (limit D)) {b} → a = b) :
    ∃ k : I, ∀ (k' : I) (_ : k' ⟶ k), ∀ a ∈ E, ∀ b ∈ E,
      pointsMap B S hS (limit D) (limit.π D k') a ∈
        @closure _ (pointTopology B S hS (D.obj k'))
          {pointsMap B S hS (limit D) (limit.π D k') b} → a = b := by
  classical
  have htop := pointTopology_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD hAffine
  let := pointTopology B S hS (limit D)
  let := fun i => pointTopology B S hS (D.obj i)
  have hpair : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → ∃ k : I,
      pointsMap B S hS (limit D) (limit.π D k) a ∉
        closure {pointsMap B S hS (limit D) (limit.π D k) b} := by
    intro a ha b hb hab
    by_contra hcon
    push Not at hcon
    apply hab
    refine hE a ha b hb (specializes_iff_mem_closure.1 ?_)
    exact specializes_of_forall_specializes_of_eq_iInf_induced
      (τ := fun i => pointTopology B S hS (D.obj i))
      (fun k => pointsMap B S hS (limit D) (limit.π D k)) htop
      (fun k => specializes_iff_mem_closure.2 (hcon k))
  have : Nonempty I := IsCofiltered.nonempty
  choose! kk hkk using hpair
  let O : Finset I := ((hEf.prod hEf).toFinset.filter (fun ab => ab.1 ≠ ab.2)).image
    (fun ab => kk ab.1 ab.2)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists O
  refine ⟨k, fun k' g a ha b hb h => by_contra fun hab => ?_⟩
  have hmem : kk a b ∈ O := Finset.mem_image.2 ⟨(a, b), by simp [ha, hb, hab], rfl⟩
  obtain ⟨g'⟩ := hk hmem
  have hcomp : pointsMap B S hS (limit D) (limit.π D (kk a b)) =
      pointsMap B S hS (D.obj k') (D.map (g ≫ g')) ∘
        pointsMap B S hS (limit D) (limit.π D k') := by
    rw [← pointsMap_comp, limit.w]
  apply hkk a ha b hb hab
  rw [hcomp]
  exact specializes_iff_mem_closure.1
    ((specializes_iff_mem_closure.2 h).map (continuous_pointsMap B S hS (D.map (g ≫ g'))))

/-- **A cartesian square stays cartesian after cancelling a monomorphism on its top side.** -/
theorem _root_.CategoryTheory.Limits.IsPullback.C1573.of_comp_mono {C : Type*} [Category C]
    {P X' X Y Z : C} {p' : P ⟶ X'} {ι : X' ⟶ X} [Mono ι] {f : P ⟶ Y} {g : X ⟶ Z} {q : Y ⟶ Z}
    (h : IsPullback (p' ≫ ι) f g q) : IsPullback p' f (ι ≫ g) q := by
  refine ⟨⟨by simpa using h.w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift (s.fst ≫ ι) s.snd (by simpa using s.condition)) ?_ ?_ ?_⟩⟩
  · exact fun s => (cancel_mono ι).1 (by simp)
  · exact fun s => h.lift_snd _ _ _
  · exact fun s m hm₁ hm₂ => h.hom_ext (by rw [h.lift_fst, ← hm₁, Category.assoc])
      (by rw [h.lift_snd, ← hm₂])

section Integers

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))

/-- An absolutely separated algebraic space over `Spec ℤ` is separated over the terminal object. -/
theorem C1573.isSeparated_terminal_of_isAbsolutelySeparated
    {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ F)
    (h : IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ F) :
    IsSeparated B (⊤_ Scheme.{u}) hZ ((isTerminal_yoneda_obj_base B (⊤_ Scheme.{u}) hZ).from F) :=
  (isSeparatedOver_iff_isSeparated_of_isTerminal B (⊤_ Scheme.{u}) hZ
    (isTerminal_yoneda_obj_base B (⊤_ Scheme.{u}) hZ) _).1
    ((isAbsolutelySeparated_iff_isSeparatedOver B (⊤_ Scheme.{u}) hZ hZ inferInstance hF).1 h)

/-- If the limit of a descent situation is absolutely separated, so is every late enough stage. -/
private theorem exists_forall_ge_isAbsolutelySeparated_system_obj {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I)
    (hconv : SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ D.system)
    (hX : IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ D.limitCone.pt) :
    ∃ j, ∀ k, j ≤ k → IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ (D.system.obj (op k)) := by
  obtain ⟨j, -, hj⟩ :=
    DescentSituation.C1573.exists_isAbsolutelySeparated_system_obj_of_siteContainsBaseChangeLimits
      B (⊤_ Scheme.{u}) hZ hZ D hconv hX
  exact ⟨j, fun k hjk => isAbsolutelySeparated_of_isSeparated B (⊤_ Scheme.{u}) hZ hZ hj
    (isSeparated_of_isAffineHom B (⊤_ Scheme.{u}) hZ _ (D.algebraicSpace k) (D.algebraicSpace j)
      (D.transition_affine (homOfLE hjk).op))⟩

/-- **A Chow datum over `Spec ℤ`, by Noetherian approximation.** Let `f : X ⟶ Y` be a morphism of
finite presentation of algebraic spaces over `Spec ℤ`, with `Y` quasi-compact and separated and
`X` separated, quasi-compact and locally Noetherian. Then `f` has a Chow datum. -/
theorem C1573.exists_chowDatum_of_isFinitePresentation {X Y : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
    (f : X.1 ⟶ Y.1) (hfp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ f)
    (hYqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Y.1)
    (hYsep : IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ Y.1)
    (hXsep : IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ X.1)
    (hXqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X.1)
    (hXN : HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    Nonempty (ChowDatum X f) := by
  classical
  have hYqs := isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ Y.1
    hYsep
  obtain ⟨A, hconv⟩ : HasConventionalNoetherianApproximation B hZ Y.1 := by
    obtain ⟨A₀, a, -, has, hae⟩ :=
      (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (⊤_ Scheme.{u}) hZ Y.1
        Y.2).mp hYqc
    exact hasConventionalNoetherianApproximation_of_etaleAtlas Y.2 hYqc hYqs A₀ a has hae
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  have hD : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (A.diagram.obj j) := A.isAlgebraicSpace
  have hQc : ∀ j, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (A.diagram.obj j) :=
    fun j => (NoetherianApproximation.isNoetherian_obj B hZ A j).1
  have hQs : ∀ j, IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (A.diagram.obj j) :=
    A.isAbsolutelyQuasiSeparated
  have hAff : ∀ {j j' : A.Iᵒᵖ} (g : j ⟶ j'), IsAffineHom B (⊤_ Scheme.{u}) hZ (A.diagram.map g) :=
    fun g => A.isAffineHom_map g
  let e : Y.1 ≅ limit A.diagram := A.isLimit.conePointUniqueUpToIso (limit.isLimit A.diagram)
  have hlim : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (limit A.diagram) :=
    IsAlgebraicSpace.of_iso Y.2 e
  have hfp' : IsFinitePresentation B (⊤_ Scheme.{u}) hZ (f ≫ e.hom) :=
    isFinitePresentation_of_arrowIso B _ hZ f (f ≫ e.hom) (𝟙 X.1) e.hom (by simp) hfp
  obtain ⟨i, X₀, hX₀, hX₀fp, ⟨eX⟩⟩ :=
    exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ hZ
      A.diagram hD hAff hQc hQs hconv hlim (Over.mk (f ≫ e.hom)) X.2 hfp'
  let M : MorphismDescentSituation B (⊤_ Scheme.{u}) hZ hZ A.I :=
    { base := A.diagram
      base_isAlgebraicSpace := fun k => hD (op k)
      transition_affine := fun g => hAff g
      limit_isAlgebraicSpace := hlim
      initial := i.unop
      source₀ := X₀.left
      target₀ := A.diagram.obj i
      sourceToBase := X₀.hom
      targetToBase := 𝟙 _
      map₀ := X₀.hom
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hX₀
      target₀_isAlgebraicSpace := hD i
      base₀_quasiCompact := hQc i
      base₀_quasiSeparated := hQs i
      source₀_quasiCompact :=
        isQuasiCompactSpace_of_isFinitePresentation B (⊤_ Scheme.{u}) hZ X₀.hom (hD i) (hQc i)
          hX₀fp
      source₀_quasiSeparated :=
        isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ hX₀ (hQs i)
          hX₀fp.2.2
      target₀_quasiCompact := hQc i
      target₀_quasiSeparated := hQs i }
  let α : M.sourceLimit ≅ X.1 :=
    pullbackSymmetry (limit.π A.diagram i) X₀.hom ≪≫ (Over.forget _).mapIso eX.symm
  have hαf : α.inv ≫ pullback.fst (limit.π A.diagram i) X₀.hom = f ≫ e.hom := by
    show (eX.hom.left ≫ (pullbackSymmetry (limit.π A.diagram i) X₀.hom).inv) ≫ _ = _
    rw [Category.assoc, pullbackSymmetry_inv_comp_fst]
    exact Over.w eX.hom
  set Ysys := M.baseDescentSituation with hYsys
  set Xsys := M.stagesSourceDescentSituation with hXsys
  have hconvY : SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ Ysys.system :=
    hconv.comp_subtypeGe i.unop
  have hconvX : SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ Xsys.system :=
    (hconv.comp_subtypeGe i.unop).baseChangeOverSystem _ _
  have hYlimsep : IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ Ysys.limitCone.pt :=
    isAbsolutelySeparated_of_isSeparated B (⊤_ Scheme.{u}) hZ hZ hYsep
      (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ e.inv)
  obtain ⟨jY, hjY⟩ := exists_forall_ge_isAbsolutelySeparated_system_obj hZ Ysys hconvY hYlimsep
  have hXlimsep : IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ Xsys.limitCone.pt :=
    isAbsolutelySeparated_of_isSeparated B (⊤_ Scheme.{u}) hZ hZ hXsep
      (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ α.hom)
  obtain ⟨jX, hjX⟩ := exists_forall_ge_isAbsolutelySeparated_system_obj hZ Xsys hconvX hXlimsep
  let := pointTopology B (⊤_ Scheme.{u}) hZ X.1
  let := pointTopology B (⊤_ Scheme.{u}) hZ (limit Xsys.system)
  have hXqs := isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ X.1
    hXsep
  have hdec := isDecentSpace_of_isAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ X.1 X.2 hXqs
  have : NoetherianSpace (points B (⊤_ Scheme.{u}) hZ X.1) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B (⊤_ Scheme.{u}) hZ X.1 X.2 hXqc hXN
  have : QuasiSober (points B (⊤_ Scheme.{u}) hZ X.1) :=
    quasiSober_points_of_isDecentSpace B (⊤_ Scheme.{u}) hZ X.2 hdec
  have : T0Space (points B (⊤_ Scheme.{u}) hZ X.1) :=
    t0Space_points_of_isDecentSpace B (⊤_ Scheme.{u}) hZ X.2 hdec
  set E := genericPoints (points B (⊤_ Scheme.{u}) hZ X.1) with hE
  have hEf : E.Finite := genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  let β : X.1 ≅ limit Xsys.system :=
    α.symm ≪≫ Xsys.isLimit.conePointUniqueUpToIso (limit.isLimit _)
  let H := pointsHomeomorphOfIso B (⊤_ Scheme.{u}) hZ β
  obtain ⟨kD, hkDinc⟩ := exists_stage_pointsMap_incomparable Xsys.system hconvX
    (fun j => Xsys.algebraicSpace j.unop) (fun g => Xsys.transition_affine g)
    (E := H '' E) (hEf.image _) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      rw [← Set.image_singleton, ← H.image_closure] at hab
      rw [eq_of_mem_genericPoints_of_mem_closure ha hb (H.injective.mem_set_image.1 hab)])
  obtain ⟨k₁, hk₁Y, hk₁X⟩ := exists_ge_ge jY jX
  obtain ⟨k, hk₁, hkD⟩ := exists_ge_ge k₁ kD.unop
  have hYk := hjY k (hk₁Y.trans hk₁)
  have hXk := hjX k (hk₁X.trans hk₁)
  set fk : Xsys.system.obj (op k) ⟶ Ysys.system.obj (op k) := pullback.fst _ _ with hfk
  set pk : X.1 ⟶ Xsys.system.obj (op k) := β.hom ≫ limit.π Xsys.system (op k) with hpk
  set qk : Y.1 ⟶ Ysys.system.obj (op k) := e.hom ≫ limit.π A.diagram (op k.1) with hqk
  have hpk' : pk = α.inv ≫ Xsys.limitCone.π.app (op k) :=
    (Category.assoc _ _ _).trans (congrArg (α.inv ≫ ·)
      (Xsys.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op k)))
  have hsq : IsPullback pk f fk qk := by
    have h0 := isPullback_baseChangeOverMap B (⊤_ Scheme.{u}) hZ (limit.π A.diagram i)
      ((M.stagesBaseToInitial).app (op k)) ((M.stagesBaseCone).π.app (op k))
      (M.stagesBaseCone_π_comp (op k)) X₀.hom
    rw [hpk']
    refine h0.of_iso α (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc α _).symm
    · have h : pullback.fst (limit.π A.diagram i) X₀.hom = α.hom ≫ f ≫ e.hom :=
        (Iso.hom_inv_id_assoc α _).symm.trans (congrArg (α.hom ≫ ·) hαf)
      exact (congrArg (· ≫ e.inv) h).trans ((Category.assoc _ _ _).trans
        (congrArg (α.hom ≫ ·) (by rw [Category.assoc, e.hom_inv_id, Category.comp_id])))
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc e _).symm
  have hXkalg := Xsys.algebraicSpace k
  have hYkalg := Ysys.algebraicSpace k
  have hpkaff : IsAffineHom B (⊤_ Scheme.{u}) hZ pk :=
    isAffineHom_iso_comp β.hom
      (isAffineHom_limitπ_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ Xsys.system hconvX
        (fun g => Xsys.transition_affine g) (op k))
  have hqkaff : IsAffineHom B (⊤_ Scheme.{u}) hZ qk :=
    isAffineHom_iso_comp e.hom
      (isAffineHom_limitπ_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ A.diagram hconv hAff
        (op k.1))
  set Xb := schemeTheoreticImageSubfunctor B (⊤_ Scheme.{u}) hZ pk with hXb
  have hXbcl : IsClosedSubspace B (⊤_ Scheme.{u}) hZ Xb :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B (⊤_ Scheme.{u}) hZ pk hXkalg
  set p' : X.1 ⟶ Xb.toFunctor := toSchemeTheoreticImage B (⊤_ Scheme.{u}) hZ pk with hp'
  have hp'ι : p' ≫ Xb.ι = pk := toSchemeTheoreticImage_ι B (⊤_ Scheme.{u}) hZ pk
  have hsq' : IsPullback p' f (Xb.ι ≫ fk) qk :=
    IsPullback.C1573.of_comp_mono (by rw [hp'ι]; exact hsq)
  have hp'aff : IsAffineHom B (⊤_ Scheme.{u}) hZ p' :=
    isAffineHom_of_isPullback hsq'.flip hqkaff
  let := pointTopology B (⊤_ Scheme.{u}) hZ Xb.toFunctor
  let := pointTopology B (⊤_ Scheme.{u}) hZ (Xsys.system.obj (op k))
  have hpkqc : IsQuasiCompact B (⊤_ Scheme.{u}) hZ pk :=
    isQuasiCompact_of_isAffineHom' B (⊤_ Scheme.{u}) hZ pk X.2 hXkalg hpkaff
  have hqd : DenseRange (pointsMap B (⊤_ Scheme.{u}) hZ X.1 p') :=
    denseRange_pointsMap_toSchemeTheoreticImage_of_isQuasiCompact B (⊤_ Scheme.{u}) hZ pk X.2
      hXkalg hpkqc
  have hdense : ∀ O : Set (points B (⊤_ Scheme.{u}) hZ Xb.toFunctor), IsOpen O → Dense O →
      Dense (pointsMap B (⊤_ Scheme.{u}) hZ X.1 p' ⁻¹' O) := by
    intro O hO hOd
    refine dense_preimage_of_finite_of_closure_eq_univ (continuous_pointsMap _ _ _ p') hqd hEf
      genericPoints.closure ?_ hO hOd
    intro a ha b hb h
    have h1 : pointsMap B (⊤_ Scheme.{u}) hZ X.1 pk a ∈
        closure {pointsMap B (⊤_ Scheme.{u}) hZ X.1 pk b} := by
      rw [← hp'ι, pointsMap_comp]
      exact specializes_iff_mem_closure.1
        ((specializes_iff_mem_closure.2 h).map (continuous_pointsMap _ _ _ Xb.ι))
    have h2 := hkDinc (op k) (homOfLE hkD).op (H a) ⟨a, ha, rfl⟩ (H b) ⟨b, hb, rfl⟩
    have hHk : ∀ x, pointsMap B (⊤_ Scheme.{u}) hZ (limit Xsys.system)
        (limit.π Xsys.system (op k)) (H x) = pointsMap B (⊤_ Scheme.{u}) hZ X.1 pk x := by
      intro x
      rw [hpk, pointsMap_comp]
      rfl
    rw [hHk, hHk] at h2
    exact H.injective (h2 h1)
  have : IsAffine (⊤_ Scheme.{u}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  have : _root_.AlgebraicGeometry.IsNoetherian (⊤_ Scheme.{u}) := {}
  set tZ := isTerminal_yoneda_obj_base B (⊤_ Scheme.{u}) hZ with htZ
  have hT := isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ (Over.mk (𝟙 (B.obj hZ)))
  have hTsep : IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ
      (yoneda.obj (Over.mk (𝟙 (B.obj hZ)))) :=
    isAbsolutelySeparated_of_isSeparated_to_affine B (⊤_ Scheme.{u}) hZ hZ _
      (inferInstanceAs (IsAffine (⊤_ Scheme.{u}))) (𝟙 _)
      (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ _)
  have hTqs := isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ _ hTsep
  have hXbsep : IsSeparated B (⊤_ Scheme.{u}) hZ (tZ.from Xb.toFunctor) :=
    isSeparated_terminal_of_isAbsolutelySeparated hZ hXbcl.1
      (isAbsolutelySeparated_of_isSeparated B (⊤_ Scheme.{u}) hZ hZ hXk
        (isSeparated_of_isClosedImmersion B (⊤_ Scheme.{u}) hZ Xb.ι hXbcl.2))
  have hfkfp' : IsFinitePresentation B (⊤_ Scheme.{u}) hZ
      (pullback.fst ((M.stagesBaseToInitial).app (op k)) X₀.hom) :=
    isFinitePresentation_of_arrowIso B _ hZ (pullback.snd X₀.hom _) _
      (pullbackSymmetry X₀.hom _).hom (𝟙 _) (by rw [pullbackSymmetry_hom_comp_fst]; simp)
      (isFinitePresentation_pullback_snd B (⊤_ Scheme.{u}) hZ X₀.hom _ hX₀ (hD i) hYkalg hX₀fp)
  have hfkfp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ fk := hfkfp'
  have hYkLFT : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ (tZ.from (Ysys.system.obj (op k))) := by
    have h := isLocallyOfFiniteType_terminal_of_isFiniteTypeOverIntegers
      (A.isFiniteTypeOverIntegers (op k.1))
    let := isLocallyOfFiniteType_respectsIso B (⊤_ Scheme.{u}) hZ
    have he : tZ.from (Ysys.system.obj (op k)) =
        terminal.from _ ≫ (terminalIsTerminal.uniqueUpToIso tZ).hom := tZ.hom_ext _ _
    rw [he]
    exact MorphismProperty.RespectsIso.postcomp
      (P := fun _ _ f => IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ f) _ _ h
  have hXbft : IsFiniteType B (⊤_ Scheme.{u}) hZ (tZ.from Xb.toFunctor) := by
    refine ⟨?_, isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hT hTqs
      (isQuasiCompactSpace_of_isClosedImmersion B (⊤_ Scheme.{u}) hZ (Xsys.quasiCompact k) Xb.ι
        hXbcl.2) _⟩
    have he : tZ.from Xb.toFunctor = Xb.ι ≫ fk ≫ tZ.from (Ysys.system.obj (op k)) :=
      tZ.hom_ext _ _
    rw [he]
    exact isLocallyOfFiniteType_comp' B (⊤_ Scheme.{u}) hZ _ _ hXkalg hT
      (isLocallyOfFiniteType_of_isClosedImmersion B (⊤_ Scheme.{u}) hZ Xb.ι hXbcl.2)
      (isLocallyOfFiniteType_comp' B (⊤_ Scheme.{u}) hZ _ _ hYkalg hT
        (isFiniteType_of_isFinitePresentation B (⊤_ Scheme.{u}) hZ hfkfp).1 hYkLFT)
  have hYksep : IsSeparated B (⊤_ Scheme.{u}) hZ (tZ.from (Ysys.system.obj (op k))) :=
    isSeparated_terminal_of_isAbsolutelySeparated hZ hYkalg hYk
  obtain ⟨d₀⟩ := exists_chowDatum_of_isAffine (S := ⊤_ Scheme.{u})
    (⟨Xb.toFunctor, hXbcl.1⟩ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ) (tZ.from _) hXbsep hXbft
    (Xb.ι ≫ fk) hYksep
  have hpair := ((isAffineHom_tfae_of_isAlgebraicSpace B (⊤_ Scheme.{u}) hZ p' X.2
    hXbcl.1).out 2 1).mp hp'aff
  exact d₀.baseChange f p' qk hsq' hpair.2
    (isSeparated_terminal_of_isAbsolutelySeparated hZ X.2 hXsep) hXN hdense

end Integers

end AlgebraicGeometry.Space

end
