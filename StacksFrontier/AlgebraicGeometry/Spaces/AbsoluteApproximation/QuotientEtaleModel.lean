module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientChartLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientLimitAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismPropertiesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SchemeStageChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget

/-!
# An étale neighbourhood of the limit of a system of étale quotients descends to a stage

Let `E` be an inverse system of étale equivalence relations `(V_i, R_i)` over a directed set,
with cartesian source squares, affine transition morphisms on the objects and a limit
`V = lim V_i` in schemes, whose system of quotients `U_i = V_i / R_i` has bounded charts, and let
`U = lim U_i`. This is the situation of the proof of Stacks 07SU after the system approximating
the open part `U` has been made small
(`AlgebraicGeometry.Space.EtaleRelationSystem.exists_chartsBounded_reindex`).

Given an étale morphism of finite presentation `W ⟶ U` from an algebraic space, the proof of
Stacks 07SU descends it to a stage: by Stacks 07SK there are an index `0` and an algebraic space
`W_0` of finite presentation over `U_0` whose base change to `U` is `W`; by Stacks 07SL the base
change `W_i ⟶ U_i` is étale for `i` large; and if `W` is a scheme, then by Stacks 07SR so is
`W_i` for `i` large.

## Main results

* `AlgebraicGeometry.Space.EtaleRelationSystem.exists_morphismDescentSystem_of_isEtale`: the
  descent of `W ⟶ U` to a morphism `W₀ ⟶ U_{i₀}` at a stage, through a morphism descent system
  with bounded charts, with an étale stage and, when `W` is representable, a representable
  stage.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

namespace EtaleRelationSystem

/-- **The étale neighbourhood of the open part descends to a stage (proof of Stacks 07SU).**
Let `E` be an inverse system of étale equivalence relations over a directed set `I`, with affine
transition morphisms on the objects and a limit of the objects in schemes, whose system of
quotients `U_i` has bounded charts and quasi-compact quasi-separated stages, with algebraic
limit `U`. Let `Y ⟶ U` be an étale morphism of finite presentation from an algebraic space.

Then there are a stage `i₀` and an étale morphism of finite presentation `f₀ : W₀ ⟶ U_{i₀}`
from an algebraic space whose base change to `U` is `Y ⟶ U` (Stacks 07SK), whose base change
`W_i ⟶ U_i` is étale at some stage (Stacks 07SL), and — if `Y` is representable — whose base
change `W_i` is representable at some stage (Stacks 07SR). -/
theorem exists_morphismDescentSystem_of_isEtale {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (E : EtaleRelationSystem B S hS Iᵒᵖ)
    (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
    (hb : ChartsBounded B S hS E.quotient)
    (hqc : ∀ j, IsQuasiCompactSpace B S hS (E.quotient.obj j))
    (hqs : ∀ j, IsAbsolutelyQuasiSeparated B S hS hZ (E.quotient.obj j))
    (hL : IsAlgebraicSpace B S hS (limit E.quotient))
    (Y : Over (limit E.quotient)) (hY : IsAlgebraicSpace B S hS Y.left)
    (hFp : IsFinitePresentation B S hS Y.hom) (hEt : IsEtale B S hS Y.hom) :
    ∃ (i₀ : I) (Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (y : Y₀ ⟶ E.quotient.obj (op i₀)),
      IsAlgebraicSpace B S hS Y₀ ∧ IsFinitePresentation B S hS y ∧
      (∃ e : Y.left ≅ pullback (limit.π E.quotient (op i₀)) y,
        e.hom ≫ pullback.fst _ _ = Y.hom) ∧
      (∃ (i : I) (le : i₀ ≤ i), IsEtale B S hS (pullback.fst (E.quotient.map (homOfLE le).op) y)) ∧
      (Y.left.IsRepresentable → ∃ (i : I) (le : i₀ ≤ i),
        (pullback (E.quotient.map (homOfLE le).op) y).IsRepresentable) := by
  -- étaleness of `a` and `b` agree when `a ≫ fst = b` for a pullback projection along `𝟙`
  have hfst : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : G ⟶ H) (a : F ⟶ pullback g (𝟙 H))
      (b : F ⟶ G), a ≫ pullback.fst g (𝟙 H) = b → (IsEtale B S hS a ↔ IsEtale B S hS b) := by
    rintro F G H g a b rfl
    refine ⟨fun h => isEtale_comp B S hS h (isEtale_of_isIso B S hS _), fun h => ?_⟩
    simpa using isEtale_comp B S hS h (isEtale_of_isIso B S hS (inv (pullback.fst g (𝟙 _))))
  have hD : ∀ j, IsAlgebraicSpace B S hS (E.quotient.obj j) := E.isAlgebraicSpace_quotient_obj
  have hAff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (E.quotient.map g) :=
    E.isAffineHom_quotient_map hobj
  obtain ⟨i, Yi, hYi, hYifp, ⟨e⟩⟩ :=
    exists_model_of_finitePresentation_of_affineChartLimitsInSchemes B S hS hZ E.quotient hD hAff
      hqc hqs hL (E.isAffineHom_limit_π hobj cV hV hL) (E.affineChartLimitsInSchemes hobj cV hV)
      Y hY hFp
  let D : MorphismDescentSystemOfChartsBounded B S hS hZ I :=
    { base := E.quotient
      chartsBounded := hb
      base_isAlgebraicSpace := fun j => hD (op j)
      transition_affine := hAff
      limit_isAlgebraicSpace := hL
      initial := i.unop
      source₀ := Yi.left
      target₀ := E.quotient.obj i
      sourceToBase := Yi.hom
      targetToBase := 𝟙 _
      map₀ := Yi.hom
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hYi
      target₀_isAlgebraicSpace := hD i
      base₀_quasiCompact := hqc i
      base₀_quasiSeparated := hqs i
      source₀_quasiCompact := isQuasiCompactSpace_source_of_isQuasiCompact B S hS (hD i) (hqc i)
        hYifp.2.1
      source₀_quasiSeparated := isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hYi
        (hqs i) hYifp.2.2
      target₀_quasiCompact := hqc i
      target₀_quasiSeparated := hqs i }
  let eY : Y.left ≅ D.sourceLimit := (Over.forget _).mapIso e ≪≫ pullbackSymmetry _ _
  let q : D.sourceLimit ⟶ limit D.base := pullback.fst _ _
  have heY : eY.hom ≫ q = Y.hom := by
    show (e.hom.left ≫ (pullbackSymmetry Yi.hom (limit.π E.quotient i)).hom) ≫
      pullback.fst (limit.π E.quotient i) Yi.hom = Y.hom
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    simpa using Over.w e.hom
  have hEtLim : IsEtale B S hS D.mapLimit := by
    refine (hfst (limit.π E.quotient i) _ (eY.inv ≫ Y.hom) ?_).2
      (isEtale_comp B S hS (isEtale_of_isIso B S hS _) hEt)
    rw [← heY, Iso.inv_hom_id_assoc]
    exact pullback.lift_fst _ _ _
  obtain ⟨i', le, hi'⟩ := D.exists_isEtale_mapAt hEtLim hYifp.1
  refine ⟨i.unop, Yi.left, Yi.hom, hYi, hYifp, ⟨eY, heY⟩, ⟨i', le, ?_⟩, fun hrep => ?_⟩
  · exact (hfst _ _ _ (pullback.lift_fst _ _ _)).1 hi'
  obtain ⟨k, -, hk⟩ :=
    D.stagesSourceDescentSituation.exists_isRepresentable_system_obj_of_chartsBounded
      D.chartsBounded_stagesSourceSystem (isRepresentable_of_natIso _ eY)
  exact ⟨k.1, k.2, hk⟩

end EtaleRelationSystem

end AlgebraicGeometry.Space

end
