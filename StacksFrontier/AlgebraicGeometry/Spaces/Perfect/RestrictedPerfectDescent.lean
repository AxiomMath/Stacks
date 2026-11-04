module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationAffinePerfectDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfectPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomId

/-!
# Descent of perfect objects for the restrictions of Situation 09RH

The proof of Stacks 09RJ runs the induction principle of Stacks 08GP over the quasi-compact and
quasi-separated objects `U₀` of `(X₀)_{spaces,étale}`, for the property that the perfect objects
on `U = X ×_{X₀} U₀` descend to some `U_i = X_i ×_{X₀} U₀`. This file sets up that property and
proves it for the affine `U₀`.

The restricted systems keep the size bound on their charts that the affine case needs
(`AlgebraicGeometry.Space.DescentSituation.chartsBounded_restrictTo`): reindexing along the
inclusion of the later stages and base changing along `U₀ ⟶ X₀` both preserve it.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.PerfectObjectsDescend`: every perfect object of
  `D(𝒪_X)` on the limit is `Lfᵢ^* Eᵢ` for a stage `i ≥ 0` and a perfect object `Eᵢ` of
  `D(𝒪_{Xᵢ})` (the essential surjectivity half of Stacks 09RJ).

## Main results

* `AlgebraicGeometry.Space.DescentSituation.chartsBounded_restrictTo`.
* `AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_restrictTo_of_isAffineSpace`:
  the affine case of the induction.
* `AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_of_restrictTo_id`: the property
  for the restriction to `X₀` itself is the property for the situation.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.Space.DescentSituation

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **The essential surjectivity half of Stacks 09RJ** for a situation `D`: every perfect object
`E` of `D(𝒪_X)` on the limit `X` (on the model of the spaces-étale site) is `Lfᵢ^* Eᵢ` for some
stage `i ≥ 0` and some perfect object `Eᵢ` of `D(𝒪_{Xᵢ})`, where `fᵢ : X ⟶ Xᵢ` is the
projection. -/
def PerfectObjectsDescend : Prop :=
  ∀ (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).O))),
    (spacesEtaleModelRingedSite B S hS ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).IsPerfect E →
    ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelRingedTopos B S hS ⟨D.system.obj (op i), D.algebraicSpace i⟩).O))),
      (spacesEtaleModelRingedSite B S hS ⟨D.system.obj (op i), D.algebraicSpace i⟩).IsPerfect Eᵢ ∧
        Nonempty ((derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E)

/-- Perfect objects descend in Situation 09RH when the charts are bounded and the chosen stage is
affine (`exists_isPerfect_derivedPullback_iso_of_isAffineSpace`). -/
theorem perfectObjectsDescend_of_isAffineSpace (hb : ChartsBounded B S hS D.system)
    (hbase : IsAffineSpace B S hS (D.system.obj (op D.base))) : D.PerfectObjectsDescend :=
  fun E hE => D.exists_isPerfect_derivedPullback_iso_of_isAffineSpace hb hbase E hE

/-- The later stages are fewer than the site's size cutoff, being a subtype of the index set. -/
theorem mk_laterStages_op_lt (hb : ChartsBounded B S hS D.system) :
    #({i : I // D.base ≤ i}ᵒᵖ) < B.cutoff :=
  calc #({i : I // D.base ≤ i}ᵒᵖ) = #{i : I // D.base ≤ i} :=
        mk_congr (Opposite.equivToOpposite (α := {i : I // D.base ≤ i})).symm
    _ ≤ #I := mk_subtype_le _
    _ = #Iᵒᵖ := mk_congr (Opposite.equivToOpposite (α := I))
    _ < B.cutoff := hb.mk_lt

/-- **The charts of the later stages are bounded** when those of the whole system are: the
transition morphisms of the later stages are transition morphisms of the system, and the index
category is a thin subcategory. -/
theorem chartsBounded_laterStages (hb : ChartsBounded B S hS D.system) :
    ChartsBounded B S hS D.laterStages.system :=
  hb.comp (laterStagesInclusion D).op (mk_laterStages_op_lt D hb)
    (mk_over_lt_of_mk_lt B.aleph0_lt_cutoff (mk_laterStages_op_lt D hb)
      (fun k k' =>
        have : Finite (k ⟶ k') := Finite.of_subsingleton
        (lt_aleph0_of_finite _).le))

variable {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAlgebraicSpace B S hS U₀)
  (hU₀qc : IsQuasiCompactSpace B S hS U₀) (hU₀qs : IsAbsolutelyQuasiSeparated B S hS hZ U₀)
  (u : U₀ ⟶ D.system.obj (op D.base))

/-- **The restriction `U_i = X_i ×_{X₀} U₀` of Situation 09RH has bounded charts** when the
situation has: the later stages have bounded charts
(`AlgebraicGeometry.Space.DescentSituation.chartsBounded_laterStages`) and base change along
`U₀ ⟶ X₀` preserves the bound (`AlgebraicGeometry.Space.ChartsBounded.baseChangeOver`). -/
theorem chartsBounded_restrictTo (hb : ChartsBounded B S hS D.system) :
    ChartsBounded B S hS (D.restrictTo hU₀ hU₀qc hU₀qs u).system :=
  (D.chartsBounded_laterStages hb).baseChangeOver (laterStagesToBaseStage D) u

/-- The chosen stage `X₀ ×_{X₀} U₀` of the restricted situation is affine when `U₀` is. -/
theorem isAffineSpace_restrictTo_base (hU₀aff : IsAffineSpace B S hS U₀) :
    IsAffineSpace B S hS ((D.restrictTo hU₀ hU₀qc hU₀qs u).system.obj
      (op (D.restrictTo hU₀ hU₀qc hU₀qs u).base)) := by
  have : IsIso (D.system.map (homOfLE (le_refl D.base)).op) := by
    rw [show D.system.map (homOfLE (le_refl D.base)).op = 𝟙 _ from D.system.map_id _]
    infer_instance
  exact hU₀aff.of_iso (asIso (pullback.snd (D.system.map (homOfLE (le_refl D.base)).op) u)).symm

/-- **Stacks 09RJ, essential surjectivity, for an affine `U₀`**: perfect objects on
`U = X ×_{X₀} U₀` descend to some `U_i = X_i ×_{X₀} U₀`, when the charts of the situation are
bounded and `U₀` is affine. This is the affine case of the induction of Stacks 08GP in the
source's proof. -/
theorem perfectObjectsDescend_restrictTo_of_isAffineSpace (hb : ChartsBounded B S hS D.system)
    (hU₀aff : IsAffineSpace B S hS U₀) :
    (D.restrictTo hU₀ hU₀qc hU₀qs u).PerfectObjectsDescend :=
  (D.restrictTo hU₀ hU₀qc hU₀qs u).perfectObjectsDescend_of_isAffineSpace
    (D.chartsBounded_restrictTo hU₀ hU₀qc hU₀qs u hb)
    (D.isAffineSpace_restrictTo_base hU₀ hU₀qc hU₀qs u hU₀aff)

omit hU₀ hU₀qc hU₀qs u in
/-- **Perfect objects descend in Situation 09RH as soon as they descend for its restriction to
`X₀` itself**, the system `X_i ×_{X₀} X₀` with limit `X ×_{X₀} X₀`: the cartesian projections
`σ : X ×_{X₀} X₀ ⟶ X` and `τᵢ : X_i ×_{X₀} X₀ ⟶ X_i` are isomorphisms commuting with the
projections of the limits, and derived pullback along an isomorphism is an equivalence
(`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso`,
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackIdIso`). This is the last step of the
induction of Stacks 08GP in the proof of Stacks 09RJ, which proves the property for the
object `X₀` of `(X₀)_{spaces,étale}`. -/
theorem perfectObjectsDescend_of_restrictTo_id
    (h : (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
      (𝟙 _)).PerfectObjectsDescend) : D.PerfectObjectsDescend := by
  intro E hE
  let D' := D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
    (D.quasiSeparated D.base) (𝟙 _)
  let XA : AlgebraicSpaces B S hS := ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩
  let XA' : AlgebraicSpaces B S hS := ⟨D'.limitCone.pt, D'.limitAlgebraicSpace⟩
  have hσ : IsIso (pullback.fst (D.limitCone.π.app (op D.base)) (𝟙 (D.system.obj (op D.base)))) :=
    (IsPullback.of_hasPullback _ _).isIso_fst_of_isIso
  let σ : XA' ≅ XA := ObjectProperty.isoMk _
    (@asIso _ _ _ _ (pullback.fst (D.limitCone.π.app (op D.base)) (𝟙 (D.system.obj (op D.base))))
      hσ)
  obtain ⟨i, hi, E'ᵢ, hE'ᵢ, ⟨e'⟩⟩ := h _ (isPerfect_derivedPullback_spacesEtaleModelHom σ.hom E hE)
  let XiA : AlgebraicSpaces B S hS := ⟨D.system.obj (op i.1), D.algebraicSpace i.1⟩
  let XiA' : AlgebraicSpaces B S hS := ⟨D'.system.obj (op i), D'.algebraicSpace i⟩
  have hτ : IsIso (pullback.fst (D.system.map (homOfLE i.2).op) (𝟙 (D.system.obj (op D.base)))) :=
    (IsPullback.of_hasPullback _ _).isIso_fst_of_isIso
  let τ : XiA' ≅ XiA := ObjectProperty.isoMk _
    (@asIso _ _ _ _ (pullback.fst (D.system.map (homOfLE i.2).op) (𝟙 (D.system.obj (op D.base))))
      hτ)
  let π : XA ⟶ XiA := ObjectProperty.homMk (D.limitCone.π.app (op i.1))
  let π' : XA' ⟶ XiA' := ObjectProperty.homMk (D'.limitCone.π.app (op i))
  have hsq : π' ≫ τ.hom = σ.hom ≫ π :=
    ObjectProperty.hom_ext _ (by
      exact baseChangeOverMap_fst B S hS (D.limitCone.π.app (op D.base))
        ((laterStagesToBaseStage D).app (op i)) ((laterStages D).limitCone.π.app (op i))
        (limitCone_π_comp_laterStagesToBaseStage D (op i)) (𝟙 _))
  have hsq' : π ≫ τ.inv = σ.inv ≫ π' := by
    rw [Iso.comp_inv_eq, Category.assoc, hsq, Iso.inv_hom_id_assoc]
  let L := fun {Y Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z) =>
    derivedPullback (spacesEtaleModelHom B S hS k)
  refine ⟨i.1, i.2, (L τ.inv).obj E'ᵢ,
    isPerfect_derivedPullback_spacesEtaleModelHom τ.inv E'ᵢ hE'ᵢ, ⟨?_⟩⟩
  exact (spacesEtaleModelDerivedPullbackCompIso B S hS π τ.inv).app E'ᵢ ≪≫
    eqToIso (congrArg (fun k => (L k).obj E'ᵢ) hsq') ≪≫
    ((spacesEtaleModelDerivedPullbackCompIso B S hS σ.inv π').app E'ᵢ).symm ≪≫
    (L σ.inv).mapIso e' ≪≫
    (spacesEtaleModelDerivedPullbackCompIso B S hS σ.inv σ.hom).app E ≪≫
    eqToIso (congrArg (fun k => (L k).obj E) σ.inv_hom_id) ≪≫
    (spacesEtaleModelDerivedPullbackIdIso B S hS XA).app E

end AlgebraicGeometry.Space.DescentSituation

end
