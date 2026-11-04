module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.Uniqueness
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.BaseChangeTwistLowCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.PicardDescent
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.GlobalGeneration
public import StacksFrontier.AlgebraicGeometry.Morphisms.UnitPushforwardFlatBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The contraction of all rational tails commutes with extension of the ground field

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, with
at-worst-nodal singularities and of genus at least one, and let `c : X ⟶ Y` be a chain of
contractions of rational tails after which none are left. For a field extension `K/k` the base
change `c_K : X_K ⟶ Y_K` is, up to a unique isomorphism under `X_K`, the contraction of all
rational tails of `X_K`. This is the base change statement of [Stacks, Tag 0E3L].

## Main results

* `AlgebraicGeometry.invertibleCurveDegree_pullback_nonneg_of_isGeneratedByGlobalSections`: an
  invertible module some positive power of which is globally generated pulls back to a module of
  nonnegative degree on a proper integral curve.
* `AlgebraicGeometry.forall_not_isRationalTail_baseChange`: a nodal curve of positive genus
  without rational tails has none after extension of the ground field.
* `AlgebraicGeometry.comp_eq_of_isContractionOfRationalTail_baseChange` and
  `AlgebraicGeometry.IsIteratedContractionOfRationalTails.exists_comp_eq_baseChange`: a morphism
  from `X_K` onto a nodal curve of positive genus without rational tails, with `𝒪_Z = d_*𝒪_{X_K}`,
  factors through the base change of every chain of contractions of rational tails of `X`.
* `AlgebraicGeometry.IsIteratedContractionOfRationalTails.existsUnique_iso_baseChange`:
  [Stacks, Tag 0E3L], compatibility with base field extensions.

## Implementation notes

The source deduces the base change statement from [Stacks, Tag 0E3I] with details omitted. Here
the contraction `d : X_K ⟶ Z` of all rational tails of `X_K` factors through `c_K`, step by step
along the chain, because each step contracts `C_K`, a disjoint union of rational tails of `X_K`
([Stacks, Tag 0E3I]), each of which `d` maps to a point. Conversely `c_K` factors through `d`,
since `Y_K` has no rational tails, its dualizing sheaf being the pullback of `ω_Y`
([Stacks, Tag 0E32]), which has nonnegative degree on every curve mapping to `Y`
([Stacks, Tag 0E3K]), while a rational tail has negative degree ([Stacks, Tag 0E63]).

## References

* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
* [Stacks Project, Tag 0E3I](https://stacks.math.columbia.edu/tag/0E3I)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **A globally generated power of an invertible module pulls back to nonnegative degree.** Let
`g : C ⟶ Y` be a morphism from a proper integral scheme of dimension at most one over `k`, and
`ℒ` an invertible `𝒪_Y`-module with `ℒ^{⊗ n}` globally generated for some `n ≥ 1`. Then
`g^*ℒ^{⊗ n}` is globally generated, so has a nonzero global section, and
`n · deg(g^*ℒ) = deg(g^*ℒ^{⊗ n}) ≥ 0` ([Stacks, Tag 0B40]). -/
theorem invertibleCurveDegree_pullback_nonneg_of_isGeneratedByGlobalSections (k : Type u)
    [Field k] {C Y : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1) (g : C ⟶ Y) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (n : ℕ) (hn : 0 < n)
    (hL : SheafOfModules.IsGeneratedByGlobalSections
      (tensorPower Y.presheaf Y.ringCatSheaf.2 L n)) :
    letI : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
        ((Scheme.Modules.pullback g).obj L) :=
      Stacks.Modules.isInvertible_pullback g _
    0 ≤ invertibleCurveDegree k f hdim ((Scheme.Modules.pullback g).obj L) := by
  let : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj L) :=
    Stacks.Modules.isInvertible_pullback g _
  let Ln := tensorPower Y.presheaf Y.ringCatSheaf.2 L (n : ℤ)
  have hLn : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property Ln :=
    Scheme.Modules.isInvertible_tensorPower Y L n
  let : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj Ln) :=
    Stacks.Modules.isInvertible_pullback g _
  have : Stacks.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj Ln) :=
    Stacks.ProjectionFormula.isInvertible_schemeModulesPullback g Ln
  obtain ⟨σ⟩ := hL
  let σ' := Stacks.AlgebraicGeometry.FlatBaseChange.pullbackGeneratingSections g Ln σ
  obtain ⟨i, hi⟩ := exists_ne_zero_of_generatingSections ((Scheme.Modules.pullback g).obj Ln)
    inferInstance σ'
  have h0 := invertibleCurveDegree_nonneg_of_eval_top_ne_zero k f hdim
    ((Scheme.Modules.pullback g).obj Ln) _ hi
  have h1 : invertibleCurveDegree k f hdim ((Scheme.Modules.pullback g).obj Ln) =
      n * invertibleCurveDegree k f hdim ((Scheme.Modules.pullback g).obj L) :=
    invertibleCurveDegree_pullback_tensorPower g f hdim L n
  rw [h1] at h0
  exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast hn)

/-- **The base change of a proper nodal curve with `H⁰(X, 𝒪_X) = k` is again one**, of the same
dimension. -/
private theorem baseChange_curve_facts (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
    (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    IsProper (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
        (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop) ∧
      topologicalKrullDim
        (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) = 1 ∧
      letI : (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over (Spec (.of K)) :=
        ⟨pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
      Stacks.Curves.HasAtWorstNodalSingularities K
        (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) := by
  have hpb : IsPullback (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) fX
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := IsPullback.of_hasPullback _ _
  refine ⟨MorphismProperty.of_isPullback hpb inferInstance,
    isIso_globalSections_baseChange k K _ _ fX hpb,
    by rw [topologicalKrullDim_baseChange k K _ _ fX hpb, hdim], ?_⟩
  let : X.Over (Spec (.of k)) := ⟨fX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType fX)
  exact Stacks.Curves.hasAtWorstNodalSingularities_baseChange k K X
    (equidimensional_of_isIso_globalSections_of_dimension_one k fX hdim) hdim hnodal

/-- A scheme locally of finite type over a field with at worst nodal singularities is reduced. -/
private theorem isReduced_of_nodal_over (K : Type u) [Field K] {Z : Scheme.{u}}
    (fZ : Z ⟶ Spec (.of K)) [LocallyOfFiniteType fZ]
    (h : letI : Z.Over (Spec (.of K)) := ⟨fZ⟩
      Stacks.Curves.HasAtWorstNodalSingularities K Z) : IsReduced Z := by
  let : Z.Over (Spec (.of K)) := ⟨fZ⟩
  have : LocallyOfFiniteType (Z ↘ Spec (.of K)) := inferInstanceAs (LocallyOfFiniteType fZ)
  exact Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities K _ h

/-- **A nodal curve of positive genus without rational tails has none after extension of the
ground field.** Let `Y` be a proper scheme of dimension one over `k` with `H⁰(Y, 𝒪_Y) = k`, at
worst nodal, of genus `g ≥ 1` and without rational tails, and let `K/k` be a field extension. A
rational tail `D` of `Y_K` would have `deg(ω_{Y_K}|_D) < 0` ([Stacks, Tag 0E63]). But
`ω_{Y_K} = pr^*ω_Y` ([Stacks, Tag 0E32]), and `ω_Y ≅ 𝒪_Y` if `g = 1` while `ω_Y^{⊗ 2}` is globally
generated if `g ≥ 2` ([Stacks, Tag 0E3K]), so `ω_{Y_K}|_D` has nonnegative degree. -/
theorem forall_not_isRationalTail_baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) [IsProper fY] (hdim : topologicalKrullDim Y = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop)]
    (hnodal : letI : Y.Over (Spec (.of k)) := ⟨fY⟩
      Stacks.Curves.HasAtWorstNodalSingularities k Y)
    (htail : ∀ C : Y.IdealSheafData, ¬ @IsRationalTail k _ Y ⟨fY⟩ C) (hgenus : 1 ≤ genus fY) :
    ∀ D : (pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IdealSheafData,
      ¬ @IsRationalTail K _ (pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        ⟨pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩ D := by
  set g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  intro D hD
  have hpb : IsPullback (pullback.fst fY g) (pullback.snd fY g) fY g :=
    IsPullback.of_hasPullback fY g
  let : Y.Over (Spec (.of k)) := ⟨fY⟩
  let : (pullback fY g).Over (Spec (.of K)) := ⟨pullback.snd fY g⟩
  have : IsProper (Y ↘ Spec (.of k)) := inferInstanceAs (IsProper fY)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop))
  obtain ⟨_, _, hdimK, hnodalK⟩ := baseChange_curve_facts k K fY hdim hnodal
  have : IsProper (pullback fY g ↘ Spec (.of K)) :=
    inferInstanceAs (IsProper (pullback.snd fY g))
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (pullback fY g ↘ Spec (.of K)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (pullback.snd fY g).appTop))
  have hneg := invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail
    hdimK hnodalK D hD
  have hDdim := Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail K
    (pullback fY g) hdimK D hD
  have : IsIntegral D.subscheme := hD.isIntegral
  have := connectedSpace_of_isIso_globalSections k fY
  have := connectedSpace_of_isIso_globalSections K (pullback fY g ↘ Spec (.of K))
  let hω : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField fY) :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
  let hωK := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K
    (pullback fY g) hdimK hnodalK
  let := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback D.subschemeι
    (Stacks.Duality.dualizingSheafOverField (pullback fY g ↘ Spec (.of K))) hωK
  -- `ω_{Y_K}|_D ≅ (D ⟶ Y)^* ω_Y`
  let e : (Scheme.Modules.pullback D.subschemeι).obj
      (Stacks.Duality.dualizingSheafOverField (pullback fY g ↘ Spec (.of K))) ≅
      (Scheme.Modules.pullback (D.subschemeι ≫ pullback.fst fY g)).obj
        (Stacks.Duality.dualizingSheafOverField fY) :=
    (Scheme.Modules.pullback D.subschemeι).mapIso
        (Stacks.Duality.dualizingSheafOverFieldBaseChangeIso fY (pullback.fst fY g)
          (pullback.snd fY g) hpb).symm ≪≫
      (Scheme.Modules.pullbackComp D.subschemeι (pullback.fst fY g)).app _
  let : SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (D.subschemeι ≫ pullback.fst fY g)).obj
        (Stacks.Duality.dualizingSheafOverField fY)) :=
    Stacks.Modules.isInvertible_pullback _ _
  have hdeg := invertibleCurveDegree_eq_of_iso (k := K)
    (D.subschemeι ≫ (pullback fY g ↘ Spec (.of K))) hDdim.le e
  have hnn : 0 ≤ invertibleCurveDegree K (D.subschemeι ≫ (pullback fY g ↘ Spec (.of K)))
      hDdim.le ((Scheme.Modules.pullback (D.subschemeι ≫ pullback.fst fY g)).obj
        (Stacks.Duality.dualizingSheafOverField fY)) := by
    by_cases h1 : genus fY = 1
    · obtain ⟨φ⟩ : Nonempty (Stacks.Duality.dualizingSheafOverField fY ≅
          SheafOfModules.unit Y.ringCatSheaf) :=
        nonempty_dualizingSheafOverField_iso_unit_of_forall_not_isRationalTail hdim hnodal htail h1
      let ψ : (Scheme.Modules.pullback (D.subschemeι ≫ pullback.fst fY g)).obj
          (Stacks.Duality.dualizingSheafOverField fY) ≅ SheafOfModules.unit
              D.subscheme.ringCatSheaf :=
        (Scheme.Modules.pullback (D.subschemeι ≫ pullback.fst fY g)).mapIso φ ≪≫
          Scheme.Modules.pullbackUnitIso _
      rw [invertibleCurveDegree_eq_of_iso (k := K)
        (D.subschemeι ≫ (pullback fY g ↘ Spec (.of K))) hDdim.le ψ,
        invertibleCurveDegree_unit_eq_zero]
    · exact invertibleCurveDegree_pullback_nonneg_of_isGeneratedByGlobalSections K _ hDdim.le
        (D.subschemeι ≫ pullback.fst fY g) _ 2 (by norm_num) <|
        isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField_of_forall_not_isRationalTail
          hdim hnodal htail (show 2 ≤ genus fY by omega) 2 le_rfl
  rw [← hdeg] at hnn
  exact lt_irrefl _ (hnn.trans_lt hneg)

/-- **The base change of a morphism over the base is a pullback of it**: for `c : X ⟶ Y` over `S`
and `g : T ⟶ S`, the square formed by `c_T : X_T ⟶ Y_T`, `c` and the two projections is
cartesian. -/
theorem isPullback_map_baseChange {X Y S T : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) (g : T ⟶ S)
    (c : X ⟶ Y) (h : c ≫ fY = fX) :
    IsPullback (pullback.fst fX g)
      (pullback.map fX g fY g c (𝟙 T) (𝟙 S) (by rw [Category.comp_id, h]) (by simp)) c
      (pullback.fst fY g) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback fY g)
  have : pullback.map fX g fY g c (𝟙 T) (𝟙 S) (by rw [Category.comp_id, h]) (by simp) ≫
      pullback.snd fY g = pullback.snd fX g := by simp
  rw [this, h]
  exact IsPullback.of_hasPullback fX g

/-- **After extension of the ground field, a morphism onto a curve of positive genus without
rational tails factors through the base change of a contraction of a rational tail.** Let `X` be a
proper nodal curve over `k` with `H⁰(X, 𝒪_X) = k`, `C` a rational tail with contraction
`cont : X ⟶ X'` and `ι : X' ⟶ X` the inclusion of the closure of the complement, and `d : X_K ⟶ Z`
a morphism over `K` with `𝒪_Z = d_*𝒪_{X_K}` onto a nodal curve of positive genus without rational
tails. Then `d = cont_K ≫ ι_K ≫ d`.

By [Stacks, Tag 0E3I] `C_K` is a disjoint union of rational tails `Dᵢ` of `X_K`, and `X_K` is
covered by `X'_K` and the `Dᵢ`. On `X'_K` both sides agree as `ι ≫ cont = 𝟙`. Each `Dᵢ` is mapped
to a point by `d`
(`AlgebraicGeometry.subsingleton_range_of_isRationalTail_of_forall_not_isRationalTail`) and by
`cont_K`, which sends `C_K` into the finite scheme `Spec(K ⊗_k Γ(C, 𝒪_C))`; so both sides factor
through the canonical map of `Dᵢ` to its attaching point, which `ι_K ≫ cont_K` fixes, lying on
`X'_K`. As `X_K` is reduced and `Z` separated, the two morphisms agree. -/
theorem comp_eq_of_isContractionOfRationalTail_baseChange (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
    (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData}
    (hC : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      IsRationalTail k X C)
    {cont : X ⟶ complementaryCurve C}
    (hc : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      IsContractionOfRationalTail hC cont)
    (hbase : cont ≫ complementaryCurveι C ≫ fX = fX)
    {Z : Scheme.{u}} {fZ : Z ⟶ Spec (.of K)} [IsProper fZ] (hZdim : topologicalKrullDim Z = 1)
    (hZnodal : letI : Z.Over (Spec (.of K)) := ⟨fZ⟩
      Stacks.Curves.HasAtWorstNodalSingularities K Z)
    (hZtail : ∀ D : Z.IdealSheafData, ¬ @IsRationalTail K _ Z ⟨fZ⟩ D) (hZgenus : 1 ≤ genus fZ)
    {d : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Z}
    (hd : d ≫ fZ = pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hdO : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom)) :
    pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) (complementaryCurveι C ≫ fX)
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) cont (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hbase]) (by simp) ≫
      pullback.map (complementaryCurveι C ≫ fX) (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) (complementaryCurveι C) (𝟙 _) (𝟙 _)
        (by simp) (by simp) ≫ d = d := by
  set ι := complementaryCurveι C with hι
  set contK := pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) (ι ≫ fX)
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) cont (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hbase]) (by simp) with hcontK
  set ιK := pullback.map (ι ≫ fX) (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) ι (𝟙 _) (𝟙 _) (by simp) (by simp) with hιK
  set pX := pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) with hpX
  let : X.Over (Spec (.of k)) := ⟨fX⟩
  let : (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over (Spec (.of K)) :=
    ⟨pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper fX)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
  have hpb : IsPullback pX (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) fX
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := IsPullback.of_hasPullback _ _
  obtain ⟨_, _, hdimK, hnodalK⟩ := baseChange_curve_facts k K fX hdim hnodal
  have : IsProper (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘
      Spec (.of K)) :=
    inferInstanceAs (IsProper (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop))
  have : IsReduced (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
    isReduced_of_nodal_over K _ hnodalK
  -- [Stacks, Tag 0E3I]: `C_K` is a disjoint union of rational tails `Dⱼ`
  obtain ⟨J, hJ, D, hD, e, he⟩ : ∃ (J : Type u) (_ : Finite J)
      (D : J → (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IdealSheafData)
      (_ : ∀ j, IsRationalTail K (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (D j))
      (e : (∐ fun j ↦ (D j).subscheme) ≅ (C.comap pX).subscheme),
      e.hom ≫ (C.comap pX).subschemeι = Sigma.desc fun j ↦ (D j).subschemeι :=
    exists_iso_sigma_isRationalTail_baseChange k K X hdim hnodal C hC
  have hDι (j : J) : Sigma.ι (fun j ↦ (D j).subscheme) j ≫ e.hom ≫ (C.comap pX).subschemeι =
      (D j).subschemeι :=
    (congrArg (fun m ↦ Sigma.ι (fun j ↦ (D j).subscheme) j ≫ m) he).trans
      (Sigma.ι_desc _ _)
  -- `ι_K ≫ cont_K = 𝟙`
  have hιc : ιK ≫ contK = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [hιK, hcontK, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.id_comp]
      rw [hι, hc.1, Category.comp_id]
    · simp [hιK, hcontK]
  -- the ranges of `ι`, `ι_K` and `C_K`
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian fX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  have : IsNoetherian X := ⟨⟩
  have hrangeι : Set.range ι = closure ((C.support : Set X)ᶜ) := by
    show Set.range (complementaryCurveIdeal C).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    show ((Scheme.Opens.ι C.support.compl).ker.support : Set X) = _
    rw [Scheme.Hom.support_ker, Scheme.Opens.range_ι]
    rfl
  have hrangeιK : Set.range ιK = pX ⁻¹' Set.range ι := by
    rw [hιK, Scheme.Pullback.range_map]
    simp [hpX]
  have hrangeCK : Set.range (C.comap pX).subschemeι = pX ⁻¹' (C.support : Set X) := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, Set.range_eq_univ.mpr (C.comapIso pX).hom.surjective, Set.image_univ,
      Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι]
  have hmemD : ∀ z ∈ Set.range (C.comap pX).subschemeι, ∃ j, z ∈ Set.range (D j).subschemeι := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk (fun j ↦ (D j).subscheme)).surjective (e.inv w)
    refine ⟨j, y, ?_⟩
    rw [← hDι j, Scheme.Hom.comp_apply, ← sigmaMk_mk, hy, Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply e.inv e.hom, e.inv_hom_id]
    rfl
  have hdisj : ∀ i j : J, i ≠ j → ∀ y y', (D i).subschemeι y ≠ (D j).subschemeι y' := by
    intro i j hij y y' hyy
    rw [← hDι i, ← hDι j, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hyy
    have h1 := e.hom.homeomorph.injective ((C.comap pX).subschemeι.isClosedEmbedding.injective hyy)
    rw [sigmaι_eq_iff] at h1
    exact hij (Sigma.mk.inj_iff.mp h1).1
  have hrangeι' : Set.range ι = ((complementaryCurveIdeal C).support : Set X) := by
    show Set.range (complementaryCurveIdeal C).subschemeι = _
    exact Scheme.IdealSheafData.range_subschemeι _
  have : IsLocallyNoetherian (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd fX (Spec.map (CommRingCat.ofHom
        (algebraMap k K))))
  have : CompactSpace (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd fX (Spec.map (CommRingCat.ofHom
        (algebraMap k K))))
  have : IsNoetherian (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}) := ⟨⟩
  -- the attaching point of `Dⱼ` lies over `X'`
  have hattach (j : J) : pX ((D j).subschemeι (hD j).attachingPoint) ∈ Set.range ι := by
    rw [hrangeι]
    set x' := (D j).subschemeι (hD j).attachingPoint with hx'
    have hx'J : x' ∈ ((complementaryCurveIdeal (D j)).support : Set _) := by
      have hmem : x' ∈ ((intersectionWithComplementaryCurveIdeal (D j)).support : Set _) := by
        rw [(hD j).intersectionWithComplementaryCurveIdeal_eq,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl
      rw [Scheme.IdealSheafData.support_sup] at hmem
      exact hmem.2
    have hJcl : ((complementaryCurveIdeal (D j)).support : Set _) =
        closure (((D j).support : Set (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            : Scheme.{u})))ᶜ := by
      show ((Scheme.Opens.ι (D j).support.compl).ker.support :
        Set (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) = _
      rw [Scheme.Hom.support_ker, Scheme.Opens.range_ι]
      rfl
    rw [hJcl] at hx'J
    by_contra hnot
    set F : Set (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
      ⋃ i ∈ ({i | i ≠ j} : Set J), Set.range (D i).subschemeι with hF
    have hFcl : IsClosed F := (Set.toFinite _).isClosed_biUnion fun i _ ↦
      (D i).subschemeι.isClosedEmbedding.isClosed_range
    have hx'F : x' ∉ F := by
      rw [hF, Set.mem_iUnion₂]
      rintro ⟨i, hi, y, hy⟩
      exact hdisj i j hi y _ hy
    have hUo : IsOpen (pX ⁻¹' (closure ((C.support : Set X)ᶜ))ᶜ) :=
      isClosed_closure.isOpen_compl.preimage pX.continuous
    obtain ⟨z, ⟨hzU, hzF⟩, hzD⟩ :=
      mem_closure_iff.mp hx'J _ (hUo.inter hFcl.isOpen_compl) ⟨hnot, hx'F⟩
    have hzC : pX z ∈ (C.support : Set X) := by
      by_contra h
      exact hzU (subset_closure h)
    have hzCK : z ∈ Set.range (C.comap pX).subschemeι := by rwa [hrangeCK]
    obtain ⟨i, hi⟩ := hmemD z hzCK
    by_cases hij : i = j
    · subst hij
      exact hzD (by rwa [← Scheme.IdealSheafData.range_subschemeι])
    · exact hzF (Set.mem_biUnion hij hi)
  -- `X'_K` and `C_K` cover `X_K`
  let cov := coprod.desc ιK (C.comap pX).subschemeι
  have : Surjective cov := ⟨fun z ↦ by
    rcases (Stacks.Curves.StableModel.support_union_support_complementaryCurveIdeal C ▸
        Set.mem_univ (pX z) :
      pX z ∈ (C.support : Set X) ∪ (complementaryCurveIdeal C).support) with h | h
    · obtain ⟨w, hw⟩ : z ∈ Set.range (C.comap pX).subschemeι := by rwa [hrangeCK]
      refine ⟨(coprod.inr : (C.comap pX).subscheme ⟶ _ ⨿ (C.comap pX).subscheme) w, ?_⟩
      rw [← Scheme.Hom.comp_apply, coprod.inr_desc]
      exact hw
    · obtain ⟨w, hw⟩ : z ∈ Set.range ιK := by
        rw [hrangeιK]
        show pX z ∈ Set.range ι
        rwa [hrangeι']
      refine ⟨(coprod.inl : pullback (ι ≫ fX) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
        _ ⨿ _) w, ?_⟩
      rw [← Scheme.Hom.comp_apply, coprod.inl_desc]
      exact hw⟩
  -- `d` contracts each `Dⱼ`
  have hDcon (j : J) : (Set.range ((D j).subschemeι ≫ d)).Subsingleton :=
    subsingleton_range_of_isRationalTail_of_forall_not_isRationalTail K hdimK hnodalK (hD j) hd
      hdO hZdim hZnodal hZtail hZgenus
  -- `cont_K` maps `C_K` into the finite scheme `Spec (K ⊗_k Γ(C, 𝒪_C))`
  have : IsProper (C.subschemeι ≫ fX) := inferInstance
  let A := Γ(C.subscheme, ⊤)
  let : Algebra k A := ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ fX).appTop).hom.toAlgebra
  have : Module.Finite k A := by
    have := forall_finiteDimensional_cohomologyOverField_unit k (C.subschemeι ≫ fX) 0
    exact Module.Finite.equiv (cohomologyOverFieldZeroIsoSections k (C.subschemeι ≫ fX)
      (SheafOfModules.unit C.subscheme.ringCatSheaf)).toLinearEquiv
  have hfΓ : C.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      C.subschemeι ≫ fX := by
    show C.subscheme.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
      (C.subschemeι ≫ fX).appTop) = C.subschemeι ≫ fX
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  obtain ⟨-, p, -, htail⟩ := hc
  have := hC.isIso_Γevaluation_attachingPoint
  let w : Spec (.of A) ⟶ complementaryCurve C :=
    Spec.map (inv (C.subscheme.Γevaluation hC.attachingPoint)) ≫ p
  have hw : C.subschemeι ≫ cont = C.subscheme.toSpecΓ ≫ w := by
    rw [htail]
    simp only [canonicalMapToAttachingPoint, Category.assoc, w]
  have hwb : w ≫ ι ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    apply ext_of_isAffine
    have h1 : C.subscheme.toSpecΓ ≫ w ≫ ι ≫ fX =
        C.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
      rw [hfΓ, ← Category.assoc, ← hw, Category.assoc, hbase]
    have h2 := congrArg Scheme.Hom.appTop h1
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h2
    have : IsIso C.subscheme.toSpecΓ.appTop := by rw [Scheme.toSpecΓ_appTop]; infer_instance
    exact (cancel_mono _).1 h2
  let qC : (C.comap pX).subscheme ⟶ C.subscheme :=
    (C.comapIso pX).hom ≫ pullback.snd pX C.subschemeι
  have hqC : (C.comap pX).subschemeι ≫ pX = qC ≫ C.subschemeι := by
    simp only [qC, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  let u : (C.comap pX).subscheme ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (Spec.map (CommRingCat.ofHom
          (algebraMap k A))) :=
    pullback.lift ((C.comap pX).subschemeι ≫ pullback.snd fX (Spec.map (CommRingCat.ofHom
        (algebraMap k K)))) (qC ≫ C.subscheme.toSpecΓ)
      (by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, hqC]
        simp only [Category.assoc]
        exact congrArg (qC ≫ ·) hfΓ.symm)
  let v : pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (Spec.map (CommRingCat.ofHom
      (algebraMap k A))) ⟶
      pullback (ι ≫ fX) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    pullback.lift (pullback.snd _ _ ≫ w) (pullback.fst _ _)
      (by rw [Category.assoc, hwb, ← pullback.condition])
  have huv : (C.comap pX).subschemeι ≫ contK = u ≫ v := by
    apply pullback.hom_ext
    · simp only [hcontK, u, v, Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc]
      rw [← Category.assoc, hqC, Category.assoc, hw]
    · simp only [hcontK, u, v, Category.assoc, pullback.lift_snd, Category.comp_id]
      exact (pullback.lift_fst _ _ _).symm
  have : Module.Finite K (K ⊗[k] A) := inferInstance
  have : IsArtinianRing (K ⊗[k] A) := IsArtinianRing.of_finite K _
  have : T2Space (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) : Scheme.{u}) :=
    (pullbackSpecIso k K A).hom.homeomorph.isEmbedding.t2Space
  have hconK (j : J) : (Set.range ((D j).subschemeι ≫ contK)).Subsingleton := by
    have : IsIntegral (D j).subscheme := (hD j).isIntegral
    rw [← hDι j, Category.assoc, Category.assoc, huv]
    have hirr : IsPreirreducible
        (Set.range (Sigma.ι (fun j ↦ (D j).subscheme) j ≫ e.hom ≫ u)) := by
      rw [← Set.image_univ]
      exact ((IrreducibleSpace.isIrreducible_univ _).image _
        (Scheme.Hom.continuous _).continuousOn).isPreirreducible
    have : Set.range (Sigma.ι (fun j ↦ (D j).subscheme) j ≫ e.hom ≫ u ≫ v) =
        v '' Set.range (Sigma.ι (fun j ↦ (D j).subscheme) j ≫ e.hom ≫ u) := by
      rw [← Set.range_comp]
      rfl
    rw [this]
    exact hirr.subsingleton.image _
  -- `ι_K ≫ cont_K` fixes the attaching point of each `Dⱼ`
  have : IsClosedImmersion ιK :=
    MorphismProperty.of_isPullback
      (isPullback_map_baseChange (ι ≫ fX) fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ι rfl)
      inferInstance
  have hfix (j : J) : (D j).subscheme.fromSpecResidueField (hD j).attachingPoint ≫
      (D j).subschemeι ≫ contK ≫ ιK =
        (D j).subscheme.fromSpecResidueField (hD j).attachingPoint ≫ (D j).subschemeι := by
    obtain ⟨a, ha⟩ := Stacks.Curves.exists_comp_eq_of_range_subset_of_isClosedImmersion ιK
      ((D j).subscheme.fromSpecResidueField (hD j).attachingPoint ≫ (D j).subschemeι) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Hom.comp_apply]
        have hy : (D j).subscheme.fromSpecResidueField (hD j).attachingPoint y =
            (hD j).attachingPoint := by
          have := Set.mem_range_self (f := (D j).subscheme.fromSpecResidueField
            (hD j).attachingPoint) y
          rwa [Scheme.range_fromSpecResidueField] at this
        rw [hy, hrangeιK]
        exact hattach j)
    rw [← Category.assoc, ← ha, Category.assoc, ← Category.assoc ιK contK, hιc,
      Category.id_comp]
  have hDj (j : J) : (D j).subschemeι ≫ contK ≫ ιK ≫ d = (D j).subschemeι ≫ d := by
    obtain ⟨q, hq⟩ := Stacks.Curves.StableModel.exists_comp_eq_canonicalMapToAttachingPoint K _
      (hD j) d (hDcon j)
    obtain ⟨q', hq'⟩ := Stacks.Curves.StableModel.exists_comp_eq_canonicalMapToAttachingPoint K _
      (hD j) (contK ≫ ιK ≫ d) (by
        have : Set.range ((D j).subschemeι ≫ contK ≫ ιK ≫ d) =
            (ιK ≫ d) '' Set.range ((D j).subschemeι ≫ contK) := by
          rw [← Set.range_comp]
          rfl
        rw [this]
        exact (hconK j).image _)
    have hret : (D j).subscheme.fromSpecResidueField (hD j).attachingPoint ≫
        canonicalMapToAttachingPoint (hD j) =
          𝟙 (Spec ((D j).subscheme.residueField (hD j).attachingPoint)) := by
      simp only [canonicalMapToAttachingPoint, Scheme.fromSpecResidueField,
        Category.assoc, Scheme.fromSpecStalk_toSpecΓ_assoc,
        ← AlgebraicGeometry.Spec.map_comp]
      rw [← AlgebraicGeometry.Spec.map_id, AlgebraicGeometry.Spec.map_inj]
      simp [Scheme.Γevaluation, Scheme.evaluation]
    have e1 : (D j).subscheme.fromSpecResidueField (hD j).attachingPoint ≫
        (D j).subschemeι ≫ d = q := by
      rw [hq, ← Category.assoc, hret, Category.id_comp]
    have e2 : (D j).subscheme.fromSpecResidueField (hD j).attachingPoint ≫
        (D j).subschemeι ≫ contK ≫ ιK ≫ d = q' := by
      rw [hq', ← Category.assoc, hret, Category.id_comp]
    rw [hq', hq, ← e1, ← e2]
    congr 1
    simp only [← Category.assoc] at hfix ⊢
    rw [hfix j]
  -- conclusion
  refine ext_of_isDominant_of_isSeparated fZ ?_ cov ?_
  · simp [hd, hcontK, hιK]
  · apply coprod.hom_ext
    · simp only [cov, coprod.inl_desc_assoc]
      rw [← Category.assoc ιK contK, hιc, Category.id_comp]
    · simp only [cov, coprod.inr_desc_assoc]
      rw [← cancel_epi e.hom]
      apply Sigma.hom_ext
      intro j
      have h1 := hDj j
      rw [← hDι j] at h1
      simpa only [Category.assoc] using h1

/-- **After extension of the ground field, a morphism onto a curve of positive genus without
rational tails factors through the base change of every chain of contractions of rational
tails.** Let `c : X ⟶ Y` be a chain of contractions of rational tails of a proper nodal curve `X`
over `k` with `H⁰(X, 𝒪_X) = k`, and `d : X_K ⟶ Z` a morphism over `K` with `𝒪_Z = d_*𝒪_{X_K}`
onto a nodal curve of positive genus without rational tails. Then `d = c_K ≫ φ` for some
`φ : Y_K ⟶ Z`: by induction along the chain, using
`AlgebraicGeometry.comp_eq_of_isContractionOfRationalTail_baseChange` at each step and the
stability of `𝒪_Y = c_*𝒪_X` under flat base change. -/
theorem IsIteratedContractionOfRationalTails.exists_comp_eq_baseChange (k K : Type u) [Field k]
    [Field K] [Algebra k K] {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    {c : X ⟶ Y} (hseq : IsIteratedContractionOfRationalTails k fX fY c) (hproper : IsProper fX)
    (hdim : topologicalKrullDim X = 1) (hglob : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    {Z : Scheme.{u}} {fZ : Z ⟶ Spec (.of K)} [IsProper fZ] (hZdim : topologicalKrullDim Z = 1)
    (hZnodal : letI : Z.Over (Spec (.of K)) := ⟨fZ⟩
      Stacks.Curves.HasAtWorstNodalSingularities K Z)
    (hZtail : ∀ D : Z.IdealSheafData, ¬ @IsRationalTail K _ Z ⟨fZ⟩ D) (hZgenus : 1 ≤ genus fZ)
    {d : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Z} (hd : d ≫ fZ =
        pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hdO : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom)) :
    ∃ φ : pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Z,
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map
          (CommRingCat.ofHom (algebraMap k K))) c (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hseq.comp_structureMap]) (by simp) ≫ φ = d := by
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  induction hseq with
  | identity X fX => exact ⟨d, by simp⟩
  | @step X₀ X₁ X₂ f₀ f₁ f₂ c₁ d₁ C hC e hc hbase hd₁ ih =>
    let : X₀.Over (Spec (.of k)) := ⟨f₀⟩
    have : IsProper f₀ := hproper
    have := hglob
    -- the next curve in the chain
    have h1 : IsIteratedContractionOfRationalTails k f₀ f₁ (c₁ ≫ 𝟙 X₁) :=
      .step C hC e hc hbase (.identity X₁ f₁)
    have hp₁ : IsProper f₁ := h1.isProper_target hdim hnodal
    have hdim₁ := h1.topologicalKrullDim_target hdim hnodal
    have hglob₁ := h1.isIso_globalSections_target hdim hnodal
    have hnodal₁ := h1.hasAtWorstNodalSingularities_target hdim hnodal
    have hO₁ := h1.isIso_unitToPushforwardObjUnit hdim hnodal
    rw [Category.comp_id] at hO₁
    have : IsProper (c₁ ≫ f₁) := hbase ▸ hproper
    have : IsProper c₁ := IsProper.of_comp c₁ f₁
    -- the contraction `c₁ ≫ e.inv` and its base change
    have hef : e.hom ≫ f₁ = complementaryCurveι C ≫ f₀ :=
      iso_hom_comp_structureMorphism hC e hc hbase
    have hb' : (c₁ ≫ e.inv) ≫ complementaryCurveι C ≫ f₀ = f₀ := by
      rw [← hef, Category.assoc, Iso.inv_hom_id_assoc, hbase]
    have hstep := comp_eq_of_isContractionOfRationalTail_baseChange k K f₀ hdim hnodal hC hc hb'
      hZdim hZnodal hZtail hZgenus hd hdO
    let eK := pullback.map f₁ (Spec.map (CommRingCat.ofHom (algebraMap k K))) (complementaryCurveι
        C ≫ f₀) (Spec.map (CommRingCat.ofHom (algebraMap k K))) e.inv (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← hef, Iso.inv_hom_id_assoc]) (by simp)
    let c₁K := pullback.map f₀ (Spec.map (CommRingCat.ofHom (algebraMap k K))) f₁ (Spec.map
        (CommRingCat.ofHom (algebraMap k K))) c₁ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hbase])
      (by simp)
    let d' : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Z := eK ≫ pullback.map
        (complementaryCurveι C ≫ f₀) (Spec.map (CommRingCat.ofHom (algebraMap k K))) f₀ (Spec.map
        (CommRingCat.ofHom (algebraMap k K)))
      (complementaryCurveι C) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ d
    have hdd : c₁K ≫ d' = d := by
      rw [← hstep]
      simp only [d', ← Category.assoc]
      congr 2
      apply pullback.hom_ext <;> simp [eK, c₁K]
    have : Flat (pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback f₁ (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))).flip hflat
    have hc₁KO : IsIso (SheafOfModules.unitToPushforwardObjUnit c₁K.toRingCatSheafHom) :=
      Scheme.Hom.isIso_unitToPushforwardObjUnit_of_isPullback c₁
        (isPullback_map_baseChange f₀ f₁ (Spec.map (CommRingCat.ofHom (algebraMap k K))) c₁ hbase)
            hO₁
    have hd'O : IsIso (SheafOfModules.unitToPushforwardObjUnit d'.toRingCatSheafHom) :=
      Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_of_comp c₁K d' hc₁KO
        (hdd ▸ hdO)
    have hd' : d' ≫ fZ = pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
      have h2 : c₁K ≫ d' ≫ fZ = c₁K ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap k
          K))) := by
        rw [← Category.assoc, hdd, hd]
        simp [c₁K]
      have : IsIso c₁K.appTop :=
        Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c₁K hc₁KO ⊤
      apply ext_of_isAffine
      have h3 := congrArg Scheme.Hom.appTop h2
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h3
      exact (cancel_mono _).1 h3
    obtain ⟨φ, hφ⟩ := ih hp₁ hdim₁ hglob₁ hnodal₁ hd' hd'O
    refine ⟨φ, ?_⟩
    rw [← hdd, ← hφ, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [c₁K]

/-- **Morphisms out of a reduced scheme over `S` into a separated `S`-scheme are determined after
a dominant morphism**: `c ≫ a = c ≫ b` gives `a = b`, first after composing with the separated
structure morphism `s`, whose target is separated, and then outright. -/
@[ega "I 7.2.2.1" "Base S separated", ega "IV 11.10.1" "(a) ⇒ (d), special case"]
theorem hom_ext_of_isDominant_of_isSeparated {W A B S : Scheme.{u}} [IsReduced A] [S.IsSeparated]
    (c : W ⟶ A) [IsDominant c] (s : B ⟶ S) [IsSeparated s] {a b : A ⟶ B} (h : c ≫ a = c ≫ b) :
    a = b :=
  ext_of_isDominant_of_isSeparated s
    (ext_of_isDominant c (by rw [← Category.assoc, ← Category.assoc, h])) c h

/-- **Stacks Project, Tag 0E3L, compatibility with extension of the ground field.** Let `X` be a
proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, at-worst-nodal singularities
and genus at least one, `c : X ⟶ Y` a chain of contractions of rational tails after which none
are left, and `K/k` a field extension. For every chain `d : X_K ⟶ Z` of contractions of rational
tails of `X_K` after which none are left, there is a unique isomorphism `e : Y_K ≅ Z` with
`c_K ≫ e = d`: the formation of the contraction of all rational tails commutes with the base
change to `K`.

`d` factors through `c_K`
(`AlgebraicGeometry.IsIteratedContractionOfRationalTails.exists_comp_eq_baseChange`, using
[Stacks, Tag 0E3I]). Conversely `Y_K` is a nodal curve of positive genus without rational tails
(`AlgebraicGeometry.forall_not_isRationalTail_baseChange`) and `𝒪_{Y_K} = (c_K)_*𝒪_{X_K}` by flat
base change, so `c_K` factors through `d`
(`IsIteratedContractionOfRationalTails.exists_comp_eq_of_forall_not_isRationalTail`).
The two factorizations are mutually inverse, `c_K` and `d` being dominant onto reduced curves. -/
@[stacks 0E3L "compatibility with base field extensions"]
theorem IsIteratedContractionOfRationalTails.existsUnique_iso_baseChange (k K : Type u) [Field k]
    [Field K] [Algebra k K] {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    {c : X ⟶ Y} [IsProper fX] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hgenus : 1 ≤ genus fX)
    (hseq : IsIteratedContractionOfRationalTails k fX fY c)
    (hterminal : ∀ C : Y.IdealSheafData, ¬ @IsRationalTail k _ Y ⟨fY⟩ C)
    {Z : Scheme.{u}} {fZ : Z ⟶ Spec (.of K)} {d : pullback fX (Spec.map (CommRingCat.ofHom
        (algebraMap k K))) ⟶ Z}
    (hd : IsIteratedContractionOfRationalTails K (pullback.snd fX (Spec.map (CommRingCat.ofHom
        (algebraMap k K)))) fZ d)
    (hdterminal : ∀ C : Z.IdealSheafData, ¬ @IsRationalTail K _ Z ⟨fZ⟩ C) :
    ∃! e : pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅ Z,
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map
          (CommRingCat.ofHom (algebraMap k K))) c (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hseq.comp_structureMap]) (by simp) ≫ e.hom = d := by
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hcomp := hseq.comp_structureMap
  -- `X_K`
  have hpbX : IsPullback (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) fX (Spec.map
      (CommRingCat.ofHom (algebraMap k K))) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨_, _, hdimK, hnodalK⟩ := baseChange_curve_facts k K fX hdim hnodal
  -- `Z`
  have : IsProper fZ := hd.isProper_target hdimK hnodalK
  have hZdim := hd.topologicalKrullDim_target hdimK hnodalK
  have hZnodal := hd.hasAtWorstNodalSingularities_target hdimK hnodalK
  have hZgenus : 1 ≤ genus fZ := by
    rwa [hd.genus_target hdimK hnodalK, genus_baseChange k K _ _ fX hpbX]
  have hdO := hd.isIso_unitToPushforwardObjUnit hdimK hnodalK
  -- `Y_K`
  have : IsProper fY := hseq.isProper_target hdim hnodal
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop) :=
    hseq.isIso_globalSections_target hdim hnodal
  have hYdim := hseq.topologicalKrullDim_target hdim hnodal
  have hYnodal := hseq.hasAtWorstNodalSingularities_target hdim hnodal
  have hYgenus : 1 ≤ genus fY := hgenus.trans_eq (hseq.genus_target hdim hnodal).symm
  have hpbY : IsPullback (pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))) fY (Spec.map
      (CommRingCat.ofHom (algebraMap k K))) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨_, _, hYKdim, hYKnodal⟩ :=
    baseChange_curve_facts k K fY hYdim hYnodal
  have hYKtail := forall_not_isRationalTail_baseChange k K fY hYdim hYnodal hterminal hYgenus
  have hYKgenus : 1 ≤ genus (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
    rwa [genus_baseChange k K _ _ fY hpbY]
  -- `c_K`
  set cK := pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map
      (CommRingCat.ofHom (algebraMap k K))) c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hcomp]) (by
      simp)
    with hcK
  have : IsProper (c ≫ fY) := hcomp ▸ inferInstance
  have : IsProper c := IsProper.of_comp c fY
  have : Flat (pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      MorphismProperty.of_isPullback hpbY.flip hflat
  have hcKO : IsIso (SheafOfModules.unitToPushforwardObjUnit cK.toRingCatSheafHom) :=
    Scheme.Hom.isIso_unitToPushforwardObjUnit_of_isPullback c
      (isPullback_map_baseChange fX fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) c hcomp)
          (hseq.isIso_unitToPushforwardObjUnit hdim hnodal)
  have hcKs : cK ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    simp [hcK]
  -- the two factorizations
  obtain ⟨φ, hφ⟩ := hseq.exists_comp_eq_baseChange k K inferInstance hdim inferInstance hnodal
    hZdim hZnodal hdterminal hZgenus hd.comp_structureMap hdO
  obtain ⟨ψ, hψ, -, -⟩ := hd.exists_comp_eq_of_forall_not_isRationalTail inferInstance hdimK
    inferInstance hnodalK hYKdim hYKnodal hYKtail hYKgenus hcKs hcKO
  have : IsReduced (pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
    isReduced_of_nodal_over K _ hYKnodal
  have : IsReduced Z := isReduced_of_nodal_over K fZ hZnodal
  have hφ' : cK ≫ φ = d := hφ
  have : IsDominant cK := cK.isDominant_of_isIso_unitToPushforwardObjUnit hcKO
  have : IsDominant d := d.isDominant_of_isIso_unitToPushforwardObjUnit hdO
  have h1 : φ ≫ ψ = 𝟙 _ := hom_ext_of_isDominant_of_isSeparated cK (pullback.snd fY (Spec.map
      (CommRingCat.ofHom (algebraMap k K))))
    (by rw [← Category.assoc, hφ', hψ, Category.comp_id])
  have h2 : ψ ≫ φ = 𝟙 _ := hom_ext_of_isDominant_of_isSeparated d fZ
    (by rw [← Category.assoc, hψ, hφ', Category.comp_id])
  exact ⟨⟨φ, ψ, h1, h2⟩, hφ, fun e he ↦ Iso.ext <| hom_ext_of_isDominant_of_isSeparated cK fZ
    ((show cK ≫ e.hom = d from he).trans hφ'.symm)⟩

end AlgebraicGeometry

end
