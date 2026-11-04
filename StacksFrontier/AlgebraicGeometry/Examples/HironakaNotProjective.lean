module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaThreefold
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaConicChart
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaNotProjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.InvertibleFibreEulerConstant
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerSumUnionTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjPointOfRingHom
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Basic

/-!
# Hironaka's morphism is not projective, granted the facts about the local model

Hironaka's threefold `f : V ⟶ Y = ℙ³_k` (`Stacks.Examples.HironakaThreefold.hironakaMorphism`)
blows up the conics `C` and `D` in the two orders over `Y - {Q}` and `Y - {P}`. On each of the
two affine charts `D₊(X₀) ∋ P` and `D₊(X₁) ∋ Q` the pair of centres is the same pair of ideals
`I = (x, y)`, `J = (x - y², z)` of `A = k[x, y, z]`
(`Stacks.Examples.HironakaConicChart`), so over each chart `f` is the **model tower**
`T = strictTower I J ⟶ Spec A`: blow up `I`, then the strict transform of `V(J)`. This file
reduces the non-projectivity of `f` to a precisely stated list of facts about `T` alone, the
structure `Stacks.Examples.HironakaNotProjective.ModelFacts`, and proves the reduction.

## The facts about the model

For every invertible module `ℋ` on the source of `T` (each `χ` is
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.eulerSum` of a restriction of `ℋ`):

* (nodal) the fibre `T_O` over the origin is the scheme-theoretic union `V(I_A) ∪ V(I_B)` of two
  closed subschemes meeting in one `k`-rational point, with `A = V(I_A) ≅ ℙ¹_k` over `k`;
* (family over `V(I)`) `χ(ℋ|T_c) = χ(ℋ|T_O)` for every `k`-point `c = (0, 0, c₂)` of `V(I)`:
  `T ×_A V(I) ⟶ V(I)` is a proper flat family over a connected base;
* (family over `V(J)`) `χ(ℋ|T_d) = χ(ℋ|B)` for every `k`-point `d = (t², t, 0)`, `t ≠ 0`, of
  `V(J)`, where `B = V(I_B)`: over `V(J) - {O}` the tower is the blow-up of `V(J)`, whose fibres
  are the fibres of the exceptional `ℙ¹`-bundle `E₂ ⟶ V(J')`, and `B` is its fibre over the point
  `o'` above `O`.

## The argument

The point `c₀ = [1 : 1 : 1 : 0]` of `C` is the model point `(0, 0, 1)` of the chart at `P`, which
lies on `V(I) = C`, and the model point `(1, 1, 0)` of the chart at `Q`, which lies on
`V(J) = C`; the point `d₀ = [1 : 1 : 0 : 1]` of `D` is `(1, 1, 0)` at `P` and `(0, 0, 1)` at `Q`.
For an invertible `ℋ` on `V`, let `ℋ_P`, `ℋ_Q` be its restrictions to the two copies of the
model. Reading the fibre `V_{c₀}` in the two charts,

`χ(ℋ_P|T_O) = χ(ℋ|V_{c₀}) = χ(ℋ_Q|B)`,  and likewise  `χ(ℋ_P|B) = χ(ℋ|V_{d₀}) = χ(ℋ_Q|T_O)`.

The nodal decomposition gives `χ(ℋ_P|T_O) + 1 = χ(ℋ_P|A) + χ(ℋ_P|B)` and the same for `ℋ_Q`, so
`χ(ℋ_P|A) + χ(ℋ_Q|A) = 2`, where `A` sits in the fibre of `f` over `P` and over `Q`. Since an
ample invertible module on `ℙ¹_k` has `χ ≥ 2`, `f` is not projective
(`Stacks.Examples.HironakaNotProjective.not_isProjective_of_eulerSum_add_eq_two`).

## Main definitions

* `Stacks.Examples.HironakaNotProjective.modelTower`: the model tower `T ⟶ Spec k[x, y, z]`.
* `Stacks.Examples.HironakaNotProjective.towerToVP`, `...towerToVQ`: the two open immersions of
  the source of `T` into `V`, over the charts `chartP`, `chartQ`.
* `Stacks.Examples.HironakaNotProjective.ModelFacts`: the facts about the model.

## Main results

* `Stacks.Examples.HironakaNotProjective.isPullback_towerToVP`, `...isPullback_towerToVQ`:
  over each chart, `f` is the model tower, as a cartesian square.
* `Stacks.Examples.HironakaNotProjective.modelKPoint_chartP_eq_chartQ_c₀`,
  `...modelKPoint_chartP_eq_chartQ_d₀`: the `k`-points `c₀`, `d₀` read in the two charts, as
  equal morphisms `Spec k ⟶ Y`.
* `Stacks.Examples.HironakaNotProjective.not_isProjective_hironakaMorphism_of_modelFacts`.
* `exists_proper_locallyProjective_not_projective_of_modelFacts` and
  `exists_proper_locallyProjective_not_projective_of_forall_modelFacts` (same namespace): granted
  the model facts over one field (resp. every field),
  Hironaka's example is a proper, locally projective, non-projective morphism to a quasi-compact
  quasi-separated scheme (the body of
  `Stacks.Examples.ProjectivityNotLocalOnBase.ProperLocallyProjectiveNotProjective`).

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [H, Example B.3.4.1]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
open AlgebraicGeometry.TwoStepTower
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff setOneHom)
open Stacks.Examples.HironakaConicIdealSheaf Stacks.Examples.HironakaThreefold
  Stacks.Examples.HironakaConicChart
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Examples.HironakaNotProjective

variable (k : Type u) [Field k]

/-! ### The model tower and its two copies in `V` -/

/-- The source of the model tower: `Bl_{I} Spec k[x, y, z]` blown up again in the strict
transform of `V(J)`, for `I = (x, y)`, `J = (x - y², z)`. -/
abbrev modelSpace : Scheme.{u} :=
  blowUp (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))

/-- **The model tower** `T ⟶ Spec k[x, y, z]`: blow up `I = (x, y)`, then the strict transform
of `V(J)`, `J = (x - y², z)`. -/
abbrev modelTower : modelSpace k ⟶ Spec (CommRingCat.of (ModelRing k)) :=
  strictTower (modelIdealSheafI k) (modelIdealSheafJ k)

/-- Over the chart `D₊(X₀)`, Hironaka's morphism is the model tower. -/
theorem exists_isPullback_modelTower_chartP :
    ∃ t : modelSpace k ⟶ hironakaThreefold k,
      IsPullback (modelTower k) t (chartP k) (hironakaMorphism k) := by
  have h := exists_isPullback_strictTower (chartPAwayQ k)
    ((idealSheafC k).comap (opensAwayQ k).ι) ((idealSheafD k).comap (opensAwayQ k).ι)
  rw [comap_comap_idealSheafC_chartPAwayQ, comap_comap_idealSheafD_chartPAwayQ] at h
  obtain ⟨t, T⟩ := h
  have T' := T.paste_vert (isPullback_awayQ k)
  rw [chartPAwayQ_ι] at T'
  exact ⟨_, T'⟩

/-- Over the chart `D₊(X₁)`, Hironaka's morphism is the model tower: there the first centre is
`D` and the second `C`, which the chart takes to `I` and `J`. -/
theorem exists_isPullback_modelTower_chartQ :
    ∃ t : modelSpace k ⟶ hironakaThreefold k,
      IsPullback (modelTower k) t (chartQ k) (hironakaMorphism k) := by
  have h := exists_isPullback_strictTower (chartQAwayP k)
    ((idealSheafD k).comap (opensAwayP k).ι) ((idealSheafC k).comap (opensAwayP k).ι)
  rw [comap_comap_idealSheafD_chartQAwayP, comap_comap_idealSheafC_chartQAwayP] at h
  obtain ⟨t, T⟩ := h
  have T' := T.paste_vert (isPullback_awayP k)
  rw [chartQAwayP_ι] at T'
  exact ⟨_, T'⟩

/-- The copy of the model over the chart `D₊(X₀)` inside `V`. -/
def towerToVP : modelSpace k ⟶ hironakaThreefold k :=
  (exists_isPullback_modelTower_chartP k).choose

/-- The copy of the model over the chart `D₊(X₁)` inside `V`. -/
def towerToVQ : modelSpace k ⟶ hironakaThreefold k :=
  (exists_isPullback_modelTower_chartQ k).choose

/-- **Over `D₊(X₀)`, `f` is the model tower**, as a cartesian square. -/
theorem isPullback_towerToVP :
    IsPullback (modelTower k) (towerToVP k) (chartP k) (hironakaMorphism k) :=
  (exists_isPullback_modelTower_chartP k).choose_spec

/-- **Over `D₊(X₁)`, `f` is the model tower**, as a cartesian square. -/
theorem isPullback_towerToVQ :
    IsPullback (modelTower k) (towerToVQ k) (chartQ k) (hironakaMorphism k) :=
  (exists_isPullback_modelTower_chartQ k).choose_spec

/-! ### The facts about the model -/

/-- **The facts about the model tower that Hironaka's argument needs.** `ModelFacts k` holds
when there are

* a fibre square `IsPullback qO gO (modelTower k) (modelKPoint k 0)` (the fibre `T_O` of the
  model tower over the origin `x = y = z = 0`),
* ideal sheaves `IA`, `IB` on `T_O` with `IA ⊓ IB = ⊥` (`T_O` is the union of `V(IA)` and
  `V(IB)`) whose intersection `V(IA ⊔ IB)` is a `k`-rational point,
* an isomorphism `eA` over `k` of `V(IA)` with `ℙ¹_k`,

such that, for every invertible module `H` on the source of the model tower,

* (`famI`) at every `k`-point `c = (0, 0, c₂)` of `V(I)`, the fibre of the tower has the same
  Euler characteristic of `H` as `T_O`;
* (`famJ`) at every `k`-point `d = (t², t, 0)`, `t ≠ 0`, of `V(J)`, the fibre of the tower has
  the same Euler characteristic of `H` as `V(IB)`.

The constructor `ModelFacts.intro` takes these data and facts in this order. -/
inductive ModelFacts : Prop where
  | intro (ZO : Scheme.{u}) (qO : ZO ⟶ modelSpace k) (gO : ZO ⟶ Spec (.of k))
      (isPullback : IsPullback qO gO (modelTower k) (modelKPoint k 0))
      (IA IB : ZO.IdealSheafData) (inf_eq_bot : IA ⊓ IB = ⊥)
      (isIso_sup : IsIso ((IA ⊔ IB).subschemeι ≫ gO))
      (eA : IA.subscheme ≅ AlgebraicGeometry.Proj (polyGrading k 1))
      (eA_hom : eA.hom ≫ projToSpecCoeff k 1 = IA.subschemeι ≫ gO)
      (famI : ∀ (H : (modelSpace k).Modules)
        [SheafOfModules.IsInvertible (modelSpace k).presheaf (modelSpace k).ringCatSheaf.2 H]
        (c : Fin 3 → k), c 0 = 0 → c 1 = 0 →
        ∀ {Z : Scheme.{u}} (q : Z ⟶ modelSpace k) (g : Z ⟶ Spec (.of k)),
          IsPullback q g (modelTower k) (modelKPoint k c) →
          eulerSum k g ((Scheme.Modules.pullback q).obj H) =
            eulerSum k gO ((Scheme.Modules.pullback qO).obj H))
      (famJ : ∀ (H : (modelSpace k).Modules)
        [SheafOfModules.IsInvertible (modelSpace k).presheaf (modelSpace k).ringCatSheaf.2 H]
        (d : Fin 3 → k), d 0 = d 1 ^ 2 → d 2 = 0 → d 1 ≠ 0 →
        ∀ {Z : Scheme.{u}} (q : Z ⟶ modelSpace k) (g : Z ⟶ Spec (.of k)),
          IsPullback q g (modelTower k) (modelKPoint k d) →
          eulerSum k g ((Scheme.Modules.pullback q).obj H) =
            eulerSum k (IB.subschemeι ≫ gO) ((Scheme.Modules.pullback (IB.subschemeι ≫ qO)).obj H))

/-! ### The points `c₀` and `d₀` in the two charts -/

/-- The `k`-point of the model at `c`, followed by the chart `D₊(X₀)`, is the `k`-point of `ℙ³`
with homogeneous coordinates `(1, c₀ + c₂², c₂, c₁)`. -/
theorem modelKPoint_comp_chartP (c : Fin 3 → k) (p : Fin 4 → k) (h0 : p 0 = 1)
    (h1 : p 1 = c 0 + c 2 ^ 2) (h2 : p 2 = c 2) (h3 : p 3 = c 1)
    (hu : IsUnit (MvPolynomial.eval p (X 0 : MvPolynomial (Fin 4) k))) :
    modelKPoint k c ≫ chartP k = Stacks.ProjPoint.point (homogeneousSubmodule (Fin 4) k)
      (MvPolynomial.eval p) (X 0) (X_mem_one k 0) one_pos hu := by
  have hring : (MvPolynomial.eval c).comp (chartRingEquivP k).symm.toRingHom =
      Stacks.ProjPoint.awayEval (homogeneousSubmodule (Fin 4) k) (MvPolynomial.eval p) (X 0)
        hu := by
    ext x
    obtain ⟨n, a, ha, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (homogeneousSubmodule (Fin 4) k) (X_mem_one k 0) x
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      chartRingEquivP_symm_mk, Stacks.ProjPoint.awayEval_mk]
    have hunit : hu.unit = 1 := Units.ext (by simp [h0])
    rw [hunit, inv_one, one_pow, Units.val_one, mul_one]
    have hcomp : (MvPolynomial.eval c).comp ((ofChartP k).toRingHom.comp (setOneHom k 3 0)) =
        MvPolynomial.eval p := by
      refine MvPolynomial.ringHom_ext (fun r => by simp [setOneHom]) (fun i => ?_)
      fin_cases i <;> simp [setOneHom, ofChartP, h0, h1, h2, h3]
    exact DFunLike.congr_fun hcomp a
  rw [modelKPoint, chartP, Stacks.ProjPoint.point, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, hring]

/-- The `k`-point of the model at `c`, followed by the chart `D₊(X₁)`, is the `k`-point of `ℙ³`
with homogeneous coordinates `(c₀ + c₂², 1, c₁, c₂)`. -/
theorem modelKPoint_comp_chartQ (c : Fin 3 → k) (p : Fin 4 → k) (h0 : p 0 = c 0 + c 2 ^ 2)
    (h1 : p 1 = 1) (h2 : p 2 = c 1) (h3 : p 3 = c 2)
    (hu : IsUnit (MvPolynomial.eval p (X 1 : MvPolynomial (Fin 4) k))) :
    modelKPoint k c ≫ chartQ k = Stacks.ProjPoint.point (homogeneousSubmodule (Fin 4) k)
      (MvPolynomial.eval p) (X 1) (X_mem_one k 1) one_pos hu := by
  have hring : (MvPolynomial.eval c).comp (chartRingEquivQ k).symm.toRingHom =
      Stacks.ProjPoint.awayEval (homogeneousSubmodule (Fin 4) k) (MvPolynomial.eval p) (X 1)
        hu := by
    ext x
    obtain ⟨n, a, ha, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (homogeneousSubmodule (Fin 4) k) (X_mem_one k 1) x
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      chartRingEquivQ_symm_mk, Stacks.ProjPoint.awayEval_mk]
    have hunit : hu.unit = 1 := Units.ext (by simp [h1])
    rw [hunit, inv_one, one_pow, Units.val_one, mul_one]
    have hcomp : (MvPolynomial.eval c).comp ((ofChartQ k).toRingHom.comp (setOneHom k 3 1)) =
        MvPolynomial.eval p := by
      refine MvPolynomial.ringHom_ext (fun r => by simp [setOneHom]) (fun i => ?_)
      fin_cases i <;> simp [setOneHom, ofChartQ, h0, h1, h2, h3]
    exact DFunLike.congr_fun hcomp a
  rw [modelKPoint, chartQ, Stacks.ProjPoint.point, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, hring]

/-- **The point `c₀ = [1 : 1 : 1 : 0]` in the two charts**: the model point `(0, 0, 1)` at `P`
and the model point `(1, 1, 0)` at `Q`, as equal morphisms `Spec k ⟶ ℙ³_k`. -/
theorem modelKPoint_chartP_eq_chartQ_c₀ :
    modelKPoint k ![0, 0, 1] ≫ chartP k = modelKPoint k ![1, 1, 0] ≫ chartQ k := by
  rw [modelKPoint_comp_chartP k _ ![1, 1, 1, 0] (by simp) (by simp) (by simp) (by simp)
      (by simp),
    modelKPoint_comp_chartQ k _ ![1, 1, 1, 0] (by simp) (by simp) (by simp) (by simp) (by simp)]
  exact Stacks.ProjPoint.point_indep _ _ _ _ _ _ _ _

/-- **The point `d₀ = [1 : 1 : 0 : 1]` in the two charts**: the model point `(1, 1, 0)` at `P`
and the model point `(0, 0, 1)` at `Q`, as equal morphisms `Spec k ⟶ ℙ³_k`. -/
theorem modelKPoint_chartP_eq_chartQ_d₀ :
    modelKPoint k ![1, 1, 0] ≫ chartP k = modelKPoint k ![0, 0, 1] ≫ chartQ k := by
  rw [modelKPoint_comp_chartP k _ ![1, 1, 0, 1] (by simp) (by simp) (by simp) (by simp)
      (by simp),
    modelKPoint_comp_chartQ k _ ![1, 1, 0, 1] (by simp) (by simp) (by simp) (by simp) (by simp)]
  exact Stacks.ProjPoint.point_indep _ _ _ _ _ _ _ _

/-! ### Fibres of `V` read in the two charts -/

/-- **A fibre of `V` read in the two charts.** If the `k`-point `c` of the model at `P` and the
`k`-point `c'` of the model at `Q` are the same point of `ℙ³_k`, then for any fibres of the model
tower over `c` and over `c'`, the restrictions of a module `ℋ` on `V` (through the two copies of
the model) have the same Euler characteristic: both fibres are the fibre of `f` over that point. -/
theorem eulerSum_fibre_chartP_eq_chartQ {c c' : Fin 3 → k}
    (hcc : modelKPoint k c ≫ chartP k = modelKPoint k c' ≫ chartQ k)
    (H : (hironakaThreefold k).Modules)
    {Z Z' : Scheme.{u}} (q : Z ⟶ modelSpace k) (g : Z ⟶ Spec (.of k))
    (sq : IsPullback q g (modelTower k) (modelKPoint k c))
    (q' : Z' ⟶ modelSpace k) (g' : Z' ⟶ Spec (.of k))
    (sq' : IsPullback q' g' (modelTower k) (modelKPoint k c')) :
    eulerSum k g ((Scheme.Modules.pullback q).obj
        ((Scheme.Modules.pullback (towerToVP k)).obj H)) =
      eulerSum k g' ((Scheme.Modules.pullback q').obj
        ((Scheme.Modules.pullback (towerToVQ k)).obj H)) := by
  have s₁ := sq.paste_horiz (isPullback_towerToVP k).flip
  have s₂ := sq'.paste_horiz (isPullback_towerToVQ k).flip
  rw [hcc] at s₁
  rw [← eulerSum_pullback_comp, ← eulerSum_pullback_comp]
  exact eulerSum_pullback_eq_of_iso k _ _ g g' (s₁.isoIsPullback _ _ s₂)
    (s₁.isoIsPullback_hom_fst _ _ s₂) (s₁.isoIsPullback_hom_snd _ _ s₂) H

/-- The Euler characteristic of a restriction along `j` of a pullback along a composite. -/
theorem eulerSum_pullback_pullback_comp {T Z W X : Scheme.{u}} (j : T ⟶ Z) (a : Z ⟶ W)
    (b : W ⟶ X) (g : T ⟶ Spec (.of k)) (H : X.Modules) :
    eulerSum k g ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback (a ≫ b)).obj H)) =
      eulerSum k g ((Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj H))) :=
  eulerSum_congr k g ((Scheme.Modules.pullback j).mapIso
    ((Scheme.Modules.pullbackComp a b).app H).symm)

/-! ### Non-projectivity -/

/-- **Hironaka's morphism is not projective, granted the facts about the model.** For an
invertible `ℋ` on `V` with restrictions `ℋ_P`, `ℋ_Q` to the two copies of the model, the fibre
over `c₀` gives `χ(ℋ_P|T_O) = χ(ℋ_Q|B)`, the fibre over `d₀` gives `χ(ℋ_P|B) = χ(ℋ_Q|T_O)`, and
the two nodal decompositions then give `χ(ℋ_P|A) + χ(ℋ_Q|A) = 2`, with `A ≅ ℙ¹_k` in the fibres
of `f` over `P` and over `Q`; this is impossible for an `ℋ` ample on the fibres. -/
theorem not_isProjective_hironakaMorphism_of_modelFacts (h : ModelFacts k) :
    ¬ IsProjective (hironakaMorphism k) := by
  obtain ⟨ZO, qO, gO, sqO, IA, IB, hIAB, hpt, eA, heA, famI, famJ⟩ := h
  have sqP := sqO.paste_horiz (isPullback_towerToVP k).flip
  have sqQ := sqO.paste_horiz (isPullback_towerToVQ k).flip
  have : IsProper gO := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsProper) sqP (isProper_hironakaMorphism k)
  refine not_isProjective_of_eulerSum_add_eq_two (hironakaMorphism k) k sqP sqQ
    IA.subschemeι IA.subschemeι eA heA eA heA ?_
  intro H _
  rw [eulerSum_pullback_pullback_comp, eulerSum_pullback_pullback_comp]
  -- the restrictions of `H` to the two copies of the model
  have hP : SheafOfModules.IsInvertible (modelSpace k).presheaf (modelSpace k).ringCatSheaf.2
      ((Scheme.Modules.pullback (towerToVP k)).obj H) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  have hQ : SheafOfModules.IsInvertible (modelSpace k).presheaf (modelSpace k).ringCatSheaf.2
      ((Scheme.Modules.pullback (towerToVQ k)).obj H) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  have : SheafOfModules.IsInvertible ZO.presheaf ZO.ringCatSheaf.2
      ((Scheme.Modules.pullback qO).obj ((Scheme.Modules.pullback (towerToVP k)).obj H)) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  have : SheafOfModules.IsInvertible ZO.presheaf ZO.ringCatSheaf.2
      ((Scheme.Modules.pullback qO).obj ((Scheme.Modules.pullback (towerToVQ k)).obj H)) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  -- the nodal decompositions of the fibres over `P` and over `Q`
  have nP := EulerSumUnionTwist.eulerSum_add_one_of_inf_eq_bot_of_isIso_sup k gO
    ((Scheme.Modules.pullback qO).obj ((Scheme.Modules.pullback (towerToVP k)).obj H))
    IA IB hIAB hpt
  have nQ := EulerSumUnionTwist.eulerSum_add_one_of_inf_eq_bot_of_isIso_sup k gO
    ((Scheme.Modules.pullback qO).obj ((Scheme.Modules.pullback (towerToVQ k)).obj H))
    IA IB hIAB hpt
  have bP := eulerSum_pullback_comp k IB.subschemeι qO (IB.subschemeι ≫ gO)
    ((Scheme.Modules.pullback (towerToVP k)).obj H)
  have bQ := eulerSum_pullback_comp k IB.subschemeι qO (IB.subschemeι ≫ gO)
    ((Scheme.Modules.pullback (towerToVQ k)).obj H)
  -- the fibre over `c₀`
  have s₁ := IsPullback.of_hasPullback (modelTower k) (modelKPoint k ![0, 0, 1])
  have s₂ := IsPullback.of_hasPullback (modelTower k) (modelKPoint k ![1, 1, 0])
  have c₁ := famI ((Scheme.Modules.pullback (towerToVP k)).obj H) ![0, 0, 1] (by simp)
    (by simp) _ _ s₁
  have c₂ := famJ ((Scheme.Modules.pullback (towerToVQ k)).obj H) ![1, 1, 0] (by simp)
    (by simp) (by simp) _ _ s₂
  have c₃ := eulerSum_fibre_chartP_eq_chartQ k (modelKPoint_chartP_eq_chartQ_c₀ k) H _ _ s₁ _ _ s₂
  -- the fibre over `d₀`
  have d₁ := famJ ((Scheme.Modules.pullback (towerToVP k)).obj H) ![1, 1, 0] (by simp)
    (by simp) (by simp) _ _ s₂
  have d₂ := famI ((Scheme.Modules.pullback (towerToVQ k)).obj H) ![0, 0, 1] (by simp)
    (by simp) _ _ s₁
  have d₃ := eulerSum_fibre_chartP_eq_chartQ k (modelKPoint_chartP_eq_chartQ_d₀ k) H _ _ s₂ _ _ s₁
  omega

/-- **Hironaka's example, granted the facts about the model over one field.** If `ModelFacts k`
holds for a field `k`, Hironaka's morphism `V ⟶ ℙ³_k` is a proper, Zariski-locally projective,
non-projective morphism to a quasi-compact quasi-separated scheme. The conclusion is the body of
`Stacks.Examples.ProjectivityNotLocalOnBase.ProperLocallyProjectiveNotProjective`, unfolded (that
file imports this one). -/
theorem exists_proper_locallyProjective_not_projective_of_modelFacts (h : ModelFacts k) :
    ∃ (V Y : Scheme.{u}) (f : V ⟶ Y), CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
      IsProper f ∧ IsLocallyProjective f ∧ ¬ IsProjective f :=
  ⟨_, _, hironakaMorphism k, inferInstance, inferInstance, isProper_hironakaMorphism k,
    isLocallyProjective_hironakaMorphism k, not_isProjective_hironakaMorphism_of_modelFacts k h⟩

/-- **Hironaka's example, granted the facts about the model over every field**, applied to the
field `ULift (ZMod 2)` of `Type u`. -/
theorem exists_proper_locallyProjective_not_projective_of_forall_modelFacts
    (h : ∀ (k : Type u) [Field k], ModelFacts k) :
    ∃ (V Y : Scheme.{u}) (f : V ⟶ Y), CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
      IsProper f ∧ IsLocallyProjective f ∧ ¬ IsProjective f :=
  exists_proper_locallyProjective_not_projective_of_modelFacts (ULift.{u} (ZMod 2)) (h _)

end Stacks.Examples.HironakaNotProjective

end
