module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaNotProjective
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.CentreFamily
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.ExceptionalFamily
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.OriginFibre

/-!
# The Euler-characteristic relation `χ(ℋ_P|A) + χ(ℋ_Q|A) = 2`

Let `T ⟶ Spec k[x, y, z]` be the model tower of Hironaka's example
(`Stacks.Examples.HironakaNotProjective.modelTower`), let `T_O` be its fibre over the origin and
`A ⊆ T_O` the component isomorphic to `ℙ¹_k`. Suppose a morphism `f : V ⟶ Y` contains two copies
of the model tower, as cartesian squares over two morphisms `c_P, c_Q : Spec k[x, y, z] ⟶ Y`,
glued so that the model points `(0, 0, 1)` at `P` and `(1, 1, 0)` at `Q` are the same point of
`Y`, and likewise `(1, 1, 0)` at `P` and `(0, 0, 1)` at `Q`. Then for every invertible module
`ℋ` on `V`, with restrictions `ℋ_P`, `ℋ_Q` to the two copies of `A`,

`χ(ℋ_P|A) + χ(ℋ_Q|A) = 2`.

This is the argument of
`Stacks.Examples.HironakaNotProjective.not_isProjective_hironakaMorphism_of_modelFacts`, with
Hironaka's threefold, `ℙ³_k` and the two charts replaced by arbitrary data satisfying the same
two cartesian squares and the same two point identities, and with the facts about the model
supplied by `Stacks.Examples.HironakaLocalModel.modelFacts`. Reading the fibre of `f` over each
of the two glued points in the two charts gives `χ(ℋ_P|T_O) = χ(ℋ_Q|B)` and
`χ(ℋ_P|B) = χ(ℋ_Q|T_O)`, where `T_O = A ∪ B` is the nodal decomposition, and the two nodal
decompositions `χ(T_O) + 1 = χ(A) + χ(B)` give the relation.

The argument only uses `ℋ` along the family `T ×_{𝔸³} V(I)` over the line `V(I)`, along the
exceptional divisor `E₂ ⟶ V(J')` of the second blow-up, and along `T_O`, all of which lie over
`V(I) ∪ V(J)`. So the relation also holds for an invertible module defined only on an open of `V`
containing the images of these, which is how it is stated in
`Stacks.Examples.HironakaNotProjective.eulerSum_add_eq_two_of_opens_of_nodal`: the constancy of
`χ` in the two families is re-run there for the restriction of `ℋ` to each family.

## Main results

* `Stacks.Examples.HironakaNotProjective.eulerSum_fibre_eq_of_isPullback`: two fibres of a
  morphism `m` lying over the same point of `Y` through two cartesian squares give restrictions
  of a module with the same Euler characteristic.
* `Stacks.Examples.HironakaNotProjective.exists_eulerSum_add_eq_two`: the relation, for any two
  copies of the model tower glued as above.
* `Stacks.Examples.HironakaNotProjective.exists_eulerSum_add_eq_two_of_opens`: the relation for
  an invertible module on an open `W ⊆ V` containing the images of the part of the two copies of
  the model over `V(I) ∪ V(J)`; `exists_eulerSum_add_eq_two_and_of_opens` gives both forms with
  the same `T_O` and `A`.
* `Stacks.Examples.HironakaNotProjective.exists_eulerSum_towerToVP_add_towerToVQ_eq_two`: the
  relation for Hironaka's morphism itself.

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [H, Example B.3.4.1]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
open AlgebraicGeometry.TwoStepTower
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.Examples.HironakaThreefold Stacks.Examples.HironakaConicChart
open Stacks.Examples.HironakaLocalModel (centreIdeal curveIdeal)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Examples.HironakaNotProjective

variable (k : Type u) [Field k]

/-- **A fibre of `f` read in two cartesian squares.** Let `m : X ⟶ B` be the base change of
`f : V ⟶ Y` along both `cP` and `cQ` (through `tP` and `tQ`). If the `k`-points `y` and `y'` of
`B` map to the same point of `Y` under `cP` and `cQ`, then for any fibres of `m` over `y` and over
`y'`, the restrictions of a module `ℋ` on `V` (through `tP` and through `tQ`) have the same Euler
characteristic: both fibres are the fibre of `f` over that point. -/
theorem eulerSum_fibre_eq_of_isPullback {X B V Y : Scheme.{u}} (m : X ⟶ B) (f : V ⟶ Y)
    (cP cQ : B ⟶ Y) (tP tQ : X ⟶ V) (hP : IsPullback m tP cP f) (hQ : IsPullback m tQ cQ f)
    {y y' : Spec (.of k) ⟶ B} (hyy : y ≫ cP = y' ≫ cQ) (H : V.Modules)
    {Z Z' : Scheme.{u}} (q : Z ⟶ X) (g : Z ⟶ Spec (.of k)) (sq : IsPullback q g m y)
    (q' : Z' ⟶ X) (g' : Z' ⟶ Spec (.of k)) (sq' : IsPullback q' g' m y') :
    eulerSum k g ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback tP).obj H)) =
      eulerSum k g' ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback tQ).obj H)) := by
  have s₁ := sq.paste_horiz hP.flip
  have s₂ := sq'.paste_horiz hQ.flip
  rw [hyy] at s₁
  rw [← eulerSum_pullback_comp, ← eulerSum_pullback_comp]
  exact eulerSum_pullback_eq_of_iso k _ _ g g' (s₁.isoIsPullback _ _ s₂)
    (s₁.isoIsPullback_hom_fst _ _ s₂) (s₁.isoIsPullback_hom_snd _ _ s₂) H

/-- A morphism whose image lies in an open `W` factors through `W`. -/
theorem exists_comp_ι_eq_of_forall_mem {X V : Scheme.{u}} (W : V.Opens) (a : X ⟶ V)
    (h : ∀ x, a x ∈ W) : ∃ l : X ⟶ W.toScheme, l ≫ W.ι = a :=
  ⟨IsOpenImmersion.lift W.ι a (by rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact h x),
    IsOpenImmersion.lift_fac _ _ _⟩

/-- Two morphisms to an open `W` of `V` that agree after the inclusion into `V` and are related by
an isomorphism of their sources over `Spec k` restrict a module on `W` to modules with the same
Euler characteristic. -/
theorem eulerSum_pullback_eq_of_iso_of_comp_ι {Z Z' V : Scheme.{u}} {W : V.Opens}
    (a : Z ⟶ W.toScheme) (a' : Z' ⟶ W.toScheme) (g : Z ⟶ Spec (.of k)) (g' : Z' ⟶ Spec (.of k))
    (e : Z ≅ Z') (ha : e.hom ≫ a' ≫ W.ι = a ≫ W.ι) (hg : e.hom ≫ g' = g) (H : W.toScheme.Modules) :
    eulerSum k g ((Scheme.Modules.pullback a).obj H) =
      eulerSum k g' ((Scheme.Modules.pullback a').obj H) :=
  eulerSum_pullback_eq_of_iso k a a' g g' e
    (by rw [← cancel_mono W.ι, Category.assoc, ha]) hg H

/-! ### The model tower lies over `V(I) ∪ V(J)` along the two families -/

/-- The line `V(x, y) = Spec k[z]` lies in the first centre `V(I)`. -/
theorem lineι_mem_supportSet (y : Spec (CommRingCat.of (Polynomial k))) :
    HironakaLocalModel.lineι k y ∈ (modelIdealSheafI k).supportSet := by
  change HironakaLocalModel.lineι k y ∈ (centreIdeal k).supportSet
  rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support]
  refine (HironakaLocalModel.mem_support_idealSheafOf_iff k
    (HironakaLocalModel.centreRingIdeal k) _).mpr ?_
  rw [Ideal.span_le]
  rintro _ (rfl | rfl)
  · change HironakaLocalModel.lineMap k (MvPolynomial.X 0) ∈ y.asIdeal
    simp [HironakaLocalModel.lineMap]
  · change HironakaLocalModel.lineMap k (MvPolynomial.X 1) ∈ y.asIdeal
    simp [HironakaLocalModel.lineMap]

/-- The exceptional divisor `E₂` of the second blow-up lies over the second centre `V(J)`. -/
theorem modelTower_exceptional_mem_supportSet
    (x : exceptionalDivisor (strictCentre (centreIdeal k) (curveIdeal k))) :
    modelTower k ((exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k))).subschemeι x) ∈
      (modelIdealSheafJ k).supportSet := by
  have hw : blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k))
      ((exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k))).subschemeι x) ∈
        ((strictCentre (centreIdeal k) (curveIdeal k)).support :
          Set (blowUp (centreIdeal k))) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    refine ⟨Stacks.AlgebraicGeometry.exceptionalSubschemeMap
      (strictCentre (centreIdeal k) (curveIdeal k)) x, ?_⟩
    have h := Scheme.IdealSheafData.subschemeMap_subschemeι
      (exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k)))
      (strictCentre (centreIdeal k) (curveIdeal k))
      (blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k)))
      ((strictCentre (centreIdeal k) (curveIdeal k)).le_map_comap
        (blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k))))
    rw [← Scheme.Hom.comp_apply (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
      (strictCentre (centreIdeal k) (curveIdeal k))), h, Scheme.Hom.comp_apply]
  obtain ⟨y, hy⟩ := HironakaLocalModel.support_strictCentre_subset_range_chartι_one k hw
  have hy' : HironakaLocalModel.chartι k 1 y ∈
      (strictCentre (centreIdeal k) (curveIdeal k)).support := by
    rw [hy]
    exact hw
  rw [HironakaLocalModel.chartι_mem_support_strictCentre_iff,
    HironakaLocalModel.comap_chartι_one_strictCentre,
    HironakaLocalModel.mem_support_idealSheafOf_iff] at hy'
  change blowUpToBase (centreIdeal k) (blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k))
      ((exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k))).subschemeι x)) ∈
    (curveIdeal k).supportSet
  rw [← hy, ← Scheme.Hom.comp_apply (HironakaLocalModel.chartι k 1),
    HironakaLocalModel.chartι_comp_blowUpToBase,
    Scheme.IdealSheafData.mem_supportSet_iff_mem_support]
  refine (HironakaLocalModel.mem_support_idealSheafOf_iff k
    (HironakaLocalModel.curveRingIdeal k) _).mpr ?_
  rw [Ideal.span_le]
  rintro _ (rfl | rfl)
  · have h1 : (MvPolynomial.X 0 - MvPolynomial.X 1 : HironakaLocalModel.Ring3 k) ∈ y.asIdeal :=
      hy' (Ideal.subset_span (Set.mem_insert _ _))
    change HironakaLocalModel.chartHom k 1 (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2) ∈ y.asIdeal
    have : HironakaLocalModel.chartHom k 1 (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2) =
        (MvPolynomial.X 0 - MvPolynomial.X 1) * MvPolynomial.X 1 := by
      simp [HironakaLocalModel.chartHom_one_eq, sub_mul, pow_two]
    rw [this]
    exact Ideal.mul_mem_right _ _ h1
  · change HironakaLocalModel.chartHom k 1 (MvPolynomial.X 2) ∈ y.asIdeal
    simpa [HironakaLocalModel.chartHom_one_eq] using
      hy' (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

/-- A fibre of the model tower over a `k`-point `(t², t, 0)`, `t ≠ 0`, of `V(J) ∖ V(I)` is a
fibre of the exceptional family `E₂ ⟶ V(J')` of the second blow-up. -/
theorem exists_isPullback_exceptionalSubschemeMap_of_modelKPoint (d : Fin 3 → k)
    (hd0 : d 0 = d 1 ^ 2) (hd2 : d 2 = 0) (hd1 : d 1 ≠ 0) {F : Scheme.{u}}
    (q : F ⟶ blowUp (strictCentre (centreIdeal k) (curveIdeal k))) (g : F ⟶ Spec (.of k))
    (hq : IsPullback q g (strictTower (centreIdeal k) (curveIdeal k)) (modelKPoint k d)) :
    ∃ q₁ : F ⟶ exceptionalDivisor (strictCentre (centreIdeal k) (curveIdeal k)),
      q₁ ≫ (exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k))).subschemeι = q ∧
      IsPullback q₁ g (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
        (strictCentre (centreIdeal k) (curveIdeal k)))
        (HironakaLocalModel.strictLinePoint k (d 1)) := by
  have hq' := hq
  have hbot := HironakaLocalModel.isPullback_strictLinePoint_blowUpToBase k d hd0 hd2 hd1
  have hc : (q ≫ blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k))) ≫
      blowUpToBase (centreIdeal k) = g ≫ modelKPoint k d := by
    rw [Category.assoc]
    exact hq'.w
  have hw : q ≫ blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k)) =
      g ≫ HironakaLocalModel.strictLinePoint k (d 1) ≫
        (strictCentre (centreIdeal k) (curveIdeal k)).subschemeι := by
    have hl := hbot.lift_snd _ g hc
    have hf := hbot.lift_fst _ g hc
    rw [Category.comp_id] at hl
    rw [← hf, hl]
  have htop : IsPullback q g (blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k)))
      (HironakaLocalModel.strictLinePoint k (d 1) ≫
        (strictCentre (centreIdeal k) (curveIdeal k)).subschemeι) :=
    IsPullback.of_bot (by rw [Category.comp_id]; exact hq') hw hbot
  exact
    Stacks.AlgebraicGeometry.exists_isPullback_exceptionalSubschemeMap_of_isPullback_blowUpToBase
      _ _ htop

/-! ### The relation, localized to an open containing the two families -/

/-- **The Euler-characteristic relation for an invertible module on an open.** Let the fibre
`T_O` of the model tower over the origin be the union of `V(IA)` and `V(IB)` meeting in a
`k`-rational point, with `V(IB)` a fibre of the exceptional family `E₂ ⟶ V(J')` over a `k`-point
`o'`. Let `f : V ⟶ Y` be the model tower over `cP` (through `tP`) and over `cQ` (through `tQ`),
glued along the points `c₀`, `d₀` as in `exists_eulerSum_add_eq_two`, and let `W ⊆ V` be an open
containing the images under `tP` and `tQ` of the part of the model over `V(I) ∪ V(J)`. Then for
every invertible module `ℋ` on `W`, with `gP`, `gQ` the two maps `V(IA) ⟶ W`,
`χ(gP^*ℋ) + χ(gQ^*ℋ) = 2`. -/
theorem eulerSum_add_eq_two_of_opens_of_nodal {ZO : Scheme.{u}} (qO : ZO ⟶ modelSpace k)
    (gO : ZO ⟶ Spec (.of k)) (sqO : IsPullback qO gO (modelTower k) (modelKPoint k 0))
    (IA IB : ZO.IdealSheafData) (hinf : IA ⊓ IB = ⊥) (hsup : IsIso ((IA ⊔ IB).subschemeι ≫ gO))
    (o' : Spec (.of k) ⟶ (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k)).subscheme)
    (hB : ∀ {F' : Scheme.{u}}
      (q' : F' ⟶ exceptionalDivisor (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k)))
      (g' : F' ⟶ Spec (.of k)),
      IsPullback q' g' (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
        (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))) o' →
      ∃ e : IB.subscheme ≅ F',
        e.hom ≫ q' ≫ (exceptionalIdeal
          (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))).subschemeι =
            IB.subschemeι ≫ qO ∧
          e.hom ≫ g' = IB.subschemeι ≫ gO)
    {V Y : Scheme.{u}} (f : V ⟶ Y) (cP cQ : Spec (.of (ModelRing k)) ⟶ Y)
    (tP tQ : modelSpace k ⟶ V)
    (hsP : IsPullback (modelTower k) tP cP f) (hsQ : IsPullback (modelTower k) tQ cQ f)
    (hc : modelKPoint k ![0, 0, 1] ≫ cP = modelKPoint k ![1, 1, 0] ≫ cQ)
    (hd : modelKPoint k ![1, 1, 0] ≫ cP = modelKPoint k ![0, 0, 1] ≫ cQ)
    (W : V.Opens)
    (hWP : ∀ x : modelSpace k, modelTower k x ∈
      (modelIdealSheafI k).supportSet ∪ (modelIdealSheafJ k).supportSet → tP x ∈ W)
    (hWQ : ∀ x : modelSpace k, modelTower k x ∈
      (modelIdealSheafI k).supportSet ∪ (modelIdealSheafJ k).supportSet → tQ x ∈ W)
    (gP gQ : IA.subscheme ⟶ W.toScheme) (hgP : gP ≫ W.ι = IA.subschemeι ≫ qO ≫ tP)
    (hgQ : gQ ≫ W.ι = IA.subschemeι ≫ qO ≫ tQ)
    (H : W.toScheme.Modules)
    [SheafOfModules.IsInvertible W.toScheme.presheaf W.toScheme.ringCatSheaf.2 H] :
    eulerSum k (IA.subschemeι ≫ gO) ((Scheme.Modules.pullback gP).obj H) +
      eulerSum k (IA.subschemeι ≫ gO) ((Scheme.Modules.pullback gQ).obj H) = 2 := by
  have : IsProper gO := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsProper) sqO (HironakaLocalModel.isProper_strictTower k)
  -- the family over the line `V(I)` and the exceptional family over `V(J')`, mapped into `W`
  have hL : ∀ x : (pullback (strictTower (centreIdeal k) (curveIdeal k))
      (HironakaLocalModel.lineι k) : Scheme.{u}),
      modelTower k (pullback.fst (strictTower (centreIdeal k) (curveIdeal k))
        (HironakaLocalModel.lineι k) x) ∈
        (modelIdealSheafI k).supportSet ∪ (modelIdealSheafJ k).supportSet := fun x => by
    left
    change strictTower (centreIdeal k) (curveIdeal k)
      (pullback.fst (strictTower (centreIdeal k) (curveIdeal k)) (HironakaLocalModel.lineι k) x) ∈ _
    rw [← Scheme.Hom.comp_apply (pullback.fst (strictTower (centreIdeal k) (curveIdeal k))
      (HironakaLocalModel.lineι k)), pullback.condition, Scheme.Hom.comp_apply]
    exact lineι_mem_supportSet k _
  have hE : ∀ x : exceptionalDivisor (strictCentre (centreIdeal k) (curveIdeal k)),
      modelTower k ((exceptionalIdeal (strictCentre (centreIdeal k)
        (curveIdeal k))).subschemeι x) ∈
        (modelIdealSheafI k).supportSet ∪ (modelIdealSheafJ k).supportSet :=
    fun x => Or.inr (modelTower_exceptional_mem_supportSet k x)
  obtain ⟨lP, hlP⟩ := exists_comp_ι_eq_of_forall_mem W
    (pullback.fst (strictTower (centreIdeal k) (curveIdeal k))
      (HironakaLocalModel.lineι k) ≫ tP)
    (fun x => hWP _ (hL x))
  obtain ⟨lQ, hlQ⟩ := exists_comp_ι_eq_of_forall_mem W
    (pullback.fst (strictTower (centreIdeal k) (curveIdeal k))
      (HironakaLocalModel.lineι k) ≫ tQ)
    (fun x => hWQ _ (hL x))
  obtain ⟨eP, heP⟩ := exists_comp_ι_eq_of_forall_mem W
    ((exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k))).subschemeι ≫ tP)
    (fun x => hWP _ (hE x))
  obtain ⟨eQ, heQ⟩ := exists_comp_ι_eq_of_forall_mem W
    ((exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k))).subschemeι ≫ tQ)
    (fun x => hWQ _ (hE x))
  -- invertibility of the restrictions of `H`
  have iLP : SheafOfModules.IsInvertible
      (pullback (strictTower (centreIdeal k) (curveIdeal k))
        (HironakaLocalModel.lineι k)).presheaf
      (pullback (strictTower (centreIdeal k) (curveIdeal k))
        (HironakaLocalModel.lineι k)).ringCatSheaf.2
      ((Scheme.Modules.pullback lP).obj H) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  have iLQ : SheafOfModules.IsInvertible
      (pullback (strictTower (centreIdeal k) (curveIdeal k))
        (HironakaLocalModel.lineι k)).presheaf
      (pullback (strictTower (centreIdeal k) (curveIdeal k))
        (HironakaLocalModel.lineι k)).ringCatSheaf.2
      ((Scheme.Modules.pullback lQ).obj H) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  have iEP : SheafOfModules.IsInvertible
      (exceptionalDivisor (strictCentre (centreIdeal k) (curveIdeal k))).presheaf
      (exceptionalDivisor (strictCentre (centreIdeal k) (curveIdeal k))).ringCatSheaf.2
      ((Scheme.Modules.pullback eP).obj H) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  have iEQ : SheafOfModules.IsInvertible
      (exceptionalDivisor (strictCentre (centreIdeal k) (curveIdeal k))).presheaf
      (exceptionalDivisor (strictCentre (centreIdeal k) (curveIdeal k))).ringCatSheaf.2
      ((Scheme.Modules.pullback eQ).obj H) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  -- the family over the line is proper and flat over a connected base
  have := HironakaLocalModel.isProper_strictTower k
  have := HironakaLocalModel.flat_strictTower_line k
  have : PreconnectedSpace (Spec (CommRingCat.of (Polynomial k))) :=
    inferInstanceAs (PreconnectedSpace (PrimeSpectrum (Polynomial k)))
  -- the fibres: `T_O` over the origin, `Z₁` over `(0, 0, 1)`, `Z₂` over `(1, 1, 0)`
  obtain ⟨qOL, hqOL, sqOL⟩ := HironakaLocalModel.exists_isPullback_line k 0 rfl rfl qO gO sqO
  have s₁ := IsPullback.of_hasPullback (modelTower k) (modelKPoint k ![0, 0, 1])
  have s₂ := IsPullback.of_hasPullback (modelTower k) (modelKPoint k ![1, 1, 0])
  obtain ⟨q₁L, hq₁L, sq₁L⟩ := HironakaLocalModel.exists_isPullback_line k ![0, 0, 1]
    (by simp) (by simp) _ _ s₁
  obtain ⟨q₂E, hq₂E, sq₂E⟩ := exists_isPullback_exceptionalSubschemeMap_of_modelKPoint k
    ![1, 1, 0] (by simp) (by simp) (by simp) _ _ s₂
  have sqB := IsPullback.of_hasPullback (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
    (strictCentre (centreIdeal k) (curveIdeal k))) o'
  obtain ⟨eB, heB₁', heB₂⟩ := hB _ _ sqB
  have heB₁ : eB.hom ≫ pullback.fst (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
      (strictCentre (centreIdeal k) (curveIdeal k))) o' ≫
        (exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k))).subschemeι =
      IB.subschemeι ≫ qO := heB₁'
  -- the maps `gP`, `gQ` factor through the origin fibre
  have egP : gP = IA.subschemeι ≫ qOL ≫ lP := by
    rw [← cancel_mono W.ι, hgP]
    simp only [Category.assoc, hlP]
    exact congrArg (IA.subschemeι ≫ ·) ((reassoc_of% hqOL) tP).symm
  have egQ : gQ = IA.subschemeι ≫ qOL ≫ lQ := by
    rw [← cancel_mono W.ι, hgQ]
    simp only [Category.assoc, hlQ]
    exact congrArg (IA.subschemeι ≫ ·) ((reassoc_of% hqOL) tQ).symm
  rw [egP, egQ, eulerSum_pullback_comp, eulerSum_pullback_comp]
  have : SheafOfModules.IsInvertible ZO.presheaf ZO.ringCatSheaf.2
      ((Scheme.Modules.pullback (qOL ≫ lP)).obj H) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  have : SheafOfModules.IsInvertible ZO.presheaf ZO.ringCatSheaf.2
      ((Scheme.Modules.pullback (qOL ≫ lQ)).obj H) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  -- the nodal decompositions of the two copies of `T_O`
  have nP := EulerSumUnionTwist.eulerSum_add_one_of_inf_eq_bot_of_isIso_sup k gO
    ((Scheme.Modules.pullback (qOL ≫ lP)).obj H) IA IB hinf hsup
  have nQ := EulerSumUnionTwist.eulerSum_add_one_of_inf_eq_bot_of_isIso_sup k gO
    ((Scheme.Modules.pullback (qOL ≫ lQ)).obj H) IA IB hinf hsup
  -- constancy along the family over `V(I)`
  have c₁ : eulerSum k (pullback.snd (modelTower k) (modelKPoint k ![0, 0, 1]))
        ((Scheme.Modules.pullback (q₁L ≫ lP)).obj H) =
      eulerSum k gO ((Scheme.Modules.pullback (qOL ≫ lP)).obj H) := by
    rw [eulerSum_pullback_comp, eulerSum_pullback_comp]
    exact eulerSum_eq_of_isPullback_of_isInvertible _ _ _ _ q₁L _ sq₁L qOL gO sqOL
  have d₂ : eulerSum k (pullback.snd (modelTower k) (modelKPoint k ![0, 0, 1]))
        ((Scheme.Modules.pullback (q₁L ≫ lQ)).obj H) =
      eulerSum k gO ((Scheme.Modules.pullback (qOL ≫ lQ)).obj H) := by
    rw [eulerSum_pullback_comp, eulerSum_pullback_comp]
    exact eulerSum_eq_of_isPullback_of_isInvertible _ _ _ _ q₁L _ sq₁L qOL gO sqOL
  -- constancy along the exceptional family over `V(J')`
  have c₂ : eulerSum k (pullback.snd (modelTower k) (modelKPoint k ![1, 1, 0]))
        ((Scheme.Modules.pullback (q₂E ≫ eQ)).obj H) =
      eulerSum k (pullback.snd (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
          (strictCentre (centreIdeal k) (curveIdeal k))) o')
        ((Scheme.Modules.pullback (pullback.fst
          (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
          (strictCentre (centreIdeal k) (curveIdeal k))) o' ≫ eQ)).obj H) := by
    rw [eulerSum_pullback_comp, eulerSum_pullback_comp]
    exact eulerSum_eq_of_isPullback_of_isInvertible _ _ _ _ q₂E _ sq₂E _ _ sqB
  have d₁ : eulerSum k (pullback.snd (modelTower k) (modelKPoint k ![1, 1, 0]))
        ((Scheme.Modules.pullback (q₂E ≫ eP)).obj H) =
      eulerSum k (pullback.snd (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
          (strictCentre (centreIdeal k) (curveIdeal k))) o')
        ((Scheme.Modules.pullback (pullback.fst
          (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
          (strictCentre (centreIdeal k) (curveIdeal k))) o' ≫ eP)).obj H) := by
    rw [eulerSum_pullback_comp, eulerSum_pullback_comp]
    exact eulerSum_eq_of_isPullback_of_isInvertible _ _ _ _ q₂E _ sq₂E _ _ sqB
  -- `V(IB)` is the fibre of the exceptional family over `o'`
  have bP : eulerSum k (IB.subschemeι ≫ gO) ((Scheme.Modules.pullback IB.subschemeι).obj
      ((Scheme.Modules.pullback (qOL ≫ lP)).obj H)) =
      eulerSum k (pullback.snd (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
          (strictCentre (centreIdeal k) (curveIdeal k))) o')
        ((Scheme.Modules.pullback (pullback.fst
          (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
          (strictCentre (centreIdeal k) (curveIdeal k))) o' ≫ eP)).obj H) := by
    rw [← eulerSum_pullback_comp]
    refine eulerSum_pullback_eq_of_iso_of_comp_ι k _ _ _ _ eB ?_ heB₂ H
    simp only [Category.assoc, heP, hlP]
    exact ((reassoc_of% heB₁) tP).trans
      (congrArg (IB.subschemeι ≫ ·) ((reassoc_of% hqOL) tP).symm)
  have bQ : eulerSum k (IB.subschemeι ≫ gO) ((Scheme.Modules.pullback IB.subschemeι).obj
      ((Scheme.Modules.pullback (qOL ≫ lQ)).obj H)) =
      eulerSum k (pullback.snd (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
          (strictCentre (centreIdeal k) (curveIdeal k))) o')
        ((Scheme.Modules.pullback (pullback.fst
          (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
          (strictCentre (centreIdeal k) (curveIdeal k))) o' ≫ eQ)).obj H) := by
    rw [← eulerSum_pullback_comp]
    refine eulerSum_pullback_eq_of_iso_of_comp_ι k _ _ _ _ eB ?_ heB₂ H
    simp only [Category.assoc, heQ, hlQ]
    exact ((reassoc_of% heB₁) tQ).trans
      (congrArg (IB.subschemeι ≫ ·) ((reassoc_of% hqOL) tQ).symm)
  -- the fibre of `f` over `c₀`, read in the two charts
  have c₃ : eulerSum k (pullback.snd (modelTower k) (modelKPoint k ![0, 0, 1]))
        ((Scheme.Modules.pullback (q₁L ≫ lP)).obj H) =
      eulerSum k (pullback.snd (modelTower k) (modelKPoint k ![1, 1, 0]))
        ((Scheme.Modules.pullback (q₂E ≫ eQ)).obj H) := by
    have S₁ := s₁.paste_horiz hsP.flip
    have S₂ := s₂.paste_horiz hsQ.flip
    rw [hc] at S₁
    refine eulerSum_pullback_eq_of_iso_of_comp_ι k _ _ _ _ (S₁.isoIsPullback _ _ S₂) ?_
      (S₁.isoIsPullback_hom_snd _ _ S₂) H
    simp only [Category.assoc, heQ, hlP]
    exact (congrArg ((S₁.isoIsPullback _ _ S₂).hom ≫ ·) ((reassoc_of% hq₂E) tQ)).trans
      ((S₁.isoIsPullback_hom_fst _ _ S₂).trans ((reassoc_of% hq₁L) tP).symm)
  -- the fibre of `f` over `d₀`, read in the two charts
  have d₃ : eulerSum k (pullback.snd (modelTower k) (modelKPoint k ![1, 1, 0]))
        ((Scheme.Modules.pullback (q₂E ≫ eP)).obj H) =
      eulerSum k (pullback.snd (modelTower k) (modelKPoint k ![0, 0, 1]))
        ((Scheme.Modules.pullback (q₁L ≫ lQ)).obj H) := by
    have S₁ := s₂.paste_horiz hsP.flip
    have S₂ := s₁.paste_horiz hsQ.flip
    rw [hd] at S₁
    refine eulerSum_pullback_eq_of_iso_of_comp_ι k _ _ _ _ (S₁.isoIsPullback _ _ S₂) ?_
      (S₁.isoIsPullback_hom_snd _ _ S₂) H
    simp only [Category.assoc, heP, hlQ]
    exact (congrArg ((S₁.isoIsPullback _ _ S₂).hom ≫ ·) ((reassoc_of% hq₁L) tQ)).trans
      ((S₁.isoIsPullback_hom_fst _ _ S₂).trans ((reassoc_of% hq₂E) tP).symm)
  omega

/-- **The Euler-characteristic relation for an invertible module on all of `V`**, derived from
`eulerSum_add_eq_two_of_opens_of_nodal` with the open `W = V`. -/
theorem eulerSum_add_eq_two_of_nodal {ZO : Scheme.{u}} (qO : ZO ⟶ modelSpace k)
    (gO : ZO ⟶ Spec (.of k)) (sqO : IsPullback qO gO (modelTower k) (modelKPoint k 0))
    (IA IB : ZO.IdealSheafData) (hinf : IA ⊓ IB = ⊥) (hsup : IsIso ((IA ⊔ IB).subschemeι ≫ gO))
    (o' : Spec (.of k) ⟶ (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k)).subscheme)
    (hB : ∀ {F' : Scheme.{u}}
      (q' : F' ⟶ exceptionalDivisor (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k)))
      (g' : F' ⟶ Spec (.of k)),
      IsPullback q' g' (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
        (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))) o' →
      ∃ e : IB.subscheme ≅ F',
        e.hom ≫ q' ≫ (exceptionalIdeal
          (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))).subschemeι =
            IB.subschemeι ≫ qO ∧
          e.hom ≫ g' = IB.subschemeι ≫ gO)
    {V Y : Scheme.{u}} (f : V ⟶ Y) (cP cQ : Spec (.of (ModelRing k)) ⟶ Y)
    (tP tQ : modelSpace k ⟶ V)
    (hsP : IsPullback (modelTower k) tP cP f) (hsQ : IsPullback (modelTower k) tQ cQ f)
    (hc : modelKPoint k ![0, 0, 1] ≫ cP = modelKPoint k ![1, 1, 0] ≫ cQ)
    (hd : modelKPoint k ![1, 1, 0] ≫ cP = modelKPoint k ![0, 0, 1] ≫ cQ)
    (H : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H] :
    eulerSum k (IA.subschemeι ≫ gO)
        ((Scheme.Modules.pullback (IA.subschemeι ≫ qO ≫ tP)).obj H) +
      eulerSum k (IA.subschemeι ≫ gO)
        ((Scheme.Modules.pullback (IA.subschemeι ≫ qO ≫ tQ)).obj H) = 2 := by
  obtain ⟨gP, hgP⟩ := exists_comp_ι_eq_of_forall_mem (⊤ : V.Opens)
    (IA.subschemeι ≫ qO ≫ tP) (fun _ => by simp)
  obtain ⟨gQ, hgQ⟩ := exists_comp_ι_eq_of_forall_mem (⊤ : V.Opens)
    (IA.subschemeι ≫ qO ≫ tQ) (fun _ => by simp)
  have : SheafOfModules.IsInvertible (⊤ : V.Opens).toScheme.presheaf
      (⊤ : V.Opens).toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback (⊤ : V.Opens).ι).obj H) :=
    Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback _ _
  have h := eulerSum_add_eq_two_of_opens_of_nodal k qO gO sqO IA IB hinf hsup o' hB f cP cQ
    tP tQ hsP hsQ hc hd ⊤ (fun _ _ => by simp) (fun _ _ => by simp) gP gQ hgP hgQ
    ((Scheme.Modules.pullback (⊤ : V.Opens).ι).obj H)
  rwa [← eulerSum_pullback_comp, ← eulerSum_pullback_comp, hgP, hgQ] at h

/-- **The Euler-characteristic relation of Hironaka's example, for any two glued copies of the
model tower, globally and on an open.** There are a fibre `T_O` of the model tower over the
origin and a closed subscheme `A = V(IA) ⊆ T_O` isomorphic over `k` to `ℙ¹_k` such that, whenever
`f : V ⟶ Y` is the model tower over `cP` (through `tP`) and over `cQ` (through `tQ`), with the
model points `(0, 0, 1)` at `P` and `(1, 1, 0)` at `Q` the same point of `Y`, and `(1, 1, 0)` at
`P` and `(0, 0, 1)` at `Q` the same point of `Y`:

* the restrictions of every invertible module `ℋ` on `V` to the two copies of `A` satisfy
  `χ(ℋ_P|A) + χ(ℋ_Q|A) = 2`;
* the same holds for every invertible module `ℋ` on an open `W ⊆ V` containing the images under
  `tP` and `tQ` of the part of the model over `V(I) ∪ V(J)`, with `gP`, `gQ : A ⟶ W` the two
  maps of `A` into `W`. -/
theorem exists_eulerSum_add_eq_two_and_of_opens :
    ∃ (ZO : Scheme.{u}) (qO : ZO ⟶ modelSpace k) (gO : ZO ⟶ Spec (.of k))
      (_ : IsPullback qO gO (modelTower k) (modelKPoint k 0)) (IA : ZO.IdealSheafData)
      (eA : IA.subscheme ≅ AlgebraicGeometry.Proj (polyGrading k 1)),
      eA.hom ≫ projToSpecCoeff k 1 = IA.subschemeι ≫ gO ∧
      (∀ {V Y : Scheme.{u}} (f : V ⟶ Y) (cP cQ : Spec (.of (ModelRing k)) ⟶ Y)
        (tP tQ : modelSpace k ⟶ V),
        IsPullback (modelTower k) tP cP f → IsPullback (modelTower k) tQ cQ f →
        modelKPoint k ![0, 0, 1] ≫ cP = modelKPoint k ![1, 1, 0] ≫ cQ →
        modelKPoint k ![1, 1, 0] ≫ cP = modelKPoint k ![0, 0, 1] ≫ cQ →
        ∀ (H : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H],
          eulerSum k (IA.subschemeι ≫ gO)
              ((Scheme.Modules.pullback (IA.subschemeι ≫ qO ≫ tP)).obj H) +
            eulerSum k (IA.subschemeι ≫ gO)
              ((Scheme.Modules.pullback (IA.subschemeι ≫ qO ≫ tQ)).obj H) = 2) ∧
      ∀ {V Y : Scheme.{u}} (f : V ⟶ Y) (cP cQ : Spec (.of (ModelRing k)) ⟶ Y)
        (tP tQ : modelSpace k ⟶ V),
        IsPullback (modelTower k) tP cP f → IsPullback (modelTower k) tQ cQ f →
        modelKPoint k ![0, 0, 1] ≫ cP = modelKPoint k ![1, 1, 0] ≫ cQ →
        modelKPoint k ![1, 1, 0] ≫ cP = modelKPoint k ![0, 0, 1] ≫ cQ →
        ∀ (W : V.Opens),
        (∀ x : modelSpace k, modelTower k x ∈
          (modelIdealSheafI k).supportSet ∪ (modelIdealSheafJ k).supportSet → tP x ∈ W) →
        (∀ x : modelSpace k, modelTower k x ∈
          (modelIdealSheafI k).supportSet ∪ (modelIdealSheafJ k).supportSet → tQ x ∈ W) →
        ∀ (gP gQ : IA.subscheme ⟶ W.toScheme), gP ≫ W.ι = IA.subschemeι ≫ qO ≫ tP →
          gQ ≫ W.ι = IA.subschemeι ≫ qO ≫ tQ →
        ∀ (H : W.toScheme.Modules)
          [SheafOfModules.IsInvertible W.toScheme.presheaf W.toScheme.ringCatSheaf.2 H],
          eulerSum k (IA.subschemeι ≫ gO) ((Scheme.Modules.pullback gP).obj H) +
            eulerSum k (IA.subschemeι ≫ gO) ((Scheme.Modules.pullback gQ).obj H) = 2 := by
  obtain ⟨ZO, qO, gO, sqO, IA, IB, hinf, hsup, ⟨eA, heA⟩, o', hB⟩ :=
    HironakaLocalModel.nodal_originFibre k
  exact ⟨ZO, qO, gO, sqO, IA, eA, heA,
    fun f cP cQ tP tQ hsP hsQ hc hd H _ =>
      eulerSum_add_eq_two_of_nodal k qO gO sqO IA IB hinf hsup o' hB f cP cQ tP tQ hsP hsQ hc hd H,
    fun f cP cQ tP tQ hsP hsQ hc hd W hWP hWQ gP gQ hgP hgQ H _ =>
      eulerSum_add_eq_two_of_opens_of_nodal k qO gO sqO IA IB hinf hsup o' hB f cP cQ tP tQ hsP
        hsQ hc hd W hWP hWQ gP gQ hgP hgQ H⟩

/-- **The Euler-characteristic relation of Hironaka's example, for any two glued copies of the
model tower.** There are a fibre `T_O` of the model tower over the origin and a closed subscheme
`A ⊆ T_O` isomorphic over `k` to `ℙ¹_k` such that: whenever `f : V ⟶ Y` is the model tower over
`cP` (through `tP`) and over `cQ` (through `tQ`), with the model points `(0, 0, 1)` at `P` and
`(1, 1, 0)` at `Q` the same point of `Y`, and `(1, 1, 0)` at `P` and `(0, 0, 1)` at `Q` the same
point of `Y`, the restrictions of every invertible module `ℋ` on `V` to the two copies of `A`
satisfy `χ(ℋ_P|A) + χ(ℋ_Q|A) = 2`. -/
theorem exists_eulerSum_add_eq_two :
    ∃ (ZO : Scheme.{u}) (qO : ZO ⟶ modelSpace k) (gO : ZO ⟶ Spec (.of k))
      (_ : IsPullback qO gO (modelTower k) (modelKPoint k 0)) (IA : ZO.IdealSheafData)
      (eA : IA.subscheme ≅ AlgebraicGeometry.Proj (polyGrading k 1)),
      eA.hom ≫ projToSpecCoeff k 1 = IA.subschemeι ≫ gO ∧
      ∀ {V Y : Scheme.{u}} (f : V ⟶ Y) (cP cQ : Spec (.of (ModelRing k)) ⟶ Y)
        (tP tQ : modelSpace k ⟶ V),
        IsPullback (modelTower k) tP cP f → IsPullback (modelTower k) tQ cQ f →
        modelKPoint k ![0, 0, 1] ≫ cP = modelKPoint k ![1, 1, 0] ≫ cQ →
        modelKPoint k ![1, 1, 0] ≫ cP = modelKPoint k ![0, 0, 1] ≫ cQ →
        ∀ (H : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H],
          eulerSum k (IA.subschemeι ≫ gO)
              ((Scheme.Modules.pullback (IA.subschemeι ≫ qO ≫ tP)).obj H) +
            eulerSum k (IA.subschemeι ≫ gO)
              ((Scheme.Modules.pullback (IA.subschemeι ≫ qO ≫ tQ)).obj H) = 2 := by
  obtain ⟨ZO, qO, gO, sqO, IA, eA, heA, h, -⟩ := exists_eulerSum_add_eq_two_and_of_opens k
  exact ⟨ZO, qO, gO, sqO, IA, eA, heA, h⟩

/-- **The Euler-characteristic relation of Hironaka's example, for an invertible module on an
open containing the two families.** The localized half of
`exists_eulerSum_add_eq_two_and_of_opens`. -/
theorem exists_eulerSum_add_eq_two_of_opens :
    ∃ (ZO : Scheme.{u}) (qO : ZO ⟶ modelSpace k) (gO : ZO ⟶ Spec (.of k))
      (_ : IsPullback qO gO (modelTower k) (modelKPoint k 0)) (IA : ZO.IdealSheafData)
      (eA : IA.subscheme ≅ AlgebraicGeometry.Proj (polyGrading k 1)),
      eA.hom ≫ projToSpecCoeff k 1 = IA.subschemeι ≫ gO ∧
      ∀ {V Y : Scheme.{u}} (f : V ⟶ Y) (cP cQ : Spec (.of (ModelRing k)) ⟶ Y)
        (tP tQ : modelSpace k ⟶ V),
        IsPullback (modelTower k) tP cP f → IsPullback (modelTower k) tQ cQ f →
        modelKPoint k ![0, 0, 1] ≫ cP = modelKPoint k ![1, 1, 0] ≫ cQ →
        modelKPoint k ![1, 1, 0] ≫ cP = modelKPoint k ![0, 0, 1] ≫ cQ →
        ∀ (W : V.Opens),
        (∀ x : modelSpace k, modelTower k x ∈
          (modelIdealSheafI k).supportSet ∪ (modelIdealSheafJ k).supportSet → tP x ∈ W) →
        (∀ x : modelSpace k, modelTower k x ∈
          (modelIdealSheafI k).supportSet ∪ (modelIdealSheafJ k).supportSet → tQ x ∈ W) →
        ∀ (gP gQ : IA.subscheme ⟶ W.toScheme), gP ≫ W.ι = IA.subschemeι ≫ qO ≫ tP →
          gQ ≫ W.ι = IA.subschemeι ≫ qO ≫ tQ →
        ∀ (H : W.toScheme.Modules)
          [SheafOfModules.IsInvertible W.toScheme.presheaf W.toScheme.ringCatSheaf.2 H],
          eulerSum k (IA.subschemeι ≫ gO) ((Scheme.Modules.pullback gP).obj H) +
            eulerSum k (IA.subschemeι ≫ gO) ((Scheme.Modules.pullback gQ).obj H) = 2 := by
  obtain ⟨ZO, qO, gO, sqO, IA, eA, heA, -, h⟩ := exists_eulerSum_add_eq_two_and_of_opens k
  exact ⟨ZO, qO, gO, sqO, IA, eA, heA, h⟩

/-- **The Euler-characteristic relation for Hironaka's morphism.** There are a fibre `T_O` of
the model tower over the origin and a closed subscheme `A ⊆ T_O` isomorphic over `k` to `ℙ¹_k`
such that, for every invertible module `ℋ` on Hironaka's threefold `V`, the restrictions of `ℋ`
to the copies of `A` in the fibres over `P` (through `towerToVP`) and over `Q` (through
`towerToVQ`) satisfy `χ(ℋ_P|A) + χ(ℋ_Q|A) = 2`. -/
theorem exists_eulerSum_towerToVP_add_towerToVQ_eq_two :
    ∃ (ZO : Scheme.{u}) (qO : ZO ⟶ modelSpace k) (gO : ZO ⟶ Spec (.of k))
      (_ : IsPullback qO gO (modelTower k) (modelKPoint k 0)) (IA : ZO.IdealSheafData)
      (eA : IA.subscheme ≅ AlgebraicGeometry.Proj (polyGrading k 1)),
      eA.hom ≫ projToSpecCoeff k 1 = IA.subschemeι ≫ gO ∧
      ∀ (H : (hironakaThreefold k).Modules)
        [SheafOfModules.IsInvertible (hironakaThreefold k).presheaf
          (hironakaThreefold k).ringCatSheaf.2 H],
        eulerSum k (IA.subschemeι ≫ gO)
            ((Scheme.Modules.pullback (IA.subschemeι ≫ qO ≫ towerToVP k)).obj H) +
          eulerSum k (IA.subschemeι ≫ gO)
            ((Scheme.Modules.pullback (IA.subschemeι ≫ qO ≫ towerToVQ k)).obj H) = 2 := by
  obtain ⟨ZO, qO, gO, sqO, IA, eA, heA, h⟩ := exists_eulerSum_add_eq_two k
  exact ⟨ZO, qO, gO, sqO, IA, eA, heA, fun H _ => h (hironakaMorphism k) (chartP k) (chartQ k)
    (towerToVP k) (towerToVQ k) (isPullback_towerToVP k) (isPullback_towerToVQ k)
    (modelKPoint_chartP_eq_chartQ_c₀ k) (modelKPoint_chartP_eq_chartQ_d₀ k) H⟩

end Stacks.Examples.HironakaNotProjective

end
