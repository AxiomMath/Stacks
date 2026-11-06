module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FiberSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingAlongDomination
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingRegularSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreRegularityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspace

/-!
# The fibre regular sequence of Stacks 06LW over an enlarged field

The hypothesis of Stacks 06LW is that finitely many global regular functions `f₁, …, f_r` on an
algebraic space `X` map to a regular sequence in the étale local ring `𝒪_{F, z̄}` of the fibre
`F = X ×_Y Spec k` at a geometric point `z`.  This file transports that hypothesis along a
domination of geometric points of `F` and to the base-changed fibre
`F ×_{Spec k} Spec k' = X ×_Y Spec k'` over a field extension `k'` of `k`, and reads it on a
chart of the fibre.

## Main results

* `AlgebraicGeometry.Space.etaleLocalRingGerm_eval_eq_of_hom` and
  `AlgebraicGeometry.Space.etaleLocalRingGerm_eval_eq`: the germ in the étale local ring of a
  global regular function does not depend on the small étale neighbourhood it is read on.
* `AlgebraicGeometry.Space.isRegular_ofFn_etaleLocalRingMap_eval_of_dominates`: the hypothesis
  transported along a domination of geometric points of `F`.
* `AlgebraicGeometry.Space.isRegular_ofFn_etaleLocalRingMap_eval_pullback_fst`: the hypothesis
  transported along the projection `F ×_{Spec k} Spec k' ⟶ F`.
* `AlgebraicGeometry.Space.isRegular_ofFn_etaleLocalRingMap_etaleLocalRingGerm_iff_fiber`: over a
  chart of the fibre identified with `U_v ×_{κ(v)} Spec K` compatibly with its morphism to the
  chart `U` of `X`, regularity in the étale local ring is regularity of the restrictions to `U_v`
  in the ordinary local ring `𝒪_{U_v, u}`.

## References

* [Stacks Project, Tag 00LM](https://stacks.math.columbia.edu/tag/00LM)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The germ of a global regular function is independent of the neighbourhood -/

/-- The germ in the étale local ring of a global regular function is unchanged along a morphism
of small étale neighbourhoods. -/
theorem etaleLocalRingGerm_eval_eq_of_hom (X : AlgebraicSpaces B S hS)
    (a : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    {z : GeometricPoint B S hS X.1} {N M : SmallEtaleNeighborhood z} (h : N ⟶ M) :
    etaleLocalRingGerm B S hS X.1 z (op N) (a.eval (op N.chart)) =
      etaleLocalRingGerm B S hS X.1 z (op M) (a.eval (op M.chart)) := by
  exact (congrArg (etaleLocalRingGerm B S hS X.1 z (op N)) (a.property h.hom.op).symm).trans
    (RingHom.congr_fun (etaleLocalRingGerm_comp_map B S hS h) (a.eval (op M.chart)))

/-- The germ in the étale local ring of a global regular function does not depend on the small
étale neighbourhood it is read on. -/
theorem etaleLocalRingGerm_eval_eq (X : AlgebraicSpaces B S hS)
    (a : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    {z : GeometricPoint B S hS X.1} (N M : SmallEtaleNeighborhood z) :
    etaleLocalRingGerm B S hS X.1 z (op N) (a.eval (op N.chart)) =
      etaleLocalRingGerm B S hS X.1 z (op M) (a.eval (op M.chart)) := by
  obtain ⟨W, ⟨gN, gM⟩⟩ := SmallEtaleNeighborhood.exists_common_refinement X.2 N M
  exact (etaleLocalRingGerm_eval_eq_of_hom B S hS X a gN).symm.trans
    (etaleLocalRingGerm_eval_eq_of_hom B S hS X a gM)

/-! ### Transporting the fibre hypothesis of Stacks 06LW -/

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_FibreRegularSequenceBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_FibreRegularSequenceBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _


/-- Regularity of `List.ofFn f` is unchanged under a pointwise change of `f`. -/
private theorem isRegular_ofFn_congr {R : Type*} [CommRing R] {r : ℕ} {f g : Fin r → R}
    (h : ∀ i, f i = g i) :
    RingTheory.Sequence.IsRegular R (List.ofFn f) ↔
      RingTheory.Sequence.IsRegular R (List.ofFn g) := by
  rw [funext h]

/-- If the global regular functions `a₁, …, a_r` of `X` map to a regular sequence in the étale
local ring of `F` at `z`, and `z'` is a geometric point of `F` dominated by `z` — its section is
the restriction of that of `z` along `d` — then they do so at `z'` as well. -/
theorem isRegular_ofFn_etaleLocalRingMap_eval_of_dominates (X : AlgebraicSpaces B S hS) {r : ℕ}
    (a : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (p : F ⟶ X.1)
    {z z' : GeometricPoint B S hS F}
    (d : z'.val.siteObject ⟶ z.val.siteObject)
    (hd : F.map d.op z.val.value = z'.val.value)
    (hreg : ∀ N : SmallEtaleNeighborhood (geometricPointMap p z),
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F z)
        (List.ofFn fun i : Fin r => etaleLocalRingMap hF p z
          (etaleLocalRingGerm B S hS X.1 (geometricPointMap p z) (op N)
            ((a i).eval (op N.chart))))) :
    ∀ M : SmallEtaleNeighborhood (geometricPointMap p z'),
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F z')
        (List.ofFn fun i : Fin r => etaleLocalRingMap hF p z'
          (etaleLocalRingGerm B S hS X.1 (geometricPointMap p z') (op M)
            ((a i).eval (op M.chart)))) := by
  intro M
  obtain ⟨N₀⟩ := nonempty_smallEtaleNeighborhood X.2 (geometricPointMap p z)
  have h2 := isRegular_ofFn_etaleLocalRingMap_germ_along hF X.2 p d hd N₀
    (fun i => (a i).eval (op N₀.chart)) (hreg N₀)
  exact (isRegular_ofFn_congr fun i => congrArg (etaleLocalRingMap hF p z')
    (etaleLocalRingGerm_eval_eq B S hS X (a i) _ M)).mp h2

/-- Let `F` be an algebraic space over the spectrum of a field `k` in the site and let
`c : T' ⟶ Spec k` be a morphism of the site, so that `F' = F ×_{Spec k} T'` is the base-changed
fibre.  If the global regular functions `a₁, …, a_r` of `X` map to a regular sequence in the
étale local ring of `F` at the image of a geometric point `w` of `F'`, then they do so in the
étale local ring of `F'` at `w`. -/
theorem isRegular_ofFn_etaleLocalRingMap_eval_pullback_fst (X : AlgebraicSpaces B S hS) {r : ℕ}
    (a : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (p : F ⟶ X.1)
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (π : F ⟶ yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))
    {T' : BigFppfOver B S hS}
    (c : T' ⟶ (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS))
    (hF' : IsAlgebraicSpace B S hS (pullback π (yoneda.map c)))
    (w : GeometricPoint B S hS (pullback π (yoneda.map c)))
    (hreg : ∀ N : SmallEtaleNeighborhood
        (geometricPointMap p (geometricPointMap (pullback.fst π (yoneda.map c)) w)),
      RingTheory.Sequence.IsRegular
        (etaleLocalRing B S hS F (geometricPointMap (pullback.fst π (yoneda.map c)) w))
        (List.ofFn fun i : Fin r =>
          etaleLocalRingMap hF p (geometricPointMap (pullback.fst π (yoneda.map c)) w)
            (etaleLocalRingGerm B S hS X.1
              (geometricPointMap p (geometricPointMap (pullback.fst π (yoneda.map c)) w)) (op N)
              ((a i).eval (op N.chart))))) :
    ∀ M : SmallEtaleNeighborhood
        (geometricPointMap (pullback.fst π (yoneda.map c) ≫ p) w),
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS (pullback π (yoneda.map c)) w)
        (List.ofFn fun i : Fin r =>
          etaleLocalRingMap hF' (pullback.fst π (yoneda.map c) ≫ p) w
            (etaleLocalRingGerm B S hS X.1
              (geometricPointMap (pullback.fst π (yoneda.map c) ≫ p) w) (op M)
              ((a i).eval (op M.chart)))) := by
  intro M
  have hiff := isRegular_map_etaleLocalRingMap_iff_of_isFlatAt B S hS hF' hF
    (pullback.fst π (yoneda.map c)) w
    (isFlatAt_pullback_fst_yoneda_map_of_field B S hS hF hk b π c w.image)
    (List.ofFn fun i : Fin r =>
      etaleLocalRingMap hF p (geometricPointMap (pullback.fst π (yoneda.map c)) w)
        (etaleLocalRingGerm B S hS X.1
          (geometricPointMap p (geometricPointMap (pullback.fst π (yoneda.map c)) w)) (op M)
          ((a i).eval (op M.chart))))
  have h' := hiff.mpr (hreg M)
  rw [List.map_ofFn] at h'
  exact (isRegular_ofFn_congr fun i => RingHom.congr_fun
    (etaleLocalRingMap_comp hF' hF (pullback.fst π (yoneda.map c)) p w) _).mp h'


/-! ### Reading the fibre hypothesis on the chart of the fibre -/

/-- Let `f : X' ⟶ X` be a morphism of algebraic spaces, let `x̄` be a geometric point of `X'` and
let `cU` be a morphism of the site from the chart of a small étale neighbourhood `N` of `x̄` to an
étale chart `U` of `X`, commuting over `f`. Suppose the chart scheme of `N` is identified, by a
flat morphism `j`, with the base change `U_v ×_{κ(v)} Spec K` of the fibre at `v` of a morphism of
schemes `g : U ⟶ V`, compatibly with `cU` — the composite `U_v ×_{κ(v)} Spec K ⟶ U_v ⟶ U` is the
morphism of schemes underlying `cU`.

Then finitely many global regular functions `a₁, …, a_r` on `U` are a regular sequence in the
étale local ring `𝒪_{X', x̄}` — in the sense of
`AlgebraicGeometry.Space.FibreIsRegularSequenceAt`, their germs at `x̄` pushed along `f` — if and
only if their restrictions to the fibre `U_v` are a regular sequence in the ordinary local ring
`𝒪_{U_v, u}`. -/
theorem isRegular_ofFn_etaleLocalRingMap_etaleLocalRingGerm_iff_fiber
    {Xs Ys : AlgebraicSpaces B S hS} (f : Xs ⟶ Ys)
    (xbar : GeometricPoint B S hS Xs.1) (N : SmallEtaleNeighborhood xbar)
    (Wc : SmallEtale B S hS Ys.1) (cU : N.chart.obj.left ⟶ Wc.obj.left)
    (hcomm : N.chart.obj.hom ≫ f.hom = yoneda.map cU ≫ Wc.obj.hom)
    {V : Scheme.{u}} (g : chartScheme Wc ⟶ V) (v : V) {K : Type u} [Field K]
    (φ : V.residueField v ⟶ CommRingCat.of K)
    (j : chartScheme N.chart ⟶ pullback (g.fiberToSpecResidueField v) (Spec.map φ))
    [Flat j]
    (hm : (BigFppfOver.toScheme B S hS).map cU =
      j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ) ≫ g.fiberι v)
    {r : ℕ} (a : Fin r → Γ(chartScheme Wc, ⊤)) :
    RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Xs.1 xbar)
        (List.ofFn fun i : Fin r => etaleLocalRingMap Xs.2 f.hom xbar
          (etaleLocalRingGerm B S hS Ys.1 (geometricPointMap f.hom xbar)
            (op (targetNeighborhood B S hS N Wc cU hcomm)) (a i))) ↔
      RingTheory.Sequence.IsRegular ((g.fiber v).presheaf.stalk
          ((j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ))
            (chartPoint B S hS Xs.1 N)))
        (List.ofFn fun i : Fin r => (g.fiber v).presheaf.germ ⊤
          ((j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ))
            (chartPoint B S hS Xs.1 N)) trivial ((g.fiberι v).appTop (a i))) := by
  have hstep : ∀ i : Fin r, etaleLocalRingMap Xs.2 f.hom xbar
        (etaleLocalRingGerm B S hS Ys.1 (geometricPointMap f.hom xbar)
          (op (targetNeighborhood B S hS N Wc cU hcomm)) (a i)) =
      (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N).comp
          (((j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ)).stalkMap
            (chartPoint B S hS Xs.1 N)).hom)
        ((g.fiber v).presheaf.germ ⊤
          ((j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ))
            (chartPoint B S hS Xs.1 N)) trivial ((g.fiberι v).appTop (a i))) := by
    intro i
    have hgerm := ConcreteCategory.congr_hom
      (Stacks.AlgebraicGeometry.appTop_comp_germ_top
        ((BigFppfOver.toScheme B S hS).map cU) (chartPoint B S hS Xs.1 N)) (a i)
    have hfib := ConcreteCategory.congr_hom
      (Stacks.AlgebraicGeometry.appTop_comp_germ_top
        (j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ))
        (chartPoint B S hS Xs.1 N)) ((g.fiberι v).appTop (a i))
    have happ : ((BigFppfOver.toScheme B S hS).map cU).appTop (a i) =
        (j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ)).appTop
          ((g.fiberι v).appTop (a i)) := by
      rw [hm, ← Category.assoc, Scheme.Hom.comp_appTop]
      rfl
    refine Eq.trans (etaleLocalRingMap_etaleLocalRingGerm_eq B S hS f xbar N Wc cU hcomm
      (a i)) ?_
    refine congrArg (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N) ?_
    exact Eq.trans hgerm.symm (Eq.trans (congrArg
      ((chartScheme N.chart).presheaf.germ ⊤ (chartPoint B S hS Xs.1 N) trivial) happ) hfib)
  refine Iff.trans ?_ (isRegular_map_etaleLocalRing_iff_fiber_extendResidueField B S hS Xs.1
    Xs.2 N g v φ j (List.ofFn fun i : Fin r => (g.fiber v).presheaf.germ ⊤
      ((j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ))
        (chartPoint B S hS Xs.1 N)) trivial ((g.fiberι v).appTop (a i))))
  rw [List.map_ofFn]
  exact isRegular_ofFn_congr hstep

end AlgebraicGeometry.Space

end
