module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartHomRestrSliceBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleHomDescentSingleChart

/-!
# Descent of morphisms of modules from a surjective étale chart of an algebraic space

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B` and let `W` be an étale
scheme chart of `X` whose structure morphism is surjective.  A morphism `ℳ|_W ⟶ 𝒩|_W` of the
restrictions of two `𝒪_X`-modules to that chart is the restriction of a *unique* morphism
`ℳ ⟶ 𝒩` as soon as its two relocalizations to a chart playing the role of the kernel pair
`W ×_X W` agree.

`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleHomDescentSingleChart.lean` proves exactly that,
but with the restriction to the chart read as restriction to the *slice* `X_étale/W` of the small
étale site — the shape in which the gluing form of Stacks 03EM is available.  The consumers of
the statement hold instead a morphism of the inverse images of Stacks 03LU along the structure
morphism of the chart.  **This file joins the two readings.**

`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleHomDescentPresentation.lean` specialises the
result to the atlas of an étale presentation, where the kernel pair is the presentation's
relation.

The chart-level statement is the half of étale descent of morphisms that
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/HomDescent.lean` does not prove:
that file shows a morphism of `𝒪_X`-modules is *determined* by its inverse images along an étale
covering, and the statements below produce one from a compatible inverse image along a single
surjective chart.  Quasi-coherence is used nowhere: this is the sheaf condition on the small
étale site of `X`.

## Main definitions

* `AlgebraicGeometry.Space.chartSliceHom`: the slice reading of a morphism of the chart
  restrictions of two `𝒪_X`-modules — the morphism of the restrictions to `X_étale/W` which the
  comparison of Stacks 03LY carries it to.

## Main results

* `AlgebraicGeometry.Space.eq_of_isoConj_eq`: conjugation by two isomorphisms is injective on
  morphisms.  Stated abstractly, and applied below with every morphism positional.
* `AlgebraicGeometry.Space.chartModuleRestriction_map_eq_iff`: **the join.**  A morphism of
  `𝒪_X`-modules restricts to a given morphism of the chart restrictions exactly when its
  underlying presheaf morphism restricts to the slice reading of that morphism.
* `AlgebraicGeometry.Space.existsUnique_hom_of_chartSliceHom_relocalization_eq`: **descent of
  morphisms from a surjective étale chart.**  A morphism of the chart restrictions whose slice
  reading has equal relocalizations along a pair of arrows dominating every pair is the
  restriction of a unique morphism of `𝒪_X`-modules.
* `AlgebraicGeometry.Space.exists_dominating_hom_of_isPullback`: **a chart exhibited as the
  kernel pair dominates every pair of arrows.**  If `p, q : R ⟶ W` are morphisms of charts of
  `X` whose
  underlying morphisms of the site exhibit `R` as the fibre product `W ×_X W`, then every pair of
  arrows into `W` factors through them.  This is the only place the identification of the
  relation with the kernel pair is used, and it is used exactly as the source of Stacks 03M3
  uses it.
* `AlgebraicGeometry.Space.existsUnique_hom_of_isPullback`: the two previous results combined.

## Implementation notes

**The join is a full-faithfulness argument, not a computation on sections.**  The comparison
`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso` of Stacks 03LY identifies the chart
restriction with restriction to the slice followed by the reindexing
`AlgebraicGeometry.Space.chartModuleSliceReindex` along the comparison functor of Stacks 04M0,
and that reindexing is an *equivalence*
(`AlgebraicGeometry.Space.isEquivalence_chartModuleSliceReindex`).  So a morphism of the chart
restrictions has a unique preimage under it, whose underlying presheaf morphism is a morphism of
the `restrFun` restrictions with no transport — `SheafOfModules.over` and the `restrFun` of
Stacks 03EM agree on underlying presheaves of modules, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartHomRestrSliceBridge.lean` record.  Nothing here
evaluates a component.

**Why the rearrangement is an abstract lemma.**  Cancelling the two components of the comparison
with `CategoryTheory.cancel_epi` and `CategoryTheory.cancel_mono` sends instance search after
`CategoryTheory.Mono` for a morphism of `AlgebraicGeometry.Space.Modules`, which reaches the
`CategoryTheory.Abelian` instance of that category and leaves the module universe as a
metavariable; the elaborator then reports stuck universe constraints rather than a missing
instance.  `AlgebraicGeometry.Space.eq_of_isoConj_eq` carries the two isomorphisms and nothing
else, so its instantiation is first-order and no instance is searched for.

**The kernel pair enters as a pair of arrows, not as a product.**
`AlgebraicGeometry.Space.existsUnique_hom_of_single_chart` takes the dominating pair as an
argument, so the identification of the relation with `W ×_X W` is used only to produce the
factorisation, and the binary product of the small étale site — which exists, and is that fibre
product — never has to be compared with the relation.  The factorisation itself is
`CategoryTheory.IsPullback.lift` in presheaves, pulled back into the site by fullness of the
Yoneda embedding.

## What this is an input to, and what is still owed

Stacks 03M3 asserts that for a surjective étale `φ : U ⟶ X` with `R = U ×_X U` the functor
`ℱ ↦ (φ^*ℱ, α)` from quasi-coherent `𝒪_X`-modules to quasi-coherent modules on the groupoid
`(U, R, s, t, c)` is an equivalence.  The results here are the descent of morphisms that its
**fullness** clause needs, under the tag's own hypothesis `R = U ×_X U` with `t`, `s` the
projections — which is what `AlgebraicGeometry.Space.exists_dominating_hom_of_isPullback`
consumes, and what an étale presentation supplies.

What is still owed for fullness is the translation of the compatibility condition: the `comm`
field of `AlgebraicGeometry.Space.QuasicoherentModule.Hom` says that the morphism of inverse
images commutes with the two canonical transition morphisms, and what
`AlgebraicGeometry.Space.existsUnique_hom_of_isPullback` consumes is the agreement of the two
relocalizations of its slice reading.  Nothing here relates the two, and no declaration here
carries the `03M3` attribute.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Conjugation by two isomorphisms is injective on morphisms.**  Stated with the two
isomorphisms and nothing else, so that its instantiation at a comparison of functors of modules
is first-order and searches for no instance; see the implementation notes. -/
theorem eq_of_isoConj_eq {C : Type*} [Category C] {A A' D D' : C} (e : A ≅ A') (f : D ≅ D')
    {u v : A ⟶ D} (h : e.inv ≫ u ≫ f.hom = e.inv ≫ v ≫ f.hom) : u = v := by
  have h2 := congrArg (fun z : A' ⟶ D' => e.hom ≫ z ≫ f.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using h2

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### The slice reading of a morphism of chart restrictions -/

/-- **The slice reading of a morphism of the chart restrictions of two `𝒪_X`-modules**: the
morphism of their restrictions to the slice `X_étale/W` which the comparison of Stacks 03LY
carries it to.

The comparison identifies the chart restriction with restriction to the slice followed by the
reindexing along the comparison functor of Stacks 04M0, and that reindexing is an equivalence, so
the preimage exists and is unique; its underlying presheaf morphism is a morphism of the
`restrFun` restrictions with no transport. -/
def chartSliceHom (W : SmallEtale B S hS X.1) (M N : Modules.{u, u} B S hS X.1 X.2)
    (a : (chartModuleRestriction B S hS X W).obj M ⟶ (chartModuleRestriction B S hS X W).obj N) :
    (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) W).obj M.val ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) W).obj N.val :=
  ((chartModuleSliceReindex B S hS X W).preimage
    ((chartModuleRestrictionSliceIso B S hS X W).inv.app M ≫ a ≫
      (chartModuleRestrictionSliceIso B S hS X W).hom.app N)).val

/-- The reindexing of the slice restriction of a morphism of `𝒪_X`-modules is its chart
restriction, conjugated by the comparison of Stacks 03LY.  This is the naturality of that
comparison, with one of its two components cancelled. -/
theorem chartModuleSliceReindex_map_overFunctor_map (W : SmallEtale B S hS X.1)
    {M N : Modules.{u, u} B S hS X.1 X.2} (ψ : M ⟶ N) :
    (chartModuleSliceReindex B S hS X W).map
        ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) W).map ψ) =
      (chartModuleRestrictionSliceIso B S hS X W).inv.app M ≫
        (chartModuleRestriction B S hS X W).map ψ ≫
        (chartModuleRestrictionSliceIso B S hS X W).hom.app N := by
  rw [(chartModuleRestrictionSliceIso B S hS X W).hom.naturality ψ, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]
  rfl

/-- **The join of the two readings of restriction to a chart.**  A morphism of `𝒪_X`-modules
restricts to a given morphism `a` of the chart restrictions exactly when its underlying presheaf
morphism restricts to the slice reading of `a`.

Both directions are the previous lemma: the reindexing along the comparison functor of
Stacks 04M0 is faithful, which gives the forward direction, and full, which gives the
backward. -/
theorem chartModuleRestriction_map_eq_iff (W : SmallEtale B S hS X.1)
    (M N : Modules.{u, u} B S hS X.1 X.2)
    (a : (chartModuleRestriction B S hS X W).obj M ⟶ (chartModuleRestriction B S hS X W).obj N)
    (ψ : M ⟶ N) :
    (chartModuleRestriction B S hS X W).map ψ = a ↔
      (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) W).map ψ.val =
        chartSliceHom B S hS X W M N a := by
  set c := (chartModuleRestrictionSliceIso B S hS X W).inv.app M ≫ a ≫
    (chartModuleRestrictionSliceIso B S hS X W).hom.app N with hc
  have hpre := (chartModuleSliceReindex B S hS X W).map_preimage c
  have key := chartModuleSliceReindex_map_overFunctor_map B S hS X W ψ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine congrArg SheafOfModules.Hom.val
      ((chartModuleSliceReindex B S hS X W).map_injective (key.trans ?_))
    rw [h, hpre]
  · have hval : (SheafOfModules.overFunctor (structureRingSheaf B S hS X) W).map ψ =
        (chartModuleSliceReindex B S hS X W).preimage c := SheafOfModules.hom_ext h
    rw [hval, hpre] at key
    exact eq_of_isoConj_eq ((chartModuleRestrictionSliceIso B S hS X W).app M)
      ((chartModuleRestrictionSliceIso B S hS X W).app N) key.symm

/-! ### Descent of morphisms from a surjective chart -/

/-- **Descent of morphisms of `𝒪_X`-modules from a surjective étale chart.**  Let `W` be an étale
scheme chart of `X` with surjective structure morphism and let `p, q : R ⟶ W` be a pair of
morphisms of charts through which every pair of arrows into `W` factors.  A morphism `a` of the
restrictions of two `𝒪_X`-modules to `W` whose slice reading has equal relocalizations along `p`
and `q` is the restriction of a unique morphism `ℳ ⟶ 𝒩`.

This is `AlgebraicGeometry.Space.existsUnique_hom_of_single_chart`, the one-element gluing form
of Stacks 03EM, read through the join above; the surjective chart covers the final object of the
small étale site by `AlgebraicGeometry.Space.coversTop_singleton_of_isSurjective`. -/
theorem existsUnique_hom_of_chartSliceHom_relocalization_eq (W : SmallEtale B S hS X.1)
    (hW : IsSurjective B S hS W.1.hom) {R : SmallEtale B S hS X.1} (p q : R ⟶ W)
    (hdom : ∀ (Z : SmallEtale B S hS X.1) (f g : Z ⟶ W), ∃ h : Z ⟶ R, h ≫ p = f ∧ h ≫ q = g)
    (M N : Modules.{u, u} B S hS X.1 X.2)
    (a : (chartModuleRestriction B S hS X W).obj M ⟶ (chartModuleRestriction B S hS X W).obj N)
    (hpq : homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val p
          (chartSliceHom B S hS X W M N a) =
        homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val q
          (chartSliceHom B S hS X W M N a)) :
    ∃! ψ : M ⟶ N, (chartModuleRestriction B S hS X W).map ψ = a := by
  obtain ⟨Φ, hΦ, huniq⟩ := existsUnique_hom_of_single_chart B S hS X.1 X.2 M.val N.val N.isSheaf
    W (coversTop_singleton_of_isSurjective B S hS X W hW) R p q hdom _ hpq
  exact ⟨⟨Φ⟩, (chartModuleRestriction_map_eq_iff B S hS X W M N a ⟨Φ⟩).2 hΦ, fun ψ hψ =>
    SheafOfModules.hom_ext
      (huniq ψ.val ((chartModuleRestriction_map_eq_iff B S hS X W M N a ψ).1 hψ))⟩

/-! ### A chart exhibited as the kernel pair -/

/-- **A chart exhibited as the kernel pair dominates every pair of arrows.**  If `p, q : R ⟶ W`
are morphisms of étale charts of `X` whose underlying morphisms of the site exhibit `R` as the
fibre product `W ×_X W`, then every pair of arrows `Z ⟶ W` factors through `p` and `q`.

The factorisation is produced in presheaves by the universal property of the fibre product — the
two arrows out of `Z` agree after composing with the structure morphism of `W`, both composites
being the structure morphism of `Z` — and pulled back into the site by fullness of the Yoneda
embedding; its two triangles then hold in the site by faithfulness. -/
theorem exists_dominating_hom_of_isPullback {W R : SmallEtale B S hS X.1} (p q : R ⟶ W)
    (hpb : IsPullback (yoneda.map p.1.left) (yoneda.map q.1.left) W.1.hom W.1.hom)
    (Z : SmallEtale B S hS X.1) (f g : Z ⟶ W) :
    ∃ h : Z ⟶ R, h ≫ p = f ∧ h ≫ q = g := by
  have hf : yoneda.map f.1.left ≫ W.1.hom = Z.1.hom := CostructuredArrow.w f.1
  have hcomm : yoneda.map f.1.left ≫ W.1.hom = yoneda.map g.1.left ≫ W.1.hom :=
    hf.trans (CostructuredArrow.w g.1).symm
  obtain ⟨h', hh'⟩ : ∃ h' : Z.1.left ⟶ R.1.left,
      yoneda.map h' = hpb.lift (yoneda.map f.1.left) (yoneda.map g.1.left) hcomm :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hp : h' ≫ p.1.left = f.1.left := yoneda.map_injective (by simp [hh'])
  have hq : h' ≫ q.1.left = g.1.left := yoneda.map_injective (by simp [hh'])
  have hw : yoneda.map h' ≫ R.1.hom = Z.1.hom := by
    rwa [← CostructuredArrow.w p.1, ← Category.assoc, ← Functor.map_comp, hp]
  refine ⟨⟨CostructuredArrow.homMk h' hw⟩, ?_, ?_⟩
  · ext : 2
    exact hp
  · ext : 2
    exact hq

/-- **Descent of morphisms of `𝒪_X`-modules from a surjective étale chart whose kernel pair is a
given chart.**  This is
`AlgebraicGeometry.Space.existsUnique_hom_of_chartSliceHom_relocalization_eq` with the
domination hypothesis discharged from the identification of `R` with `W ×_X W`. -/
theorem existsUnique_hom_of_isPullback (W : SmallEtale B S hS X.1)
    (hW : IsSurjective B S hS W.1.hom) {R : SmallEtale B S hS X.1} (p q : R ⟶ W)
    (hpb : IsPullback (yoneda.map p.1.left) (yoneda.map q.1.left) W.1.hom W.1.hom)
    (M N : Modules.{u, u} B S hS X.1 X.2)
    (a : (chartModuleRestriction B S hS X W).obj M ⟶ (chartModuleRestriction B S hS X W).obj N)
    (hpq : homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val p
          (chartSliceHom B S hS X W M N a) =
        homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val q
          (chartSliceHom B S hS X W M N a)) :
    ∃! ψ : M ⟶ N, (chartModuleRestriction B S hS X W).map ψ = a :=
  existsUnique_hom_of_chartSliceHom_relocalization_eq B S hS X W hW p q
    (exists_dominating_hom_of_isPullback B S hS X p q hpb) M N a hpq

end AlgebraicGeometry.Space

end
