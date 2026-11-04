module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentStage
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackShrink
/-!
# The descent condition for a morphism over one open of a stage, and its two compatibilities

[Stacks Project, Tag 01ZR] (2) is proved for a cofiltered diagram of *affine* schemes by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_canonical_of_isAffine'`, and the
general quasi-compact quasi-separated case is to be deduced from it by Zariski glueing.  The chart
step of that deduction is
`Stacks.AlgebraicGeometry.ModuleLimits.exists_over_map_of_isAffineOpen_stage`, which descends the
restriction of the given morphism `φ` to the preimage of one affine open of the stage, in the
*pullback* form in which the tag states its conclusion.  Glueing such local data requires them in
the *restriction* form — as morphisms of the restrictions to the members of a covering of a stage —
and requires knowing that two of them agree on the overlaps.

This file supplies the translation and the two compatibilities.

`IsChartDescent q f p hq eQ φ χ` is the descent condition for a morphism `χ` of the restrictions
to an open `W` of a stage: conjugating `χ` along the limit projection `q` by
`Stacks.Modules.restrictPullbackIso` gives, over the preimage of the open `V` of the base, the
restriction of `φ` read through the canonical identification
`Stacks.AlgebraicGeometry.ModuleLimits.canHom` of the iterated pullback with the pullback of the
composite.  Two facts about it are proved, and they are the two halves of the glueing:

* **two chart data for the same `φ` agree on the overlap of their opens after pullback to the
  limit** (`pullback_map_restrictHomOfLE_eq_of_isChartDescent`) — this is the hypothesis of
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit'` for the diagram of
  preimages of the overlap, so it is what reduces the agreement on overlaps to Tag 01ZR (3);
* **the condition is stable under transport to a later stage**
  (`isChartDescent_of_isStageTransport`), and the transport commutes with restricting to a
  smaller open (`isStageTransport_restrictHomOfLE`), which is what lets the finitely many charts
  and the finitely many overlaps be refined to a single stage.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfPullback`: the conjugate by
  `Stacks.Modules.restrictPullbackIso` of an arbitrary morphism between the pullbacks along the
  restricted morphism of the restrictions to the open of the base.  It differs from
  `Stacks.AlgebraicGeometry.ModuleLimits.pullbackHomOfRestrict` in that its argument is not
  required to be a pullback of a morphism of the restrictions.
* `Stacks.AlgebraicGeometry.ModuleLimits.IsChartDescent`: the descent condition.
* `Stacks.AlgebraicGeometry.ModuleLimits.IsStageTransport`: the characterisation of the transport
  of a morphism of restrictions over an open of a stage to an open of a later stage.
* `Stacks.AlgebraicGeometry.ModuleLimits.coneProj` and
  `Stacks.AlgebraicGeometry.ModuleLimits.stageHom`: the projection of a cone onto one of its legs
  and the transition morphism of a stage over `i`, with their source and target spelled uniformly.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.isChartDescent_restrictHomOfPullback`: **the chart datum
  of Tag 01ZR (2), in the canonically pinned pullback form, satisfies the descent condition.**  The
  input is `Stacks.AlgebraicGeometry.ModuleLimits.restrictPullbackIso_hom_comp`, the compatibility
  of `Stacks.Modules.restrictPullbackIso` with composition.
* `Stacks.AlgebraicGeometry.ModuleLimits.pullback_map_restrictHomOfLE_eq_of_isChartDescent`: **two
  chart data satisfying the descent condition for the same `φ` agree on the overlap of their opens
  after pullback to the limit.**  The input is
  `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_pullbackHomOfRestrict_comm`, the
  compatibility of the conjugation with shrinking both of its opens.
* `Stacks.AlgebraicGeometry.ModuleLimits.isChartDescent_of_isStageTransport`: **a chart datum
  transported to a later stage still satisfies the descent condition.**  The input is
  `Stacks.AlgebraicGeometry.ModuleLimits.pullbackHomOfRestrict_comp`, the compatibility of the
  conjugation with composition.
* `Stacks.AlgebraicGeometry.ModuleLimits.isStageTransport_restrictHomOfLE`: **the restriction of a
  transport is the transport of the restriction.**
* `Stacks.AlgebraicGeometry.ModuleLimits.eq_of_isStageTransport`: two transports of morphisms whose
  conjugates along the transition morphism agree are equal.
* `Stacks.AlgebraicGeometry.ModuleLimits.canonicalDescent_resLE`,
  `Stacks.AlgebraicGeometry.ModuleLimits.descentDatum_resLE` and
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_chartComparisons`: the data produced by
  `exists_over_map_of_isAffineOpen_stage` for the diagram of preimages of an open, respelled with
  `AlgebraicGeometry.Scheme.Hom.resLE` in place of the diagram and cone of
  `AlgebraicGeometry.EventualLimit.preimageDiagram`.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isChartDescent_of_isAffineOpen`: **the chart step
  of Tag 01ZR (2) in descent-condition form, at every later stage.**  Over an affine open of a
  stage the restriction of the given morphism is, at every sufficiently late stage, the datum of a
  morphism of restrictions satisfying the descent condition.  This is the form in which the
  finitely many charts of a covering of a stage can be glued, and it is obtained from
  `canonicalDescent_coneProj` and `exists_isChartDescent_coneProj`.

## Implementation notes

Everything is stated over *abstract* morphisms `q`, `f`, `p` with an abstract `q ≫ f = p`, and the
proofs begin by substituting that equation.  Stating the comparisons for the concrete
`AlgebraicGeometry.Scheme.Hom.resLE` terms of the diagram of preimages makes the kernel descend
into `AlgebraicGeometry.Scheme.Modules.pullback`, i.e. into sheafification, and exceed its budget
even on a proof that is literally `rfl`.

For the same reason the three respellings of the last section are declarations of their own rather
than steps inside a larger proof: each is definitional, and each is comfortably inside the budget
on its own.

The statement of `canonicalDescent_resLE` is, unavoidably, *not uniform* in how it spells the
scheme that carries the open `c.π.app i ⁻¹ᵁ V`: the occurrences inside
`AlgebraicGeometry.Scheme.Hom.resLE` and `canHom` are typed at the source of `c.π.app k.left`,
while the occurrence inside `Scheme.Modules.restrictFunctor` is typed at the source of
`c.π.app i`, these being two definitionally equal but syntactically different descriptions of the
vertex of the cone.  Elaborating the statement is cheap, and converting the output of
`exists_over_map_of_isAffineOpen_stage` to it is within budget, precisely because each occurrence
keeps the description it is given by the morphism it comes from.

Feeding that statement to `isChartDescent_restrictHomOfPullback` is *not* within budget, and the
reason is this non-uniformity rather than the difficulty of any one conversion.  That lemma, like
every statement quantified over abstract `q`, `f`, `p` with a common source `S`, spells the open as
`p ⁻¹ᵁ V` with `S` throughout, so instantiating it forces one description everywhere; the
definitional equality between the two descriptions then has to be re-established at every position
of a term with some hundred thousand nodes, and the conversion descends through
`AlgebraicGeometry.Scheme.Hom.resLE` into `AlgebraicGeometry.morphismRestrict` and the
scheme-theoretic fibre product.  Declaring those locally irreducible does not help: that brings the
*elaboration* of the instantiation inside the budget, and the kernel, which ignores reducibility
attributes, then faces the same conversion.

The last section removes the non-uniformity instead of converting it away.  The two projections of
the cone and the transition morphism are read through `coneProj` and `stageHom`, whose source and
target are `c.pt` and `D.obj i` *by declaration*; a statement written with them is uniform by
construction, `canonicalDescent_coneProj` is the conversion of `canonicalDescent_resLE` carried out
in that spelling, and `exists_isChartDescent_coneProj` then instantiates
`isChartDescent_restrictHomOfPullback` at it with no conversion whatsoever.  The two are separate
declarations for the reason recorded above: each alone is inside the budget and the two together
are not.

A *definition* is needed here and an argument will not do.  Taking the projection as a variable `p`
with a hypothesis `p = c.π.app i` makes it opaque, so a hypothesis written with the concrete
projection — which is what the chart step produces — no longer typechecks against the statement;
`coneProj D c i` unfolds to `c.π.app i`, so it does.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

variable {S T T' B : Scheme.{u}}

/-! ### Functoriality of the two conjugations -/

/-- Restriction to a smaller open commutes with composition of morphisms of restrictions. -/
theorem restrictHomOfLE_comp {X : Scheme.{u}} {M N P : X.Modules} {V W : X.Opens} (e : V ≤ W)
    (χ : restrict M W.ι ⟶ restrict N W.ι) (χ' : restrict N W.ι ⟶ restrict P W.ι) :
    restrictHomOfLE e (χ ≫ χ') = restrictHomOfLE e χ ≫ restrictHomOfLE e χ' := by
  rw [restrictHomOfLE_eq, restrictHomOfLE_eq, restrictHomOfLE_eq,
    CategoryTheory.Functor.map_comp]
  simp

/-- The conjugate of a composite of morphisms of restrictions is the composite of their
conjugates. -/
theorem pullbackHomOfRestrict_comp' {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) {M M' N : Y.Modules}
    (ξ : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj M')
    (ξ' : (restrictFunctor U.ι).obj M' ⟶ (restrictFunctor U.ι).obj N) :
    pullbackHomOfRestrict f e (ξ ≫ ξ') =
      pullbackHomOfRestrict f e ξ ≫ pullbackHomOfRestrict f e ξ' := by
  simp only [pullbackHomOfRestrict, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]

/-- **Naturality.**  The conjugate of the restriction of a morphism of modules on the target is
the restriction of its pullback. -/
theorem pullbackHomOfRestrict_restrictFunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) {M N : Y.Modules} (ψ : M ⟶ N) :
    pullbackHomOfRestrict f e ((restrictFunctor U.ι).map ψ) =
      (restrictFunctor V.ι).map ((pullback f).map ψ) := by
  have hnat := (Stacks.Modules.restrictPullbackIso f e).hom.naturality ψ
  dsimp only [Functor.comp_map] at hnat
  rw [pullbackHomOfRestrict, ← reassoc_of% hnat]
  simp

/-! ### The conjugate of an arbitrary morphism of pullbacks of restrictions -/

/-- The conjugate, by `Stacks.Modules.restrictPullbackIso`, of an arbitrary morphism between the
pullbacks along `f|_V : V ⟶ U` of the restrictions to `U`. -/
noncomputable def restrictHomOfPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) {M N : Y.Modules}
    (χ : (pullback (f.resLE U V e)).obj ((restrictFunctor U.ι).obj M) ⟶
      (pullback (f.resLE U V e)).obj ((restrictFunctor U.ι).obj N)) :
    (restrictFunctor V.ι).obj ((pullback f).obj M) ⟶
      (restrictFunctor V.ι).obj ((pullback f).obj N) :=
  (Stacks.Modules.restrictPullbackIso f e).hom.app M ≫ χ ≫
    (Stacks.Modules.restrictPullbackIso f e).inv.app N

/-! ### The descent condition over one open of a stage -/

/-- The canonical descent condition for a morphism `χ` of the restrictions to an open `W` of a
stage of the pullbacks of `F` and `G`: conjugating `χ` along the limit projection `q` gives, over
the preimage of the open `V` of the base, the restriction of `φ` read through the canonical
identification. -/
def IsChartDescent (q : S ⟶ T) (f : T ⟶ B) (p : S ⟶ B) (hq : q ≫ f = p)
    {V : B.Opens} {W : T.Opens} (eQ : p ⁻¹ᵁ V ≤ q ⁻¹ᵁ W)
    {F G : B.Modules} (φ : (pullback p).obj F ⟶ (pullback p).obj G)
    (χ : (restrictFunctor W.ι).obj ((pullback f).obj F) ⟶
      (restrictFunctor W.ι).obj ((pullback f).obj G)) : Prop :=
  pullbackHomOfRestrict q eQ χ ≫ (restrictFunctor (p ⁻¹ᵁ V).ι).map (canHom q f p hq G) =
    (restrictFunctor (p ⁻¹ᵁ V).ι).map (canHom q f p hq F) ≫
      (restrictFunctor (p ⁻¹ᵁ V).ι).map φ

/-- **The chart datum produced in the canonically pinned pullback form satisfies the descent
condition.** -/
theorem isChartDescent_restrictHomOfPullback (q : S ⟶ T) (f : T ⟶ B) (p : S ⟶ B)
    (hq : q ≫ f = p) {V U : B.Opens} {W : T.Opens}
    (eU : W ≤ f ⁻¹ᵁ U) (eP : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U) (eQ : p ⁻¹ᵁ V ≤ q ⁻¹ᵁ W)
    (hw : q.resLE W (p ⁻¹ᵁ V) eQ ≫ f.resLE U W eU = p.resLE U (p ⁻¹ᵁ V) eP)
    {F G : B.Modules} (φ : (pullback p).obj F ⟶ (pullback p).obj G)
    (φk : (pullback (f.resLE U W eU)).obj ((restrictFunctor U.ι).obj F) ⟶
      (pullback (f.resLE U W eU)).obj ((restrictFunctor U.ι).obj G))
    (hφk : (pullback (q.resLE W (p ⁻¹ᵁ V) eQ)).map φk ≫
        canHom (q.resLE W (p ⁻¹ᵁ V) eQ) (f.resLE U W eU) (p.resLE U (p ⁻¹ᵁ V) eP) hw
          ((restrictFunctor U.ι).obj G) =
      canHom (q.resLE W (p ⁻¹ᵁ V) eQ) (f.resLE U W eU) (p.resLE U (p ⁻¹ᵁ V) eP) hw
          ((restrictFunctor U.ι).obj F) ≫
        ((Stacks.Modules.restrictPullbackIso p eP).inv.app F ≫
          (restrictFunctor (p ⁻¹ᵁ V).ι).map φ ≫
          (Stacks.Modules.restrictPullbackIso p eP).hom.app G)) :
    IsChartDescent q f p hq eQ φ (restrictHomOfPullback f eU φk) := by
  subst hq
  have S : ∀ M : B.Modules,
      (Stacks.Modules.restrictPullbackIso q eQ).hom.app ((pullback f).obj M) ≫
        (pullback (q.resLE W ((q ≫ f) ⁻¹ᵁ V) eQ)).map
          ((Stacks.Modules.restrictPullbackIso f eU).hom.app M) ≫
        canHom (q.resLE W ((q ≫ f) ⁻¹ᵁ V) eQ) (f.resLE U W eU)
          ((q ≫ f).resLE U ((q ≫ f) ⁻¹ᵁ V) eP) hw ((restrictFunctor U.ι).obj M) =
        (restrictFunctor ((q ≫ f) ⁻¹ᵁ V).ι).map (canHom q f (q ≫ f) rfl M) ≫
          (Stacks.Modules.restrictPullbackIso (q ≫ f) eP).hom.app M :=
    restrictPullbackIso_hom_comp q f eU eQ eP
  have SG' : (restrictFunctor ((q ≫ f) ⁻¹ᵁ V).ι).map (canHom q f (q ≫ f) rfl G) =
      (Stacks.Modules.restrictPullbackIso q eQ).hom.app ((pullback f).obj G) ≫
        (pullback (q.resLE W ((q ≫ f) ⁻¹ᵁ V) eQ)).map
          ((Stacks.Modules.restrictPullbackIso f eU).hom.app G) ≫
        canHom (q.resLE W ((q ≫ f) ⁻¹ᵁ V) eQ) (f.resLE U W eU)
            ((q ≫ f).resLE U ((q ≫ f) ⁻¹ᵁ V) eP) hw ((restrictFunctor U.ι).obj G) ≫
          (Stacks.Modules.restrictPullbackIso (q ≫ f) eP).inv.app G := by
    rw [reassoc_of% S G]
    simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  have hinvG : (pullback (q.resLE W ((q ≫ f) ⁻¹ᵁ V) eQ)).map
        ((Stacks.Modules.restrictPullbackIso f eU).inv.app G) ≫
      (Stacks.Modules.restrictPullbackIso q eQ).inv.app ((pullback f).obj G) ≫
        (restrictFunctor ((q ≫ f) ⁻¹ᵁ V).ι).map (canHom q f (q ≫ f) rfl G) =
      canHom (q.resLE W ((q ≫ f) ⁻¹ᵁ V) eQ) (f.resLE U W eU)
          ((q ≫ f).resLE U ((q ≫ f) ⁻¹ᵁ V) eP) hw ((restrictFunctor U.ι).obj G) ≫
        (Stacks.Modules.restrictPullbackIso (q ≫ f) eP).inv.app G := by
    rw [SG', Iso.inv_hom_id_app_assoc, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [IsChartDescent, restrictHomOfPullback, pullbackHomOfRestrict]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hinvG, reassoc_of% hφk, reassoc_of% S F]
  simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

/-- `isChartDescent_restrictHomOfPullback` with the three restricted morphisms taken as abstract
arguments, so that a caller holding them under other names instantiates it by `rfl` instead of
forcing the kernel through a definitional unfolding inside `Scheme.Modules.pullback`. -/
theorem exists_isChartDescent (q : S ⟶ T) (f : T ⟶ B) (p : S ⟶ B)
    (hq : q ≫ f = p) {V U : B.Opens} {W : T.Opens}
    (eU : W ≤ f ⁻¹ᵁ U) (eP : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U) (eQ : p ⁻¹ᵁ V ≤ q ⁻¹ᵁ W)
    {πk : (p ⁻¹ᵁ V).toScheme ⟶ W.toScheme} (hπk : πk = q.resLE W (p ⁻¹ᵁ V) eQ)
    {gk : W.toScheme ⟶ U.toScheme} (hgk : gk = f.resLE U W eU)
    (hw : πk ≫ gk = p.resLE U (p ⁻¹ᵁ V) eP)
    {F G : B.Modules} (φ : (pullback p).obj F ⟶ (pullback p).obj G)
    (φk : (pullback gk).obj ((restrictFunctor U.ι).obj F) ⟶
      (pullback gk).obj ((restrictFunctor U.ι).obj G))
    (hφk : (pullback πk).map φk ≫
        canHom πk gk (p.resLE U (p ⁻¹ᵁ V) eP) hw ((restrictFunctor U.ι).obj G) =
      canHom πk gk (p.resLE U (p ⁻¹ᵁ V) eP) hw ((restrictFunctor U.ι).obj F) ≫
        ((Stacks.Modules.restrictPullbackIso p eP).inv.app F ≫
          (restrictFunctor (p ⁻¹ᵁ V).ι).map φ ≫
          (Stacks.Modules.restrictPullbackIso p eP).hom.app G)) :
    ∃ χ : (restrictFunctor W.ι).obj ((pullback f).obj F) ⟶
        (restrictFunctor W.ι).obj ((pullback f).obj G),
      IsChartDescent q f p hq eQ φ χ := by
  subst hπk
  subst hgk
  exact ⟨_, isChartDescent_restrictHomOfPullback q f p hq eU eP eQ hw φ φk hφk⟩

/-- Two morphisms of restrictions with the same conjugate have the same pullback along the
restricted morphism `f.resLE U V e`. -/
theorem pullback_map_eq_of_pullbackHomOfRestrict_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) {M N : Y.Modules}
    (ξ₁ ξ₂ : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N)
    (h : pullbackHomOfRestrict f e ξ₁ = pullbackHomOfRestrict f e ξ₂) :
    (pullback (f.resLE U V e)).map ξ₁ = (pullback (f.resLE U V e)).map ξ₂ := by
  rw [pullbackHomOfRestrict, pullbackHomOfRestrict] at h
  exact (cancel_mono ((Stacks.Modules.restrictPullbackIso f e).inv.app N)).mp
    ((cancel_epi ((Stacks.Modules.restrictPullbackIso f e).hom.app M)).mp h)

/-! ### Carrying a chart datum to a later stage -/

/-- The characterisation of the transport of a morphism of restrictions over an open `W` of a
stage to an open `W'` of a later stage: its conjugate along the transition morphism `w`, read
through the canonical identification of the iterated pullback with the pullback of the
composite. -/
def IsStageTransport (w : T' ⟶ T) (f : T ⟶ B) (f' : T' ⟶ B) (hf : w ≫ f = f')
    {W : T.Opens} {W' : T'.Opens} (eW : W' ≤ w ⁻¹ᵁ W) {F G : B.Modules}
    (χ : (restrictFunctor W.ι).obj ((pullback f).obj F) ⟶
      (restrictFunctor W.ι).obj ((pullback f).obj G))
    (χ' : (restrictFunctor W'.ι).obj ((pullback f').obj F) ⟶
      (restrictFunctor W'.ι).obj ((pullback f').obj G)) : Prop :=
  (restrictFunctor W'.ι).map (canHom w f f' hf F) ≫ χ' =
    pullbackHomOfRestrict w eW χ ≫ (restrictFunctor W'.ι).map (canHom w f f' hf G)

/-- Every morphism of restrictions over an open `W` of a stage has a transport to any open `W'`
of a later stage contained in the preimage of `W`. -/
theorem exists_isStageTransport (w : T' ⟶ T) (f : T ⟶ B) (f' : T' ⟶ B) (hf : w ≫ f = f')
    {W : T.Opens} {W' : T'.Opens} (eW : W' ≤ w ⁻¹ᵁ W) {F G : B.Modules}
    (χ : (restrictFunctor W.ι).obj ((pullback f).obj F) ⟶
      (restrictFunctor W.ι).obj ((pullback f).obj G)) :
    ∃ χ' : (restrictFunctor W'.ι).obj ((pullback f').obj F) ⟶
      (restrictFunctor W'.ι).obj ((pullback f').obj G),
      IsStageTransport w f f' hf eW χ χ' := by
  refine ⟨CategoryTheory.inv ((restrictFunctor W'.ι).map (canHom w f f' hf F)) ≫
    pullbackHomOfRestrict w eW χ ≫ (restrictFunctor W'.ι).map (canHom w f f' hf G), ?_⟩
  rw [IsStageTransport, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- Two transports of morphisms with the same conjugate along the transition morphism agree. -/
theorem eq_of_isStageTransport (w : T' ⟶ T) (f : T ⟶ B) (f' : T' ⟶ B) (hf : w ≫ f = f')
    {W : T.Opens} {W' : T'.Opens} (eW : W' ≤ w ⁻¹ᵁ W) {F G : B.Modules}
    {χ₁ χ₂ : (restrictFunctor W.ι).obj ((pullback f).obj F) ⟶
      (restrictFunctor W.ι).obj ((pullback f).obj G)}
    {χ₁' χ₂' : (restrictFunctor W'.ι).obj ((pullback f').obj F) ⟶
      (restrictFunctor W'.ι).obj ((pullback f').obj G)}
    (h₁ : IsStageTransport w f f' hf eW χ₁ χ₁')
    (h₂ : IsStageTransport w f f' hf eW χ₂ χ₂')
    (h : (pullback (w.resLE W W' eW)).map χ₁ = (pullback (w.resLE W W' eW)).map χ₂) :
    χ₁' = χ₂' := by
  rw [IsStageTransport] at h₁ h₂
  refine (cancel_epi ((restrictFunctor W'.ι).map (canHom w f f' hf F))).mp ?_
  rw [h₁, h₂, pullbackHomOfRestrict, pullbackHomOfRestrict, h]

/-- **The restriction of a transport is the transport of the restriction.** -/
theorem isStageTransport_restrictHomOfLE (w : T' ⟶ T) (f : T ⟶ B) (f' : T' ⟶ B)
    (hf : w ≫ f = f') {W Wab : T.Opens} {W' W'' : T'.Opens} (hU : Wab ≤ W) (hV : W'' ≤ W')
    (eW : W' ≤ w ⁻¹ᵁ W) (eW'' : W'' ≤ w ⁻¹ᵁ Wab) {F G : B.Modules}
    {χ : (restrictFunctor W.ι).obj ((pullback f).obj F) ⟶
      (restrictFunctor W.ι).obj ((pullback f).obj G)}
    {χ' : (restrictFunctor W'.ι).obj ((pullback f').obj F) ⟶
      (restrictFunctor W'.ι).obj ((pullback f').obj G)}
    (h : IsStageTransport w f f' hf eW χ χ') :
    IsStageTransport w f f' hf eW'' (restrictHomOfLE hU χ) (restrictHomOfLE hV χ') := by
  rw [IsStageTransport] at h
  have hr := congrArg (restrictHomOfLE hV) h
  rwa [restrictHomOfLE_comp, restrictHomOfLE_comp, restrictHomOfLE_restrictFunctor_map,
    restrictHomOfLE_restrictFunctor_map,
    restrictHomOfLE_pullbackHomOfRestrict_comm w hU hV eW eW''] at hr

/-- **A chart datum transported to a later stage still satisfies the descent condition.** -/
theorem isChartDescent_of_isStageTransport
    (q : S ⟶ T) (q' : S ⟶ T') (w : T' ⟶ T) (f : T ⟶ B) (f' : T' ⟶ B) (p : S ⟶ B)
    (hqw : q' ≫ w = q) (hf : w ≫ f = f') (hq : q ≫ f = p) (hq' : q' ≫ f' = p)
    {V : B.Opens} {W : T.Opens} {W' : T'.Opens}
    (eQ : p ⁻¹ᵁ V ≤ q ⁻¹ᵁ W) (eW : W' ≤ w ⁻¹ᵁ W) (eQ' : p ⁻¹ᵁ V ≤ q' ⁻¹ᵁ W')
    {F G : B.Modules} (φ : (pullback p).obj F ⟶ (pullback p).obj G)
    {χ : (restrictFunctor W.ι).obj ((pullback f).obj F) ⟶
      (restrictFunctor W.ι).obj ((pullback f).obj G)}
    {χ' : (restrictFunctor W'.ι).obj ((pullback f').obj F) ⟶
      (restrictFunctor W'.ι).obj ((pullback f').obj G)}
    (hχ : IsChartDescent q f p hq eQ φ χ) (ht : IsStageTransport w f f' hf eW χ χ') :
    IsChartDescent q' f' p hq' eQ' φ χ' := by
  subst hqw
  rw [IsStageTransport] at ht
  have h1 := congrArg (pullbackHomOfRestrict q' eQ') ht
  rw [pullbackHomOfRestrict_comp', pullbackHomOfRestrict_comp',
    pullbackHomOfRestrict_restrictFunctor_map,
    pullbackHomOfRestrict_restrictFunctor_map] at h1
  have hC := pullbackHomOfRestrict_comp q' w eW eQ' eQ χ
  have hr : ∀ M : B.Modules,
      (restrictFunctor (p ⁻¹ᵁ V).ι).map ((pullback q').map (canHom w f f' hf M)) ≫
      (restrictFunctor (p ⁻¹ᵁ V).ι).map (canHom q' f' p hq' M) =
      (restrictFunctor (p ⁻¹ᵁ V).ι).map
          (canHom q' w (q' ≫ w) rfl ((pullback f).obj M)) ≫
        (restrictFunctor (p ⁻¹ᵁ V).ι).map (canHom (q' ≫ w) f p hq M) := fun M => by
    have hc := canHom_comp q' w f (q' ≫ w) rfl f' hf p hq hq' M
    simp only [canNatIso_hom_app] at hc
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hc]
  rw [IsChartDescent] at hχ ⊢
  rw [← cancel_epi ((restrictFunctor (p ⁻¹ᵁ V).ι).map
      ((pullback q').map (canHom w f f' hf F))), ← Category.assoc, h1, Category.assoc,
    hr G, reassoc_of% hC, hχ, reassoc_of% hr F]

/-! ### Agreement of two chart data on the overlap, in the limit -/

/-- **Two chart data satisfying the descent condition for the same `φ` agree on the overlap after
pulling back to the limit.**  This is `restrictHomOfLE_pullbackHomOfRestrict_comm` — the
compatibility of the conjugation with shrinking both opens — together with the invertibility of
the canonical identification. -/
theorem pullback_map_restrictHomOfLE_eq_of_isChartDescent
    (q : S ⟶ T) (f : T ⟶ B) (p : S ⟶ B) (hq : q ≫ f = p)
    {Va Vb Vab : B.Opens} {Wa Wb Wab : T.Opens}
    (eQa : p ⁻¹ᵁ Va ≤ q ⁻¹ᵁ Wa) (eQb : p ⁻¹ᵁ Vb ≤ q ⁻¹ᵁ Wb)
    (eQab : p ⁻¹ᵁ Vab ≤ q ⁻¹ᵁ Wab) (hUa : Wab ≤ Wa) (hUb : Wab ≤ Wb)
    (hVa : p ⁻¹ᵁ Vab ≤ p ⁻¹ᵁ Va) (hVb : p ⁻¹ᵁ Vab ≤ p ⁻¹ᵁ Vb)
    {F G : B.Modules} (φ : (pullback p).obj F ⟶ (pullback p).obj G)
    {χa : (restrictFunctor Wa.ι).obj ((pullback f).obj F) ⟶
      (restrictFunctor Wa.ι).obj ((pullback f).obj G)}
    {χb : (restrictFunctor Wb.ι).obj ((pullback f).obj F) ⟶
      (restrictFunctor Wb.ι).obj ((pullback f).obj G)}
    (ha : IsChartDescent q f p hq eQa φ χa) (hb : IsChartDescent q f p hq eQb φ χb) :
    (pullback (q.resLE Wab (p ⁻¹ᵁ Vab) eQab)).map (restrictHomOfLE hUa χa) =
      (pullback (q.resLE Wab (p ⁻¹ᵁ Vab) eQab)).map (restrictHomOfLE hUb χb) := by
  have key : ∀ {Vx : B.Opens} {Wx : T.Opens} (eQx : p ⁻¹ᵁ Vx ≤ q ⁻¹ᵁ Wx) (hU : Wab ≤ Wx)
      (hV : p ⁻¹ᵁ Vab ≤ p ⁻¹ᵁ Vx)
      {χ : (restrictFunctor Wx.ι).obj ((pullback f).obj F) ⟶
        (restrictFunctor Wx.ι).obj ((pullback f).obj G)},
      IsChartDescent q f p hq eQx φ χ →
      pullbackHomOfRestrict q eQab (restrictHomOfLE hU χ) ≫
          (restrictFunctor (p ⁻¹ᵁ Vab).ι).map (canHom q f p hq G) =
        (restrictFunctor (p ⁻¹ᵁ Vab).ι).map (canHom q f p hq F) ≫
          (restrictFunctor (p ⁻¹ᵁ Vab).ι).map φ := by
    intro Vx Wx eQx hU hV χ h
    rw [IsChartDescent] at h
    have k := congrArg (restrictHomOfLE hV) h
    rwa [restrictHomOfLE_comp, restrictHomOfLE_comp,
      restrictHomOfLE_pullbackHomOfRestrict_comm q hU hV eQx eQab,
      restrictHomOfLE_restrictFunctor_map, restrictHomOfLE_restrictFunctor_map,
      restrictHomOfLE_restrictFunctor_map] at k
  refine pullback_map_eq_of_pullbackHomOfRestrict_eq q eQab _ _ ?_
  refine (cancel_mono ((restrictFunctor (p ⁻¹ᵁ Vab).ι).map (canHom q f p hq G))).mp ?_
  rw [key eQa hUa hVa ha, key eQb hUb hVb hb]

/-! ### The chart step in descent-condition form -/

section Stage

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Limits.Cone D)

/-- The three definitional comparisons of opens that the chart step needs: the preimage of `V`
in a stage over `i` is contained in the preimage of the base open, the same at the limit, and the
resulting triangle of restricted morphisms commutes.  Packaged in one declaration so that the
chart step itself performs no unfolding. -/
theorem exists_chartComparisons (i : I) {V : (D.obj i).Opens} {k : Over i}
    (hk : k ⟶ Over.mk (𝟙 i))
    (eQ : c.π.app i ⁻¹ᵁ V ≤ c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V)) :
    ∃ (eU : D.map k.hom ⁻¹ᵁ V ≤ D.map hk.left ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V))
      (eP : c.π.app i ⁻¹ᵁ V ≤ c.π.app i ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V)),
      (c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) eQ ≫
          (D.map hk.left).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU =
        (c.π.app i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) eP := by
  have hkl : hk.left ≫ 𝟙 i = k.hom := Over.w hk
  have eU : D.map k.hom ⁻¹ᵁ V ≤ D.map hk.left ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← D.map_comp, hkl]
  exact ⟨eU, Scheme.Hom.preimage_mono (c.π.app i) (show V ≤ D.map (𝟙 i) ⁻¹ᵁ V by simp),
    (EventualLimit.preimageCone D c i V).w hk⟩

/-- The chart datum of
`Stacks.AlgebraicGeometry.ModuleLimits.exists_over_map_of_isAffineOpen_stage`, read as a morphism
between the pullbacks along the transition morphism spelled as an
`AlgebraicGeometry.Scheme.Hom.resLE`.  The two types are definitionally equal; the conversion is
isolated here so that no consumer repeats it. -/
noncomputable def descentDatum_resLE (i : I) {V : (D.obj i).Opens} {k : Over i}
    (hk : k ⟶ Over.mk (𝟙 i))
    (eU : D.map k.hom ⁻¹ᵁ V ≤ D.map hk.left ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V))
    (F G : (D.obj i).Modules)
    (φk : (pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
      (pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G)) :
    (pullback ((D.map hk.left).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
      (pullback ((D.map hk.left).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G) :=
  φk

/-- The canonical descent equation produced by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_over_map_of_isAffineOpen_stage`, with the data of
`AlgebraicGeometry.EventualLimit.preimageCone` and
`AlgebraicGeometry.EventualLimit.preimageDiagram` spelled as the
`AlgebraicGeometry.Scheme.Hom.resLE` they are and the comparison isomorphism read at the level of
natural transformations.

The conversion is definitional throughout, and it is carried out in a declaration of its own:
performing it inside the application of
`Stacks.AlgebraicGeometry.ModuleLimits.isChartDescent_restrictHomOfPullback` makes the elaborator
exceed its budget, while either half alone is well inside it. -/
theorem canonicalDescent_resLE (i : I) {V : (D.obj i).Opens} {k : Over i}
    (hk : k ⟶ Over.mk (𝟙 i))
    (eQ : c.π.app i ⁻¹ᵁ V ≤ c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V))
    (eU : D.map k.hom ⁻¹ᵁ V ≤ D.map hk.left ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V))
    (eP : c.π.app i ⁻¹ᵁ V ≤ c.π.app i ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V))
    (hw : (c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) eQ ≫
        (D.map hk.left).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU =
      (c.π.app i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) eP)
    (F G : (D.obj i).Modules)
    (φ : (pullback (c.π.app i)).obj F ⟶ (pullback (c.π.app i)).obj G)
    {ψ : (pullback ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
      (pullback ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G)}
    (hψ : ψ = ((Stacks.Modules.restrictPullbackIso (c.π.app i) eP).app F).inv ≫
      (restrictFunctor (c.π.app i ⁻¹ᵁ V).ι).map φ ≫
      ((Stacks.Modules.restrictPullbackIso (c.π.app i) eP).app G).hom)
    (φk : (pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
      (pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G))
    (hφk : (pullback ((EventualLimit.preimageCone D c i V).π.app k)).map φk ≫
        canHom ((EventualLimit.preimageCone D c i V).π.app k)
          ((EventualLimit.preimageDiagram D i V).map hk)
          ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))
          ((EventualLimit.preimageCone D c i V).w hk)
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G) =
      canHom ((EventualLimit.preimageCone D c i V).π.app k)
          ((EventualLimit.preimageDiagram D i V).map hk)
          ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))
          ((EventualLimit.preimageCone D c i V).w hk)
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ≫ ψ) :
    (pullback ((c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) eQ)).map
          (descentDatum_resLE D i hk eU F G φk) ≫
        canHom ((c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) eQ)
          ((D.map hk.left).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)
          ((c.π.app i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) eP) hw
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G) =
      canHom ((c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) eQ)
          ((D.map hk.left).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)
          ((c.π.app i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) eP) hw
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ≫
        ((Stacks.Modules.restrictPullbackIso (c.π.app i) eP).inv.app F ≫
          (restrictFunctor (c.π.app i ⁻¹ᵁ V).ι).map φ ≫
          (Stacks.Modules.restrictPullbackIso (c.π.app i) eP).hom.app G) := by
  subst hψ
  exact hφk

/-! ### The chart step in descent-condition form, over a projection of the cone -/

/-- The projection of a cone onto one of its legs, with its source spelled as the vertex of the
cone.

`c.π.app j` has source `((CategoryTheory.Functor.const I).obj c.pt).obj j`, a different expression
for each `j`.  Reading the projections through this definition instead makes a statement that
mentions two of them uniform in the scheme they start from, which is what lets such a statement be
handed to a lemma quantified over morphisms with a common source. -/
def coneProj (j : I) : c.pt ⟶ D.obj j := c.π.app j

/-- The transition morphism attached to a morphism of `CategoryTheory.Over i` into the terminal
object, with its target spelled `D.obj i`.

As with `coneProj`, the point is the spelling: the target of `D.map hk.left` is
`D.obj (CategoryTheory.Over.mk (𝟙 i)).left`. -/
def stageHom {i : I} {k : Over i} (hk : k ⟶ Over.mk (𝟙 i)) : D.obj k.left ⟶ D.obj i :=
  D.map hk.left

/-- The projection at a stage over `i`, followed by the transition morphism to `i`, is the
projection at `i`. -/
theorem coneProj_comp_stageHom {i : I} {k : Over i} (hk : k ⟶ Over.mk (𝟙 i)) :
    coneProj D c k.left ≫ stageHom D hk = coneProj D c i :=
  c.w hk.left

variable (i : I) {V : (D.obj i).Opens} {k : Over i}

/-- `descentDatum_resLE` with the transition morphism spelled `stageHom`: the chart datum of
`Stacks.AlgebraicGeometry.ModuleLimits.exists_over_map_of_isAffineOpen_stage`, read as a morphism
between the pullbacks along `stageHom D hk` restricted to the two opens.  The two types are
definitionally equal; the conversion is isolated here so that no consumer repeats it. -/
noncomputable def descentDatum_stageHom (hk : k ⟶ Over.mk (𝟙 i))
    (eU : D.map k.hom ⁻¹ᵁ V ≤ stageHom D hk ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V))
    (F G : (D.obj i).Modules)
    (φk : (pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
      (pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G)) :
    (pullback ((stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
      (pullback ((stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G) :=
  φk

/-- `canonicalDescent_resLE` with the two projections and the transition morphism spelled
`coneProj` and `stageHom`.

This is the statement of the canonical descent equation that
`isChartDescent_restrictHomOfPullback` instantiates to, so feeding this to it needs no conversion
at all; see the implementation notes. -/
theorem canonicalDescent_coneProj (hk : k ⟶ Over.mk (𝟙 i))
    (eQ : coneProj D c i ⁻¹ᵁ V ≤ coneProj D c k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V))
    (eU : D.map k.hom ⁻¹ᵁ V ≤ stageHom D hk ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V))
    (eP : coneProj D c i ⁻¹ᵁ V ≤ coneProj D c i ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V))
    (hw : (coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eQ ≫
        (stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU =
      (coneProj D c i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eP)
    (F G : (D.obj i).Modules)
    (φ : (pullback (coneProj D c i)).obj F ⟶ (pullback (coneProj D c i)).obj G)
    {ψ : (pullback ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
      (pullback ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G)}
    (hψ : ψ = ((Stacks.Modules.restrictPullbackIso (coneProj D c i) eP).app F).inv ≫
      (restrictFunctor (coneProj D c i ⁻¹ᵁ V).ι).map φ ≫
      ((Stacks.Modules.restrictPullbackIso (coneProj D c i) eP).app G).hom)
    (φk : (pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
      (pullback ((EventualLimit.preimageDiagram D i V).map hk)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G))
    (hφk : (pullback ((EventualLimit.preimageCone D c i V).π.app k)).map φk ≫
        canHom ((EventualLimit.preimageCone D c i V).π.app k)
          ((EventualLimit.preimageDiagram D i V).map hk)
          ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))
          ((EventualLimit.preimageCone D c i V).w hk)
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G) =
      canHom ((EventualLimit.preimageCone D c i V).π.app k)
          ((EventualLimit.preimageDiagram D i V).map hk)
          ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))
          ((EventualLimit.preimageCone D c i V).w hk)
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ≫ ψ) :
    (pullback ((coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eQ)).map
          (descentDatum_stageHom D i hk eU F G φk) ≫
        canHom ((coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eQ)
          ((stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)
          ((coneProj D c i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eP) hw
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G) =
      canHom ((coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eQ)
          ((stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)
          ((coneProj D c i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eP) hw
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ≫
        ((Stacks.Modules.restrictPullbackIso (coneProj D c i) eP).inv.app F ≫
          (restrictFunctor (coneProj D c i ⁻¹ᵁ V).ι).map φ ≫
          (Stacks.Modules.restrictPullbackIso (coneProj D c i) eP).hom.app G) := by
  subst hψ
  exact hφk

/-- `isChartDescent_restrictHomOfPullback` at a projection of the cone: the canonical descent
equation in the form `canonicalDescent_coneProj` produces it gives a morphism of the restrictions
to the preimage of `V` at the stage satisfying the descent condition. -/
theorem exists_isChartDescent_coneProj (hk : k ⟶ Over.mk (𝟙 i))
    (eQ : coneProj D c i ⁻¹ᵁ V ≤ coneProj D c k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V))
    (eU : D.map k.hom ⁻¹ᵁ V ≤ stageHom D hk ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V))
    (eP : coneProj D c i ⁻¹ᵁ V ≤ coneProj D c i ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V))
    (hw : (coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eQ ≫
        (stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU =
      (coneProj D c i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eP)
    (F G : (D.obj i).Modules)
    (φ : (pullback (coneProj D c i)).obj F ⟶ (pullback (coneProj D c i)).obj G)
    (φk : (pullback ((stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ⟶
      (pullback ((stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)).obj
        ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G))
    (hφk : (pullback ((coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ V)
            (coneProj D c i ⁻¹ᵁ V) eQ)).map φk ≫
        canHom ((coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eQ)
          ((stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)
          ((coneProj D c i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eP) hw
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj G) =
      canHom ((coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eQ)
          ((stageHom D hk).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V) eU)
          ((coneProj D c i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (coneProj D c i ⁻¹ᵁ V) eP) hw
          ((restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj F) ≫
        ((Stacks.Modules.restrictPullbackIso (coneProj D c i) eP).inv.app F ≫
          (restrictFunctor (coneProj D c i ⁻¹ᵁ V).ι).map φ ≫
          (Stacks.Modules.restrictPullbackIso (coneProj D c i) eP).hom.app G)) :
    ∃ χ : (restrictFunctor (D.map k.hom ⁻¹ᵁ V).ι).obj ((pullback (stageHom D hk)).obj F) ⟶
        (restrictFunctor (D.map k.hom ⁻¹ᵁ V).ι).obj ((pullback (stageHom D hk)).obj G),
      IsChartDescent (coneProj D c k.left) (stageHom D hk) (coneProj D c i)
        (coneProj_comp_stageHom D c hk) eQ φ χ :=
  ⟨_, isChartDescent_restrictHomOfPullback _ _ _ (coneProj_comp_stageHom D c hk)
    eU eP eQ hw φ φk hφk⟩

section Affine

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- **The chart step of Tag 01ZR (2) in descent-condition form, at every later stage.**  Let `V`
be an affine open of the stage `D.obj i` and let `φ` be a morphism between the pullbacks to the
limit of two finitely presented modules on `D.obj i`.  Then there is a stage `j` over `i` such
that for *every* stage `k` over `i` admitting a morphism to `j` there is a morphism of the
restrictions to the preimage of `V` at `k` satisfying `IsChartDescent`.

This is `exists_over_map_of_isAffineOpen` followed by `exists_canonical_of_terminal_base`,
`canonicalDescent_coneProj` and `exists_isChartDescent_coneProj`.  It is the form in which the
finitely many charts of a covering of a stage can be glued. -/
theorem exists_isChartDescent_of_isAffineOpen (hc : Limits.IsLimit c) (hV : IsAffineOpen V)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (pullback (coneProj D c i)).obj F ⟶ (pullback (coneProj D c i)).obj G) :
    ∃ j : Over i, ∀ (k : Over i) (hk : k ⟶ Over.mk (𝟙 i)), (k ⟶ j) →
      ∀ eQ : coneProj D c i ⁻¹ᵁ V ≤ coneProj D c k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V),
        ∃ χ : (restrictFunctor (D.map k.hom ⁻¹ᵁ V).ι).obj ((pullback (stageHom D hk)).obj F) ⟶
            (restrictFunctor (D.map k.hom ⁻¹ᵁ V).ι).obj ((pullback (stageHom D hk)).obj G),
          IsChartDescent (coneProj D c k.left) (stageHom D hk) (coneProj D c i)
            (coneProj_comp_stageHom D c hk) eQ φ χ := by
  obtain ⟨j, e, φj, hφj⟩ := exists_over_map_of_isAffineOpen D c hc i hV F G φ
  refine ⟨j, fun k hk m eQ => ?_⟩
  obtain ⟨φk, hφk⟩ := exists_canonical_of_terminal_base
    (EventualLimit.preimageDiagram D i V) (EventualLimit.preimageCone D c i V) _ e φj hφj k hk m
  obtain ⟨eU, eP, hw⟩ := exists_chartComparisons D c i hk eQ
  exact exists_isChartDescent_coneProj D c i hk eQ eU eP hw F G φ
    (descentDatum_stageHom D i hk eU F G φk)
    (canonicalDescent_coneProj D c i hk eQ eU eP hw F G φ rfl φk hφk)

end Affine

end Stage




end Stacks.AlgebraicGeometry.ModuleLimits

end
