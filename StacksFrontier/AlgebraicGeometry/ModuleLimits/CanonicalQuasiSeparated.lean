module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalLocal
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalConsequences
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01ZR (2) for quasi-compact quasi-separated stages

This file proves [Stacks Project, Tag 01ZR] (2) for a cofiltered diagram of quasi-compact
quasi-separated schemes with affine transition morphisms, in the canonically pinned form
`Stacks.AlgebraicGeometry.ModuleLimits.HasCanonicalDescent`: a morphism between the pullbacks to
the limit of two finitely presented modules on a stage is, after passing to a later stage, the
base change of a morphism there *through the canonical identification*.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.preimageStageIncl`: the morphism `D k ⁻¹ᵁ V ⟶ D i`
  obtained from the inclusion of the preimage of an open `V` of the stage `D i` followed by the
  transition morphism.  A *local piece* of a descended morphism is a morphism of the pullbacks
  along it.
* `Stacks.AlgebraicGeometry.ModuleLimits.preimageTrans` and `...preimageConeπ`: the transition
  morphisms of the preimages of `V`, and the projections from the preimage of `V` in the limit,
  written with the open subschemes themselves as source and target.
* `Stacks.AlgebraicGeometry.ModuleLimits.limitRestrict`: a morphism of pullbacks to the limit,
  restricted to the preimage of an open of a stage.
* `Stacks.AlgebraicGeometry.ModuleLimits.overlapRestrict`: a local piece, restricted to a smaller
  open of the base stage.
* `Stacks.AlgebraicGeometry.ModuleLimits.stagePush`: a local piece, pushed to a later stage.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_of_isAffineOpen`: the local piece over
  one member of an affine covering of the stage.
* `Stacks.AlgebraicGeometry.ModuleLimits.hasCanonicalDescent_of_isLimit` and
  `...hasCanonicalDescent_of_isLimit'`: **[Stacks Project, Tag 01ZR] (2)** in the canonically
  pinned form, the second with the index morphism universe unrestricted.

## Implementation notes

The argument is Zariski glueing over a *finite* affine open covering `V a` of the stage `D i`,
and it is organised so that every object in play is a morphism of pullbacks along a morphism to
`D i` — never a morphism of restrictions.  The local piece attached to a member `V a` of the
covering and a stage `k` over `i` is a morphism of the pullbacks along
`preimageStageIncl D i (V a) k`, and the three operations performed on it are
`overlapRestrict` (pass to a smaller open of `D i`), `stagePush` (pass to a later stage) and
`Stacks.AlgebraicGeometry.ModuleLimits.canConj` (read it through a canonical identification).
All three are `canConj` of a pullback, so
`Stacks.AlgebraicGeometry.ModuleLimits.canConj_canConj` — the cocycle — is the only coherence
ever needed, and the comparison of the pullback along an open immersion with the restriction
functor never appears.

The two steps of the argument that need a hypothesis beyond the affine case are:

* the two local pieces over `V a` and over `V b` need only agree *eventually*, which is
  [Stacks Project, Tag 01ZR] (3) applied to the diagram of preimages of `V a ⊓ V b`.  That open
  is quasi-compact because `D i` is quasi-separated, and its preimage in a later stage is
  quasi-compact because the transition morphisms are affine, hence quasi-compact;
* the finitely many stages the pairs produce have to be brought under one *morphism* to the
  common stage, not merely under one object: the local pieces are pushed along a chosen
  transition morphism, so the agreement is needed for that same morphism.  Objects of
  `CategoryTheory.Over k₀` are exactly morphisms to `k₀`, and `Over k₀` is cofiltered
  (`CategoryTheory.IsCofiltered.over`), so `CategoryTheory.IsCofiltered.inf_objs_exists` there
  produces the common morphism.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

/-! ### The stages of the diagram of preimages of an open of a stage -/

/-- The preimage in a later stage of a quasi-compact open of a stage is quasi-compact, so every
stage of the diagram of preimages of a quasi-compact open is a quasi-compact scheme. -/
theorem compactSpace_preimageDiagram_obj {I : Type*} [Category I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (i : I) {U : (D.obj i).Opens}
    (hU : IsCompact (U : Set (D.obj i))) (k : Over i) :
    CompactSpace ((EventualLimit.preimageDiagram D i U).obj k) :=
  isCompact_iff_compactSpace.mp ((D.map k.hom).isCompact_preimage hU)

/-! ### The local pieces of a descended morphism -/

section Pieces

variable {I : Type*} [Category I] (D : I ⥤ Scheme.{u}) (i : I)

/-- The morphism `D k ⁻¹ᵁ V ⟶ D i` attached to an open `V` of the stage `D i` and an index `k`
over `i`: the inclusion of the preimage of `V` followed by the transition morphism.  A *local
piece* of a morphism descended to the stage `k` is a morphism of the pullbacks along this
morphism. -/
noncomputable abbrev preimageStageIncl (V : (D.obj i).Opens) (k : Over i) :
    (D.map k.hom ⁻¹ᵁ V).toScheme ⟶ D.obj i :=
  (D.map k.hom ⁻¹ᵁ V).ι ≫ D.map k.hom

/-- The transition morphism between the preimages of `V` in two stages.  This is the value of
`AlgebraicGeometry.EventualLimit.preimageDiagram` on a morphism of `CategoryTheory.Over i`,
written so that its source and target are the open subschemes themselves. -/
noncomputable abbrev preimageTrans (V : (D.obj i).Opens) {k₁ k₀ : Over i} (v : k₁ ⟶ k₀) :
    (D.map k₁.hom ⁻¹ᵁ V).toScheme ⟶ (D.map k₀.hom ⁻¹ᵁ V).toScheme :=
  (D.map v.left).resLE _ _ (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w v])

/-- The projection from the preimage of `V` in the limit to its preimage in a stage.  This is the
value of `AlgebraicGeometry.EventualLimit.preimageCone`, written so that its source and target
are the open subschemes themselves. -/
noncomputable abbrev preimageConeπ (c : Cone D) (V : (D.obj i).Opens) (k : Over i) :
    (c.π.app i ⁻¹ᵁ V).toScheme ⟶ (D.map k.hom ⁻¹ᵁ V).toScheme :=
  (c.π.app k.left).resLE _ _ (by rw [← Scheme.Hom.comp_preimage, c.w])

/-- Restricting to a smaller open and then including into the stage is including into the
stage. -/
theorem homOfLE_comp_preimageStageIncl (k : Over i) {V P : (D.obj i).Opens} (hPV : P ≤ V) :
    (D.obj k.left).homOfLE (Scheme.Hom.preimage_mono (D.map k.hom) hPV) ≫
        preimageStageIncl D i V k
      = preimageStageIncl D i P k := by
  rw [preimageStageIncl, preimageStageIncl, ← Category.assoc, Scheme.homOfLE_ι]

/-- The transition morphism of the preimages of `V` composed with the inclusion into the earlier
stage is the inclusion into the later stage. -/
theorem preimageTrans_comp_preimageStageIncl (V : (D.obj i).Opens) {k₁ k₀ : Over i} (v : k₁ ⟶ k₀) :
    preimageTrans D i V v ≫ preimageStageIncl D i V k₀ = preimageStageIncl D i V k₁ := by
  rw [preimageStageIncl, preimageStageIncl, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι (D.map v.left) _, Category.assoc, ← D.map_comp, Over.w v]

/-- Restricting to a smaller open commutes with passing to a later stage. -/
theorem homOfLE_comp_preimageTrans {V P : (D.obj i).Opens} (hPV : P ≤ V) {k₁ k₀ : Over i}
    (v : k₁ ⟶ k₀) :
    (D.obj k₁.left).homOfLE (Scheme.Hom.preimage_mono (D.map k₁.hom) hPV) ≫
          preimageTrans D i V v
      = preimageTrans D i P v ≫
          (D.obj k₀.left).homOfLE (Scheme.Hom.preimage_mono (D.map k₀.hom) hPV) := by
  refine (cancel_mono (D.map k₀.hom ⁻¹ᵁ V).ι).mp ?_
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι (D.map v.left) _, ← Category.assoc,
    Scheme.homOfLE_ι, Category.assoc, Scheme.homOfLE_ι,
    Scheme.Hom.resLE_comp_ι (D.map v.left) _]

/-- The projection to a stage followed by the inclusion of the preimage of `V` into that stage is
the inclusion of the preimage of `V` in the limit, followed by the projection. -/
theorem preimageConeπ_comp_preimageStageIncl (c : Cone D) (V : (D.obj i).Opens) (k : Over i) :
    preimageConeπ D i c V k ≫ preimageStageIncl D i V k
      = (c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i := by
  rw [preimageStageIncl, ← Category.assoc, Scheme.Hom.resLE_comp_ι (c.π.app k.left) _,
    Category.assoc, c.w]

/-- The projection from the limit to a stage factors through the projection to a later stage. -/
theorem preimageConeπ_comp_preimageTrans (c : Cone D) (V : (D.obj i).Opens) {k₁ k₀ : Over i}
    (v : k₁ ⟶ k₀) :
    preimageConeπ D i c V k₁ ≫ preimageTrans D i V v = preimageConeπ D i c V k₀ := by
  refine (cancel_mono (D.map k₀.hom ⁻¹ᵁ V).ι).mp ?_
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι (D.map v.left) _, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι (c.π.app k₁.left) _, Category.assoc, c.w v.left,
    Scheme.Hom.resLE_comp_ι (c.π.app k₀.left) _]

/-- Restricting to a smaller open commutes with the projection from the limit. -/
theorem preimageConeπ_comp_homOfLE (c : Cone D) {V P : (D.obj i).Opens} (hPV : P ≤ V)
    (k : Over i) :
    preimageConeπ D i c P k ≫
          (D.obj k.left).homOfLE (Scheme.Hom.preimage_mono (D.map k.hom) hPV)
      = c.pt.homOfLE (Scheme.Hom.preimage_mono (c.π.app i) hPV) ≫ preimageConeπ D i c V k := by
  refine (cancel_mono (D.map k.hom ⁻¹ᵁ V).ι).mp ?_
  have e1 : (preimageConeπ D i c P k ≫ (D.obj k.left).homOfLE
        (Scheme.Hom.preimage_mono (D.map k.hom) hPV)) ≫ (D.map k.hom ⁻¹ᵁ V).ι
      = (c.π.app i ⁻¹ᵁ P).ι ≫ c.π.app k.left := by
    rw [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι (c.π.app k.left) _]
  have e2 : (c.pt.homOfLE (Scheme.Hom.preimage_mono (c.π.app i) hPV) ≫
        preimageConeπ D i c V k) ≫ (D.map k.hom ⁻¹ᵁ V).ι
      = (c.π.app i ⁻¹ᵁ P).ι ≫ c.π.app k.left := by
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι (c.π.app k.left) _, ← Category.assoc]
    exact congrArg (fun z => z ≫ c.π.app k.left) (Scheme.homOfLE_ι _ _)
  rw [e1, e2]

/-- The restriction of a local piece over `V` to a smaller open `P` of `D i`. -/
noncomputable def overlapRestrict (k : Over i) {V P : (D.obj i).Opens} (hPV : P ≤ V)
    {F G : (D.obj i).Modules}
    (X : (Scheme.Modules.pullback (preimageStageIncl D i V k)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i V k)).obj G) :
    (Scheme.Modules.pullback (preimageStageIncl D i P k)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i P k)).obj G :=
  canConj ((D.obj k.left).homOfLE (Scheme.Hom.preimage_mono (D.map k.hom) hPV))
    (preimageStageIncl D i V k) (preimageStageIncl D i P k)
    (homOfLE_comp_preimageStageIncl D i k hPV)
    ((Scheme.Modules.pullback
      ((D.obj k.left).homOfLE (Scheme.Hom.preimage_mono (D.map k.hom) hPV))).map X)

/-- A local piece over `V`, pushed to a later stage. -/
noncomputable def stagePush {k₁ k₀ : Over i} (v : k₁ ⟶ k₀) (V : (D.obj i).Opens)
    {F G : (D.obj i).Modules}
    (X : (Scheme.Modules.pullback (preimageStageIncl D i V k₀)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i V k₀)).obj G) :
    (Scheme.Modules.pullback (preimageStageIncl D i V k₁)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i V k₁)).obj G :=
  canConj (preimageTrans D i V v) (preimageStageIncl D i V k₀) (preimageStageIncl D i V k₁)
    (preimageTrans_comp_preimageStageIncl D i V v)
    ((Scheme.Modules.pullback (preimageTrans D i V v)).map X)

/-- Composing two transition morphisms of the preimages of `V`. -/
theorem preimageTrans_comp (V : (D.obj i).Opens) {k₂ k₁ k₀ : Over i} (u : k₂ ⟶ k₁)
    (v : k₁ ⟶ k₀) :
    preimageTrans D i V u ≫ preimageTrans D i V v = preimageTrans D i V (u ≫ v) := by
  refine (cancel_mono (D.map k₀.hom ⁻¹ᵁ V).ι).mp ?_
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι (D.map v.left) _, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι (D.map u.left) _, Category.assoc, ← D.map_comp, ← Over.comp_left,
    Scheme.Hom.resLE_comp_ι (D.map (u ≫ v).left) _]

/-- Restricting to a smaller open of `D i` and then including the preimage into the limit. -/
theorem homOfLE_comp_limitIncl (c : Cone D) {V P : (D.obj i).Opens} (hPV : P ≤ V) :
    c.pt.homOfLE (Scheme.Hom.preimage_mono (c.π.app i) hPV) ≫
        ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i)
      = (c.π.app i ⁻¹ᵁ P).ι ≫ c.π.app i := by
  rw [← Category.assoc]
  exact congrArg (fun z => z ≫ c.π.app i) (Scheme.homOfLE_ι _ _)

/-- A morphism of the pullbacks to the limit, restricted to the preimage of an open `V` of the
stage `D i` and read through the canonical identification as a morphism of the pullbacks along
the inclusion of that preimage followed by the projection. -/
noncomputable def limitRestrict (c : Cone D) (V : (D.obj i).Opens) {F G : (D.obj i).Modules}
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    (Scheme.Modules.pullback ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i)).obj G :=
  canConj (c.π.app i ⁻¹ᵁ V).ι (c.π.app i) ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i) rfl
    ((Scheme.Modules.pullback (c.π.app i ⁻¹ᵁ V).ι).map φ)

/-- **The restriction to the limit is compatible with shrinking the open.**  The restriction of
`φ` to the preimage of a smaller open `P` is the canonical base change of its restriction to the
preimage of `V` along the inclusion. -/
theorem isCanonicalBaseChange_limitRestrict (c : Cone D) {V P : (D.obj i).Opens} (hPV : P ≤ V)
    {F G : (D.obj i).Modules}
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    IsCanonicalBaseChange (c.pt.homOfLE (Scheme.Hom.preimage_mono (c.π.app i) hPV))
      ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i) ((c.π.app i ⁻¹ᵁ P).ι ≫ c.π.app i)
      (homOfLE_comp_limitIncl D i c hPV) (limitRestrict D i c V φ)
      (limitRestrict D i c P φ) :=
  (isCanonicalBaseChange_stage_iff (c.pt.homOfLE (Scheme.Hom.preimage_mono (c.π.app i) hPV))
    (c.π.app i ⁻¹ᵁ V).ι (c.π.app i) (c.π.app i ⁻¹ᵁ P).ι (Scheme.homOfLE_ι _ _)
    ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i) rfl ((c.π.app i ⁻¹ᵁ P).ι ≫ c.π.app i) rfl
    (homOfLE_comp_limitIncl D i c hPV) φ (limitRestrict D i c P φ)).mpr
      ((isCanonicalBaseChange_iff _ _ _ _ _ _).mpr rfl)

/-- **Restricting to a smaller open and passing to a later stage commute.**  Both composites are
the local piece read through the canonical identification attached to the one morphism
`D k₁ ⁻¹ᵁ P ⟶ D k₀ ⁻¹ᵁ V`, so this is the cocycle. -/
theorem overlapRestrict_stagePush {k₁ k₀ : Over i} (v : k₁ ⟶ k₀) {V P : (D.obj i).Opens}
    (hPV : P ≤ V) {F G : (D.obj i).Modules}
    (X : (Scheme.Modules.pullback (preimageStageIncl D i V k₀)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i V k₀)).obj G) :
    overlapRestrict D i k₁ hPV (stagePush D i v V X)
      = stagePush D i v P (overlapRestrict D i k₀ hPV X) := by
  have hmor := homOfLE_comp_preimageTrans D i hPV v
  have hι₀ := homOfLE_comp_preimageStageIncl D i k₀ hPV
  have hι₁ := homOfLE_comp_preimageStageIncl D i k₁ hPV
  have hEV := preimageTrans_comp_preimageStageIncl D i V v
  have hEP := preimageTrans_comp_preimageStageIncl D i P v
  have hfac : ((D.obj k₁.left).homOfLE (Scheme.Hom.preimage_mono (D.map k₁.hom) hPV) ≫
        preimageTrans D i V v) ≫ preimageStageIncl D i V k₀ = preimageStageIncl D i P k₁ := by
    rw [hmor, Category.assoc, hι₀, hEP]
  have hL := canConj_canConj
    ((D.obj k₁.left).homOfLE (Scheme.Hom.preimage_mono (D.map k₁.hom) hPV))
    (preimageTrans D i V v) (preimageStageIncl D i V k₀) _ rfl
    (preimageStageIncl D i V k₁) hEV (preimageStageIncl D i P k₁) hfac hι₁ X
  have hR := canConj_canConj (preimageTrans D i P v)
    ((D.obj k₀.left).homOfLE (Scheme.Hom.preimage_mono (D.map k₀.hom) hPV))
    (preimageStageIncl D i V k₀)
    ((D.obj k₁.left).homOfLE (Scheme.Hom.preimage_mono (D.map k₁.hom) hPV) ≫
      preimageTrans D i V v) hmor.symm (preimageStageIncl D i P k₀) hι₀
    (preimageStageIncl D i P k₁) hfac hEP X
  simp only [overlapRestrict, stagePush]
  rw [hL, hR]

/-- Restricting to a smaller open of the stage, as a morphism to the stage. -/
theorem homOfLE_comp_preimageStageIncl' (k : Over i) {V : (D.obj i).Opens}
    {V' : (D.obj k.left).Opens} (h : V' ≤ D.map k.hom ⁻¹ᵁ V) :
    (D.obj k.left).homOfLE h ≫ preimageStageIncl D i V k = V'.ι ≫ D.map k.hom := by
  rw [preimageStageIncl, ← Category.assoc, Scheme.homOfLE_ι]

/-- Reading a restricted local piece over a smaller open `V'` of the later stage agrees with
reading the original local piece over `V'`. -/
private theorem canConj_homOfLE_overlapRestrict (k : Over i) {V P : (D.obj i).Opens}
    (hPV : P ≤ V) {V' : (D.obj k.left).Opens} (hP : V' ≤ D.map k.hom ⁻¹ᵁ P)
    (hV : V' ≤ D.map k.hom ⁻¹ᵁ V) {F G : (D.obj i).Modules}
    (X : (Scheme.Modules.pullback (preimageStageIncl D i V k)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i V k)).obj G) :
    canConj ((D.obj k.left).homOfLE hP) (preimageStageIncl D i P k) (V'.ι ≫ D.map k.hom)
        (homOfLE_comp_preimageStageIncl' D i k hP)
        ((Scheme.Modules.pullback ((D.obj k.left).homOfLE hP)).map (overlapRestrict D i k hPV X))
      = canConj ((D.obj k.left).homOfLE hV) (preimageStageIncl D i V k) (V'.ι ≫ D.map k.hom)
        (homOfLE_comp_preimageStageIncl' D i k hV)
        ((Scheme.Modules.pullback ((D.obj k.left).homOfLE hV)).map X) :=
  canConj_canConj ((D.obj k.left).homOfLE hP)
    ((D.obj k.left).homOfLE (Scheme.Hom.preimage_mono (D.map k.hom) hPV))
    (preimageStageIncl D i V k) ((D.obj k.left).homOfLE hV) (Scheme.homOfLE_homOfLE _ _ _)
    (preimageStageIncl D i P k) (homOfLE_comp_preimageStageIncl D i k hPV)
    (V'.ι ≫ D.map k.hom) (homOfLE_comp_preimageStageIncl' D i k hV)
    (homOfLE_comp_preimageStageIncl' D i k hP) X

/-- The composite of the projection from the limit with the inclusion of a smaller open of the
stage. -/
theorem preimageConeπ_comp_homOfLE_comp (c : Cone D) {V P : (D.obj i).Opens} (hPV : P ≤ V)
    (k : Over i) :
    (preimageConeπ D i c P k ≫
          (D.obj k.left).homOfLE (Scheme.Hom.preimage_mono (D.map k.hom) hPV)) ≫
        preimageStageIncl D i V k
      = (c.π.app i ⁻¹ᵁ P).ι ≫ c.π.app i := by
  rw [Category.assoc, homOfLE_comp_preimageStageIncl D i k hPV,
    preimageConeπ_comp_preimageStageIncl D i c P k]

/-- **A local piece pushed to a later stage still has the restriction of `φ` as its canonical
base change.** -/
theorem isCanonicalBaseChange_stagePush (c : Cone D) (V : (D.obj i).Opens) {k₁ k₀ : Over i}
    (v : k₁ ⟶ k₀) {F G : (D.obj i).Modules}
    {φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G}
    {X : (Scheme.Modules.pullback (preimageStageIncl D i V k₀)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i V k₀)).obj G}
    (h : IsCanonicalBaseChange (preimageConeπ D i c V k₀) (preimageStageIncl D i V k₀)
      ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i) (preimageConeπ_comp_preimageStageIncl D i c V k₀) X
      (limitRestrict D i c V φ)) :
    IsCanonicalBaseChange (preimageConeπ D i c V k₁) (preimageStageIncl D i V k₁)
      ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i) (preimageConeπ_comp_preimageStageIncl D i c V k₁)
      (stagePush D i v V X) (limitRestrict D i c V φ) :=
  (isCanonicalBaseChange_stage_iff (preimageConeπ D i c V k₁) (preimageTrans D i V v)
    (preimageStageIncl D i V k₀) (preimageConeπ D i c V k₀)
    (preimageConeπ_comp_preimageTrans D i c V v) (preimageStageIncl D i V k₁)
    (preimageTrans_comp_preimageStageIncl D i V v) ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i)
    (preimageConeπ_comp_preimageStageIncl D i c V k₀)
    (preimageConeπ_comp_preimageStageIncl D i c V k₁) X (limitRestrict D i c V φ)).mpr h

/-- **A local piece restricted to a smaller open still has the restriction of `φ` as its
canonical base change.** -/
theorem isCanonicalBaseChange_overlapRestrict (c : Cone D) {V P : (D.obj i).Opens} (hPV : P ≤ V)
    (k : Over i) {F G : (D.obj i).Modules}
    {φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G}
    {X : (Scheme.Modules.pullback (preimageStageIncl D i V k)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i V k)).obj G}
    (h : IsCanonicalBaseChange (preimageConeπ D i c V k) (preimageStageIncl D i V k)
      ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i) (preimageConeπ_comp_preimageStageIncl D i c V k) X
      (limitRestrict D i c V φ)) :
    IsCanonicalBaseChange (preimageConeπ D i c P k) (preimageStageIncl D i P k)
      ((c.π.app i ⁻¹ᵁ P).ι ≫ c.π.app i) (preimageConeπ_comp_preimageStageIncl D i c P k)
      (overlapRestrict D i k hPV X) (limitRestrict D i c P φ) := by
  have hstep := isCanonicalBaseChange_restrict (preimageConeπ D i c V k)
    (preimageStageIncl D i V k) ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i)
    (preimageConeπ_comp_preimageStageIncl D i c V k)
    (c.pt.homOfLE (Scheme.Hom.preimage_mono (c.π.app i) hPV))
    (preimageConeπ D i c P k ≫
      (D.obj k.left).homOfLE (Scheme.Hom.preimage_mono (D.map k.hom) hPV))
    (preimageConeπ_comp_homOfLE D i c hPV k).symm ((c.π.app i ⁻¹ᵁ P).ι ≫ c.π.app i)
    (homOfLE_comp_limitIncl D i c hPV) (preimageConeπ_comp_homOfLE_comp D i c hPV k) h
  rw [(isCanonicalBaseChange_iff _ _ _ _ _ _).mp
    (isCanonicalBaseChange_limitRestrict D i c hPV φ)] at hstep
  exact (isCanonicalBaseChange_stage_iff (preimageConeπ D i c P k)
    ((D.obj k.left).homOfLE (Scheme.Hom.preimage_mono (D.map k.hom) hPV))
    (preimageStageIncl D i V k) _ rfl (preimageStageIncl D i P k)
    (homOfLE_comp_preimageStageIncl D i k hPV) ((c.π.app i ⁻¹ᵁ P).ι ≫ c.π.app i)
    (preimageConeπ_comp_homOfLE_comp D i c hPV k)
    (preimageConeπ_comp_preimageStageIncl D i c P k) X (limitRestrict D i c P φ)).mpr hstep

end Pieces


/-! ### The affine case over one member of an affine covering -/

section Member

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **The affine case of Tag 01ZR (2) on the diagram of preimages of an affine open.**  For an
affine open `V` of the stage `D i` the diagram of preimages of `V` is a cofiltered diagram of
affine schemes whose limit is the preimage of `V` in the limit, so the affine case applies to it
and descends any morphism of the pullbacks to that preimage. -/
private theorem exists_canonical_affine_step (hc : IsLimit c) (i : I) {V : (D.obj i).Opens}
    (hV : IsAffineOpen V) (F G : (D.obj i).Modules)
    [F.IsFinitePresentation] [G.IsFinitePresentation]
    (ϕ : (Scheme.Modules.pullback (preimageConeπ D i c V (Over.mk (𝟙 i)))).obj
          ((Scheme.Modules.pullback (preimageStageIncl D i V (Over.mk (𝟙 i)))).obj F) ⟶
        (Scheme.Modules.pullback (preimageConeπ D i c V (Over.mk (𝟙 i)))).obj
          ((Scheme.Modules.pullback (preimageStageIncl D i V (Over.mk (𝟙 i)))).obj G)) :
    ∃ (j : Over i) (e : j ⟶ Over.mk (𝟙 i))
      (χ : (Scheme.Modules.pullback (preimageTrans D i V e)).obj
            ((Scheme.Modules.pullback (preimageStageIncl D i V (Over.mk (𝟙 i)))).obj F) ⟶
          (Scheme.Modules.pullback (preimageTrans D i V e)).obj
            ((Scheme.Modules.pullback (preimageStageIncl D i V (Over.mk (𝟙 i)))).obj G)),
      IsCanonicalBaseChange (preimageConeπ D i c V j) (preimageTrans D i V e)
        (preimageConeπ D i c V (Over.mk (𝟙 i)))
        (preimageConeπ_comp_preimageTrans D i c V e) χ ϕ := by
  have haff : ∀ k : Over i, IsAffine ((EventualLimit.preimageDiagram D i V).obj k) :=
    EventualLimit.isAffine_preimageDiagram_obj D i hV
  have hfpF : ((Scheme.Modules.pullback
      (preimageStageIncl D i V (Over.mk (𝟙 i)))).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback _ F
  have hfpG : ((Scheme.Modules.pullback
      (preimageStageIncl D i V (Over.mk (𝟙 i)))).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback _ G
  exact @exists_map_of_pullback_canonical_of_isAffine' (Over i) _ _
    (EventualLimit.preimageDiagram D i V) (EventualLimit.preimageCone D c i V) haff
    (EventualLimit.isLimitPreimageCone D c hc i V) (Over.mk (𝟙 i)) _ _ hfpF hfpG ϕ

/-- **The local piece over one member of an affine covering.**  Let `V` be an affine open of the
stage `D i` and let `φ` be a morphism of the pullbacks to the limit of two finitely presented
modules on `D i`.  Then there is an index `j` over `i` such that for every index `k` over `i`
with a morphism to `j`, the restriction of `φ` to the preimage of `V` in the limit is the
canonical base change of a local piece over `V` at the stage `k`.

The affine case is applied on the diagram of preimages of `V`
(`exists_canonical_affine_step`); the stage it produces is pushed to `k` by
`Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_stage_iff`, and the modules on `V`
are the pullbacks of `F` and `G` along the inclusion, so that
`Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_factor_iff` turns the conclusion
into a statement about `F` and `G` themselves. -/
theorem exists_canonical_of_isAffineOpen (hc : IsLimit c) (i : I) {V : (D.obj i).Opens}
    (hV : IsAffineOpen V) (F G : (D.obj i).Modules)
    [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ j : Over i, ∀ (k : Over i), (k ⟶ j) →
      ∃ X : (Scheme.Modules.pullback (preimageStageIncl D i V k)).obj F ⟶
            (Scheme.Modules.pullback (preimageStageIncl D i V k)).obj G,
        IsCanonicalBaseChange (preimageConeπ D i c V k) (preimageStageIncl D i V k)
          ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i)
          (preimageConeπ_comp_preimageStageIncl D i c V k) X (limitRestrict D i c V φ) := by
  obtain ⟨j, e, χ, hχ⟩ := exists_canonical_affine_step D c hc i hV F G
    (canUnconj (preimageConeπ D i c V (Over.mk (𝟙 i)))
      (preimageStageIncl D i V (Over.mk (𝟙 i))) ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i)
      (preimageConeπ_comp_preimageStageIncl D i c V (Over.mk (𝟙 i)))
      (limitRestrict D i c V φ))
  exact ⟨j, fun k u => exists_isCanonicalBaseChange_of_stage_factor
    (preimageConeπ D i c V k) (preimageTrans D i V u) (preimageTrans D i V e)
    (preimageStageIncl D i V (Over.mk (𝟙 i))) (preimageConeπ D i c V j)
    (preimageConeπ_comp_preimageTrans D i c V u) (preimageTrans D i V (u ≫ e))
    (preimageTrans_comp D i V u e) (preimageConeπ D i c V (Over.mk (𝟙 i)))
    (preimageConeπ_comp_preimageTrans D i c V e)
    (preimageConeπ_comp_preimageTrans D i c V (u ≫ e)) (preimageStageIncl D i V k)
    (preimageTrans_comp_preimageStageIncl D i V (u ≫ e))
    ((c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i)
    (preimageConeπ_comp_preimageStageIncl D i c V (Over.mk (𝟙 i)))
    (preimageConeπ_comp_preimageStageIncl D i c V k) χ (limitRestrict D i c V φ) hχ⟩

end Member

/-! ### Tag 01ZR (2) for quasi-compact quasi-separated stages -/

section Main

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- The projection to a stage, the inclusion of the preimage of `V` and the transition morphism
compose to the inclusion of the preimage of `V` in the limit followed by the projection. -/
theorem preimageConeπ_comp_ι_comp (i : I) (V : (D.obj i).Opens) (k : Over i) :
    (preimageConeπ D i c V k ≫ (D.map k.hom ⁻¹ᵁ V).ι) ≫ D.map k.hom
      = (c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i := by
  rw [Category.assoc]
  exact preimageConeπ_comp_preimageStageIncl D i c V k

variable [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

omit [∀ i : I, CompactSpace (D.obj i)] in
/-- **The local pieces over two members of an affine covering agree over a later stage.**  Both
restrictions to the overlap have the same canonical base change to the limit, namely the
restriction of `φ`, so their pullbacks to the limit agree; [Stacks Project, Tag 01ZR] (3) applied
to the diagram of preimages of the overlap then makes them agree over a later stage.

The overlap of two affine opens of `D i` is quasi-compact because `D i` is quasi-separated, and
its preimage in a later stage is quasi-compact because the transition morphisms are affine. -/
private theorem exists_over_overlapRestrict_eq (hc : IsLimit c) (i : I)
    {V₁ V₂ : (D.obj i).Opens} (hV₁ : IsAffineOpen V₁) (hV₂ : IsAffineOpen V₂) (k : Over i)
    {F G : (D.obj i).Modules} [F.IsFinitePresentation] [G.IsFinitePresentation]
    {φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G}
    {X₁ : (Scheme.Modules.pullback (preimageStageIncl D i V₁ k)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i V₁ k)).obj G}
    {X₂ : (Scheme.Modules.pullback (preimageStageIncl D i V₂ k)).obj F ⟶
      (Scheme.Modules.pullback (preimageStageIncl D i V₂ k)).obj G}
    (h₁ : IsCanonicalBaseChange (preimageConeπ D i c V₁ k) (preimageStageIncl D i V₁ k)
      ((c.π.app i ⁻¹ᵁ V₁).ι ≫ c.π.app i) (preimageConeπ_comp_preimageStageIncl D i c V₁ k) X₁
      (limitRestrict D i c V₁ φ))
    (h₂ : IsCanonicalBaseChange (preimageConeπ D i c V₂ k) (preimageStageIncl D i V₂ k)
      ((c.π.app i ⁻¹ᵁ V₂).ι ≫ c.π.app i) (preimageConeπ_comp_preimageStageIncl D i c V₂ k) X₂
      (limitRestrict D i c V₂ φ)) :
    ∃ (κ : Over i) (e : κ ⟶ k),
      (Scheme.Modules.pullback (preimageTrans D i (V₁ ⊓ V₂) e)).map
          (overlapRestrict D i k (inf_le_left : V₁ ⊓ V₂ ≤ V₁) X₁)
        = (Scheme.Modules.pullback (preimageTrans D i (V₁ ⊓ V₂) e)).map
          (overlapRestrict D i k (inf_le_right : V₁ ⊓ V₂ ≤ V₂) X₂) := by
  have hP : IsCompact ((V₁ ⊓ V₂ : (D.obj i).Opens) : Set (D.obj i)) := by
    rw [Opens.coe_inf]
    exact IsQuasiSeparated.of_quasiSeparatedSpace Set.univ _ _ (Set.subset_univ _) V₁.isOpen
      hV₁.isCompact (Set.subset_univ _) V₂.isOpen hV₂.isCompact
  have heq := pullback_map_eq_of_isCanonicalBaseChange (preimageConeπ D i c (V₁ ⊓ V₂) k)
    (preimageStageIncl D i (V₁ ⊓ V₂) k) ((c.π.app i ⁻¹ᵁ (V₁ ⊓ V₂)).ι ≫ c.π.app i)
    (preimageConeπ_comp_preimageStageIncl D i c (V₁ ⊓ V₂) k)
    (isCanonicalBaseChange_overlapRestrict D i c (inf_le_left : V₁ ⊓ V₂ ≤ V₁) k h₁)
    (isCanonicalBaseChange_overlapRestrict D i c (inf_le_right : V₁ ⊓ V₂ ≤ V₂) k h₂)
  have haff : ∀ {x y : Over i} (f : x ⟶ y),
      IsAffineHom ((EventualLimit.preimageDiagram D i (V₁ ⊓ V₂)).map f) :=
    fun _ => inferInstance
  have hcs : CompactSpace ((EventualLimit.preimageDiagram D i (V₁ ⊓ V₂)).obj k) :=
    compactSpace_preimageDiagram_obj D i hP k
  have hfp₁ : ((Scheme.Modules.pullback
      (preimageStageIncl D i (V₁ ⊓ V₂) k)).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback _ F
  have hfp₂ : ((Scheme.Modules.pullback
      (preimageStageIncl D i (V₁ ⊓ V₂) k)).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback _ G
  exact @exists_pullback_map_eq_of_isLimit' (Over i) _ _
    (EventualLimit.preimageDiagram D i (V₁ ⊓ V₂)) haff
    (EventualLimit.preimageCone D c i (V₁ ⊓ V₂))
    (EventualLimit.isLimitPreimageCone D c hc i (V₁ ⊓ V₂)) k hcs _ _ hfp₁ hfp₂ _ _ heq

/-- **[Stacks Project, Tag 01ZR] (2)** for a cofiltered diagram of quasi-compact quasi-separated
schemes with affine transition morphisms, in the canonically pinned form: a morphism between the
pullbacks to the limit of two finitely presented modules on a stage is, after passing to a later
stage, the base change of a morphism there through the canonical identification.

Choose a finite affine open covering `V a` of the stage.  Over each member the affine case
applies to the diagram of preimages and produces a local piece at a stage over `i`
(`exists_canonical_of_isAffineOpen`); a common refinement brings all of them to one stage `k₀`.
Two local pieces restrict to morphisms over the overlap with the same canonical base change to
the limit, so [Stacks Project, Tag 01ZR] (3) makes them agree over a later stage
(`exists_over_overlapRestrict_eq`); the finitely many morphisms to `k₀` the pairs produce are
brought under a single one by cofilteredness of `CategoryTheory.Over k₀`, and the local pieces
are pushed along it.  They then agree over every open contained in two members, so they glue
(`Stacks.AlgebraicGeometry.ModuleLimits.exists_isCanonicalBaseChange_of_opens_cover`), and the
canonical equation on the limit, being local, follows from the canonical equation over the
preimages of the members of the covering. -/
@[ega "IV 8.1.1" "partial"]
theorem hasCanonicalDescent_of_isLimit (hc : IsLimit c) : HasCanonicalDescent D c := by
  classical
  intro i F G hF hG φ
  have : F.IsFinitePresentation := hF
  have : G.IsFinitePresentation := hG
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  let V : 𝒰.I₀ → (D.obj i).Opens := fun a => (𝒰.f a).opensRange
  have hVa : ∀ a, IsAffineOpen (V a) := fun a => isAffineOpen_opensRange _
  have hcov : ∀ x : D.obj i, ∃ a, x ∈ V a := fun x =>
    𝒰.isOpenCover_opensRange.exists_mem x
  -- the local pieces, at one common stage `k₀`
  choose jj hjj using fun a => exists_canonical_of_isAffineOpen D c hc i (hVa a) F G φ
  obtain ⟨k₀, hk₀⟩ := IsCofiltered.inf_objs_exists (Finset.image jj Finset.univ)
  choose X hX using fun a =>
    hjj a k₀ (hk₀ (Finset.mem_image_of_mem _ (Finset.mem_univ a))).some
  -- a stage over `k₀` for each pair of members, and one morphism factoring through all of them
  choose κ ee hee using fun p : 𝒰.I₀ × 𝒰.I₀ =>
    exists_over_overlapRestrict_eq D c hc i (hVa p.1) (hVa p.2) k₀ (hX p.1) (hX p.2)
  obtain ⟨K, hK⟩ := IsCofiltered.inf_objs_exists
    (Finset.image (fun p : 𝒰.I₀ × 𝒰.I₀ => Over.mk (ee p)) Finset.univ)
  have hagree : ∀ p : 𝒰.I₀ × 𝒰.I₀,
      (Scheme.Modules.pullback (preimageTrans D i (V p.1 ⊓ V p.2) K.hom)).map
          (overlapRestrict D i k₀ (inf_le_left : V p.1 ⊓ V p.2 ≤ V p.1) (X p.1))
        = (Scheme.Modules.pullback (preimageTrans D i (V p.1 ⊓ V p.2) K.hom)).map
          (overlapRestrict D i k₀ (inf_le_right : V p.1 ⊓ V p.2 ≤ V p.2) (X p.2)) := by
    intro p
    obtain ⟨w⟩ := hK (Finset.mem_image_of_mem _ (Finset.mem_univ p))
    rw [← Over.w w, ← preimageTrans_comp]
    exact pullback_map_eq_of_precomp _ _ (hee p)
  -- the pushed local pieces agree on the overlaps
  have hY : ∀ a b : 𝒰.I₀,
      overlapRestrict D i K.left (inf_le_left : V a ⊓ V b ≤ V a)
            (stagePush D i K.hom (V a) (X a))
        = overlapRestrict D i K.left (inf_le_right : V a ⊓ V b ≤ V b)
            (stagePush D i K.hom (V b) (X b)) := by
    intro a b
    rw [overlapRestrict_stagePush, overlapRestrict_stagePush]
    simp only [stagePush]
    rw [hagree (a, b)]
  -- glue them
  have hOtop : ⨆ a, D.map K.left.hom ⁻¹ᵁ V a = (⊤ : (D.obj K.left.left).Opens) := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨a, ha⟩ := hcov ((D.map K.left.hom).base x)
    exact Opens.mem_iSup.mpr ⟨a, ha⟩
  have hglue : ∀ (a b : 𝒰.I₀) (V' : (D.obj K.left.left).Opens)
      (ha : V' ≤ D.map K.left.hom ⁻¹ᵁ V a) (hb : V' ≤ D.map K.left.hom ⁻¹ᵁ V b),
      canConj ((D.obj K.left.left).homOfLE ha) (preimageStageIncl D i (V a) K.left)
            (V'.ι ≫ D.map K.left.hom) (homOfLE_comp_preimageStageIncl' D i K.left ha)
            ((Scheme.Modules.pullback ((D.obj K.left.left).homOfLE ha)).map
              (stagePush D i K.hom (V a) (X a)))
        = canConj ((D.obj K.left.left).homOfLE hb) (preimageStageIncl D i (V b) K.left)
            (V'.ι ≫ D.map K.left.hom) (homOfLE_comp_preimageStageIncl' D i K.left hb)
            ((Scheme.Modules.pullback ((D.obj K.left.left).homOfLE hb)).map
              (stagePush D i K.hom (V b) (X b))) := by
    intro a b V' ha hb
    have hab : V' ≤ D.map K.left.hom ⁻¹ᵁ (V a ⊓ V b) := fun x hx => ⟨ha hx, hb hx⟩
    rw [← canConj_homOfLE_overlapRestrict D i K.left (inf_le_left : V a ⊓ V b ≤ V a) hab ha,
      ← canConj_homOfLE_overlapRestrict D i K.left (inf_le_right : V a ⊓ V b ≤ V b) hab hb,
      hY a b]
  obtain ⟨θ, hθ⟩ := exists_isCanonicalBaseChange_of_opens_cover (D.map K.left.hom)
    (fun a => D.map K.left.hom ⁻¹ᵁ V a) hOtop
    (fun a => preimageStageIncl D i (V a) K.left) (fun _ => rfl)
    (fun a => stagePush D i K.hom (V a) (X a)) hglue
  refine ⟨K.left.left, K.left.hom, θ, ?_⟩
  refine isCanonicalBaseChange_of_forall_cover (c.π.app K.left.left) (D.map K.left.hom)
    (c.π.app i) (c.w K.left.hom) (fun a => c.π.app i ⁻¹ᵁ V a)
    (fun x => hcov ((c.π.app i).base x))
    (fun a => preimageConeπ D i c (V a) K.left ≫ (D.map K.left.hom ⁻¹ᵁ V a).ι)
    (fun a => (Scheme.Hom.resLE_comp_ι (c.π.app K.left.left) _).symm)
    (fun a => (c.π.app i ⁻¹ᵁ V a).ι ≫ c.π.app i) (fun _ => rfl)
    (fun a => preimageConeπ_comp_ι_comp D c i (V a) K.left) fun a => ?_
  refine (isCanonicalBaseChange_stage_iff (preimageConeπ D i c (V a) K.left)
    (D.map K.left.hom ⁻¹ᵁ V a).ι (D.map K.left.hom)
    (preimageConeπ D i c (V a) K.left ≫ (D.map K.left.hom ⁻¹ᵁ V a).ι) rfl
    (preimageStageIncl D i (V a) K.left) rfl ((c.π.app i ⁻¹ᵁ V a).ι ≫ c.π.app i)
    (preimageConeπ_comp_ι_comp D c i (V a) K.left)
    (preimageConeπ_comp_preimageStageIncl D i c (V a) K.left) θ
    (limitRestrict D i c (V a) φ)).mp ?_
  rw [(isCanonicalBaseChange_iff (D.map K.left.hom ⁻¹ᵁ V a).ι (D.map K.left.hom)
    (preimageStageIncl D i (V a) K.left) rfl θ
    (stagePush D i K.hom (V a) (X a))).mp (hθ a)]
  exact isCanonicalBaseChange_stagePush D i c (V a) K.hom (hX a)

end Main

/-! ### The index morphism universe, and the consequences -/

section IndexHomUniverse

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

/-- Transport of the conclusion of Tag 01ZR (2) along an equality of the transition morphism. -/
private theorem isCanonicalBaseChange_congr {W Z X : Scheme.{u}} (q : W ⟶ Z) {g g' : Z ⟶ X}
    (h : g = g') (pi : W ⟶ X) (hpi : q ≫ g = pi) (hpi' : q ≫ g' = pi) (F G : X.Modules)
    (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)
    (hex : ∃ φj' : (Scheme.Modules.pullback g').obj F ⟶ (Scheme.Modules.pullback g').obj G,
      IsCanonicalBaseChange q g' pi hpi' φj' φ) :
    ∃ φj : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G,
      IsCanonicalBaseChange q g pi hpi φj φ := by
  subst h
  exact hex

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

include c in
/-- **[Stacks Project, Tag 01ZR] (2)** in the canonically pinned form, with the index morphism
universe unrestricted.  This is `hasCanonicalDescent_of_isLimit` applied to
`CategoryTheory.Functor.FullImage D`, whose index morphisms live in the universe of the
schemes and which carries all the hypotheses. -/
theorem hasCanonicalDescent_of_isLimit' (hc : IsLimit c) : HasCanonicalDescent D c := by
  intro i F G hF hG φ
  obtain ⟨j, gm, φj, hφj⟩ := @hasCanonicalDescent_of_isLimit (FullImage D) _ _ (ι D) _
    (cone D c) _ _ (isLimitCone D hc) ⟨i⟩ F G hF hG φ
  refine ⟨j.as, hom D gm, ?_⟩
  exact isCanonicalBaseChange_congr (c.π.app j.as) (map_hom D gm) (c.π.app i)
    (c.w (hom D gm)) ((cone D c).w gm) F G φ ⟨φj, hφj⟩

end IndexHomUniverse

end Stacks.AlgebraicGeometry.ModuleLimits

end
