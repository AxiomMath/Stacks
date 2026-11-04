module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.InvariantOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.CechGroupoidDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic

/-!
# Invariance for a descent datum and for the groupoid scheme it presents

A descent datum `(V, φ)` for a morphism `f : X ⟶ Y` of schemes over `S` is the same thing as a
groupoid scheme cartesian over the Čech groupoid of `f`, whose scheme of objects is `V`. There
are then two notions of invariance for a subset of `V`: the *descent-datum* one, that `φ`
carries the part of `V ×_Y X` over it onto the part of `X ×_Y V` over it, and the *groupoid*
one, that every arrow of the cartesian groupoid scheme whose source lies in the subset has its
target there too. This file identifies the two.

Both notions turn out to be equalities of preimages along two maps out of one scheme, and the
identification is the comparison of those maps. On the groupoid side invariance, written as an
implication, is automatically an equality of the preimages along the source and the target map,
because inversion exchanges the two. On the descent side the two maps out of `V ×_Y X` are the
projection to `V` and the gluing action `AlgebraicGeometry.DescentData.actOn`, and the
involution exchanging them is again the one sending an arrow to its inverse.

## Main definitions

* `AlgebraicGeometry.cartesianOverObjectsComparison` identifies the object scheme of a groupoid
  scheme cartesian over `G` with the scheme of an equivariant scheme presenting it.
* `AlgebraicGeometry.DescentData.actSwap` is the involution of `V ×_S X` carrying a pair
  `(v, x)` to the pair consisting of the action of `x` on `v` and the image of `v` in `X`.
* `AlgebraicGeometry.DescentData.IsInvariantSet` is set-theoretic invariance of a subset of `V`
  under a descent datum for a single morphism.
* `AlgebraicGeometry.cechDescentObjectsIso` is the object scheme of the cartesian groupoid
  scheme of a descent datum, identified with `V` as a scheme over `S`.
* `AlgebraicGeometry.cechDescentArrowComparison` reads an arrow of that groupoid scheme as a
  point of `V ×_Y X`, and `AlgebraicGeometry.cechDescentArrowSection` is its section.

## Main results

* `Stacks.Groupoids.isInvariantSet_iff_preimage_eq` and
  `Stacks.Groupoids.isInvariantOpen_iff_preimage_eq`: invariance under a groupoid scheme is the
  equality of the preimages along the source and the target map.
* `AlgebraicGeometry.cartesianOverSource_comp_comparison`: the source map of a groupoid scheme
  cartesian over `G` is the action of the corresponding equivariant scheme on its target map.
* `AlgebraicGeometry.cechDescentSource_comp_objectsIso`: for the cartesian groupoid scheme of a
  descent datum that action is the gluing action of the datum.
* `AlgebraicGeometry.DescentData.isInvariantSet_iff_subset`: set-theoretic invariance under a
  descent datum needs to be checked in one direction only.
* `AlgebraicGeometry.DescentData.isInvariantOpens_iff_isInvariantSet`: invariance of a family
  of opens, for a single morphism, is set-theoretic invariance of the underlying set.
* `AlgebraicGeometry.isInvariantSet_cechDescent_iff` and
  `AlgebraicGeometry.isInvariantOpen_cechDescent_iff`: **the translation.** A subset, resp. an
  open, of `V` is invariant under the cartesian groupoid scheme of a descent datum if and only
  if it is invariant for the descent datum. Both directions hold.
* `AlgebraicGeometry.isInvariantSet_cechDescentCartesianOver_iff` and
  `AlgebraicGeometry.isInvariantOpen_cechDescentCartesianOver_iff` are the same statements
  read the other way round, starting from an arbitrary subset, resp. open, of the object
  scheme of the cartesian groupoid scheme.

## Implementation notes

The equivalence between groupoid schemes cartesian over `G` and equivariant schemes for `G` is
only available through `AlgebraicGeometry.cartesianOverEquivalenceEquivariantScheme` and the
three equations characterizing it, so the source map of a cartesian groupoid scheme is reached
through `AlgebraicGeometry.cartesianOverEquivalenceEquivariantScheme_descentIso_hom`: feeding
the target map and the map on arrows into that equation returns the source map, which is
therefore the action. Nothing else about the arrow scheme is needed, and in particular its
comparison with a fibre product is not: the comparison
`AlgebraicGeometry.cechDescentArrowComparison` to `V ×_Y X` is written down directly from the
target map and the map on arrows, and all that is used of it is that it is a split epimorphism.
Its section is produced from the cartesian square of the structure morphism, which exhibits the
arrow scheme as a fibre product along the *source* map; the involution
`AlgebraicGeometry.DescentData.actSwap` converts between the two.

The scheme of arrows of the Čech groupoid is a fibre product and its source and target maps are
the two projections, but only up to unfolding the definition of the groupoid; the elaborator
will do that unfolding while typechecking a statement and refuse to do it while building the
motive of a rewrite. The two composites of the map on arrows with those projections are
therefore named, as `AlgebraicGeometry.cechDescentArrowSourceBase` and
`AlgebraicGeometry.cechDescentArrowTargetBase`, and every statement below uses the names.

## References

* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 03LO](https://stacks.math.columbia.edu/tag/03LO)
* [Stacks Project, Tag 0APE](https://stacks.math.columbia.edu/tag/0APE)
* [Stacks Project, Tag 0APF](https://stacks.math.columbia.edu/tag/0APF)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- On points, the source of the inverse of an arrow is the target of that arrow. -/
theorem source_inverse_apply (r : G.arrows.left) :
    G.source.left (G.inverse.left r) = G.target.left r := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun k : G.arrows ⟶ G.objects ↦ k.left r) G.source_inverse

/-- On points, the target of the inverse of an arrow is the source of that arrow. -/
theorem target_inverse_apply (r : G.arrows.left) :
    G.target.left (G.inverse.left r) = G.source.left r := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun k : G.arrows ⟶ G.objects ↦ k.left r) G.target_inverse

/-- Invariance of a subset of the objects of a groupoid scheme is the equality of its preimages
along the source and the target map: the implication defining invariance holds in the other
direction too, by applying it to the inverse of an arrow.

**Stacks Project, Tag 03LO.** -/
theorem isInvariantSet_iff_preimage_eq (W : Set G.objects.left) :
    IsInvariantSet G W ↔ ⇑G.source.left ⁻¹' W = ⇑G.target.left ⁻¹' W := by
  refine ⟨fun h ↦ Set.eq_of_subset_of_subset (fun r hr ↦ h r hr) fun r hr ↦ ?_,
    fun h r hr ↦ h.subset hr⟩
  have := h (G.inverse.left r) (by simpa [Set.mem_preimage, source_inverse_apply] using hr)
  simpa [Set.mem_preimage, target_inverse_apply] using this

/-- Invariance of an open subscheme of the objects of a groupoid scheme is the equality of its
inverse images along the source and the target map.

**Stacks Project, Tag 03LO.** -/
theorem isInvariantOpen_iff_preimage_eq (W : G.objects.left.Opens) :
    IsInvariantOpen G W ↔ G.source.left ⁻¹ᵁ W = G.target.left ⁻¹ᵁ W := by
  rw [IsInvariantOpen, isInvariantSet_iff_preimage_eq, TopologicalSpace.Opens.ext_iff]
  rfl

end Stacks.Groupoids

namespace AlgebraicGeometry

open Stacks.Groupoids

/-! ### The source map of a cartesian groupoid scheme is an action -/

section CartesianOver

variable {S : Scheme.{u}} (G : GroupoidScheme S) (P : CartesianOver G)
  (V : EquivariantScheme G)
  (c : (cartesianOverEquivalenceEquivariantScheme G).functor.obj P ≅ V)

/-- The action of an equivariant scheme does not change when the point acted on is replaced by
an equal one. -/
theorem EquivariantScheme.action_congr {T : Over S} {v w : T ⟶ V.obj.left} (b : T ⟶ G.arrows)
    (hv : v ≫ V.obj.hom = b ≫ G.target) (hw : w ≫ V.obj.hom = b ≫ G.target) (h : v = w) :
    V.action v b hv = V.action w b hw := by
  subst h
  rfl

/-- The comparison from the object scheme of a groupoid scheme cartesian over `G` to the scheme
of an equivariant scheme presenting it, induced by an isomorphism with the equivariant scheme
that the equivalence of Tag 0APE produces. -/
def cartesianOverObjectsComparison : P.left.objects ⟶ V.obj.left :=
  (eqToHom (cartesianOverEquivalenceEquivariantScheme_obj_eq G P).symm).left ≫ c.hom.hom.left

/-- The comparison lies over the object scheme of `G`. -/
theorem cartesianOverObjectsComparison_comp :
    cartesianOverObjectsComparison G P V c ≫ V.obj.hom = P.hom.mapObjects := by
  rw [cartesianOverObjectsComparison, Category.assoc, Over.w, Over.w]
  rfl

/-- The target of an arrow, read in the equivariant scheme, lies over the target of the image
of that arrow in `G`. -/
theorem cartesianOverTarget_comp_comparison_comp :
    (P.left.target ≫ cartesianOverObjectsComparison G P V c) ≫ V.obj.hom =
      P.hom.mapArrows ≫ G.target := by
  rw [Category.assoc, cartesianOverObjectsComparison_comp]
  exact P.hom.map_target.symm

/-- **The source map of a groupoid scheme cartesian over `G` is the action.** Read in the
equivariant scheme presenting it, the source of an arrow is the action of the image of that
arrow in `G` on its target.

**Stacks Project, Tag 0APE.** -/
theorem cartesianOverSource_comp_comparison :
    P.left.source ≫ cartesianOverObjectsComparison G P V c =
      V.action (P.left.target ≫ cartesianOverObjectsComparison G P V c) P.hom.mapArrows
        (cartesianOverTarget_comp_comparison_comp G P V c) := by
  have heq := cartesianOverEquivalenceEquivariantScheme_obj_eq G P
  have w : (P.left.target ≫ (eqToHom heq.symm).left) ≫
      ((cartesianOverEquivalenceEquivariantScheme G).functor.obj P).obj.hom =
      P.hom.mapArrows ≫ G.target := by
    simpa only [Category.assoc, Over.w, Over.mk_hom] using P.hom.map_target.symm
  have hA : ((cartesianOverEquivalenceEquivariantScheme G).functor.obj P).action
        (P.left.target ≫ (eqToHom heq.symm).left) P.hom.mapArrows w =
      P.left.source ≫ (eqToHom heq.symm).left := by
    rw [EquivariantScheme.action, ← Category.assoc,
      cartesianOverEquivalenceEquivariantScheme_descentIso_hom G P, pullback.lift_snd]
  have hB := c.hom.comm P.left.arrows (P.left.target ≫ (eqToHom heq.symm).left)
    P.hom.mapArrows w
  rw [hA] at hB
  exact (Category.assoc P.left.source (eqToHom heq.symm).left c.hom.hom.left).symm.trans
    (hB.trans (EquivariantScheme.action_congr G V P.hom.mapArrows _ _
      (Category.assoc P.left.target (eqToHom heq.symm).left c.hom.hom.left)))

end CartesianOver

/-! ### Invariance for a descent datum relative to a single morphism -/

namespace DescentData

variable {S X : Scheme.{u}} {a : X ⟶ S} (D : DescentData (fun _ : Unit ↦ a))

/-- The gluing action is the action on the two projections of `V ×_S X`. -/
theorem actOn_eq_act :
    D.actOn = D.act (pullback.fst ((D.obj ()).hom ≫ a) a)
      (pullback.snd ((D.obj ()).hom ≫ a) a) pullback.condition := by
  simpa using D.comp_actOn (𝟙 _)

/-- The involution of `V ×_S X` carrying a pair `(v, x)` to the pair consisting of the action of
`x` on `v` and the image of `v` in `X`. It is the inversion of the groupoid scheme that the
descent datum presents, read on `V ×_S X`. -/
def actSwap : pullback ((D.obj ()).hom ≫ a) a ⟶ pullback ((D.obj ()).hom ≫ a) a :=
  pullback.lift D.actOn (pullback.fst ((D.obj ()).hom ≫ a) a ≫ (D.obj ()).hom)
    (by rw [← Category.assoc, D.actOn_hom, Category.assoc, pullback.condition])

/-- The first component of the involution of `V ×_S X` is the gluing action. -/
@[reassoc (attr := simp)]
theorem actSwap_fst : D.actSwap ≫ pullback.fst ((D.obj ()).hom ≫ a) a = D.actOn :=
  pullback.lift_fst _ _ _

/-- The second component of the involution of `V ×_S X` is the image in `X` of the point of
`V`. -/
@[reassoc (attr := simp)]
theorem actSwap_snd :
    D.actSwap ≫ pullback.snd ((D.obj ()).hom ≫ a) a =
      pullback.fst ((D.obj ()).hom ≫ a) a ≫ (D.obj ()).hom :=
  pullback.lift_snd _ _ _

/-- The involution exchanges the gluing action with the projection to `V`. -/
@[reassoc (attr := simp)]
theorem actSwap_actOn : D.actSwap ≫ D.actOn = pullback.fst ((D.obj ()).hom ≫ a) a := by
  have hc : D.actOn ≫ (D.obj ()).hom ≫ a =
      (pullback.fst ((D.obj ()).hom ≫ a) a ≫ (D.obj ()).hom) ≫ a := by
    rw [← Category.assoc, D.actOn_hom, Category.assoc, pullback.condition]
  have h1 : D.actSwap ≫ D.actOn =
      D.act D.actOn (pullback.fst ((D.obj ()).hom ≫ a) a ≫ (D.obj ()).hom) hc := by
    rw [D.comp_actOn D.actSwap]
    exact D.act_congr D.actSwap_fst D.actSwap_snd
  have hxz : pullback.snd ((D.obj ()).hom ≫ a) a ≫ a =
      (pullback.fst ((D.obj ()).hom ≫ a) a ≫ (D.obj ()).hom) ≫ a := by
    rw [Category.assoc]
    exact pullback.condition.symm
  rw [h1]
  exact (D.act_act_of D.actOn_eq_act rfl hxz).trans (D.act_self _)

/-- The map `AlgebraicGeometry.DescentData.actSwap` is an involution. -/
@[simp]
theorem actSwap_actSwap : D.actSwap ≫ D.actSwap = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.actSwap_fst, D.actSwap_actOn, Category.id_comp]
  · rw [Category.assoc, D.actSwap_snd, ← Category.assoc, D.actSwap_fst, D.actOn_hom,
      Category.id_comp]

/-- A subset `E` of the scheme `V` of a descent datum relative to a single morphism is
*invariant* when the gluing isomorphism carries the inverse image of `E` in `V ×_S X` onto its
inverse image in `X ×_S V`, set-theoretically. This is the condition `φ(E ×_S X) = X ×_S E` of
the source, for a subset which need not be open.

**Stacks Project, Tag 023W.** -/
def IsInvariantSet (E : Set (D.obj ()).left) : Prop :=
  ⇑D.actOn ⁻¹' E = ⇑(pullback.fst ((D.obj ()).hom ≫ a) a) ⁻¹' E

/-- Invariance of a subset only has to be checked in one direction: the reverse inclusion
follows by applying it to `AlgebraicGeometry.DescentData.actSwap`. -/
theorem isInvariantSet_iff_subset (E : Set (D.obj ()).left) :
    D.IsInvariantSet E ↔
      ⇑D.actOn ⁻¹' E ⊆ ⇑(pullback.fst ((D.obj ()).hom ≫ a) a) ⁻¹' E := by
  refine ⟨fun h ↦ h.subset, fun h ↦ Set.eq_of_subset_of_subset h fun z hz ↦ ?_⟩
  have h₁ : D.actOn (D.actSwap z) = pullback.fst ((D.obj ()).hom ≫ a) a z := by
    rw [← Scheme.Hom.comp_apply, D.actSwap_actOn]
  have h₂ : pullback.fst ((D.obj ()).hom ≫ a) a (D.actSwap z) = D.actOn z := by
    rw [← Scheme.Hom.comp_apply, D.actSwap_fst]
  have hmem := h (show D.actSwap z ∈ ⇑D.actOn ⁻¹' E from by rwa [Set.mem_preimage, h₁])
  rwa [Set.mem_preimage, h₂] at hmem

/-- For a descent datum relative to a single morphism, invariance of a family of open
subschemes is set-theoretic invariance of the one open subscheme it consists of. The family is
indexed by `Unit`, so no generality is lost in taking it constant.

**Stacks Project, Tag 023W.** -/
theorem isInvariantOpens_iff_isInvariantSet (W : (D.obj ()).left.Opens) :
    D.IsInvariantOpens (fun _ ↦ W) ↔ D.IsInvariantSet (W : Set (D.obj ()).left) := by
  rw [IsInvariantSet, ← Scheme.Hom.coe_preimage, ← Scheme.Hom.coe_preimage,
    ← TopologicalSpace.Opens.ext_iff]
  refine ⟨fun h ↦ ?_, fun h _ _ ↦ ?_⟩
  · rw [DescentData.actOn, Scheme.Hom.comp_preimage]
    exact h () ()
  · rw [← Scheme.Hom.comp_preimage]
    exact h

end DescentData

/-! ### The translation between the two notions of invariance -/

section Translation

variable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (D : DescentDatum f.left)

/-- The two projections of the kernel pair of `f`, read at a generalized point of it, lie over
the same point of `Y`. -/
theorem comp_cechKernelPair_condition {W : Over S} (b : W ⟶ pullback f f) :
    (b ≫ pullback.fst f f) ≫ f = (b ≫ pullback.snd f f) ≫ f := by
  rw [Category.assoc, cechKernelPair_condition, Category.assoc]

/-- **The object scheme of the cartesian groupoid scheme of a descent datum is `V`**, as a
scheme over the base. This is
`AlgebraicGeometry.cechDescentCartesianOverObjectsIso` read in schemes over `S` rather than in
schemes over `X`.

**Stacks Project, Tag 0APF.** -/
def cechDescentObjectsIso :
    (cechDescentCartesianOver f D).left.objects ≅ cechDescentObject f D :=
  (Over.forget X).mapIso (cechDescentCartesianOverObjectsIso f D)

/-- The structure morphism to `X` of the object scheme of the cartesian groupoid scheme of a
descent datum. -/
def cechDescentObjectsBase : (cechDescentCartesianOver f D).left.objects ⟶ X :=
  (cechDescentCartesianOver f D).hom.mapObjects

/-- The image in the kernel pair of `f` of an arrow of the cartesian groupoid scheme of a
descent datum. -/
def cechDescentArrowBase : (cechDescentCartesianOver f D).left.arrows ⟶ pullback f f :=
  (cechDescentCartesianOver f D).hom.mapArrows

/-- The point of `X` under the source of the image in the Čech groupoid of an arrow of the
cartesian groupoid scheme of a descent datum. -/
def cechDescentArrowSourceBase : (cechDescentCartesianOver f D).left.arrows ⟶ X :=
  cechDescentArrowBase f D ≫ pullback.snd f f

/-- The point of `X` under the target of the image in the Čech groupoid of an arrow of the
cartesian groupoid scheme of a descent datum. -/
def cechDescentArrowTargetBase : (cechDescentCartesianOver f D).left.arrows ⟶ X :=
  cechDescentArrowBase f D ≫ pullback.fst f f

/-- The source and the target of the image of an arrow in the Čech groupoid lie over the same
point of `Y`. -/
theorem cechDescentArrowBase_comp :
    cechDescentArrowTargetBase f D ≫ f = cechDescentArrowSourceBase f D ≫ f :=
  comp_cechKernelPair_condition f (cechDescentArrowBase f D)

/-- The identification of the object scheme with `V` lies over `X`. -/
theorem cechDescentObjectsIso_hom_comp_base :
    (cechDescentObjectsIso f D).hom ≫ cechDescentStructure f D = cechDescentObjectsBase f D :=
  Over.w (cechDescentCartesianOverObjectsIso f D).hom

/-- The inverse identification carries the structure morphism of the object scheme to the
structure morphism of `V`. -/
theorem cechDescentObjectsIso_inv_comp_base :
    (cechDescentObjectsIso f D).inv ≫ cechDescentObjectsBase f D = cechDescentStructure f D := by
  rw [← cechDescentObjectsIso_hom_comp_base, ← Category.assoc,
    (cechDescentObjectsIso f D).inv_hom_id, Category.id_comp]

/-- The inverse identification carries the structure morphism of the object scheme to the
structure morphism of `V`, on underlying schemes. -/
theorem cechDescentObjectsIso_inv_comp_base_left :
    (cechDescentObjectsIso f D).inv.left ≫ (cechDescentObjectsBase f D).left =
      (D.obj ()).hom :=
  congrArg Over.Hom.left (cechDescentObjectsIso_inv_comp_base f D)

/-- The target of an arrow, read in `V`, lies over the target of its image in the Čech
groupoid. -/
theorem cechDescentTarget_comp_objectsIso_comp_structure :
    ((cechDescentCartesianOver f D).left.target ≫ (cechDescentObjectsIso f D).hom) ≫
        cechDescentStructure f D =
      cechDescentArrowTargetBase f D := by
  rw [Category.assoc, cechDescentObjectsIso_hom_comp_base]
  exact ((cechDescentCartesianOver f D).hom.map_target).symm

/-- The target of an arrow, read in `V`, and the source of its image in the Čech groupoid lie
over the same point of `Y`. -/
theorem cechDescentTarget_arrow_condition :
    ((cechDescentCartesianOver f D).left.target ≫ (cechDescentObjectsIso f D).hom) ≫
        cechDescentStructure f D ≫ f =
      cechDescentArrowSourceBase f D ≫ f :=
  cechDescentPoint_condition f D
    ((cechDescentCartesianOver f D).left.target ≫ (cechDescentObjectsIso f D).hom)
    (cechDescentArrowBase f D) (cechDescentTarget_comp_objectsIso_comp_structure f D)

/-- **The source map of the cartesian groupoid scheme of a descent datum is the gluing
action.**

**Stacks Project, Tag 0APF.** -/
theorem cechDescentSource_comp_objectsIso :
    (cechDescentCartesianOver f D).left.source ≫ (cechDescentObjectsIso f D).hom =
      cechDescentAct f D
        ((cechDescentCartesianOver f D).left.target ≫ (cechDescentObjectsIso f D).hom)
        (cechDescentArrowSourceBase f D) (cechDescentTarget_arrow_condition f D) := by
  have h1 : (cechDescentCartesianOver f D).left.source ≫ (cechDescentObjectsIso f D).hom =
      (cechDescentEquivariantScheme f D).action
        ((cechDescentCartesianOver f D).left.target ≫ (cechDescentObjectsIso f D).hom)
        (cechDescentArrowBase f D)
        (cechDescentTarget_comp_objectsIso_comp_structure f D) :=
    cartesianOverSource_comp_comparison (cechGroupoid f) (cechDescentCartesianOver f D)
      (cechDescentEquivariantScheme f D)
      ((cartesianOverEquivalenceEquivariantScheme (cechGroupoid f)).counitIso.app
        (cechDescentEquivariantScheme f D))
  rw [h1]
  exact cechDescentEquivariantScheme_action f D _ _ _ (cechDescentTarget_arrow_condition f D)

/-- The source of an arrow, read in `V`, lies over the source of its image in the Čech
groupoid. -/
theorem cechDescentSource_comp_objectsIso_comp_structure :
    ((cechDescentCartesianOver f D).left.source ≫ (cechDescentObjectsIso f D).hom) ≫
        cechDescentStructure f D =
      cechDescentArrowSourceBase f D := by
  rw [cechDescentSource_comp_objectsIso, cechDescentAct_comp_structure]

/-- The source of an arrow, read in `V`, and the target of its image in the Čech groupoid lie
over the same point of `Y`. -/
theorem cechDescentSource_arrow_condition :
    ((cechDescentCartesianOver f D).left.source ≫ (cechDescentObjectsIso f D).hom) ≫
        cechDescentStructure f D ≫ f =
      cechDescentArrowTargetBase f D ≫ f :=
  calc ((cechDescentCartesianOver f D).left.source ≫ (cechDescentObjectsIso f D).hom) ≫
          cechDescentStructure f D ≫ f
      = (((cechDescentCartesianOver f D).left.source ≫ (cechDescentObjectsIso f D).hom) ≫
          cechDescentStructure f D) ≫ f := (Category.assoc _ _ _).symm
    _ = cechDescentArrowSourceBase f D ≫ f := by
        rw [cechDescentSource_comp_objectsIso_comp_structure]
    _ = cechDescentArrowTargetBase f D ≫ f := (cechDescentArrowBase_comp f D).symm

/-- An arrow of the cartesian groupoid scheme of a descent datum, read as a point of
`V ×_Y X`: its target in `V`, together with the source of its image in the Čech groupoid. -/
def cechDescentArrowComparison :
    (cechDescentCartesianOver f D).left.arrows.left ⟶
      pullback ((D.obj ()).hom ≫ f.left) f.left :=
  pullback.lift
    ((cechDescentCartesianOver f D).left.target ≫ (cechDescentObjectsIso f D).hom).left
    (cechDescentArrowSourceBase f D).left
    (cechDescentStructure_comp_left f D
      ((cechDescentCartesianOver f D).left.target ≫ (cechDescentObjectsIso f D).hom)
      (cechDescentArrowSourceBase f D) (cechDescentTarget_arrow_condition f D))

/-- The first component of the comparison is the target of the arrow, read in `V`. -/
@[reassoc (attr := simp)]
theorem cechDescentArrowComparison_fst :
    cechDescentArrowComparison f D ≫ pullback.fst ((D.obj ()).hom ≫ f.left) f.left =
      ((cechDescentCartesianOver f D).left.target ≫ (cechDescentObjectsIso f D).hom).left :=
  pullback.lift_fst _ _ _

/-- The second component of the comparison is the point of `X` under the source of the image of
the arrow in the Čech groupoid. -/
@[reassoc (attr := simp)]
theorem cechDescentArrowComparison_snd :
    cechDescentArrowComparison f D ≫ pullback.snd ((D.obj ()).hom ≫ f.left) f.left =
      (cechDescentArrowSourceBase f D).left :=
  pullback.lift_snd _ _ _

/-- The comparison carries the gluing action to the source map. -/
@[reassoc (attr := simp)]
theorem cechDescentArrowComparison_actOn :
    cechDescentArrowComparison f D ≫ D.actOn =
      ((cechDescentCartesianOver f D).left.source ≫ (cechDescentObjectsIso f D).hom).left := by
  rw [cechDescentSource_comp_objectsIso, cechDescentAct_left]
  rfl

/-- The comparison carries the projection to `V`, followed by the structure morphism, to the
target of the image of the arrow in the Čech groupoid. -/
theorem cechDescentArrowComparison_comp_fst_comp_structure :
    (cechDescentArrowComparison f D ≫ pullback.fst ((D.obj ()).hom ≫ f.left) f.left) ≫
        (D.obj ()).hom =
      (cechDescentArrowTargetBase f D).left := by
  have h0 : ((cechDescentCartesianOver f D).left.target ≫
        (cechDescentObjectsIso f D).hom).left ≫ (cechDescentStructure f D).left =
      (cechDescentArrowTargetBase f D).left := by
    rw [← Over.comp_left]
    exact congrArg Over.Hom.left (cechDescentTarget_comp_objectsIso_comp_structure f D)
  rw [cechDescentArrowComparison_fst]
  exact h0

/-- The comparison, composed with the involution of `V ×_Y X`: the source map together with the
target of the image of the arrow in the Čech groupoid. -/
theorem cechDescentArrowComparison_actSwap :
    cechDescentArrowComparison f D ≫ D.actSwap =
      pullback.lift
        ((cechDescentCartesianOver f D).left.source ≫ (cechDescentObjectsIso f D).hom).left
        (cechDescentArrowTargetBase f D).left
        (cechDescentStructure_comp_left f D
          ((cechDescentCartesianOver f D).left.source ≫ (cechDescentObjectsIso f D).hom)
          (cechDescentArrowTargetBase f D) (cechDescentSource_arrow_condition f D)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.actSwap_fst, cechDescentArrowComparison_actOn, pullback.lift_fst]
  · rw [Category.assoc, D.actSwap_snd, ← Category.assoc,
      cechDescentArrowComparison_comp_fst_comp_structure, pullback.lift_snd]

/-- The arrow of the Čech groupoid attached to a point of `V ×_Y X`: the given point of `X`
together with the image in `X` of the given point of `V`. -/
def cechDescentSectionArrow :
    pullback ((D.obj ()).hom ≫ f.left) f.left ⟶ (pullback f f).left :=
  pullback.lift (pullback.snd ((D.obj ()).hom ≫ f.left) f.left)
      (pullback.fst ((D.obj ()).hom ≫ f.left) f.left ≫ (D.obj ()).hom)
      (by rw [Category.assoc]; exact pullback.condition.symm) ≫
    (overPullbackLeftIso f f).inv

/-- The first projection of the Čech arrow attached to a point of `V ×_Y X` is its point of
`X`. -/
theorem cechDescentSectionArrow_comp_fst :
    cechDescentSectionArrow f D ≫ (pullback.fst f f).left =
      pullback.snd ((D.obj ()).hom ≫ f.left) f.left := by
  rw [cechDescentSectionArrow, Category.assoc, overPullbackLeftIso_inv_fst, pullback.lift_fst]

/-- The second projection of the Čech arrow attached to a point of `V ×_Y X` is the image in `X`
of its point of `V`. -/
theorem cechDescentSectionArrow_comp_snd :
    cechDescentSectionArrow f D ≫ (pullback.snd f f).left =
      pullback.fst ((D.obj ()).hom ≫ f.left) f.left ≫ (D.obj ()).hom := by
  rw [cechDescentSectionArrow, Category.assoc, overPullbackLeftIso_inv_snd, pullback.lift_snd]

/-- The second projection of the Čech arrow attached to a point of `V ×_Y X` is the structure
morphism to `X` of its point of `V`, read in the object scheme. -/
theorem cechDescentSectionArrow_condition :
    cechDescentSectionArrow f D ≫ (pullback.snd f f).left =
      (pullback.fst ((D.obj ()).hom ≫ f.left) f.left ≫
          (cechDescentObjectsIso f D).inv.left) ≫ (cechDescentObjectsBase f D).left := by
  rw [cechDescentSectionArrow_comp_snd, Category.assoc,
    cechDescentObjectsIso_inv_comp_base_left]

/-- A point of `V ×_Y X` determines an arrow of the cartesian groupoid scheme of `D` whose
source is the given point of `V` and whose image in the Čech groupoid is the pair consisting of
the given point of `X` and the image of the given point of `V`. -/
def cechDescentArrowSection :
    pullback ((D.obj ()).hom ≫ f.left) f.left ⟶
      (cechDescentCartesianOver f D).left.arrows.left :=
  (cechDescentCartesianOver f D).isCartesian.lift (cechDescentSectionArrow f D)
    (pullback.fst ((D.obj ()).hom ≫ f.left) f.left ≫ (cechDescentObjectsIso f D).inv.left)
    (cechDescentSectionArrow_condition f D)

/-- The image in the Čech groupoid of the arrow attached to a point of `V ×_Y X` is
`AlgebraicGeometry.cechDescentSectionArrow`. -/
theorem cechDescentArrowSection_comp_arrowBase :
    cechDescentArrowSection f D ≫ (cechDescentArrowBase f D).left =
      cechDescentSectionArrow f D :=
  (cechDescentCartesianOver f D).isCartesian.lift_fst _ _ _

/-- The source of the arrow attached to a point of `V ×_Y X` is its point of `V`, read in the
object scheme. -/
theorem cechDescentArrowSection_comp_sourceLeft :
    cechDescentArrowSection f D ≫ (cechDescentCartesianOver f D).left.source.left =
      pullback.fst ((D.obj ()).hom ≫ f.left) f.left ≫
        (cechDescentObjectsIso f D).inv.left :=
  (cechDescentCartesianOver f D).isCartesian.lift_snd _ _ _

/-- The source, read in `V`, of the arrow attached to a point of `V ×_Y X` is its point of `V`. -/
theorem cechDescentArrowSection_comp_source :
    cechDescentArrowSection f D ≫ (cechDescentCartesianOver f D).left.source.left ≫
        (cechDescentObjectsIso f D).hom.left =
      pullback.fst ((D.obj ()).hom ≫ f.left) f.left := by
  rw [← Category.assoc, cechDescentArrowSection_comp_sourceLeft, Category.assoc,
    ← Over.comp_left, (cechDescentObjectsIso f D).inv_hom_id]
  simp

/-- An arrow is recovered from its source and the target of its image in the Čech groupoid. -/
theorem cechDescentArrowSection_comp_comparison_actSwap :
    cechDescentArrowSection f D ≫ cechDescentArrowComparison f D ≫ D.actSwap = 𝟙 _ := by
  rw [cechDescentArrowComparison_actSwap]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.id_comp, Over.comp_left]
    exact cechDescentArrowSection_comp_source f D
  · rw [Category.assoc, pullback.lift_snd, Category.id_comp, cechDescentArrowTargetBase,
      Over.comp_left, ← Category.assoc, cechDescentArrowSection_comp_arrowBase]
    exact cechDescentSectionArrow_comp_fst f D

/-- The arrow attached to a point of `V ×_Y X`, followed by the comparison, is the involution
`AlgebraicGeometry.DescentData.actSwap`. -/
theorem cechDescentArrowSection_comp_comparison :
    cechDescentArrowSection f D ≫ cechDescentArrowComparison f D = D.actSwap := by
  calc _ = (cechDescentArrowSection f D ≫ cechDescentArrowComparison f D) ≫
        (D.actSwap ≫ D.actSwap) := by rw [D.actSwap_actSwap, Category.comp_id]
    _ = D.actSwap := by
      rw [← Category.assoc, Category.assoc (cechDescentArrowSection f D),
        cechDescentArrowSection_comp_comparison_actSwap, Category.id_comp]

/-- The comparison is a split epimorphism. -/
theorem cechDescentArrowComparison_section :
    (D.actSwap ≫ cechDescentArrowSection f D) ≫ cechDescentArrowComparison f D = 𝟙 _ := by
  rw [Category.assoc, cechDescentArrowSection_comp_comparison, D.actSwap_actSwap]

/-- Every point of `V ×_Y X` comes from an arrow of the cartesian groupoid scheme of `D`. -/
theorem cechDescentArrowComparison_surjective :
    Function.Surjective ⇑(cechDescentArrowComparison f D) := by
  intro z
  refine ⟨(D.actSwap ≫ cechDescentArrowSection f D) z, ?_⟩
  rw [← Scheme.Hom.comp_apply, cechDescentArrowComparison_section]
  simp

/-- **The translation between the two notions of invariance, for subsets.** A subset of `V` is
set-theoretically invariant under the cartesian groupoid scheme that a descent datum presents
if and only if it is set-theoretically invariant for the descent datum. This is the
set-theoretic half of step 4 of the proof of Tag 0APK.

**Stacks Project, Tag 0APK.** -/
theorem isInvariantSet_cechDescent_iff (E : Set (D.obj ()).left) :
    Stacks.Groupoids.IsInvariantSet (cechDescentCartesianOver f D).left
        (⇑(cechDescentObjectsIso f D).hom.left ⁻¹' E) ↔ D.IsInvariantSet E := by
  have key : ∀ (a : (cechDescentCartesianOver f D).left.arrows.left ⟶
        (cechDescentCartesianOver f D).left.objects.left) (k : pullback ((D.obj ()).hom ≫ f.left)
        f.left ⟶ (D.obj ()).left),
      a ≫ (cechDescentObjectsIso f D).hom.left = cechDescentArrowComparison f D ≫ k →
      ⇑a ⁻¹' (⇑(cechDescentObjectsIso f D).hom.left ⁻¹' E) =
        ⇑(cechDescentArrowComparison f D) ⁻¹' (⇑k ⁻¹' E) := fun a k h ↦
    Set.ext fun r ↦ by simp only [Set.mem_preimage, ← Scheme.Hom.comp_apply, h]
  have hs := key (cechDescentCartesianOver f D).left.source.left D.actOn (by
    rw [← Over.comp_left, ← cechDescentArrowComparison_actOn])
  have ht := key (cechDescentCartesianOver f D).left.target.left
    (pullback.fst ((D.obj ()).hom ≫ f.left) f.left) (by
    rw [← Over.comp_left, ← cechDescentArrowComparison_fst])
  rw [Stacks.Groupoids.isInvariantSet_iff_preimage_eq, hs, ht, DescentData.IsInvariantSet]
  exact (cechDescentArrowComparison_surjective f D).preimage_injective.eq_iff

/-- **The translation between the two notions of invariance, for opens.** An open subscheme of
`V` is invariant under the cartesian groupoid scheme that a descent datum presents if and only
if it is invariant for the descent datum. This is step 4 of the proof of Tag 0APK.

**Stacks Project, Tag 0APK.** -/
theorem isInvariantOpen_cechDescent_iff (W : (D.obj ()).left.Opens) :
    Stacks.Groupoids.IsInvariantOpen (cechDescentCartesianOver f D).left
        ((cechDescentObjectsIso f D).hom.left ⁻¹ᵁ W) ↔
      D.IsInvariantOpens (fun _ ↦ W) := by
  rw [DescentData.isInvariantOpens_iff_isInvariantSet, ← isInvariantSet_cechDescent_iff f D]
  exact Iff.rfl

/-- Every subset of the object scheme of the cartesian groupoid scheme of `D` is the inverse
image of a subset of `V`. -/
@[simp]
theorem cechDescentObjectsIso_hom_preimage_inv_preimage
    (E : Set (cechDescentCartesianOver f D).left.objects.left) :
    ⇑(cechDescentObjectsIso f D).hom.left ⁻¹' (⇑(cechDescentObjectsIso f D).inv.left ⁻¹' E) =
      E := by
  rw [← Set.preimage_comp]
  refine Set.ext fun r ↦ ?_
  have h : (cechDescentObjectsIso f D).inv.left
      ((cechDescentObjectsIso f D).hom.left r) = r := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left,
      (cechDescentObjectsIso f D).hom_inv_id]
    simp
  rw [Set.mem_preimage, Function.comp_apply, h]

/-- Every open of the object scheme of the cartesian groupoid scheme of `D` is the inverse
image of an open of `V`. -/
@[simp]
theorem cechDescentObjectsIso_hom_preimage_inv_preimage_opens
    (W : (cechDescentCartesianOver f D).left.objects.left.Opens) :
    (cechDescentObjectsIso f D).hom.left ⁻¹ᵁ
        ((cechDescentObjectsIso f D).inv.left ⁻¹ᵁ W) = W :=
  TopologicalSpace.Opens.ext (cechDescentObjectsIso_hom_preimage_inv_preimage f D
    (W : Set (cechDescentCartesianOver f D).left.objects.left))

/-- **The translation, for an arbitrary subset of the object scheme.** This is the form in
which step 4 of the proof of Tag 0APK uses it: a set-theoretically invariant subset of the
object scheme of the cartesian groupoid scheme becomes a set-theoretically invariant subset
of `V`, and conversely.

**Stacks Project, Tag 0APK.** -/
theorem isInvariantSet_cechDescentCartesianOver_iff
    (E : Set (cechDescentCartesianOver f D).left.objects.left) :
    Stacks.Groupoids.IsInvariantSet (cechDescentCartesianOver f D).left E ↔
      D.IsInvariantSet (⇑(cechDescentObjectsIso f D).inv.left ⁻¹' E) := by
  rw [← isInvariantSet_cechDescent_iff f D (⇑(cechDescentObjectsIso f D).inv.left ⁻¹' E),
    cechDescentObjectsIso_hom_preimage_inv_preimage]

/-- **The translation, for an arbitrary open of the object scheme.** This is the form in which
step 4 of the proof of Tag 0APK uses it: an invariant open of the object scheme of the
cartesian groupoid scheme becomes an invariant open of `V`, and conversely.

**Stacks Project, Tag 0APK.** -/
theorem isInvariantOpen_cechDescentCartesianOver_iff
    (W : (cechDescentCartesianOver f D).left.objects.left.Opens) :
    Stacks.Groupoids.IsInvariantOpen (cechDescentCartesianOver f D).left W ↔
      D.IsInvariantOpens (fun _ ↦ (cechDescentObjectsIso f D).inv.left ⁻¹ᵁ W) := by
  rw [← isInvariantOpen_cechDescent_iff f D ((cechDescentObjectsIso f D).inv.left ⁻¹ᵁ W),
    cechDescentObjectsIso_hom_preimage_inv_preimage_opens]

end Translation

end AlgebraicGeometry

end

end
