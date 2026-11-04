module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent transports, and their effectivity

A descent datum relative to a morphism `f : X ⟶ B`, read on generalized points, is an operation
taking a point of the scheme `V` over `X` and a point `b` of `X` to a new point of `V` lying
over `b`, subject to three laws: moving a point to the point of `X` it already lies over does
nothing, moving twice is moving once, and the operation commutes with change of test object.
This is `AlgebraicGeometry.DescentTransport`. A descent transport determines an
`AlgebraicGeometry.DescentData`, and a descent transport in a slice of `Over S` is effective
under separatedness and finiteness hypotheses.

## Main definitions

* `AlgebraicGeometry.DescentTransport` is the operation described above.
* `AlgebraicGeometry.transportGluing` and `AlgebraicGeometry.transportDescentData` are the
  gluing isomorphism and the descent datum it determines.
* `AlgebraicGeometry.DescentTransport.mapRightAdjoint` transports the operation along a right
  adjoint.

## Main results

* `AlgebraicGeometry.DescentDatum.Descended.proj_act`: the projection onto a descended scheme is
  invariant for the gluing action of the datum, read on generalized points.
* `AlgebraicGeometry.transportDescentData_act`: the gluing action of the descent datum of a
  transport is the transport.
* `AlgebraicGeometry.exists_effectiveTransport`: **a descent transport in a slice of `Over S`
  whose structure morphism is separated, locally quasi-finite and locally of finite type is
  effective along a surjective flat quasi-compact covering** — the scheme it is carried by
  descends, and the projection onto the descended scheme is invariant for the transport.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms Opposite

universe u

namespace AlgebraicGeometry

namespace DescentDatum.Descended

variable {X B : Scheme.{u}} {f : X ⟶ B} {D : DescentDatum f}

/-- A generalized point of a product in a slice, read on the literal fibre product. -/
lemma prodLift_left_comp_prodLeftIsoPullback {A A' : Over B} {T : Over B} (v : T ⟶ A)
    (x : T ⟶ A') (h : v.left ≫ A.hom = x.left ≫ A'.hom) :
    (prod.lift v x).left ≫ (Over.prodLeftIsoPullback A A').hom =
      pullback.lift v.left x.left h := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst, Over.prodLeftIsoPullback_hom_snd,
      pullback.lift_fst, pullback.lift_snd, ← Over.comp_left, prod.lift_fst, prod.lift_snd]

/-- **The projection of a descended scheme is invariant for the gluing action.**  This is
`AlgebraicGeometry.DescentDatum.Descended.proj_invariant` read on generalized points. -/
lemma proj_act (Q : D.Descended) {T : Over B} (v : T ⟶ (Over.map f).obj D.over)
    (x : T ⟶ Over.mk f) : (D.act v x).left ≫ Q.proj = v.left ≫ Q.proj := by
  have hvx : v.left ≫ ((Over.map f).obj D.over).hom = x.left ≫ (Over.mk f).hom :=
    (Over.w v).trans (Over.w x).symm
  have hiso : D.transitionPullbackIso.hom =
      (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫
        (D.transition.hom.left).left ≫
        (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom := by
    rfl
  have hfst : (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom ≫
      pullback.fst ((Over.map f).obj D.over).hom (Over.mk f).hom =
      (prod.fst : (Over.map f).obj D.over ⨯ Over.mk f ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  have hsnd : (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom ≫
      pullback.snd (Over.mk f).hom ((Over.map f).obj D.over).hom =
      (prod.snd : Over.mk f ⨯ (Over.map f).obj D.over ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have h := congrArg (pullback.lift v.left x.left hvx ≫ ·) Q.proj_invariant
  simp only [hiso, Category.assoc] at h
  rw [← Category.assoc (pullback.lift v.left x.left hvx),
    ← prodLift_left_comp_prodLeftIsoPullback v x hvx] at h
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
  have goalL : (D.act v x).left ≫ Q.proj =
      (prod.lift v x).left ≫ (D.transition.hom.left).left ≫
        (prod.snd : Over.mk f ⨯ (Over.map f).obj D.over ⟶ _).left ≫ Q.proj := by
    rw [DescentDatum.act, gluingAction]
    simp only [Over.comp_left, Category.assoc]
  have goalR : v.left ≫ Q.proj =
      (prod.lift v x).left ≫
        (prod.fst : (Over.map f).obj D.over ⨯ Over.mk f ⟶ _).left ≫ Q.proj := by
    rw [← Category.assoc, ← Over.comp_left, prod.lift_fst]
  rw [goalL, goalR, ← hsnd, ← hfst]
  simp only [Category.assoc] at h ⊢
  exact h

end DescentDatum.Descended

/-- A descent transport for `p : V ⟶ X`: an operation moving a generalized point `a` of `V` to
a point of `V` lying over a given generalized point `b` of `X`, which fixes a point moved to the
point of `X` it already lies over, for which moving twice is moving once, and which commutes with
change of test object. -/
structure DescentTransport {C : Type*} [Category C] {V X : C} (p : V ⟶ X) where
  /-- The point of `V` obtained by moving `a` to lie over `b`. -/
  move : ∀ {T : C}, (T ⟶ V) → (T ⟶ X) → (T ⟶ V)
  /-- The moved point lies over `b`. -/
  base : ∀ {T : C} (a : T ⟶ V) (b : T ⟶ X), move a b ≫ p = b
  /-- Moving a point to the point of `X` it lies over does nothing. -/
  refl : ∀ {T : C} (a : T ⟶ V), move a (a ≫ p) = a
  /-- Moving twice is moving once, to the second point. -/
  trans : ∀ {T : C} (a : T ⟶ V) (b c : T ⟶ X), move (move a b) c = move a c
  /-- The operation commutes with precomposition by a morphism of test objects. -/
  naturality : ∀ {T T' : C} (f : T' ⟶ T) (a : T ⟶ V) (b : T ⟶ X),
    f ≫ move a b = move (f ≫ a) (f ≫ b)

/-- The isomorphism `V ⨯ X ≅ X ⨯ V` determined by a descent transport, sending `(a, b)` to
`(a ≫ p, d.move a b)`. -/
noncomputable def transportGluing {C : Type*} [Category C] [HasBinaryProducts C]
    {V X : C} {p : V ⟶ X} (d : DescentTransport p) : V ⨯ X ≅ X ⨯ V where
  hom := prod.lift (prod.fst ≫ p) (d.move prod.fst prod.snd)
  inv := prod.lift (d.move prod.snd prod.fst) (prod.snd ≫ p)
  hom_inv_id := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, d.naturality, prod.lift_snd]
      rw [d.trans, d.refl]
      simp
    · simp [d.base]
  inv_hom_id := by
    apply prod.hom_ext
    · simp [d.base]
    · simp only [Category.assoc, prod.lift_snd, d.naturality, prod.lift_fst]
      rw [d.trans, d.refl]
      simp

/-- The descent datum along `f` on the scheme `W` over `X` whose gluing isomorphism is
`AlgebraicGeometry.transportGluing d`. -/
noncomputable def transportDescentData {B X : Scheme.{u}} (f : X ⟶ B)
    (W : Over X) (d : DescentTransport (structureMap f W)) :
    AlgebraicGeometry.DescentData (fun _ : Unit ↦ f) where
  obj _ := W
  gluing _ _ := Over.isoMk (transportGluing d) (by
    apply prod.hom_ext <;> simp [transportGluing, d.base])
  cocycle _ _ _ := by
    apply prod.hom_ext
    · apply prod.hom_ext <;>
        simp [transportGluing, prodMapLastTwo, prodMapFirstThird,
          d.base, d.naturality]
    · simp [transportGluing, prodMapLastTwo, prodMapFirstThird,
        d.base, d.naturality, d.trans]

/-- The descent transport for `F.map p` obtained from a descent transport for `p` and a right
adjoint `F`, by moving points through the adjunction bijection. -/
noncomputable def DescentTransport.mapRightAdjoint
    {C D : Type*} [Category C] [Category D] {L : D ⥤ C} {F : C ⥤ D}
    (adj : L ⊣ F) {V X : C} {p : V ⟶ X} (d : DescentTransport p) :
    DescentTransport (F.map p) where
  move {T} a b := adj.homEquiv T V
    (d.move ((adj.homEquiv T V).symm a) ((adj.homEquiv T X).symm b))
  base a b := by
    rw [← adj.homEquiv_naturality_right, d.base, Equiv.apply_symm_apply]
  refl a := by
    rw [adj.homEquiv_naturality_right_symm, d.refl, Equiv.apply_symm_apply]
  trans a b c := by simp only [Equiv.symm_apply_apply, d.trans]
  naturality f a b := by
    rw [← adj.homEquiv_naturality_left, d.naturality,
      adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_left_symm]

/-- On images of points under `F`, the transport `d.mapRightAdjoint adj` is the image under `F`
of the transport `d`. -/
lemma DescentTransport.mapRightAdjoint_move_map
    {C D : Type*} [Category C] [Category D] {L : D ⥤ C} {F : C ⥤ D}
    (adj : L ⊣ F) {V X : C} {p : V ⟶ X} (d : DescentTransport p)
    {T : C} (a : T ⟶ V) (b : T ⟶ X) :
    (d.mapRightAdjoint adj).move (F.map a) (F.map b) = F.map (d.move a b) := by
  simp only [DescentTransport.mapRightAdjoint, Adjunction.homEquiv_symm_apply]
  change adj.homEquiv _ _ (d.move
    ((F ⋙ L).map a ≫ adj.counit.app V) ((F ⋙ L).map b ≫ adj.counit.app X)) = _
  rw [adj.counit.naturality a, adj.counit.naturality b]
  simp only [Functor.id_map, ← d.naturality, Adjunction.homEquiv_apply,
    Functor.map_comp, ← Category.assoc, adj.right_triangle_components, Category.id_comp]

/-- The gluing action of the descent datum of a descent transport is the transport. -/
lemma transportDescentData_act {B X : Scheme.{u}} (f : X ⟶ B) (W : Over X)
    (d : DescentTransport (structureMap f W)) {T : Over B}
    (v : T ⟶ (Over.map f).obj W) (x : T ⟶ Over.mk f) :
    DescentDatum.act (transportDescentData f W d) v x = d.move v x := by
  change prod.lift v x ≫
    prod.lift (prod.fst ≫ structureMap f W) (d.move prod.fst prod.snd) ≫ prod.snd = d.move v x
  rw [prod.lift_snd, d.naturality, prod.lift_fst, prod.lift_snd]

/-- **A descent transport whose structure morphism is separated, locally quasi-finite and
locally of finite type is effective**, along a surjective flat quasi-compact covering: the
scheme it is carried by descends, and the projection to the descended scheme is invariant for
the transport. -/
@[sga "3 X 5.4" "special case"]
lemma exists_effectiveTransport {S : Scheme.{u}} {R X B : Over S}
    (p : R ⟶ X) (f : X ⟶ B)
    (d : DescentTransport (Over.homMk p : Over.mk (p ≫ f) ⟶ Over.mk f))
    [Surjective f.left] [Flat f.left] [QuasiCompact f.left]
    [IsSeparated p.left] [LocallyOfFiniteType p.left] [LocallyQuasiFinite p.left] :
    ∃ (Y : Over S) (j : Y ⟶ B) (r : R ⟶ Y), IsPullback r p j f ∧
      ∀ {T : Over B} (a : T ⟶ Over.mk (p ≫ f)) (b : T ⟶ Over.mk f),
        (d.move a b).left ≫ r = a.left ≫ r := by
  let E := Over.iteratedSliceEquiv B
  let d' : DescentTransport (structureMap f.left (Over.mk p.left)) :=
    d.mapRightAdjoint E.symm.toAdjunction
  obtain ⟨Q⟩ := DescentDatum.nonempty_descended_of_isEffective
    (DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite
      (transportDescentData f.left (Over.mk p.left) d')
      (show IsSeparated p.left from inferInstance)
      (show LocallyQuasiFinite p.left from inferInstance)
      (show LocallyOfFiniteType p.left from inferInstance))
  have hw : Q.proj ≫ Q.base.hom = p.left ≫ f.left := Q.isPullback.w.symm
  have hw2 : (p.left ≫ f.left) ≫ B.hom = R.hom := by
    rw [Category.assoc, Over.w f, Over.w p]
  let r : R ⟶ (Over.map B.hom).obj Q.base := Over.homMk Q.proj (by
    change Q.proj ≫ Q.base.hom ≫ B.hom = R.hom
    rw [← Category.assoc, hw]
    exact hw2)
  let j : (Over.map B.hom).obj Q.base ⟶ B := Over.homMk Q.base.hom
  refine ⟨_, j, r, ?_, ?_⟩
  · apply IsPullback.of_map (Over.forget S) _
    · exact Q.isPullback.flip
    · exact Over.OverMorphism.ext hw
  · intro T a b
    have hact := transportDescentData_act f.left (Over.mk p.left) d'
      (E.functor.map a) (E.functor.map b)
    have h := Q.proj_act (E.functor.map a) (E.functor.map b)
    rw [hact] at h
    have hmap := DescentTransport.mapRightAdjoint_move_map E.symm.toAdjunction d a b
    change d'.move (E.functor.map a) (E.functor.map b) = E.functor.map (d.move a b) at hmap
    rw [hmap] at h
    refine Over.OverMorphism.ext ?_
    rw [Over.comp_left, Over.comp_left]
    exact h

end AlgebraicGeometry

end
