module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.GlueingClosedFibre

/-!
# The pushout of Tag 0E25 is cartesian over the base

Let `s` be a situation of [Stacks Project, Tag 0ECI] and let `a : T ⟶ s.S` be a flat, separated,
locally quasi-finite morphism to its base.  If a cartesian diagram `d` over `s` is the base
change of the span of `s` along `a` -- meaning that the two squares relating its verticals to
the structure morphisms of `s` are cartesian over `a` -- then the induced morphism of pushouts
is cartesian over `a` as well:

```
Y' ⨿_{Z'} X' -----> Y ⨿_Z X
     |                 |
     v                 v
     T ------a-------> s.S
```

This is the form in which [Stacks Project, Tag 0ECL] is used to descend the pushout along an
étale chart of an algebraic space: it identifies the pushout formed over a chart with the base
change of the pushout formed over a larger chart, and that identification is what turns an
equivalence relation on the chart into an equivalence relation on the pushout.

## Main results

* `AlgebraicGeometry.isIso_triplePushoutMap`: a morphism of cartesian diagrams whose three
  components are isomorphisms induces an isomorphism of pushouts.
* `AlgebraicGeometry.isPullback_pushoutMap_of_isPullback`: the square displayed above is
  cartesian.

## Implementation notes

The proof compares the given diagram `d` with the canonical base-change diagram
`AlgebraicGeometry.pushoutSpanBaseChangeDiagram` attached to the base change
`(Y ⨿_Z X) ×_{s.S} T` of the pushout itself.  [Stacks Project, Tag 0ECL],
`AlgebraicGeometry.isIso_pushoutBaseChangeMap`, says the pushout of that canonical diagram *is*
the base change; full faithfulness of the pushout construction on cartesian diagrams,
`AlgebraicGeometry.exists_cartesianTripleHom_of_comp_pushoutMap`, turns the comparison morphism
of pushouts into a morphism of diagrams, and each of its three components is an isomorphism
because source and target are pullbacks of the same cospan.  No new geometry is used.

The hypotheses are phrased with the structure morphism `π` of the induced pushout to `T` given
rather than constructed, together with its two restrictions.  That is what the caller has: the
pushout formed over the smaller chart comes with its own structure morphism, and the two
restrictions identify it with the one the universal property would produce.

## References

* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ECK](https://stacks.math.columbia.edu/tag/0ECK)
* [Stacks Project, Tag 0ECL](https://stacks.math.columbia.edu/tag/0ECL)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}

/-- The componentwise inverse of a morphism of cartesian diagrams whose three components are
isomorphisms. -/
def CartesianTripleHom.inv {d e : CartesianDiagram s} (m : CartesianTripleHom d e)
    [IsIso m.x] [IsIso m.y] [IsIso m.z] : CartesianTripleHom e d where
  x := CategoryTheory.inv m.x
  y := CategoryTheory.inv m.y
  z := CategoryTheory.inv m.z
  left := by
    apply (cancel_epi m.z).1
    rw [← Category.assoc, ← m.left, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  right := by
    apply (cancel_epi m.z).1
    rw [← Category.assoc, ← m.right, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  overX := by rw [← m.overX, IsIso.inv_hom_id_assoc]
  overY := by rw [← m.overY, IsIso.inv_hom_id_assoc]
  overZ := by rw [← m.overZ, IsIso.inv_hom_id_assoc]

/-- A morphism of cartesian diagrams whose three components are isomorphisms induces an
isomorphism of the two pushouts. -/
theorem isIso_triplePushoutMap {d e : CartesianDiagram s} (m : CartesianTripleHom d e)
    [IsIso m.x] [IsIso m.y] [IsIso m.z] : IsIso (triplePushoutMap m) := by
  have hmn : CartesianTripleHom.comp m m.inv = CartesianTripleHom.id d :=
    CartesianTripleHom.ext (by simp [CartesianTripleHom.comp, CartesianTripleHom.inv,
        CartesianTripleHom.id])
      (by simp [CartesianTripleHom.comp, CartesianTripleHom.inv, CartesianTripleHom.id])
      (by simp [CartesianTripleHom.comp, CartesianTripleHom.inv, CartesianTripleHom.id])
  have hnm : CartesianTripleHom.comp m.inv m = CartesianTripleHom.id e :=
    CartesianTripleHom.ext (by simp [CartesianTripleHom.comp, CartesianTripleHom.inv,
        CartesianTripleHom.id])
      (by simp [CartesianTripleHom.comp, CartesianTripleHom.inv, CartesianTripleHom.id])
      (by simp [CartesianTripleHom.comp, CartesianTripleHom.inv, CartesianTripleHom.id])
  refine ⟨triplePushoutMap m.inv, ?_, ?_⟩
  · rw [← triplePushoutMap_comp, hmn, triplePushoutMap_id]
  · rw [← triplePushoutMap_comp, hnm, triplePushoutMap_id]

/-- Two pullbacks of one cospan with a compatible comparison morphism between them are
isomorphic through it. -/
private theorem isIso_of_isPullback_of_isPullback {P P' X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {fst' : P' ⟶ X} {snd' : P' ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) (m : P ⟶ P')
    (hm₁ : m ≫ fst' = fst) (hm₂ : m ≫ snd' = snd) : IsIso m := by
  refine ⟨h.lift fst' snd' h'.w, ?_, ?_⟩
  · refine h.hom_ext ?_ ?_
    · rw [Category.assoc, h.lift_fst, hm₁, Category.id_comp]
    · rw [Category.assoc, h.lift_snd, hm₂, Category.id_comp]
  · refine h'.hom_ext ?_ ?_
    · rw [Category.assoc, hm₁, h.lift_fst, Category.id_comp]
    · rw [Category.assoc, hm₂, h.lift_snd, Category.id_comp]

/-- **The pushout of [Stacks Project, Tag 0E25] is cartesian over a flat, separated, locally
quasi-finite base change of the base.**  If the two verticals of a cartesian diagram `d` over a
situation `s` exhibit its two outer corners as the base changes of those of `s` along
`a : T ⟶ s.S`, and `π` is a morphism from the induced pushout to `T` restricting to them, then
the square relating the two pushouts to `T` and to `s.S` is cartesian.

The hypotheses `hinl` and `hinr` pin `π` down: a morphism out of a pushout is determined by its
two restrictions. -/
theorem isPullback_pushoutMap_of_isPullback
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    {T : Scheme.{u}} (a : T ⟶ s.S)
    [Flat a] [IsSeparated a] [LocallyOfFiniteType a] [LocallyQuasiFinite a]
    (d : CartesianDiagram s) (pXd : d.X' ⟶ T) (pYd : d.Y' ⟶ T)
    (hX : IsPullback d.f pXd s.pX a) (hY : IsPullback d.g pYd s.pY a)
    (π : pushoutScheme (inducedSituation s d) ⟶ T)
    (hinl : pushoutInl (inducedSituation s d) ≫ π = pXd)
    (hinr : pushoutInr (inducedSituation s d) ≫ π = pYd) :
    IsPullback (pushoutMap s d) π (pushoutToBase s) a := by
  have hbaseInl : pushoutInl s ≫ pushoutToBase s = s.pX := by simp [pushoutToBase]
  have hbaseInr : pushoutInr s ≫ pushoutToBase s = s.pY := by simp [pushoutToBase]
  have : IsIso (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
      (pushoutSpanBaseChangeOver_props s a)) :=
    isIso_pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
      (pushoutSpanBaseChangeOver_props s a)
  -- the square commutes
  have hcomm : pushoutMap s d ≫ pushoutToBase s = π ≫ a := by
    refine (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.hom_ext
      ?_ ?_
    · rw [← Category.assoc, (pushoutMap_left_isPullback s d).w, Category.assoc, hbaseInl,
        ← Category.assoc, hinl, hX.w]
    · rw [← Category.assoc, (pushoutMap_right_isPullback s d).w, Category.assoc, hbaseInr,
        ← Category.assoc, hinr, hY.w]
  -- the comparison morphism to the base change of the pushout
  have hcfst : pullback.lift (pushoutMap s d) π hcomm ≫ pullback.fst (pushoutToBase s) a =
      pushoutMap s d := pullback.lift_fst _ _ _
  have hcsnd : pullback.lift (pushoutMap s d) π hcomm ≫ pullback.snd (pushoutToBase s) a =
      π := pullback.lift_snd _ _ _
  -- it comes from a morphism of cartesian diagrams
  have hk : (pullback.lift (pushoutMap s d) π hcomm ≫ CategoryTheory.inv
        (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
          (pushoutSpanBaseChangeOver_props s a))) ≫
        pushoutMap s (pushoutSpanBaseChangeDiagram s a) = pushoutMap s d := by
    rw [Category.assoc, ← pushoutBaseChangeMap_comp_hom s (pushoutSpanBaseChangeOver s a)
      (pushoutSpanBaseChangeOver_props s a), IsIso.inv_hom_id_assoc]
    exact hcfst
  obtain ⟨m, hm⟩ := exists_cartesianTripleHom_of_comp_pushoutMap d
    (pushoutSpanBaseChangeDiagram s a)
    (pullback.lift (pushoutMap s d) π hcomm ≫ CategoryTheory.inv
      (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
        (pushoutSpanBaseChangeOver_props s a))) hk
  -- the pushout of the canonical base-change diagram *is* the base change of the pushout
  have hbfst : pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
        (pushoutSpanBaseChangeOver_props s a) ≫ pullback.fst (pushoutToBase s) a =
      pushoutMap s (pushoutSpanBaseChangeDiagram s a) :=
    pushoutBaseChangeMap_comp_hom s (pushoutSpanBaseChangeOver s a)
      (pushoutSpanBaseChangeOver_props s a)
  have hbcMain : IsPullback (pushoutMap s (pushoutSpanBaseChangeDiagram s a))
      (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
          (pushoutSpanBaseChangeOver_props s a) ≫ pullback.snd (pushoutToBase s) a)
      (pushoutToBase s) a := by
    refine IsPullback.of_iso_pullback ⟨?_⟩
      (asIso (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
        (pushoutSpanBaseChangeOver_props s a))) hbfst rfl
    rw [← hbfst, Category.assoc, Category.assoc, pullback.condition]
  -- the two outer corners of the canonical base-change diagram are base changes
  have hbcX : IsPullback (pushoutSpanBaseChangeDiagram s a).f
      (pushoutInl (inducedSituation s (pushoutSpanBaseChangeDiagram s a)) ≫
        (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
          (pushoutSpanBaseChangeOver_props s a) ≫ pullback.snd (pushoutToBase s) a))
      s.pX a := by
    have h := IsPullback.paste_horiz
      (pushoutMap_left_isPullback s (pushoutSpanBaseChangeDiagram s a)) hbcMain.flip
    rw [hbaseInl] at h
    exact h.flip
  have hbcY : IsPullback (pushoutSpanBaseChangeDiagram s a).g
      (pushoutInr (inducedSituation s (pushoutSpanBaseChangeDiagram s a)) ≫
        (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
          (pushoutSpanBaseChangeOver_props s a) ≫ pullback.snd (pushoutToBase s) a))
      s.pY a := by
    have h := IsPullback.paste_horiz
      (pushoutMap_right_isPullback s (pushoutSpanBaseChangeDiagram s a)) hbcMain.flip
    rw [hbaseInr] at h
    exact h.flip
  -- the components of `m` over `X` and over `Y` are isomorphisms
  have : IsIso m.x := by
    refine isIso_of_isPullback_of_isPullback hX hbcX m.x m.overX ?_
    have hstep : m.x ≫ pushoutInl (inducedSituation s (pushoutSpanBaseChangeDiagram s a)) =
        pushoutInl (inducedSituation s d) ≫ (pullback.lift (pushoutMap s d) π hcomm ≫
          CategoryTheory.inv (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
            (pushoutSpanBaseChangeOver_props s a))) := by
      rw [← pushoutInl_comp_triplePushoutMap m, hm]
    rw [← Category.assoc, hstep]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hcsnd, hinl]
  have : IsIso m.y := by
    refine isIso_of_isPullback_of_isPullback hY hbcY m.y m.overY ?_
    have hstep : m.y ≫ pushoutInr (inducedSituation s (pushoutSpanBaseChangeDiagram s a)) =
        pushoutInr (inducedSituation s d) ≫ (pullback.lift (pushoutMap s d) π hcomm ≫
          CategoryTheory.inv (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
            (pushoutSpanBaseChangeOver_props s a))) := by
      rw [← pushoutInr_comp_triplePushoutMap m, hm]
    rw [← Category.assoc, hstep]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hcsnd, hinr]
  -- hence so is the component over `Z`
  have : IsIso m.z := by
    have hbcZ : IsPullback ((pushoutSpanBaseChangeDiagram s a).i' ≫ CategoryTheory.inv m.x)
        (pushoutSpanBaseChangeDiagram s a).h d.f s.i := by
      refine (pushoutSpanBaseChangeDiagram s a).left_isPullback.of_iso (Iso.refl _)
        (asIso m.x).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id]
        rw [← m.overX, IsIso.inv_hom_id_assoc]
      · simp
    refine isIso_of_isPullback_of_isPullback d.left_isPullback hbcZ m.z ?_ m.overZ
    rw [← Category.assoc, ← m.left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  -- so the comparison morphism is an isomorphism, and the square is cartesian
  have : IsIso (triplePushoutMap m) := isIso_triplePushoutMap m
  have : IsIso (pullback.lift (pushoutMap s d) π hcomm ≫ CategoryTheory.inv
      (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
        (pushoutSpanBaseChangeOver_props s a))) := hm ▸ inferInstance
  have : IsIso (pullback.lift (pushoutMap s d) π hcomm) := by
    have he : pullback.lift (pushoutMap s d) π hcomm =
        (pullback.lift (pushoutMap s d) π hcomm ≫ CategoryTheory.inv
          (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
            (pushoutSpanBaseChangeOver_props s a))) ≫
          pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
            (pushoutSpanBaseChangeOver_props s a) := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [he]
    infer_instance
  exact IsPullback.of_iso_pullback ⟨hcomm⟩ (asIso (pullback.lift (pushoutMap s d) π hcomm))
    hcfst hcsnd

end AlgebraicGeometry

end
