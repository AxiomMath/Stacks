module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.Trace

/-!
# Uniqueness of a Serre functor

Any two Serre equivalences on a `k`-linear category are related by a natural isomorphism of
their underlying self-functors which matches up their Serre pairings, and that natural
isomorphism is unique.

## Main results

* `CategoryTheory.serreEquivalence_uniqueUpToUniqueIso` gives the unique pairing-compatible
  natural isomorphism between the functors underlying two Serre equivalences.

## Implementation notes

The isomorphism is stated for the underlying self-functors rather than for the equivalences.
Compatibility with the pairings identifies the induced maps on every dual Hom space, so the
uniqueness assertion is relative to the Serre data and not uniqueness among arbitrary natural
isomorphisms. The comparison map is built from the trace functional of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.Trace`: compatibility with the
pairings is exactly compatibility with the traces, and the trace determines a morphism into a
Serre image.

## References

* [Stacks Project, Tag 0FY6](https://stacks.math.columbia.edu/tag/0FY6)
-/

@[expose] public section

namespace CategoryTheory

universe u v w

private noncomputable def comparisonPreimage {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S T : SerreEquivalence k (C := C)) (X : C) :
    (T.equivalence.inverse.obj (S.equivalence.functor.obj X) ⟶ X) := by
  let Z := T.equivalence.inverse.obj (S.equivalence.functor.obj X)
  let c := T.equivalence.counitIso.app (S.equivalence.functor.obj X)
  exact (T.pairing Z X).symm
    ((serreTrace k S X).comp (Linear.rightComp k X c.hom))

private lemma comparison_trace {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S T : SerreEquivalence k (C := C)) (X : C)
    (h : X ⟶ T.equivalence.functor.obj (T.equivalence.inverse.obj
      (S.equivalence.functor.obj X))) :
    serreTrace k T (T.equivalence.inverse.obj (S.equivalence.functor.obj X))
      (comparisonPreimage S T X ≫ h) =
    serreTrace k S X (h ≫ (T.equivalence.counitIso.app
      (S.equivalence.functor.obj X)).hom) := by
  let Z := T.equivalence.inverse.obj (S.equivalence.functor.obj X)
  let c := T.equivalence.counitIso.app (S.equivalence.functor.obj X)
  calc
    serreTrace k T Z (comparisonPreimage S T X ≫ h) =
        (T.pairing Z X (comparisonPreimage S T X)) h :=
          serreTrace_comp k T (comparisonPreimage S T X) h
    _ = serreTrace k S X (h ≫ c.hom) := by
      simp [comparisonPreimage, Linear.rightComp_apply, Z, c]

private noncomputable def comparisonComponent {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S T : SerreEquivalence k (C := C)) (X : C) :
    S.equivalence.functor.obj X ⟶ T.equivalence.functor.obj X := by
  let c := T.equivalence.counitIso.app (S.equivalence.functor.obj X)
  exact c.inv ≫ T.equivalence.functor.map (comparisonPreimage S T X)

private lemma comparison_trace_eq {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S T : SerreEquivalence k (C := C)) {X : C} (u : X ⟶ S.equivalence.functor.obj X) :
    serreTrace k S X u = serreTrace k T X (u ≫ comparisonComponent S T X) := by
  let Z := T.equivalence.inverse.obj (S.equivalence.functor.obj X)
  let c := T.equivalence.counitIso.app (S.equivalence.functor.obj X)
  calc
    serreTrace k S X u = serreTrace k T Z (comparisonPreimage S T X ≫ (u ≫ c.inv)) := by
      simpa [Category.assoc, c] using (comparison_trace S T X (u ≫ c.inv)).symm
    _ = serreTrace k T X ((u ≫ c.inv) ≫ T.equivalence.functor.map (comparisonPreimage S T X)) :=
      (serreTrace_cyclic k T (comparisonPreimage S T X) (u ≫ c.inv)).symm
    _ = serreTrace k T X (u ≫ comparisonComponent S T X) := by
      simp [comparisonComponent, Category.assoc, c]

private lemma comparisonComponent_natural {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S T : SerreEquivalence k (C := C)) {X Y : C} (f : X ⟶ Y) :
    S.equivalence.functor.map f ≫ comparisonComponent S T Y =
      comparisonComponent S T X ≫ T.equivalence.functor.map f := by
  apply serrePairing_hom_ext k T
  intro a
  rw [← serreTrace_comp, ← serreTrace_comp]
  calc
    serreTrace k T Y (a ≫ S.equivalence.functor.map f ≫ comparisonComponent S T Y) =
        serreTrace k S Y (a ≫ S.equivalence.functor.map f) :=
      by simpa using (comparison_trace_eq S T (a ≫ S.equivalence.functor.map f)).symm
    _ = serreTrace k S X (f ≫ a) := serreTrace_cyclic k S f a
    _ = serreTrace k T X (f ≫ a ≫ comparisonComponent S T X) := by
      simpa using comparison_trace_eq S T (f ≫ a)
    _ = _ := by simpa using (serreTrace_cyclic k T f (a ≫ comparisonComponent S T X)).symm

private lemma comparison_pairing {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S T : SerreEquivalence k (C := C))
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ S.equivalence.functor.obj X) :
    S.pairing X Y f g = T.pairing X Y f (g ≫ comparisonComponent S T X) := by
  rw [← serreTrace_comp, ← serreTrace_comp, comparison_trace_eq S T, Category.assoc]

private lemma dual_extensionality {k : Type u} [Field k] {V : Type*}
    [AddCommGroup V] [Module k V] [Module.Projective k V] {x y : V}
    (h : ∀ φ : Module.Dual k V, φ x = φ y) : x = y := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k (x - y)).mp
  intro φ
  simp [map_sub, h φ]

private lemma comparisonComponent_unique {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S T : SerreEquivalence k (C := C)) (X : C)
    (a : S.equivalence.functor.obj X ⟶ T.equivalence.functor.obj X)
    (ha : ∀ (Y : C) (f : X ⟶ Y) (g : Y ⟶ S.equivalence.functor.obj X),
      S.pairing X Y f g = T.pairing X Y f (g ≫ a)) :
    a = comparisonComponent S T X := by
  let : Module.Projective k (S.equivalence.functor.obj X ⟶ T.equivalence.functor.obj X) :=
    Module.Projective.of_free
  apply dual_extensionality (k := k)
  intro φ
  let f := (T.pairing X (S.equivalence.functor.obj X)).symm φ
  simpa [f] using (ha _ f (𝟙 _)).symm.trans (comparison_pairing S T f (𝟙 _))

private lemma comparisonComponent_self {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S : SerreEquivalence k (C := C)) (X : C) :
    comparisonComponent S S X = 𝟙 (S.equivalence.functor.obj X) :=
  (comparisonComponent_unique S S X (𝟙 _) fun _ _ _ => by simp).symm

private lemma comparisonComponent_inverse_left {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S T : SerreEquivalence k (C := C)) (X : C) :
    comparisonComponent S T X ≫ comparisonComponent T S X =
      𝟙 (S.equivalence.functor.obj X) :=
  (comparisonComponent_unique S S X _ fun _ f g => by
    simpa [Category.assoc] using
      (comparison_pairing S T f g).trans
        (comparison_pairing T S f (g ≫ comparisonComponent S T X))).trans
    (comparisonComponent_self S X)

private noncomputable def serreComparisonIso {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C]
    (S T : SerreEquivalence k (C := C)) :
    S.equivalence.functor ≅ T.equivalence.functor :=
  NatIso.ofComponents (fun X =>
    { hom := comparisonComponent S T X
      inv := comparisonComponent T S X
      hom_inv_id := comparisonComponent_inverse_left S T X
      inv_hom_id := comparisonComponent_inverse_left T S X })
    (fun f => comparisonComponent_natural S T f)

variable (k : Type u) [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- **Stacks Project, Tag 0FY6.** Two Serre functors have a unique natural isomorphism
preserving their Serre pairings. -/
@[stacks 0FY6 "serre_functor_unique"]
lemma serreEquivalence_uniqueUpToUniqueIso
    (S T : SerreEquivalence k (C := C)) :
    ∃! α : S.equivalence.functor ≅ T.equivalence.functor,
      ∀ (X Y : C) (f : X ⟶ Y) (g : Y ⟶ S.equivalence.functor.obj X),
        S.pairing X Y f g = T.pairing X Y f (g ≫ α.hom.app X) := by
  refine ⟨serreComparisonIso S T, fun X Y f g => comparison_pairing S T f g, ?_⟩
  intro α hα
  exact Iso.ext <| NatTrans.ext <| funext fun X =>
    comparisonComponent_unique S T X (α.hom.app X) (hα X)

end CategoryTheory
