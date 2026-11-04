module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Irreducible
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.IdentityComponentGeometric
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Irreducible group schemes over a field are geometrically irreducible

An irreducible group scheme `G` over a field `k` is geometrically irreducible: its only
irreducible component contains the identity, so it is geometrically irreducible by Stacks 047M,
and passing from the reduced induced subscheme back to `G` does not change the underlying spaces
of the base changes.  By Stacks 0B7Q the same holds for connected group schemes.

## Main results

* `AlgebraicGeometry.GeometricallyIrreducible.of_comp_surjective`: geometric irreducibility
  descends along a surjective morphism of the source.
* `AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace`,
  `AlgebraicGeometry.geometricallyIrreducible_of_connectedSpace`: irreducible, respectively
  connected, group schemes over a field are geometrically irreducible.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **Geometric irreducibility descends along a surjection of the source**: if `i ≫ f` is
geometrically irreducible and `i` is surjective, so is `f`, every base change of `f` being the
image of the corresponding base change of `i ≫ f`. -/
@[ega "IV 4.5.4" "more general"]
theorem GeometricallyIrreducible.of_comp_surjective {X X' S : Scheme.{u}} (i : X' ⟶ X)
    (f : X ⟶ S) [Surjective i] [GeometricallyIrreducible (i ≫ f)] :
    GeometricallyIrreducible f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IrreducibleSpace (pullback (i ≫ f) y : Scheme.{u}) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := i ≫ f) y (pullback.fst _ _)
      (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  let u : (pullback (i ≫ f) y : Scheme.{u}) ⟶ Z :=
    h.lift (pullback.fst (i ≫ f) y ≫ i) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
  have hsq : IsPullback u (pullback.fst (i ≫ f) y) fst i := by
    refine IsPullback.of_right (h₁₂ := snd) (h₂₂ := f) (v₁₃ := y) ?_ (h.lift_fst _ _ _) h.flip
    rw [h.lift_snd]
    exact (IsPullback.of_hasPullback (i ≫ f) y).flip
  have : Surjective u := MorphismProperty.of_isPullback hsq.flip ‹Surjective i›
  exact Function.Surjective.irreducibleSpace u.continuous u.surjective

/-- **An irreducible group scheme over a field is geometrically irreducible.**  Its only
irreducible component, `G` itself, contains the identity, so its reduced induced subscheme is
geometrically irreducible (Stacks 047M), and that subscheme maps onto `G`. -/
@[ega "IV 15.6.10" "special case",
  sga "3 IX 5.5" "special case",
  sga "3 VIA 2.4" "(i), special case",
  sga "3 VIA 2.6.2" "special case",
  sga "3 VIA 2.6.5" "more general"]
theorem geometricallyIrreducible_of_irreducibleSpace {k : Type u} [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IrreducibleSpace G.left] :
    GeometricallyIrreducible G.hom := by
  have hG : G = Over.mk G.hom := by cases G; rfl
  let : GrpObj (Over.mk G.hom) := hG ▸ (inferInstance : GrpObj G)
  let Z : irreducibleComponents G.left :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, fun _ _ _ => Set.subset_univ _⟩
  have h := geometricallyIrreducible_irreducibleComponent_of_identity k G.left G.hom Z
    (Set.subset_univ _)
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : TopologicalSpace.Closeds G.left)
  have : Surjective I.subschemeι := ⟨fun x => by
    show x ∈ Set.range I.subschemeι
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact Set.mem_univ x⟩
  exact GeometricallyIrreducible.of_comp_surjective I.subschemeι G.hom

/-- **A connected group scheme over a field is geometrically irreducible** (Stacks 0B7Q and
047M). -/
@[sga "3 IX 5.5" "more general", sga "3 VIA 2.6.5" "more general"]
theorem geometricallyIrreducible_of_connectedSpace {k : Type u} [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [ConnectedSpace G.left] :
    GeometricallyIrreducible G.hom :=
  have := irreducibleSpace_of_connectedSpace G
  geometricallyIrreducible_of_irreducibleSpace G

end AlgebraicGeometry

end
