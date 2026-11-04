module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualNaturality

/-!
# Mates under transport of pairings, and under reflection along a fully faithful functor

`CategoryTheory.ExactPairing.mate` is computed here for the two ways a pairing is moved that the
passage from a complex-level dual to a dual in the derived category uses:

* transport along isomorphisms of **both** the object and its dual
  (`CategoryTheory.exactPairingCongr`), of which the library had only the one-sided
  `CategoryTheory.ExactPairing.mate_exactPairingCongrRight`;
* reflection along a fully faithful monoidal functor
  (`CategoryTheory.ExactPairing.ofFullyFaithful`), the inverse direction of
  `CategoryTheory.ExactPairing.map_mate`.

## Main results

* `CategoryTheory.ExactPairing.mate_eq_of_evaluation`: the mate depends on the two pairings only
  through their evaluations. This is the tool the rest of the file is written with: it reduces an
  identity of mates taken at different presentations of the same duals to an identity of
  evaluations, with the mate never unfolded.
* `CategoryTheory.ExactPairing.mate_exactPairingCongrLeft` and
  `CategoryTheory.ExactPairing.mate_exactPairingCongr`: the mate for pairings transported along
  isomorphisms of the object, and of the object and its dual together.
* `CategoryTheory.ExactPairing.map_mate_ofFullyFaithful`: **a fully faithful monoidal functor
  reflects the mate.** For `ι` fully faithful and monoidal and a pairing of `ι.obj A` with
  `ι.obj A'`, the mate for the reflected pairings of
  `CategoryTheory.ExactPairing.ofFullyFaithful` is carried by `ι` to the mate for the given
  pairings.

## Implementation notes

**Why only the evaluations.** `CategoryTheory.ExactPairing.mate` is pinned down by
`CategoryTheory.ExactPairing.eq_mate` from the identity `g ▷ X ≫ ε_X = Y' ◁ f ≫ ε_Y`, which
mentions the evaluations alone. So two pairings with equal evaluations have equal mates even
when their coevaluations are presented differently, and none of the proofs below has to compute a
coevaluation. For `CategoryTheory.ExactPairing.ofFullyFaithful`, whose evaluation is a
`CategoryTheory.Functor.preimage` and therefore opaque, this is what keeps the computation to a
single application of `CategoryTheory.Functor.map_preimage`.

**No tag.** Mathlib states the transports of a pairing and the mate identities; their
compatibility is not a numbered statement of the Stacks project either (§4.21.48 discusses mates
only through [Stacks, Tag 0FFV]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactPairing

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- **The mate depends on the pairings only through their evaluations.** Two pairings of the same
pair of objects with the same evaluation — presented differently, or transported from different
duals — have the same mates. -/
theorem mate_eq_of_evaluation {X Y X' Y' : C} (pX pX' : ExactPairing X X')
    (pY pY' : ExactPairing Y Y') (hX : pX.evaluation' = pX'.evaluation')
    (hY : pY.evaluation' = pY'.evaluation') (f : X ⟶ Y) :
    mate pX pY f = mate pX' pY' f :=
  eq_mate pX' pY' f _ (by rw [← hX, ← hY]; exact mate_comp_evaluation pX pY f)

/-- The mate for pairings transported along isomorphisms of the objects being dualised. The
morphism whose mate is taken is conjugated by the two isomorphisms. -/
theorem mate_exactPairingCongrLeft {X X₀ X' Y Y₀ Y' : C} (pX : ExactPairing X₀ X')
    (pY : ExactPairing Y₀ Y') (iX : X ≅ X₀) (iY : Y ≅ Y₀) (f : X ⟶ Y) :
    mate (@exactPairingCongrLeft C _ _ X X₀ X' pX iX)
        (@exactPairingCongrLeft C _ _ Y Y₀ Y' pY iY) f =
      mate pX pY (iX.inv ≫ f ≫ iY.hom) := by
  refine (eq_mate _ _ f _ ?_).symm
  show mate pX pY (iX.inv ≫ f ≫ iY.hom) ▷ X ≫ X' ◁ iX.hom ≫ pX.evaluation' =
    Y' ◁ f ≫ Y' ◁ iY.hom ≫ pY.evaluation'
  rw [← MonoidalCategory.whisker_exchange_assoc, mate_comp_evaluation,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

/-- **The mate for pairings transported along isomorphisms of both the object and its dual.**
The one-sided form is `CategoryTheory.ExactPairing.mate_exactPairingCongrRight`; this is the
two-sided form, which is what reads a mate at a pairing obtained from another by re-seating the
object and the dual at once. -/
theorem mate_exactPairingCongr {X X₀ X' X₀' Y Y₀ Y' Y₀' : C} (pX : ExactPairing X₀ X₀')
    (pY : ExactPairing Y₀ Y₀') (iX : X ≅ X₀) (iX' : X' ≅ X₀') (iY : Y ≅ Y₀) (iY' : Y' ≅ Y₀')
    (f : X ⟶ Y) :
    mate (@exactPairingCongr C _ _ X X₀ X' X₀' pX iX iX')
        (@exactPairingCongr C _ _ Y Y₀ Y' Y₀' pY iY iY') f =
      iY'.hom ≫ mate pX pY (iX.inv ≫ f ≫ iY.hom) ≫ iX'.inv := by
  rw [show mate (@exactPairingCongr C _ _ X X₀ X' X₀' pX iX iX')
        (@exactPairingCongr C _ _ Y Y₀ Y' Y₀' pY iY iY') f =
      mate (@exactPairingCongrLeft C _ _ X X₀ X'
          (@exactPairingCongrRight C _ _ X₀ X' X₀' pX iX') iX)
        (@exactPairingCongrLeft C _ _ Y Y₀ Y'
          (@exactPairingCongrRight C _ _ Y₀ Y' Y₀' pY iY') iY) f from rfl,
    mate_exactPairingCongrLeft, mate_exactPairingCongrRight]

section FullyFaithful

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The evaluation of the pairing obtained by pushing a reflected pairing forward again is the
evaluation it was reflected from: the structure maps of the monoidal functor cancel. -/
theorem evaluation_map_ofFullyFaithful (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful]
    (A A' : C) [pA : ExactPairing (F.obj A) (F.obj A')] :
    (@ExactPairing.map C D _ _ _ _ F _ A A'
        (ExactPairing.ofFullyFaithful F A A')).evaluation' = pA.evaluation' := by
  show μ F A' A ≫ F.map (ExactPairing.ofFullyFaithful F A A').evaluation' ≫ η F = _
  rw [show (ExactPairing.ofFullyFaithful F A A').evaluation' =
      F.preimage (δ F A' A ≫ pA.evaluation' ≫ ε F) from rfl, F.map_preimage]
  simp

/-- **A fully faithful monoidal functor reflects the mate.** If `ι` is fully faithful and
monoidal and `ι.obj A'`, `ι.obj B'` are duals of `ι.obj A`, `ι.obj B`, then the mate of
`g : A ⟶ B` for the reflected pairings of `CategoryTheory.ExactPairing.ofFullyFaithful` is
carried by `ι` to the mate of `ι.map g` for the given pairings. This is the converse direction of
`CategoryTheory.ExactPairing.map_mate`. -/
theorem map_mate_ofFullyFaithful (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful]
    (A A' B B' : C) [pA : ExactPairing (F.obj A) (F.obj A')]
    [pB : ExactPairing (F.obj B) (F.obj B')] (g : A ⟶ B) :
    F.map (mate (ExactPairing.ofFullyFaithful F A A')
        (ExactPairing.ofFullyFaithful F B B') g) = mate pA pB (F.map g) := by
  rw [map_mate F (ExactPairing.ofFullyFaithful F A A') (ExactPairing.ofFullyFaithful F B B') g]
  exact mate_eq_of_evaluation _ _ _ _ (evaluation_map_ofFullyFaithful F A A')
    (evaluation_map_ofFullyFaithful F B B') _

end FullyFaithful

end CategoryTheory.ExactPairing

end
