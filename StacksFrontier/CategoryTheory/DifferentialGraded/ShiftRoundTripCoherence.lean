module

public import StacksFrontier.CategoryTheory.DifferentialGraded.TriangleIso

/-!
# The round-trip coherence of an isomorphism-valued axiom (B)

For an isomorphism-valued axiom (B), `DGCategory.ShiftAxiomBIso`, the round-trip coherence asks
that shifting the round trip `x[1][-1] ≅ x` by `1` gives the round trip `z[-1][1] ≅ z` at
`z = x[1]`. It holds for strict data, and under it the shift of the rotated arrow of an admissible
short exact sequence is its connecting arrow, up to a round trip.

## Main definitions

* `DGCategory.IsRigid`: an isomorphism of `Comp(A)` that is the identity read along an equality of
  objects.
* `DGCategory.ShiftAxiomBIso.RoundTripCoherent`: the round-trip coherence.

## Main results

* `DGCategory.IsRigid.unique`: two rigid isomorphisms with the same endpoints are equal.
* `DGCategory.ShiftAxiomB.roundTripCoherent`: a strict axiom (B) satisfies the coherence.
* `DGCategory.ShiftAxiomBIso.shift_shiftedConnecting`: under the coherence, the shift of the
  rotated arrow is the connecting arrow precomposed with the round trip `z[-1][1] ≅ z`.

## References

* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B);
  [Tag 09QJ](https://stacks.math.columbia.edu/tag/09QJ), axioms (A), (B) and (C).
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- An isomorphism of `Comp(A)` is rigid when it is the identity read along an equality of
objects. -/
structure IsRigid {x y : A.Obj} (e : (show A.Comp from x) ≅ (show A.Comp from y)) : Prop where
  obj_eq : x = y
  hom_eq : e.hom = (eqCompIso (A := A) obj_eq).hom

/-- The identity read along an equality of objects is rigid. -/
theorem isRigid_eqCompIso {x y : A.Obj} (h : x = y) : IsRigid (eqCompIso (A := A) h) := ⟨h, rfl⟩

/-- The inverse of a rigid isomorphism is rigid. -/
theorem IsRigid.ofSymm {x y : A.Obj} {e : (show A.Comp from x) ≅ (show A.Comp from y)}
    (he : IsRigid e) : IsRigid e.symm := by
  obtain ⟨h, hh⟩ := he
  subst h
  refine ⟨rfl, ?_⟩
  rw [Iso.ext hh]
  rfl

/-- A composite of rigid isomorphisms is rigid. -/
theorem IsRigid.ofTrans {x y z : A.Obj} {e : (show A.Comp from x) ≅ (show A.Comp from y)}
    {e' : (show A.Comp from y) ≅ (show A.Comp from z)}
    (he : IsRigid e) (he' : IsRigid e') : IsRigid (e ≪≫ e') := by
  obtain ⟨h, hh⟩ := he
  obtain ⟨h', hh'⟩ := he'
  subst h h'
  refine ⟨rfl, ?_⟩
  rw [Iso.ext hh, Iso.ext hh']
  exact Subtype.ext (A.id_comp _)

/-- A rigid isomorphism is determined by its endpoints. -/
theorem IsRigid.unique {x y : A.Obj} {e e' : (show A.Comp from x) ≅ (show A.Comp from y)}
    (he : IsRigid e) (he' : IsRigid e') : e.hom = e'.hom := by
  obtain ⟨h, hh⟩ := he
  obtain ⟨h', hh'⟩ := he'
  subst h
  rw [hh, hh']

/-- The shift of a rigid isomorphism is the identity read along the shifted equality. -/
theorem IsRigid.mapCocycle (F : DGCategory.DGFunctor A A) {x y : A.Obj}
    {e : (show A.Comp from x) ≅ (show A.Comp from y)} (he : IsRigid e) :
    ∃ h : F.obj x = F.obj y, F.mapCocycle e.hom = (eqCompIso (A := A) h).hom := by
  obtain ⟨h, hh⟩ := he
  refine ⟨congrArg F.obj h, ?_⟩
  subst h
  rw [hh]
  exact Subtype.ext (F.map_id x)

/-- The round trip `x[a][b] ≅ x` of a strict axiom (B), with `a + b = 0`, is rigid. -/
private theorem isRigid_roundTrip (S : ShiftAxiomB A) (a b : ℤ) (hab : a + b = 0) (x : A.Obj) :
    IsRigid ((S.toShiftAxiomBIso.addIso a b x).symm ≪≫ S.toShiftAxiomBIso.indexIso hab x ≪≫
      S.toShiftAxiomBIso.zeroIso x) :=
  IsRigid.ofTrans
    (IsRigid.ofSymm (isRigid_eqCompIso
      (show (S.shiftFunctor (a + b)).obj x =
          (S.shiftFunctor b).obj ((S.shiftFunctor a).obj x) from by
        rw [add_comm a b]; exact S.add_obj b a x)))
    (IsRigid.ofTrans
      (isRigid_eqCompIso (congrArg (fun j : ℤ => (S.shiftFunctor j).obj x) hab))
      (isRigid_eqCompIso (S.zero_obj x)))

/-- The round-trip coherence holds for a strict axiom (B). -/
private theorem roundTrip_strict (S : ShiftAxiomB A) (x : A.Obj) :
    (S.shiftFunctor 1).mapCocycle (S.toShiftAxiomBIso.unshiftIso x).hom =
      (S.toShiftAxiomBIso.reshiftIso ((S.shiftFunctor 1).obj x)).hom := by
  have hu : IsRigid (S.toShiftAxiomBIso.unshiftIso x) := isRigid_roundTrip S 1 (-1) (by omega) x
  have hr : IsRigid (S.toShiftAxiomBIso.reshiftIso ((S.shiftFunctor 1).obj x)) :=
    isRigid_roundTrip S (-1) 1 (by omega) _
  obtain ⟨h, hh⟩ := IsRigid.mapCocycle (S.shiftFunctor 1) hu
  rw [hh]
  exact IsRigid.unique (isRigid_eqCompIso h) hr

/-- The round-trip coherence of an isomorphism-valued axiom (B): for every object `x`, shifting
the round trip `x[1][-1] ≅ x` by `1` gives the round trip `z[-1][1] ≅ z` at `z = x[1]`. -/
def ShiftAxiomBIso.RoundTripCoherent (S : ShiftAxiomBIso A) : Prop :=
  ∀ x : A.Obj, (S.shiftFunctor 1).mapCocycle (S.unshiftIso x).hom =
    (S.reshiftIso ((S.shiftFunctor 1).obj x)).hom

/-- A strict axiom (B) satisfies the round-trip coherence. -/
theorem ShiftAxiomB.roundTripCoherent (S : ShiftAxiomB A) :
    S.toShiftAxiomBIso.RoundTripCoherent := roundTrip_strict S

/-- Under the round-trip coherence, the shift by `1` of the rotated arrow of `E` is its
connecting arrow precomposed with the round trip `z[-1][1] ≅ z`. -/
theorem ShiftAxiomBIso.shift_shiftedConnecting (S : ShiftAxiomBIso A)
    (hS : S.RoundTripCoherent) {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    (S.shiftFunctor 1).mapCocycle (S.shiftedConnecting E) =
      A.compCocycle (S.connectingCocycle E) (S.reshiftIso z).hom := by
  apply Subtype.ext
  change (S.shiftFunctor 1).map
      (A.comp (by omega : (0 : ℤ) + 0 = 0) (S.unshiftIso x).hom.1
        ((S.shiftFunctor (-1)).map (S.connectingCocycle E).1)) = _
  rw [(S.shiftFunctor 1).map_comp, show (S.shiftFunctor 1).map (S.unshiftIso x).hom.1 =
      (S.reshiftIso ((S.shiftFunctor 1).obj x)).hom.1 from congrArg Subtype.val (hS x)]
  exact S.reshiftIso_natural (S.connectingCocycle E).1

end DGCategory
