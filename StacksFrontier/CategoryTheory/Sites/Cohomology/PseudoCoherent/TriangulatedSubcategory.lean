module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.ShiftAndVanishing

/-!
# The pseudo-coherent objects of `D(O)` form a thick triangulated subcategory

Let `(C, O)` be a ringed site. The pseudo-coherent objects of `D(O)` (Stacks 08FT) are closed
under isomorphisms, contain zero, are stable under every shift, are closed under extensions
(Stacks 08FV) and are stable under retracts (Stacks 08FW). This packages them as a property of
the objects of `D(O)` carrying the corresponding instances, at independent universes of the
objects and the morphisms of the site and of the sections of the structure sheaf.

## Main definitions

* `AlgebraicGeometry.RingedSite.isPseudoCoherentObject`: pseudo-coherence as a property of the
  objects of `D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentObject_shift`: the shift of a pseudo-coherent
  object is pseudo-coherent.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentObject_isTriangulated`: the pseudo-coherent
  objects form a triangulated subcategory.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentObject_isStableUnderRetracts`: a retract of a
  pseudo-coherent object is pseudo-coherent.

## Implementation notes

Stability under retracts uses no idempotent completeness of `D(O)`: a split monomorphism
`i : A ⟶ B` sits in a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` whose third map vanishes, so
`B ≅ A ⊞ C`, and Stacks 08FW applies to that biproduct. Stacks 08FW is stated with a derived
category on every slice of the site, which is a hypothesis of that statement only; the standard
model is supplied for it inside the proof.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08FW](https://stacks.math.columbia.edu/tag/08FW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v w d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Pseudo-coherence** (Stacks 08FT) as a property of the objects of `D(O)`. -/
def isPseudoCoherentObject : ObjectProperty
    (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  fun E => X.IsPseudoCoherent E

/-- An object satisfies `AlgebraicGeometry.RingedSite.isPseudoCoherentObject` exactly when it is
pseudo-coherent. -/
theorem isPseudoCoherentObject_iff
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    X.isPseudoCoherentObject E ↔ X.IsPseudoCoherent E :=
  Iff.rfl

/-- Pseudo-coherence transports along isomorphisms of `D(O)`: the representing complex is
unchanged and its comparison isomorphism is composed with the given one. -/
instance isPseudoCoherentObject_isClosedUnderIsomorphisms :
    X.isPseudoCoherentObject.IsClosedUnderIsomorphisms where
  of_iso e h := by
    obtain ⟨K, hK, ⟨eK⟩⟩ := h
    exact ⟨K, hK, ⟨eK ≪≫ e⟩⟩

/-- **The shift of a pseudo-coherent object of `D(O)` is pseudo-coherent**: shifting by `n`
turns `(m + n)`-pseudo-coherence into `m`-pseudo-coherence, for every `m`. -/
theorem isPseudoCoherentObject_shift
    {E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : X.isPseudoCoherentObject E) (n : ℤ) : X.isPseudoCoherentObject (E⟦n⟧) := by
  refine (isPseudoCoherent_iff_forall_isPseudoCoherentFrom X _).2 fun m => ?_
  have h' := (isPseudoCoherentFrom_shift_iff X (m + n) n E).2
    ((isPseudoCoherent_iff_forall_isPseudoCoherentFrom X E).1 h (m + n))
  rwa [add_sub_cancel_right] at h'

/-- **The pseudo-coherent objects of `D(O)` form a triangulated subcategory**: they contain
zero, are stable under shifts, and are closed under extensions (Stacks 08FV). -/
instance isPseudoCoherentObject_isTriangulated :
    X.isPseudoCoherentObject.IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, isPseudoCoherent_of_isZero_general X _ (isZero_zero _)⟩
  isStableUnderShiftBy n := ⟨fun _ hE => isPseudoCoherentObject_shift X hE n⟩
  ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _
    ((isPseudoCoherent_of_distinguished_general X T hT).2.1 h₁ h₃)

/-- **A retract of a pseudo-coherent object of `D(O)` is pseudo-coherent.** The split
monomorphism `i : A ⟶ B` sits in a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` whose third map
vanishes, so `B ≅ A ⊞ C`, and a summand of a pseudo-coherent biproduct is pseudo-coherent
(Stacks 08FW). -/
instance isPseudoCoherentObject_isStableUnderRetracts :
    X.isPseudoCoherentObject.IsStableUnderRetracts where
  of_retract {A _} r h := by
    obtain ⟨C, g, k, hT⟩ := distinguished_cocone_triangle r.i
    have h₃ : (Triangle.mk r.i g k).mor₃ = 0 :=
      Triangle.mor₃_eq_zero_of_mono₁ _ hT (show Mono r.i from inferInstance)
    obtain ⟨e, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT h₃
    exact isPseudoCoherent_left_of_biprod_general X
      (hDer := fun _ => HasDerivedCategory.standard _) A C
      (X.isPseudoCoherentObject.prop_of_iso e h)

end AlgebraicGeometry.RingedSite

end
