module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.TotalComplexShift
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso

/-!
# Weibel's acyclic assembly lemma for an arbitrary lower bound in the second degree

`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map` proves that a columnwise
quasi-isomorphism of double complexes induces a quasi-isomorphism on total complexes, for
double complexes vanishing in negative second degrees and in first degrees `≪ 0`. This file
removes the normalisation of the second bound: the same conclusion holds for double complexes
vanishing in second degrees `< b` and first degrees `< a`, for arbitrary integers `a` and `b`.

## Main results

* `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_lowerBound`: the acyclic assembly
  lemma with both bounds arbitrary.

## Implementation notes

The reduction is a conjugation by the shift `[0, b]` of a double complex, which is Mathlib's
`HomologicalComplex₂.shiftFunctor₂`: its value at `(p, q)` is the value of the original at
`(p, q + b)`, so it vanishes in negative second degrees as soon as the original vanishes in
second degrees `< b`, and its columns are the shifts of the original columns, hence
quasi-isomorphisms along with them. The comparison of the two total complexes is Mathlib's
`HomologicalComplex₂.totalShift₂Iso`, whose naturality identifies the shift of the map on
total complexes with the map on total complexes of the shift, up to the two isomorphisms; a
shift of a map of cochain complexes is a quasi-isomorphism exactly when the map is.
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex ComplexShape

namespace StacksDraft.TotalComplexQuasiIso

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **Weibel's acyclic assembly lemma with an arbitrary lower bound in the second degree**: a
morphism of double complexes which is a quasi-isomorphism on each column induces a
quasi-isomorphism on total complexes, provided both double complexes vanish in second degrees
`< b` and in first degrees `< a`. -/
lemma quasiIso_total_map_of_lowerBound
    {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z') (a b : ℤ)
    (hq : ∀ p q, q < b → IsZero ((Z.X p).X q)) (hp : ∀ p, p < a → IsZero (Z.X p))
    (hq' : ∀ p q, q < b → IsZero ((Z'.X p).X q)) (hp' : ∀ p, p < a → IsZero (Z'.X p))
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)]
    (hf : ∀ p, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) := by
  have hshift : QuasiIso (HomologicalComplex₂.total.map
      ((HomologicalComplex₂.shiftFunctor₂ A b).map f) (up ℤ)) := by
    refine quasiIso_total_map _ a (fun p q hq0 => ?_) (fun p hpa => ?_)
      (fun p q hq0 => ?_) (fun p hpa => ?_) (fun p => ?_)
    · exact (hq p (q + b) (by lia)).of_iso (Z.shiftFunctor₂XXIso p q b (q + b) rfl)
    · exact Functor.map_isZero (shiftFunctor (CochainComplex A ℤ) b) (hp p hpa)
    · exact (hq' p (q + b) (by lia)).of_iso (Z'.shiftFunctor₂XXIso p q b (q + b) rfl)
    · exact Functor.map_isZero (shiftFunctor (CochainComplex A ℤ) b) (hp' p hpa)
    · exact (CochainComplex.quasiIso_shift_iff (f.f p) b).2 (hf p)
  rw [← CochainComplex.quasiIso_shift_iff _ b]
  have heq : (shiftFunctor (CochainComplex A ℤ) b).map
        (HomologicalComplex₂.total.map f (up ℤ)) =
      (Z.totalShift₂Iso b).inv ≫ HomologicalComplex₂.total.map
        ((HomologicalComplex₂.shiftFunctor₂ A b).map f) (up ℤ) ≫ (Z'.totalShift₂Iso b).hom := by
    rw [HomologicalComplex₂.totalShift₂Iso_hom_naturality f b, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [heq]
  infer_instance

end StacksDraft.TotalComplexQuasiIso

end
