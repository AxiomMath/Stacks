module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.SingleApproximationGeneral
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TruncatingApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles

/-!
# Pseudo-coherence under shifts and in the standard t-structure, on a ringed site

Elementary facts about `m`-pseudo-coherence of objects of `D(O)` on a ringed site, at
independent site, morphism and module universes.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isLE`: an object of `D^{≤ n}(O)` is
  `(n + 1)`-pseudo-coherent.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isZero`: a zero object of `D(O)` is
  `m`-pseudo-coherent for every `m`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_shift_iff`: the shift by `n` of an object
  of `D(O)` is `(m - n)`-pseudo-coherent exactly when the object is `m`-pseudo-coherent.

## Implementation notes

Everything is proved from the public interface. The first result represents the object by a
complex and applies
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_of_local_epi_homologyπ_general` with the
zero module as the local approximation, the cohomology sheaf in degree `n + 1` being zero. The
shift is an induction on `n` whose two steps are parts (1) and (3) of Stacks 08FV
(`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_one_general` and
`..._three_general`) applied to the rotated contractible triangle `A ⟶ 0 ⟶ A[1] ⟶ A[1]`, whose
middle vertex is pseudo-coherent in every degree; the converse is the forward direction for the
shift by `-n`.

## References

* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
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

/-- **An object of `D^{≤ n}(O)` is `(n + 1)`-pseudo-coherent.** A complex representing it has no
cohomology above `n`, so on every object of the site the zero module, placed in degree `n + 1`,
approximates it:
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_of_local_epi_homologyπ_general` applies with
the maximal sieve. -/
theorem isPseudoCoherentFrom_of_isLE
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℤ)
    [E.IsLE n] :
    X.IsPseudoCoherentFrom E (n + 1) := by
  set K := DerivedCategory.Q.objPreimage E
  have hK : ∀ i, n < i → IsZero (K.homology i) := fun i hi =>
    (DerivedCategory.isZero_of_isLE E n i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors _ i).app K).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso (DerivedCategory.Q.objObjPreimageIso E))
  refine isPseudoCoherentFrom_of_iso X (n + 1)
    (isPseudoCoherentFrom_Q_of_local_epi_homologyπ_general X K (n + 1)
      (fun j hj => hK j (by omega))
      fun U => ⟨⊤, by simp, fun V f _ => ⟨0,
        IsDirectSummandOfFiniteFree.of_isZero_general _ (isZero_zero _), 0,
        IsZero.epi (X.isZero_homology_restrictComplex_general V K (n + 1)
          (hK (n + 1) (by omega))) _⟩⟩)
    (DerivedCategory.Q.objObjPreimageIso E).symm

/-- **A zero object of `D(O)` is `m`-pseudo-coherent for every `m`**, lying in `D^{≤ m - 1}(O)`. -/
theorem isPseudoCoherentFrom_of_isZero
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : IsZero E) (m : ℤ) :
    X.IsPseudoCoherentFrom E m := by
  have : E.IsLE (m - 1) := (DerivedCategory.isLE_iff E (m - 1)).2 fun i _ =>
    (DerivedCategory.homologyFunctor _ i).map_isZero hE
  have h := isPseudoCoherentFrom_of_isLE X E (m - 1)
  rwa [sub_add_cancel] at h

/-- The shift by `1` of an `(m + 1)`-pseudo-coherent object of `D(O)` is `m`-pseudo-coherent:
Stacks 08FV (1) on the rotated contractible triangle `E ⟶ 0 ⟶ E[1] ⟶ E[1]`. -/
theorem isPseudoCoherentFrom_shift_one (m : ℤ)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPseudoCoherentFrom E (m + 1)) :
    X.IsPseudoCoherentFrom (E⟦(1 : ℤ)⟧) m :=
  isPseudoCoherentFrom_of_distinguished_one_general X m (contractibleTriangle E).rotate
    (rot_of_distTriang _ (contractible_distinguished E)) hE
    (isPseudoCoherentFrom_of_isZero X _ (isZero_zero _) m)

/-- The shift by `-1` of an `m`-pseudo-coherent object of `D(O)` is `(m + 1)`-pseudo-coherent:
Stacks 08FV (3) on the rotated contractible triangle `E[-1] ⟶ 0 ⟶ E[-1][1] ⟶ E[-1][1]`, whose
third vertex is `E`. -/
theorem isPseudoCoherentFrom_shift_neg_one (m : ℤ)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPseudoCoherentFrom E m) :
    X.IsPseudoCoherentFrom (E⟦(-1 : ℤ)⟧) (m + 1) :=
  isPseudoCoherentFrom_of_distinguished_three_general X m
    (contractibleTriangle (E⟦(-1 : ℤ)⟧)).rotate
    (rot_of_distTriang _ (contractible_distinguished _))
    (isPseudoCoherentFrom_of_isZero X _ (isZero_zero _) (m + 1))
    (isPseudoCoherentFrom_of_iso X m hE
      ((shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by omega)).app E))

/-- **The shift by `n` of an object of `D(O)` is `(m - n)`-pseudo-coherent exactly when the object
is `m`-pseudo-coherent.** The forward direction is an induction on `n`, from the shifts by `1`
and by `-1`; the converse is the forward direction for the shift by `-n`, since
`E[n][-n] ≅ E`. -/
theorem isPseudoCoherentFrom_shift_iff (m n : ℤ)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    X.IsPseudoCoherentFrom (E⟦n⟧) (m - n) ↔ X.IsPseudoCoherentFrom E m := by
  have fwd : ∀ (m n : ℤ)
      (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      X.IsPseudoCoherentFrom E m → X.IsPseudoCoherentFrom (E⟦n⟧) (m - n) := by
    intro m n E hE
    induction n using Int.induction_on with
    | zero =>
      rw [sub_zero]
      exact isPseudoCoherentFrom_of_iso X m hE ((shiftFunctorZero _ ℤ).app E)
    | succ i ih =>
      have h := isPseudoCoherentFrom_shift_one X (m - (i + 1)) (E⟦(i : ℤ)⟧)
        (by rw [show m - ((i : ℤ) + 1) + 1 = m - i by ring]; exact ih)
      exact isPseudoCoherentFrom_of_iso X _ h ((shiftFunctorAdd' _ (i : ℤ) 1 (i + 1) rfl).app E)
    | pred i ih =>
      have h := isPseudoCoherentFrom_shift_neg_one X (m - (-i)) (E⟦(-i : ℤ)⟧) ih
      rw [show m - (-(i : ℤ) - 1) = m - (-i) + 1 by ring]
      exact isPseudoCoherentFrom_of_iso X _ h
        ((shiftFunctorAdd' _ (-(i : ℤ)) (-1) (-i - 1) (by ring)).app E)
  refine ⟨fun h => ?_, fwd m n E⟩
  have h' := fwd (m - n) (-n) (E⟦n⟧) h
  rw [show m - n - -n = m by ring] at h'
  exact isPseudoCoherentFrom_of_iso X m h' ((shiftFunctorCompIsoId _ n (-n) (by omega)).app E).symm

end AlgebraicGeometry.RingedSite

end
