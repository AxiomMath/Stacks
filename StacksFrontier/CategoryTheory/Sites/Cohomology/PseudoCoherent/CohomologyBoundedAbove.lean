module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.ShiftAndVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# Pseudo-coherence of a bounded above object of `D(O)` from its cohomology sheaves

Let `(C, O)` be a ringed site, let `m` be an integer and let `E` be an object of `D(O)` whose
cohomology vanishes in all degrees above some bound. If the cohomology sheaf `Hⁱ(E)`, placed in
degree zero, is `(m - i)`-pseudo-coherent for every `i ≥ m`, then `E` is `m`-pseudo-coherent.

This is the ringed-site form of the globally bounded above case of Stacks 09V8, which is
carried for a ringed *space* by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_homology_of_boundedAbove` of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/BoundedAboveCohomology.lean`. It is the
truncation induction that the converse half of Stacks 08IK runs on the small étale site of a
Noetherian algebraic space.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero_general`:
  an `O`-module which is `(m - j)`-pseudo-coherent in degree zero is `m`-pseudo-coherent when
  placed in degree `j`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isGE_of_isLE_general`: an object of
  `D(O)` concentrated in a single degree `a` is `m`-pseudo-coherent as soon as its cohomology
  there, placed in degree zero, is `(m - a)`-pseudo-coherent.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_homology_of_boundedAbove_general`: the
  induction itself.

## Implementation notes

The three steps are the ones of the ringed-space argument, and nothing in them is specific to a
space; what had to be supplied on a site is the two ingredients above, since the canonical
t-structure and its truncation triangles are generic for an abelian category with a derived
category.

Placing a module in degree `j` is shifting it by `-j` in `D(O)`, and shifting by `n` shifts the
pseudo-coherence bound by `n`
(`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_shift_iff`); that is the whole content of the
first step. An object concentrated in degree `a` is isomorphic to its cohomology there placed in
degree `a` (`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`), which is the second.

The induction is on the number `n` of degrees between `m` and the upper bound, with `m` fixed and
the bound descending. At each step the canonical triangle `τ^{<d}E ⟶ E ⟶ τ^{≥d}E` splits off the
top cohomology degree `d`: the third vertex is concentrated in degree `d`, where its cohomology is
that of `E` (`DerivedCategory.isIso_homologyFunctor_map_truncGEπ`), and the first vertex has one
degree less room above `m` and the same cohomology below `d`
(`DerivedCategory.isIso_homologyFunctor_map_truncLTι`), so the inductive hypothesis applies to
it. Stacks 08FV part (2),
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_two_general`, assembles the
two. When the bound equals `m` the first vertex has no cohomology at all in degrees at least `m`,
and `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isLE` finishes it.

No `stacks` attribute sits here: Stacks 09V8 is registered on the ringed-space statement
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_homology`, which carries the tag's own
hypothesis of a merely *local* bound, while the statement below asks for a global one.

## References

* [Stacks Project, Lemma 20.47.8 (Tag 09V8)](https://stacks.math.columbia.edu/tag/09V8)
* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **An `O`-module which is `(m - j)`-pseudo-coherent in degree zero is `m`-pseudo-coherent when
placed in degree `j`.** Placing it in degree `j` is shifting it by `-j`, and shifting by `-j`
shifts the pseudo-coherence bound by `j`
(`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_shift_iff`). -/
theorem isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero_general
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m j : ℤ)
    (h : X.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M) (m - j)) :
    X.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj M) m := by
  have e : (DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj M ≅
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M)⟦(-j : ℤ)⟧ :=
    ((DerivedCategory.singleFunctors
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso
      (-j) j 0 (by omega)).symm.app M
  have hshift : X.IsPseudoCoherentFrom
      (((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M)⟦(-j : ℤ)⟧)
      m := by
    simpa using (isPseudoCoherentFrom_shift_iff X (m - j) (-j) _).2 h
  exact isPseudoCoherentFrom_of_iso X m hshift e

/-- **An object of `D(O)` concentrated in a single degree is `m`-pseudo-coherent as soon as its
cohomology there is.** If `E` has no cohomology outside the degree `a` and `Hᵃ(E)`, placed in
degree zero, is `(m - a)`-pseudo-coherent, then `E` is `m`-pseudo-coherent.

Such an `E` is isomorphic to `Hᵃ(E)` placed in degree `a`
(`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`, with the module it produces
identified with `Hᵃ(E)` through `DerivedCategory.singleFunctorCompHomologyFunctorIso`), and
placing a module in degree `a` shifts the pseudo-coherence bound by `a`. -/
theorem isPseudoCoherentFrom_of_isGE_of_isLE_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a m : ℤ) [E.IsGE a] [E.IsLE a]
    (h : X.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).obj E)) (m - a)) :
    X.IsPseudoCoherentFrom E m := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE E a
  have q : (DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).obj E ≅ Y :=
    (DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).app Y
  exact isPseudoCoherentFrom_of_iso X m
    (isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero_general X _ m a h)
    (e ≪≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).mapIso q.symm)

/-- If `Hᵈ(E)` in degree zero is `(m - d)`-pseudo-coherent, then `τ^{≥d}E` is `m`-pseudo-coherent.
-/
private theorem isPseudoCoherentFrom_truncGE_of_homology
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (d m : ℤ) [E.IsLE d]
    (h : X.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) d).obj E)) (m - d)) :
    X.IsPseudoCoherentFrom ((DerivedCategory.TStructure.t.truncGE d).obj E) m := by
  have : ((DerivedCategory.TStructure.t.truncGE d).obj E).IsLE d := inferInstance
  have hiso : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) d).map
      ((DerivedCategory.TStructure.t.truncGEπ d).app E)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ d d le_rfl E
  exact isPseudoCoherentFrom_of_isGE_of_isLE_general X _ d m
    (isPseudoCoherentFrom_of_iso X (m - d) h
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).mapIso
        (asIso ((DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) d).map
          ((DerivedCategory.TStructure.t.truncGEπ d).app E))).symm))

/-- The induction behind
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_homology_of_boundedAbove_general`, on the
number `n` of degrees between `m` and the upper bound. -/
private theorem isPseudoCoherentFrom_of_homology_aux (m : ℤ) :
    ∀ (n : ℕ) (E : DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))), E.IsLE (m + n) →
      (∀ i : ℤ, m ≤ i → X.IsPseudoCoherentFrom
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          ((DerivedCategory.homologyFunctor
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj E))
        (m - i)) →
      X.IsPseudoCoherentFrom E m := by
  intro n
  induction n with
  | zero =>
    intro E hLE hcoh
    have : E.IsLE m := by simpa using hLE
    have h₁ : X.IsPseudoCoherentFrom ((DerivedCategory.TStructure.t.truncLT m).obj E) m := by
      have : ((DerivedCategory.TStructure.t.truncLT m).obj E).IsLE (m - 1) :=
        DerivedCategory.TStructure.t.isLE_truncLT_obj E m (m - 1) (by omega)
      have h :=
        isPseudoCoherentFrom_of_isLE X ((DerivedCategory.TStructure.t.truncLT m).obj E) (m - 1)
      rwa [sub_add_cancel] at h
    have h₃ := isPseudoCoherentFrom_truncGE_of_homology X E m m (hcoh m le_rfl)
    exact isPseudoCoherentFrom_of_distinguished_two_general X m _
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished m E) h₁ h₃
  | succ n ih =>
    intro E hLE hcoh
    have hEb : E.IsLE (m + (n : ℤ) + 1) :=
      DerivedCategory.TStructure.t.isLE_of_le E (m + ((n + 1 : ℕ) : ℤ)) _ (by push_cast; omega)
    have h₁ : X.IsPseudoCoherentFrom
        ((DerivedCategory.TStructure.t.truncLT (m + (n : ℤ) + 1)).obj E) m := by
      have hlt : ((DerivedCategory.TStructure.t.truncLT (m + (n : ℤ) + 1)).obj E).IsLE
          (m + (n : ℤ)) :=
        DerivedCategory.TStructure.t.isLE_truncLT_obj E (m + (n : ℤ) + 1) (m + (n : ℤ)) (by omega)
      refine ih _ hlt fun i hi => ?_
      by_cases hib : i < m + (n : ℤ) + 1
      · have hiso : IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map
            ((DerivedCategory.TStructure.t.truncLTι (m + (n : ℤ) + 1)).app E)) :=
          DerivedCategory.isIso_homologyFunctor_map_truncLTι (m + (n : ℤ) + 1) i hib E
        exact isPseudoCoherentFrom_of_iso X (m - i) (hcoh i hi)
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).mapIso
            (asIso ((DerivedCategory.homologyFunctor
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map
              ((DerivedCategory.TStructure.t.truncLTι (m + (n : ℤ) + 1)).app E))))
      · exact isPseudoCoherentFrom_of_isZero X _ (Functor.map_isZero _
          (DerivedCategory.isZero_of_isLE _ (m + (n : ℤ)) i (by omega))) (m - i)
    have h₃ := isPseudoCoherentFrom_truncGE_of_homology X E (m + (n : ℤ) + 1) m
      (hcoh (m + (n : ℤ) + 1) (by omega))
    exact isPseudoCoherentFrom_of_distinguished_two_general X m _
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished (m + (n : ℤ) + 1) E) h₁ h₃

/-- **A bounded above object of `D(O)` whose cohomology sheaves are pseudo-coherent in the
corresponding degrees is pseudo-coherent** — the globally bounded above case of Stacks 09V8 on a
ringed site. Let `E` be an object of `D(O)` whose cohomology vanishes in every degree above `b`
and suppose that `Hⁱ(E)`, placed in degree zero, is `(m - i)`-pseudo-coherent for every `i ≥ m`.
Then `E` is `m`-pseudo-coherent.

Only the cohomology in degrees at least `m` is constrained, the lower degrees being irrelevant to
`m`-pseudo-coherence; and the bound `b` is allowed to be smaller than `m`, the induction running
over the degrees between `m` and the larger of the two. -/
theorem isPseudoCoherentFrom_of_homology_of_boundedAbove_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (m b : ℤ)
    (hb : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj E))
    (hcoh : ∀ i : ℤ, m ≤ i → X.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj E)) (m - i)) :
    X.IsPseudoCoherentFrom E m := by
  have hcast : ((max b m - m).toNat : ℤ) = max b m - m := Int.toNat_of_nonneg (by omega)
  have hmax : E.IsLE (max b m) := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => hb i (lt_of_le_of_lt (le_max_left b m) hi)
  exact isPseudoCoherentFrom_of_homology_aux X m (max b m - m).toNat E
    (DerivedCategory.TStructure.t.isLE_of_le E (max b m) _ (by rw [hcast]; omega)) hcoh

end AlgebraicGeometry.RingedSite

end
