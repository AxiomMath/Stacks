module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
import StacksCore.Tactic.StacksAttribute

/-!
# A strictly perfect complex is bounded, and so is what it approximates

A strictly perfect complex has only finitely many nonzero terms (Stacks 08FL), so its cohomology
vanishes above some degree.  An `m`-pseudo-coherent complex is locally approximated by strictly
perfect complexes in a way that is an isomorphism on cohomology in every degree `> m`; hence over
each member of the witnessing covering its cohomology vanishes above a degree, and the degree can
be taken uniform over a **finite** subfamily.

This is the first half of the boundedness step of Stacks 08HE (2) ⇒ (1) — `m`-pseudo-coherence
together with finite coverings puts the object in `D⁻`, which is where the induction on `n - m`
starts.  What is supplied here is the per-member bound and the uniform bound over a finite
family; turning that into a bound for the cohomology sheaves themselves is a separate statement,
since it needs zero-detection for sheaves of modules along a covering.

## Main results

* `CochainComplex.exists_isZero_homologyFunctor_obj_of_finite`: a cochain complex with only
  finitely many nonzero terms — the boundedness clause of a strictly perfect complex — has
  vanishing cohomology above some degree.
* `RingedSite.exists_isZero_homology_restrictComplex_of_isPseudoCoherentComplexFrom`: over each
  member of the covering that witnesses `m`-pseudo-coherence at an object, the restricted complex
  has vanishing cohomology above some degree.
* `RingedSite.exists_bound_isZero_homology_restrictComplex_of_finite`: the same bound taken
  uniformly over a finite subfamily of the covering.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m d

/-- **A cochain complex has vanishing cohomology where it has a zero term.**  The homology at a
degree is a subquotient of the term in that degree. -/
public theorem HomologicalComplex.isZero_homologyFunctor_obj_of_isZero_X
    {A : Type u} [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ) (j : ℤ)
    (h : IsZero (K.X j)) :
    IsZero ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) j).obj K) :=
  (HomologicalComplex.exactAt_iff_isZero_homology K j).1
    (HomologicalComplex.ExactAt.of_isZero h)

/-- **A cochain complex with only finitely many nonzero terms has vanishing cohomology above
some degree.**  A finite set of integers is bounded above, and the cohomology vanishes wherever
the term does.

This is the boundedness clause of a strictly perfect complex, `IsStrictlyPerfect.bounded`
(clause (1) of Stacks 08FL), separated from it so that the statement needs none of the
sheafification instances that the direct-summand clause carries. -/
public theorem CochainComplex.exists_isZero_homologyFunctor_obj_of_finite
    {A : Type u} [Category.{v} A] [Abelian A] (E : CochainComplex A ℤ)
    (h : {i : ℤ | ¬ IsZero (E.X i)}.Finite) :
    ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) j).obj E) := by
  obtain ⟨b, hb⟩ := h.bddAbove
  refine ⟨b, fun j hj => HomologicalComplex.isZero_homologyFunctor_obj_of_isZero_X E j ?_⟩
  by_contra hz
  exact absurd (hb (Set.mem_ofPred.2 hz)) (not_le.2 hj)

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{m}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **An `m`-pseudo-coherent complex is bounded above on each member of its witnessing
covering.**  At an object `U` the definition (Stacks 08FT (1)) provides a covering presieve `S`
and, over each member, a strictly perfect complex `P` with a map `P ⟶ E|_V` that is an
isomorphism on cohomology in every degree `> m`.  The cohomology of `P` vanishes above a degree,
and transporting along those isomorphisms gives the same for `E|_V` above the larger of that
degree and `m`. -/
public theorem exists_isZero_homology_restrictComplex_of_isPseudoCoherentComplexFrom
    (E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (k : ℤ)
    (hE : X.IsPseudoCoherentComplexFrom E k) (U : X.C) :
    ∃ S : Presieve U, (Sieve.generate S ∈ X.J U) ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f → ∃ b : ℤ, ∀ j : ℤ, b < j →
        IsZero ((HomologicalComplex.homologyFunctor
          (SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
          (ComplexShape.up ℤ) j).obj (X.restrictComplex E V)) := by
  obtain ⟨S, hS, hmem⟩ := hE U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨P, hP, α, hiso, _⟩ := hmem f hf
  obtain ⟨b, hb⟩ := CochainComplex.exists_isZero_homologyFunctor_obj_of_finite P hP.bounded
  refine ⟨max b k, fun j hj => ?_⟩
  have hk : k < j := lt_of_le_of_lt (le_max_right b k) hj
  have := hiso j hk
  exact (hb j (lt_of_le_of_lt (le_max_left b k) hj)).of_iso
    (asIso (HomologicalComplex.homologyMap α j)).symm

omit [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **The bound is uniform over a finite subfamily.**  Given a bound on each member of a finite
family of arrows, a single bound works for all of them: the maximum over the family.

This is the shape the boundedness step of Stacks 08HE (2) ⇒ (1) consumes.  Finiteness is where
the finite-refinement input enters: on the small affine étale site the coverings are finite
(`AlgebraicGeometry.SmallEtale.smallAffineEtale_covering_finite_flat`), and
`Stacks.Sites.exists_finite_flat_refinement` refines an arbitrary covering to a finite one. -/
public theorem exists_bound_isZero_homology_restrictComplex_of_finite
    (E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {ι : Type*} [Finite ι]
    (V : ι → X.C)
    (hb : ∀ i : ι, ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((HomologicalComplex.homologyFunctor
        (SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i)))
        (ComplexShape.up ℤ) j).obj (X.restrictComplex E (V i)))) :
    ∃ b : ℤ, ∀ (i : ι) (j : ℤ), b < j →
      IsZero ((HomologicalComplex.homologyFunctor
        (SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i)))
        (ComplexShape.up ℤ) j).obj (X.restrictComplex E (V i))) := by
  choose c hc using hb
  obtain ⟨b, hbd⟩ := (Set.finite_range c).bddAbove
  exact ⟨b, fun i j hj => hc i j (lt_of_le_of_lt (hbd (Set.mem_range_self i)) hj)⟩

end AlgebraicGeometry.RingedSite

end
