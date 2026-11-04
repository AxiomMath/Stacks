module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Comparison

/-!
# The graded divided-power polynomial algebra on a family of variables, as a function of it

`exists_gradedDividedPowerPolynomial_of_indices` builds a graded divided-power polynomial
algebra on any prescribed family `idx : ℕ → Type _` of variable indices, but it does so as an
existential statement: the algebra, its grading, its divided powers and its universal property
come out as the components of a nine-fold `∃`. This file bundles those components into a
structure, `IndexedPresentation`, and chooses one for every family, so that the algebra on a
family is a *function* of the family.

That is what a construction by recursion on the degree needs. Such a recursion adjoins the
variables of degree `k + 1` after inspecting the algebra on the variables of degrees `≤ k`, so
the data at rung `k` would otherwise be a dependent pair — a family of index types together
with an algebra built from it and a boundary map into that algebra — and a dependent pair
cannot be produced by a recursion into a fixed type. With the algebra presented as a function
of the family, the data at rung `k` is just the family, and the recursion is an ordinary one.

## Main definitions

* `DividedPowers.TateResolution.IndexedPresentation` bundles a graded divided-power polynomial
  algebra over `P` whose index family is a prescribed `idx`, together with its universal
  property.
* `DividedPowers.TateResolution.IndexedPresentation.gen` is the variable at an index of the
  prescribed family, and `IndexedPresentation.comparison` is the comparison algebra map
  determined by a degree-wise map of prescribed families.
* `DividedPowers.TateResolution.chosenPresentation` is a choice of such a presentation for every
  family.

## Main results

* `DividedPowers.TateResolution.IndexedPresentation.existsUnique_hom` — the universal property,
  with the variables indexed by the prescribed family rather than by the structure's own field.
* `DividedPowers.TateResolution.IndexedPresentation.exists_comparison` — a degree-wise map of
  prescribed families induces an algebra map preserving coefficients, variables, the grading and
  the divided powers.
* `DividedPowers.TateResolution.IndexedPresentation.exists_comparison_retraction` — that algebra
  map is split by a graded algebra map when the map of families has a degree-wise retraction,
  and so is injective (`IndexedPresentation.comparison_injective`).
* `DividedPowers.TateResolution.IndexedPresentation.comparison_comp` and
  `IndexedPresentation.comparison_self` — the chosen comparisons form a directed system. This
  needs the uniqueness half of the universal property: the comparison is a *choice*, so nothing
  formal makes the comparison of a composite the composite of the comparisons.

## Implementation notes

The universal property is a field, and a structure field cannot be universe-polymorphic, so the
target algebra is taken in the same universe as the algebra itself. That is the universe every
consumer here needs: both algebras being compared are presentations of families in
`ℕ → Type (max u v w)`.

The structure's own index family is `polynomial.indices`, which the `indices_eq` field pins to
the prescribed `idx`. That equality is one of *type families*, so transporting an index along it
needs a `cast` and not a `▸`; `indexEquiv` packages the transport once, and `gen`,
`existsUnique_hom` and `exists_comparison` are stated through it so that no consumer sees a
cast.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

/-- A graded divided-power polynomial algebra over `P` on a prescribed family `idx` of variable
indices, bundled with its graded divided-power universal property.

Every field is one component of the conclusion of
`exists_gradedDividedPowerPolynomial_of_indices`; bundling them is what makes the algebra on a
family a function of the family, as a construction by recursion on the degree requires. -/
public structure IndexedPresentation (R : Type u) (P : Type v) [CommRing R] [CommRing P]
    [Algebra R P] (idx : ℕ → Type (max u v w)) where
  /-- The underlying type of the presenting algebra. -/
  A : Type (max u v w)
  /-- The ring structure on the presenting algebra. -/
  ring : Ring A
  /-- The presenting algebra is an `R`-algebra. -/
  algebra : letI : Ring A := ring; Algebra R A
  /-- The homogeneous pieces of the presenting algebra. -/
  grade : letI : Ring A := ring; letI : Algebra R A := algebra;
    ℕ → Submodule R A
  /-- The homogeneous pieces make the presenting algebra a graded algebra. -/
  graded : letI : Ring A := ring; letI : Algebra R A := algebra;
    GradedAlgebra grade
  /-- The grading is strictly graded-commutative. -/
  strict : letI : Ring A := ring; letI : Algebra R A := algebra;
    letI : GradedAlgebra grade := graded;
    IsStrictlyGradedComm grade
  /-- The divided powers on the positive even part. -/
  gamma : letI : Ring A := ring; letI : Algebra R A := algebra;
    letI : GradedAlgebra grade := graded;
    letI : IsStrictlyGradedComm grade := strict;
    DividedPowerStructure grade
  /-- The coefficient algebra, sitting in degree zero. -/
  coefficient : letI : Ring A := ring; letI : Algebra R A := algebra;
    P →ₐ[R] A
  /-- The presentation of the algebra by variables over its coefficient algebra. -/
  polynomial : letI : Ring A := ring; letI : Algebra R A := algebra;
    letI : GradedAlgebra grade := graded;
    letI : IsStrictlyGradedComm grade := strict;
    GradedDividedPowerPolynomial grade gamma coefficient
  /-- The variables are indexed by the prescribed family. -/
  indices_eq : polynomial.indices = idx
  /-- The graded divided-power universal property, with the target in the same universe. -/
  universal : letI : Ring A := ring; letI : Algebra R A := algebra;
    letI : GradedAlgebra grade := graded;
    letI : IsStrictlyGradedComm grade := strict;
    ∀ {D : Type (max u v w)} [Ring D] [Algebra R D]
      (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
      (ε : DividedPowerStructure Dᵢ) (f : P →ₐ[R] D)
      (t : (Σ n : ℕ, polynomial.indices n) → D),
      (∀ (m : ℕ) (p : P), p ∈ degreeZeroGrade R P m → f p ∈ Dᵢ m) →
      (∀ (n : ℕ) (p : P), p ∈ positiveEvenPart (degreeZeroGrade R P) →
        ε.dpow n (f p) = f ((degreeZeroDividedPowers R P).dpow n p)) →
      (∀ j : Σ n : ℕ, polynomial.indices n, t j ∈ Dᵢ (j.1 + 1)) →
      ∃! g : A →ₐ[R] D,
        (∀ p : P, g (coefficient p) = f p) ∧
        (∀ j : Σ n : ℕ, polynomial.indices n, g (polynomial.generator j) = t j) ∧
        (∀ (m : ℕ) (x : A), x ∈ grade m → g x ∈ Dᵢ m) ∧
        (∀ (n : ℕ) (x : A), x ∈ positiveEvenPart grade →
          ε.dpow n (g x) = g (gamma.dpow n x))

namespace IndexedPresentation

variable {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]
  {idx idx' idx'' : ℕ → Type (max u v w)}

/-- The ring structure on the presenting algebra of `T`, as an instance. -/
public instance instRing (T : IndexedPresentation.{u, v, w} R P idx) : Ring T.A := T.ring

/-- The `R`-algebra structure on the presenting algebra of `T`, as an instance. -/
public instance instAlgebra (T : IndexedPresentation.{u, v, w} R P idx) :
    Algebra R T.A := T.algebra

/-- The grading of the presenting algebra of `T`, as a `GradedAlgebra` instance. -/
public instance instGraded (T : IndexedPresentation.{u, v, w} R P idx) :
    GradedAlgebra T.grade := T.graded

/-- The grading of the presenting algebra of `T` is strictly graded-commutative, as an
instance. -/
public instance instStrict (T : IndexedPresentation.{u, v, w} R P idx) :
    IsStrictlyGradedComm T.grade := T.strict

/-- The transport of an index of the prescribed family to an index of the structure's own
family, as an equivalence. The two families are equal, but the equality is one of type
families, so the transport is a `cast` and this packages it once. -/
public def indexEquiv (T : IndexedPresentation.{u, v, w} R P idx) :
    (Σ n : ℕ, idx n) ≃ Σ n : ℕ, T.polynomial.indices n :=
  Equiv.sigmaCongrRight fun n => Equiv.cast (congrFun T.indices_eq n).symm

/-- Transporting an index of the prescribed family along `indexEquiv` keeps its degree. -/
public theorem indexEquiv_fst (T : IndexedPresentation.{u, v, w} R P idx)
    (j : Σ n : ℕ, idx n) : (T.indexEquiv j).1 = j.1 := rfl

/-- Transporting an index of the structure's own family back along `indexEquiv` keeps its
degree. -/
public theorem indexEquiv_symm_fst (T : IndexedPresentation.{u, v, w} R P idx)
    (j : Σ n : ℕ, T.polynomial.indices n) : (T.indexEquiv.symm j).1 = j.1 := rfl

/-- The variable of `T` at an index of the prescribed family. -/
public def gen (T : IndexedPresentation.{u, v, w} R P idx) (j : Σ n : ℕ, idx n) : T.A :=
  T.polynomial.generator (T.indexEquiv j)

/-- The variable of `T` at an index of degree `n` of the prescribed family is homogeneous of
degree `n + 1`. -/
public theorem gen_mem (T : IndexedPresentation.{u, v, w} R P idx) (j : Σ n : ℕ, idx n) :
    T.gen j ∈ T.grade (j.1 + 1) :=
  T.polynomial.generator_mem (T.indexEquiv j)

/-- The coefficients of `T` are homogeneous of degree zero. -/
public theorem coefficient_mem_grade_zero (T : IndexedPresentation.{u, v, w} R P idx) (p : P) :
    T.coefficient p ∈ T.grade 0 :=
  T.polynomial.coefficient_mem p

/-- The coefficient algebra map of `T` is injective. -/
public theorem coefficient_injective (T : IndexedPresentation.{u, v, w} R P idx) :
    Function.Injective T.coefficient :=
  T.polynomial.coefficient_injective

/-- The graded divided-power universal property of `T`, with the variables indexed by the
prescribed family: an algebra map out of `T.A` is determined by an algebra map of the
coefficients and a choice of boundary of the right degree for each prescribed variable. -/
public theorem existsUnique_hom (T : IndexedPresentation.{u, v, w} R P idx)
    {D : Type (max u v w)} [Ring D] [Algebra R D] (Dᵢ : ℕ → Submodule R D)
    [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ] (ε : DividedPowerStructure Dᵢ)
    (f : P →ₐ[R] D) (t : (Σ n : ℕ, idx n) → D)
    (hf : ∀ (m : ℕ) (p : P), p ∈ degreeZeroGrade R P m → f p ∈ Dᵢ m)
    (hε : ∀ (n : ℕ) (p : P), p ∈ positiveEvenPart (degreeZeroGrade R P) →
      ε.dpow n (f p) = f ((degreeZeroDividedPowers R P).dpow n p))
    (ht : ∀ j : Σ n : ℕ, idx n, t j ∈ Dᵢ (j.1 + 1)) :
    ∃! g : T.A →ₐ[R] D,
      (∀ p : P, g (T.coefficient p) = f p) ∧
      (∀ j : Σ n : ℕ, idx n, g (T.gen j) = t j) ∧
      (∀ (m : ℕ) (x : T.A), x ∈ T.grade m → g x ∈ Dᵢ m) ∧
      (∀ (n : ℕ) (x : T.A), x ∈ positiveEvenPart T.grade →
        ε.dpow n (g x) = g (T.gamma.dpow n x)) := by
  have hre : ∀ g : T.A →ₐ[R] D,
      (∀ j : Σ n : ℕ, T.polynomial.indices n, g (T.polynomial.generator j) =
        t (T.indexEquiv.symm j)) ↔ ∀ j : Σ n : ℕ, idx n, g (T.gen j) = t j := by
    intro g
    refine ⟨fun hg j => ?_, fun hg j => ?_⟩
    · have h2 := hg (T.indexEquiv j)
      rw [Equiv.symm_apply_apply] at h2
      exact h2
    · have h2 : T.polynomial.generator j = T.gen (T.indexEquiv.symm j) :=
        (congrArg T.polynomial.generator (T.indexEquiv.apply_symm_apply j)).symm
      rw [h2]
      exact hg _
  obtain ⟨g, ⟨hg1, hg2, hg3, hg4⟩, hgu⟩ :=
    T.universal Dᵢ ε f (fun j => t (T.indexEquiv.symm j)) hf hε
      (fun j => by
        have h3 := ht (T.indexEquiv.symm j)
        rwa [T.indexEquiv_symm_fst j] at h3)
  refine ⟨g, ⟨hg1, (hre g).mp hg2, hg3, hg4⟩, fun g' hg' => hgu g' ?_⟩
  exact ⟨hg'.1, (hre g').mpr hg'.2.1, hg'.2.2.1, hg'.2.2.2⟩

/-- The universal property of `T` with target `T'` and its coefficient map, for any choice of
boundaries `t` of the right degree. -/
private theorem existsUnique_hom_to (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (t : (Σ n : ℕ, idx n) → T'.A)
    (ht : ∀ j : Σ n : ℕ, idx n, t j ∈ T'.grade (j.1 + 1)) :
    ∃! g : T.A →ₐ[R] T'.A,
      (∀ p : P, g (T.coefficient p) = T'.coefficient p) ∧
      (∀ j : Σ n : ℕ, idx n, g (T.gen j) = t j) ∧
      (∀ (m : ℕ) (x : T.A), x ∈ T.grade m → g x ∈ T'.grade m) ∧
      (∀ (n : ℕ) (x : T.A), x ∈ positiveEvenPart T.grade →
        T'.gamma.dpow n (g x) = g (T.gamma.dpow n x)) :=
  T.existsUnique_hom T'.grade T'.gamma T'.coefficient t
    (mem_grade_of_mem_degreeZeroGrade T'.grade T'.coefficient T'.coefficient_mem_grade_zero)
    (dpow_comp_of_degreeZero T'.grade T'.gamma T'.coefficient) ht

/-- An algebra endomorphism of `T.A` fixing the coefficients and the variables, graded and
compatible with the divided powers, is the identity. -/
private theorem eq_id_of_fixes (T : IndexedPresentation.{u, v, w} R P idx) (g : T.A →ₐ[R] T.A)
    (hc : ∀ p : P, g (T.coefficient p) = T.coefficient p)
    (hv : ∀ j : Σ n : ℕ, idx n, g (T.gen j) = T.gen j)
    (hm : ∀ (m : ℕ) (x : T.A), x ∈ T.grade m → g x ∈ T.grade m)
    (hd : ∀ (n : ℕ) (x : T.A), x ∈ positiveEvenPart T.grade →
      T.gamma.dpow n (g x) = g (T.gamma.dpow n x)) :
    g = AlgHom.id R T.A := by
  obtain ⟨_, -, hu⟩ := T.existsUnique_hom_to T T.gen T.gen_mem
  exact (hu g ⟨hc, hv, hm, hd⟩).trans
    (hu (AlgHom.id R T.A) ⟨fun _ => rfl, fun _ => rfl, fun _ _ hx => hx, fun _ _ _ => rfl⟩).symm

/-- **The comparison of two presentations over the same coefficient algebra**, determined by a
degree-wise map of their prescribed index families: it sends coefficients to coefficients and
the variable at `j` in degree `n + 1` to the variable at `e n j` in the same degree, and it is
graded and compatible with the divided powers.

With the target family the full one and the source family a truncation of it, this is the map
along which a boundary chosen in the algebra built so far is transported to the final
algebra. -/
public theorem exists_comparison (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n) :
    ∃ g : T.A →ₐ[R] T'.A,
      (∀ p : P, g (T.coefficient p) = T'.coefficient p) ∧
      (∀ j : Σ n : ℕ, idx n, g (T.gen j) = T'.gen ⟨j.1, e j.1 j.2⟩) ∧
      (∀ (m : ℕ) (x : T.A), x ∈ T.grade m → g x ∈ T'.grade m) ∧
      (∀ (n : ℕ) (x : T.A), x ∈ positiveEvenPart T.grade →
        T'.gamma.dpow n (g x) = g (T.gamma.dpow n x)) := by
  obtain ⟨g, hg, -⟩ :=
    T.existsUnique_hom_to T' (fun j => T'.gen ⟨j.1, e j.1 j.2⟩)
      (fun j => T'.gen_mem ⟨j.1, e j.1 j.2⟩)
  exact ⟨g, hg⟩

/-- A choice of the comparison map of `exists_comparison`, so that it too is a function of the
two families and the degree-wise map between them. -/
public noncomputable def comparison (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n) :
    T.A →ₐ[R] T'.A :=
  (T.exists_comparison T' e).choose

/-- The comparison map sends the coefficient of `p` to the coefficient of `p`. -/
public theorem comparison_coefficient (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n) (p : P) :
    T.comparison T' e (T.coefficient p) = T'.coefficient p :=
  (T.exists_comparison T' e).choose_spec.1 p

/-- The comparison map sends the variable at `j` to the variable at the image of `j` under the
degree-wise map of index families. -/
public theorem comparison_gen (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n)
    (j : Σ n : ℕ, idx n) :
    T.comparison T' e (T.gen j) = T'.gen ⟨j.1, e j.1 j.2⟩ :=
  (T.exists_comparison T' e).choose_spec.2.1 j

/-- The comparison map is graded: it carries the piece of degree `m` into the piece of degree
`m`. -/
public theorem comparison_mem_grade (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n)
    (m : ℕ) (x : T.A) (hx : x ∈ T.grade m) : T.comparison T' e x ∈ T'.grade m :=
  (T.exists_comparison T' e).choose_spec.2.2.1 m x hx

/-- The comparison map commutes with the divided powers on the positive even part. -/
public theorem comparison_dpow (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n)
    (n : ℕ) (x : T.A) (hx : x ∈ positiveEvenPart T.grade) :
    T'.gamma.dpow n (T.comparison T' e x) = T.comparison T' e (T.gamma.dpow n x) :=
  (T.exists_comparison T' e).choose_spec.2.2.2 n x hx

/-- A graded algebra map carries the positive even part into the positive even part: the
positive even part is the supremum of the pieces of positive even degree, and each of them is
carried into the piece of the same degree. -/
public theorem mem_positiveEvenPart_of_mem (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (g : T.A →ₐ[R] T'.A)
    (hg : ∀ (m : ℕ) (x : T.A), x ∈ T.grade m → g x ∈ T'.grade m) {x : T.A}
    (hx : x ∈ positiveEvenPart T.grade) : g x ∈ positiveEvenPart T'.grade := by
  have hmap : Submodule.map g.toLinearMap (positiveEvenPart T.grade) ≤
      positiveEvenPart T'.grade := by
    rw [Submodule.map_iSup]
    exact iSup_le fun d =>
      Submodule.map_le_iff_le_comap.mpr fun y hy => Submodule.mem_iSup_of_mem d (hg _ y hy)
  exact hmap ⟨x, hx, rfl⟩

/-- **The comparison is split by a graded algebra map as soon as the degree-wise map of index
families has a degree-wise retraction.** The retraction of families gives a map back on
algebras — the variables outside the image go to zero, which is legitimate because zero is
homogeneous of every degree — and the composite fixes the coefficients and every variable, so
the uniqueness half of the universal property identifies it with the identity.

This is what identifies the algebra on a truncated family of variables with a subalgebra of the
algebra on the full family, and so identifies their homology in low degrees. The retraction
being graded is what makes a preimage of a homogeneous element homogeneous. -/
public theorem exists_comparison_retraction (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n)
    (ρ : ∀ n : ℕ, idx' n → Option (idx n)) (hρ : ∀ (n : ℕ) (x : idx n), ρ n (e n x) = some x) :
    ∃ r : T'.A →ₐ[R] T.A,
      (∀ x : T.A, r (T.comparison T' e x) = x) ∧
      ∀ (m : ℕ) (x : T'.A), x ∈ T'.grade m → r x ∈ T.grade m := by
  obtain ⟨h, ⟨hh1, hh2, hh3, hh4⟩, -⟩ :=
    T'.existsUnique_hom_to T (fun j => (ρ j.1 j.2).elim 0 fun x => T.gen ⟨j.1, x⟩)
      (fun j => by
        rcases hopt : ρ j.1 j.2 with _ | x
        · simp
        · simpa [hopt] using T.gen_mem ⟨j.1, x⟩)
  have hcomp : h.comp (T.comparison T' e) = AlgHom.id R T.A := by
    refine T.eq_id_of_fixes _ (fun p => ?_) (fun j => ?_) (fun m x hx => ?_) (fun n x hx => ?_)
    · simp only [AlgHom.coe_comp, Function.comp_apply, T.comparison_coefficient, hh1]
    · simp only [AlgHom.coe_comp, Function.comp_apply, T.comparison_gen,
        hh2 ⟨j.1, e j.1 j.2⟩, hρ j.1 j.2, Option.elim]
    · exact hh3 m _ (T.comparison_mem_grade T' e m x hx)
    · simp only [AlgHom.coe_comp, Function.comp_apply]
      rw [hh4 n _ (T.mem_positiveEvenPart_of_mem T' (T.comparison T' e)
          (T.comparison_mem_grade T' e) hx), T.comparison_dpow T' e n x hx]
  refine ⟨h, fun x => ?_, hh3⟩
  have hx := congrArg (fun g : T.A →ₐ[R] T.A => g x) hcomp
  simpa using hx

/-- **The comparison is injective as soon as the degree-wise map of index families has a
degree-wise retraction**, since it is then split by `exists_comparison_retraction`. -/
public theorem comparison_injective (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n)
    (ρ : ∀ n : ℕ, idx' n → Option (idx n)) (hρ : ∀ (n : ℕ) (x : idx n), ρ n (e n x) = some x) :
    Function.Injective (T.comparison T' e) := by
  obtain ⟨r, hr, -⟩ := T.exists_comparison_retraction T' e ρ hρ
  intro a b hab
  rw [← hr a, ← hr b, hab]

/-- **The chosen comparison maps compose.** The comparison along a composite of degree-wise maps
of index families is the composite of the comparisons: both satisfy the four conditions
characterising a map out of the source, so the uniqueness half of the universal property
identifies them.

The comparison is a *choice* of the map produced by `exists_comparison`, so this is not formal:
without it the comparisons of a tower of index families need not form a directed system. -/
public theorem comparison_comp (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx')
    (T'' : IndexedPresentation.{u, v, w} R P idx'')
    (e : ∀ n : ℕ, idx n → idx' n) (e' : ∀ n : ℕ, idx' n → idx'' n) :
    (T'.comparison T'' e').comp (T.comparison T' e) =
      T.comparison T'' (fun n x => e' n (e n x)) := by
  obtain ⟨g, -, hu⟩ := T.existsUnique_hom_to T'' (fun j => T''.gen ⟨j.1, e' j.1 (e j.1 j.2)⟩)
    (fun j => T''.gen_mem ⟨j.1, e' j.1 (e j.1 j.2)⟩)
  refine (hu _ ⟨fun p => ?_, fun j => ?_, fun m x hx => ?_, fun n x hx => ?_⟩).trans
    (hu _ ⟨T.comparison_coefficient T'' _, T.comparison_gen T'' _,
      T.comparison_mem_grade T'' _, T.comparison_dpow T'' _⟩).symm
  · simp only [AlgHom.coe_comp, Function.comp_apply, T.comparison_coefficient T' e,
      T'.comparison_coefficient T'' e']
  · simp only [AlgHom.coe_comp, Function.comp_apply, T.comparison_gen T' e,
      T'.comparison_gen T'' e']
  · exact T'.comparison_mem_grade T'' e' m _ (T.comparison_mem_grade T' e m x hx)
  · simp only [AlgHom.coe_comp, Function.comp_apply]
    rw [T'.comparison_dpow T'' e' n _
        (T.mem_positiveEvenPart_of_mem T' (T.comparison T' e)
          (T.comparison_mem_grade T' e) hx),
      T.comparison_dpow T' e n x hx]

/-- The comparison of a presentation with itself along the identity of its index family is the
identity. -/
public theorem comparison_self (T : IndexedPresentation.{u, v, w} R P idx) :
    T.comparison T (fun _ x => x) = AlgHom.id R T.A := by
  exact T.eq_id_of_fixes _ (T.comparison_coefficient T _) (T.comparison_gen T _)
    (T.comparison_mem_grade T _) (T.comparison_dpow T _)

end IndexedPresentation

/-- Every prescribed family of variable indices carries a graded divided-power polynomial
algebra over `P`, bundled with its universal property. This is
`exists_gradedDividedPowerPolynomial_of_indices` with its nine-fold existential packaged. -/
public theorem nonempty_indexedPresentation {R : Type u} {P : Type v} [CommRing R] [CommRing P]
    [Algebra R P] (idx : ℕ → Type (max u v w)) :
    Nonempty (IndexedPresentation.{u, v, w} R P idx) := by
  obtain ⟨A, rA, aA, Aᵢ, gA, sA, γ, ι, h, hidx, huniv⟩ :=
    exists_gradedDividedPowerPolynomial_of_indices.{u, v, w, max u v w} (R := R) (P := P) idx
  exact ⟨⟨A, rA, aA, Aᵢ, gA, sA, γ, ι, h, hidx,
    fun Dᵢ _ _ ε f t hf hε ht => huniv Dᵢ ε f t hf hε ht⟩⟩

/-- **The graded divided-power polynomial algebra on a prescribed family of variables, as a
function of the family.** A construction by recursion on the degree inspects the algebra built
from the variables of low degree before choosing the variables of the next degree, so it needs
the algebra to depend on the family and on nothing else. -/
public noncomputable def chosenPresentation (R : Type u) (P : Type v) [CommRing R] [CommRing P]
    [Algebra R P] (idx : ℕ → Type (max u v w)) : IndexedPresentation.{u, v, w} R P idx :=
  (nonempty_indexedPresentation.{u, v, w} (R := R) (P := P) idx).some

end DividedPowers.TateResolution

end
