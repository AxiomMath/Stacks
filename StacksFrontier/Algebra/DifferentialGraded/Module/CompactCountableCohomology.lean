module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CountableCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents

/-!
# Countable cohomology of a derived colimit of compact objects

Let `(A, d)` be a differential graded algebra over a commutative ring `R` whose cohomology
`H^k(A)` is countable in every degree. This file proves the easy implication of
[Stacks, Tag 0CRM]: if an object `M` of `D(A, d)` is a derived colimit `hocolim Eₙ` of a system of
*compact* objects, then `H^i(M)` is countable in every degree.

Cohomology on `D(A, d)` is represented by the regular module, `H^i(X) = Hom(A, X[i])`, and the
regular module is a compact object, so cohomology commutes with countable direct sums. A compact
object is a direct summand of the image of a differential graded module with a finite cell
filtration (Tag 09R3), whose cohomology is countable; so the direct sum `⊕ Eₙ` has countable
cohomology, and the long exact cohomology sequence of the triangle defining the derived colimit
bounds `H^i(hocolim Eₙ)` between two cohomology modules of `⊕ Eₙ`.

## Main results

* `DifferentialGradedModule.countable_cohomology_of_isCompactObject`: a compact object of
  `D(A, d)` has countable cohomology.
* `DifferentialGradedModule.countable_cohomology_coproduct`: a countable direct sum of objects
  with countable cohomology has countable cohomology.
* `DifferentialGradedModule.countable_cohomology_of_isHomotopyColimit_of_isCompactObject`:
  **Stacks 0CRM**, the implication (1) ⇒ (2).
* `DifferentialGradedModule.exists_isHomotopyColimit_isCompactObject_of_hasFiniteCellFiltration`:
  the colimit of a system of modules with finite cell filtrations satisfies condition (1), which
  is the last step of the converse implication.
* `DifferentialGradedModule.cohomologyEquivHomRegularShift`: a degree-`i` cohomology class of `X`
  is a morphism `A[-i] ⟶ X`, out of a compact object.
* `DifferentialGradedModule.exists_isCompactObject_cohomologyFunctor_map_eq` and
  `DifferentialGradedModule.exists_isCompactObject_comp_eq_cohomologyFunctor_map_eq`: every
  cohomology class of `M` is reached from a compact object, and a compact object mapping to `M`
  can be enlarged, compatibly, so as to reach a prescribed class.
* `DifferentialGradedModule.exists_isCompactObject_comp_eq_cohomologyFunctor_map_eq_zero`: a
  cohomology class of a compact object which dies in `M` can be killed by attaching one cell,
  again compatibly.

The last three are the one-cell-at-a-time steps of the implication (2) ⇒ (1) of Tag 0CRM. That
implication, and the equivalence of the tag, are proved in
`StacksFrontier/Algebra/DifferentialGraded/Module/CompactCountableConverse.lean`, which assembles a
cell tower whose terms are compact; the assembly does not go through Tag 0CRK, so the
identification of the cohomology of a derived colimit with the colimit of the cohomologies is not
needed (Tag 0CRK would need `H^i` to commute with countable direct sums as a
*colimit-preserving functor*, whereas what is available here is the bijection on `Hom`-groups of
`DifferentialGradedModule.countable_cohomology_coproduct`). The tag on this file accordingly
covers only (1) ⇒ (2).

## Implementation notes

Compactness of an object is tested against families indexed by the universe `u` of the chapter's
differential graded interface, whereas a derived colimit is a colimit of a system indexed by `ℕ`;
so the direct sum of the groups `Hom(A, Eₙ[i])` is taken over `ULift.{u} ℕ`, whose coprojections
exhibit `∐ Eₙ` as a direct sum all the same
(`DifferentialGradedModule.isColimitCofanULift`).

For the same reason `IsCompactObject.{u}` is the universe-restricted reading of compactness: it
tests only families indexed in `Type u`, while the source quantifies over arbitrary index sets.
Source-compactness implies it, not conversely, so a hypothesis of compactness in this spelling is
weaker than the source's and a conclusion of compactness in this spelling is stronger. The
cell-attachment results below *conclude* compactness, in the universe-restricted spelling; the
objects they produce are built from `A` by shifts, binary direct sums and cones, so this is no
loss in practice, but it is a stronger conclusion than the source states and is recorded here
rather than left implicit.

Degree-`i` cohomology is a homological functor on `D(A, d)`
(`DifferentialGradedModule.cohomologyFunctor_isHomological`), which is what makes the long exact
sequence available; the relevant exactness is the one at the third vertex of the triangle,
`H^i(⊕ Eₙ) → H^i(M) → H^{i+1}(⊕ Eₙ)`. Both pretriangulated structures on `K(A, d)` are in scope
once the differential graded interface is imported; the derived colimit of Tag 0CRL and the
homological functor used here are read in the cone-triangle structure, which is therefore the one
given priority.

## References

* [Stacks Project, Tag 0CRM](https://stacks.math.columbia.edu/tag/0CRM); the characterisation of
  the compact objects is [Tag 09R3](https://stacks.math.columbia.edu/tag/09R3), the definition of
  a derived colimit is [Tag 090Z](https://stacks.math.columbia.edu/tag/090Z).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/- The derived colimit of Tag 0CRL and the homological functor `H^i` of this chapter are read in
the cone-triangle structure on `K(A, d)`, which is therefore the one given priority here. -/
attribute [local instance 10000] instPretriangulatedHomotopyCategory

variable (A : DifferentialGradedAlgebra.{u, u} R)

/-! ### Cohomology as morphisms out of the regular module -/

/-- The image of the regular module in `D(A, d)`, which represents cohomology and is a compact
object. -/
abbrev regularObject : derivedCategory.{u, u, u} A :=
  (toDerivedCategory A).obj (regularModule A)

/-- Degree-`n` cohomology of an object of `D(A, d)` is countable exactly when the group of
morphisms from the regular module into its `n`-th shift is. -/
theorem countable_cohomologyFunctor_iff (X : derivedCategory.{u, u, u} A) (n : ℤ) :
    Countable ((cohomologyFunctor A n).obj X) ↔ Countable (regularObject A ⟶ X⟦n⟧) :=
  (cohomologyLinearEquivHomRegular A n X).toEquiv.countable_iff

/-! ### Compact objects -/

/-- **A compact object of `D(A, d)` has countable cohomology**, as soon as the algebra does. By
Tag 09R3 it is a direct summand of the image of a differential graded module with a finite cell
filtration, whose cohomology is countable, and cohomology carries the splitting to a surjection. -/
theorem countable_cohomology_of_isCompactObject (hA : ∀ k : ℤ, Countable (A.Cohomology k))
    (E : derivedCategory.{u, u, u} A) (hE : IsCompactObject.{u} E) (n : ℤ) :
    Countable ((cohomologyFunctor A n).obj E) := by
  obtain ⟨P, hP, i, r, hir⟩ :=
    (isCompactObject_iff_exists_retract_hasFiniteCellFiltration A E).1 hE
  -- Retype the splitting in the spelling `D(A, d) = (quasiIsomorphisms A).Localization`.
  let i' : E ⟶ (toDerivedCategory A).obj P := i
  let r' : (toDerivedCategory A).obj P ⟶ E := r
  have hir' : i' ≫ r' = 𝟙 E := hir
  have hPc : Countable ((cohomologyFunctor A n).obj ((toDerivedCategory A).obj P)) := by
    have h0 : Countable ((gradedCohomologyFunctor A n).obj P) :=
      HasCountableCohomology.of_hasFiniteCellFiltration A hA hP n
    exact countable_of_iso ((cohomologyFunctorIso A n).app P).symm
  have hsplit : (cohomologyFunctor A n).map i' ≫ (cohomologyFunctor A n).map r' =
      𝟙 ((cohomologyFunctor A n).obj E) := by
    rw [← CategoryTheory.Functor.map_comp, hir', CategoryTheory.Functor.map_id]
  refine @Function.Surjective.countable _ _ hPc ((cohomologyFunctor A n).map r').hom ?_
  intro y
  refine ⟨((cohomologyFunctor A n).map i').hom y, ?_⟩
  simpa [ModuleCat.comp_apply] using ConcreteCategory.congr_hom hsplit y

/-! ### Countable direct sums -/

/-- The coprojections of `∐ Z` indexed by a universe lift of `ℕ` exhibit `∐ Z` as the direct sum
of the lifted family, which is the form in which compactness tests it. -/
def isColimitCofanULift (Z : ℕ → derivedCategory.{u, u, u} A) [HasCoproduct Z] :
    IsColimit (Cofan.mk (∐ Z) (fun k : ULift.{u} ℕ => Sigma.ι Z k.down)) :=
  Cofan.IsColimit.mk _ (fun t => Sigma.desc fun n => t.inj (ULift.up n))
    (fun t k => Sigma.ι_desc (fun n => t.inj (ULift.up n)) k.down)
    (fun t _ hm => Sigma.hom_ext _ _ fun n => (hm (ULift.up n)).trans
      (Sigma.ι_desc (fun n => t.inj (ULift.up n)) n).symm)

/-- **A countable direct sum of objects with countable cohomology has countable cohomology.**
Cohomology is represented by the regular module, which is a compact object, so a morphism from it
into a direct sum is a finite sum of morphisms into the summands. -/
theorem countable_cohomology_coproduct (E : ℕ → derivedCategory.{u, u, u} A) (n : ℤ)
    (h : ∀ j, Countable ((cohomologyFunctor A n).obj (E j))) :
    Countable ((cohomologyFunctor A n).obj (∐ E)) := by
  classical
  have hshift : PreservesColimitsOfShape (Discrete ℕ)
      (CategoryTheory.shiftFunctor (derivedCategory.{u, u, u} A) n) := inferInstance
  have hcop : HasCoproduct fun j => (E j)⟦n⟧ := inferInstance
  have ecop : (∐ fun j => (E j)⟦n⟧) ≅ (∐ E)⟦n⟧ :=
    asIso (sigmaComparison (CategoryTheory.shiftFunctor (derivedCategory.{u, u, u} A) n) E)
  have hsum : ∀ j, Countable (regularObject A ⟶ (E j)⟦n⟧) := fun j =>
    (countable_cohomologyFunctor_iff A (E j) n).1 (h j)
  have hds : Countable (DirectSum (ULift.{u} ℕ) fun k => (regularObject A ⟶ (E k.down)⟦n⟧)) :=
    DirectSum.countable
  have hreg : IsCompactObject.{u} (regularObject A) := isCompactObject_q_regularModule A
  have hbij := bijective_cofanMap (regularObject A) hreg
    (fun k : ULift.{u} ℕ => Sigma.ι (fun j => (E j)⟦n⟧) k.down)
    (isColimitCofanULift A (fun j => (E j)⟦n⟧))
  have h1 : Countable (regularObject A ⟶ ∐ fun j => (E j)⟦n⟧) :=
    @Function.Surjective.countable _ _ hds _ hbij.2
  have h2 : Countable (regularObject A ⟶ (∐ E)⟦n⟧) :=
    Function.Injective.countable (f := fun g => g ≫ ecop.inv)
      fun a b hab => by simpa using (cancel_mono ecop.inv).1 hab
  exact (countable_cohomologyFunctor_iff A (∐ E) n).2 h2

/-! ### The derived colimit -/

/-- **Stacks 0CRM, the implication (1) ⇒ (2).** *"Let `(A, d)` be a differential graded algebra
such that `H^i(A)` is countable for every `i`. Let `M` be an object of `D(A, d)`. If
`M = hocolim Eₙ` with each `Eₙ` compact, then `H^i(M)` is countable for every `i`."*

Cohomology commutes with the derived colimit in the weak sense that the long exact sequence of the
triangle `⊕ Eₙ → ⊕ Eₙ → M → (⊕ Eₙ)[1]` places `H^i(M)` between two cohomology modules of `⊕ Eₙ`,
and those are countable because each `Eₙ` is compact. -/
@[stacks 0CRM "(1) implies (2)"]
theorem countable_cohomology_of_isHomotopyColimit_of_isCompactObject
    (hA : ∀ k : ℤ, Countable (A.Cohomology k)) (M : derivedCategory.{u, u, u} A)
    (F : ℕ ⥤ derivedCategory.{u, u, u} A) (hF : ∀ j, IsCompactObject.{u} (F.obj j))
    (hM : IsHomotopyColimit F M) (i : ℤ) :
    Countable ((cohomologyFunctor A i).obj M) := by
  obtain ⟨p, q, hT⟩ := hM
  set H := degreeZeroCohomologyOnLocalization.{u, u, u} A with hH
  let _ : H.ShiftSequence ℤ := Functor.ShiftSequence.tautological H ℤ
  have hcop : ∀ m : ℤ, Countable ((cohomologyFunctor A m).obj (∐ F.obj)) := fun m =>
    countable_cohomology_coproduct A F.obj m
      fun j => countable_cohomology_of_isCompactObject A hA (F.obj j) (hF j) m
  have hexact := H.homologySequence_exact₃ _ hT i (i + 1) rfl
  have h₁ : Countable (ShortComplex.mk _ _ (H.comp_homologySequenceδ _ hT i (i + 1) rfl)).X₁ :=
    hcop i
  have h₃ : Countable (ShortComplex.mk _ _ (H.comp_homologySequenceδ _ hT i (i + 1) rfl)).X₃ :=
    hcop (i + 1)
  exact ShortComplex.countable_X₂ _ hexact

/-! ### A countable increasing union of modules with finite cell filtrations -/

/-- **The last step of the converse implication of Tag 0CRM.** If a system `P₀ → P₁ → ⋯` of
differential graded modules has every `Pₙ` carrying a finite cell filtration, then its colimit is,
in `D(A, d)`, a derived colimit of compact objects — that is, it satisfies condition (1) of
Tag 0CRM. The system of images is compact by Tag 09R3, taken along the identity splitting, and the
derived colimit is represented by the colimit of differential graded modules by Tag 0CRL. -/
theorem exists_isHomotopyColimit_isCompactObject_of_hasFiniteCellFiltration
    (F : ℕ ⥤ DifferentialGradedModule.{u, u, u} A)
    (hF : ∀ n, HasFiniteCellFiltration (F.obj n)) :
    ∃ G : ℕ ⥤ derivedCategory.{u, u, u} A, (∀ n, IsCompactObject.{u} (G.obj n)) ∧
      IsHomotopyColimit G ((toDerivedCategory A).obj (Limits.colimit F)) := by
  refine ⟨F ⋙ toDerivedCategory A, fun n => ?_,
    isHomotopyColimit_toDerivedCategory_obj_colimit A F⟩
  refine (isCompactObject_iff_exists_retract_hasFiniteCellFiltration A
    ((F ⋙ toDerivedCategory A).obj n)).2 ⟨F.obj n, hF n, 𝟙 _, 𝟙 _, Category.comp_id _⟩

/-! ### Cohomology classes as morphisms out of a shift of the regular module -/

/-- The shift adjunction `(-)[-i] ⊣ (-)[i]` of `D(A, d)`, the two halves of the shift
autoequivalence. -/
def shiftNegAdjunction (i : ℤ) :
    CategoryTheory.shiftFunctor (derivedCategory.{u, u, u} A) (-i) ⊣
      CategoryTheory.shiftFunctor (derivedCategory.{u, u, u} A) i :=
  (shiftEquiv' (derivedCategory.{u, u, u} A) (-i) i (neg_add_cancel i)).toAdjunction

/-- **A degree-`i` cohomology class of `X` is a morphism `A[-i] ⟶ X` of `D(A, d)`.** The regular
module represents cohomology, `H^i(X) = Hom(A, X[i])`
(`DifferentialGradedModule.cohomologyLinearEquivHomRegular`), and the shift adjunction
`(-)[-i] ⊣ (-)[i]` reads a morphism `A ⟶ X[i]` as a morphism out of `A[-i]`.

Since `A` is a compact object of `D(A, d)`, so is `A[-i]`; this is the form in which a cohomology
class is attached to a compact object. -/
def cohomologyEquivHomRegularShift (i : ℤ) (X : derivedCategory.{u, u, u} A) :
    ↥((cohomologyFunctor A i).obj X) ≃ ((regularObject A)⟦-i⟧ ⟶ X) :=
  (cohomologyLinearEquivHomRegular A i X).toEquiv.trans
    ((shiftNegAdjunction A i).homEquiv (regularObject A) X).symm

/-- The morphism naming a cohomology class is the morphism `A ⟶ X[i]` of the representability
isomorphism, read across the shift adjunction. This pins
`DifferentialGradedModule.cohomologyEquivHomRegularShift` down. -/
theorem homEquiv_cohomologyEquivHomRegularShift (i : ℤ) (X : derivedCategory.{u, u, u} A)
    (x : (cohomologyFunctor A i).obj X) :
    (shiftNegAdjunction A i).homEquiv (regularObject A) X
        (cohomologyEquivHomRegularShift A i X x) =
      cohomologyLinearEquivHomRegular A i X x :=
  ((shiftNegAdjunction A i).homEquiv (regularObject A) X).apply_symm_apply _

/-- **Pushing a cohomology class forward composes the morphism naming it.** The morphism
`A[-i] ⟶ Y` naming `H^i(v) x` is the morphism naming `x` followed by `v`. -/
theorem cohomologyEquivHomRegularShift_naturality (i : ℤ)
    {X Y : derivedCategory.{u, u, u} A} (v : X ⟶ Y) (x : (cohomologyFunctor A i).obj X) :
    cohomologyEquivHomRegularShift A i Y ((cohomologyFunctor A i).map v x) =
      cohomologyEquivHomRegularShift A i X x ≫ v := by
  refine ((shiftNegAdjunction A i).homEquiv (regularObject A) Y).injective ?_
  refine (homEquiv_cohomologyEquivHomRegularShift A i Y _).trans ?_
  refine (cohomologyLinearEquivHomRegular_naturality A i v x).trans ?_
  refine Eq.trans
    (congrArg (· ≫ v⟦i⟧') (homEquiv_cohomologyEquivHomRegularShift A i X x).symm) ?_
  exact ((shiftNegAdjunction A i).homEquiv_naturality_right
    (cohomologyEquivHomRegularShift A i X x) v).symm

/-- The zero cohomology class is named by the zero morphism. -/
theorem cohomologyEquivHomRegularShift_zero (i : ℤ) (X : derivedCategory.{u, u, u} A) :
    cohomologyEquivHomRegularShift A i X 0 = 0 := by
  have hz : (shiftNegAdjunction A i).homEquiv (regularObject A) X 0 = 0 := by
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  refine ((shiftNegAdjunction A i).homEquiv (regularObject A) X).injective ?_
  exact ((homEquiv_cohomologyEquivHomRegularShift A i X 0).trans
    (map_zero (cohomologyLinearEquivHomRegular A i X))).trans hz.symm

/-! ### Attaching a cell to a compact approximation -/

/-- Every shift of the regular module is a compact object of `D(A, d)`. -/
private theorem isCompactObject_shift_regularObject (i : ℤ) :
    IsCompactObject.{u} ((regularObject A)⟦i⟧) :=
  have hP : IsCompactObject.{u} (regularObject A) := isCompactObject_q_regularModule A
  isCompactObject_shift hP i

/-- **A degree-`i` cohomology class comes from a compact object.** For every class `x ∈ H^i(M)`
there is a compact object `E` of `D(A, d)` and a morphism `u : E ⟶ M` carrying a class of `E`
onto `x`.

The object is `A[-i]`, a shift of the regular module, and the morphism is the one naming `x`
(`DifferentialGradedModule.cohomologyEquivHomRegularShift`): the class it carries onto `x` is the
one named by the identity of `A[-i]`. -/
theorem exists_isCompactObject_cohomologyFunctor_map_eq (M : derivedCategory.{u, u, u} A)
    (i : ℤ) (x : (cohomologyFunctor A i).obj M) :
    ∃ (E : derivedCategory.{u, u, u} A) (u : E ⟶ M) (y : (cohomologyFunctor A i).obj E),
      IsCompactObject.{u} E ∧ (cohomologyFunctor A i).map u y = x := by
  refine ⟨(regularObject A)⟦-i⟧, cohomologyEquivHomRegularShift A i M x,
    (cohomologyEquivHomRegularShift A i ((regularObject A)⟦-i⟧)).symm (𝟙 _),
    isCompactObject_shift_regularObject A (-i), ?_⟩
  refine (cohomologyEquivHomRegularShift A i M).injective ?_
  rw [cohomologyEquivHomRegularShift_naturality, Equiv.apply_symm_apply, Category.id_comp]

/-- **A compact approximation of `M` can be enlarged to reach a given cohomology class.** Let `E`
be a compact object of `D(A, d)` and `u : E ⟶ M` a morphism. For every class `x ∈ H^i(M)` there is
a morphism `f : E ⟶ E'` into a compact object through which `u` factors, and a class of `E'`
carried onto `x`.

The object is `E' = E ⊕ A[-i]`, with the morphism naming `x` on the second summand; the class is
the one named by the second coprojection. -/
theorem exists_isCompactObject_comp_eq_cohomologyFunctor_map_eq
    {M E : derivedCategory.{u, u, u} A} (hE : IsCompactObject.{u} E) (u : E ⟶ M) (i : ℤ)
    (x : (cohomologyFunctor A i).obj M) :
    ∃ (E' : derivedCategory.{u, u, u} A) (f : E ⟶ E') (u' : E' ⟶ M)
      (y : (cohomologyFunctor A i).obj E'),
      IsCompactObject.{u} E' ∧ f ≫ u' = u ∧ (cohomologyFunctor A i).map u' y = x := by
  refine ⟨E ⊞ (regularObject A)⟦-i⟧, biprod.inl,
    biprod.desc u (cohomologyEquivHomRegularShift A i M x),
    (cohomologyEquivHomRegularShift A i (E ⊞ (regularObject A)⟦-i⟧)).symm biprod.inr,
    isCompactObject_biprod hE (isCompactObject_shift_regularObject A (-i)), biprod.inl_desc _ _, ?_⟩
  refine (cohomologyEquivHomRegularShift A i M).injective ?_
  rw [cohomologyEquivHomRegularShift_naturality, Equiv.apply_symm_apply, biprod.inr_desc]

/-- **A cohomology class dying in `M` can be killed by attaching a cell.** Let `E` be a compact
object of `D(A, d)` and `u : E ⟶ M` a morphism. A class `y ∈ H^i(E)` killed by `H^i(u)` is killed
already by a morphism `f : E ⟶ E'` into a compact object through which `u` factors.

The class `y` is named by a morphism `c : A[-i] ⟶ E` whose composite with `u` vanishes, and `E'`
is the cone on `c`. It is compact because `A[-i]` and `E` are (Tag 07LS for the third vertex of a
distinguished triangle), the morphism `u` factors through it because `c ≫ u = 0`, and `y` dies in
it because `c` followed by the second morphism of a distinguished triangle vanishes.

Together with `DifferentialGradedModule.exists_isCompactObject_cohomologyFunctor_map_eq` this is
the inductive step of the construction of a system of compact objects approximating `M`, which is
the content of the implication (2) ⇒ (1) of Tag 0CRM. -/
theorem exists_isCompactObject_comp_eq_cohomologyFunctor_map_eq_zero
    {M E : derivedCategory.{u, u, u} A} (hE : IsCompactObject.{u} E) (u : E ⟶ M) (i : ℤ)
    (y : (cohomologyFunctor A i).obj E) (hy : (cohomologyFunctor A i).map u y = 0) :
    ∃ (E' : derivedCategory.{u, u, u} A) (f : E ⟶ E') (u' : E' ⟶ M),
      IsCompactObject.{u} E' ∧ f ≫ u' = u ∧ (cohomologyFunctor A i).map f y = 0 := by
  have hcu : cohomologyEquivHomRegularShift A i E y ≫ u = 0 := by
    rw [← cohomologyEquivHomRegularShift_naturality, hy,
      cohomologyEquivHomRegularShift_zero]
  obtain ⟨E', f, w, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle (cohomologyEquivHomRegularShift A i E y)
  have hcf : cohomologyEquivHomRegularShift A i E y ≫ f = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
  obtain ⟨u', hu'⟩ := Pretriangulated.Triangle.yoneda_exact₂ _ hT u hcu
  refine ⟨E', f, u',
    isCompactObject_obj₃ _ hT (isCompactObject_shift_regularObject A (-i)) hE, hu'.symm, ?_⟩
  refine (cohomologyEquivHomRegularShift A i E').injective ?_
  rw [cohomologyEquivHomRegularShift_naturality, hcf, cohomologyEquivHomRegularShift_zero]

end DifferentialGradedModule

end
