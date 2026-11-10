module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Localization.Construction
public import StacksFrontier.Algebra.DifferentialGraded.Module.LongExactSequence
public import StacksFrontier.Algebra.DifferentialGraded.Module.Triangulated
public import StacksFrontier.Algebra.DirectSum.GradedSubmodule
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksCore.Tactic.StacksAttribute
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksCore.Algebra.Homology.HomologicalComplexAbelian

/-! # Acyclic differential graded modules and quasi-isomorphisms

For a differential graded algebra `(A, d)` over a commutative ring `R`, the acyclic right
differential graded `A`-modules form a strictly full, saturated triangulated subcategory of the
homotopy category `K(A, d)`, and the multiplicative system it generates consists exactly of the
quasi-isomorphisms. Localizing `K(A, d)` at the quasi-isomorphisms — the derived category of
`(A, d)` — therefore kills precisely the acyclic modules, and degree-zero cohomology descends
through both the homotopy category and that localization.

## Main definitions

* `DifferentialGradedModule.acyclic'`: the acyclic modules, as a property of objects of
  `K(A, d)`.
* `DifferentialGradedModule.quasiIsomorphisms'`: the morphisms of `K(A, d)` inducing an
  isomorphism on every cohomology module.
* `DifferentialGradedModule.DegreeZeroCohomologyDescent'`,
  `DifferentialGradedModule.degreeZeroCohomologyOnHomotopy'` and
  `DifferentialGradedModule.degreeZeroCohomologyOnLocalization'`: the descended cohomology
  functors, with the natural isomorphisms expressing each factorization.

## Main results

* `DifferentialGradedModule.acyclic_isClosedUnderIsomorphisms'`,
  `DifferentialGradedModule.acyclic_isTriangulated'` and
  `DifferentialGradedModule.acyclic_isSaturated'`: the acyclic modules are a strictly full,
  saturated triangulated subcategory.
* `DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms'`: the multiplicative system
  attached to that subcategory is the class of quasi-isomorphisms.
* `DifferentialGradedModule.quasiIsomorphisms_map_iff'`: a morphism in the image of the homotopy
  quotient is a quasi-isomorphism exactly when the representing map of differential graded
  modules is one.
* `DifferentialGradedModule.quasiIsomorphisms_isSaturated'`: the quasi-isomorphisms form a
  saturated multiplicative system.
* `DifferentialGradedModule.localization_kernel_eq_acyclic'`: the objects killed by the
  localization at the quasi-isomorphisms are exactly the acyclic modules.

## Implementation notes

Objects of `K(A, d)` are differential graded modules, and a quotient morphism is declared a
quasi-isomorphism when *every* map of differential graded modules representing it is a
quasi-isomorphism of the underlying cochain complexes. That is equivalent to the apparently
weaker condition on one representative, because homotopic maps induce the same map on
cohomology; `DifferentialGradedModule.quasiIsomorphisms_map_iff'` is what makes the description
usable, and representatives always exist because the homotopy quotient is full.

Everything else is deduced from a single homological functor,
`DifferentialGradedModule.degreeZeroHomologyOnHomotopy`: the acyclic modules are its
homological kernel, so the subcategory facts, the identification of `trW`, saturation and the
kernel of the localization are all instances of the general theory of the kernel of a
homological functor on a triangulated category
(`StacksFrontier/CategoryTheory/Triangulated/Quotient.lean`, Stacks Tags 05RD, 05RL and 05RM).

`DifferentialGradedModule.dgShiftToCochainShiftIso` has to identify
`(M.shift n).toCochainComplex.d i (i + 1)` with
`M.toCochainComplex.d (i + n) (i + 1 + n)`, whose second degree is `(i + n) + 1` only up to a
proved equality of integers. `DifferentialGradedModule.toCochainComplex_d` describes the
differential only at `d i (i + 1)`, so the comparison needs that description reindexed, which is
what `DifferentialGradedModule.toCochainComplex_d_eq_of_eq` supplies. The local
`implicit_reducible` attribute above covers the rest of the file.

## Naming

Every declaration here whose name ends in a prime is a second, independent treatment of the
same Tag 09KW material as `DifferentialGradedModule.acyclic` and
`DifferentialGradedModule.quasiIsomorphisms`, and the prime is what keeps the two apart. The
two *predicates* do agree: this file fixes the three universes of the homotopy category equal,
and at equal universes `DifferentialGradedModule.acyclic'` and
`DifferentialGradedModule.quasiIsomorphisms'` are the unprimed ones by `rfl`.

What is not interchangeable is everything stated against the triangulated structure of
`K(A, d)`. Here that structure is
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, whose distinguished triangles
are those of an admissible short exact sequence, and which is obtained by `Classical.choose`
from an existence statement; the unprimed family is stated against
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`, whose distinguished triangles
are the cone triangles. The two classes of triangles agree by Tag 09KH, but that
identification is not formalized, so the two instances are distinct data and neither family of
results can be used in place of the other. Concretely, with both modules imported,
`DifferentialGradedModule.acyclic_isTriangulated` does not have type
`(acyclic' A).IsTriangulated` and `DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms`
does not have type `(acyclic' A).trW = quasiIsomorphisms' A`, the mismatch being exactly the
pretriangulated and preadditive instances. The results that do *not* mention the triangulated
structure transfer: `DifferentialGradedModule.quasiIsomorphisms_map_iff`,
`DifferentialGradedModule.acyclic_isSaturated` and
`DifferentialGradedModule.quasiIsomorphisms_isSaturated` close the primed statements, and
`DifferentialGradedModule.degreeZeroCohomologyOnHomotopy'` is the unprimed functor by `rfl`.
Unifying the two developments therefore waits on Tag 09KH.

## References

* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

/- The underlying cochain complex of a differential graded module, its differential and the
underlying map of a homomorphism are made locally reducible: the comparisons below are between
a construction on `M.grading n` and the same construction on `M.toCochainComplex.X n`, which are
equal by definition but not reducibly so. -/
attribute [local implicit_reducible] toCochainComplex gradedDifferential Hom.gradedMap

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)

/-- Transporting a homogeneous element along an equality of degrees does not change it. -/
lemma grading_eqToHom_apply
    {M : DifferentialGradedModule.{u, u, u} A} {i j : ℤ} (h : i = j)
    (x : M.grading i) :
    ((eqToHom (congrArg (fun n => ModuleCat.of R (M.grading n)) h)).hom x : M.M) = x := by
  subst j
  rfl

/-- A homotopy between homomorphisms of differential graded modules induces a homotopy between
the underlying cochain maps. -/
noncomputable def underlyingHomotopy
    {M N : DifferentialGradedModule.{u, u, u} A} {f g : M ⟶ N}
    (h : Homotopy f g) :
    _root_.Homotopy f.toCochainMap g.toCochainMap := by
  let k (n m : ℤ) (hnm : m + 1 = n) : M.grading n →ₗ[R] N.grading m := {
    toFun := fun x => ⟨h.toLinearMap x, by
      have hx := h.map_grading n x x.property
      simpa only [show n - 1 = m by omega] using hx⟩
    map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
    map_smul' := by
      intro r x
      apply Subtype.ext
      exact (h.toLinearMap.restrictScalars R).map_smul r x }
  refine {
    hom := fun n m => if hnm : m + 1 = n then ModuleCat.ofHom (k n m hnm) else 0
    zero := by intro n m hnm; exact dite_eq_right hnm
    comm := ?_ }
  intro n
  rw [dNext_eq _ (i' := n + 1) (by rfl),
    prevD_eq _ (j' := n - 1) (by change n - 1 + 1 = n; omega)]
  simp only [dite_eq_left (show n - 1 + 1 = n by omega)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change M.grading n at x
  apply Subtype.ext
  have he := h.homotopy_eq (x : M.M)
  simp only [toCochainComplex,
    CochainComplex.of.d, sub_add_cancel, dite_true]
  simp only [eqToHom_refl, Category.comp_id, ModuleCat.hom_add, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.add_apply, Submodule.coe_add,
    grading_eqToHom_apply (A := A) (M := N)
      (show n - 1 + 1 = n by omega),
    Hom.toCochainMap_f, ModuleCat.hom_ofHom]
  change f.toFun x = h.toLinearMap (M.d x) + N.d (h.toLinearMap x) + g.toFun x
  calc
    f.toFun x = (N.d (h.toLinearMap x) + h.toLinearMap (M.d x)) + g.toFun x :=
      (sub_eq_iff_eq_add).mp he
    _ = _ := by abel

/-- Degree-zero cohomology of a differential graded module, descended to the homotopy category.
The descent is possible because homotopic homomorphisms induce the same map on cohomology. -/
noncomputable def degreeZeroHomologyOnHomotopy :
    HomotopyCategory.{u, u, u} A ⥤ ModuleCat.{u} R :=
  CategoryTheory.Quotient.lift (homotopyRel A)
    (forgetToCochainComplex A ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0)
    (by
      intro M N f g h
      exact (underlyingHomotopy (A := A) h.some).homologyMap_eq 0)

/-- The differential of the underlying cochain complex, on a homogeneous element. -/
theorem toCochainComplex_d_apply
    (M : DifferentialGradedModule.{u, u, u} A) (i : ℤ) (x : M.grading i) :
    (M.toCochainComplex.d i (i + 1)).hom x = M.gradedDifferential i x := by
  rw [M.toCochainComplex_d]
  rfl

/-- The differential of the underlying cochain complex between any two degrees that differ by
one. `DifferentialGradedModule.toCochainComplex_d` describes `d i j` only in the spelling
`j = i + 1`; this reindexes it along a proved equality of degrees, conjugated by the transport
of the target component, so that the description is available at any `j` with `i + 1 = j`.

Mathlib's `HomologicalComplex.d_comp_XIsoOfEq_hom` is the same reindexing for a general
complex, but phrases the transport through `HomologicalComplex.XIsoOfEq`, whose source and
target are written with `HomologicalComplex.X`. Matching that against a component of
`CochainComplex.of` is not something `rw` or `simp` will do, so the form here names the
components directly as `ModuleCat.of R (M.grading _)`, which is what makes it usable. -/
theorem toCochainComplex_d_eq_of_eq
    (M : DifferentialGradedModule.{u, u, u} A) {i j : ℤ} (h : i + 1 = j) :
    M.toCochainComplex.d i j =
      ModuleCat.ofHom (M.gradedDifferential i) ≫
        eqToHom (congrArg (fun k => ModuleCat.of R (M.grading k)) h) := by
  subst h
  rw [M.toCochainComplex_d, eqToHom_refl, Category.comp_id]

/-- The underlying cochain complex of a shifted differential graded module has the same terms as
the shift of the underlying cochain complex. -/
theorem dgShiftCochainComponentEq
    (M : DifferentialGradedModule.{u, u, u} A) (n i : ℤ) :
    (shift M n).toCochainComplex.X i =
      ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj
        M.toCochainComplex).X i := by
  simp [toCochainComplex_X,
    CochainComplex.shiftFunctor_obj_X', shift_grading]
  rfl

/-- The underlying cochain complex of a shifted differential graded module is isomorphic to the
shift of the underlying cochain complex. -/
noncomputable def dgShiftToCochainShiftIso
    (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    (shift M n).toCochainComplex ≅
      (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj
        M.toCochainComplex := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => show (shift M n).toCochainComplex.X i ≅
      ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj
        M.toCochainComplex).X i from
          eqToIso (dgShiftCochainComponentEq (A := A) M n i)) ?_
  intro i j hij
  simp only [ComplexShape.up_Rel] at hij
  subst j
  have hidx : (i + n) + 1 = (i + 1) + n := by omega
  have hi := dgShiftCochainComponentEq (A := A) M n i
  have hj := dgShiftCochainComponentEq (A := A) M n (i + 1)
  cases hi
  cases hj
  simp only [eqToIso, eqToHom_refl, Category.id_comp, Category.comp_id,
    CochainComplex.shiftFunctor_obj_d']
  rw [toCochainComplex_d, toCochainComplex_d_eq_of_eq (A := A) M hidx]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change M.grading (i + n) at x
  apply Subtype.ext
  simp [grading_eqToHom_apply (A := A) (M := M) hidx]
  rfl

/-- The forgetful functor to cochain complexes commutes with the shift, naturally in the module. -/
noncomputable def dgShiftToCochainShiftNatIso (n : ℤ) :
    shiftFunctor A n ⋙ forgetToCochainComplex A ≅
      forgetToCochainComplex A ⋙
        CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n :=
  NatIso.ofComponents (fun M => dgShiftToCochainShiftIso A M n) (by
    intro M N f
    ext i x
    rfl)

/-- Degree-`i` cohomology of a differential graded module, descended to the homotopy category. -/
noncomputable def homologyOnHomotopy (i : ℤ) :
    HomotopyCategory.{u, u, u} A ⥤ ModuleCat.{u} R :=
  CategoryTheory.Quotient.lift (homotopyRel A)
    (forgetToCochainComplex A ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i)
    (by
      intro M N f g h
      exact (underlyingHomotopy (A := A) h.some).homologyMap_eq i)

/-- Degree-zero cohomology of an `i`-fold shift is degree-`i` cohomology. -/
noncomputable def homologyShiftIso
    (M : DifferentialGradedModule.{u, u, u} A) (i : ℤ) :
    (degreeZeroHomologyOnHomotopy A).obj
        ((toHomotopyCategory.{u, u, u} A).obj (shift M i)) ≅
      (homologyOnHomotopy (A := A) i).obj ((toHomotopyCategory.{u, u, u} A).obj M) := by
  let F₀ := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0
  let Fᵢ := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i
  have e₁ : F₀.obj (shift M i).toCochainComplex ≅
      F₀.obj ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) i).obj
        M.toCochainComplex) := F₀.mapIso (dgShiftToCochainShiftIso (A := A) M i)
  have e₂ : F₀.obj ((CategoryTheory.shiftFunctor
        (CochainComplex (ModuleCat.{u} R) ℤ) i).obj M.toCochainComplex) ≅
    Fᵢ.obj M.toCochainComplex := (F₀.shiftIso i 0 i (by omega)).app M.toCochainComplex
  simpa only [degreeZeroHomologyOnHomotopy, homologyOnHomotopy,
    Quotient.lift_obj_functor_obj, Functor.comp_obj,
    forgetToCochainComplex,
    HomologicalComplex.homologyFunctor_obj, F₀, Fᵢ] using e₁ ≪≫ e₂

/-- Degree-zero cohomology of an `i`-fold shift vanishes exactly when degree-`i` cohomology
does. -/
theorem degreeZeroHomology_shift_isZero_iff
    (M : DifferentialGradedModule.{u, u, u} A) (i : ℤ) :
    IsZero ((degreeZeroHomologyOnHomotopy A).obj
      (((toHomotopyCategory.{u, u, u} A).obj M)⟦i⟧)) ↔
    IsZero ((homologyOnHomotopy (A := A) i).obj ((toHomotopyCategory.{u, u, u} A).obj M)) := by
  have hshift : (((toHomotopyCategory.{u, u, u} A).obj M)⟦i⟧) =
      (toHomotopyCategory.{u, u, u} A).obj (shift M i) := by
    change ((CategoryTheory.shiftFunctor
        (HomotopyCategory.{u, u, u} A) i).obj
          ((toHomotopyCategory.{u, u, u} A).obj M)) =
      (toHomotopyCategory.{u, u, u} A).obj
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, u, u} A) i).obj M)
    exact CategoryTheory.Quotient.functor_obj_shift
      (homotopyRel A) ℤ M i
  rw [hshift]
  exact (homologyShiftIso A M i).isZero_iff

/-- A differential graded module is acyclic exactly when all of its cohomology modules vanish. -/
theorem acyclic_iff_homologyOnHomotopy
    (M : DifferentialGradedModule.{u, u, u} A) :
    M.toCochainComplex.Acyclic ↔ ∀ i : ℤ,
      IsZero ((homologyOnHomotopy (A := A) i).obj ((toHomotopyCategory.{u, u, u} A).obj M)) := by
  rw [HomologicalComplex.acyclic_iff]
  simp only [HomologicalComplex.exactAt_iff_isZero_homology, homologyOnHomotopy,
    Quotient.lift_obj_functor_obj, Functor.comp_obj, forgetToCochainComplex,
    HomologicalComplex.homologyFunctor_obj]

/-- Degree-zero cohomology on the homotopy category is additive. -/
theorem degreeZeroHomologyOnHomotopy_additive :
    (degreeZeroHomologyOnHomotopy A).Additive := by
  let q : DifferentialGradedModule.{u, u, u} A ⥤
      HomotopyCategory.{u, u, u} A := toHomotopyCategory.{u, u, u} A
  let H : HomotopyCategory.{u, u, u} A ⥤ ModuleCat.{u} R :=
      degreeZeroHomologyOnHomotopy A
  have : (q ⋙ H).Additive := by
    apply CategoryTheory.Functor.additive_of_iso
      (CategoryTheory.Quotient.lift.isLift _ _ _).symm
  exact CategoryTheory.Functor.additive_of_full_essSurj_comp q H

/-- In an admissible short exact sequence, the composite of the underlying maps vanishes. -/
private theorem toFun_comp_toFun_eq_zero
    {K L M : DifferentialGradedModule.{u, u, u} A}
    {f : K ⟶ L} {g : L ⟶ M} (hfg : IsAdmissibleShortExact f g) (x : K.M) :
    g.toFun (f.toFun x) = 0 := by
  have hmem : f.toFun x ∈ LinearMap.ker g.toFun := by
    rw [← hfg.exact]
    exact ⟨x, rfl⟩
  exact hmem

/-- An element of a graded piece hit by a homomorphism is hit from the same graded piece. -/
private theorem exists_gradedMap_eq
    {K L : DifferentialGradedModule.{u, u, u} A} (φ : K ⟶ L) (n : ℤ) (y : L.grading n)
    (x : K.M) (hx : φ.toFun x = y) : ∃ z, φ.gradedMap n z = y := by
  have hgraded := DirectSum.coe_decompose_apply_map (R := R)
    K.grading L.grading φ.toFun (fun i z hz => φ.map_grading i z hz) x n
  rw [hx, DirectSum.decompose_of_mem_same L.grading y.2] at hgraded
  exact ⟨⟨_, (DirectSum.decompose K.grading x n).2⟩, Subtype.ext hgraded.symm⟩

/-- An admissible short exact sequence of differential graded modules remains short exact after
forgetting to cochain complexes over the base ring. -/
theorem admissibleShortExact_forgetToCochainComplex
    {K L M : DifferentialGradedModule.{u, u, u} A}
    (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) :
    ((ShortComplex.mk f g (by
      apply Hom.ext
      apply LinearMap.ext
      intro x
      have hmem : f.toFun x ∈ LinearMap.ker g.toFun := by
        rw [← hfg.exact]
        exact ⟨x, rfl⟩
      change g.toFun (f.toFun x) = 0 at hmem
      exact hmem)).map
        (forgetToCochainComplex A)).ShortExact := by
  have hExact (n : ℤ) : Function.Exact (f.gradedMap n) (g.gradedMap n) := by
    intro y
    constructor
    · intro hy
      have hmem : (y : L.M) ∈ LinearMap.range f.toFun := by
        rw [hfg.exact, LinearMap.mem_ker]
        exact congrArg Subtype.val hy
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hmem
      exact exists_gradedMap_eq A f n y x hx
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      exact toFun_comp_toFun_eq_zero A hfg x
  have hSurj (n : ℤ) : Function.Surjective (g.gradedMap n) := by
    intro y
    obtain ⟨x, hx⟩ := hfg.surjective (y : M.M)
    exact exists_gradedMap_eq A g n y x hx
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact hExact n
  · rw [ModuleCat.mono_iff_injective]
    exact fun _ _ hxy => Subtype.ext (hfg.injective (congrArg Subtype.val hxy))
  · rw [ModuleCat.epi_iff_surjective]
    exact hSurj n

/-- Degree-zero cohomology on the homotopy category is a homological functor: it takes a
distinguished triangle to an exact sequence. This is the single input from which all the
subcategory and localization statements below are deduced. -/
theorem degreeZeroHomologyOnHomotopy_isHomological :
    (degreeZeroHomologyOnHomotopy A).IsHomological := by
  let Q := toHomotopyCategory.{u, u, u} A
  let H := degreeZeroHomologyOnHomotopy A
  let : H.Additive := degreeZeroHomologyOnHomotopy_additive (A := A)
  apply Functor.IsHomological.mk'
  intro T hT
  rw [distinguishedTriangles_eq] at hT
  obtain ⟨K, L, M, f, g, hfg, c, ⟨e⟩⟩ :=
    (isDistinguishedTriangle_iff A T).mp hT
  let S : ShortComplex (DifferentialGradedModule.{u, u, u} A) :=
    ShortComplex.mk f g (by
      apply Hom.ext
      apply LinearMap.ext
      exact toFun_comp_toFun_eq_zero A hfg)
  have hS := admissibleShortExact_forgetToCochainComplex A f g hfg
  have hLES := HomologicalComplex.HomologySequence.composableArrows₅_exact hS 0 1 (by simp)
  refine ⟨associatedTriangleOfSplittings A f g hfg c, e, ?_⟩
  let F0 := forgetToCochainComplex A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0
  have hF0 : (S.map F0).Exact := by
    change ((HomologicalComplex.HomologySequence.composableArrows₅ hS 0 1 (by simp)).sc
      hLES.toIsComplex 0 (by omega)).Exact
    exact hLES.exact 0
  let isoH : Q ⋙ H ≅ F0 := CategoryTheory.Quotient.lift.isLift _ _ _
  change (S.map (Q ⋙ H)).Exact
  exact (ShortComplex.exact_iff_of_iso (S.mapNatIso isoH)).2 hF0

/-- Being a quasi-isomorphism is invariant under homotopy of homomorphisms. -/
theorem quasiIso_of_homotopic'
    {M N : DifferentialGradedModule.{u, u, u} A}
    {f g : M ⟶ N} (h : Homotopic f g)
    (hf : QuasiIso f.toCochainMap) : QuasiIso g.toCochainMap := by
  refine (quasiIso_iff _).2 ?_
  intro i
  apply (quasiIsoAt_iff _ i).2
  have hIso : IsIso (HomologicalComplex.homologyMap g.toCochainMap i) := by
    rw [← (underlyingHomotopy A h.some).homologyMap_eq i]
    change IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).map
        f.toCochainMap))
    exact ((quasiIsoAt_iff f.toCochainMap i).1 (hf.quasiIsoAt i)).isIso'
  exact ⟨hIso⟩

/-- The acyclic differential graded modules, as objects of the homotopy category. -/
@[stacks 09KW "acyclic subcategory"]
def acyclic' : ObjectProperty (HomotopyCategory.{u, u, u} A) :=
  fun X => X.as.toCochainComplex.Acyclic

/-- The quasi-isomorphisms in the homotopy category of differential graded modules. -/
@[stacks 09KW "quasi-isomorphisms"]
def quasiIsomorphisms' :
    MorphismProperty (HomotopyCategory.{u, u, u} A) :=
  fun X Y f => ∀ (g : X.as ⟶ Y.as), (toHomotopyCategory.{u, u, u} A).map g = f →
    QuasiIso ((forgetToCochainComplex A).map g)

/-- A quasi-isomorphism of differential graded modules is inverted by degree-zero cohomology on
the homotopy category. -/
theorem degreeZeroHomology_map_isIso
    {M N : DifferentialGradedModule.{u, u, u} A} (g : M ⟶ N)
    (hg : QuasiIso ((forgetToCochainComplex A).map g)) :
    IsIso ((degreeZeroHomologyOnHomotopy A).map ((toHomotopyCategory.{u, u, u} A).map g)) := by
  let F := forgetToCochainComplex A
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0
  have hmap : (degreeZeroHomologyOnHomotopy A).map ((toHomotopyCategory.{u, u, u} A).map g) =
      (F ⋙ H).map g := CategoryTheory.Quotient.lift_map_functor_map _ _ _ g
  rw [hmap]
  have hQi : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
        (ComplexShape.up ℤ) 0).map (F.map g)) :=
    (quasiIsoAt_iff (F.map g) 0).1 ((quasiIso_iff (F.map g)).1 hg 0)
  change IsIso (HomologicalComplex.homologyMap (F.map g) 0)
  exact hQi.isIso'

/-- Degree-zero cohomology on the homotopy category inverts the quasi-isomorphisms, which is what
lets it descend to the localization. -/
theorem degreeZeroHomology_inverts_quasiIsomorphisms :
    (quasiIsomorphisms' A).IsInvertedBy (degreeZeroHomologyOnHomotopy A) := by
  intro X Y f hf
  induction f using Quot.inductionOn with
  | _ g =>
    exact degreeZeroHomology_map_isIso (A := A) g (hf g rfl)

/-- The functors and natural isomorphisms expressing descent of degree-zero
cohomology through the homotopy category and its localization. -/
structure DegreeZeroCohomologyDescent' where
  /-- Degree-zero cohomology on the homotopy category. -/
  homotopy : HomotopyCategory.{u, u, u} A ⥤ ModuleCat.{u} R
  /-- Degree-zero cohomology on the localization at quasi-isomorphisms. -/
  localization : (quasiIsomorphisms' A).Localization ⥤ ModuleCat.{u} R
  /-- `homotopy` composed with the quotient functor is degree-zero cohomology of the underlying
  cochain complex. -/
  homotopyIso :
    (toHomotopyCategory.{u, u, u} A) ⋙ homotopy ≅
      forgetToCochainComplex A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0
  /-- `localization` composed with the localization functor is `homotopy`. -/
  localizationIso : (quasiIsomorphisms' A).Q ⋙ localization ≅ homotopy

/-- The canonical descent data for degree-zero cohomology. -/
@[stacks 09KW "factorization of degree-zero cohomology"]
noncomputable def degreeZeroCohomologyDescent' :
    DegreeZeroCohomologyDescent' A where
  homotopy := degreeZeroHomologyOnHomotopy A
  localization := Localization.lift (degreeZeroHomologyOnHomotopy A)
    (degreeZeroHomology_inverts_quasiIsomorphisms A) (quasiIsomorphisms' A).Q
  homotopyIso := CategoryTheory.Quotient.lift.isLift _ _ _
  localizationIso := Localization.fac (degreeZeroHomologyOnHomotopy A)
    (degreeZeroHomology_inverts_quasiIsomorphisms A) (quasiIsomorphisms' A).Q

/-- Degree-zero cohomology on the DG-module homotopy category. -/
noncomputable def degreeZeroCohomologyOnHomotopy' :
    HomotopyCategory.{u, u, u} A ⥤ ModuleCat.{u} R :=
  (degreeZeroCohomologyDescent' A).homotopy

/-- Degree-zero cohomology on the localization at quasi-isomorphisms. -/
noncomputable def degreeZeroCohomologyOnLocalization' :
    (quasiIsomorphisms' A).Localization ⥤ ModuleCat.{u} R :=
  (degreeZeroCohomologyDescent' A).localization

/-- The natural identification of homotopy-category cohomology with DG-module
cohomology. -/
noncomputable def degreeZeroCohomologyOnHomotopyIso' :
    (toHomotopyCategory.{u, u, u} A) ⋙ degreeZeroCohomologyOnHomotopy' A ≅
      forgetToCochainComplex A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0 :=
  (degreeZeroCohomologyDescent' A).homotopyIso

/-- The natural identification expressing descent through localization. -/
noncomputable def degreeZeroCohomologyOnLocalizationIso' :
    (quasiIsomorphisms' A).Q ⋙ degreeZeroCohomologyOnLocalization' A ≅
      degreeZeroCohomologyOnHomotopy' A :=
  (degreeZeroCohomologyDescent' A).localizationIso

/-- A DG-module map induces a quasi-isomorphism in the homotopy category
exactly when it is a quasi-isomorphism of the underlying cochain complexes. -/
@[stacks 09KW "quasi-isomorphisms represented by DG-module maps"]
theorem quasiIsomorphisms_map_iff'
    {M N : DifferentialGradedModule.{u, u, u} A} (g : M ⟶ N) :
    quasiIsomorphisms' A ((toHomotopyCategory.{u, u, u} A).map g) ↔
      QuasiIso ((forgetToCochainComplex A).map g) :=
  ⟨fun h => h g rfl, fun hg g' hg' => quasiIso_of_homotopic' A
    ((CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) g g').mp hg'.symm) hg⟩

/-- Acyclicity is invariant under isomorphism in the homotopy category. -/
@[stacks 09KW "strict fullness"]
instance acyclic_isClosedUnderIsomorphisms' :
    (acyclic' A).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    cases X with
    | mk M =>
      cases Y with
      | mk N =>
        have hX' := (acyclic_iff_homologyOnHomotopy (A := A) M).mp hX
        apply (acyclic_iff_homologyOnHomotopy (A := A) N).mpr
        exact fun i => (hX' i).of_iso ((homologyOnHomotopy A i).mapIso e).symm

/-- The homological kernel of degree-zero cohomology is the subcategory of acyclic modules. -/
theorem homologicalKernel_degreeZeroHomology_eq_acyclic :
    (degreeZeroHomologyOnHomotopy A).homologicalKernel = acyclic' A := by
  ext X
  cases X with
  | mk M =>
    change (∀ i : ℤ, IsZero ((degreeZeroHomologyOnHomotopy A).obj
      (((toHomotopyCategory.{u, u, u} A).obj M)⟦i⟧))) ↔ M.toCochainComplex.Acyclic
    rw [acyclic_iff_homologyOnHomotopy A M]
    exact forall_congr' (degreeZeroHomology_shift_isZero_iff A M)

/-- Acyclic differential graded modules form a triangulated subcategory. -/
@[stacks 09KW "triangulated subcategory"]
instance acyclic_isTriangulated' : (acyclic' A).IsTriangulated := by
  rw [← homologicalKernel_degreeZeroHomology_eq_acyclic A]
  let := degreeZeroHomologyOnHomotopy_isHomological A
  exact (Functor.isTriangulated_and_isSaturated_homologicalKernel
    (degreeZeroHomologyOnHomotopy A)).1

/-- The triangulated subcategory of acyclic modules is saturated. -/
@[stacks 09KW "saturation of acyclic modules"]
instance acyclic_isSaturated' : (acyclic' A).IsSaturated := by
  rw [← homologicalKernel_degreeZeroHomology_eq_acyclic A]
  let := degreeZeroHomologyOnHomotopy_isHomological A
  exact (Functor.isTriangulated_and_isSaturated_homologicalKernel
    (degreeZeroHomologyOnHomotopy A)).2

/-- Degree-`i` cohomology factors through the homotopy category as the `i`-fold shift followed by
degree-zero cohomology. -/
noncomputable def homologyShiftFactorsIso (i : ℤ) :
    toHomotopyCategory.{u, u, u} A ⋙
        (CategoryTheory.shiftFunctor (HomotopyCategory.{u, u, u} A) i ⋙
          degreeZeroHomologyOnHomotopy A) ≅
      forgetToCochainComplex A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i := by
  let Q := toHomotopyCategory.{u, u, u} A
  let S := CategoryTheory.shiftFunctor (HomotopyCategory.{u, u, u} A) i
  let S' := shiftFunctor A i
  let U := forgetToCochainComplex A
  let H := degreeZeroHomologyOnHomotopy A
  let H₀ := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0
  let Sc := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) i
  exact (Functor.associator Q S H).symm ≪≫
    Functor.isoWhiskerRight (Q.commShiftIso i).symm H ≪≫
    Functor.associator S' Q H ≪≫
    Functor.isoWhiskerLeft S' (CategoryTheory.Quotient.lift.isLift _ _ _) ≪≫
    (Functor.associator S' U H₀).symm ≪≫
    Functor.isoWhiskerRight (dgShiftToCochainShiftNatIso A i) H₀ ≪≫
    Functor.associator U Sc H₀ ≪≫
    Functor.isoWhiskerLeft U (H₀.shiftIso i 0 i (by omega))

/-- A homomorphism of differential graded modules induces an isomorphism on the `i`-fold shift of
degree-zero cohomology exactly when it does on degree-`i` cohomology of cochain complexes. -/
theorem degreeZeroHomology_shift_map_isIso_iff
    {M N : DifferentialGradedModule.{u, u, u} A} (g : M ⟶ N) (i : ℤ) :
    IsIso ((degreeZeroHomologyOnHomotopy A).map
      (((toHomotopyCategory.{u, u, u} A).map g)⟦i⟧')) ↔
    IsIso (HomologicalComplex.homologyMap
      ((forgetToCochainComplex A).map g) i) :=
  NatIso.isIso_map_iff (homologyShiftFactorsIso A i) g

/-- The morphisms whose cones are acyclic are exactly the quasi-isomorphisms. -/
@[stacks 09KW "associated multiplicative system"]
theorem acyclic_trW_eq_quasiIsomorphisms' :
    (acyclic' A).trW = quasiIsomorphisms' A := by
  rw [← homologicalKernel_degreeZeroHomology_eq_acyclic A]
  let H := degreeZeroHomologyOnHomotopy A
  change H.homologicalKernel.trW = quasiIsomorphisms' A
  let := degreeZeroHomologyOnHomotopy_isHomological A
  let : H.ShiftSequence ℤ := Functor.ShiftSequence.tautological H ℤ
  ext X Y f
  cases X with
  | mk M =>
    cases Y with
    | mk N =>
      induction f using Quot.inductionOn with
      | _ g =>
        change H.homologicalKernel.trW ((toHomotopyCategory.{u, u, u} A).map g) ↔
          quasiIsomorphisms' A ((toHomotopyCategory.{u, u, u} A).map g)
        rw [quasiIsomorphisms_map_iff', H.mem_homologicalKernel_trW_iff,
          quasiIso_iff]
        apply forall_congr'
        intro i
        exact (degreeZeroHomology_shift_map_isIso_iff A g i).trans
          (quasiIsoAt_iff_isIso_homologyMap _ i).symm

/-- The quasi-isomorphisms admit a right calculus of fractions: they are the morphisms whose cone
is acyclic, and the acyclic modules form a triangulated subcategory. -/
instance quasiIsomorphisms_hasRightCalculusOfFractions' :
    (quasiIsomorphisms' A).HasRightCalculusOfFractions := by
  rw [← acyclic_trW_eq_quasiIsomorphisms' A]
  infer_instance

/-- Quasi-isomorphisms form a saturated multiplicative system. -/
@[stacks 09KW "saturated multiplicative system"]
theorem quasiIsomorphisms_isSaturated' :
    (quasiIsomorphisms' A).IsSaturated := by
  rw [← acyclic_trW_eq_quasiIsomorphisms' A,
    ← homologicalKernel_degreeZeroHomology_eq_acyclic A]
  let := degreeZeroHomologyOnHomotopy_isHomological A
  exact (Functor.isSaturated_homologicalKernel_and_mem_trW_iff_and_exists_lift
    (degreeZeroHomologyOnHomotopy A)
    (degreeZeroHomologyOnHomotopy A).homologicalKernel.trW.Q).2.1.1

/-- The objects annihilated by localization at quasi-isomorphisms are exactly
the acyclic differential graded modules. -/
@[stacks 09KW "kernel of localization"]
theorem localization_kernel_eq_acyclic' :
    ((quasiIsomorphisms' A).Q).kernel = acyclic' A := by
  rw [← acyclic_trW_eq_quasiIsomorphisms' A]
  exact ObjectProperty.isLeast_trW_kernel_and_kernel_eq_self.2
    (acyclic' A) (acyclic' A).trW.Q

end DifferentialGradedModule
