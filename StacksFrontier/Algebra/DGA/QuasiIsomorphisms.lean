module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Localization.Predicate
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.LongExactSequence
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.Algebra.DGA.Pretriangulated
public import StacksFrontier.Algebra.DGA.Octahedron
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Acyclic differential graded modules and quasi-isomorphisms

Let `A` be a differential graded algebra. Inside the homotopy category of right
differential graded `A`-modules there are two distinguished classes: the acyclic
modules, and the morphisms that induce isomorphisms on all cohomology. The
derived category of `A` is obtained from the homotopy category either by killing
the first class or by inverting the second, so both classes have to be available
before that construction can be stated.

## Main definitions

* `DifferentialGradedModule.acyclic` is the class of objects of the homotopy
  category whose underlying cochain complex is acyclic.
* `DifferentialGradedModule.quasiIsomorphisms` is the class of morphisms of the
  homotopy category represented by quasi-isomorphisms of underlying cochain
  complexes.
* `DifferentialGradedModule.DegreeZeroCohomologyDescent` packages the two functors
  and the two natural isomorphisms through which degree-zero cohomology descends,
  and `DifferentialGradedModule.degreeZeroCohomologyDescent` constructs them.
* `DifferentialGradedModule.degreeZeroCohomologyOnHomotopy` and
  `DifferentialGradedModule.degreeZeroCohomologyOnLocalization` are degree-zero
  cohomology on the homotopy category and on the localization at
  quasi-isomorphisms, with
  `DifferentialGradedModule.degreeZeroCohomologyOnHomotopyIso` and
  `DifferentialGradedModule.degreeZeroCohomologyOnLocalizationIso` the natural
  isomorphisms identifying each with the previous stage.

## Implementation notes

Objects of the homotopy category are a type synonym of differential graded
modules, so acyclicity of an object is acyclicity of the cochain complex
underlying its representative; no choice is involved and the predicate needs no
well-definedness argument.

Morphisms of the homotopy category are homotopy classes, so the corresponding
condition on a morphism `f` is stated over all differential graded module
homomorphisms representing `f`: every such representative is required to be a
quasi-isomorphism on underlying cochain complexes. Quantifying over all
representatives rather than choosing one keeps the definition free of choice and
makes the condition immediately usable, since homotopic homomorphisms induce the
same maps on cohomology. Representatives always exist because the homotopy
quotient functor is full.

Cohomology of the underlying complexes is taken in `ModuleCat R`, which is
abelian, so every cochain complex of such modules has homology in each degree
and `QuasiIso` applies without further hypotheses.

The descent of degree-zero cohomology is recorded as a structure bundling both
descended functors with both comparison isomorphisms, rather than as four
separate declarations. The homotopy category is a quotient category and the
localization is built by formally inverting morphisms, so each stage of the
descent is a universal factorization whose data and whose comparison isomorphism
are produced together; keeping them in one structure is what lets the second
factorization be stated against the functor the first one produced.

## Naming

`DifferentialGradedModule.acyclic'` and `DifferentialGradedModule.quasiIsomorphisms'` are a
second treatment of the same Tag 09KW material with the three universes of the homotopy
category fixed equal; at equal universes they are the properties defined here, by `rfl`. The
two families cannot be merged yet, because the primed one is stated against a different
pretriangulated structure on `K(A, d)` — distinguished triangles coming from admissible short
exact sequences rather than from cones — and the identification of the two classes of triangles
is Tag 09KH, which is not formalized. The `Naming` section of
`DifferentialGradedModule.acyclic'` records which statements do and do not transfer.

## References

* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- The acyclic differential graded modules, as a class of objects of the
homotopy category of right differential graded `A`-modules. -/
@[stacks 09KW "acyclic subcategory"]
def acyclic : ObjectProperty (HomotopyCategory.{u, v, w} A) :=
  fun X => X.as.toCochainComplex.Acyclic

/-- The quasi-isomorphisms in the homotopy category of right differential graded
`A`-modules: those morphisms all of whose representing homomorphisms are
quasi-isomorphisms of the underlying cochain complexes. -/
@[stacks 09KW "quasi-isomorphisms"]
def quasiIsomorphisms : MorphismProperty (HomotopyCategory.{u, v, w} A) :=
  fun X Y f => ∀ (g : X.as ⟶ Y.as), (toHomotopyCategory A).map g = f →
    QuasiIso ((forgetToCochainComplex A).map g)


/-! ### From a homotopy of differential graded modules to a homotopy of cochain complexes

A homotopy of differential graded module homomorphisms is a right `A`-linear map lowering
the grading by one; a Mathlib homotopy of the underlying cochain complexes is a family of
maps `grading i ⟶ grading j` supported on `j + 1 = i`.  Restricting the right `A`-linear
map to homogeneous components converts the former into the latter.
-/

section Bridge

variable {A}
variable {M N : DifferentialGradedModule.{u, v, w} A}

/-- The underlying map of a homotopy, as an `R`-linear map. -/
def Homotopy.toRLinearMap {f g : Hom M N} (h : Homotopy f g) : M.M →ₗ[R] N.M where
  toFun := h.toLinearMap
  map_add' := h.toLinearMap.map_add
  map_smul' r x := by
    rw [RingHom.id_apply, ← smul_one_smul (MulOpposite A.A) r x,
      h.toLinearMap.map_smul, smul_one_smul]

/-- `Homotopy.toRLinearMap` agrees pointwise with the underlying right `A`-linear map. -/
@[simp] theorem Homotopy.toRLinearMap_apply {f g : Hom M N} (h : Homotopy f g) (x : M.M) :
    h.toRLinearMap x = h.toLinearMap x := rfl

/-- A homotopy restricted to homogeneous components, lowering the degree by one. -/
def Homotopy.gradedHom {f g : Hom M N} (h : Homotopy f g) (i j : ℤ) (hij : j + 1 = i) :
    M.grading i →ₗ[R] N.grading j :=
  LinearMap.codRestrict _ (h.toRLinearMap ∘ₗ (M.grading i).subtype) (fun x => by
    have hx := h.map_grading i x x.2
    rwa [show i - 1 = j by omega] at hx)

/-- The value of `Homotopy.gradedHom` on a homogeneous element is the value of the homotopy
on it. -/
@[simp] theorem Homotopy.gradedHom_apply {f g : Hom M N} (h : Homotopy f g)
    (i j : ℤ) (hij : j + 1 = i) (x : M.grading i) :
    (h.gradedHom i j hij x : N.M) = h.toLinearMap x := rfl

/-- The components of the cochain homotopy induced by a homotopy: the restriction
`Homotopy.gradedHom` to degree `i` when `j + 1 = i`, and zero otherwise. -/
def Homotopy.cochainHom {f g : Hom M N} (h : Homotopy f g) (i j : ℤ) :
    M.toCochainComplex.X i ⟶ N.toCochainComplex.X j :=
  if hij : j + 1 = i then ModuleCat.ofHom (h.gradedHom i j hij) else 0

/-- For `j + 1 = i`, the component `Homotopy.cochainHom h i j` is the restriction
`Homotopy.gradedHom h i j`. -/
theorem Homotopy.cochainHom_eq {f g : Hom M N} (h : Homotopy f g) (i j : ℤ) (hij : j + 1 = i) :
    h.cochainHom i j = ModuleCat.ofHom (h.gradedHom i j hij) := dite_eq_left hij

/-- For `j + 1 ≠ i`, the component `Homotopy.cochainHom h i j` vanishes. -/
theorem Homotopy.cochainHom_eq_zero {f g : Hom M N} (h : Homotopy f g) (i j : ℤ)
    (hij : ¬ j + 1 = i) : h.cochainHom i j = 0 := dite_eq_right hij

/-- The homotopy identity on homogeneous components. -/
theorem Homotopy.comm_aux {f g : Hom M N} (h : Homotopy f g) (j : ℤ) :
    ModuleCat.ofHom (f.gradedMap (j + 1)) =
      ModuleCat.ofHom (M.gradedDifferential (j + 1)) ≫
          ModuleCat.ofHom (h.gradedHom (j + 1 + 1) (j + 1) rfl) +
        ModuleCat.ofHom (h.gradedHom (j + 1) j rfl) ≫
          ModuleCat.ofHom (N.gradedDifferential j) +
        ModuleCat.ofHom (g.gradedMap (j + 1)) := by
  ext x
  have hx := h.homotopy_eq ((x : ↥(M.grading (j + 1))) : M.M)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.add_apply,
    LinearMap.coe_comp, Function.comp_apply, Hom.gradedMap_apply, Submodule.coe_add,
    Homotopy.gradedHom_apply, gradedDifferential_apply]
  rw [← sub_eq_iff_eq_add, hx]
  abel

/-- A homotopy of differential graded module homomorphisms induces a homotopy of the
underlying cochain maps. -/
def Homotopy.toCochainHomotopy {f g : Hom M N} (h : Homotopy f g) :
    _root_.Homotopy f.toCochainMap g.toCochainMap where
  hom := h.cochainHom
  zero i j hij := h.cochainHom_eq_zero i j (fun hh => hij (ComplexShape.up_mk _ _ hh))
  comm i := by
    obtain ⟨j, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (ComplexShape.up_mk (j + 1) (j + 1 + 1) rfl),
      prevD_eq _ (ComplexShape.up_mk j (j + 1) rfl),
      h.cochainHom_eq (j + 1 + 1) (j + 1) rfl, h.cochainHom_eq (j + 1) j rfl,
      toCochainComplex_d, toCochainComplex_d, Hom.toCochainMap_f, Hom.toCochainMap_f]
    exact h.comm_aux j

/-- Homotopic homomorphisms induce the same map on the homology of the underlying
cochain complexes. -/
theorem homologyMap_eq_of_homotopic {f g : Hom M N} (h : Homotopic f g) (i : ℤ) :
    HomologicalComplex.homologyMap ((forgetToCochainComplex A).map f) i =
      HomologicalComplex.homologyMap ((forgetToCochainComplex A).map g) i :=
  h.some.toCochainHomotopy.homologyMap_eq i

/-- Being a quasi-isomorphism of underlying cochain complexes only depends on the homotopy
class of a homomorphism. -/
theorem quasiIso_of_homotopic {f g : Hom M N} (h : Homotopic f g)
    (hg : QuasiIso ((forgetToCochainComplex A).map g)) :
    QuasiIso ((forgetToCochainComplex A).map f) := by
  rw [quasiIso_iff] at hg ⊢
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, homologyMap_eq_of_homotopic h i,
    ← quasiIsoAt_iff_isIso_homologyMap]
  exact hg i

end Bridge

/-- A homomorphism of differential graded modules induces a quasi-isomorphism in the
homotopy category exactly when it is a quasi-isomorphism of the underlying cochain
complexes. -/
@[stacks 09KW "quasi-isomorphisms represented by DG-module maps"]
theorem quasiIsomorphisms_map_iff {M N : DifferentialGradedModule.{u, v, w} A} (g : M ⟶ N) :
    quasiIsomorphisms A ((toHomotopyCategory A).map g) ↔
      QuasiIso ((forgetToCochainComplex A).map g) :=
  ⟨fun h => h g rfl, fun h g' hg' =>
    quasiIso_of_homotopic ((CategoryTheory.Quotient.functor_map_eq_iff _ g' g).mp hg') h⟩

/-- Acyclicity is invariant under isomorphism in the homotopy category: an isomorphism there
is represented by a homotopy equivalence of the underlying cochain complexes, so it induces
isomorphisms on all homology. -/
@[stacks 09KW "strict fullness"]
instance acyclic_isClosedUnderIsomorphisms :
    (acyclic.{u, v, w} A).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨a, ha⟩ := (toHomotopyCategory A).map_surjective e.hom
    obtain ⟨b, hb⟩ := (toHomotopyCategory A).map_surjective e.inv
    have key : ∀ {P Q : DifferentialGradedModule.{u, v, w} A} (p : P ⟶ Q) (q : Q ⟶ P),
        Homotopic (p ≫ q) (𝟙 P) → ∀ i : ℤ,
          HomologicalComplex.homologyMap ((forgetToCochainComplex A).map p) i ≫
            HomologicalComplex.homologyMap ((forgetToCochainComplex A).map q) i = 𝟙 _ := by
      intro P Q p q hpq i
      rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp,
        homologyMap_eq_of_homotopic hpq i, CategoryTheory.Functor.map_id,
        HomologicalComplex.homologyMap_id]
    have hab : Homotopic (a ≫ b) (𝟙 X.as) := by
      refine (CategoryTheory.Quotient.functor_map_eq_iff
        (homotopyRel.{u, v, w} A) (a ≫ b) (𝟙 X.as)).mp ?_
      change (toHomotopyCategory A).map (a ≫ b) = (toHomotopyCategory A).map (𝟙 X.as)
      rw [CategoryTheory.Functor.map_comp, ha, hb, e.hom_inv_id,
        CategoryTheory.Functor.map_id]
      rfl
    have hba : Homotopic (b ≫ a) (𝟙 Y.as) := by
      refine (CategoryTheory.Quotient.functor_map_eq_iff
        (homotopyRel.{u, v, w} A) (b ≫ a) (𝟙 Y.as)).mp ?_
      change (toHomotopyCategory A).map (b ≫ a) = (toHomotopyCategory A).map (𝟙 Y.as)
      rw [CategoryTheory.Functor.map_comp, hb, ha, e.inv_hom_id,
        CategoryTheory.Functor.map_id]
      rfl
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hX' := hX i
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at hX'
    have : IsIso (HomologicalComplex.homologyMap ((forgetToCochainComplex A).map a) i) :=
      ⟨_, key a b hab i, key b a hba i⟩
    exact hX'.of_iso (asIso
      (HomologicalComplex.homologyMap ((forgetToCochainComplex A).map a) i)).symm

/-! ### Descent of degree-zero cohomology

Degree-zero cohomology of the underlying cochain complex is a functor on differential graded
modules.  Homotopic homomorphisms induce the same map on cohomology, so it factors through
the homotopy category; a quasi-isomorphism is sent to an isomorphism by the resulting
functor, so that functor factors in turn through the localization at the
quasi-isomorphisms.
-/

section Descent

/-- Degree-zero cohomology of the underlying cochain complex, as a functor on the homotopy
category of right differential graded `A`-modules.  This is the factorization of degree-zero
cohomology through the homotopy quotient. -/
noncomputable def degreeZeroCohomologyLift :
    HomotopyCategory.{u, v, w} A ⥤ ModuleCat.{w} R :=
  CategoryTheory.Quotient.lift (homotopyRel.{u, v, w} A)
    (forgetToCochainComplex A ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) 0)
    fun _ _ _ _ h => homologyMap_eq_of_homotopic h 0

/-- Degree-zero cohomology on the homotopy category sends quasi-isomorphisms to
isomorphisms of `R`-modules. -/
theorem isInvertedBy_degreeZeroCohomologyLift :
    (quasiIsomorphisms.{u, v, w} A).IsInvertedBy (degreeZeroCohomologyLift A) := by
  intro X Y f hf
  obtain ⟨g, rfl⟩ := (toHomotopyCategory A).map_surjective f
  have h : QuasiIso ((forgetToCochainComplex A).map g) := hf g rfl
  rw [quasiIso_iff] at h
  exact (quasiIsoAt_iff_isIso_homologyMap _ 0).mp (h 0)

/-- The data expressing descent of degree-zero cohomology through the homotopy category and
its localization at quasi-isomorphisms: a functor at each stage, together with a natural
isomorphism identifying it with the previous stage after composing with the canonical
functor. -/
structure DegreeZeroCohomologyDescent where
  /-- Degree-zero cohomology as a functor on the homotopy category. -/
  homotopy : HomotopyCategory.{u, v, w} A ⥤ ModuleCat.{w} R
  /-- Degree-zero cohomology as a functor on the localization at quasi-isomorphisms. -/
  localization : (quasiIsomorphisms.{u, v, w} A).Localization ⥤ ModuleCat.{w} R
  /-- Precomposing the homotopy-category functor with the homotopy quotient recovers
  degree-zero cohomology of the underlying cochain complexes. -/
  homotopyIso :
    toHomotopyCategory A ⋙ homotopy ≅
      forgetToCochainComplex A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) 0
  /-- Precomposing the functor on the localization with the localization functor recovers the
  functor on the homotopy category. -/
  localizationIso : (quasiIsomorphisms.{u, v, w} A).Q ⋙ localization ≅ homotopy

/-- Degree-zero cohomology of differential graded modules factors through the homotopy
category, and the resulting functor factors in turn through the localization at the
quasi-isomorphisms.  Both factorizations are the universal ones: the first is the lift along
the quotient by homotopy, available because homotopic homomorphisms agree on cohomology, and
the second is the lift along the localization functor, available because a quasi-isomorphism
becomes invertible on cohomology. -/
@[stacks 09KW "factorization of degree-zero cohomology"]
noncomputable def degreeZeroCohomologyDescent :
    DegreeZeroCohomologyDescent.{u, v, w} A where
  homotopy := degreeZeroCohomologyLift A
  localization :=
    CategoryTheory.Localization.lift (degreeZeroCohomologyLift A)
      (isInvertedBy_degreeZeroCohomologyLift A) (quasiIsomorphisms A).Q
  homotopyIso := CategoryTheory.Quotient.lift.isLift _ _ _
  localizationIso := CategoryTheory.Localization.fac _ _ _

/-- Degree-zero cohomology on the homotopy category of right differential graded
`A`-modules. -/
noncomputable def degreeZeroCohomologyOnHomotopy :
    HomotopyCategory.{u, v, w} A ⥤ ModuleCat.{w} R :=
  (degreeZeroCohomologyDescent.{u, v, w} A).homotopy

/-- Degree-zero cohomology on the localization of the homotopy category at the
quasi-isomorphisms. -/
noncomputable def degreeZeroCohomologyOnLocalization :
    (quasiIsomorphisms.{u, v, w} A).Localization ⥤ ModuleCat.{w} R :=
  (degreeZeroCohomologyDescent.{u, v, w} A).localization

/-- Degree-zero cohomology on the homotopy category agrees with degree-zero cohomology of the
underlying cochain complexes. -/
noncomputable def degreeZeroCohomologyOnHomotopyIso :
    toHomotopyCategory A ⋙ degreeZeroCohomologyOnHomotopy.{u, v, w} A ≅
      forgetToCochainComplex A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) 0 :=
  (degreeZeroCohomologyDescent.{u, v, w} A).homotopyIso

/-- Degree-zero cohomology on the localization at the quasi-isomorphisms agrees with
degree-zero cohomology on the homotopy category. -/
noncomputable def degreeZeroCohomologyOnLocalizationIso :
    (quasiIsomorphisms.{u, v, w} A).Q ⋙ degreeZeroCohomologyOnLocalization.{u, v, w} A ≅
      degreeZeroCohomologyOnHomotopy.{u, v, w} A :=
  (degreeZeroCohomologyDescent.{u, v, w} A).localizationIso

end Descent

/-! ### Cohomology in every degree, and the shift

Degree-zero cohomology of a shifted differential graded module is cohomology of the original one
in the shifted degree, both on objects and naturally in the module.

The underlying cochain complex of `M[n]` and the `n`-th shift of the underlying cochain complex of
`M` have the same objects and the same differentials.
-/

section Shift

private theorem shiftToCochain_X_eq (M : DifferentialGradedModule.{u, v, w} A) (n i : ℤ) :
    (shift M n).toCochainComplex.X i =
      ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) n).obj
        M.toCochainComplex).X i := rfl

private theorem toCochainComplex_d_val (M : DifferentialGradedModule.{u, v, w} A) {p q : ℤ}
    (hpq : p + 1 = q) (x : M.toCochainComplex.X p) :
    ((M.toCochainComplex.d p q).hom x : M.grading q).val = M.d (x : M.grading p).val := by
  subst hpq
  rw [toCochainComplex_d]
  rfl

private theorem grading_val_zsmul (M : DifferentialGradedModule.{u, v, w} A) (p c : ℤ)
    (y : M.toCochainComplex.X p) :
    (c • y : M.grading p).val = c • (y : M.grading p).val := rfl

private theorem units_smul_hom_apply {X Y : ModuleCat.{w} R} (u : ℤˣ) (f : X ⟶ Y) (x : X) :
    (u • f).hom x = (u : ℤ) • f.hom x := rfl

private theorem shift_d_val_apply (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) (y : M.M) :
    (shift M n).d y = (n.negOnePow : ℤ) • M.d y := rfl

/-- The differential of the shifted cochain complex, read through the unshifted module. -/
private theorem shiftCochain_d_val (M : DifferentialGradedModule.{u, v, w} A) (n i : ℤ)
    (x : M.toCochainComplex.X (i + n)) :
    ((n.negOnePow • M.toCochainComplex.d (i + n) (i + 1 + n)).hom x :
        M.grading (i + 1 + n)).val
      = (n.negOnePow : ℤ) • M.d (x : M.grading (i + n)).val := by
  rw [units_smul_hom_apply, grading_val_zsmul,
    toCochainComplex_d_val A M (show (i + n) + 1 = i + 1 + n by omega)]

/-- The differential of the cochain complex of the shifted module, read through the unshifted
module. -/
private theorem dgShiftCochain_d_val (M : DifferentialGradedModule.{u, v, w} A) (n i : ℤ)
    (y : (shift M n).toCochainComplex.X i) :
    (((shift M n).toCochainComplex.d i (i + 1)).hom y : (shift M n).grading (i + 1)).val
      = (n.negOnePow : ℤ) • M.d (y : (shift M n).grading i).val := by
  rw [toCochainComplex_d_val A (shift M n) (show i + 1 = i + 1 from rfl), shift_d_val_apply]

/-- The underlying cochain complex of a shifted differential graded module is the shift of the
underlying cochain complex. -/
private noncomputable def shiftToCochainShiftIso (M : DifferentialGradedModule.{u, v, w} A)
    (n : ℤ) :
    (shift M n).toCochainComplex ≅
      (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) n).obj
        M.toCochainComplex := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => eqToIso (shiftToCochain_X_eq A M n i)) ?_
  intro i j hij
  simp only [ComplexShape.up_Rel] at hij
  subst j
  exact ModuleCat.hom_ext <| LinearMap.ext fun x => Subtype.ext <|
    (shiftCochain_d_val A M n i x).trans (dgShiftCochain_d_val A M n i x).symm

/-- Forgetting to cochain complexes commutes with the shift. -/
private noncomputable def shiftForgetNatIso (n : ℤ) :
    shiftFunctor A n ⋙ forgetToCochainComplex.{u, v, w} A ≅
      forgetToCochainComplex.{u, v, w} A ⋙
        CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) n :=
  NatIso.ofComponents (fun M => shiftToCochainShiftIso A M n) (by
    intro M N f
    ext i x
    rfl)

/-- Cohomology of the underlying cochain complex in degree `i`, as a functor on the homotopy
category. -/
private noncomputable def cohomologyLift (i : ℤ) :
    HomotopyCategory.{u, v, w} A ⥤ ModuleCat.{w} R :=
  CategoryTheory.Quotient.lift (homotopyRel.{u, v, w} A)
    (forgetToCochainComplex A ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) i)
    fun _ _ _ _ h => homologyMap_eq_of_homotopic h i

private theorem acyclic_iff_cohomologyLift (M : DifferentialGradedModule.{u, v, w} A) :
    M.toCochainComplex.Acyclic ↔
      ∀ i : ℤ, Limits.IsZero ((cohomologyLift.{u, v, w} A i).obj
        ((toHomotopyCategory A).obj M)) := by
  rw [HomologicalComplex.acyclic_iff]
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  constructor <;> intro h i <;>
    simpa only [cohomologyLift, CategoryTheory.Quotient.lift_obj_functor_obj,
      Functor.comp_obj, forgetToCochainComplex,
      HomologicalComplex.homologyFunctor_obj] using h i

/-- Degree-zero cohomology of the `i`-th shift, as a functor on differential graded modules, is
cohomology in degree `i`. -/
private noncomputable def cohomologyShiftFactorsIso (i : ℤ) :
    toHomotopyCategory.{u, v, w} A ⋙
        (CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) i ⋙
          degreeZeroCohomologyLift.{u, v, w} A) ≅
      forgetToCochainComplex.{u, v, w} A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) i := by
  let Q := toHomotopyCategory.{u, v, w} A
  let S := CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) i
  let S' := shiftFunctor A i
  let U := forgetToCochainComplex.{u, v, w} A
  let H := degreeZeroCohomologyLift.{u, v, w} A
  let H₀ := HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) 0
  let Sc := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) i
  exact (Functor.associator Q S H).symm ≪≫
    Functor.isoWhiskerRight (Q.commShiftIso i).symm H ≪≫
    Functor.associator S' Q H ≪≫
    Functor.isoWhiskerLeft S' (CategoryTheory.Quotient.lift.isLift _ _ _) ≪≫
    (Functor.associator S' U H₀).symm ≪≫
    Functor.isoWhiskerRight (shiftForgetNatIso A i) H₀ ≪≫
    Functor.associator U Sc H₀ ≪≫
    Functor.isoWhiskerLeft U (H₀.shiftIso i 0 i (by omega))

private theorem degreeZero_shift_isZero_iff (M : DifferentialGradedModule.{u, v, w} A) (i : ℤ) :
    Limits.IsZero ((degreeZeroCohomologyLift.{u, v, w} A).obj
        (((toHomotopyCategory A).obj M)⟦i⟧)) ↔
      Limits.IsZero ((cohomologyLift.{u, v, w} A i).obj ((toHomotopyCategory A).obj M)) :=
  Iso.isZero_iff ((cohomologyShiftFactorsIso A i).app M)

end Shift

/-! ### Degree-zero cohomology is a homological functor

A distinguished triangle of the homotopy category is isomorphic to a cone triangle, so its
rotation is isomorphic to the rotation of a cone triangle, whose first two morphisms are the cone
sequence `L → C(g) → K[1]`.  That sequence is degreewise the split short exact sequence of a
product, so the long exact cohomology sequence applies to it; its exactness in the middle is the
homological property.  Rotating is what makes the cone sequence available: the first two
morphisms of a cone triangle itself are `g` and the cone inclusion, which is not a short exact
sequence, while those of its rotation are.
-/

section Homological

open CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {K L : DifferentialGradedModule.{u, v, w} A}

/-- The cone sequence `L → C(g) → K[1]`, as a short complex of differential graded modules. -/
private noncomputable def coneShortComplex (g : K ⟶ L) :
    ShortComplex (DifferentialGradedModule.{u, v, w} A) :=
  ShortComplex.mk (coneIncl g) (coneProj g) (Hom.ext (LinearMap.ext fun _ => rfl))

/-- In each degree the cone sequence is the split short exact sequence of a product, so it stays
short exact after forgetting to cochain complexes over the base ring. -/
private theorem coneShortComplex_map_shortExact (g : K ⟶ L) :
    ((coneShortComplex A g).map (forgetToCochainComplex A)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    refine fun b => ⟨fun hb => ⟨⟨(b : (coneObject g).grading n).val.1,
      ((coneGrading_mem n (b : (coneObject g).grading n).val).mp
        (b : (coneObject g).grading n).2).1⟩,
      Subtype.ext (Prod.ext rfl (congrArg Subtype.val hb).symm)⟩, ?_⟩
    rintro ⟨a, rfl⟩
    rfl
  · rw [ModuleCat.mono_iff_injective]
    change Function.Injective ((coneIncl g).gradedMap n)
    exact fun x y hxy => Subtype.ext ((Prod.mk.injEq _ _ _ _).mp (congrArg Subtype.val hxy)).1
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective ((coneProj g).gradedMap n)
    intro z
    refine ⟨⟨((0 : L.M), (z : (shift K 1).grading n).val),
      (coneGrading_mem n _).mpr ⟨(L.grading n).zero_mem,
        (z : (shift K 1).grading n).2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Degree-zero cohomology on the homotopy category is additive: it becomes additive after
composition with the homotopy quotient, which is full and essentially surjective. -/
instance degreeZeroCohomologyLift_additive :
    (degreeZeroCohomologyLift.{u, v, w} A).Additive := by
  have : (toHomotopyCategory.{u, v, w} A ⋙ degreeZeroCohomologyLift.{u, v, w} A).Additive :=
    Functor.additive_of_iso (CategoryTheory.Quotient.lift.isLift _ _ _).symm
  exact Functor.additive_of_full_essSurj_comp (toHomotopyCategory.{u, v, w} A) _

private theorem exact_map_rotate_coneTriangle (g : K ⟶ L)
    (hT : (coneTriangle g).rotate ∈ distTriang (HomotopyCategory.{u, v, w} A)) :
    ((shortComplexOfDistTriangle ((coneTriangle g).rotate) hT).map
      (degreeZeroCohomologyLift.{u, v, w} A)).Exact := by
  have hS := coneShortComplex_map_shortExact A g
  have hLES := HomologicalComplex.HomologySequence.composableArrows₅_exact hS 0 1 (by simp)
  have hF : ((coneShortComplex A g).map (forgetToCochainComplex.{u, v, w} A ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) 0)).Exact := by
    change ((HomologicalComplex.HomologySequence.composableArrows₅ hS 0 1 (by simp)).sc
      hLES.toIsComplex 0 (by omega)).Exact
    exact hLES.exact 0
  have isoH : toHomotopyCategory.{u, v, w} A ⋙ degreeZeroCohomologyLift.{u, v, w} A ≅
      forgetToCochainComplex.{u, v, w} A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) 0 :=
    CategoryTheory.Quotient.lift.isLift _ _ _
  have hQH : ((coneShortComplex A g).map (toHomotopyCategory.{u, v, w} A ⋙
      degreeZeroCohomologyLift.{u, v, w} A)).Exact :=
    (ShortComplex.exact_iff_of_iso ((coneShortComplex A g).mapNatIso isoH)).2 hF
  have hQH' : (((coneShortComplex A g).map (toHomotopyCategory.{u, v, w} A)).map
      (degreeZeroCohomologyLift.{u, v, w} A)).Exact := hQH
  have e : (coneShortComplex A g).map (toHomotopyCategory.{u, v, w} A) ≅
      shortComplexOfDistTriangle ((coneTriangle g).rotate) hT :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (quotientShiftIso K 1)
      ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.id_comp _)
  exact (ShortComplex.exact_iff_of_iso
    ((degreeZeroCohomologyLift.{u, v, w} A).mapShortComplex.mapIso e)).1 hQH'

/-- **Stacks 09KW.** Degree-zero cohomology on the homotopy category of right differential graded
`A`-modules is a homological functor. -/
instance degreeZeroCohomologyLift_isHomological :
    (degreeZeroCohomologyLift.{u, v, w} A).IsHomological := by
  apply Functor.IsHomological.mk'
  intro T hT
  obtain ⟨K, L, g, ⟨e⟩⟩ := inv_rot_of_distTriang T hT
  refine ⟨(coneTriangle g).rotate,
    ((triangleRotation (HomotopyCategory.{u, v, w} A)).counitIso.app T).symm ≪≫
      (Pretriangulated.rotate (HomotopyCategory.{u, v, w} A)).mapIso e, ?_⟩
  exact exact_map_rotate_coneTriangle A g _

/-- The objects of the homotopy category killed by degree-zero cohomology in every shift are
exactly the acyclic ones. -/
theorem homologicalKernel_eq_acyclic :
    (degreeZeroCohomologyLift.{u, v, w} A).homologicalKernel = acyclic.{u, v, w} A := by
  ext X
  cases X with
  | mk M =>
    change (∀ i : ℤ, IsZero ((degreeZeroCohomologyLift.{u, v, w} A).obj
      (((toHomotopyCategory A).obj M)⟦i⟧))) ↔ M.toCochainComplex.Acyclic
    rw [acyclic_iff_cohomologyLift A M]
    exact forall_congr' (degreeZero_shift_isZero_iff A M)

/-- Acyclic differential graded modules form a triangulated subcategory of the homotopy category:
they are the objects killed by degree-zero cohomology in every shift, and degree-zero cohomology
is a homological functor. -/
@[stacks 09KW "triangulated subcategory"]
instance acyclic_isTriangulated : (acyclic.{u, v, w} A).IsTriangulated := by
  rw [← homologicalKernel_eq_acyclic A]
  exact (Functor.isTriangulated_and_isSaturated_homologicalKernel
    (degreeZeroCohomologyLift.{u, v, w} A)).1

/-- The triangulated subcategory of acyclic differential graded modules is saturated: the kernel of
a homological functor is stable under retracts, and a direct summand is a retract. -/
@[stacks 09KW "saturation of acyclic modules"]
instance acyclic_isSaturated : (acyclic.{u, v, w} A).IsSaturated := by
  rw [← homologicalKernel_eq_acyclic A]
  exact (Functor.isTriangulated_and_isSaturated_homologicalKernel
    (degreeZeroCohomologyLift.{u, v, w} A)).2

end Homological

/-! ### The multiplicative system attached to the acyclic modules

A morphism of the homotopy category has acyclic cone exactly when it is a quasi-isomorphism: by
the long exact cohomology sequence criterion the first condition says that every shift of the
morphism is inverted by degree-zero cohomology, and the comparison of the previous section turns
each of those into an isomorphism on cohomology in the corresponding degree.
-/

section MultiplicativeSystem

open CategoryTheory.Limits CategoryTheory.Pretriangulated

/-- The morphisms of the homotopy category whose cone is acyclic are exactly the
quasi-isomorphisms. -/
@[stacks 09KW "associated multiplicative system"]
theorem acyclic_trW_eq_quasiIsomorphisms :
    (acyclic.{u, v, w} A).trW = quasiIsomorphisms.{u, v, w} A := by
  rw [← homologicalKernel_eq_acyclic A]
  let _ : (degreeZeroCohomologyLift.{u, v, w} A).ShiftSequence ℤ :=
    Functor.ShiftSequence.tautological _ ℤ
  ext X Y f
  cases X with
  | mk M =>
    cases Y with
    | mk N =>
      induction f using Quot.inductionOn with
      | _ g =>
        change (degreeZeroCohomologyLift.{u, v, w} A).homologicalKernel.trW
            ((toHomotopyCategory A).map g) ↔
          quasiIsomorphisms A ((toHomotopyCategory A).map g)
        rw [quasiIsomorphisms_map_iff,
          (degreeZeroCohomologyLift.{u, v, w} A).mem_homologicalKernel_trW_iff, quasiIso_iff]
        refine forall_congr' fun i => ?_
        exact (NatIso.isIso_map_iff (cohomologyShiftFactorsIso A i) g).trans
          (quasiIsoAt_iff_isIso_homologyMap _ i).symm

end MultiplicativeSystem

/-! ### Saturation, and the kernel of the localization

The homotopy category of right differential graded `A`-modules is triangulated, and that is what
makes the Verdier correspondence between triangulated subcategories and multiplicative systems
usable here.  Two consequences of it are recorded.  First, the multiplicative system attached to
the kernel of a homological functor is saturated, so the quasi-isomorphisms are a saturated
multiplicative system.  Second, a strictly full saturated triangulated subcategory is recovered as
the class of objects killed by the localization at its own multiplicative system, so the objects
killed by the localization at the quasi-isomorphisms are exactly the acyclic modules.
-/

section Saturation

open CategoryTheory.Limits CategoryTheory.Pretriangulated

/-- The quasi-isomorphisms of the homotopy category of right differential graded `A`-modules form
a saturated multiplicative system: they are the morphisms whose cone lies in the kernel of
degree-zero cohomology, and the multiplicative system attached to the kernel of a homological
functor on a triangulated category is saturated. -/
@[stacks 09KW "saturated multiplicative system"]
theorem quasiIsomorphisms_isSaturated : (quasiIsomorphisms.{u, v, w} A).IsSaturated := by
  rw [← acyclic_trW_eq_quasiIsomorphisms A, ← homologicalKernel_eq_acyclic A]
  exact (Functor.isSaturated_homologicalKernel_and_mem_trW_iff_and_exists_lift
    (degreeZeroCohomologyLift.{u, v, w} A)
    (degreeZeroCohomologyLift.{u, v, w} A).homologicalKernel.trW.Q).2.1.1

/-- The objects of the homotopy category annihilated by the localization at the
quasi-isomorphisms are exactly the acyclic differential graded modules: the acyclic modules are a
strictly full saturated triangulated subcategory, and such a subcategory is the kernel of the
localization at the multiplicative system it determines. -/
@[stacks 09KW "kernel of localization"]
theorem localization_kernel_eq_acyclic :
    ((quasiIsomorphisms.{u, v, w} A).Q).kernel = acyclic.{u, v, w} A := by
  rw [← acyclic_trW_eq_quasiIsomorphisms A]
  exact ObjectProperty.isLeast_trW_kernel_and_kernel_eq_self.2
    (acyclic.{u, v, w} A) (acyclic.{u, v, w} A).trW.Q

end Saturation

end DifferentialGradedModule

end
