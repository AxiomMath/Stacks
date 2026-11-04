module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryComp
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryHomotopyCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.RepresentableFunctor

/-!
# The representable differential graded module functor

Let `A` be a differential graded category over a commutative ring `R` and let `x` be an object of
`A`. The endomorphisms of `x` form a differential graded `R`-algebra `End(x)`, composition makes
every `Hom(x, y)` a right differential graded `End(x)`-module, and `y ↦ Hom(x, y)` is a functor of
differential graded categories. It therefore induces ordinary functors on closed degree-zero
morphisms and on homotopy classes, with values in the differential graded `End(x)`-modules and in
their homotopy category.

## Main definitions

* `DGCategory.HomRepresentation`: all of this data, together with the identifications that pin it
  down: degreewise linear equivalences of the algebra and of the modules with the original Hom
  groups, under which the multiplication, the right action and the functorial map are
  composition.
* `DGCategory.homRepresentation`: the construction of this data for any `A` and `x`.

## Implementation notes

The algebra and the modules are characterised by degreewise linear equivalences to the Hom groups
of `A` rather than by a chosen total-space presentation, so that a client never has to unfold the
direct sums. The multiplicative conditions are phrased as the existence of a homogeneous element
with a prescribed underlying value, which is how one avoids transporting along the
non-definitional arithmetic of the grading group.

The induced ordinary functors are the canonical `DGCategory.DGFunctor.onComp` and
`DGCategory.DGFunctor.onK` of Tag 09L8, composed with the comparisons of Tag 09LC between the
category of complexes (resp. the homotopy category) of the differential graded category of
differential graded modules and the category of differential graded modules (resp. its homotopy
category).

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe w v u

variable {R : Type u} [CommRing R] (A : DGCategory.{w, v, u} R) (x : A.Obj)

/-- The canonical representable differential graded module functor `Hom(x, -)`, together with the
identifications that specify its endomorphism algebra and its action on objects and homogeneous
morphisms. -/
structure HomRepresentation where
  /-- The endomorphism differential graded algebra of `x`. -/
  algebra : DifferentialGradedAlgebra.{u, w} R
  /-- The functor of differential graded categories `Hom(x, -)`. -/
  functor : DGCategory.DGFunctor A (DifferentialGradedModule.dgCategory.{u, w, w} algebra)
  /-- The degree-`n` part of the algebra is the degree-`n` endomorphisms of `x`. -/
  algebraHom : ∀ n : ℤ, algebra.grading n ≃ₗ[R] A.Hom x x n
  /-- The degree-`n` part of `Hom(x, y)` is the degree-`n` morphisms `x ⟶ y`. -/
  moduleHom : ∀ (y : A.Obj) (n : ℤ), (functor.obj y).grading n ≃ₗ[R] A.Hom x y n
  /-- The differential of the algebra is the differential of `A`. -/
  algebra_d : ∀ (n : ℤ) (a : algebra.grading n),
    algebraHom (n + 1) ⟨algebra.d a, algebra.d_mem n a a.property⟩ = A.d (algebraHom n a)
  /-- The differential of each module is the differential of `A`. -/
  module_d : ∀ (y : A.Obj) (n : ℤ) (a : (functor.obj y).grading n),
    moduleHom y (n + 1) ⟨(functor.obj y).d a, (functor.obj y).d_mem n a a.property⟩ =
      A.d (moduleHom y n a)
  /-- Multiplication in the algebra is composition in `A`. -/
  algebra_mul : ∀ (m n k : ℤ) (h : m + n = k)
      (a : algebra.grading m) (b : algebra.grading n),
    ∃ c : algebra.grading k,
      (c.1 = (a.1 * b.1)) ∧ (algebraHom k c = A.comp h (algebraHom m a) (algebraHom n b))
  /-- The unit of the algebra is the identity of `x`. -/
  algebra_one : ∃ e : algebra.grading 0, (e.1 = 1) ∧ (algebraHom 0 e = A.id x)
  /-- The right action on each module is composition in `A`. -/
  module_action : ∀ (y : A.Obj) (m n k : ℤ) (h : m + n = k)
      (a : (functor.obj y).grading m) (b : algebra.grading n),
    ∃ c : (functor.obj y).grading k,
      (c.1 = MulOpposite.op (b.1) • a.1) ∧
        (moduleHom y k c = A.comp h (moduleHom y m a) (algebraHom n b))
  /-- The functorial map is composition in `A`. -/
  map_comp : ∀ (y z : A.Obj) (m n k : ℤ) (h : m + n = k)
      (f : A.Hom y z m) (a : (functor.obj y).grading n),
    ∃ c : (functor.obj z).grading k,
      (c.1 = (functor.map f).1 a.1) ∧ (moduleHom z k c = A.comp h f (moduleHom y n a))
  /-- The induced functor on closed degree-zero morphisms. -/
  complexesFunctor : A.Comp ⥤ DifferentialGradedModule.{u, w, w} algebra
  /-- The induced functor on closed degree-zero morphisms is the canonical one. -/
  complexesFunctor_eq : complexesFunctor =
    functor.onComp ⋙ (DifferentialGradedModule.dgCategoryCompEquivalence algebra).1.functor
  /-- The induced functor on homotopy classes. -/
  homotopyFunctor : A.K ⥤ DifferentialGradedModule.HomotopyCategory.{u, w, w} algebra
  /-- The induced functor on homotopy classes is the canonical one. -/
  homotopyFunctor_eq : homotopyFunctor =
    functor.onK ⋙ (DifferentialGradedModule.homotopyCategoryEquivalence algebra).inverse

/-- The endomorphism differential graded algebra and representable differential graded functor
`Hom(x, -)` of an object `x` of a differential graded category, with the induced functors on the
category of complexes and on the homotopy category. -/
@[stacks 09LE]
noncomputable def homRepresentation : HomRepresentation A x := by
  classical
  refine {
    algebra := endAlgebra A x
    functor := representableDGFunctor A x
    algebraHom := fun n => DirectSum.rangeGradingEquiv R (endFamily A x) n
    moduleHom := fun y n => DirectSum.rangeGradingEquiv R (repFamily A x y) n
    algebra_d := ?_
    module_d := ?_
    algebra_mul := ?_
    algebra_one := ?_
    module_action := ?_
    map_comp := ?_
    complexesFunctor := (representableDGFunctor A x).onComp ⋙
      (DifferentialGradedModule.dgCategoryCompEquivalence (endAlgebra A x)).1.functor
    complexesFunctor_eq := rfl
    homotopyFunctor := (representableDGFunctor A x).onK ⋙
      (DifferentialGradedModule.homotopyCategoryEquivalence (endAlgebra A x)).inverse
    homotopyFunctor_eq := rfl }
  · intro n a
    obtain ⟨f, hf⟩ := (DirectSum.mem_rangeGrading R (endFamily A x) n a.1).mp a.2
    have h₁ : DirectSum.rangeGradingEquiv R (endFamily A x) n a = f :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (endFamily A x) (i := n) a f hf
    have hmem : endDifferential A x a.1 ∈ DirectSum.rangeGrading R (endFamily A x) (n + 1) := by
      rw [hf, endDifferential_of]
      exact ⟨A.d f, DirectSum.lof_eq_of R ℤ (endFamily A x) (n + 1) (A.d f)⟩
    have h₂ : DirectSum.rangeGradingEquiv R (endFamily A x) (n + 1)
        ⟨endDifferential A x a.1, hmem⟩ = A.d f :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (endFamily A x) (i := n + 1) _ (A.d f)
        (by change endDifferential A x a.1 = _; rw [hf, endDifferential_of])
    exact h₂.trans (congrArg A.d h₁.symm)
  · intro y n a
    obtain ⟨f, hf⟩ := (DirectSum.mem_rangeGrading R (repFamily A x y) n a.1).mp a.2
    have h₁ : DirectSum.rangeGradingEquiv R (repFamily A x y) n a = f :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (repFamily A x y) (i := n) a f hf
    have hmem : repDifferential A x y a.1 ∈
        DirectSum.rangeGrading R (repFamily A x y) (n + 1) := by
      rw [hf, repDifferential_of]
      exact ⟨A.d f, DirectSum.lof_eq_of R ℤ (repFamily A x y) (n + 1) (A.d f)⟩
    have h₂ : DirectSum.rangeGradingEquiv R (repFamily A x y) (n + 1)
        ⟨repDifferential A x y a.1, hmem⟩ = A.d f :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (repFamily A x y) (i := n + 1) _ (A.d f)
        (by change repDifferential A x y a.1 = _; rw [hf, repDifferential_of])
    exact h₂.trans (congrArg A.d h₁.symm)
  · intro m n k h a b
    obtain ⟨f, hf⟩ := (DirectSum.mem_rangeGrading R (endFamily A x) m a.1).mp a.2
    obtain ⟨g, hg⟩ := (DirectSum.mem_rangeGrading R (endFamily A x) n b.1).mp b.2
    have hmem : DirectSum.of (endFamily A x) k (A.comp h f g) ∈
        DirectSum.rangeGrading R (endFamily A x) k :=
      ⟨A.comp h f g, DirectSum.lof_eq_of R ℤ (endFamily A x) k (A.comp h f g)⟩
    have hval : DirectSum.of (endFamily A x) k (A.comp h f g) =
        DirectSum.of (endFamily A x) m f * DirectSum.of (endFamily A x) n g := by
      rw [endTotal_of_mul_of]
      exact DirectSum.of_eq_of_heq (show k = m + n by omega)
        (comp_heq (show m + n = k by omega) f g).symm
    have ha : DirectSum.rangeGradingEquiv R (endFamily A x) m a = f :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (endFamily A x) (i := m) a f hf
    have hb : DirectSum.rangeGradingEquiv R (endFamily A x) n b = g :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (endFamily A x) (i := n) b g hg
    have hc : DirectSum.rangeGradingEquiv R (endFamily A x) k
        ⟨DirectSum.of (endFamily A x) k (A.comp h f g), hmem⟩ = A.comp h f g :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (endFamily A x) (i := k) _ (A.comp h f g) rfl
    have hcomp : A.comp h f g =
        A.comp h (DirectSum.rangeGradingEquiv R (endFamily A x) m a)
          (DirectSum.rangeGradingEquiv R (endFamily A x) n b) := by rw [ha, hb]
    refine ⟨⟨DirectSum.of (endFamily A x) k (A.comp h f g), hmem⟩, ?_, hc.trans hcomp⟩
    rw [hf, hg]
    exact hval
  · have hmem : DirectSum.of (endFamily A x) 0 (A.id x) ∈
        DirectSum.rangeGrading R (endFamily A x) 0 :=
      ⟨A.id x, DirectSum.lof_eq_of R ℤ (endFamily A x) 0 (A.id x)⟩
    exact ⟨⟨DirectSum.of (endFamily A x) 0 (A.id x), hmem⟩, (endTotal_one_eq A x).symm,
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (endFamily A x) (i := 0) _ (A.id x) rfl⟩
  · intro y m n k h a b
    obtain ⟨f, hf⟩ := (DirectSum.mem_rangeGrading R (repFamily A x y) m a.1).mp a.2
    obtain ⟨g, hg⟩ := (DirectSum.mem_rangeGrading R (endFamily A x) n b.1).mp b.2
    have hmem : DirectSum.of (repFamily A x y) k (A.comp h f g) ∈
        DirectSum.rangeGrading R (repFamily A x y) k :=
      ⟨A.comp h f g, DirectSum.lof_eq_of R ℤ (repFamily A x y) k (A.comp h f g)⟩
    have hval : DirectSum.of (repFamily A x y) k (A.comp h f g) =
        repActionLinear A x y (DirectSum.of (endFamily A x) n g)
          (DirectSum.of (repFamily A x y) m f) := by
      rw [repActionLinear_of]
      exact DirectSum.of_eq_of_heq (show k = m + n by omega)
        (comp_heq (show m + n = k by omega) f g).symm
    have ha : DirectSum.rangeGradingEquiv R (repFamily A x y) m a = f :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (repFamily A x y) (i := m) a f hf
    have hb : DirectSum.rangeGradingEquiv R (endFamily A x) n b = g :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (endFamily A x) (i := n) b g hg
    have hc : DirectSum.rangeGradingEquiv R (repFamily A x y) k
        ⟨DirectSum.of (repFamily A x y) k (A.comp h f g), hmem⟩ = A.comp h f g :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (repFamily A x y) (i := k) _ (A.comp h f g) rfl
    have hcomp : A.comp h f g =
        A.comp h (DirectSum.rangeGradingEquiv R (repFamily A x y) m a)
          (DirectSum.rangeGradingEquiv R (endFamily A x) n b) := by rw [ha, hb]
    refine ⟨⟨DirectSum.of (repFamily A x y) k (A.comp h f g), hmem⟩, ?_, hc.trans hcomp⟩
    change DirectSum.of (repFamily A x y) k (A.comp h f g) = repActionLinear A x y b.1 a.1
    rw [hf, hg]
    exact hval
  · intro y z m n k h f a
    obtain ⟨g, hg⟩ := (DirectSum.mem_rangeGrading R (repFamily A x y) n a.1).mp a.2
    have hmem : DirectSum.of (repFamily A x z) k (A.comp h f g) ∈
        DirectSum.rangeGrading R (repFamily A x z) k :=
      ⟨A.comp h f g, DirectSum.lof_eq_of R ℤ (repFamily A x z) k (A.comp h f g)⟩
    have hval : DirectSum.of (repFamily A x z) k (A.comp h f g) =
        repPostcomp A x f (DirectSum.of (repFamily A x y) n g) := by
      rw [repPostcomp_of]
      exact DirectSum.of_eq_of_heq (show k = m + n by omega)
        (comp_heq (show m + n = k by omega) f g).symm
    have ha : DirectSum.rangeGradingEquiv R (repFamily A x y) n a = g :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (repFamily A x y) (i := n) a g hg
    have hc : DirectSum.rangeGradingEquiv R (repFamily A x z) k
        ⟨DirectSum.of (repFamily A x z) k (A.comp h f g), hmem⟩ = A.comp h f g :=
      DirectSum.rangeGradingEquiv_eq_of_coe_eq R (repFamily A x z) (i := k) _ (A.comp h f g) rfl
    have hcomp : A.comp h f g =
        A.comp h f (DirectSum.rangeGradingEquiv R (repFamily A x y) n a) := by rw [ha]
    refine ⟨⟨DirectSum.of (repFamily A x z) k (A.comp h f g), hmem⟩, ?_, hc.trans hcomp⟩
    change DirectSum.of (repFamily A x z) k (A.comp h f g) = repPostcomp A x f a.1
    rw [hg]
    exact hval

/-! ### Where the base ring sits

The endomorphism differential graded algebra of an object of a differential graded category over
`R` is an `R`-algebra, so the base ring maps into it. The two lemmas below say *where*: in degree
zero, as the scalar multiples of the identity of the object, and — on a differential graded module
over it — as the right action of that image.
-/

namespace HomRepresentation

variable {A} {x} (H : HomRepresentation A x)

/-- The image of the base ring lies in degree zero of the endomorphism algebra: it consists of the
scalar multiples of the unit, which is homogeneous of degree zero. -/
lemma algebraMap_mem_grading_zero (r : R) :
    algebraMap R H.algebra.A r ∈ H.algebra.grading 0 := by
  obtain ⟨e, he, -⟩ := H.algebra_one
  have hr : algebraMap R H.algebra.A r = r • (e : H.algebra.A) := by
    rw [he, Algebra.algebraMap_eq_smul_one]
  rw [hr]
  exact (H.algebra.grading 0).smul_mem r e.property

/-- Under the identification `DGCategory.HomRepresentation.algebraHom` of degree-zero elements of
the endomorphism algebra with degree-zero endomorphisms of the object, the image of `r : R` is `r`
times the identity. -/
lemma algebraHom_algebraMap (r : R) :
    H.algebraHom 0 ⟨algebraMap R H.algebra.A r, H.algebraMap_mem_grading_zero r⟩ =
      r • A.id x := by
  obtain ⟨e, he, hid⟩ := H.algebra_one
  have hsub : (⟨algebraMap R H.algebra.A r, H.algebraMap_mem_grading_zero r⟩ :
      H.algebra.grading 0) = r • e :=
    Subtype.ext (by rw [Submodule.coe_smul, he]; exact Algebra.algebraMap_eq_smul_one r)
  rw [hsub, map_smul, hid]

end HomRepresentation

end DGCategory

/-- On a differential graded module, the right action of the image of `r : R` in the algebra is the
action of `r`. -/
lemma DifferentialGradedModule.op_algebraMap_smul {R : Type*} [CommRing R]
    {A : DifferentialGradedAlgebra R} (M : DifferentialGradedModule A) (r : R) (m : M.M) :
    MulOpposite.op (algebraMap R A.A r) • m = r • m := by
  rw [Algebra.algebraMap_eq_smul_one, MulOpposite.op_smul, MulOpposite.op_one]
  exact smul_one_smul (MulOpposite A.A) r m
