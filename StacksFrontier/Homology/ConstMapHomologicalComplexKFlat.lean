module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import StacksFrontier.Homology.ConstMapHomologicalComplexMonoidal
public import StacksFrontier.Homology.KFlat.Bifunctor

/-!
# Constant diagrams of complexes are K-flat

Let `J` be a category and `D` a monoidal abelian category whose tensor product commutes with the
coproducts occurring in a total complex, so that both `CochainComplex D ℤ` and
`CochainComplex (J ⥤ D) ℤ` carry the total tensor product of `Mathlib.Algebra.Homology.Monoidal`
(the latter by `StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits`).  This file
proves that

  `(Functor.const J).mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex D ℤ ⥤ CochainComplex (J ⥤ D) ℤ`

carries K-flat complexes to K-flat complexes, for the K-flatness of
`StacksFrontier.Homology.KFlat.Bifunctor` taken at the total tensor product on each side.

The argument is pointwise.  Evaluation at an object of `J` is strong monoidal for the pointwise
monoidal structure on `J ⥤ D` — strictly so, both its tensorator and its unit comparison being
identities — hence acts monoidally on complexes by
`CategoryTheory.Functor.mapHomologicalComplexMonoidal`, so it carries a total tensor product of
complexes of diagrams to the total tensor product of the evaluations.  It is also exact, and the
evaluations jointly reflect isomorphisms, so acyclicity of a complex of diagrams is exactly
acyclicity of all its evaluations.  Since evaluating a constant diagram gives back what it was
constant at, K-flatness of `K` in `CochainComplex D ℤ` therefore gives K-flatness of the constant
diagram at `K`.

## Main definitions

* `CategoryTheory.Functor.evaluationCoreMonoidal` and
  `CategoryTheory.Functor.evaluationMonoidal`: **evaluation at an object of `J` is a monoidal
  functor** `(J ⥤ D) ⥤ D` for the pointwise monoidal structure.  Mathlib has the pointwise
  monoidal structure (`CategoryTheory.Monoidal.functorCategoryMonoidal`) but records no monoidal
  functor structure on evaluation.
* `CategoryTheory.Functor.evaluationMapHomologicalComplexMonoidal`: evaluation acts monoidally
  on homological complexes.

## Main results

* `CategoryTheory.Functor.evaluation_jointlyReflectIsomorphisms`: the evaluation functors of a
  functor category jointly reflect isomorphisms.
* `HomologicalComplex.acyclic_iff_forall_evaluation`: **a complex of diagrams is acyclic exactly
  when all of its evaluations are.**
* `CochainComplex.KFlatBifunctor.kFlat_constMapHomologicalComplex`: **the constant diagram at a
  K-flat complex is K-flat.**

## Implementation notes

`Functor.const J ⋙ (evaluation J D).obj k` is *definitionally* `𝟭 D`, and consequently
`((evaluation J D).obj k).mapHomologicalComplex c` applied to a constant diagram of complexes
returns the complex it was constant at, by `rfl`.  That is what keeps the main proof free of any
transport: the only isomorphism used is the tensorator of the evaluation acting on complexes.

The statement proved here is the missing input identified in the implementation notes of
`StacksFrontier.Homology.ConstMapHomologicalComplexMonoidal`, namely the mathematical statement
about K-flatness in a functor category which the second of the two localization descents of
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` requires.  It is *not* by itself
enough for that descent: the K-flat localization also needs K-flat resolutions to exist in
`CochainComplex (J ⥤ D) ℤ`, and no such existence statement is available for a functor category
in this repository — every K-flat resolution theorem here is specialized either to
`CochainComplex (ModuleCat R) ℤ` (`CochainComplex.KFlat.exists_kFlat_resolution`, Tag 06Y4) or
to complexes of sheaves of modules on a ringed site
(`Stacks.SheafOfModules.exists_kFlat_quasiIso`, Tag 06YS), and there is no transport of
K-flat-resolution existence along an equivalence of categories.  So nothing about the derived
category is claimed here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v₁ u₁ v₂ u₂ u

namespace CategoryTheory

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D]

/-- **The evaluation functors of a functor category jointly reflect isomorphisms**: a natural
transformation all of whose components are isomorphisms is one. -/
theorem Functor.evaluation_jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms (fun k : J => (evaluation J D).obj k) where
  isIso f h :=
    have : ∀ k : J, IsIso (f.app k) := h
    NatIso.isIso_of_isIso_app f

section Monoidal

variable [MonoidalCategory D]

/-- **Evaluation at an object of `J` is strictly monoidal** for the pointwise monoidal structure
on `J ⥤ D`: the tensor product of `J ⥤ D` is objectwise and its unit is the constant diagram at
the unit of `D`, so both the unit comparison and the tensorator are identities. -/
def Functor.evaluationCoreMonoidal (k : J) : ((evaluation J D).obj k).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left _ _ := by simp
  μIso_hom_natural_right _ _ := by simp
  associativity _ _ _ := by simp
  left_unitality _ := by simp
  right_unitality _ := by simp

/-- **Evaluation at an object of `J` is a monoidal functor** `(J ⥤ D) ⥤ D` for the pointwise
monoidal structure on the functor category. -/
instance Functor.evaluationMonoidal (k : J) : ((evaluation J D).obj k).Monoidal :=
  (Functor.evaluationCoreMonoidal k).toMonoidal

/-- The tensorator of evaluation at `k` is the identity of `F.obj k ⊗ G.obj k`. -/
@[simp]
lemma Functor.evaluationMonoidal_μ_app (k : J) (F G : J ⥤ D) :
    Functor.LaxMonoidal.μ ((evaluation J D).obj k) F G = 𝟙 (F.obj k ⊗ G.obj k) :=
  rfl

/-- The unit comparison of evaluation at `k` is the identity of `𝟙_ D`. -/
@[simp]
lemma Functor.evaluationMonoidal_ε_app (k : J) :
    Functor.LaxMonoidal.ε ((evaluation J D).obj k) = 𝟙 (𝟙_ D) :=
  rfl

/-- The oplax tensorator of evaluation at `k` is the identity of `F.obj k ⊗ G.obj k`. -/
@[simp]
lemma Functor.evaluationMonoidal_δ_app (k : J) (F G : J ⥤ D) :
    Functor.OplaxMonoidal.δ ((evaluation J D).obj k) F G = 𝟙 (F.obj k ⊗ G.obj k) :=
  rfl

/-- The oplax unit comparison of evaluation at `k` is the identity of `𝟙_ D`. -/
@[simp]
lemma Functor.evaluationMonoidal_η_app (k : J) :
    Functor.OplaxMonoidal.η ((evaluation J D).obj k) = 𝟙 (𝟙_ D) :=
  rfl

end Monoidal

end CategoryTheory

/-! ### Acyclicity of a complex of diagrams -/

namespace HomologicalComplex

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {I : Type*} {c : ComplexShape I}

/-- **A complex of diagrams is acyclic exactly when all of its evaluations are acyclic.**
Evaluation is exact and the evaluations jointly reflect isomorphisms, so
`CategoryTheory.JointlyReflectIsomorphisms.exactAt_iff` applies in each degree. -/
theorem acyclic_iff_forall_evaluation (G : HomologicalComplex (J ⥤ D) c) :
    G.Acyclic ↔
      ∀ k : J, ((((evaluation J D).obj k).mapHomologicalComplex c).obj G).Acyclic := by
  have h := CategoryTheory.Functor.evaluation_jointlyReflectIsomorphisms (J := J) (D := D)
  exact ⟨fun hG k n => ((h.exactAt_iff G n).1 (hG n) k),
    fun hk n => (h.exactAt_iff G n).2 fun k => hk k n⟩

end HomologicalComplex

/-! ### K-flatness of a constant diagram of complexes -/

namespace CochainComplex.KFlatBifunctor

open CategoryTheory.Functor

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCoproducts.{0} D] [HasColimitsOfSize.{0, 0} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]

/-- **Evaluation acts monoidally on homological complexes.**  This is
`CategoryTheory.Functor.mapHomologicalComplexMonoidal` applied to the strong monoidal functor
`CategoryTheory.Functor.evaluationMonoidal`; the graded-object conditions it requires for the
functor category `J ⥤ D` are supplied by
`StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits`, and evaluation preserves
every colimit a functor category has. -/
@[instance_reducible]
def _root_.CategoryTheory.Functor.evaluationMapHomologicalComplexMonoidal (k : J) :
    ((((evaluation J D).obj k)).mapHomologicalComplex (ComplexShape.up ℤ)).Monoidal :=
  inferInstance

omit [HasColimitsOfSize.{0, 0} D] in
/-- **The constant diagram at a K-flat complex is K-flat.**

If `K : CochainComplex D ℤ` is K-flat for the total tensor product of `CochainComplex D ℤ`, then
the constant diagram at `K` is K-flat for the total tensor product of
`CochainComplex (J ⥤ D) ℤ`.

Both acyclicity and the total tensor product of a complex of diagrams are detected by evaluating
at the objects of `J`: `HomologicalComplex.acyclic_iff_forall_evaluation` for the first, and the
tensorator of `CategoryTheory.Functor.evaluationMapHomologicalComplexMonoidal` for the second.
Evaluating the constant diagram at `K` returns `K`, so each evaluation of
`G ⊗ (constant diagram at K)` is `(evaluation of G) ⊗ K`, acyclic because `K` is K-flat. -/
theorem kFlat_constMapHomologicalComplex (K : CochainComplex D ℤ)
    (hK : KFlat (curriedTensor D) K) :
    KFlat (curriedTensor (J ⥤ D))
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  intro G hG
  rw [show totalComplex (curriedTensor (J ⥤ D)) G
        (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      G ⊗ ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K from
      rfl, HomologicalComplex.acyclic_iff_forall_evaluation]
  intro k n
  exact HomologicalComplex.ExactAt.of_iso
    (hK ((((evaluation J D).obj k).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
      ((HomologicalComplex.acyclic_iff_forall_evaluation G).1 hG k) n)
    (Functor.Monoidal.μIso (((evaluation J D).obj k).mapHomologicalComplex (ComplexShape.up ℤ))
      G (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

end CochainComplex.KFlatBifunctor

end
