module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCohomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedZerothCohomology

/-!
# Zeroth cohomology on the homotopy category is a homological functor

Let `(C, O)` be a ringed site and let `A` be a sheaf of differential graded `O`-algebras. Zeroth
cohomology descends from right differential graded `A`-modules to their homotopy category
`K(Mod(A, d))`; this file proves that the descended functor is *homological*: it takes a
distinguished triangle of `K(Mod(A, d))` to an exact sequence of sheaves of `O`-modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.zerothCohomologyFunctor_isHomological`:
  zeroth cohomology on the homotopy category is homological, in the sense of
  `CategoryTheory.Functor.IsHomological`.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.zerothCohomologyFunctor_additive`:
  zeroth cohomology on the homotopy category is additive.

## Implementation notes

The pre-triangulated structure on `K(Mod(A, d))` is
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.instPretriangulated`, which exists over
a ringed site `X`, so the base here is `X.ringSheaf`.

By `SheafOfModules.DifferentialGradedModule.HomotopyCategory.distinguished_iff`, a distinguished
triangle of `K(Mod(A, d))` is isomorphic to the triangle of an admissible short exact sequence
`M → N → P` of right differential graded modules, one carrying a chosen splitting
`DGCategory.GradedSplitShortExact` in the underlying graded category. Transported to the
underlying complexes, the splitting exhibits `M^• → N^• → P^•` as a degreewise split short exact
sequence of cochain complexes, and exactness at `H⁰` is
`CategoryTheory.ShortComplex.ShortExact.homology_exact₂` in degree `0`.

The degree-`n` `Hom` type of the differential graded category is only equal to the type of
action-linear cochains, by the field
`SheafOfModules.DifferentialGradedModule.DGCategoryData.homs`, so passing to the underlying
cochain is a cast, `moduleCochain`. Its compatibility with composition, the differential, the
identity and addition are fields of `DGCategoryData`.

## References

* [Stacks Project, Tag 0FT2](https://stacks.math.columbia.edu/tag/0FT2)
* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
* [Stacks Project, Tag 0FRK](https://stacks.math.columbia.edu/tag/0FRK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.HomComplex

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-! ### The cochain underlying a homogeneous morphism

The degree-`n` `Hom` type of the differential graded category of right differential graded
modules is *equal* to the type of action-linear cochains of degree `n`, so passing to the
underlying cochain is a cast. These lemmas record that the cast commutes with composition, the
identity, zero and addition.
-/

/-- The cochain of sheaves of modules underlying a homogeneous morphism of the differential
graded category of right differential graded modules. -/
private noncomputable abbrev moduleCochain {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f : (dgCategoryData.{u, v, w} A).category.Hom (asObject A M) (asObject A N) n) :
    Cochain M.complex N.complex n :=
  (Equiv.cast ((dgCategoryData.{u, v, w} A).homs M N n) f).val

/-- A homogeneous morphism is determined by its underlying cochain. -/
private theorem moduleCochain_injective {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ} :
    Function.Injective (moduleCochain.{u, v, w} A (M := M) (N := N) (n := n)) :=
  underlyingCochain_injective A _

/-- The cochain of a composite is the composite of the cochains. -/
private theorem moduleCochain_comp {M N P : DifferentialGradedModule.{u, v, w} A} {m n k : ℤ}
    (h : m + n = k)
    (g : (dgCategoryData.{u, v, w} A).category.Hom (asObject A N) (asObject A P) m)
    (f : (dgCategoryData.{u, v, w} A).category.Hom (asObject A M) (asObject A N) n) :
    moduleCochain A ((dgCategoryData.{u, v, w} A).category.comp h g f) =
      (moduleCochain A f).comp (moduleCochain A g) (by omega) :=
  underlyingCochain_comp A _ h g f

/-- The cochain of an identity is the identity cochain. -/
private theorem moduleCochain_id (M : DifferentialGradedModule.{u, v, w} A) :
    moduleCochain.{u, v, w} A ((dgCategoryData.{u, v, w} A).category.id (asObject A M)) =
      Cochain.ofHom (𝟙 M.complex) :=
  underlyingCochain_id A _ M

/-- The cochain of a zero homogeneous morphism is zero. -/
private theorem moduleCochain_zero (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    moduleCochain.{u, v, w} A (0 : (dgCategoryData.{u, v, w} A).category.Hom
      (asObject A M) (asObject A N) n) = 0 :=
  underlyingCochain_zero A _ M N n

/-- Passing to underlying cochains is additive. -/
private theorem moduleCochain_add {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (f g : (dgCategoryData.{u, v, w} A).category.Hom (asObject A M) (asObject A N) k) :
    moduleCochain A (f + g) = moduleCochain A f + moduleCochain A g :=
  underlyingCochain_add A _ f g

/-- The cochain of the cocycle attached to a morphism of right differential graded modules is
that morphism, read on the underlying complexes. -/
private theorem moduleCochain_cocycleOfHom {M N : DifferentialGradedModule.{u, v, w} A}
    (f : M ⟶ N) :
    moduleCochain.{u, v, w} A (cocycleOfHom A (dgCategoryData.{u, v, w} A) f).1 =
      Cochain.ofHom f.toHomologicalComplex :=
  congrArg Subtype.val
    ((Equiv.cast ((dgCategoryData.{u, v, w} A).homs M N 0)).apply_symm_apply _)

/-! ### The underlying degreewise split short exact sequence

An admissible short exact sequence of right differential graded modules has a chosen splitting
in the underlying graded category. Transported to cochains, it splits the underlying sequence of
complexes of sheaves of modules in every degree.
-/

section Split

variable {M N P : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) (g : N ⟶ P)
  (E : DGCategory.GradedSplitShortExact (A := (dgCategoryData.{u, v, w} A).category)
    (asObject A M) (asObject A N) (asObject A P))

include E

/-- The chosen splitting retracts the first morphism in every degree. -/
private theorem split_f_r (hf : cocycleOfHom A (dgCategoryData A) f = E.a) (p : ℤ) :
    f.toHomologicalComplex.f p ≫ (moduleCochain A E.π).v p p (add_zero p) = 𝟙 _ := by
  simpa [moduleCochain_comp, moduleCochain_id, ← hf, moduleCochain_cocycleOfHom] using
    Cochain.congr_v (congrArg (moduleCochain.{u, v, w} A) E.π_a) p p (add_zero p)

/-- The chosen splitting sections the second morphism in every degree. -/
private theorem split_s_g (hg : cocycleOfHom A (dgCategoryData A) g = E.b) (p : ℤ) :
    (moduleCochain A E.s).v p p (add_zero p) ≫ g.toHomologicalComplex.f p = 𝟙 _ := by
  simpa [moduleCochain_comp, moduleCochain_id, ← hg, moduleCochain_cocycleOfHom] using
    Cochain.congr_v (congrArg (moduleCochain.{u, v, w} A) E.b_s) p p (add_zero p)

/-- The retraction and the section of the chosen splitting are complementary in every degree. -/
private theorem split_id (hf : cocycleOfHom A (dgCategoryData A) f = E.a)
    (hg : cocycleOfHom A (dgCategoryData A) g = E.b) (p : ℤ) :
    (moduleCochain A E.π).v p p (add_zero p) ≫ f.toHomologicalComplex.f p +
      g.toHomologicalComplex.f p ≫ (moduleCochain A E.s).v p p (add_zero p) = 𝟙 _ := by
  simpa [moduleCochain_add, moduleCochain_comp, moduleCochain_id, ← hf, ← hg,
    moduleCochain_cocycleOfHom] using
    Cochain.congr_v (congrArg (moduleCochain.{u, v, w} A) E.a_π_add_s_b) p p (add_zero p)

end Split

/-- A split pair of morphisms composes to zero. -/
private theorem comp_eq_zero_of_split {C₀ : Type*} [Category C₀] [Preadditive C₀]
    {M₀ N₀ P₀ : C₀} (a : M₀ ⟶ N₀) (b : N₀ ⟶ P₀) (r : N₀ ⟶ M₀) (s : P₀ ⟶ N₀)
    (h1 : a ≫ r = 𝟙 M₀) (h2 : s ≫ b = 𝟙 P₀) (h3 : r ≫ a + b ≫ s = 𝟙 N₀) :
    a ≫ b = 0 := by
  have : IsSplitMono s := .mk' ⟨b, h2⟩
  rw [← cancel_mono s, zero_comp, Category.assoc]
  simpa [reassoc_of% h1] using a ≫= h3

section Sequence

variable {M N P : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) (g : N ⟶ P)
  (E : DGCategory.GradedSplitShortExact (A := (dgCategoryData.{u, v, w} A).category)
    (asObject A M) (asObject A N) (asObject A P))

include E

/-- The underlying sequence of complexes of sheaves of modules is a complex. -/
theorem split_comp_eq_zero (hf : cocycleOfHom A (dgCategoryData A) f = E.a)
    (hg : cocycleOfHom A (dgCategoryData A) g = E.b) :
    f.toHomologicalComplex ≫ g.toHomologicalComplex = 0 := by
  ext p : 1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  exact comp_eq_zero_of_split _ _ _ _ (split_f_r A f E hf p) (split_s_g A g E hg p)
    (split_id A f g E hf hg p)

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The underlying sequence of complexes of sheaves of modules is short exact, being split in
every degree by the chosen splitting of the admissible short exact sequence. -/
theorem split_shortExact (hf : cocycleOfHom A (dgCategoryData A) f = E.a)
    (hg : cocycleOfHom A (dgCategoryData A) g = E.b) :
    (ShortComplex.mk f.toHomologicalComplex g.toHomologicalComplex
      (split_comp_eq_zero A f g E hf hg)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun p => ShortComplex.Splitting.shortExact
    { r := (moduleCochain A E.π).v p p (add_zero p)
      s := (moduleCochain A E.s).v p p (add_zero p)
      f_r := split_f_r A f E hf p
      s_g := split_s_g A g E hg p
      id := split_id A f g E hf hg p }

end Sequence

/-! ### Zeroth cohomology on the homotopy category is homological -/

section Homological

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The quotient functor to the homotopy category of right differential graded modules is
essentially surjective, being the quotient functor of a categorical quotient. -/
instance quotient_essSurj : (HomotopyCategory.quotient.{u, v, w} A).EssSurj :=
  CategoryTheory.Quotient.essSurj_functor _

/-- Zeroth cohomology of right differential graded modules is additive, being the composite of
the additive functor forgetting the action with Mathlib's degree-zero homology functor. -/
instance zerothCohomologyFunctor_additive : (zerothCohomologyFunctor.{u, v, w} A).Additive := by
  change (toCochainComplex.{u, v, w} A ⋙ HomologicalComplex.homologyFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) 0).Additive
  infer_instance

namespace HomotopyCategory

/-- Zeroth cohomology on the homotopy category of right differential graded modules is additive:
it becomes additive after composition with the quotient functor, which is full and essentially
surjective. -/
instance zerothCohomologyFunctor_additive :
    (HomotopyCategory.zerothCohomologyFunctor.{u, v, w} A).Additive := by
  have h : (HomotopyCategory.quotient.{u, v, w} A ⋙
      HomotopyCategory.zerothCohomologyFunctor.{u, v, w} A).Additive :=
    Functor.additive_of_iso (CategoryTheory.Quotient.lift.isLift _ _ _).symm
  exact Functor.additive_of_full_essSurj_comp (HomotopyCategory.quotient.{u, v, w} A) _

/-- Zeroth cohomology on the homotopy category of right differential graded `A`-modules is a
homological functor: it takes a distinguished triangle of `K(Mod(A, d))` to an exact sequence of
sheaves of `O`-modules. -/
@[stacks 0FT2 "H^0 on the homotopy category is a homological functor"]
instance zerothCohomologyFunctor_isHomological :
    (HomotopyCategory.zerothCohomologyFunctor.{u, v, w} A).IsHomological := by
  apply Functor.IsHomological.mk'
  intro T hT
  rw [HomotopyCategory.distinguished_iff] at hT
  obtain ⟨M, N, P, f, g, δ, E, hf, hg, ⟨e⟩, -⟩ := hT
  refine ⟨Triangle.mk ((HomotopyCategory.quotient A).map f)
    ((HomotopyCategory.quotient A).map g) δ, e, ?_⟩
  exact (split_shortExact A f g E hf hg).homology_exact₂ 0

end HomotopyCategory

end Homological

end SheafOfModules.DifferentialGradedModule
