module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction

/-!
# The canonical comparison map of the sections of a differential graded module

Let `C` be a category, viewed as a site with the chaotic topology, let `O` be a sheaf of rings
on it, let `(A, d)` be a sheaf of differential graded `O`-algebras and let `M` be a right
differential graded `A`-module. For a morphism `a : V ⟶ U` of `Cᵒᵖ` the sections `M(V)` and
`M(U)` are differential graded modules over the section algebras `A(V)` and `A(U)`, and
restriction of sections is a homomorphism `M(V) ⟶ M(U)` of differential graded `A(V)`-modules.
Its adjoint transpose under the adjunction between derived extension of scalars along
`A(V) ⟶ A(U)` and derived restriction of scalars — Tag 0BYX — is the canonical map

`M(V) ⊗^𝐋_{A(V)} A(U) ⟶ M(U)`

of `D(A(U), d)`. Because the topology is chaotic, evaluation at an object is exact and
`RΓ(U, M)` is computed by `M(U)`; this map is therefore the canonical map of Definition 24.33.1,
and the quasi-coherence condition of that definition is that it be an isomorphism for every
morphism of the site.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.Chaotic.sectionClass`: the class of `M(U)` in
  `D(A(U), d)`.
* `SheafOfModules.DifferentialGradedModule.Chaotic.sectionBaseChange`: derived extension of scalars
  `- ⊗^𝐋_{A(V)} A(U)` along the restriction homomorphism of the section algebras.
* `SheafOfModules.DifferentialGradedModule.Chaotic.derivedSectionRestriction`: the image in
  `D(A(V), d)` of restriction of sections, read through the factorization of derived restriction
  of scalars.
* `SheafOfModules.DifferentialGradedModule.Chaotic.sectionComparison`: **the canonical map
  `M(V) ⊗^𝐋_{A(V)} A(U) ⟶ M(U)`**, the adjoint transpose of the previous one.
* `SheafOfModules.DifferentialGradedModule.Chaotic.IsQCModule`: the quasi-coherence
  condition on a right differential graded `A`-module.

## Implementation notes

Derived extension of scalars is the derived tensor product with the regular bimodule of the
restriction homomorphism. Derived restriction of scalars is the descent of restriction of scalars
through the localizations, and `DifferentialGradedModule.derivedRestrictionFactorization` is the
canonical isomorphism exhibiting that descent; through it the image of restriction of sections in
`D(A(V), d)` becomes a map into the derived restriction of the class of `M(U)`.

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory DirectSum

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

namespace Chaotic

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- **The class of the sections `M(U)` in the derived category `D(A(U), d)`.** -/
abbrev sectionClass (M : DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.derivedCategory' (A.sectionAlgebra U) :=
  (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q.obj
    ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
      (M.sectionModule U))

variable {U V : Cᵒᵖ}

/-- **Derived extension of scalars `- ⊗^𝐋_{A(V)} A(U)`** along the restriction homomorphism of
the section algebras: the derived tensor product with its regular bimodule, Tag 0BYX. -/
abbrev sectionBaseChange (A : DifferentialGradedAlgebra.{t, a} R) (a : V ⟶ U) :
    _root_.DifferentialGradedModule.derivedCategory' (A.sectionAlgebra V) ⥤
      _root_.DifferentialGradedModule.derivedCategory' (A.sectionAlgebra U) :=
  DifferentialGraded.Bimodule.derivedTensorFunctor
    (DifferentialGraded.Bimodule.regular (A.sectionRestriction a))

/-- The adjunction between derived extension of scalars along the restriction homomorphism and
derived restriction of scalars along it, Tag 0BYX. -/
abbrev sectionBaseChangeAdj (A : DifferentialGradedAlgebra.{t, a} R) (a : V ⟶ U) :
    sectionBaseChange A a ⊣
      _root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a) :=
  DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction (A.sectionRestriction a)

/-- **Restriction of sections, in the derived category `D(A(V), d)`**: the image of the
homomorphism `M(V) ⟶ M(U)` of differential graded `A(V)`-modules, read as a map into the derived
restriction of the class of `M(U)` through the factorization of derived restriction of
scalars. -/
def derivedSectionRestriction (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U) :
    sectionClass M V ⟶
      (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).obj
        (sectionClass M U) :=
  (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
          (M.sectionModuleRestriction a)) ≫
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
        ((_root_.DifferentialGradedModule.restrictScalarsHomotopyFunctorIso
          (A.sectionRestriction a)).inv.app (M.sectionModule U)) ≫
    (_root_.DifferentialGradedModule.derivedRestrictionFactorization
      (A.sectionRestriction a)).inv.app
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (M.sectionModule U))

/-- **The canonical map `M(V) ⊗^𝐋_{A(V)} A(U) ⟶ M(U)` of `D(A(U), d)`** attached to a morphism
`a : V ⟶ U` of `Cᵒᵖ`: the adjoint transpose of restriction of sections under the adjunction
between derived extension and derived restriction of scalars. -/
def sectionComparison (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U) :
    (sectionBaseChange A a).obj (sectionClass M V) ⟶ sectionClass M U :=
  ((sectionBaseChangeAdj A a).homEquiv _ _).symm (derivedSectionRestriction M a)

/-- The adjoint transpose of `sectionComparison M a` under `sectionBaseChangeAdj A a` is
`derivedSectionRestriction M a`. -/
theorem homEquiv_sectionComparison (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U) :
    (sectionBaseChangeAdj A a).homEquiv _ _ (sectionComparison M a) =
      derivedSectionRestriction M a :=
  Equiv.apply_symm_apply _ _

/-! ### Naturality in the differential graded module -/

section Naturality

variable {M N : DifferentialGradedModule.{t, a, a} A}

/-- Restriction of sections is natural in the right differential graded module: the restriction
maps of `M` and of `N` commute with a homomorphism `M ⟶ N`. -/
theorem sectionRestrictAdd_sectionMapAdd (f : M ⟶ N) (a : V ⟶ U) (x : M.totalSections V) :
    N.sectionRestrictAdd a (sectionMapAdd f V x) =
      sectionMapAdd f U (M.sectionRestrictAdd a x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n p =>
      simp only [sectionMapAdd_of, sectionRestrictAdd_of]
      exact congrArg (DirectSum.of (N.sectionsPiece U) n)
        (PresheafOfModules.naturality_apply (f.toHomologicalComplex.f n).val a p).symm

/-- Restriction of sections is natural in the right differential graded module, as an equality
of homomorphisms of differential graded `A(V)`-modules. -/
theorem sectionMap_comp_sectionModuleRestriction (f : M ⟶ N) (a : V ⟶ U) :
    sectionMap f V ≫ N.sectionModuleRestriction a =
      M.sectionModuleRestriction a ≫
        _root_.DifferentialGradedModule.restrictScalarsHom (A.sectionRestriction a)
          (sectionMap f U) :=
  _root_.DifferentialGradedModule.Hom.ext
    (LinearMap.ext fun x ↦ sectionRestrictAdd_sectionMapAdd f a x)

/-- The map of classes in `D(A(U), d)` induced by a homomorphism of right differential graded
`A`-modules. -/
def sectionClassMap (f : M ⟶ N) (U : Cᵒᵖ) : sectionClass M U ⟶ sectionClass N U :=
  (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q.map
    ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).map
      (sectionMap f U))

end Naturality

/-- **The quasi-coherence condition of Definition 24.33.1, on a right differential graded
`A`-module**: for every morphism `U → V` of the chaotic site the canonical map
`M(V) ⊗^𝐋_{A(V)} A(U) ⟶ M(U)` is an isomorphism of `D(A(U), d)`. -/
def IsQCModule (M : DifferentialGradedModule.{t, a, a} A) : Prop :=
  ∀ ⦃U V : Cᵒᵖ⦄ (a : V ⟶ U), IsIso (sectionComparison M a)

end Chaotic

end DifferentialGradedModule

end SheafOfModules

end
