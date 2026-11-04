module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport

/-!
# The support of a sub- or quotient module, and vanishing over the range of a map of points

Let `X` be an algebraic space over a scheme `S` of a big fppf site.  The support of Stacks 04KA
of an `𝒪_X`-module shrinks both under passage to a submodule and under passage to a quotient
module: a monomorphism of modules is injective and an epimorphism is surjective on every
geometric stalk, so neither can create a nonzero stalk.  In particular the kernel of a map of
`𝒪_X`-modules is supported in the support of its source and the cokernel in the support of its
target.

Combined with the vanishing criterion of Stacks 04KA — a module is zero exactly when its
support is empty — this yields a criterion for vanishing relative to a map `f` into the point
set of `X`: a module whose support is contained in the range of `f` and whose support has empty
inverse image under `f` is zero.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_toSheaf_subset_of_mono` and
  `AlgebraicGeometry.Space.supportOfSheaf_toSheaf_subset_of_epi`: the support of the source of a
  monomorphism of `𝒪_X`-modules, respectively of the target of an epimorphism, is contained in
  the support of the other module.  `AlgebraicGeometry.Space.supportOfSheaf_kernel_subset` and
  `AlgebraicGeometry.Space.supportOfSheaf_cokernel_subset` are the cases of a kernel and of a
  cokernel.
* `AlgebraicGeometry.Space.isZero_of_preimage_supportOfSheaf_eq_empty`: an `𝒪_X`-module whose
  support lies in the range of a map into the point set of `X` and has empty inverse image
  under that map is zero.
* `AlgebraicGeometry.Space.isIso_iff_mono_and_epi_modules`: a map of `𝒪_X`-modules is an
  isomorphism exactly when it is both a monomorphism and an epimorphism.

## Implementation notes

The two support containments are proved on geometric stalks rather than by transporting
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_mono`, which is a statement about abelian
sheaves, across `SheafOfModules.toSheaf`; the latter route would need that functor to preserve
monomorphisms.  They are accordingly stated at the module universe of the structure rings,
which is the universe at which the two stalkwise clauses of Stacks 04K5 for modules are
available, whereas the vanishing criterion holds at an arbitrary module universe.

The kernel and cokernel statements assume only the existence of that kernel, respectively of
that cokernel, rather than the abelian structure of the category, so that they apply to
whichever construction of kernels and cokernels is in force.  Their type ascriptions on
`CategoryTheory.Limits.kernel` and `CategoryTheory.Limits.cokernel` are needed because the
underlying ring sheaf of `SheafOfModules.toSheaf` is otherwise left to unification.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

/-! ### A set inside the range of a map with empty inverse image -/

namespace Set

/-- A set contained in the range of a map and having empty inverse image under that map is
empty. -/
theorem eq_empty_of_subset_range_of_preimage_eq_empty {α β : Type*} {f : α → β} {A : Set β}
    (hA : A ⊆ Set.range f) (h : f ⁻¹' A = ∅) : A = ∅ := by
  rw [← Set.image_preimage_eq_of_subset hA, h, Set.image_empty]

end Set

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-! ### The support of a submodule and of a quotient module -/

/-- **Stacks 04KB for modules.**  The support of the source of a monomorphism of `𝒪_X`-modules
is contained in the support of its target: a monomorphism is injective on every geometric
stalk, so a point carrying a nonzero stalk of the source carries a nonzero stalk of the
target. -/
theorem supportOfSheaf_toSheaf_subset_of_mono {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    [Mono φ] :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) := by
  intro y hy
  obtain ⟨p, hp, hnt⟩ :=
    (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F y).mp hy
  have := hnt
  exact (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X G y).mpr
    ⟨p, hp, (injective_geometricModuleStalkMap_of_mono B S hS X p φ).nontrivial⟩

/-- The support of the target of an epimorphism of `𝒪_X`-modules is contained in the support of
its source: an epimorphism is surjective on every geometric stalk, so a point carrying a
nonzero stalk of the target carries a nonzero stalk of the source. -/
theorem supportOfSheaf_toSheaf_subset_of_epi {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    [Epi φ] :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  intro y hy
  obtain ⟨p, hp, hnt⟩ :=
    (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X G y).mp hy
  have := hnt
  exact (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F y).mpr
    ⟨p, hp, (surjective_geometricModuleStalkMap_of_epi B S hS X p φ).nontrivial⟩

/-- The support of the kernel of a map of `𝒪_X`-modules is contained in the support of its
source. -/
theorem supportOfSheaf_kernel_subset {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    [HasKernel φ] :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj (kernel φ : Modules.{u, u} B S hS X.1 X.2)) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) :=
  supportOfSheaf_toSheaf_subset_of_mono B S hS X (kernel.ι φ)

/-- The support of the cokernel of a map of `𝒪_X`-modules is contained in the support of its
target. -/
theorem supportOfSheaf_cokernel_subset {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    [HasCokernel φ] :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj (cokernel φ : Modules.{u, u} B S hS X.1 X.2)) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) :=
  supportOfSheaf_toSheaf_subset_of_epi B S hS X (cokernel.π φ)

/-! ### Vanishing over the range of a map of point sets -/

/-- An `𝒪_X`-module whose support is contained in the range of a map `f` into the point set of
`X` and whose support has empty inverse image under `f` is zero: its support is empty, and a
module with empty support vanishes. -/
theorem isZero_of_preimage_supportOfSheaf_eq_empty {α : Type*} (f : α → points B S hS X.1)
    (F : Modules.{u, m} B S hS X.1 X.2)
    (hsub : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆ Set.range f)
    (hpre : f ⁻¹' supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) = ∅) :
    IsZero F :=
  (supportOfSheaf_eq_empty_iff_isZero B S hS X F).mp
    (Set.eq_empty_of_subset_range_of_preimage_eq_empty hsub hpre)

/-! ### Isomorphisms of modules -/

/-- A map of `𝒪_X`-modules is an isomorphism exactly when it is both a monomorphism and an
epimorphism: the category of `𝒪_X`-modules with sections in the universe of the schemes is
abelian, hence balanced. -/
theorem isIso_iff_mono_and_epi_modules {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G) :
    IsIso φ ↔ Mono φ ∧ Epi φ :=
  have := balanced_modules B S hS X
  isIso_iff_mono_and_epi φ

end AlgebraicGeometry.Space

end
