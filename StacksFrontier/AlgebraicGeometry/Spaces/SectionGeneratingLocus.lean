module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The open subspace over which a global section generates a module

Let `X` be an algebraic space over a scheme `S`, let `𝓜` be an `𝒪_X`-module on the small étale
site of `X` and let `s` be a global section of `𝓜`.  The section is the same thing as the map
`𝒪_X ⟶ 𝓜`, `1 ↦ s`, and `s` *generates* `𝓜` at a point `x ∈ |X|` when the stalk of the cokernel
of that map at a geometric point over `x` vanishes, that is when `x` lies outside the support of
the cokernel.  This set of points is the *generating locus* of `s`.

When `𝓜` is of finite type, so is the cokernel, whose support is then closed (Stacks 07TZ), and
the generating locus is open; by Stacks 03BZ it is the point set of a unique open subspace
`U_s ⊆ X`, the open subspace "over which `s` is a generator of `𝓜`" of the proof of
Stacks 0D2W.  For an invertible `𝓜` it is the nonvanishing locus of `s`.

## Main definitions

* `AlgebraicGeometry.Space.sectionGeneratingLocus`: the set of points of `X` at which `s` generates
  `𝓜`.
* `AlgebraicGeometry.Space.generatingSubspace`: the subfunctor of `X` cut out by the generating
  locus.

## Main results

* `AlgebraicGeometry.Space.isOpen_sectionGeneratingLocus`: the generating locus of a section of a
  module of finite type is open.
* `AlgebraicGeometry.Space.isOpenSubspace_generatingSubspace`: the generating subspace of a
  section of a module of finite type is an open subspace.
* `AlgebraicGeometry.Space.range_pointsMap_ι_generatingSubspace`: its point set is the
  generating locus.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-- The *generating locus* of a global section `s` of an `𝒪_X`-module `𝓜`: the points of `X`
outside the support of the cokernel of the map `𝒪_X ⟶ 𝓜` given by `s`, that is the points at
which `s` generates `𝓜`. -/
def sectionGeneratingLocus (M : Modules.{u, u} B S hS X hX) (s : M.sections) :
    Set (points B S hS X) :=
  (supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj
    (cokernel (C := Modules.{u, u} B S hS X hX) (M.unitHomEquiv.symm s))))ᶜ

/-- A point lies in the generating locus of `s` exactly when it lies outside the support of the
cokernel of the map `𝒪_X ⟶ 𝓜` given by `s`. -/
theorem mem_sectionGeneratingLocus_iff (M : Modules.{u, u} B S hS X hX) (s : M.sections)
    (x : points B S hS X) :
    x ∈ sectionGeneratingLocus B S hS M s ↔
      x ∉ supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj
        (cokernel (C := Modules.{u, u} B S hS X hX) (M.unitHomEquiv.symm s))) :=
  Iff.rfl

/-- **The generating locus of a section of a module of finite type is open.**  The cokernel is a
quotient of the module, hence of finite type, and the support of a module of finite type is
closed by Stacks 07TZ. -/
theorem isOpen_sectionGeneratingLocus (M : Modules.{u, u} B S hS X hX) (s : M.sections)
    (hM : SheafOfModules.IsFiniteTypeOnSite M) : IsOpen (sectionGeneratingLocus B S hS M s) :=
  (isClosed_supportOfSheaf_of_epi B S hS X hX
    (cokernel.π (C := Modules.{u, u} B S hS X hX) (M.unitHomEquiv.symm s)) hM).isOpen_compl

variable (hX) in
/-- The *generating subspace* `U_s` of a global section `s` of an `𝒪_X`-module `𝓜`: the
subfunctor of `X` cut out by the generating locus of `s`.  For `𝓜` of finite type it is the
open subspace over which `s` generates `𝓜`
(`AlgebraicGeometry.Space.isOpenSubspace_generatingSubspace`). -/
def generatingSubspace (M : Modules.{u, u} B S hS X hX) (s : M.sections) : Subfunctor X :=
  openSubspaceOfPoints B S hS X (sectionGeneratingLocus B S hS M s)

/-- **The generating subspace of a section of a module of finite type is an open subspace.**
This is Stacks 03BZ applied to the generating locus, which is open by
`AlgebraicGeometry.Space.isOpen_sectionGeneratingLocus`. -/
theorem isOpenSubspace_generatingSubspace (M : Modules.{u, u} B S hS X hX) (s : M.sections)
    (hM : SheafOfModules.IsFiniteTypeOnSite M) :
    IsOpenSubspace B S hS (generatingSubspace B S hS hX M s) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hX _ (isOpen_sectionGeneratingLocus B S hS M s hM)

/-- The point set of the generating subspace is the generating locus. -/
theorem range_pointsMap_ι_generatingSubspace (M : Modules.{u, u} B S hS X hX) (s : M.sections) :
    Set.range (pointsMap B S hS (generatingSubspace B S hS hX M s).toFunctor
      (generatingSubspace B S hS hX M s).ι) = sectionGeneratingLocus B S hS M s :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

end AlgebraicGeometry.Space

end
