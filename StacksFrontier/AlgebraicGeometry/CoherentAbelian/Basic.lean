module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AbelianCategory
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
import StacksCore.Tactic.StacksAttribute

/-!
# Coherent sheaves of modules on a ringed space form an abelian subcategory

There are two coherence predicates for sheaves of modules on a ringed space, both encoding the
definition of Stacks Tag 01BV: `SheafOfModules.IsCoherent` and `Stacks.SheafOfModules.IsCoherent`,
classes with the same two fields. This file shows that they agree, deduces that the two object
properties are *equal*, and transports across that equality the closure of
`Stacks.SheafOfModules.coherentModules` under kernels, cokernels and extensions. Consequently the
coherent sheaves of modules, for `SheafOfModules.IsCoherent`, form an abelian category whose
inclusion into all sheaves of modules is exact.

## Main results

* `AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent`: the two coherence
  predicates agree, and `coherentModules_eq` upgrades this to an equality of object properties.
* `AlgebraicGeometry.CoherentAbelian.coherentModules_containsZero` and the four closure
  instances after it: the five parent classes of `ObjectProperty.IsWeakSerreClass
  (fun M : SheafOfModules.{u} R => M.IsCoherent)`. The assembled
  `ObjectProperty.IsWeakSerreClass` instance itself is
  `SheafOfModules.coherentModules_isWeakSerreClass`.
* `AlgebraicGeometry.CoherentAbelian.coherentModulesAbelian`: the category of coherent sheaves
  of modules is abelian.
* `AlgebraicGeometry.CoherentAbelian.coherentModules_inclusion_preservesFiniteLimits` and
  `coherentModules_inclusion_preservesFiniteColimits`: the inclusion into all sheaves of modules
  is exact.
* `AlgebraicGeometry.CoherentAbelian.isCoherent_of_mono`,
  `isFiniteType_kernel_of_isCoherent`, `isCoherent_kernel`, `isCoherent_cokernel`,
  `isCoherent_X₁_of_shortExact`, `isCoherent_X₂_of_shortExact` and
  `isCoherent_X₃_of_shortExact`: assertions (1)–(4) of Stacks Tag 01BY.

## Implementation notes

The abelian structure is assembled with structure-instance notation and an empty body rather
than by `inferInstance`: each of `Preadditive`, `HasFiniteProducts`, `IsNormalMonoCategory` and
`IsNormalEpiCategory` is found for the full subcategory, but the composite `Abelian` instance of
`Mathlib.CategoryTheory.Abelian.Subcategory` does not unify against a coherence property stated
as a lambda.

The namespace avoids the `Stacks.` prefix: inside a namespace beginning with `Stacks.`, the
name `SheafOfModules.IsCoherent` resolves to `Stacks.SheafOfModules.IsCoherent`, which collapses
the two predicates.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.CoherentAbelian

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-! ### The two coherence predicates -/

/-- `Stacks.SheafOfModules.IsCoherent` implies `SheafOfModules.IsCoherent`. -/
theorem isCoherent_of_stacksIsCoherent {M : SheafOfModules.{u} R}
    (h : Stacks.SheafOfModules.IsCoherent M) : SheafOfModules.IsCoherent M :=
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- `SheafOfModules.IsCoherent` implies `Stacks.SheafOfModules.IsCoherent`. -/
theorem stacksIsCoherent_of_isCoherent {M : SheafOfModules.{u} R}
    (h : SheafOfModules.IsCoherent M) : Stacks.SheafOfModules.IsCoherent M :=
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- `SheafOfModules.IsCoherent` and `Stacks.SheafOfModules.IsCoherent` agree. -/
theorem isCoherent_iff_stacksIsCoherent {M : SheafOfModules.{u} R} :
    SheafOfModules.IsCoherent M ↔ Stacks.SheafOfModules.IsCoherent M :=
  ⟨stacksIsCoherent_of_isCoherent, isCoherent_of_stacksIsCoherent⟩

/-- Coherence as a property of objects of the category of sheaves of modules is *equal* to
`Stacks.SheafOfModules.coherentModules R`. -/
theorem coherentModules_eq :
    (fun M : SheafOfModules.{u} R => M.IsCoherent) =
      Stacks.SheafOfModules.coherentModules R := by
  funext M
  exact propext isCoherent_iff_stacksIsCoherent

/-! ### The weak Serre package, transported -/

/-- The zero sheaf of modules is coherent. -/
instance coherentModules_containsZero :
    ObjectProperty.ContainsZero (fun M : SheafOfModules.{u} R => M.IsCoherent) :=
  coherentModules_eq (R := R) ▸
    (inferInstance : (Stacks.SheafOfModules.coherentModules R).ContainsZero)

/-- Coherence is invariant under isomorphism. -/
instance coherentModules_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun M : SheafOfModules.{u} R => M.IsCoherent) :=
  coherentModules_eq (R := R) ▸
    (inferInstance : (Stacks.SheafOfModules.coherentModules R).IsClosedUnderIsomorphisms)

/-- Coherent sheaves of modules are closed under kernels. -/
instance coherentModules_isClosedUnderKernels :
    ObjectProperty.IsClosedUnderKernels (fun M : SheafOfModules.{u} R => M.IsCoherent) :=
  coherentModules_eq (R := R) ▸
    (inferInstance : (Stacks.SheafOfModules.coherentModules R).IsClosedUnderKernels)

/-- Coherent sheaves of modules are closed under cokernels. -/
instance coherentModules_isClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels (fun M : SheafOfModules.{u} R => M.IsCoherent) :=
  coherentModules_eq (R := R) ▸
    (inferInstance : (Stacks.SheafOfModules.coherentModules R).IsClosedUnderCokernels)

/-- Coherent sheaves of modules are closed under extensions. -/
instance coherentModules_isClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions (fun M : SheafOfModules.{u} R => M.IsCoherent) :=
  coherentModules_eq (R := R) ▸
    (inferInstance : (Stacks.SheafOfModules.coherentModules R).IsClosedUnderExtensions)

/-! ### Closure statements -/

/-- **Stacks Project, Tag 01BY (1).** A finite type subsheaf of a coherent sheaf of modules is
coherent. A subsheaf is represented by a monomorphism, and the conclusion does not depend on
the choice of representative. -/
theorem isCoherent_of_mono {M N : SheafOfModules.{u} R} [hM : M.IsCoherent] [N.IsFiniteType]
    (ι : N ⟶ M) [Mono ι] : N.IsCoherent := by
  have : Stacks.SheafOfModules.IsCoherent M := stacksIsCoherent_of_isCoherent hM
  exact isCoherent_of_stacksIsCoherent (Stacks.SheafOfModules.isCoherent_of_mono ι)

/-- **Stacks Project, Tag 01BY (2).** The kernel of a morphism from a sheaf of modules of finite
type to a coherent sheaf of modules is of finite type. -/
theorem isFiniteType_kernel_of_isCoherent {M N : SheafOfModules.{u} R} [M.IsFiniteType]
    [hN : N.IsCoherent] (φ : M ⟶ N) : (kernel φ).IsFiniteType := by
  have : Stacks.SheafOfModules.IsCoherent N := stacksIsCoherent_of_isCoherent hN
  exact Stacks.SheafOfModules.isFiniteType_kernel_of_isCoherent φ

/-- **Stacks Project, Tag 01BY (3), kernels.** The kernel of a morphism of coherent sheaves of
modules is coherent. -/
instance isCoherent_kernel {M N : SheafOfModules.{u} R} [M.IsCoherent] [N.IsCoherent]
    (φ : M ⟶ N) : (kernel φ).IsCoherent :=
  ObjectProperty.prop_kernel (P := fun M : SheafOfModules.{u} R => M.IsCoherent) φ
    ‹M.IsCoherent› ‹N.IsCoherent›

/-- **Stacks Project, Tag 01BY (3), cokernels.** The cokernel of a morphism of coherent sheaves
of modules is coherent. -/
instance isCoherent_cokernel {M N : SheafOfModules.{u} R} [M.IsCoherent] [N.IsCoherent]
    (φ : M ⟶ N) : (cokernel φ).IsCoherent :=
  ObjectProperty.prop_cokernel (P := fun M : SheafOfModules.{u} R => M.IsCoherent) φ
    ‹M.IsCoherent› ‹N.IsCoherent›

/-- **Stacks Project, Tag 01BY (4).** An extension of coherent sheaves of modules is coherent:
the middle term of a short exact sequence whose outer terms are coherent. -/
theorem isCoherent_X₂_of_shortExact {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact) (h₁ : S.X₁.IsCoherent) (h₃ : S.X₃.IsCoherent) : S.X₂.IsCoherent :=
  ObjectProperty.prop_X₂_of_shortExact (P := fun M : SheafOfModules.{u} R => M.IsCoherent)
    hS h₁ h₃

/-- **Stacks Project, Tag 01BY (4).** The subobject term of a short exact sequence of sheaves of
modules is coherent when the other two terms are. -/
theorem isCoherent_X₁_of_shortExact {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent) : S.X₁.IsCoherent :=
  ObjectProperty.prop_of_isLimit_kernelFork (P := fun M : SheafOfModules.{u} R => M.IsCoherent)
    hS.fIsKernel h₂ h₃

/-- **Stacks Project, Tag 01BY (4).** The quotient term of a short exact sequence of sheaves of
modules is coherent when the other two terms are. -/
theorem isCoherent_X₃_of_shortExact {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact) (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) : S.X₃.IsCoherent :=
  ObjectProperty.prop_of_isColimit_cokernelCofork
    (P := fun M : SheafOfModules.{u} R => M.IsCoherent) hS.gIsCokernel h₁ h₂

/-! ### The abelian category of coherent sheaves of modules, and exactness of the inclusion -/

/-- **Stacks Project, Tag 01BY (5)**, first half. Coherent sheaves of modules on a ringed space
form an abelian category. -/
instance coherentModulesAbelian (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    Abelian (AlgebraicGeometry.SheafOfModules.CoherentModules R) where

/-- **Stacks Project, Tag 01BY (5)**, second half. The inclusion of coherent sheaves of modules
into all sheaves of modules preserves finite limits. -/
instance coherentModules_inclusion_preservesFiniteLimits
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    PreservesFiniteLimits
      (ObjectProperty.ι (fun M : SheafOfModules.{u} R => M.IsCoherent)) :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- **Stacks Project, Tag 01BY (5)**, second half. The inclusion of coherent sheaves of modules
into all sheaves of modules preserves finite colimits. -/
instance coherentModules_inclusion_preservesFiniteColimits
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    PreservesFiniteColimits
      (ObjectProperty.ι (fun M : SheafOfModules.{u} R => M.IsCoherent)) :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

end AlgebraicGeometry.CoherentAbelian

end
