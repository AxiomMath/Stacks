module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCommRingCounitSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage

/-!
# The inverse image of the defining ideal sheaf is a kernel

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`Z ⊆ X` be a closed subspace with inclusion `i = subspaceInclusion B S hS X Z` and defining
ideal sheaf `𝓘 = definingIdealSheaf B S hS X Z ⊆ 𝒪_X`.  This file transports the short exact
sequence
```
  0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0
```
of Stacks 03MB (`AlgebraicGeometry.Space.definingIdealShortComplex_shortExact`) along the
inverse image of sheaves of modules of Stacks 03D2 and then along its right adjoint, the direct
image of Stacks 03D1, and reads the result on sections.

## Main results

* `AlgebraicGeometry.Space.inverseImageDefiningIdealComplex_shortExact`: **`i⁻¹𝓘 ⟶ i⁻¹𝒪_X ⟶
  i⁻¹i_*𝒪_Z` is short exact.**  The inverse image of sheaves of modules is exact (Stacks 04JC
  at module level, `Stacks.Sheaves.RingedToposModules.shortExact_map_inverseImageModules`).
* `AlgebraicGeometry.Space.isLimit_kernelFork_directImageDefiningIdeal`: **`i_*i⁻¹𝓘 ⟶ i_*i⁻¹𝒪_X`
  is a kernel of `i_*i⁻¹(i♯)`.**  The direct image of modules is a right adjoint
  (Stacks 03D3), hence left exact; epimorphy is the one clause that does *not* survive, and is
  not asserted.
* `AlgebraicGeometry.Space.injective_directImageDefiningIdeal_f_val_app` and
  `AlgebraicGeometry.Space.mem_range_directImageDefiningIdeal_f_val_app`: the sectionwise form.
  Over every object of the small étale site of `X` the inclusion
  `(i_*i⁻¹𝓘)(U) ⟶ (i_*i⁻¹𝒪_X)(U)` is **injective**, and its range is **exactly** the sections
  killed by `i_*i⁻¹(i♯)`.  Naturality in `U` is automatic: the inclusion is a morphism of sheaves
  of modules, so its components commute with restriction by
  `CategoryTheory.PresheafOfModules.naturality_apply`.
* `AlgebraicGeometry.Space.conormalExtendScalarsUnit`: the canonical map
  `κ₀ : i⁻¹𝓘 ⟶ 𝒞_{Z/X}`, and
  `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_app_definingIdealSheaf`: **its
  characterisation** — the unit of Stacks 03LU at `𝓘` is the unit of Stacks 03D3 followed by the
  direct image of `κ₀` (and the comparison of the two direct images of modules).
* `AlgebraicGeometry.Space.unit_comp_map_definingIdealSheaf_ι`: the module unit of `𝓘`, pushed
  into `i_*i⁻¹𝒪_X`, is the restriction to `𝓘` of the module unit of `𝒪_X`.
* `AlgebraicGeometry.Space.directImageDefiningIdealComplex_X₂_val_obj_eq`: **the sections of the
  middle term over an object are, definitionally, its sections as a sheaf of commutative
  rings** — so a consumer may hand a section of the presheaf of rings `i_*i⁻¹𝒪_X` to the two
  statements above with no transport.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_structureProjection`: the underlying morphism
  of sheaves of sets of `AlgebraicGeometry.Space.structureProjection` is the structure map of
  Stacks 03G8.

## Implementation notes

**Why the route is the inverse image of the whole short exact sequence, and not a local
generation statement.**  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionDirectImageDerivationKernel.lean` used to
say that along the inverse-image form `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` the kernel "is not the inverse image
of the defining ideal sheaf on the nose — identifying the two is the local-generation statement,
which is not available here".  **The second half of that is false, and this file is the
refutation**: the identification is *exactness of the inverse image*, nothing more — no
generation statement, and no comparison of ideals, is involved.  The note has been corrected.

What is proved here is the statement for `i⁻¹(i♯ : 𝒪_X ⟶ i_*𝒪_Z)`.  The *inverse-image* form
`i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` differs from it only by the counit `i⁻¹i_*𝒪_Z ⟶ 𝒪_Z`
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget`), which for a closed immersion is
invertible (`AlgebraicGeometry.Space.isIso_commRingCounit_of_isClosedImmersion`), so the two
morphisms have the same kernel; reading *that* identification on sections is not done here and
is the one step a consumer phrasing its hypothesis through the inverse-image form still owes.

**Everything sectionwise is already in the library.**  `SheafOfModules.evaluation` preserves
finite limits (Mathlib), so a limit kernel fork of sheaves of modules is one of modules over
every object; that is
`SheafOfModules.injective_val_app_of_isLimit_kernelFork` and
`SheafOfModules.mem_range_val_app_of_isLimit_kernelFork`, both in the library.  Nothing here
re-derives them.

**Two elaboration facts.**

*The inverse-image short complex carries no explicit type.*  Its type is
`ShortComplex (SheafOfModules (inverseImageRingSheaf i (structureRingSheaf X)))`, and
`inverseImageRingSheaf` has six universe parameters only four of which the structure ring sheaf
of `X` determines; written out as an ascription the elaborator defaults the remaining two to `0`
and reports a mismatch at `Sheaf.{0, 0, 0, 1}`.  Pinning them by hand elaborates, but produces a
term that is then *not* the one `CategoryTheory.ShortComplex.map` builds, so the short-exactness
lemma no longer applies to it.  Leaving the type inferred is what works; the direct image lands
back in `AlgebraicGeometry.Space.Modules`, where the type can be written.

*What is not here: the two units compared on sections.* The module unit `𝒪_X ⟶ i_*i⁻¹𝒪_X` of Stacks
03D3 and the unit of `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction` both have the
set-level unit of `i⁻¹ ⊣ i_*` as their underlying morphism of sheaves of sets, by
`RingedToposModules.moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app` and
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction_unit_forget`; so they agree on sections.
That equality on sections is **not** `rfl` (the two sides are
`ConcreteCategory.hom` of a `ModuleCat` map and `CommRingCat.Hom.hom` of a `CommRingCat` map), and
both instantiations resist being written at this geometric point — the module one leaves the target
of `adj.unit.app` as a metavariable whose universe defaults wrongly, and the commutative-ring one
exhausts the heartbeat budget in `whnf`. So this half is named here and not proved.

*The `PreservesZeroMorphisms` instance must be handed over, not searched for.*  Instance search
finds `(inverseImageModules i 𝒪_X).PreservesZeroMorphisms` when that is the goal of its own
declaration, and **fails** on the very same instance when it arises as the instance argument of
`CategoryTheory.ShortComplex.map`, where the categories reach it through the
`AlgebraicGeometry.Space.Modules` spelling.  So the two instances are proved in their own
declarations above and passed explicitly with `@CategoryTheory.ShortComplex.map`.  Nothing
mathematical is involved; naming the functor in an `abbrev` does *not* help, and makes even the
standalone `Additive` goal fail.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal
  sheaf as the kernel of the structure map.
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC), exactness of the
  inverse image.
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2), the inverse image of
  sheaves of modules.
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3), the adjunction whose
  right adjoint is the direct image.
* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), the consumer: the
  first arrow of the conormal sequence of a split closed immersion is a monomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- The inverse image of sheaves of modules along the inclusion of a closed subspace preserves
zero morphisms.

Proved in its own declaration and handed to `CategoryTheory.ShortComplex.map` as an explicit
argument below: see the implementation notes of this file. -/
theorem preservesZeroMorphisms_inverseImageModules_subspaceInclusion :
    (inverseImageModules
      (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
      (structureRingSheaf B S hS X)).PreservesZeroMorphisms :=
  inferInstance

/-- The direct image of sheaves of modules along the inclusion of a closed subspace preserves
zero morphisms.  Companion of
`AlgebraicGeometry.Space.preservesZeroMorphisms_inverseImageModules_subspaceInclusion`. -/
theorem preservesZeroMorphisms_directImageModules_subspaceInclusion :
    (directImageModules
      (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
      (structureRingSheaf B S hS X)).PreservesZeroMorphisms :=
  inferInstance

/-- **The inverse image of the sequence `0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0`.**  The short complex
`i⁻¹𝓘 ⟶ i⁻¹𝒪_X ⟶ i⁻¹i_*𝒪_Z` of sheaves of `i⁻¹𝒪_X`-modules on the small étale site of `Z`,
obtained by applying the inverse image of Stacks 03D2 to
`AlgebraicGeometry.Space.definingIdealShortComplex`.

The type is left to be inferred and the zero-morphism instance is supplied by hand; see the
implementation notes of this file. -/
noncomputable def inverseImageDefiningIdealComplex :=
  @ShortComplex.map _ _ _ _ _ _ (definingIdealShortComplex B S hS X Z)
    (inverseImageModules
      (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
      (structureRingSheaf B S hS X))
    (preservesZeroMorphisms_inverseImageModules_subspaceInclusion B S hS X Z)

/-- **`0 ⟶ i⁻¹𝓘 ⟶ i⁻¹𝒪_X ⟶ i⁻¹i_*𝒪_Z ⟶ 0` is short exact.**

This is Stacks 04JC at module level — the inverse image of sheaves of modules along a morphism
of topoi is exact, `Stacks.Sheaves.RingedToposModules.shortExact_map_inverseImageModules` —
applied to the short exact sequence of Stacks 03MB. -/
theorem inverseImageDefiningIdealComplex_shortExact :
    (inverseImageDefiningIdealComplex B S hS X Z).ShortExact :=
  shortExact_map_inverseImageModules
    (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
    (structureRingSheaf B S hS X)
    (definingIdealShortComplex B S hS X Z)
    (definingIdealShortComplex_shortExact B S hS X Z)

/-- **The direct image of the inverse image of the sequence of Stacks 03MB.**  The short complex
`i_*i⁻¹𝓘 ⟶ i_*i⁻¹𝒪_X ⟶ i_*i⁻¹i_*𝒪_Z` of sheaves of `𝒪_X`-modules on the small étale site
of `X`.

It is a complex, and — by `AlgebraicGeometry.Space.isLimit_kernelFork_directImageDefiningIdeal`
— exact at the middle term with monomorphic first map.  It is *not* claimed to be short exact:
the direct image is only left exact. -/
noncomputable def directImageDefiningIdealComplex :
    ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
  @ShortComplex.map _ _ _ _ _ _ (inverseImageDefiningIdealComplex B S hS X Z)
    (directImageModules
      (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
      (structureRingSheaf B S hS X))
    (preservesZeroMorphisms_directImageModules_subspaceInclusion B S hS X Z)

/-- The direct image of sheaves of modules of Stacks 03D1 along the inclusion of a closed
subspace preserves finite limits: it is the right adjoint of the adjunction of Stacks 03D3,
`Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules`. -/
theorem preservesFiniteLimits_directImageModules_subspaceInclusion :
    PreservesFiniteLimits
      (directImageModules
        (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
        (structureRingSheaf B S hS X)) := by
  have : PreservesLimitsOfSize.{0, 0}
      (directImageModules
        (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
        (structureRingSheaf B S hS X)) :=
    (inverseImageAdjDirectImageModules
      (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
      (structureRingSheaf B S hS X)).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize.preservesFiniteLimits _

/-- **`i_*i⁻¹𝓘 ⟶ i_*i⁻¹𝒪_X` is a kernel of `i_*i⁻¹(i♯)`.**

The first map of the short exact sequence `i⁻¹𝓘 ⟶ i⁻¹𝒪_X ⟶ i⁻¹i_*𝒪_Z` is a kernel of the second
(`CategoryTheory.ShortComplex.ShortExact.fIsKernel`), and the direct image of modules preserves
finite limits, hence kernels. -/
noncomputable def isLimit_kernelFork_directImageDefiningIdeal :
    IsLimit (KernelFork.ofι (directImageDefiningIdealComplex B S hS X Z).f
      (directImageDefiningIdealComplex B S hS X Z).zero) := by
  haveI := preservesFiniteLimits_directImageModules_subspaceInclusion B S hS X Z
  haveI := preservesZeroMorphisms_directImageModules_subspaceInclusion B S hS X Z
  exact KernelFork.mapIsLimit _
    (inverseImageDefiningIdealComplex_shortExact B S hS X Z).fIsKernel
    (directImageModules
      (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
      (structureRingSheaf B S hS X))

/-- **The inclusion `(i_*i⁻¹𝓘)(U) ⟶ (i_*i⁻¹𝒪_X)(U)` is injective** over every object `U` of the
small étale site of `X`.

Evaluation at an object preserves finite limits, so the kernel fork of
`AlgebraicGeometry.Space.isLimit_kernelFork_directImageDefiningIdeal` is a kernel fork of
modules over `U`; this is
`SheafOfModules.injective_val_app_of_isLimit_kernelFork`. -/
theorem injective_directImageDefiningIdeal_f_val_app (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Injective ((directImageDefiningIdealComplex B S hS X Z).f.val.app U) :=
  _root_.SheafOfModules.injective_val_app_of_isLimit_kernelFork
    (isLimit_kernelFork_directImageDefiningIdeal B S hS X Z) U

/-- **A section of `i_*i⁻¹𝒪_X` killed by `i_*i⁻¹(i♯)` comes from `i_*i⁻¹𝓘`.**  Together with
`AlgebraicGeometry.Space.injective_directImageDefiningIdeal_f_val_app` this says that the
sections of `i_*i⁻¹𝓘` over `U` are *exactly* the kernel of the third map on sections. -/
theorem mem_range_directImageDefiningIdeal_f_val_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    {x : (directImageDefiningIdealComplex B S hS X Z).X₂.val.obj U}
    (hx : (directImageDefiningIdealComplex B S hS X Z).g.val.app U x = 0) :
    x ∈ LinearMap.range
      ((directImageDefiningIdealComplex B S hS X Z).f.val.app U).hom :=
  _root_.SheafOfModules.mem_range_val_app_of_isLimit_kernelFork
    (isLimit_kernelFork_directImageDefiningIdeal B S hS X Z) U hx

/-! ### The canonical map `i⁻¹𝓘 ⟶ 𝒞_{Z/X}` and the unit of Stacks 03LU -/

/-- **The canonical map `κ₀ : i⁻¹𝓘 ⟶ 𝒞_{Z/X}`.**  The inverse image of the defining ideal sheaf
maps to the restriction of scalars along `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` of the conormal module
`𝒞_{Z/X} = i^*𝓘 = 𝒪_Z ⊗_{i⁻¹𝒪_X} i⁻¹𝓘`.

By definition it is the unit of the extension/restriction-of-scalars adjunction of Stacks 03CZ
(`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`) at `i⁻¹𝓘`, which is the
second factor of the adjunction of Stacks 03LU; its sections send `x` to `1 ⊗ x`, by
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`.

The type is left to be inferred, for the reason recorded in the implementation notes. -/
noncomputable def conormalExtendScalarsUnit :=
  (extendRestrictScalarsAdjunction (SmallEtale.topology B S hS Z.1.toFunctor)
      (fSharpCommRing (smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z)))
      (inverseImageRingSheaf
        (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
        (structureRingSheaf B S hS X)).property
      (structureRingSheaf B S hS ⟨Z.1.toFunctor, Z.2.1⟩).property).unit.app
    ((inverseImageModules
      (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
      (structureRingSheaf B S hS X)).obj (definingIdealSheaf B S hS X Z).toSheafOfModules)

/-- The unit of the adjunction of Stacks 03LU, at the defining ideal sheaf, is the unit of the
adjunction of Stacks 03D3 followed by the direct image of
`AlgebraicGeometry.Space.conormalExtendScalarsUnit`.

This is `CategoryTheory.Adjunction.comp_unit_app` for
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`, which is by construction the
composite of the adjunction of Stacks 03D3 with the one of Stacks 03CZ. -/
theorem pullbackAdjPushforwardModules_unit_app_definingIdealSheaf :
    (pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS
            (subspaceInclusion B S hS X Z))).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules =
      (inverseImageAdjDirectImageModules
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
          (structureRingSheaf B S hS X)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
        (directImageModules
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
          (structureRingSheaf B S hS X)).map (conormalExtendScalarsUnit B S hS X Z) :=
  Adjunction.comp_unit_app _ _ _

/-- The unit of `AlgebraicGeometry.Space.modulePullbackAdjunction` is the unit of
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` followed by the comparison
`AlgebraicGeometry.Space.modulePushforwardIso` of the two direct images of modules.

The adjunction of Stacks 03LU is the modules-development one transported along that comparison
with `CategoryTheory.Adjunction.ofNatIsoRight`, whose unit is postcomposition with the
comparison; so this is `rfl`. -/
theorem modulePullbackAdjunction_unit_app_eq (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app M =
      (pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS
            (subspaceInclusion B S hS X Z))).unit.app M ≫
        (modulePushforwardIso B S hS (subspaceInclusion B S hS X Z)).hom.app
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj M) :=
  rfl

/-- **The characterisation of `AlgebraicGeometry.Space.conormalExtendScalarsUnit`.**  The unit of
the adjunction of Stacks 03LU at the defining ideal sheaf — the morphism
`𝓘 ⟶ i_*i^*𝓘 = i_*𝒞_{Z/X}` whose transpose is the identity of the conormal module — factors as
the unit of Stacks 03D3 at `𝓘`, followed by the direct image of the canonical map
`κ₀ : i⁻¹𝓘 ⟶ 𝒞_{Z/X}`, followed by the comparison of the two direct images of modules.

The conormal module is written out as `i^*𝓘`, which is what
`AlgebraicGeometry.Space.conormalModule` is by `AlgebraicGeometry.Space.conormalModule_eq`:
asking the elaborator to see through the name inside this equation costs more than the whole
heartbeat budget.

This is `AlgebraicGeometry.Space.pullbackAdjPushforwardModules_unit_app_definingIdealSheaf`
together with `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_app_eq`; both factors are
needed because the adjunction of Stacks 03LU is a transport of the modules-development one. -/
theorem modulePullbackAdjunction_unit_app_definingIdealSheaf :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules =
      (inverseImageAdjDirectImageModules
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
          (structureRingSheaf B S hS X)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
        (directImageModules
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
          (structureRingSheaf B S hS X)).map (conormalExtendScalarsUnit B S hS X Z) ≫
        (modulePushforwardIso B S hS (subspaceInclusion B S hS X Z)).hom.app
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
            (definingIdealSheaf B S hS X Z).toSheafOfModules) :=
  (modulePullbackAdjunction_unit_app_eq B S hS X Z
      (definingIdealSheaf B S hS X Z).toSheafOfModules).trans
    ((congrArg (fun m ↦ m ≫ (modulePushforwardIso B S hS
            (subspaceInclusion B S hS X Z)).hom.app
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
            (definingIdealSheaf B S hS X Z).toSheafOfModules))
        (pullbackAdjPushforwardModules_unit_app_definingIdealSheaf B S hS X Z)).trans
      (Category.assoc _ _ _))

/-! ### The module unit of the ideal sheaf and the module unit of the structure sheaf -/

/-- The first map of `AlgebraicGeometry.Space.directImageDefiningIdealComplex` is `i_*i⁻¹` of
the inclusion `𝓘 ⊆ 𝒪_X`, written at the composite-functor spelling that
`CategoryTheory.NatTrans.naturality` produces. -/
theorem directImageDefiningIdealComplex_f_eq :
    (directImageDefiningIdealComplex B S hS X Z).f =
      (inverseImageModules
            (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
            (structureRingSheaf B S hS X) ⋙
          directImageModules
            (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
            (structureRingSheaf B S hS X)).map (definingIdealSheaf B S hS X Z).ι :=
  rfl

/-- **The module unit is natural in the ideal sheaf.**  The unit `𝓘 ⟶ i_*i⁻¹𝓘` of Stacks 03D3,
followed by `i_*i⁻¹` of the inclusion `𝓘 ⊆ 𝒪_X`, is the inclusion followed by the unit
`𝒪_X ⟶ i_*i⁻¹𝒪_X`.

This is naturality of the unit; it is recorded because it is the half of the comparison of the
two units that the consumer of Stacks 05ZB needs at a section of the ideal sheaf, the other half
being the identification of the module unit of `𝒪_X` with the unit of
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`.

The two composites are written at the spelling `CategoryTheory.NatTrans.naturality` produces;
`AlgebraicGeometry.Space.directImageDefiningIdealComplex_f_eq` identifies the left-hand one with
the first map of `AlgebraicGeometry.Space.directImageDefiningIdealComplex`. -/
theorem unit_comp_map_definingIdealSheaf_ι :
    (inverseImageAdjDirectImageModules
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
          (structureRingSheaf B S hS X)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
        (inverseImageModules
              (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
              (structureRingSheaf B S hS X) ⋙
            directImageModules
              (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
              (structureRingSheaf B S hS X)).map (definingIdealSheaf B S hS X Z).ι =
      (definingIdealSheaf B S hS X Z).ι ≫
        (inverseImageAdjDirectImageModules
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
          (structureRingSheaf B S hS X)).unit.app
          (_root_.SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  ((inverseImageAdjDirectImageModules
      (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
      (structureRingSheaf B S hS X)).unit.naturality (definingIdealSheaf B S hS X Z).ι).symm

/-! ### The sections of `i_*i⁻¹𝒪_X`, and the two units -/

/-- **The sections of the middle term are the sections of `i_*i⁻¹𝒪_X` as a sheaf of rings.**  The
underlying sheaf of sets of the inverse image of sheaves of modules is the inverse image of the
underlying sheaf of sets, and the same for the direct image, so the sections of
`(i_*i⁻¹𝒪_X)` as an `𝒪_X`-module over an object of the small étale site of `X` are *the same
type* as its sections as a sheaf of commutative rings — definitionally, with no transport.

This is what lets a consumer of Stacks 05ZB hand a section of the presheaf of commutative rings
`i_*i⁻¹𝒪_X` to `AlgebraicGeometry.Space.mem_range_directImageDefiningIdeal_f_val_app`. -/
theorem directImageDefiningIdealComplex_X₂_val_obj_eq (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    ((directImageDefiningIdealComplex B S hS X Z).X₂.val.obj U : Type u) =
      ToType (((pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom).obj
          (inverseImageStructureSheaf B S hS
            (subspaceInclusion B S hS X Z))).obj.obj U) :=
  rfl

/-- **The structure projection on underlying sheaves of sets is the structure map.**  The
`𝒪_X`-module map `𝒪_X ⟶ i_*𝒪_Z` of `AlgebraicGeometry.Space.structureProjection` has, as its
underlying morphism of sheaves of sets, the structure map `i♯ : 𝒪_X ⟶ i_*𝒪_Z` of Stacks 03G8.

Both act on sections as `i♯` does, by
`AlgebraicGeometry.Space.structureProjection_val_app_apply`, so the two morphisms agree
sectionwise and hence agree.

This is the first step of the identification of the third map of
`AlgebraicGeometry.Space.directImageDefiningIdealComplex` with the inverse-image form of the
structure map; see the implementation notes. -/
theorem moduleSheafFunctor_map_structureProjection :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (structureProjection B S hS X Z) =
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (structureSharp B S hS (subspaceInclusion B S hS X Z)) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end AlgebraicGeometry.Space

end
