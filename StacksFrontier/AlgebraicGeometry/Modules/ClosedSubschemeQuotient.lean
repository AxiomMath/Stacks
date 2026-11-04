module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.Modules.IdealSheafDataSubmodule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf of a closed subscheme is the quotient of `𝒪_X` by its ideal sheaf

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on `X`, presented as
`AlgebraicGeometry.Scheme.IdealSheafData`, and let `ι = I.subschemeι` be the immersion of the
closed subscheme it cuts out. Pushing the structure sheaf of that subscheme forward gives an
`𝒪_X`-module `ι_* 𝒪_{V(I)}`, and the unit of the free/forgetful pair supplies a canonical map

  `𝒪_X ⟶ ι_* 𝒪_{V(I)}`.

This file proves that map is an **epimorphism** and that the resulting sequence

  `0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)} ⟶ 0`

is short exact, so that `ι_* 𝒪_{V(I)}` *is* the quotient `𝒪_X / I` — exhibited as a colimit, and
not merely compared to it.

Epimorphy is affine-local and already available pointwise: Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_surjective` says the map on sections over
an affine open is surjective, affine opens form a basis
(`AlgebraicGeometry.Scheme.isBasis_affineOpens`), and local surjectivity of a morphism of sheaves
of modules is equivalent to epimorphy by
`Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`. The sections map of
`SheafOfModules.unitToPushforwardObjUnit ι.toRingCatSheafHom` is the scheme morphism's own `app`
on the nose, so no comparison is needed.

The kernel is the ideal sheaf, already built as
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`, whose sections over an affine open are
`I.ideal U` by `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine`.

## Main definitions

* `Stacks.ClosedSubscheme.structureSheafProjection` — the map `𝒪_X ⟶ ι_* 𝒪_{V(I)}`.
* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` — the ideal sheaf of `I` as a
  submodule of `𝒪_X`.
* `Stacks.ClosedSubscheme.idealShortComplex` — the sequence `I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)}`, with
  the ideal sheaf presented as the categorical kernel of the projection.
* `Stacks.ClosedSubscheme.unitSubmoduleIsoKernel` — the identification of that kernel with the
  sectionwise ideal sheaf.
* `Stacks.ClosedSubscheme.isColimitCokernelCofork` — `ι_* 𝒪_{V(I)}` as a cokernel of the
  inclusion of the ideal sheaf.
* `Stacks.ClosedSubscheme.cokernelIso` — the induced isomorphism `𝒪_X / I ≅ ι_* 𝒪_{V(I)}`.

## Main results

* `Stacks.ClosedSubscheme.isLocallySurjective_structureSheafProjection` — local surjectivity.
* `Stacks.ClosedSubscheme.epi_structureSheafProjection` — the projection is an epimorphism.
* `Stacks.ClosedSubscheme.shortExact_idealShortComplex` — `0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)} ⟶ 0` is
  short exact.
* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine` — the ideal sheaf's
  sections over an affine open are `I.ideal U`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` and the two
presentations carry separately declared category instances, so an instance found at one is not
found at the other. Every categorical construction below therefore names its category explicitly
as `(C := X.Modules)`, and `shortExact_idealShortComplex` supplies `Mono` by naming
`CategoryTheory.Limits.equalizer.ι_mono` rather than by synthesis. The bridging scalar-action and
submodule instances of `Completion.IdealPowerQuasicoherent` are re-activated rather than
restated, which is what lets `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine`
be stated at all — the same discipline as `CompletionFunctor.Basic`.

The first term of `idealShortComplex` is the **categorical** kernel of the projection, not the
sectionwise one. That is a deliberate choice: it makes exactness and monomorphy the canonical
kernel sequence (`CategoryTheory.ShortComplex.exact_kernel` and `equalizer.ι_mono`), so that the
whole mathematical content of the short exact sequence is concentrated in `epi_g`, which is the
one new input. Readers wanting the sequence with the ideal sheaf itself in the first spot
compose with `unitSubmoduleIsoKernel`; the two spellings are identified by
`SheafOfModules.Submodule.kernelIso`, and
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine` computes the sections.
Stating the sequence directly at the sectionwise kernel instead would force a
`.ι`-vs-`kernel.ι` type ascription into every statement and buys nothing.

No `@[stacks ...]` attribute is placed. The statement is the defining property of the closed
subscheme attached to a quasi-coherent ideal sheaf rather than a numbered result, and the tagged
statements it is an input to — [Stacks, Tag 0C4J]'s exact sequence and [Stacks, Tag 0C6K] — need
more than this file provides.

This is the structure-sheaf case of [Stacks, Tag 08M3]. It is *not* the general statement, which
asks that `G ⟶ ι_* ι^* G` be an isomorphism for every `𝒪_X`-module `G` annihilated by `I`; the
implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientComparison.Basic` record that general
statement as missing, and it stays missing. What is settled here is the single case `G = 𝒪_X / I`,
which needs no essential-image analysis because `subschemeι_app_surjective` supplies epimorphy
directly.

## References

* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local instance] Stacks.Algebraization.monoSubmoduleι
  Stacks.Algebraization.sectionsModuleΓ Stacks.Algebraization.sectionsModuleΓSheaf
  Stacks.Algebraization.sectionsSMulCommClassΓ

namespace Stacks.ClosedSubscheme

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The canonical map `𝒪_X ⟶ ι_* 𝒪_{V(I)}` from the structure sheaf of `X` to the pushforward
of the structure sheaf of the closed subscheme cut out by `I`. -/
public noncomputable abbrev structureSheafProjection :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

/-- **The projection is locally surjective.** Over an affine open the map on sections is
Mathlib's `subschemeι_app_surjective`, and the affine opens form a basis, so every section of
`ι_* 𝒪_{V(I)}` is in the image after restriction to a neighbourhood of any point. -/
@[ega "I 4.1.7" "special case"]
public theorem isLocallySurjective_structureSheafProjection :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (structureSheafProjection I).val) := by
  constructor
  intro U s
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨V, homOfLE hVU, I.subschemeι_app_surjective ⟨V, hV⟩ _, hxV⟩

/-- **The structure sheaf of a closed subscheme is a quotient of `𝒪_X`.** -/
public instance epi_structureSheafProjection : Epi (structureSheafProjection I) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (isLocallySurjective_structureSheafProjection I)

/-- The sequence `ker ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)}`, with the categorical kernel in the first spot. -/
public noncomputable abbrev idealShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk (C := X.Modules)
    (kernel.ι (C := X.Modules) (structureSheafProjection I))
    (structureSheafProjection I) (kernel.condition (C := X.Modules) _)

/-- **`0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)} ⟶ 0` is short exact.**

Exactness at `𝒪_X` and monomorphy are the canonical kernel sequence; the content is `epi_g`,
which is `epi_structureSheafProjection`. -/
public theorem shortExact_idealShortComplex : (idealShortComplex I).ShortExact where
  exact := ShortComplex.exact_kernel (C := X.Modules) (structureSheafProjection I)
  mono_f := equalizer.ι_mono (C := X.Modules)
  epi_g := epi_structureSheafProjection I

/-- The first term of the sequence is the ideal sheaf: the categorical kernel of the projection
agrees with the sectionwise kernel, whose sections over an affine open are `I.ideal U` by
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine`.

This is `SheafOfModules.Submodule.kernelIso` at the projection. -/
public noncomputable def unitSubmoduleIsoKernel :
    (I.unitSubmodule.toSheafOfModules : X.Modules) ≅
      kernel (C := X.Modules) (structureSheafProjection I) :=
  SheafOfModules.Submodule.kernelIso (structureSheafProjection I)

/-- **`ι_* 𝒪_{V(I)}` is the quotient `𝒪_X / I`**, exhibited as a cokernel of the inclusion of
the ideal sheaf rather than merely compared to one. -/
public noncomputable def isColimitCokernelCofork :
    IsColimit (CokernelCofork.ofπ (C := X.Modules) (structureSheafProjection I)
      (kernel.condition (C := X.Modules) (structureSheafProjection I))) :=
  (shortExact_idealShortComplex I).gIsCokernel

/-- The induced isomorphism `𝒪_X / I ≅ ι_* 𝒪_{V(I)}`, compatible with the two projections out
of `𝒪_X` by `cokernel_π_comp_cokernelIso_hom`. -/
public noncomputable def cokernelIso :
    (cokernel (C := X.Modules) (kernel.ι (C := X.Modules) (structureSheafProjection I))) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitCokernelCofork I)

/-- The isomorphism `cokernelIso` carries the cokernel projection `𝒪_X ⟶ 𝒪_X / I` to
`structureSheafProjection I`. -/
@[simp]
public lemma cokernel_π_comp_cokernelIso_hom :
    cokernel.π (C := X.Modules) (kernel.ι (C := X.Modules) (structureSheafProjection I)) ≫
      (cokernelIso I).hom = structureSheafProjection I :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (isColimitCokernelCofork I) WalkingParallelPair.one

end Stacks.ClosedSubscheme

end
