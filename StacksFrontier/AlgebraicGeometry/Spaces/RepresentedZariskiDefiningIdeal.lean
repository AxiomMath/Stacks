module

public import StacksFrontier.AlgebraicGeometry.ConormalSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushSelfChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedChartZariskiIdeal

/-!
# The defining ideal sheaf of a represented closed subspace, read as the Zariski ideal sheaf

Let `B` be a big fppf site containing a scheme `S` and let `j : R ⟶ V` be a morphism of the big
fppf category over `S`.  Two sheaves of ideals are attached to it.

* The **spaces** one.  `AlgebraicGeometry.Space.kernelIdealSheaf` of the represented morphism
  `yoneda.obj R ⟶ yoneda.obj V` is the kernel of the structure map `♯` of Stacks 03G8, a
  subsheaf of `𝒪` on the small étale site of `yoneda.obj V`; when the morphism of schemes
  underlying `j` is a closed immersion it is the defining ideal sheaf of Stacks 03MB of the
  closed subspace `AlgebraicGeometry.Space.closedSubspaceRange` which `j` cuts out.
* The **schemes** one.  `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` of the
  underlying morphism of schemes is the kernel of `𝒪_V ⟶ j_*𝒪_R` as a submodule of `𝒪_V` on the
  small Zariski site, given over an open `W` by `RingHom.ker (j.app W)`.  This is the sheaf of
  ideals that `Stacks.ConormalSequenceRight.conormalDifferentialTranspose` — the transpose of the
  first arrow of Stacks 01UZ — is a morphism out of.

This file identifies them.  **There is no equality of the two**, and there could not be: they are
submodules of the structure sheaves of *different sites*, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/DefiningIdealSheafSubmoduleBridge.lean` record.  What is
identified is the Zariski **restriction** of the spaces one, which is a submodule of `𝒪_V` on the
same site as the schemes one, and that identification is an honest equality of submodules; and
then, read back up, the spaces one is the associated module of the schemes one.

## Main results

* `chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_eq_definingIdealOfHom` (in the namespace
  `AlgebraicGeometry.Space`): **the equality of submodules of `𝒪_V`, with no hypothesis on
  `j`.**  The Zariski restriction of the kernel ideal sheaf of the represented morphism to the
  identity chart *is*
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` of the underlying morphism of
  schemes.
* `AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_eq_definingIdealOfHom`: the same for
  the defining ideal sheaf of the closed subspace which a represented closed immersion cuts out.
* `AlgebraicGeometry.Space.chartSectionsRingHom_mem_kernelIdealSheaf_selfChart_iff` and
  `AlgebraicGeometry.Space.chartSectionsRingHom_mem_definingIdealAt_selfChart_iff`: **the sections
  comparison with the Zariski restriction eliminated from the statement.**  A regular function on
  a Zariski open `W` lands in the spaces-side sheaf of ideals, over the étale chart which `W` cuts
  out, exactly when `j` kills it on sections over `W`.  Each side is named in its own vocabulary,
  so this is the form a comparison of two morphisms *out of* the two sheaves of ideals reads the
  identification of their sources off.
* `AlgebraicGeometry.Space.representedSmallEtaleRestrictionDefiningIdealSheafIso`: **the defining
  ideal sheaf read on the small étale site of the representing scheme** — it is the associated
  module of `definingIdealOfHom` of the underlying morphism.  This is the spelling in which a
  module enters `AlgebraicGeometry.Space.homEquiv_symm_representedModulePullback`, whose
  transposition is stated at `(representedSmallEtaleModuleEquivalence …).inverse.obj M`.
* `AlgebraicGeometry.Space.representedAssociatedModuleDefiningIdealOfHomIso`: the same
  identification in the forward direction, which is the spelling
  `AlgebraicGeometry.Space.representedAssociatedModuleChartZariskiIdealSheafIso` and
  `AlgebraicGeometry.Space.representedModulePullbackFunctorIso` are stated in.
* `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` and
  `AlgebraicGeometry.Space.representedSmallEtaleRestrictionIdealSheafIso`: the two preceding
  isomorphisms with the Zariski side named as the *categorical* kernel
  `Stacks.ClosedImmersion.idealSheaf`, which is the spelling `Stacks.Conormal.conormalSheaf` of
  Morphisms, Definition 01R2 pulls back.

## Route

Everything used is proved elsewhere.  The equality of submodules is the sections identification
`AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_obj_eq_ker` — the
ideal which a Zariski open `W` inherits from the kernel ideal sheaf is `RingHom.ker (j.app W)` —
fed to `Stacks.AlgebraicGeometry.RegularIdealSheaf.eq_definingIdealOfHom_of_mem_iff`, which says
that a sheaf of ideals of `𝒪_V` cut out sectionwise by vanishing in `j_*𝒪_R` is
`definingIdealOfHom j`.  Both sides are submodules presented pointwise, so no categorical kernel
is entered.

The two isomorphisms are that equality carried across
`AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso` and
`AlgebraicGeometry.Space.representedAssociatedModuleChartZariskiIdealSheafIso`, which exhibit a
quasi-coherent sheaf of ideals of a representable algebraic space as the associated module of its
Zariski restriction; the quasi-coherence is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`, which is why the closed case
is the one the isomorphisms are stated at.  For `AlgebraicGeometry.Space.kernelIdealSheaf` of a
general `j` the tree has quasi-coherence on the site only for a quasi-compact morphism
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernelIdealSheaf`, Stacks 082Z (1)), and that
restriction is real rather than an artefact — see the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedChartZariskiIdeal.lean`.  The *equality* of
submodules above carries no such hypothesis, so the Zariski reading of the sheaf of ideals is
unconditional; only its passage back to the small étale site is not.

## Implementation notes

The proof of the equality is in term mode, and the membership equivalence it supplies is chained
explicitly through
`Stacks.AlgebraicGeometry.RegularIdealSheaf.mem_definingIdealOfHom_iff_app_eq_zero` and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.mem_definingIdealOfHom` rather than left to
definitional unfolding.  Both of those are `Iff.rfl`, so the chain is free; what it buys is that
the statement handed to
`Stacks.AlgebraicGeometry.RegularIdealSheaf.eq_definingIdealOfHom_of_mem_iff` is already in that
lemma's own spelling, instead of asking `isDefEq` to identify `RingHom.ker (j.app W)` with the
vanishing of a component of `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit`.  The same
device, for the same reason, is used throughout
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedChartZariskiIdeal.lean`, whose implementation
notes also record why an open of the identity chart's scheme has to be moved between its
spellings by `exact` into an argument position rather than by `rewrite`.

The two `Stacks.ClosedImmersion.idealSheaf` variants are *not* proved from the two
`definingIdealOfHom` ones: that would compose the equality of submodules with a second bridge
where `AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf` already supplies the
whole comparison in one step.  They are the same construction with that isomorphism in place of
the equality.

No declaration here carries a `stacks` tag.  The identification of a sheaf of ideals with its
Zariski reading is a step of the proof of Stacks 04G2 (1) and of the arrow identification of
Stacks 05ZB, not an assertion of either.

## The compatibility of the étale-site reading with the inclusions

**It is proved**, in
`StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModuleChartPushTranspose.lean`, and the shape it
takes is worth recording here because it is not the most obvious one.

`AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf` comes with
`AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf_hom_comp_ι`, so the
*Zariski* comparison is an identification of sheaves of ideals and not merely of modules; and the
equality of submodules proved here needs no such statement, an equality being compatible with
everything.  For the reading onto the small étale site the earlier section asked for the
behaviour of `AlgebraicGeometry.SmallEtale.associatedModule` on a submodule inclusion
`N.ι : N ⟶ 𝒪` together with the comparison `𝒪^a ≅ 𝒪` of
`AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit`, and the compatibility of the counit
`AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso` with it.  **None of that is
needed**: `AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso` is a
morphism *out of* an associated module, so it is determined by its transpose along the
associated-module adjunction of Stacks 03DX, and the transpose is a morphism of modules on the
small *Zariski* site, where both sides have sections.  That transpose is computed:

* `unit_comp_restrictModule_map_associatedModuleChartZariskiIdealSheafSelfChartIso_hom` (in the
  namespace `AlgebraicGeometry.Space`, written without the prefix so that it fits) — it is
  `AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush`, the comparison of scalars
  `AlgebraicGeometry.Space.chartSectionsRingHom` read on sections, followed by the transport of
  `AlgebraicGeometry.Space.chartPush_selfChart`;
* `associatedModuleChartZariskiIdealSheafSelfChartIso_transpose_val_app_apply` (same namespace)
  — the same on a section: a regular function `r` on a Zariski open `W` lying in the ideal of
  sections there goes to `chartSectionsRingHom … r`.  Since that is a *ring* homomorphism defined
  on all of `Γ(V, W)`, this **is** the compatibility with the inclusions of both sheaves of
  ideals into both structure sheaves.

The counit is never computed: its own transpose is the identity, by the right triangle identity:
`AlgebraicGeometry.SmallEtale.unit_comp_restrictModule_map_associatedModuleRestrictModuleIso_hom`.
So a comparison assembled from the *inverse* of a counit does have a sections description after
all; what cannot be described is its values read directly.

`AlgebraicGeometry.Space.chartSectionsRingHom_mem_definingIdealAt_selfChart_iff` remains the
membership form of the same content, and is what a consumer wants when it needs only that a
section lands in the sheaf of ideals rather than where it goes.

**The morphism-level form is now proved as well**, for the étale-site reading of this file:
`AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso_hom_comp_ι` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedIdealSheafInclusion.lean` says that
`AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` followed by the inclusion of
the defining ideal sheaf is the associated module of `Stacks.ClosedImmersion.idealSheafι`
followed by `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`.  Its Zariski half
carries no hypothesis at all and holds by `rfl` on sections; the passage to the small étale site
of the representing scheme is the transposition recorded above, and the passage to the small
étale site of the algebraic space cancels the counit of the comparison equivalence against
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence_counitIso_app_unit`.

## What is not proved

* The same transpose written at the `definingIdealOfHom` spelling —
  `AlgebraicGeometry.Space.representedSmallEtaleRestrictionDefiningIdealSheafIso` rather than
  `AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso` of the defining
  ideal sheaf.  Mathematically that is the statement above carried across the equality of
  submodules proved in this file, and it **was built and verified**, at a raised heartbeat
  budget; the "What is not proved" section of
  `StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModuleChartPushTranspose.lean` records the
  measurement and the four remedies that do not bring it inside this development's budget.  A
  consumer should use the statements at the defining ideal *sheaf*, where they are
  unconditional, and move to `definingIdealOfHom` by the equality of submodules.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map whose
  kernel the spaces-side sheaf of ideals is.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace.
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX), part (2), the essential
  surjectivity of the associated-module functor which the two isomorphisms rest on.
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), whose first arrow is the
  transpose of a morphism out of the schemes-side sheaf of ideals.
* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), the arrow identification
  this step feeds.
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z), part (1), the
  quasi-coherence the étale-site readings need.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)
  {R : BigFppfOver B S hS} (j : R ⟶ V)

/-! ### The Zariski restriction is the schemes-side defining ideal sheaf -/

/-- **Membership in the Zariski restriction of the kernel ideal sheaf of a represented morphism**:
a regular function on a Zariski open `W` of the representing scheme is a section of the
restriction exactly when the ring map which `j` induces on sections over `W` kills it.

This is `AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_obj_eq_ker`
read as a membership equivalence.  It is stated separately, with its section argument typed at
`Γ(chartScheme (selfChart … V), W)`, because that is the type at which the semiring structure
needed by `RingHom.mem_ker` is found: the section argument of
`Stacks.AlgebraicGeometry.RegularIdealSheaf.eq_definingIdealOfHom_of_mem_iff` is typed at the
sections of `Stacks.RingedSpace.structureSheafModule`, which is only definitionally the same
type, and instance resolution is syntactic. -/
theorem mem_chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_iff
    (W : (chartScheme (selfChart B S hS V)).Opens)
    (s : Γ(chartScheme (selfChart B S hS V), W)) :
    s ∈ (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (kernelIdealSheaf B S hS (representedSpaceMap B S hS j))
          (selfChart B S hS V)).toSubmodule.obj (op W) ↔
      (((BigFppfOver.toScheme B S hS).map j).app W).hom s = 0 :=
  ((congrArg (fun I => s ∈ I)
      (chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_obj_eq_ker B S hS V j W)).to_iff).trans
    RingHom.mem_ker

/-- **The Zariski restriction of the kernel ideal sheaf of a represented morphism is the defining
ideal sheaf of the underlying morphism of schemes**, as submodules of `𝒪_V`, with no hypothesis
on `j`.

`AlgebraicGeometry.Space.chartZariskiIdealSheaf` restricts the spaces-side sheaf of ideals to the
identity chart of `yoneda.obj V`, whose scheme is the scheme underlying `V`, and its ideal of
sections over a Zariski open `W` is `RingHom.ker (j.app W)` by
`AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_obj_eq_ker`; that is
exactly the sectionwise description which determines
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom`.

This is an equality, not an isomorphism, and that is the sharpest form the comparison takes: the
spaces-side sheaf of ideals itself and the schemes-side one are submodules of the structure
sheaves of different sites and are *not* equal, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/DefiningIdealSheafSubmoduleBridge.lean` explain. -/
theorem chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_eq_definingIdealOfHom :
    chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (kernelIdealSheaf B S hS (representedSpaceMap B S hS j)) (selfChart B S hS V) =
      Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
        ((BigFppfOver.toScheme B S hS).map j) :=
  Stacks.AlgebraicGeometry.RegularIdealSheaf.eq_definingIdealOfHom_of_mem_iff
    ((BigFppfOver.toScheme B S hS).map j) _ fun W s =>
      ((mem_chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_iff B S hS V j W s).trans
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.mem_definingIdealOfHom_iff_app_eq_zero
          ((BigFppfOver.toScheme B S hS).map j) W s).symm).trans
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.mem_definingIdealOfHom
        ((BigFppfOver.toScheme B S hS).map j) W s)

/-- **The sections comparison of the two sheaves of ideals, in the vocabulary of both sides.**  A
regular function `r` on a Zariski open `W` of the representing scheme is carried by the comparison
of scalars `AlgebraicGeometry.Space.chartSectionsRingHom` into the sections of
`AlgebraicGeometry.Space.kernelIdealSheaf` over the étale chart which `W` cuts out exactly when
`j` kills `r` on sections.

This is `AlgebraicGeometry.Space.mem_chartZariskiIdealSheaf_iff` read against
`AlgebraicGeometry.Space.mem_chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_iff`, so the
Zariski restriction is eliminated from the statement: the left-hand side mentions only the
spaces-side sheaf of ideals and the right-hand side only `j`.  It is the sections form of the
equality of submodules below, and it is the form a comparison of two morphisms *out of* the two
sheaves of ideals reads the identification of their sources off. -/
theorem chartSectionsRingHom_mem_kernelIdealSheaf_selfChart_iff
    (W : (chartScheme (selfChart B S hS V)).Opens)
    (r : Γ(chartScheme (selfChart B S hS V), W)) :
    chartSectionsRingHom B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (selfChart B S hS V) W r ∈
        (kernelIdealSheaf B S hS (representedSpaceMap B S hS j)).obj
          (op (openChartOfComparison B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V) W)) ↔
      (((BigFppfOver.toScheme B S hS).map j).app W).hom r = 0 :=
  (mem_chartZariskiIdealSheaf_iff B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (kernelIdealSheaf B S hS (representedSpaceMap B S hS j)) (selfChart B S hS V) W
        r).symm.trans
    (mem_chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_iff B S hS V j W r)

variable (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))

/-- **The Zariski restriction of the defining ideal sheaf of the closed subspace cut out by a
represented closed immersion is the defining ideal sheaf of the underlying morphism of schemes.**

This is the preceding
`AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_eq_definingIdealOfHom`
read through `AlgebraicGeometry.Space.kernelIdealSheaf_representedSpaceMap`, which for a closed
immersion identifies the kernel ideal sheaf of the represented morphism with the defining ideal
sheaf of Stacks 03MB of the closed subspace that `j` cuts out.  Closedness is used for nothing
else. -/
theorem chartZariskiIdealSheaf_selfChart_eq_definingIdealOfHom :
    chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)) (selfChart B S hS V) =
      Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
        ((BigFppfOver.toScheme B S hS).map j) :=
  by
  rw [← kernelIdealSheaf_representedSpaceMap B S hS j hj]
  exact chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_eq_definingIdealOfHom B S hS V j

/-- **The sections comparison of the two sheaves of ideals in the closed case.**  A regular
function `r` on a Zariski open `W` of the representing scheme is carried by the comparison of
scalars into `AlgebraicGeometry.Space.definingIdealAt` of the closed subspace which `j` cuts out,
at the étale chart `W` cuts out, exactly when `j` kills `r` on sections.

This is `AlgebraicGeometry.Space.chartSectionsRingHom_mem_kernelIdealSheaf_selfChart_iff` read
through `AlgebraicGeometry.Space.kernelIdealSheaf_representedSpaceMap`.  Both sides of the
comparison are now named in their own vocabulary: on the left the defining ideal of Stacks 03MB,
on the right the ring map on sections whose kernel
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` is. -/
theorem chartSectionsRingHom_mem_definingIdealAt_selfChart_iff
    (W : (chartScheme (selfChart B S hS V)).Opens)
    (r : Γ(chartScheme (selfChart B S hS V), W)) :
    chartSectionsRingHom B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (selfChart B S hS V) W r ∈
        definingIdealAt B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)
          (op (openChartOfComparison B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V) W)) ↔
      (((BigFppfOver.toScheme B S hS).map j).app W).hom r = 0 :=
  by
  rw [← definingIdealSheaf_obj, ← kernelIdealSheaf_representedSpaceMap B S hS j hj]
  exact chartSectionsRingHom_mem_kernelIdealSheaf_selfChart_iff B S hS V j W r

/-! ### The defining ideal sheaf read on the small étale site of the representing scheme -/

/-- **The defining ideal sheaf of a represented closed subspace, read on the small étale site of
the representing scheme, is the associated module of the schemes-side defining ideal sheaf.**

This is the shape in which a module enters
`AlgebraicGeometry.Space.homEquiv_symm_representedModulePullback`, whose transposition is stated
at `(representedSmallEtaleModuleEquivalence … ).inverse.obj M`; so it is the source
identification that a comparison of the spaces-level first arrow of Stacks 05ZA with the
schemes-level first arrow of Stacks 01UZ consumes, the schemes-level one being the transpose of a
morphism out of `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom`.

It is `AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso`, which
exhibits a quasi-coherent sheaf of ideals as the associated module of its Zariski restriction,
with that restriction named by
`AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_eq_definingIdealOfHom`. -/
def representedSmallEtaleRestrictionDefiningIdealSheafIso :
    (representedSmallEtaleModuleEquivalence B S hS V).inverse.obj
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)).toSheafOfModules ≅
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
          ((BigFppfOver.toScheme B S hS).map j)).toSheafOfModules :=
  (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj))
        (isQuasicoherentOnSite_definingIdealSheaf B S hS
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj))).symm ≪≫
    eqToIso (congrArg
      (fun N : (SheafOfModules.unit (chartScheme (selfChart B S hS V)).ringCatSheaf).Submodule =>
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj N.toSheafOfModules)
      (chartZariskiIdealSheaf_selfChart_eq_definingIdealOfHom B S hS V j hj))

/-- **The same identification in the forward direction**: the defining ideal sheaf of a
represented closed subspace is what the schemes-side defining ideal sheaf becomes on the small
étale site of the algebraic space.

This is the spelling `AlgebraicGeometry.Space.representedAssociatedModuleChartZariskiIdealSheafIso`
and `AlgebraicGeometry.Space.representedModulePullbackFunctorIso` are stated in, the latter
reading the inverse image of Stacks 03LU in the forward direction. -/
def representedAssociatedModuleDefiningIdealOfHomIso :
    (representedSmallEtaleModuleEquivalence B S hS V).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj
          (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom
            ((BigFppfOver.toScheme B S hS).map j)).toSheafOfModules) ≅
      (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj)).toSheafOfModules :=
  (representedSmallEtaleModuleEquivalence B S hS V).functor.mapIso
      (eqToIso (congrArg
        (fun N : (SheafOfModules.unit (chartScheme (selfChart B S hS V)).ringCatSheaf).Submodule =>
          (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj N.toSheafOfModules)
        (chartZariskiIdealSheaf_selfChart_eq_definingIdealOfHom B S hS V j hj))).symm ≪≫
    representedAssociatedModuleChartZariskiIdealSheafIso B S hS V
      (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj))
      (isQuasicoherentOnSite_definingIdealSheaf B S hS
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj))

/-! ### The same two readings against the categorical kernel -/

/-- **The defining ideal sheaf of a represented closed subspace, read on the small étale site of
the representing scheme, is the associated module of the categorical ideal sheaf of the
underlying morphism of schemes.**

This is `AlgebraicGeometry.Space.representedSmallEtaleRestrictionDefiningIdealSheafIso` with the
Zariski side named as `Stacks.ClosedImmersion.idealSheaf`, the kernel of `𝒪_V ⟶ j_*𝒪_R` in
`CategoryTheory.SheafOfModules`, which is the spelling `Stacks.Conormal.conormalSheaf` of
Morphisms, Definition 01R2 pulls back.  The passage between the two spellings is
`AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf`, not the equality of
submodules above. -/
def representedSmallEtaleRestrictionIdealSheafIso :
    (representedSmallEtaleModuleEquivalence B S hS V).inverse.obj
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)).toSheafOfModules ≅
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) :=
  (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj))
        (isQuasicoherentOnSite_definingIdealSheaf B S hS
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj))).symm ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).mapIso
      (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj)

/-- **The same identification in the forward direction**, against the categorical ideal sheaf:
the defining ideal sheaf of a represented closed subspace is what
`Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes becomes on the small
étale site of the algebraic space. -/
def representedAssociatedModuleIdealSheafIso :
    (representedSmallEtaleModuleEquivalence B S hS V).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj
          (Stacks.ClosedImmersion.idealSheaf
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)) ≅
      (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj)).toSheafOfModules :=
  (representedSmallEtaleModuleEquivalence B S hS V).functor.mapIso
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).mapIso
        (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj)).symm ≪≫
    representedAssociatedModuleChartZariskiIdealSheafIso B S hS V
      (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj))
      (isQuasicoherentOnSite_definingIdealSheaf B S hS
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj))

end AlgebraicGeometry.Space

end
