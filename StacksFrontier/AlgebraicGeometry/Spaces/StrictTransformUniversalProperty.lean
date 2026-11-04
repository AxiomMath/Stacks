module

public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformShortExact

/-!
# The universal property of the quotient by the sections supported on a subset

Let `X` be an algebraic space over a scheme `S`, let `T` be a subset of its points and let `F` be
an `𝒪_X`-module.  The sections of `F` supported on `T` form a submodule
`AlgebraicGeometry.Space.supportedSectionsSubmodule` (Stacks 0859), and this file identifies its
quotient: the projection `F ⟶ F/Γ_T(F)` is, up to a unique isomorphism, *the* epimorphism out of
`F` which kills only sections supported on `T` and whose target has no nonzero local sections
supported on `T`.

This is the space-level counterpart of the scheme-level
`AlgebraicGeometry.Scheme.Modules.exists_cokernelSupportedSectionsIso` of
`StacksFrontier/AlgebraicGeometry/SupportedQuotient/Basic.lean`, and its specialization to the
strict transform of Stacks 0862 is the counterpart of `Stacks.StrictTransform.exists_iso` of
`StacksFrontier/AlgebraicGeometry/StrictTransform/Basic.lean`.

## Main definitions

* `AlgebraicGeometry.Space.HasNoSectionsSupportedIn`: an `𝒪_X`-module has no nonzero local
  section whose support maps into `T`.
* `AlgebraicGeometry.Space.KernelSectionsSupportedIn`: a morphism of `𝒪_X`-modules kills, over
  every étale chart, only sections whose support maps into `T`.
* `AlgebraicGeometry.Space.supportedQuotientIso`: the isomorphism of the universal property.

## Main results

* `AlgebraicGeometry.Space.kernelSectionsSupportedIn_cokernelProjection`: the projection onto the
  quotient itself kills only sections supported on `T`, so the characterization below is not
  vacuous.
* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_of_injective`: having no sections supported
  on `T` passes along a morphism injective on the sections over every chart, in particular to
  submodules.
* `AlgebraicGeometry.Space.comp_cokernelProjection_eq_zero_iff`: a morphism into `F` dies
  against the projection onto `F/Γ_T(F)` exactly when it dies against any other morphism with
  the two properties above.  This is the kernel comparison the universal property rests on.
* `AlgebraicGeometry.Space.isLimit_kernelFork_supportedSectionsInclusion`: for such a morphism
  `q` the inclusion of `Γ_T(F)` *is* a kernel of `q`.
* `AlgebraicGeometry.Space.exists_supportedQuotientIso`: **the universal property.**  An
  epimorphism `q : F ⟶ Q` which kills only sections supported on `T` and whose target has no
  nonzero sections supported on `T` is the projection onto `F/Γ_T(F)`, compatibly.
* `AlgebraicGeometry.Space.exists_strictTransformSheafIso`: the same statement at the strict
  transform of Stacks 0862 — an epimorphism out of `pr_X^*F` which kills only sections supported
  on the exceptional preimage `|pr_{A'}^{-1}E|` and whose target has no sections supported there
  *is* the strict transform of `F`.

## Implementation notes

The scheme-level argument turns "supported on `Vᶜ`" into the vanishing of a morphism of sheaves
of modules — the unit of the restriction adjunction along the open `V` — and then runs formally
in the abelian category.  No such adjunction is available on the small étale site of an algebraic
space, and none is needed: the two hypotheses of the scheme-level statement,
`Mono ((restrictAdjunction V.ι).unit.app Q)` and `Mono ((restrictFunctor V.ι).map q)`, are
*equivalent* to the two conditions on local sections used here —
`AlgebraicGeometry.Space.HasNoSectionsSupportedIn` and
`AlgebraicGeometry.Space.KernelSectionsSupportedIn` — by
`AlgebraicGeometry.Scheme.Modules.mono_unit_app_of_supportedSections_eq_zero` and
`AlgebraicGeometry.Scheme.Modules.comp_eq_zero_iff_restrictFunctor_map_eq_zero`.  So the
conditions are stated directly on sections, where the small étale site has them, and both are
what a consumer at a chart can actually produce.

Everything then reduces to one equivalence,
`AlgebraicGeometry.Space.comp_cokernelProjection_eq_zero_iff`, and both of its directions are
elementwise.  The direction for the projection is
`AlgebraicGeometry.Space.cokernelπ_val_app_eq_zero_iff_mem` — a section dies in the quotient by a
submodule exactly when it lies in the submodule, which on the small étale site is exactness of
the sections of a short exact sequence of modules at the left-hand place and not a sheafification
statement.  The direction for `q` is the two hypotheses together with
`AlgebraicGeometry.Space.sectionSupportedIn_map`, that a morphism never enlarges the support of a
section.

The isomorphism itself is then the comparison of two colimits: the inclusion of `Γ_T(F)` is a
kernel of `q` (`AlgebraicGeometry.Space.isLimit_kernelFork_supportedSectionsInclusion`, whose
lift comes from the short exact sequence
`AlgebraicGeometry.Space.submoduleQuotientShortComplex`), so `q` is a cokernel of it by
`CategoryTheory.Abelian.epiIsCokernelOfKernel`, and so is the projection.
Both cokernel coforks sit over the same diagram, and
`CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso` compares them.

The module universe is `u`, the universe of the structure rings, as it must be: cokernels of
`𝒪_X`-modules are available only there,
`AlgebraicGeometry.Space.hasCokernel_modules`, whose own implementation notes record why.  The
abelian structure used in the proofs is the one instance search finds,
`SheafOfModules.instAbelian` at that universe.

**No `@[stacks]` attribute is attached, and none should be.**  The universal property of the
supported-sections quotient is not a numbered result of the Stacks Project at either level: the
source uses it inside the proof of Divisors, Lemma 080E, and the scheme-level counterpart
`Stacks.StrictTransform.exists_iso` likewise carries no tag.  What it is for is tags 0864, 0865,
0866 and 0868, each of which the source proves by identifying some other epimorphism out of
`pr_X^*F` with the strict transform.

## What is not proved

That the quotient `F/Γ_T(F)` itself has no nonzero sections supported on `T` — the space-level
counterpart of `AlgebraicGeometry.Scheme.Modules.supportedSections_compl_cokernel_eq_zero` — is
**not** established here, and it is not needed for the universal property.  The scheme-level
proof of it is the one step that genuinely uses the restriction adjunction: the quotient embeds
into the direct image `j_*(F|_V)` of its own restriction to the open complement `V` of `T`, which
has no sections supported on `T`.  For algebraic spaces the second half of that is available —
it is Stacks 085B, `AlgebraicGeometry.Space.pushforward_supportedSectionsSubmodule_range_eq`,
applied to the open subspace with point set `Tᶜ`, whose inverse image of `T` is empty — but the
embedding is not, there being no restriction adjunction along an open subspace on the small étale
site in this library.

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The two conditions on local sections -/

section Conditions

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1))

/-- An `𝒪_X`-module **has no sections supported on `T`** when every local section of it whose
support maps into `T` is zero.

This is the space-level form of the hypothesis `Mono ((restrictAdjunction V.ι).unit.app Q)` of
the scheme-level `AlgebraicGeometry.Scheme.Modules.exists_cokernelSupportedSectionsIso`, to which
it is equivalent by
`AlgebraicGeometry.Scheme.Modules.mono_unit_app_of_supportedSections_eq_zero`. -/
def HasNoSectionsSupportedIn (G : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∀ (W : SmallEtale B S hS X.1) (s : G.val.obj (op W)),
    SectionSupportedIn B S hS X.1 X.2 T G W s → s = 0

/-- A morphism of `𝒪_X`-modules **kills only sections supported on `T`** when every local
section of its source that it sends to zero has support mapping into `T`.

This is the space-level form of the hypothesis `Mono ((restrictFunctor V.ι).map q)` of the
scheme-level `AlgebraicGeometry.Scheme.Modules.exists_cokernelSupportedSectionsIso`: a section
killed by `q` restricts to zero on the open complement of the supported set, hence is supported
there. -/
def KernelSectionsSupportedIn {F Q : Modules.{u, u} B S hS X.1 X.2} (q : F ⟶ Q) : Prop :=
  ∀ (W : SmallEtale B S hS X.1) (s : F.val.obj (op W)),
    q.val.app (op W) s = 0 → SectionSupportedIn B S hS X.1 X.2 T F W s

end Conditions

/-! ### The universal property -/

section Universal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} (T : Set (points B S hS X.1))
    {F Q : Modules.{u, u} B S hS X.1 X.2} (q : F ⟶ Q)

attribute [local instance] mono_submoduleQuotientShortComplex_f

/-- **Having no sections supported on `T` passes to submodules**, and more generally along any
morphism injective on the sections over every étale chart: a morphism never enlarges the support
of a section, so a supported section of the source becomes a supported section of the target,
hence zero, hence was zero. -/
theorem hasNoSectionsSupportedIn_of_injective (φ : F ⟶ Q)
    (hinj : ∀ W : SmallEtale B S hS X.1, Function.Injective (φ.val.app (op W)))
    (hQ : HasNoSectionsSupportedIn B S hS X T Q) :
    HasNoSectionsSupportedIn B S hS X T F := fun W s hs =>
  hinj W ((hQ W _ (sectionSupportedIn_map T φ W s hs)).trans (map_zero _).symm)

/-- A section dies in the quotient by the supported sections exactly when it is supported on `T`. -/
private theorem cokernelπ_val_app_eq_zero_iff_sectionSupportedIn (W : SmallEtale B S hS X.1)
    (s : F.val.obj (op W)) :
    (cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι).val.app (op W) s = 0 ↔
      SectionSupportedIn B S hS X.1 X.2 T F W s :=
  (cokernelπ_val_app_eq_zero_iff_mem F _ (op W) s).trans
    (mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 T F W s)

/-- **The projection onto the quotient by the sections supported on `T` kills only sections
supported on `T`**, so the hypotheses of the universal property are satisfied by the projection
itself.  This is `AlgebraicGeometry.Space.cokernelπ_val_app_eq_zero_iff_mem` read in one
direction. -/
theorem kernelSectionsSupportedIn_cokernelProjection :
    KernelSectionsSupportedIn B S hS X T
      (cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι) := fun W s hs =>
  (cokernelπ_val_app_eq_zero_iff_sectionSupportedIn T W s).mp hs

/-- A morphism whose target has no sections supported on `T` kills the supported sections of its
source: a morphism never enlarges the support of a section. -/
private theorem app_eq_zero_of_mem_supportedSectionsSubmodule
    (hQ : HasNoSectionsSupportedIn B S hS X T Q) (W : SmallEtale B S hS X.1)
    (s : F.val.obj (op W))
    (hs : s ∈ (supportedSectionsSubmodule B S hS X.1 X.2 T F).toSubmodule.obj (op W)) :
    q.val.app (op W) s = 0 :=
  hQ W _ (sectionSupportedIn_map T q W s
    ((mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 T F W s).mp hs))

/-- A morphism whose target has no sections supported on `T` kills the sections of its source
supported on `T`: a morphism never enlarges the support of a section. -/
theorem supportedSectionsInclusion_comp_eq_zero (hQ : HasNoSectionsSupportedIn B S hS X T Q) :
    (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι ≫ q = 0 := by
  ext W x
  exact app_eq_zero_of_mem_supportedSectionsSubmodule T q hQ W.unop _ x.property

/-- **The kernel comparison.**  If `q` kills only sections supported on `T` and its target has
no sections supported on `T`, then a morphism into `F` dies against `q` exactly when it dies
against the projection onto the quotient of `F` by its sections supported on `T`.

Both directions are elementwise.  One is
`AlgebraicGeometry.Space.cokernelπ_val_app_eq_zero_iff_mem` followed by the fact that a morphism
carries supported sections to supported sections; the other is the same equivalence read in the
opposite direction, fed by the hypothesis on the kernel of `q`. -/
theorem comp_cokernelProjection_eq_zero_iff (hq : KernelSectionsSupportedIn B S hS X T q)
    (hQ : HasNoSectionsSupportedIn B S hS X T Q) {A : Modules.{u, u} B S hS X.1 X.2}
    (k : A ⟶ F) :
    k ≫ cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι = 0 ↔ k ≫ q = 0 := by
  constructor
  · intro h
    ext W a
    have hka : (cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι).val.app W
        (k.val.app W a) = 0 :=
      congrArg (fun m : A ⟶ _ => m.val.app W a) h
    exact app_eq_zero_of_mem_supportedSectionsSubmodule T q hQ W.unop _
      ((cokernelπ_val_app_eq_zero_iff_mem F _ W _).mp hka)
  · intro h
    ext W a
    have hka : q.val.app W (k.val.app W a) = 0 :=
      congrArg (fun m : A ⟶ _ => m.val.app W a) h
    exact (cokernelπ_val_app_eq_zero_iff_sectionSupportedIn T W.unop _).mpr (hq W.unop _ hka)

/-- **The inclusion of the sections supported on `T` is a kernel of `q`.**

A morphism into `F` killed by `q` is killed by the projection onto the quotient by the supported
sections, by `AlgebraicGeometry.Space.comp_cokernelProjection_eq_zero_iff`, hence factors
through the supported sections because the short exact sequence of a submodule and its
quotient is exact at the middle place; the factorization is unique because the inclusion is a
monomorphism. -/
def isLimit_kernelFork_supportedSectionsInclusion (hq : KernelSectionsSupportedIn B S hS X T q)
    (hQ : HasNoSectionsSupportedIn B S hS X T Q) :
    IsLimit (KernelFork.ofι (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι
      (supportedSectionsInclusion_comp_eq_zero T q hQ)) := by
  have hses := shortExact_submoduleQuotientShortComplex B S hS X F
    (supportedSectionsSubmodule B S hS X.1 X.2 T F)
  refine KernelFork.IsLimit.ofι' _ _ fun k hk =>
    ⟨hses.exact.lift k ((comp_cokernelProjection_eq_zero_iff T q hq hQ k).mpr hk),
      hses.exact.lift_f k _⟩

/-- **The isomorphism of the universal property.**  An epimorphism `q : F ⟶ Q` which kills only
sections supported on `T` and whose target has no sections supported on `T` identifies `Q` with
the quotient of `F` by its sections supported on `T`.

The inclusion of the supported sections is a kernel of `q`, so `q` is a cokernel of it by
`CategoryTheory.Abelian.epiIsCokernelOfKernel`; the projection onto the quotient is another, and
the two colimits are compared. -/
def supportedQuotientIso (hqe : Epi q) (hq : KernelSectionsSupportedIn B S hS X T q)
    (hQ : HasNoSectionsSupportedIn B S hS X T Q) :
    cokernel (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι ≅ Q :=
  have := hqe
  (cokernelIsCokernel (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel _ (isLimit_kernelFork_supportedSectionsInclusion T q hq hQ))

/-- `AlgebraicGeometry.Space.supportedQuotientIso` is compatible with the projection onto the
quotient and with `q`. -/
theorem cokernelProjection_comp_supportedQuotientIso_hom (hqe : Epi q)
    (hq : KernelSectionsSupportedIn B S hS X T q)
    (hQ : HasNoSectionsSupportedIn B S hS X T Q) :
    cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι ≫
        (supportedQuotientIso T q hqe hq hQ).hom = q :=
  have := hqe
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι)
    (Abelian.epiIsCokernelOfKernel _ (isLimit_kernelFork_supportedSectionsInclusion T q hq hQ))
    WalkingParallelPair.one

/-- **The universal property of the quotient by the sections supported on `T`.**  An
epimorphism out of `F` which kills only the local sections supported on `T` and whose target has
no nonzero local sections supported on `T` *is* the projection onto the quotient of `F` by its
sections supported on `T`, compatibly.

This is the space-level counterpart of the scheme-level
`AlgebraicGeometry.Scheme.Modules.exists_cokernelSupportedSectionsIso`. -/
theorem exists_supportedQuotientIso (hqe : Epi q)
    (hq : KernelSectionsSupportedIn B S hS X T q)
    (hQ : HasNoSectionsSupportedIn B S hS X T Q) :
    ∃ e : cokernel (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι ≅ Q,
      cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι ≫ e.hom = q :=
  ⟨supportedQuotientIso T q hqe hq hQ,
    cokernelProjection_comp_supportedQuotientIso_hom T q hqe hq hQ⟩

end Universal

/-! ### The universal property of the strict transform of a module -/

section StrictTransform

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A) (E : Subfunctor A'.1)
    (F : Modules.{u, u} B S hS X.1 X.2)

/-- **The universal property of the strict transform of a module.**  In the situation of Stacks
0862 — a morphism `b : A' ⟶ A` of algebraic spaces over `S` together with a subspace `E ⊆ A'`,
and an algebraic space `f : X ⟶ A` over `A` — let `F` be an `𝒪_X`-module.  An epimorphism out of
`pr_X^*F` which kills only the local sections supported on the exceptional preimage
`|pr_{A'}^{-1}E|`, and whose target has no nonzero local sections supported there, *is* the
quotient map onto the strict transform of `F`, compatibly.

This is the space-level counterpart of `Stacks.StrictTransform.exists_iso`.  It is the
instance of `AlgebraicGeometry.Space.exists_supportedQuotientIso` at the base change
`X ×_A A'`, the pullback `pr_X^*F` and the exceptional preimage, and carries no `@[stacks]`
attribute for the reason recorded in the module documentation. -/
theorem exists_strictTransformSheafIso
    {Q : Modules.{u, u} B S hS (strictTransformPullback B S hS f b).1
      (strictTransformPullback B S hS f b).2}
    (q : (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F ⟶ Q)
    (hqe : Epi q)
    (hq : KernelSectionsSupportedIn B S hS (strictTransformPullback B S hS f b)
      (exceptionalPreimageSet B S hS f b E) q)
    (hQ : HasNoSectionsSupportedIn B S hS (strictTransformPullback B S hS f b)
      (exceptionalPreimageSet B S hS f b E) Q) :
    ∃ e : strictTransformSheaf B S hS f b E F ≅ Q,
      strictTransformSheafQuotient B S hS f b E F ≫ e.hom = q :=
  exists_supportedQuotientIso (exceptionalPreimageSet B S hS f b E) q hqe hq hQ

end StrictTransform

end AlgebraicGeometry.Space

end
