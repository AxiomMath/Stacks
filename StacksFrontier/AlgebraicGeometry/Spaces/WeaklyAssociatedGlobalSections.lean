module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedSupport

/-!
# Sections of a module on an algebraic space supported outside an étale chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `F` be an
`𝒪_X`-module and let `U` be an étale chart of `X` whose points cover every weakly associated
point of `F`.  This file builds the subsheaf `AlgebraicGeometry.Space.outsideChartSubmodule` of
sections of `F` whose support maps outside the image of `|U| → |X|`, shows that a global section
of `F` dying on `U` is a global section of it, and shows that it has no weakly associated point:

* its weakly associated points are among those of `F`, because it is a subsheaf (Stacks 0CTZ);
* its support misses the image of `|U| → |X|`, because every one of its local sections has
  support there by construction, and `WeakAss ⊆ Supp` (Stacks 0CTY).

These are the inputs of the proof of Stacks 0CUP in
`StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedSectionsInjective`.

## Main definitions

* `AlgebraicGeometry.Space.outsideChartSubmodule` is the subsheaf of sections of `F` supported
  outside the image of the points of an étale chart.
* `AlgebraicGeometry.Space.outsideChartSection` reads a global section dying on the chart as a
  global section of that subsheaf.
* `AlgebraicGeometry.Space.submoduleQuotientShortComplex` is the short exact sequence
  `0 → N → F → F/N → 0` of a submodule of an `𝒪_X`-module.

## Main results

* `AlgebraicGeometry.Space.range_chartSchemeToPoints`: the image of the points of the scheme of
  an étale chart in `|X|` is the image of the points of the chart's representable presheaf.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_submodule_subset`: **Stacks 0CTZ** for a
  submodule — the weakly associated points of a submodule of `F` are weakly associated to `F`.
* `AlgebraicGeometry.Space.sectionSupportedIn_compl_range_of_eval_eq_zero`: a global section
  dying on an étale chart has, on every chart, support outside the image of the first chart.
* `AlgebraicGeometry.Space.supportOfSheaf_supportedSectionsSubmodule_subset`: the support of the
  subsheaf of sections supported in a subset is contained in that subset.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_outsideChartSubmodule_eq_empty`: if every
  weakly associated point of `F` lies in the image of `|U| → |X|`, then the subsheaf of sections
  supported outside that image has no weakly associated point at all.

## Implementation notes

The module universe is the universe `u` of the schemes: the abelian structure of
`AlgebraicGeometry.Space.Modules`, which the quotient of a submodule needs, is available there.
The statement of Stacks 0CTZ used below is universe-polymorphic; it is its packaging as a short
exact sequence that forces `u`.

Stacks 0CUQ — that a point outside the image of a quasi-compact and quasi-separated morphism is
not weakly associated to a direct image — is not proved here and carries no attribute.

## References

* [Stacks Project, Tag 0CTZ](https://stacks.math.columbia.edu/tag/0CTZ)
* [Stacks Project, Tag 0CTY](https://stacks.math.columbia.edu/tag/0CTY)
* [Stacks Project, Tag 0CUQ](https://stacks.math.columbia.edu/tag/0CUQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The image of an étale chart on points -/

/-- The image of `|U| → |X|`, read on the points of the scheme underlying the étale chart `U`,
is the image of the points of the representable presheaf of the chart.

The two differ by the bijection of Stacks 03BX(1) between the points of a represented presheaf
and the points of the representing scheme, which
`AlgebraicGeometry.Space.chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm` exhibits. -/
theorem range_chartSchemeToPoints (U : SmallEtale B S hS X.1) :
    Set.range (chartSchemeToPoints B S hS X.1 U) =
      Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom) := by
  rw [show chartSchemeToPoints B S hS X.1 U =
      (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom) ∘
        (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm from
    funext fun x => chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 U x,
    Set.range_comp]
  rw [(pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm.surjective.range_eq,
    Set.image_univ]

/-! ### Weakly associated points and supports of a submodule -/

/-- The short exact sequence `0 → N → F → F/N → 0` of a submodule `N` of an `𝒪_X`-module `F`,
with `F/N` the cokernel of the inclusion. -/
def submoduleQuotientShortComplex (F : Modules.{u, u} B S hS X.1 X.2) (N : F.Submodule) :
    ShortComplex (Modules.{u, u} B S hS X.1 X.2) where
  X₁ := N.toSheafOfModules
  X₂ := F
  X₃ := cokernel N.ι
  f := N.ι
  g := cokernel.π N.ι
  zero := cokernel.condition N.ι

/-- `AlgebraicGeometry.Space.submoduleQuotientShortComplex` is short exact: the inclusion of a
submodule is a monomorphism and, the `𝒪_X`-modules being an abelian category, it is the kernel
of its own cokernel. -/
theorem shortExact_submoduleQuotientShortComplex (F : Modules.{u, u} B S hS X.1 X.2)
    (N : F.Submodule) : (submoduleQuotientShortComplex B S hS X F N).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel (submoduleQuotientShortComplex B S hS X F N)
    (Abelian.monoIsKernelOfCokernel (f := N.ι) _ (colimit.isColimit _))
  mono_f := inferInstanceAs (Mono N.ι)
  epi_g := inferInstanceAs (Epi (cokernel.π N.ι))

/-- **Stacks 0CTZ for a submodule.** Every weakly associated point of a submodule of an
`𝒪_X`-module is weakly associated to the ambient module. -/
theorem weaklyAssociatedPoints_submodule_subset (F : Modules.{u, u} B S hS X.1 X.2)
    (N : F.Submodule) :
    weaklyAssociatedPoints B S hS X N.toSheafOfModules ⊆
      weaklyAssociatedPoints B S hS X F :=
  weaklyAssociatedPoints_subset_of_shortExact B S hS X
    (submoduleQuotientShortComplex B S hS X F N)
    (shortExact_submoduleQuotientShortComplex B S hS X F N)

/-- The support of a section of a submodule is contained in the support of the same section
read in the ambient module: a restriction killing the section in the ambient module kills it in
the submodule, the inclusion being injective on sections. -/
theorem supportOfSection_submodule_subset (F : Modules.{u, u} B S hS X.1 X.2)
    (N : F.Submodule) (W : SmallEtale B S hS X.1)
    (σ : N.toSheafOfModules.val.obj (op W)) :
    supportOfSection B S hS X.1
        (moduleAddSheaf B S hS X.1 X.2 N.toSheafOfModules) W σ ⊆
      supportOfSection B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) W
        (N.ι.val.app (op W) σ) := by
  refine Set.compl_subset_compl.mpr ?_
  rintro x ⟨V, f, hzero, y, hy⟩
  refine ⟨V, f, ?_, y, hy⟩
  exact Subtype.ext ((PresheafOfModules.naturality_apply N.ι.val f.op σ).trans hzero)

/-- The support of the subsheaf of sections supported in a subset `T` of `|X|` is contained in
`T`: a point of the support carries a section with a nonzero germ at some geometric point above
it, and the support of that section contains the corresponding chart point, which therefore
maps into `T`. -/
theorem supportOfSheaf_supportedSectionsSubmodule_subset
    (T : Set (points B S hS X.1)) (F : Modules.{u, u} B S hS X.1 X.2) :
    supportOfSheaf B S hS X.1 (moduleAddSheaf B S hS X.1 X.2
        (supportedSectionsSubmodule B S hS X.1 X.2 T F).toSheafOfModules) ⊆ T := by
  intro x hx
  set NN := supportedSectionsSubmodule B S hS X.1 X.2 T F with hNN
  obtain ⟨xbar, hxbar, V, σ, hσ⟩ :=
    (mem_supportOfSheaf_iff_exists_geometricModuleStalkGerm_ne_zero B S hS X
      NN.toSheafOfModules x).mp hx
  have hpt : (neighborhoodPoint B S hS X.1 V).image ∈
      supportOfSection B S hS X.1
        (moduleAddSheaf B S hS X.1 X.2 NN.toSheafOfModules) V.chart σ := fun hc =>
    hσ ((geometricModuleStalkGerm_eq_zero_iff_mem_largestOpenZeroLocus B S hS X
      NN.toSheafOfModules xbar V σ).mpr hc)
  have hsup : SectionSupportedIn B S hS X.1 X.2 T F V.chart (NN.ι.val.app (op V.chart) σ) :=
    (mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 T F V.chart _).mp σ.2
  have hmem := hsup (supportOfSection_submodule_subset B S hS X F NN V.chart σ hpt)
  rw [Set.mem_preimage, neighborhoodPoint_image B S hS X.1 V, hxbar] at hmem
  exact hmem

/-! ### Sections dying on an étale chart -/

/-- A global section of an `𝒪_X`-module vanishing on the étale chart `U` has, over every étale
chart `W`, support outside the image of the points of `U`.

A chart point of `W` whose image in `|X|` is the image of a point of `U` is the image of a point
of a common refinement of `U` and `W` (`AlgebraicGeometry.Space.exists_common_chart`), the
section restricts to zero on that refinement because it already does on `U`, and the support of
a restriction is the preimage of the support. -/
theorem sectionSupportedIn_compl_range_of_eval_eq_zero
    (F : Modules.{u, u} B S hS X.1 X.2) (U : SmallEtale B S hS X.1)
    (s : F.sections) (hs : s.eval (op U) = 0) (W : SmallEtale B S hS X.1) :
    SectionSupportedIn B S hS X.1 X.2
      (Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom))ᶜ F W
      (s.eval (op W)) := by
  intro w hw hmem
  obtain ⟨u, hu⟩ := hmem
  obtain ⟨V, a, b, r, -, hb⟩ := exists_common_chart B S hS X.1 U W u w hu
  have h1 : F.val.map b.op (s.eval (op W)) = s.eval (op V) :=
    PresheafOfModules.sections_property s b.op
  have h2 : F.val.map a.op (s.eval (op U)) = s.eval (op V) :=
    PresheafOfModules.sections_property s a.op
  have hV : F.val.map b.op (s.eval (op W)) = 0 := by
    refine h1.trans (h2.symm.trans ?_)
    rw [hs]
    exact map_zero _
  have hz : (moduleAddSheaf B S hS X.1 X.2 F).obj.map b.op (s.eval (op W)) = 0 := hV
  have h0 : supportOfSection B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) V
      ((moduleAddSheaf B S hS X.1 X.2 F).obj.map b.op (s.eval (op W))) = ∅ :=
    (congrArg (supportOfSection B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) V) hz).trans
      (supportOfSection_zero B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) V)
  refine Set.eq_empty_iff_forall_notMem.mp h0 r ?_
  rw [supportOfSection_restrict B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) W
    (s.eval (op W)) V b]
  exact Set.mem_preimage.mpr (hb ▸ hw)

/-- The subsheaf of sections of an `𝒪_X`-module whose support lies outside the image of the
points of an étale chart `U`.  In the proof of Stacks 0CUP it contains the image of the morphism
`𝒪_X → F` determined by a global section dying on `U`. -/
abbrev outsideChartSubmodule (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1) : F.Submodule :=
  supportedSectionsSubmodule B S hS X.1 X.2
    (Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom))ᶜ F

/-- A global section of `F` vanishing on the étale chart `U`, read as a global section of
`AlgebraicGeometry.Space.outsideChartSubmodule`: over every chart it is supported outside the
image of the points of `U` by
`AlgebraicGeometry.Space.sectionSupportedIn_compl_range_of_eval_eq_zero`. -/
def outsideChartSection (F : Modules.{u, u} B S hS X.1 X.2) (U : SmallEtale B S hS X.1)
    (s : F.sections) (hs : s.eval (op U) = 0) :
    (outsideChartSubmodule B S hS X F U).toSheafOfModules.sections :=
  PresheafOfModules.sectionsMk
    (fun W => ⟨s.eval W, (mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 _ F W.unop
      (s.eval W)).mpr (sectionSupportedIn_compl_range_of_eval_eq_zero B S hS X F U s hs W.unop)⟩)
    (fun {_ _} f => Subtype.ext (PresheafOfModules.sections_property s f))

/-! ### The subsheaf of sections supported outside a chart -/

/-- If every weakly associated point of `F` lies in the image of the points of the étale chart
`U`, then the subsheaf of sections of `F` supported outside that image has no weakly associated
point.

Such a point would be weakly associated to `F` because the subsheaf is a submodule
(Stacks 0CTZ), hence would lie in the image of the points of `U`; but it would also lie in the
support of the subsheaf (Stacks 0CTY), hence outside that image. -/
theorem weaklyAssociatedPoints_outsideChartSubmodule_eq_empty
    (F : Modules.{u, u} B S hS X.1 X.2) (U : SmallEtale B S hS X.1)
    (hU : weaklyAssociatedPoints B S hS X F ⊆ Set.range (chartSchemeToPoints B S hS X.1 U)) :
    weaklyAssociatedPoints B S hS X
      (outsideChartSubmodule B S hS X F U).toSheafOfModules = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  refine supportOfSheaf_supportedSectionsSubmodule_subset B S hS X _ F
    (weaklyAssociatedPoints_subset_supportOfSheaf B S hS X _ hx) ?_
  rw [← range_chartSchemeToPoints]
  exact hU (weaklyAssociatedPoints_submodule_subset B S hS X F _ hx)

end AlgebraicGeometry.Space

end
