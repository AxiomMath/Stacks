module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSchemeModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleSheafCondition

/-!
# Essential surjectivity of `M ↦ Mᵃ` on the slice at an affine chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `W` be
an étale chart of `X` whose underlying scheme `T` is affine.  The slice of the small étale site
of `X` at `W` carries two constructions of the associated module of a quasi-coherent
`𝒪_T`-module `G`:

* `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`, the module `Mᵃ` of
  [Stacks, Tag 03DU] built *by its sections* — `Stacks.Sites.siteAssociatedModule` of the
  presheaf of pullback sections of Tag 03DS, restricted along the slice projection;
* `AlgebraicGeometry.SmallEtale.associatedModule` on the small étale site of the scheme `T`,
  built as the *pullback* `CategoryTheory.SheafOfModules.pullback` along the morphism of ringed
  sites `(T_étale, 𝒪) → (T_Zar, 𝒪_T)`, read across the comparison of [Stacks, Tag 04M0].

**This file identifies them, and thereby discharges the essential-surjectivity clause of
Descent, Proposition 03DX (2) on that slice.**  The identification is what the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleEssSurj.lean` recorded as
the one missing step; with it, the module on the chart's scheme produced by
`AlgebraicGeometry.Space.exists_isQuasicoherent_iso_over_of_isAffine` — which comes out as a
*pullback* `Gᵃ` — is an `Mᵃ` in the slice's sections spelling.

Three proved inputs compose, and nothing is granted:

* `AlgebraicGeometry.Space.exists_isQuasicoherent_iso_over_of_isAffine`: the restriction of a
  quasi-coherent `𝒪_X`-module to the small étale site of an affine chart is
  `AlgebraicGeometry.Space.representedAssociatedModule` of a quasi-coherent module on the
  chart's scheme;
* [Stacks, Tag 070S] part (2), `AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`
  and `AlgebraicGeometry.SmallEtale.isIso_sheafification_map_sectionsComparison`: on the small
  étale site of a *scheme* the pullback description of `Gᵃ` is the sections description.  It is
  assembled here at the level of sheaves of modules, as
  `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules`;
* `AlgebraicGeometry.Space.chartModuleReindexEquivalence` and
  `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`: reindexing along the two
  comparisons of Tag 04M0 are equivalences of the categories of sheaves of modules, so an
  isomorphism established upstairs descends to the slice.

## Main results

* `Stacks.Sites.pushforward_associatedModulePresheaf` and
  `Stacks.Sites.pushforward_siteAssociatedModule`: reading the presheaf of modules of Tag 03DS
  along a functor of sites of schemes over `T` gives the presheaf of modules of Tag 03DS at the
  composite functor — on the nose.
* `AlgebraicGeometry.SmallEtale.sectionsSheafOfModules` and
  `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules`: **Tag 070S (2) at
  the level of sheaves of modules on the small étale site of a scheme.**
* `AlgebraicGeometry.Space.chartLocalization_comp_sliceToOver`: the two readings of the slice at
  a chart as a site of schemes over the chart's scheme agree.
* `AlgebraicGeometry.Space.chartModuleReindex_sliceAssociatedModule`: **the identification of
  the slice construction of `Gᵃ` with the sections sheaf on the small étale site of the chart's
  scheme.**
* `AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite`: **the
  essential-surjectivity clause of Descent, Proposition 03DX (2) on the slice at an affine
  chart, with no hypothesis** — the hypothesis `hEss` of
  `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj` and of
  `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_of_essSurj`.
* `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_unconditional`:
  **the uniform form of Descent, Proposition 03DW on the small étale site of an algebraic space,
  with no hypothesis.**

## Implementation notes

The identification cannot be a single `rfl`.  Elaborating it directly exhausts the heartbeat
budget, and the kernel exhausts its own budget on the `CategoryTheory.SheafOfModules` wrapper, so
the proof is split into three pieces each of which is cheap at its own level of abstraction:
`Stacks.Sites.pushforward_associatedModulePresheaf` is the one real `rfl` and is stated at
abstract sites, a scheme and a quasi-coherent module;
`AlgebraicGeometry.Space.chartModuleReindexEquivalence_functor_obj_val` and
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence_functor_obj_val` project the
reindexing equivalences onto presheaf-level pushforwards at an *abstract* module, so that the
presheaf of Tag 03DS is never unfolded; and `Stacks.SheafOfModules.eq_of_val_eq` lifts the
resulting equality of presheaves of modules to the sheaves, the sheaf condition being a
proposition.

The two composites to `CategoryTheory.Over T` are equal but not definitionally equal: equality of
functors from pointwise agreement is `CategoryTheory.Functor.hext`, which is function
extensionality, so the comparison needs that propositional equality.  Rewriting with it is
refused — the type `CategoryTheory.PresheafOfModules (Stacks.Sites.structurePresheaf T _)`
depends on the functor and the motive is not type correct.  The way through is
`Stacks.Sites.associatedModulePresheaf_heq_of_eq`, a heterogeneous congruence proved by `subst`:
at the point of use both sides have already been seen to live in one type, so `eq_of_heq`
applies.

No `@[stacks]` attribute is claimed here.  Tag 03DX (2) is an equivalence of categories and only
its essential-surjectivity clause is proved, on one slice of one site; Tag 070S quantifies over
five topologies and two sites, and its small étale part (2) is registered already at
`AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`; Tag 04M0 is registered at
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`; and Tag 03DW, whose uniform form is
discharged here, is a statement about every epimorphism of modules on every algebraic space,
which is more than the one shape this file proves.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v' u' w m

namespace Stacks.SheafOfModules

/-- Two sheaves of modules with the same underlying presheaf of modules are equal: the sheaf
condition is a proposition. -/
theorem eq_of_val_eq {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : _root_.SheafOfModules.{m} R} (h : M.val = N.val) :
    M = N := by
  obtain ⟨Mv, hMv⟩ := M
  obtain ⟨Nv, hNv⟩ := N
  cases h
  rfl

end Stacks.SheafOfModules

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (T : Scheme.{u}) (G : T.Modules) [G.IsQuasicoherent]
    {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over T)
    {C' : Type (u + 1)} [Category.{u} C'] (v : C' ⥤ C)

/-- **The restriction of the presheaf of modules `Gᵃ` along a functor of sites of schemes.**
Reading `Gᵃ` on the source site, with the identity comparison of structure presheaves, gives
`Gᵃ` formed at the composite functor to the schemes over `T`. -/
theorem pushforward_associatedModulePresheaf :
    (PresheafOfModules.pushforward.{u}
        (𝟙 (v.op ⋙ structurePresheaf T toOver))).obj
        (associatedModulePresheaf T G toOver) =
      associatedModulePresheaf T G (v ⋙ toOver) :=
  rfl

/-- **The presheaf of modules `Gᵃ` depends only on the functor to the schemes over `T`.**  Two
equal functors give the same presheaf of modules, heterogeneously: the type
`CategoryTheory.PresheafOfModules (structurePresheaf T _)` depends on the functor, so the
statement cannot be a plain equality, and `Eq.mpr` on the structure presheaf is exactly what the
consumers do not want to carry. -/
theorem associatedModulePresheaf_heq_of_eq {w w' : C' ⥤ Over T} (hw : w = w') :
    HEq (associatedModulePresheaf T G w) (associatedModulePresheaf T G w') := by
  subst hw
  rfl

variable (J : GrothendieckTopology C)
    (hR : Presheaf.IsSheaf J (structurePresheaf T toOver))
    (hM : Presheaf.IsSheaf J (associatedPresheaf T G toOver))
    (J' : GrothendieckTopology C') [v.IsContinuous J' J]

/-- **The restriction of `Gᵃ` along a continuous functor of sites of schemes over `T` is `Gᵃ`
formed on the source site.** -/
theorem pushforward_siteAssociatedModule
    (hM' : Presheaf.IsSheaf J' (associatedPresheaf T G (v ⋙ toOver))) :
    (_root_.SheafOfModules.pushforward.{u}
        (𝟙 ((v.sheafPushforwardContinuous RingCat.{u} J' J).obj
          (siteStructureSheaf T toOver J hR)))).obj
        (siteAssociatedModule T G toOver J hR hM) =
      ⟨associatedModulePresheaf T G (v ⋙ toOver), hM'⟩ :=
  Stacks.SheafOfModules.eq_of_val_eq (pushforward_associatedModulePresheaf T G toOver v)

end Stacks.Sites

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : S.Modules) [F.IsQuasicoherent]

/-- **`Fᵃ` on the small étale site of a scheme, read by its sections.**  The pullback-sections
presheaf of modules of Tag 03DS on the small étale site, with the sheaf condition of Tag 03DT
there; no sheafification occurs. -/
def sectionsSheafOfModules : SheafOfModules.{u} (structureSheaf B S hS) :=
  ⟨sectionsPresheafOfModules B S hS F, isSheaf_sectionsPresheafOfModules B S hS F⟩

/-- **Stacks 070S (2) at the level of sheaves of modules.**  The associated module of a
quasi-coherent `𝒪_S`-module on the small étale site of `S` — the pullback along the morphism of
ringed sites `(S_étale, 𝒪) → (S_Zar, 𝒪_S)` — is the pullback-sections sheaf of Tag 03DS. -/
def associatedModuleIsoSectionsSheafOfModules :
    (associatedModule B S hS).obj F ≅ sectionsSheafOfModules B S hS F :=
  (associatedModuleSheafificationIso B S hS).app F ≪≫
    @asIso _ _ _ _ _ (isIso_sheafification_map_sectionsComparison B S hS F) ≪≫
      (asIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheaf B S hS).obj)).counit)).app (sectionsSheafOfModules B S hS F)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (W : SmallEtale B S hS X.1)

/-- The two readings of the slice at a chart as a site of schemes over the chart's
scheme agree. -/
theorem chartLocalization_comp_sliceToOver :
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor ⋙
      SmallEtale.sliceToOver B S hS X.1 W =
    (representedSmallEtaleEquivalence B S hS ((SmallEtale.toOver B S hS X.1).obj W)).functor ⋙
      _root_.AlgebraicGeometry.SmallEtale.toOver (associatedBigEtaleSite B) (chartScheme W)
        ((SmallEtale.toOver B S hS X.1).obj W).left.property :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- Reading a module on the slice at a chart across the comparison of Tag 04M0 restricts its
presheaf of modules along the comparison functor, with the identity comparison of structure
presheaves. -/
theorem chartModuleReindexEquivalence_functor_obj_val
    (Q : SheafOfModules.{u} ((structureRingSheaf B S hS X).over W)) :
    ((chartModuleReindexEquivalence B S hS X W).functor.obj Q).val =
      (PresheafOfModules.pushforward.{u}
        (𝟙 ((SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor.op ⋙
          Stacks.Sites.structurePresheaf (chartScheme W)
            (SmallEtale.sliceToOver B S hS X.1 W)))).obj Q.val :=
  rfl

/-- Reading a module on the small étale site of the scheme underlying an object of the big fppf
site across the comparison with the small étale site of the represented algebraic space
restricts its presheaf of modules along the comparison functor. -/
theorem representedSmallEtaleModuleEquivalence_functor_obj_val
    (U : BigFppfOver B S hS)
    (P : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj P).val =
      (PresheafOfModules.pushforward.{u}
        (𝟙 ((representedSmallEtaleEquivalence B S hS U).functor.op ⋙
          Stacks.Sites.structurePresheaf ((BigFppfOver.toScheme B S hS).obj U)
            (_root_.AlgebraicGeometry.SmallEtale.toOver (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property)))).obj P.val :=
  rfl

/-- **The two constructions of `Gᵃ` at an étale chart agree.**  Reading the module `Gᵃ` of
Tag 03DU formed on the slice of the small étale site of `X` at the chart `W` across the
comparison of Tag 04M0 gives the pullback-sections sheaf of `G` on the small étale site of the
chart's scheme, read across the comparison of the small étale site of the represented algebraic
space with that of the scheme.

Both are the presheaf of modules of Tag 03DS restricted along a functor to the schemes over the
chart's scheme, and the two functors agree by
`AlgebraicGeometry.Space.chartLocalization_comp_sliceToOver`. -/
theorem chartModuleReindex_sliceAssociatedModule (G : (chartScheme W).Modules)
    [G.IsQuasicoherent] :
    (chartModuleReindexEquivalence B S hS X W).functor.obj
        (SmallEtale.sliceAssociatedModule B S hS X.1 X.2 W G
          (SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent B S hS X.1 W G)) =
      (representedSmallEtaleModuleEquivalence B S hS
          ((SmallEtale.toOver B S hS X.1).obj W)).functor.obj
        (_root_.AlgebraicGeometry.SmallEtale.sectionsSheafOfModules (associatedBigEtaleSite B)
          (chartScheme W) ((SmallEtale.toOver B S hS X.1).obj W).left.property G) := by
  refine Stacks.SheafOfModules.eq_of_val_eq
    ((chartModuleReindexEquivalence_functor_obj_val B S hS X W
        (SmallEtale.sliceAssociatedModule B S hS X.1 X.2 W G
          (SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent B S hS X.1 W G))).trans
      ((Stacks.Sites.pushforward_associatedModulePresheaf (chartScheme W) G
        (SmallEtale.sliceToOver B S hS X.1 W)
        (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor).trans
      ((eq_of_heq (Stacks.Sites.associatedModulePresheaf_heq_of_eq (chartScheme W) G
        (chartLocalization_comp_sliceToOver B S hS X W))).trans
      ((Stacks.Sites.pushforward_associatedModulePresheaf (chartScheme W) G
        (_root_.AlgebraicGeometry.SmallEtale.toOver (associatedBigEtaleSite B) (chartScheme W)
          ((SmallEtale.toOver B S hS X.1).obj W).left.property)
        (representedSmallEtaleEquivalence B S hS
          ((SmallEtale.toOver B S hS X.1).obj W)).functor).symm.trans
      (representedSmallEtaleModuleEquivalence_functor_obj_val B S hS _
        (_root_.AlgebraicGeometry.SmallEtale.sectionsSheafOfModules (associatedBigEtaleSite B)
          (chartScheme W) ((SmallEtale.toOver B S hS X.1).obj W).left.property G)).symm))))

/-- **The essential-surjectivity clause of Descent, Proposition 03DX (2) on the slice of the
small étale site of an algebraic space at an affine chart, with no hypothesis.**

The restriction of a quasi-coherent `𝒪_X`-module to the slice at an étale chart whose underlying
scheme is affine is isomorphic to the module `Mᵃ` of [Stacks, Tag 03DU] of a quasi-coherent
module on that scheme.  This is the hypothesis `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`, at one chart.

The quasi-coherent module on the chart's scheme is the one produced by
`AlgebraicGeometry.Space.exists_isQuasicoherent_iso_over_of_isAffine`; Tag 070S (2) turns the
pullback description of its associated module on the small étale site of that scheme into the
sections description, and
`AlgebraicGeometry.Space.chartModuleReindex_sliceAssociatedModule` identifies that with the
slice construction.  Reindexing along the comparison of Tag 04M0 is an equivalence of module
categories, so the isomorphism descends. -/
theorem exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite
    (K : Modules.{u, u} B S hS X.1 X.2) (hK : K.IsQuasicoherentOnSite)
    (hW : IsAffine (chartScheme W)) :
    ∃ (M : (chartScheme W).Modules) (_ : M.IsQuasicoherent)
      (hM : Presheaf.IsSheaf ((SmallEtale.topology B S hS X.1).over W)
        (Stacks.Sites.associatedPresheaf (chartScheme W) M
          (SmallEtale.sliceToOver B S hS X.1 W))),
      Nonempty (SmallEtale.sliceModule B S hS X.1 X.2 W K ≅
        SmallEtale.sliceAssociatedModule B S hS X.1 X.2 W M hM) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_isQuasicoherent_iso_over_of_isAffine B S hS X K hK W hW
  have := hG
  refine ⟨G, hG, SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent B S hS X.1 W G,
    ⟨((chartModuleReindexEquivalence B S hS X W).fullyFaithfulFunctor.preimageIso ?_).symm⟩⟩
  exact eqToIso (chartModuleReindex_sliceAssociatedModule B S hS X W G) ≪≫
    (representedSmallEtaleModuleEquivalence B S hS
        ((SmallEtale.toOver B S hS X.1).obj W)).functor.mapIso
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules
        (associatedBigEtaleSite B) (chartScheme W)
        ((SmallEtale.toOver B S hS X.1).obj W).left.property G).symm ≪≫ e

/-- **The uniform form of Descent, Proposition 03DW on the small étale site of an algebraic
space, with no hypothesis.**

An epimorphism of `𝒪_X`-modules whose kernel is cartesian on affine charts is surjective on the
sections over every affine étale chart.  This is
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_of_essSurj` with its
`hEss` discharged by
`AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite`: a module
cartesian on affine charts is quasi-coherent on the site, by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`. -/
theorem surjective_val_app_of_epi_of_kernel_isCartesian_unconditional
    {P Q : Modules.{u, u} B S hS X.1 X.2} (q : P ⟶ Q) (hq : Epi q)
    (hk : IsCartesianOnAffineCharts (CategoryTheory.Limits.kernel q))
    (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    Function.Surjective (q.val.app (op V)) :=
  surjective_val_app_of_epi_of_kernel_isCartesian_of_essSurj (hF := X.2)
    (fun Y hY K hK => exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite B S hS X Y K
      (isQuasicoherentOnSite_of_isCartesianOnAffineCharts K hK) hY) q hq hk V hV

end AlgebraicGeometry.Space

end
