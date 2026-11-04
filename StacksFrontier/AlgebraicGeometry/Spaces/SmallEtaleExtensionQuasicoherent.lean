module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishingCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishingFreeIndexUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsAndCokernels
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineSectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleKernelQuasicoherent

/-!
# The extension clause of Stacks 03M1 at the enlarged module universe

Let `S` be a scheme contained in a big fppf site `B` and let `F` be an algebraic space over `S`.
Stacks 03M1 asserts, among its clauses, that the middle term of a short exact sequence of
`𝒪_F`-modules whose outer terms are quasi-coherent is again quasi-coherent.  This file proves
that clause for module sections in `Type (max (u + 1) m)` with `m` arbitrary.

`AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves_of_h03DW` is the same
clause at the module universe `u` of the schemes, from a surjectivity hypothesis.  The enlarged
universe is the one in which the direct sums of
Stacks 04CK and the tensor products of Stacks 09LX are formed — the objects of the small étale
site live in `Type (u + 1)`, so the modules on it that those constructions produce have their
sections there and not in `Type u` — and it is where the other closure clauses of Stacks 03M1
already are, as `AlgebraicGeometry.Space.isClosedUnderKernels`,
`AlgebraicGeometry.Space.isClosedUnderCokernels`,
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape` and
`AlgebraicGeometry.Space.isClosedUnderDirectSumsQuasicoherent`.

## Main results

* `AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_isQuasicoherentOnSite`: the
  right-hand map of a short exact sequence whose left term is quasi-coherent is **surjective on
  the sections over every affine étale chart**, at the enlarged module universe.
* `AlgebraicGeometry.Space.SmallEtale.hasSectionBaseChangeOn_of_isCartesianOnAffineCharts`: a
  module cartesian on affine charts satisfies the base-change condition that a global
  presentation on the slice at an affine chart is assembled from.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts_enlarged`: **the
  implication "cartesian on affine charts implies quasi-coherent" of Descent,
  Proposition 03DX (2) at the enlarged module universe.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_X₂_of_shortExact` and
  `AlgebraicGeometry.Space.isClosedUnderExtensions`: **the extension clause of Stacks 03M1 at the
  enlarged module universe**, with no hypothesis.

## Implementation notes

**The surjectivity is the one cohomological step, and its input is available.**  Sections of a short
exact sequence of sheaves of modules are only left exact; the discrepancy over an affine chart is
a first Čech cohomology group of the left term, and that group vanishes by
`AlgebraicGeometry.Space.isZero_cechCohomology_succ_of_isQuasicoherentOnSite`, which is stated at
the module universe `max u m` precisely because the coefficient comparison it goes through,
`AlgebraicGeometry.Space.SmallEtale.tensorToChartSections`, is built from a bare module.  What is
done here is to feed that vanishing to Cohomology on Sites, Lemma 03F8
(`Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology`) along the cofinal system of
finite affine covering families of
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_univ`, exactly as
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_univ` does at the
universe of the schemes.  That statement is not reused: it is stated for
`AlgebraicGeometry.Space.Modules.{u, u}`, and its route to the Čech hypothesis goes through
`AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite`, whose
associated module lives on the chart's *scheme* and hence has its sections in `Type u`.

**Stacks 03F8 must be applied at explicit universes**, as it must at the universe of the schemes:
written `.{max (u + 1) m, u, u + 1, max (u + 1) m}` — the index universe of the covering
families, the morphisms of the small étale site of `F`, its objects, and the coefficients.  Left
implicit, the coefficient universe is still a metavariable when `CategoryTheory.HasSheafify` is
synthesized and instance search solves it at the universe of the objects.  The two sheafification
facts are supplied as local `letI`s from
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`, which is what makes the
abelian sheaves at the enlarged coefficient universe an abelian category.

**`Epi` and `Mono` of the sequence are named before the short complex of abelian sheaves is
built.**  `CategoryTheory.Functor.map_epi` takes `Epi T.g` as an instance, and with it absent
instance search for `Epi` runs into the `CategoryTheory.IsGrothendieckAbelian` instances of the
module category, whose universe is not determined by their conclusion.

**The converse half of Descent, Proposition 03DX (2) is obtained from global presentations and
not from the chart-relations machinery.**  `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` is
bijectivity of `AlgebraicGeometry.Space.sectionsBaseChange` at every morphism of affine charts,
which is `AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn` read at the identity family
of the slice, so
`AlgebraicGeometry.Space.SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn` gives a
global presentation on each affine chart and
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation` concludes.  Both
of those are free in the module universe.
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`, which reaches the
same implication through the relations among the tautological generators, is stated for
`AlgebraicGeometry.Space.Modules.{u, u}` and is not used here.

**No `@[stacks]` attribute is attached.**  Stacks 03M1 has six clauses and only the extension one
is proved here; its carriers are the clause-by-clause statements, and Descent,
Proposition 03DX (2) is an equivalence of categories of which only one implication appears
below — the convention of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentWeakSerreUnconditional.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/CartesianRelations.lean`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe m u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The right-hand map of a short exact sequence of `𝒪_F`-modules whose left term is
quasi-coherent is surjective on the sections over every affine étale chart**, at the enlarged
module universe and with no hypothesis beyond quasi-coherence of that term.

The sequence of abelian sheaves underlying `T` is short exact —
`CategoryTheory.SheafOfModules.toSheaf` preserves finite limits and monomorphisms, and it
preserves epimorphisms by `Stacks.SheafOfModules.EpiMono.preservesEpimorphismsToSheaf` — the
finite affine covering families of an affine chart are cofinal among its coverings, and the first
Čech cohomology of `T.X₁` on such a family vanishes; Cohomology on Sites, Lemma 03F8 concludes.

This is `AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact` at the enlarged module
universe; see the implementation notes for why that statement is not reused. -/
theorem surjective_g_val_app_of_shortExact_of_isQuasicoherentOnSite
    (T : ShortComplex (Modules.{u, max (u + 1) m} B S hS F hF)) (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (T.g.val.app (op W)) := by
  have hfl : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : HasSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{max (u + 1) m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) m, u, u + 1} _
  let : (SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max (u + 1) m, u + 1,
      u} _
  have hmono := hT.mono_f
  have hepi := hT.epi_g
  have hTab : (T.map (SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ShortExact :=
    { exact := ShortComplex.Exact.map_of_mono_of_preservesKernel hT.exact _ hmono inferInstance
      mono_f := (SheafOfModules.toSheaf _).map_mono _
      epi_g := (SheafOfModules.toSheaf _).map_epi _ }
  exact Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology.{max (u + 1) m, u, u + 1,
      max (u + 1) m}
    (SmallEtale.topology B S hS F) _ hTab W
    {E : PreZeroHypercover.{max (u + 1) m} W | Finite E.I₀ ∧
      (∀ i, IsAffine
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
      E.sieve₀ ∈ SmallEtale.topology B S hS F W}
    (fun _ hE ↦ hE.2.2)
    (fun R hR ↦ SmallEtale.exists_finite_affine_preZeroHypercover_freeIndex.{max (u + 1) m}
      W hW R hR)
    (fun _ _ _ _ ↦ inferInstance)
    (fun E hE ↦
      isZero_cechCohomology_succ_of_isQuasicoherentOnSite_freeModuleUniverse.{max (u + 1) m, u}
        B S hS F hF T.X₁ h₁ W hW E hE.1 hE.2.1 hE.2.2 1 Nat.one_pos)

/-- **A module cartesian on affine charts satisfies the base-change condition on the slice at an
affine chart**, at every object of a class consisting of objects with affine underlying scheme.

`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn` asks for bijectivity of the
`𝒪_F(W)`-linear extension of the restriction map from the sections over the chart to the
sections over `W`, for the universe-lifted restriction of the module;
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` asserts bijectivity of exactly that extension
for the module itself, at the structural morphism of `W`.  The two differ only by the universe
lift of the sections, which `Module.BaseChange.bijective_liftBaseChange_of_comm` transports along
`ULift.down`.

The module instances inside the statement of `HasSectionBaseChangeOn` are rebuilt here with the
same values rather than taken from the hypotheses, because instance search does not see them
there; this is the arrangement of
`AlgebraicGeometry.Space.SmallEtale.exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite`. -/
theorem SmallEtale.hasSectionBaseChangeOn_of_isCartesianOnAffineCharts
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    (G : Modules.{u, max (u + 1) m} B S hS F hF) (hG : IsCartesianOnAffineCharts G)
    {Q : Over V → Prop}
    (hQ : ∀ W : Over V, Q W → IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left))) :
    SmallEtale.HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, max (u + 1) m, u + 1} (G.over V)) Q := by
  intro W hQW mNT mNW algW mNWA twNW
  let mUT : Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)
      ((G.over V).val.obj (op (Over.mk (𝟙 V)))) := inferInstanceAs (Module
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over V).obj.obj
      (op (Over.mk (𝟙 V)))) ((G.over V).val.obj (op (Over.mk (𝟙 V)))))
  let mUW : Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      ((G.over V).val.obj (op W)) := inferInstanceAs (Module
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over V).obj.obj
      (op W))
    ((G.over V).val.obj (op W)))
  let mUWA : Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤) ((G.over V).val.obj (op W)) :=
    Module.compHom _ (algebraMap
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤))
  have twUW : IsScalarTower
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      ((G.over V).val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let res : (G.over V).val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V), ⊤)] (G.over V).val.obj (op W) :=
    { toFun := fun n => (G.over V).val.map (Over.mkIdTerminal.from W).op n
      map_add' := map_add ((G.over V).val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c n =>
        ((G.over V).val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl }
  have hbij : Function.Bijective (res.liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) :=
    hG V W.left hV (hQ W hQW) (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 V)).left
  exact Module.BaseChange.bijective_liftBaseChange_of_comm _ res
    { toFun := ULift.down
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    { toFun := ULift.down
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun _ => rfl) hbij

/-- **The one-member family consisting of the identity of the terminal object of the slice at a
chart is a covering family.**  The sieve it generates contains an identity, hence is the maximal
sieve.

It is the family that
`AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isCartesianOnAffineCharts` feeds to
`AlgebraicGeometry.Space.SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn`: the
base-change condition of a module cartesian on affine charts holds at *every* object of the slice
with affine underlying scheme, so no refinement of the chart is needed. -/
theorem SmallEtale.sieve_ofArrows_id_mem (V : (smallEtaleRingedSite B S hS F hF).C) :
    Sieve.ofArrows (fun _ : PUnit.{1} => (Over.mk (𝟙 V) : Over V))
        (fun _ => 𝟙 (Over.mk (𝟙 V) : Over V)) ∈
      ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)) := by
  have htop : Sieve.ofArrows (fun _ : PUnit.{1} => (Over.mk (𝟙 V) : Over V))
      (fun _ => 𝟙 (Over.mk (𝟙 V) : Over V)) = ⊤ := by
    refine Sieve.id_mem_iff_eq_top.1 ?_
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨PUnit.unit, 𝟙 _, by simp⟩
  rw [htop]
  exact ((smallEtaleRingedSite B S hS F hF).J.over V).top_mem _

/-- **A module cartesian on affine charts has a global presentation after restriction to a chart
whose underlying scheme is affine.**

This is `AlgebraicGeometry.Space.SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn` at
the identity family of the slice, with its base-change hypothesis discharged by
`AlgebraicGeometry.Space.SmallEtale.hasSectionBaseChangeOn_of_isCartesianOnAffineCharts`. -/
theorem hasGlobalPresentation_over_of_isCartesianOnAffineCharts
    (G : Modules.{u, max (u + 1) m} B S hS F hF) (hG : IsCartesianOnAffineCharts G)
    (V : (smallEtaleRingedSite B S hS F hF).C)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V))) :
    (G.over V).HasGlobalPresentation :=
  SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn B S hS F hF (G.over V) hV
    (fun _ : PUnit.{1} => 𝟙 (Over.mk (𝟙 V) : Over V))
    (SmallEtale.sieve_ofArrows_id_mem B S hS F hF V)
    (SmallEtale.hasSectionBaseChangeOn_of_isCartesianOnAffineCharts B S hS F hF hV G hG
      fun _ hW => hW.1)

/-- **A module cartesian on affine charts is quasi-coherent on the small étale site of the
algebraic space**, at the enlarged module universe.

This is the implication "base change criterion ⟹ quasi-coherent" of Descent,
Proposition 03DX (2).  The étale charts with affine underlying scheme cover the final object of
the small étale site, the module is globally presented on each of them by
`AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isCartesianOnAffineCharts`, and a module
globally presented on a covering family of the final object is quasi-coherent.

`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` is the same
implication for `AlgebraicGeometry.Space.Modules.{u, u}`, reached through the relations among the
tautological generators over a chart. -/
theorem isQuasicoherentOnSite_of_isCartesianOnAffineCharts_enlarged
    (G : Modules.{u, max (u + 1) m} B S hS F hF) (hG : IsCartesianOnAffineCharts G) :
    G.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation G
    (SmallEtale.coversTop_affineCharts B S hS F)
    fun V => hasGlobalPresentation_over_of_isCartesianOnAffineCharts B S hS F hF G hG V.1 V.2

/-- **The base change comparison of the middle term of a short exact sequence**, at a free module
universe.  Let `T : 0 → T.X₁ → T.X₂ → T.X₃ → 0` be a short exact sequence of `𝒪_F`-modules and
let `f : V ⟶ U` be a morphism of étale charts along which `T.g` is surjective on the sections
over `U`.  If the sections of `T.X₁` and of `T.X₃` over `V` are the base change of their sections
over `U`, then so are the sections of `T.X₂`.

This is `AlgebraicGeometry.Space.bijective_sectionsBaseChange_shortExact_X₂`, which is stated at
the module universe `u` of the schemes, at a free module universe `m`; the argument only uses
that the category of modules is balanced, which is an instance argument here. -/
theorem bijective_sectionsBaseChange_shortExact_X₂_freeModuleUniverse
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    [Balanced (Modules.{u, m} B S hS F hF)]
    (T : ShortComplex (Modules.{u, m} B S hS F hF)) (hT : T.ShortExact)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hgU : Function.Surjective (T.g.val.app (op U)))
    (h₁ : Function.Bijective (sectionsBaseChange T.X₁ f))
    (h₃ : Function.Bijective (sectionsBaseChange T.X₃ f)) :
    Function.Bijective (sectionsBaseChange T.X₂ f) := by
  let _ := chartAlgebra (hF := hF) f
  exact bijective_baseChange_of_shortExact_middle
    (φU := (T.f.val.app (op U)).hom) (πU := (T.g.val.app (op U)).hom)
    (φV := (T.f.val.app (op V)).hom) (πV := (T.g.val.app (op V)).hom)
    hgU (SheafOfModules.exact_val_app_of_shortExact hT (op U))
    (SheafOfModules.injective_f_val_app_of_shortExact hT (op V))
    (SheafOfModules.exact_val_app_of_shortExact hT (op V))
    (app_sectionsBaseChange T.f f) (app_sectionsBaseChange T.g f) h₁ h₃

/-- **The middle term of a short exact sequence of `𝒪_F`-modules is cartesian on affine charts
as soon as the other two terms are**, granted that `T.g` is surjective on the sections over
every affine étale chart, at a free module universe.

This is `AlgebraicGeometry.Space.isCartesianOnAffineCharts_shortExact_X₂`, which is stated at the
module universe `u` of the schemes, at a free module universe `m`, the category of modules being
balanced. -/
theorem isCartesianOnAffineCharts_shortExact_X₂_freeModuleUniverse
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    [Balanced (Modules.{u, m} B S hS F hF)]
    (T : ShortComplex (Modules.{u, m} B S hS F hF)) (hT : T.ShortExact)
    (hg : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective (T.g.val.app (op U)))
    (h₁ : IsCartesianOnAffineCharts T.X₁) (h₃ : IsCartesianOnAffineCharts T.X₃) :
    IsCartesianOnAffineCharts T.X₂ :=
  fun U V hU hV f => bijective_sectionsBaseChange_shortExact_X₂_freeModuleUniverse T hT f
    (hg U hU) (h₁ U V hU hV f) (h₃ U V hU hV f)

/-- **The extension clause of Stacks 03M1 at the enlarged module universe**: the middle term of a
short exact sequence of `𝒪_F`-modules whose outer terms are quasi-coherent is quasi-coherent.

The outer terms are cartesian on affine charts by the forward implication of Descent,
Proposition 03DX (2),
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`; the middle term is
then cartesian on affine charts by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_shortExact_X₂`, whose surjectivity input is
`AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_isQuasicoherentOnSite` above; and
a module cartesian on affine charts is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts_enlarged`. -/
theorem isQuasicoherentOnSite_X₂_of_shortExact
    (T : ShortComplex (Modules.{u, max (u + 1) m} B S hS F hF)) (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite) :
    T.X₂.IsQuasicoherentOnSite := by
  let _hab : Abelian (Modules.{u, max (u + 1) m} B S hS F hF) :=
    SheafOfModules.instAbelian.{max (u + 1) m, u, u, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  exact isQuasicoherentOnSite_of_isCartesianOnAffineCharts_enlarged B S hS F hF T.X₂
    (isCartesianOnAffineCharts_shortExact_X₂_freeModuleUniverse T hT
      (fun U hU => surjective_g_val_app_of_shortExact_of_isQuasicoherentOnSite
        B S hS F hF T hT h₁ U hU)
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse.{u, max (u + 1) m}
        B S hS F hF T.X₁ h₁)
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse.{u, max (u + 1) m}
        B S hS F hF T.X₃ h₃))

/-- **The extension clause of Stacks 03M1 for the small étale ringed site of an algebraic space**,
at the enlarged module universe and in the form of the
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions` class, with no hypothesis.

It is the third input of `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass`, hence
of Stacks 09MA for the small étale site of an algebraic space,
`AlgebraicGeometry.Space.derivedCategoryB_tensorWithComplexDerived_obj_smallEtale`. -/
theorem isClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) where
  prop_X₂_of_shortExact {T} hT h₁ h₃ :=
    isQuasicoherentOnSite_X₂_of_shortExact B S hS F hF T hT h₁ h₃

end AlgebraicGeometry.Space

end
