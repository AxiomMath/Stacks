module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.InverseLimitOfAcyclicTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-coherent module on an algebraic space is acyclic on an affine étale chart

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S` and
let `𝓜` be a quasi-coherent `𝒪_X`-module on the small étale ringed site of `X`.  This file proves
that for every étale chart `U` of `X` whose underlying scheme is affine and every `p > 0`

```
H^p(U, 𝓜) = 0,
```

in each of the three spellings the library's cohomological machinery uses: as the vanishing of
`CategoryTheory.Sheaf.H'` of the underlying abelian sheaf, as the vanishing of the `p`-th right
derived functor of the module-valued sections `CategoryTheory.SheafOfModules.evaluation`, and as
the vanishing of the `p`-th right derived functor of the abelian-group-valued sections
`Stacks.Cohomology.SiteInverseLimits.sectionsFunctor`.

**This is the statement that twenty-nine files of this tree carry as the named hypothesis
`h03DW`, respectively `h03DWab`.**  It is the étale-site analogue, for an algebraic space, of
Serre's criterion on an affine open (Cohomology of Schemes, Lemma [Stacks, Tag 01XB]); the
source reaches it by localizing the small étale site of `X` at the chart and citing Descent,
Proposition [Stacks, Tag 03DW] on the resulting small étale site of the affine scheme `U`.

## Main results

* `AlgebraicGeometry.Space.isZero_cechCohomology_succ_of_isQuasicoherentOnSite`: the Čech
  cohomology of a quasi-coherent module vanishes in positive degrees on every finite affine
  covering family of an affine étale chart, with **no hypothesis**.
* `AlgebraicGeometry.Space.isAffine_chartScheme_piObj`: an iterated fibre product, in the small
  étale site, of affine charts over an affine chart is again an affine chart.
* `AlgebraicGeometry.Space.isZero_sheafCohomology_succ_of_isAffineChart`: `H^p(U, 𝓜) = 0` for
  `p > 0`, for the cohomology `CategoryTheory.Sheaf.H'` of the underlying abelian sheaf.
* `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`: the same, for the
  right derived functors of module-valued sections — **the hypothesis `h03DW`, discharged**.
* `AlgebraicGeometry.Space.isZero_rightDerived_sectionsFunctor_of_isAffineChart`: the same, for
  the right derived functors of abelian-group-valued sections — **the hypothesis `h03DWab`,
  discharged**.

## Implementation notes

*The route.*  Four proved inputs compose, and nothing is assumed.

* The Čech vanishing on a finite affine covering family of an affine chart is
  `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_essSurj_at`, which is
  [Stacks, Tag 03FJ] case (a) transported to the small étale site of the algebraic space; its
  single hypothesis `hEss` — essential surjectivity of `M ↦ Mᵃ` on the slice at the chart — is
  discharged, unconditionally, by
  `AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite`.
* The passage from Čech vanishing on a cofinal system of coverings to the vanishing of sheaf
  cohomology is [Stacks, Tag 03F9] in the form
  `Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives`, whose
  four homological inputs are available at the coefficient universe `u` of the structure rings
  although the site is not small in that universe: it *is* essentially small there
  (`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`), which gives Grothendieck
  abelianness of the abelian sheaves and hence enough injectives.
* The cofinality input is
  `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_univ`, which refines
  any covering sieve of an affine chart by a finite affine covering family at index universe `u`;
  that is the index universe [Stacks, Tag 03F9] is applied at here, so no Čech complex is
  reindexed.
* The passage from the `Ext`-form of the cohomology of the underlying abelian sheaf to the right
  derived functors of module-valued sections is
  `Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation`, which is the
  [Stacks, Tag 03FD] comparison in the only form available on a site whose objects live one
  universe above its morphisms.  `ModuleCohomologyComparisonDef.sectionsComparisonIso`, the named
  isomorphism, is stated for a `CategoryTheory.SmallCategory` and does not apply here.

*The third clause of the Čech criterion.*  [Stacks, Tag 03F9] asks that the iterated fibre
products of a selected covering family again lie in the selected collection of objects.  For
affine charts over an affine chart that is
`AlgebraicGeometry.Space.isAffine_chartScheme_piObj`, proved exactly as its big-site counterpart
`AlgebraicGeometry.isAffine_overScheme_piObj`: the product is transported along the functor
taking a chart to its scheme, which preserves the fibre products of the site, and a finite
product of schemes affine over an affine base is affine.

*The module universe.*  Everything here is at module universe `u`, the universe of the structure
rings, which is where `AlgebraicGeometry.Space.Modules` is quasi-coherent in the sense of
[Stacks, Tag 03DX] (2) —
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts` is stated for
`Modules.{u, u}` — and where the essential surjectivity of `(-)ᵃ` on the slice at a chart is
available.  The consumers of `h03DW` state it at a free module universe `m`; what is
proved here discharges them at `m = u`.

*The four homological inputs are `local` instances.*  They are stated twice, once at the reduced
spelling `AlgebraicGeometry.Space.SmallEtale.topology` of the topology and once at the projection
spelling `(AlgebraicGeometry.Space.smallEtaleRingedSite …).J`, because instance search does not
unfold the projection — the same arrangement, for the same reason, as the instances of
`StacksFrontier.AlgebraicGeometry.Spaces.RingedSite`.  They are not registered globally:
`StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections` records that instances at the
projection spelling of this site break lemmas which unify against the reduced spelling.

*No `@[stacks 03DW]` attribute is attached, and that is deliberate.*  [Stacks, Tag 03DW] is the
comparison `H^q(S, 𝓕) = H^q(𝒞, 𝓕ᵃ)` for a *scheme* `S`, with `𝒞` one of the five big `τ`-sites
or the small Zariski or small étale site of `S`, and it is already carried in this tree in every
degree and in both of the two branches the source delimits:
`AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` for `𝒞 = (Sch/S)_τ` and
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` for `𝒞 = S_étale`, both in
`StacksDraft.AlgebraicGeometry.EtaleCohomology.CechComparison`, besides the case `q = 0` of
clause (1) at `AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv`.  The statements
below are about the small étale site of an *algebraic space* and are a *consequence* of that
comparison, not a clause of it; tagging them would claim a part of the tag the tag does not
state.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The homological inputs of the Čech criterion -/

/-- Abelian sheaves on the small étale site of an algebraic space, with coefficients at the
universe `u` of the structure rings, have enough injectives.

The site is not small at `u`, but it is essentially small there, so
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall` applies and a Grothendieck
abelian category has enough injectives. -/
@[sga "4½ Arcata 1.6.3" "special case"]
local instance enoughInjectives_sheaf_smallEtale :
    EnoughInjectives (Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}) :=
  have : IsGrothendieckAbelian.{u}
      (Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _
  inferInstance

/-- The `Ext` groups of abelian sheaves on the small étale site of an algebraic space, with
coefficients at the universe `u` of the structure rings, live in the universe `u + 1` of the
objects of the site. -/
local instance hasExt_sheaf_smallEtale :
    HasExt.{u + 1} (Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- `AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale` at the projection spelling of the
topology, which instance search does not unfold to the reduced one. -/
local instance enoughInjectives_sheaf_smallEtaleRingedSite :
    EnoughInjectives (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) :=
  enoughInjectives_sheaf_smallEtale B S hS F

/-- `AlgebraicGeometry.Space.hasExt_sheaf_smallEtale` at the projection spelling of the
topology. -/
local instance hasExt_sheaf_smallEtaleRingedSite :
    HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) :=
  hasExt_sheaf_smallEtale B S hS F

/-- The `𝒪_X`-modules at the universe of the structure rings have enough injectives.  This is
`AlgebraicGeometry.Space.enoughInjectives_modules`, named as an instance. -/
local instance enoughInjectives_modules' : EnoughInjectives (Modules.{u, u} B S hS F hF) :=
  enoughInjectives_modules B S hS F hF

/-- The `Ext` groups of the `𝒪_X`-modules at the universe of the structure rings live in the
universe `u + 1` of the objects of the site. -/
local instance hasExt_modules : HasExt.{u + 1} (Modules.{u, u} B S hS F hF) :=
  HasExt.standard _

/-! ### Čech vanishing, with no hypothesis -/

/-- **The Čech cohomology of a quasi-coherent `𝒪_X`-module vanishes in positive degrees on a
finite affine covering family of an affine étale chart.**

This is `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_essSurj_at`, which is
[Stacks, Tag 03FJ] case (a) read on the small étale site of the algebraic space, with its
hypothesis `hEss` discharged by
`AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite`: the
restriction of a quasi-coherent module to the slice at an affine chart *is* an `Mᵃ`. -/
theorem isZero_cechCohomology_succ_of_isQuasicoherentOnSite
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS F) (hW : IsAffineChart B S hS F W)
    (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffineChart B S hS F (E.X i))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W) (p : ℕ) (hp : 0 < p) :
    letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsZero (Stacks.CechSite.cechCohomology E
      ((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj
        ((SheafOfModules.toSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O))).obj M)) p) :=
  SmallEtale.isZero_cechCohomology_succ_of_essSurj_at B S hS F W hW E hfin haff hcov M
    (exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite B S hS ⟨F, hF⟩ W M hM hW) p hp

/-! ### Affine iterated fibre products -/

/-- **An iterated fibre product of affine charts over an affine chart is an affine chart.**

This is the third clause of the hypothesis `hCovObjects` of [Stacks, Tag 03F9].  The argument is
the one of `AlgebraicGeometry.isAffine_overScheme_piObj` for a localized big site: the product is
taken in the slice of the small étale site at `W`, the functor taking a chart to its scheme
preserves the fibre products of the site, hence — by
`Stacks.Sites.preservesLimit_fibreProducts_overPost` — the iterated fibre products of a family,
and a finite product of schemes affine over an affine base is affine. -/
theorem isAffine_chartScheme_piObj {W : SmallEtale B S hS F}
    (hW : IsAffineChart B S hS F W) (E : PreZeroHypercover.{u} W)
    (hX : ∀ i, IsAffineChart B S hS F (E.X i)) (p : ℕ) (i : Fin (p + 1) → E.I₀) :
    letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
        HasProduct (fun a ↦ Over.mk (E.f (j a))) := fun q j ↦
      Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
    IsAffineChart B S hS F (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left := by
  let : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (j a))) := fun q j ↦
    Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
  let u : SmallEtale B S hS F ⥤ Scheme.{u} :=
    SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS
  let A : Fin (p + 1) → Over W := fun a ↦ Over.mk (E.f (i a))
  have _ : IsAffine (u.obj W) := hW
  have _ : PreservesLimit (Discrete.functor A) (Over.post (X := W) u) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost u E
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
  have haffhom : ∀ a, _root_.AlgebraicGeometry.IsAffineHom
      ((Over.post (X := W) u).obj (A a)).hom := fun a ↦ by
    have _ : IsAffine ((Over.post (X := W) u).obj (A a)).left := hX (i a)
    exact isAffineHom_of_isAffine _
  have _ : _root_.AlgebraicGeometry.IsAffineHom
      (∏ᶜ (fun a ↦ (Over.post (X := W) u).obj (A a))).hom :=
    isAffineHom_over_finiteProduct _ haffhom
  have haff := isAffine_of_isAffineHom (∏ᶜ (fun a ↦ (Over.post (X := W) u).obj (A a))).hom
  have e : chartScheme (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left ≅
      (∏ᶜ (fun a ↦ (Over.post (X := W) u).obj (A a))).left :=
    (Over.forget (u.obj W)).mapIso (PreservesProduct.iso (Over.post (X := W) u) A)
  exact IsAffine.of_isIso e.hom

/-! ### The vanishing -/

/-- The cofinal system of coverings [Stacks, Tag 03F9] is applied to: the finite covering
families of a chart by affine charts, selected only at the affine charts. -/
abbrev affineChartCoverings (V : SmallEtale B S hS F) :
    Set { E : PreZeroHypercover.{u} V // E.sieve₀ ∈ SmallEtale.topology B S hS F V } :=
  {E | IsAffineChart B S hS F V ∧ Finite E.1.I₀ ∧ ∀ i, IsAffineChart B S hS F (E.1.X i)}

/-- **`H^p(U, 𝓜) = 0` for `p > 0`, a quasi-coherent `𝒪_X`-module `𝓜` and an affine étale chart
`U` of an algebraic space `X`** — for the cohomology `CategoryTheory.Sheaf.H'` of the underlying
abelian sheaf of `𝓜`, that is `Ext` out of the free abelian sheaf on the representable at `U`.

This is the Čech criterion [Stacks, Tag 03F9],
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives`, applied
to the affine charts and to their finite affine covering families.  Its four hypotheses are: the
existence of the iterated fibre products, which the site's pullbacks supply; that those fibre
products are again affine charts,
`AlgebraicGeometry.Space.isAffine_chartScheme_piObj`; cofinality of the finite affine covering
families among all coverings of an affine chart,
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_univ`; and the Čech
vanishing, `AlgebraicGeometry.Space.isZero_cechCohomology_succ_of_isQuasicoherentOnSite`.

The `Ext` universe is the universe `u + 1` of the objects of the site, which is where the `Ext`
groups of abelian sheaves at coefficient universe `u` live. -/
theorem isZero_sheafCohomology_succ_of_isAffineChart
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS F) (hU : IsAffineChart B S hS F U) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u + 1}
      ((SheafOfModules.toSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).obj M) p U) := by
  refine Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives.{
      u + 1, u, u, u + 1}
    (SmallEtale.topology B S hS F) {V | IsAffineChart B S hS F V}
    (affineChartCoverings B S hS F)
    (fun {V} E _ q j ↦
      Stacks.Sites.hasProduct_fibreProducts E.1 (fun _ _ _ ↦ inferInstance) q j)
    (fun {V} E hE ↦ ⟨hE.1, hE.2.2, fun q j ↦
      isAffine_chartScheme_piObj B S hS F hE.1 E.1 hE.2.2 q j⟩)
    (fun V hV R hR ↦ ?_) _ (fun {V} E hE q hq ↦ ?_) U hU p hp
  · obtain ⟨E, ⟨hfin, haff, hmem⟩, hle⟩ :=
      SmallEtale.exists_finite_affine_preZeroHypercover_univ V hV R hR
    exact ⟨⟨E, hmem⟩, ⟨hV, hfin, haff⟩, hle⟩
  · exact isZero_cechCohomology_succ_of_isQuasicoherentOnSite B S hS F hF M hM V hE.1 E.1
      hE.2.1 hE.2.2 E.2 q hq

/-- **The hypothesis `h03DW` of this tree, discharged.**  Let `X` be an algebraic space over a
scheme `S` of a big fppf site, let `U` be an étale chart of `X` whose underlying scheme is affine
and let `𝓜` be a quasi-coherent `𝒪_X`-module.  Then for every `p > 0` the `p`-th right derived
functor of the module-valued sections over `U` vanishes at `𝓜`:

```
H^p(U, 𝓜) = 0.
```

This is `AlgebraicGeometry.Space.isZero_sheafCohomology_succ_of_isAffineChart` read through
`Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation`, the [Stacks, Tag 03FD]
comparison of module cohomology with the cohomology of the underlying abelian sheaf on a site
whose objects need not be small. -/
theorem isZero_rightDerived_evaluation_of_isAffineChart
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS F) (hU : IsAffineChart B S hS F U) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      (op U)).rightDerived p).obj M) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  exact ModuleCat.isZero_iff_subsingleton.2
    (Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation
      (smallEtaleRingedSite B S hS F hF).J
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) M U n
      (isZero_sheafCohomology_succ_of_isAffineChart B S hS F hF M hM U hU (n + 1) hp))

/-- **The hypothesis `h03DWab` of this tree, discharged.**  The same vanishing as
`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`, for the
abelian-group-valued sections functor
`Stacks.Cohomology.SiteInverseLimits.sectionsFunctor` — module-valued sections followed by
forgetting the module structure.

Forgetting the module structure is exact, so it commutes with right derived functors
(`Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology`); and a module is a zero object
exactly when its underlying abelian group is. -/
theorem isZero_rightDerived_sectionsFunctor_of_isAffineChart
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS F) (hU : IsAffineChart B S hS F U) (p : ℕ) (hp : 0 < p) :
    IsZero (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS F hF) U).rightDerived p).obj M) := by
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) (op U))
    (forget₂ (ModuleCat.{u, u}
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op U)))
      AddCommGrpCat.{u}) p M
  exact (Functor.map_isZero _
    (isZero_rightDerived_evaluation_of_isAffineChart B S hS F hF M hM U hU p hp)).of_iso e.symm

end AlgebraicGeometry.Space

end
