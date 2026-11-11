module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleQuasicoherentReflection
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.AffineEtaleLiftedCartesian

/-!
# The four quasi-coherent derived categories of Stacks 0H06

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`. Stacks 0H05 and
0H06 consider four triangulated categories:

1. `D_QCoh(𝒪_F)`, on the small étale site;
2. `D_QCoh(F_{affine,étale}, 𝒪_F)`, on the affine étale charts with the étale topology;
3. `D_QCoh(F_{affine}, 𝒪_F)`, on the affine étale charts with the chaotic topology;
4. `QC(F_{affine}, 𝒪_F)`, the cartesian objects of Stacks 0GYU on the chaotic site;

and Stacks 0H06 says that they are canonically equivalent. This file constructs the three
equivalences `(1) ≌ (2) ≌ (3) ≌ (4)`, on one and the same structure sheaf and at one and the same
universe of module sections, and assembles them in
`AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChain`.

## Main definitions

* `AlgebraicGeometry.Space.affineEtaleChartQuasicoherentDerivedCategory`: category (2).
* `AlgebraicGeometry.Space.affineEtaleChartChaoticRingedSite`: the affine étale charts with the
  chaotic topology and the restricted structure sheaf,
  `AlgebraicGeometry.Space.hasQuasicoherentCohomologyAffineEtaleChart`: the condition cutting
  category (3) out of `D(F_{affine}, 𝒪_F)`, and
  `AlgebraicGeometry.Space.affineEtaleChartChaoticQuasicoherentDerivedCategory`: category (3).
* `AlgebraicGeometry.Space.affineEtaleBaseChangeData`: the base-change datum on the chart rings,
  so that category (4) is `QC (affineEtaleBaseChangeData B S hS F hF)`.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChartEquivalence`: **(1) ≌ (2)**,
  induced by restriction to the affine charts
  (`AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChartEquivalence_functor_comp_ι`).
* `AlgebraicGeometry.Space.affineEtaleChartQuasicoherentDerivedChaoticEquivalence`:
  **(2) ≌ (3)**, given by `Rε_*` with quasi-inverse `ε^*` for the change of topology
  `ε : (F_{affine,étale}, 𝒪_F) ⟶ (F_{affine}, 𝒪_F)`; see
  `AlgebraicGeometry.Space.affineEtaleChartQuasicoherentDerivedChaoticEquivalence_functor_comp_ι`.
* `AlgebraicGeometry.Space.affineEtaleChartChaoticQuasicoherentQCEquivalence` and
  `AlgebraicGeometry.Space.isQC_iff_hasQuasicoherentCohomology_affineEtaleChartChaotic`:
  **(3) ≌ (4)**, the two being the same full subcategory of `D(F_{affine}, 𝒪_F)`
  (`AlgebraicGeometry.Space.affineEtaleChartChaoticQuasicoherentQCEquivalence_functor_comp_ι`).
* `AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChain`: the three together.

## The argument

The source gets (1) ≃ (2) from the equivalence of ringed topoi of Stacks 0H03 and the intrinsic
nature of quasi-coherence, (2) ≃ (3) from Stacks 07A8 applied to `ε`, and (3) ≃ (4) from
Stacks 0GZR. Here:

* (1) ≃ (2) is the Comparison Lemma for sheaves of modules along the dense subsite inclusion of
  Stacks 04JS, derived; quasi-coherence is preserved and reflected by restriction to the affine
  charts (`AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModulePushforward_iff`).
* (2) ≃ (3) is Stacks 0GZS for `ε`, whose equivalence is given by `Rε_*` and `ε^*` exactly as
  the source's use of Stacks 07A8 is; the subcategory of 0GZS of `D(F_{affine,étale}, 𝒪_F)` is
  identified with `D_QCoh`, and `QC` with `D_QCoh(F_{affine}, 𝒪_F)` by Stacks 0GZR. The
  hypothesis of 0GZS, `IsLocallyKFlatAcyclic`, is proved
  (`AlgebraicGeometry.Space.isLocallyKFlatAcyclic_affineEtale`) from the vanishing of the higher
  cohomology of the base changes `N ⊗_{𝒪(U)} 𝒪_U` on the slices — the vanishing of the
  cohomology of quasi-coherent modules on affines used in condition (4) of the source's
  verification of 07A8 — and the identification of the 0GZS subcategory needs that cartesian
  sheaves are quasi-coherent and conversely, which is Stacks 0H04 on the affine étale site
  (`AlgebraicGeometry.Space.isCartesianPresheaf_iff_isQuasicoherentOnSite_affineEtale`): the
  description of the class `𝒜` of the source's proof.
* (3) ≃ (4) is Stacks 0GZR, the restriction maps of `𝒪_F` along morphisms of affine charts being
  flat.

## Implementation notes

The structure sheaf of all four categories is that of `D_QCoh(𝒪_F)` restricted to the affine
charts, the presheaf of chart rings `AlgebraicGeometry.Space.affineEtaleRingRestriction`, with
rings of sections in the universe `u` of the schemes. The objects of the affine étale site lie in
`Type (u + 1)`, and the derived category of modules on the chaotic site of (3) and (4) has its
modules in a universe containing that of the objects, so the whole chain is read at module
universe `max (u + 1) w`; this includes `D_QCoh(𝒪_F)`, which is
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` at that module universe. At module
universe `u`, the comparison of (1) and (2) is
`AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleRestrictionEquivalence`.

## References

* [Stacks Project, Tag 0H06](https://stacks.math.columbia.edu/tag/0H06)
* [Stacks Project, Tag 0H05](https://stacks.math.columbia.edu/tag/0H05)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0GZR](https://stacks.math.columbia.edu/tag/0GZR)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

-- The ambient-universe instances on sheaves of modules state their module universe as a `max`
-- pattern which the module universe `max (u + 1) w` does not match syntactically; instance search
-- against them leaves stuck universe constraints. The instances that apply are Mathlib's.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.QuasiCoherentCohomology
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The étale side: cartesian versus quasi-coherent on the affine charts -/

/-- **An `𝒪_F`-module is quasi-coherent exactly when its restriction to the affine étale charts
is cartesian**, for module sections in any universe containing that of the objects of the site.
The restriction maps of the restriction are those of the module along morphisms of affine charts,
so this is Descent, Proposition 03DX (2)
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse`). -/
theorem isCartesianPresheaf_affineEtaleRestrictionEquivalence_iff_isQuasicoherentOnSite
    (G : Modules.{u, max (u + 1) w} B S hS F hF) :
    IsCartesianPresheaf
        ((affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF).functor.obj G).val ↔
      G.IsQuasicoherentOnSite := by
  refine (isCartesianPresheaf_affineEtaleRestrictionEquivalence_iff.{u, max (u + 1) w}
    B S hS F hF G).trans ?_
  refine Iff.trans ?_
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse.{u, max (u + 1) w}
      B S hS F hF G).symm
  refine ⟨fun h U V hU hV f => ?_, fun h U V a =>
    (isUniversalArrow_map_iff_bijective_sectionsBaseChange.{u, max (u + 1) w}
      B S hS F hF G ((AffineEtale.inclusion B S hS F).map a.unop)).2
      (h V.unop.obj U.unop.obj V.unop.property U.unop.property
        ((AffineEtale.inclusion B S hS F).map a.unop))⟩
  have h' := h (Quiver.Hom.op ((AffineEtale.inclusion B S hS F).preimage
    (X := (⟨V, hV⟩ : AffineEtale B S hS F)) (Y := ⟨U, hU⟩) f))
  rw [Functor.op_map, Quiver.Hom.unop_op, Functor.map_preimage] at h'
  exact (isUniversalArrow_map_iff_bijective_sectionsBaseChange.{u, max (u + 1) w}
    B S hS F hF G f).1 h'

/-- **On the affine étale site, a sheaf of modules is cartesian exactly when it is
quasi-coherent** (Stacks 0H04, (1) ⇔ (2)), over the restricted structure sheaf of `D_QCoh(𝒪_F)`
and for module sections in any universe containing that of the objects of the site.

The sheaf is the restriction of an `𝒪_F`-module `G`, restriction to the affine charts being an
equivalence (`AlgebraicGeometry.Space.affineEtaleRestrictionEquivalence`); being cartesian is
quasi-coherence of `G`
(`isCartesianPresheaf_affineEtaleRestrictionEquivalence_iff_isQuasicoherentOnSite`), which is
quasi-coherence of the restriction
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModulePushforward_iff`). -/
theorem isCartesianPresheaf_iff_isQuasicoherentOnSite_affineEtale
    (N : SheafOfModules.{max (u + 1) w} (affineEtaleRingRestriction B S hS F hF)) :
    IsCartesianPresheaf N.val ↔ N.IsQuasicoherentOnSite := by
  let E := affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF
  let e : E.functor.obj (E.inverse.obj N) ≅ N := E.counitIso.app N
  have hG := isCartesianPresheaf_affineEtaleRestrictionEquivalence_iff_isQuasicoherentOnSite.{u, w}
    B S hS F hF (E.inverse.obj N)
  have hq : (E.functor.obj (E.inverse.obj N)).IsQuasicoherentOnSite ↔
      (E.inverse.obj N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_affineEtaleModulePushforward_iff.{u, max (u + 1) w} B S hS F hF _
  exact ⟨fun h => SheafOfModules.IsQuasicoherentOnSite.of_iso e
      (hq.2 (hG.1 (IsCartesianPresheaf.of_iso ((SheafOfModules.forget _).mapIso e.symm) h))),
    fun h => IsCartesianPresheaf.of_iso ((SheafOfModules.forget _).mapIso e)
      (hG.2 (hq.1 (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm h)))⟩

/-! ### Hypothesis (2) of Stacks 0GZS on the affine étale site -/

/-- The rings of sections of the restricted structure sheaf commute. -/
theorem mul_comm_affineEtaleRingRestriction (V : (AffineEtale B S hS F)ᵒᵖ)
    (x y : (affineEtaleRingRestriction B S hS F hF).obj.obj V) : x * y = y * x :=
  RingedSite.mul_comm_ringSheaf (affineEtaleRingedSite B S hS F hF) V x y

/-- Sheaves of abelian groups with sections in `max (u + 1) w` on a slice of the affine étale
site admit sheafification: the objects of the slice lie in `Type (u + 1)` and its morphisms in
`Type u`. -/
instance AffineEtale.hasSheafify_over_max (X : AffineEtale B S hS F) :
    HasSheafify ((AffineEtale.topology B S hS F).over X) AddCommGrpCat.{max (u + 1) w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) w, u, u + 1} _

/-- On a slice of the affine étale site, the morphisms of abelian presheaves with sections in
`max (u + 1) w` inverted by sheafification are the locally bijective ones. -/
instance AffineEtale.wEqualsLocallyBijective_over_max (X : AffineEtale B S hS F) :
    ((AffineEtale.topology B S hS F).over X).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) w} :=
  inferInstance

/-- Sheaves of abelian groups with sections in `max (u + 1) w` on the affine étale site admit
sheafification. -/
instance AffineEtale.hasSheafify_max :
    HasSheafify (AffineEtale.topology B S hS F) AddCommGrpCat.{max (u + 1) w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) w, u, u + 1} _

/-- On the affine étale site, the morphisms of abelian presheaves with sections in
`max (u + 1) w` inverted by sheafification are the locally bijective ones. -/
instance AffineEtale.wEqualsLocallyBijective_max :
    (AffineEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) w} :=
  inferInstance

/-- **The base changes on the slices of the affine étale site are sheaves**: for an affine chart
`U` and an `𝒪(U)`-module `N`, the presheaf `N ⊗_{𝒪(U)} 𝒪_U` on the slice at `U` is a sheaf. The
affine étale site is flatly cofinal for its scheme functor
(`AlgebraicGeometry.Space.AffineEtale.isFlatCofinal`), so this is
`Stacks.AffineSiteBaseChange.isSheaf_baseChangePresheaf`. -/
theorem baseChangeIsSheaf_affineEtale :
    Stacks.UniverseLift.BaseChangeIsSheaf.{max (u + 1) w} (affineEtaleRingRestriction B S hS F hF)
      (mul_comm_affineEtaleRingRestriction B S hS F hF) :=
  fun x N => Stacks.AffineSiteBaseChange.isSheaf_baseChangePresheaf.{max (u + 1) w}
    (AffineEtale.isFlatCofinal B S hS F) x N

open Stacks.Sites.OverModules in
/-- **The base changes on the slices of the affine étale site have no higher cohomology**: the
higher cohomology of `N ⊗_{𝒪(U)} 𝒪_U` over every object of the slice at an affine chart `U`
vanishes, by the Čech criterion along the finite flat coverings of affine schemes
(`Stacks.AffineSiteBaseChange.isZero_rightDerived_evaluation_baseChange`). This is the vanishing
of the cohomology of quasi-coherent modules on affines used by the source (Cohomology of Spaces,
Section 071Y; Cohomology of Schemes, Lemma 01XB). -/
theorem baseChangeAcyclic_affineEtale :
    letI (y : AffineEtale B S hS F) :=
      Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, w}
        (overRingSheaf (affineEtaleRingRestriction B S hS F hF) y)
    Stacks.UniverseLift.BaseChangeAcyclic.{max (u + 1) w} (affineEtaleRingRestriction B S hS F hF)
      (mul_comm_affineEtaleRingRestriction B S hS F hF)
      (baseChangeIsSheaf_affineEtale.{u, w} B S hS F hF) :=
  fun x N V p hp =>
    Stacks.AffineSiteBaseChange.isZero_rightDerived_evaluation_baseChange.{max (u + 1) w}
      (AffineEtale.isFlatCofinal B S hS F) x N
      (baseChangeIsSheaf_affineEtale.{u, w} B S hS F hF x N) V p hp

open Stacks.Sites.OverModules in
/-- **Hypothesis (2) of Stacks 0GZS for the affine étale site of `F`**: for every affine chart
`U` and every K-flat complex `M^•` of `𝒪(U)`-modules, `M^• ⟶ RΓ((F_{affine,étale}/U),
(M^• ⊗_{𝒪(U)} 𝒪_U)^#)` is a quasi-isomorphism. It follows from the two halves of the base-change
hypothesis, `baseChangeIsSheaf_affineEtale` and `baseChangeAcyclic_affineEtale`. -/
theorem isLocallyKFlatAcyclic_affineEtale :
    IsLocallyKFlatAcyclic.{w} (affineEtaleRingRestriction B S hS F hF)
      (mul_comm_affineEtaleRingRestriction B S hS F hF) :=
  Stacks.UniverseLift.isLocallyKFlatAcyclic_of_baseChangeAcyclic _ _
    (baseChangeIsSheaf_affineEtale.{u, w} B S hS F hF)
    (baseChangeAcyclic_affineEtale.{u, w} B S hS F hF)

/-- The canonical base-change datum of the restricted structure sheaf on the affine étale
charts, through which `QC(F_{affine}, 𝒪_F)` (Stacks 0GYU) is read. -/
noncomputable abbrev affineEtaleBaseChangeData :=
  baseChangeDataOfComm.{u, u, u + 1, w} (affineEtaleRingRestriction B S hS F hF).obj
    (mul_comm_affineEtaleRingRestriction B S hS F hF)

/-- **Stacks 0GZS on the affine étale site of `F`**: `Rε_*` and `ε^*` are quasi-inverse
equivalences between the full subcategory of `D(F_{affine,étale}, 𝒪_F)` of the objects `K` with
`Rε_*K` cartesian and `QC(F_{affine}, 𝒪_F)`, where `ε` is the change from the étale to the
chaotic topology on the affine étale charts. -/
noncomputable def affineEtaleCartesianPushforwardEquivalence :
    (IsCartesianPushforward.{w} (affineEtaleRingRestriction B S hS F hF)
      (affineEtaleBaseChangeData.{u, w} B S hS F hF)).FullSubcategory ≌
      QC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF) :=
  cartesianEquivalenceOfLocallyKFlatAcyclic.{w} (affineEtaleRingRestriction B S hS F hF)
    (mul_comm_affineEtaleRingRestriction B S hS F hF)
    (isLocallyKFlatAcyclic_affineEtale.{u, w} B S hS F hF)

/-- The restricted structure sheaf has commuting sections, as an instance. -/
instance commSections_affineEtaleRingRestriction :
    Stacks.TerminalBaseChange.CommSections (affineEtaleRingRestriction B S hS F hF).obj :=
  ⟨mul_comm_affineEtaleRingRestriction B S hS F hF⟩

/-- **The restriction maps of the restricted structure sheaf are flat**: a morphism of affine
étale charts is flat on the underlying affine schemes. -/
theorem flat_affineEtaleRingRestriction_map ⦃U V : (AffineEtale B S hS F)ᵒᵖ⦄ (a : V ⟶ U) :
    RingHom.Flat ((affineEtaleRingRestriction B S hS F hF).obj.map a).hom :=
  flat_affineEtaleChartRings_map B S hS F a.unop

/-- **A cartesian presheaf of modules on the affine étale site is a sheaf**
(`Stacks.AffineSiteBaseChange.isSheaf_of_isCartesianPresheaf`). -/
theorem isSheaf_of_isCartesianPresheaf_affineEtale
    (P : PresheafOfModules.{max (u + 1) w} (affineEtaleRingRestriction B S hS F hF).obj)
    (hP : IsCartesianPresheaf P) : Presheaf.IsSheaf (AffineEtale.topology B S hS F) P.presheaf :=
  Stacks.AffineSiteBaseChange.isSheaf_of_isCartesianPresheaf.{max (u + 1) w}
    (AffineEtale.isFlatCofinal B S hS F) P hP

open Stacks.Sites.OverModules in
/-- **A cartesian sheaf of modules on the affine étale site has no higher cohomology over any
affine chart**: on the slice at the chart it is the base change of its sections there, which
is acyclic by `baseChangeAcyclic_affineEtale`. -/
theorem isZero_rightDerived_evaluation_of_isCartesianPresheaf_affineEtale
    (G : SheafOfModules.{max (u + 1) w} (affineEtaleRingRestriction B S hS F hF))
    (hG : IsCartesianPresheaf G.val) (U : AffineEtale B S hS F) (p : ℕ) (hp : 0 < p) :
    letI := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, w}
      (affineEtaleRingRestriction B S hS F hF)
    IsZero (((SheafOfModules.evaluation (affineEtaleRingRestriction B S hS F hF)
      (op U)).rightDerived p).obj G) := by
  let := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, w}
    (affineEtaleRingRestriction B S hS F hF)
  exact isZero_rightDerived_evaluation_of_isCartesianPresheaf.{w}
    (affineEtaleRingRestriction B S hS F hF) (mul_comm_affineEtaleRingRestriction B S hS F hF)
    (baseChangeIsSheaf_affineEtale.{u, w} B S hS F hF)
    (baseChangeAcyclic_affineEtale.{u, w} B S hS F hF) G hG U p hp

/-- **On the affine étale site, the subcategory of Stacks 0GZS is `D_QCoh`**: an object `K` of
`D(F_{affine,étale}, 𝒪_F)` has `Rε_*K` cartesian exactly when all of its cohomology sheaves are
quasi-coherent. By `isCartesianPushforward_iff_isCartesianPresheaf_homology` the condition is
that the cohomology sheaves be cartesian, its three inputs being flatness of the restriction
maps, the sheaf property of cartesian presheaves and the acyclicity of cartesian sheaves; and a
sheaf on the affine étale site is cartesian exactly when it is quasi-coherent
(`isCartesianPresheaf_iff_isQuasicoherentOnSite_affineEtale`). -/
theorem isCartesianPushforward_affineEtale_iff
    (K : DerivedCategory
      (SheafOfModules.{max (u + 1) w} (affineEtaleRingRestriction B S hS F hF))) :
    IsCartesianPushforward.{w} (affineEtaleRingRestriction B S hS F hF)
        (affineEtaleBaseChangeData.{u, w} B S hS F hF) K ↔
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
        max (u + 1) w} (affineEtaleRingRestriction B S hS F hF)) K := by
  let := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, w}
    (affineEtaleRingRestriction B S hS F hF)
  refine (isCartesianPushforward_iff_isCartesianPresheaf_homology.{w}
    (affineEtaleRingRestriction B S hS F hF) (flat_affineEtaleRingRestriction_map B S hS F hF) _
    (isSheaf_of_isCartesianPresheaf_affineEtale.{u, w} B S hS F hF)
    (isZero_rightDerived_evaluation_of_isCartesianPresheaf_affineEtale.{u, w} B S hS F hF) K).trans
    ?_
  exact forall_congr' fun n =>
    isCartesianPresheaf_iff_isQuasicoherentOnSite_affineEtale.{u, w} B S hS F hF _

/-! ### The four categories -/

/-- **The affine étale charts of `F` with the chaotic topology**, carrying the structure sheaf of
`D_QCoh(𝒪_F)` restricted to the affine charts: the ringed site `(F_{affine}, 𝒪_F)` of categories
(3) and (4) of Stacks 0H06. For the chaotic topology every presheaf is a sheaf
(`CategoryTheory.Presheaf.isSheaf_bot`).

It differs from `AlgebraicGeometry.Space.affineEtaleChaoticRingedSite` only in its structure
sheaf, which here has its rings of sections in the universe of the schemes, as the structure
sheaf of `D_QCoh(𝒪_F)` does, rather than raised to the universe of the charts; that is what lets
it be compared with categories (1) and (2) on the nose. -/
noncomputable abbrev affineEtaleChartChaoticRingedSite : RingedSite.{u + 1, u, u} where
  C := AffineEtale B S hS F
  J := ⊥
  O := ⟨(affineEtaleRingedSite B S hS F hF).O.obj, Presheaf.isSheaf_bot _⟩

/-- The topology of `affineEtaleChartChaoticRingedSite` is the chaotic one. -/
theorem affineEtaleChartChaoticRingedSite_J :
    (affineEtaleChartChaoticRingedSite B S hS F hF).J = ⊥ := rfl

/-- **Category (2) of Stacks 0H06**, `D_QCoh(F_{affine,étale}, 𝒪_F)`: the full subcategory of the
derived category of sheaves of modules on the affine étale site of `F`, over the restricted
structure sheaf, of the objects all of whose cohomology sheaves are quasi-coherent. -/
noncomputable abbrev affineEtaleChartQuasicoherentDerivedCategory :=
  (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
    max (u + 1) w} (affineEtaleRingRestriction B S hS F hF))).FullSubcategory

/-- **Quasi-coherent cohomology on the chaotic affine étale charts**: the condition on an object
of `D(F_{affine}, 𝒪_F)` that all of its cohomology sheaves be quasi-coherent, which cuts out
category (3) of Stacks 0H06. By definition it is
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.hasQuasicoherentCohomology` of the chaotic
ringed site of the affine charts (`hasQuasicoherentCohomologyAffineEtaleChart_iff`).

What this adds is the name of the ambient derived category: `hasQuasicoherentCohomology` reads
`D(F_{affine}, 𝒪_F)` off the chaotic ringed site, while categories (2) and (4) and the derived
pushforward `Rε_*` read it as the derived category of the modules over the restricted structure
sheaf `AlgebraicGeometry.Space.affineEtaleRingRestriction`. The two are the same category, but
the translation of a full subcategory is built from the translation of the category it sits in,
so only after fixing one of the two names is the translation of (3) the translation of (4) and
the translation on the target of `Rε_*`; that is what makes the equivalences of the tag exact on
the nose rather than only up to an identification. -/
noncomputable def hasQuasicoherentCohomologyAffineEtaleChart :
    ObjectProperty (DMod.{w} (affineEtaleRingRestriction B S hS F hF).obj) :=
  hasQuasicoherentCohomology.{w} (affineEtaleChartChaoticRingedSite B S hS F hF)

/-- An object of `D(F_{affine}, 𝒪_F)` satisfies
`AlgebraicGeometry.Space.hasQuasicoherentCohomologyAffineEtaleChart` exactly when all of its
cohomology sheaves on the chaotic affine étale ringed site are quasi-coherent. -/
theorem hasQuasicoherentCohomologyAffineEtaleChart_iff
    (K : DMod.{w} (affineEtaleRingRestriction B S hS F hF).obj) :
    hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF K ↔
      hasQuasicoherentCohomology.{w} (affineEtaleChartChaoticRingedSite B S hS F hF) K :=
  Iff.rfl

/-- **Category (3) of Stacks 0H06**, `D_QCoh(F_{affine}, 𝒪_F)`: the full subcategory of the derived
category of modules on the chaotic affine étale site of `F` of the objects all of whose
cohomology sheaves are quasi-coherent. Category (4), `QC(F_{affine}, 𝒪_F)`, is
`QC (affineEtaleBaseChangeData B S hS F hF)`. -/
noncomputable abbrev affineEtaleChartChaoticQuasicoherentDerivedCategory :=
  (hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF).FullSubcategory

/-- `D_QCoh(F_{affine,étale}, 𝒪_F)` is closed under isomorphisms in the derived category. -/
instance isClosedUnderIsomorphisms_affineEtaleChartQuasicoherentDerived :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
      max (u + 1) w} (affineEtaleRingRestriction B S hS F hF))).IsClosedUnderIsomorphisms :=
  ⟨fun {_ _} e hX n ↦
    (inferInstance : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
        (affineEtaleRingRestriction B S hS F hF)).IsClosedUnderIsomorphisms).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (hX n)⟩

/-! ### (3) ≃ (4) -/

/-- **Categories (3) and (4) of Stacks 0H06 agree.** On the chaotic affine étale site of `F`, an
object of the derived category of modules is cartesian in the sense of Stacks 0GYU exactly when
all of its cohomology sheaves are quasi-coherent, for every base-change datum.

This is Stacks 0GZR, `isQC_iff_hasQuasicoherentCohomology`: a morphism of affine étale charts is
flat on the underlying affine schemes, so the restriction maps of `𝒪_F` are flat
(`AlgebraicGeometry.Space.flat_affineEtaleChartRings_map`). -/
theorem isQC_iff_hasQuasicoherentCohomology_affineEtaleChartChaotic
    (bc : BaseChangeData.{w} (affineEtaleRingRestriction B S hS F hF).obj)
    (K : DMod.{w} (affineEtaleRingRestriction B S hS F hF).obj) :
    IsQC.{w} bc K ↔
      hasQuasicoherentCohomology.{w} (affineEtaleChartChaoticRingedSite B S hS F hF) K :=
  isQC_iff_hasQuasicoherentCohomology.{w, u + 1, u, u}
    (affineEtaleChartChaoticRingedSite B S hS F hF) rfl
    (fun a => flat_affineEtaleChartRings_map B S hS F a.unop) bc K

/-- **The equivalence of categories (3) and (4) of Stacks 0H06**,
`D_QCoh(F_{affine}, 𝒪_F) ≌ QC(F_{affine}, 𝒪_F)`: the two are the same full subcategory of
`D(F_{affine}, 𝒪_F)`, by
`AlgebraicGeometry.Space.isQC_iff_hasQuasicoherentCohomology_affineEtaleChartChaotic`, and the
equivalence is the identity on objects. -/
noncomputable def affineEtaleChartChaoticQuasicoherentQCEquivalence :
    affineEtaleChartChaoticQuasicoherentDerivedCategory.{u, w} B S hS F hF ≌
      QC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF) :=
  (CategoryTheory.Equivalence.refl (C := DMod.{w}
      (affineEtaleRingRestriction B S hS F hF).obj)).congrFullSubcategory
    (P := hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF)
    (Q := IsQC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF))
    (funext fun K => propext
      (isQC_iff_hasQuasicoherentCohomology_affineEtaleChartChaotic.{u, w} B S hS F hF
        (affineEtaleBaseChangeData.{u, w} B S hS F hF) K))

/-- **The equivalence of categories (3) and (4) of Stacks 0H06 is the identity of
`D(F_{affine}, 𝒪_F)`**: its functor, followed by the inclusion of `QC(F_{affine}, 𝒪_F)`, is the
inclusion of `D_QCoh(F_{affine}, 𝒪_F)`. -/
theorem affineEtaleChartChaoticQuasicoherentQCEquivalence_functor_comp_ι :
    (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).functor ⋙
        ObjectProperty.ι (IsQC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF)) =
      ObjectProperty.ι (hasQuasicoherentCohomologyAffineEtaleChart.{u, w} B S hS F hF) :=
  rfl

/-! ### (2) ≃ (3) -/

/-- **`D_QCoh(F_{affine,étale}, 𝒪_F)` is the subcategory of Stacks 0GZS**: the identity of the
derived category, cut down along
`AlgebraicGeometry.Space.isCartesianPushforward_affineEtale_iff`. -/
noncomputable def affineEtaleChartQuasicoherentDerivedCartesianEquivalence :
    affineEtaleChartQuasicoherentDerivedCategory.{u, w} B S hS F hF ≌
      (IsCartesianPushforward.{w} (affineEtaleRingRestriction B S hS F hF)
        (affineEtaleBaseChangeData.{u, w} B S hS F hF)).FullSubcategory :=
  (CategoryTheory.Equivalence.refl.congrFullSubcategory
      (P := IsCartesianPushforward.{w} (affineEtaleRingRestriction B S hS F hF)
        (affineEtaleBaseChangeData.{u, w} B S hS F hF))
      (Q := DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u,
        max (u + 1) w} (affineEtaleRingRestriction B S hS F hF)))
      (funext fun K => propext
        (isCartesianPushforward_affineEtale_iff.{u, w} B S hS F hF K).symm)).symm

/-- **Categories (2) and (3) of Stacks 0H06 are equivalent**: for the change of topology
`ε : (F_{affine,étale}, 𝒪_F) ⟶ (F_{affine}, 𝒪_F)` from the étale to the chaotic topology on the
affine étale charts, `Rε_*` is an equivalence

`D_QCoh(F_{affine,étale}, 𝒪_F) ≌ D_QCoh(F_{affine}, 𝒪_F)`

with quasi-inverse `ε^*`.

It is Stacks 0GZS for `ε` (`AlgebraicGeometry.Space.affineEtaleCartesianPushforwardEquivalence`),
whose hypothesis is `AlgebraicGeometry.Space.isLocallyKFlatAcyclic_affineEtale`, with its source
identified with `D_QCoh(F_{affine,étale}, 𝒪_F)`
(`AlgebraicGeometry.Space.affineEtaleChartQuasicoherentDerivedCartesianEquivalence`) and its
target with `D_QCoh(F_{affine}, 𝒪_F)`
(`AlgebraicGeometry.Space.affineEtaleChartChaoticQuasicoherentQCEquivalence`). That its functor
is `Rε_*` is `affineEtaleChartQuasicoherentDerivedChaoticEquivalence_functor_comp_ι`. -/
noncomputable def affineEtaleChartQuasicoherentDerivedChaoticEquivalence :
    affineEtaleChartQuasicoherentDerivedCategory.{u, w} B S hS F hF ≌
      affineEtaleChartChaoticQuasicoherentDerivedCategory.{u, w} B S hS F hF :=
  (affineEtaleChartQuasicoherentDerivedCartesianEquivalence.{u, w} B S hS F hF).trans
    ((affineEtaleCartesianPushforwardEquivalence.{u, w} B S hS F hF).trans
      (affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF).symm)

/-- **The equivalence of categories (2) and (3) of Stacks 0H06 is `Rε_*`**: its functor, followed
by the inclusion of `D_QCoh(F_{affine}, 𝒪_F)` into `D(F_{affine}, 𝒪_F)`, is the inclusion of
`D_QCoh(F_{affine,étale}, 𝒪_F)` followed by the derived pushforward `Rε_*`. -/
theorem affineEtaleChartQuasicoherentDerivedChaoticEquivalence_functor_comp_ι :
    (affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F hF).functor ⋙
        ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ derivedEpsilonPushforward.{w} (affineEtaleRingRestriction B S hS F hF) :=
  rfl

/-! ### (1) ≃ (2) -/

/-- **Categories (1) and (2) of Stacks 0H06 are equivalent**: restriction to the affine étale
charts induces an equivalence

`D_QCoh(𝒪_F) ≌ D_QCoh(F_{affine,étale}, 𝒪_F)`.

Restriction of sheaves of `𝒪_F`-modules to the affine charts is an equivalence of abelian
categories (`AlgebraicGeometry.Space.affineEtaleRestrictionEquivalence`, the Comparison Lemma
along the dense subsite inclusion of Stacks 04JS, i.e. the equivalence of ringed topoi of
Stacks 0H03 on modules); it is exact, so it derives to an equivalence of the unbounded derived
categories, and it preserves and reflects quasi-coherence
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModulePushforward_iff`), so that
equivalence matches the two subcategories. Its functor is the derived functor of restriction,
`quasicoherentDerivedAffineEtaleChartEquivalence_functor_obj_obj`. -/
noncomputable def quasicoherentDerivedAffineEtaleChartEquivalence :
    QuasicoherentDerivedCategory.{u, max (u + 1) w} B S hS F hF ≌
      affineEtaleChartQuasicoherentDerivedCategory.{u, w} B S hS F hF :=
  letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
    HasDerivedCategory.standard _
  haveI : (affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF).functor.Additive :=
    ⟨rfl⟩
  Stacks.UniverseLift.derivedCategoryBEquivalence
    (affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleRingedSite B S hS F hF).O))
    (isQuasicoherentOnSite_affineEtaleModulePushforward_iff.{u, max (u + 1) w} B S hS F hF)

/-- **The equivalence of categories (1) and (2) of Stacks 0H06 is derived restriction**: it sends
an object of `D_QCoh(𝒪_F)` to the image of the underlying complex under the derived functor of
restriction to the affine charts. -/
theorem quasicoherentDerivedAffineEtaleChartEquivalence_functor_obj_obj
    (K : QuasicoherentDerivedCategory.{u, max (u + 1) w} B S hS F hF) :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    haveI : (affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF).functor.Additive :=
      ⟨rfl⟩
    ((quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).functor.obj K).obj =
      (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
        B S hS F hF).functor.mapDerivedCategory.obj K.obj :=
  rfl

/-- **The equivalence of categories (1) and (2) of Stacks 0H06 is derived restriction**, as an
equality of functors into `D(F_{affine,étale}, 𝒪_F)`: the functor of the equivalence, followed by
the inclusion of `D_QCoh(F_{affine,étale}, 𝒪_F)`, is the inclusion of `D_QCoh(𝒪_F)` followed by
the derived functor of restriction to the affine charts. This is
`AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChartEquivalence_functor_obj_obj` read on
functors rather than on objects. -/
theorem quasicoherentDerivedAffineEtaleChartEquivalence_functor_comp_ι :
    letI : HasDerivedCategory (Modules.{u, max (u + 1) w} B S hS F hF) :=
      HasDerivedCategory.standard _
    haveI : (affineEtaleRestrictionEquivalence.{u, max (u + 1) w} B S hS F hF).functor.Additive :=
      ⟨rfl⟩
    (quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF).functor ⋙
        ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
            (affineEtaleRingRestriction B S hS F hF))) =
      ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) w}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) ⋙
        (affineEtaleRestrictionEquivalence.{u, max (u + 1) w}
          B S hS F hF).functor.mapDerivedCategory :=
  rfl

/-! ### The chain -/

/-- **Stacks 0H06.** For an algebraic space `F` over `S`, the four categories

1. `D_QCoh(𝒪_F)`,
2. `D_QCoh(F_{affine,étale}, 𝒪_F)`,
3. `D_QCoh(F_{affine}, 𝒪_F)`, and
4. `QC(F_{affine}, 𝒪_F)`

are equivalent, by the canonical equivalences `(1) ≌ (2)` induced by restriction to the affine
charts (`AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChartEquivalence`),
`(2) ≌ (3)` given by `Rε_*` for the change of topology from the étale to the chaotic topology
(`AlgebraicGeometry.Space.affineEtaleChartQuasicoherentDerivedChaoticEquivalence`), and
`(3) ≌ (4)` the identity of the common full subcategory of `D(F_{affine}, 𝒪_F)`
(`AlgebraicGeometry.Space.affineEtaleChartChaoticQuasicoherentQCEquivalence`).  The tag is
registered here, for the equivalences, and in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineEtaleQuasicoherentDerivedChainTriangulated.lean`, for
the triangulated structure of the four categories and the exactness of the three equivalences;
the three component equivalences above are not registered separately. -/
@[stacks 0H06 "the chain of equivalences (1) ≃ (2) ≃ (3) ≃ (4)"]
noncomputable def quasicoherentDerivedAffineEtaleChain :
    (QuasicoherentDerivedCategory.{u, max (u + 1) w} B S hS F hF ≌
        affineEtaleChartQuasicoherentDerivedCategory.{u, w} B S hS F hF) ×
      (affineEtaleChartQuasicoherentDerivedCategory.{u, w} B S hS F hF ≌
        affineEtaleChartChaoticQuasicoherentDerivedCategory.{u, w} B S hS F hF) ×
      (affineEtaleChartChaoticQuasicoherentDerivedCategory.{u, w} B S hS F hF ≌
        QC.{w} (affineEtaleBaseChangeData.{u, w} B S hS F hF)) :=
  ⟨quasicoherentDerivedAffineEtaleChartEquivalence.{u, w} B S hS F hF,
    affineEtaleChartQuasicoherentDerivedChaoticEquivalence.{u, w} B S hS F hF,
    affineEtaleChartChaoticQuasicoherentQCEquivalence.{u, w} B S hS F hF⟩

end AlgebraicGeometry.Space
