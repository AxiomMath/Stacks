module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHigherDirectImagesQcqs
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleComparisonAcyclicity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcFbcAffineObjectCohomologyVanishing

/-!
# Change of topology for a locally quasi-coherent module with flat base change (Stacks 075R)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `ℱ` be a presheaf of
`𝒪_𝒳`-modules such that

* (a) `ℱ` is locally quasi-coherent (**Stacks 06WJ**), and
* (b) for every arrow `φ : x ⟶ y` of `𝒳` lying over a morphism of schemes `f : U ⟶ V` which is
  flat and locally of finite presentation, the comparison map
  `c_φ : f_{small}^*ℱ|_{V_{étale}} ⟶ ℱ|_{U_{étale}}` of **Stacks 06WC** is an isomorphism.

**Stacks 075R** says that `ℱ` is then an `𝒪_𝒳`-module, that is a sheaf for the fppf topology,
and that for the comparison morphism `ε : 𝒳_{fppf} ⟶ 𝒳_{étale}` the higher direct images
vanish, `Rε_*ℱ = ε_*ℱ`; its further clauses compare fppf and étale cohomology of `ℱ`.

## The argument

The first assertion is **Stacks 076T**. For the vanishing, `ε` is given by the identity functor
of `𝒳`, so by **Stacks 072W** the sheaf `R^iε_*ℱ` is the étale sheafification of the presheaf
`x ↦ H^i_{fppf}(x, ℱ)`; that presheaf vanishes on the objects lying over an affine scheme, which
cover every object for the étale topology, so it sheafifies to zero. The vanishing over an
object lying over an affine scheme is
`AlgebraicGeometry.Stack.isZero_sheafCohomology_of_isLocallyQuasicoherent`, the Čech argument of
**Stacks 03F9** with the Amitsur complex of **Stacks 03FJ**, read for sheaves of modules through
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv`.

## Main results

* `AlgebraicGeometry.Stack.isSheaf_fppf_of_lqc_flatLfp` and
  `AlgebraicGeometry.Stack.lqcFbcModule`: **Stacks 075R**, the first assertion: `ℱ` is an
  `𝒪_𝒳`-module.
* `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_lqc_flatLfp`: `H^i_{fppf}(x, ℱ) = 0`
  for `i > 0` and `x` lying over an affine scheme.
* `AlgebraicGeometry.Stack.hasAffineAcyclicLqcFbcModules`: the affine-object vanishing
  `AlgebraicGeometry.Stack.HasAffineAcyclicLqcFbcModules`, which the statements of
  **Stacks 08IY**, **Stacks 08IZ** and the conditional form of 075R take as a hypothesis.
* `AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule`:
  **Stacks 075R (1)**, `R^iε_*ℱ = 0` for `i > 0`.

## Implementation notes

The total category of `𝒳` has its morphisms in the universe `u` of the schemes, as an algebraic
stack has, and is assumed essentially small relative to `u`. This is the convention of the source
that a category has a *set* of objects (Categories, Definition 0014; Sites, Remark 00VI), read in
the universe of the schemes; it is what makes the sheaves of `𝒪_𝒳`-modules with sections in
`Type u` a Grothendieck abelian category, so that the derived functors of the statement exist.
All the homological inputs — sheafification, enough injectives, `Ext`-groups — are derived from
it here and are not hypotheses.

## References

* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

/- The instances `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and its two companions are
stated for sheaves of modules in a universe of the shape `max u v r w`, and
`AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor` for limits of size
`HasLimitsOfSize.{w, max v w}`; at the module and sheaf categories of this file their universe
unification problems get stuck, so they are switched off here. The structures they would provide
come from the essential smallness of the sites. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section Module

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
  (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) F)

include hlqc hbc in
/-- **Stacks 075R, the first assertion.** A presheaf of `𝒪_𝒳`-modules which is locally
quasi-coherent (**Stacks 06WJ**) and whose comparison maps `c_φ` of **Stacks 06WC** are
isomorphisms along the arrows lying over flat morphisms locally of finite presentation is a sheaf
for the fppf topology of `𝒳`, that is, an `𝒪_𝒳`-module. -/
@[stacks 075R "the first assertion: a presheaf of modules satisfying (a) and (b) is an \
𝒪_𝒳-module, i.e. a sheaf for the fppf topology"]
theorem isSheaf_fppf_of_lqc_flatLfp :
    Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf) F.presheaf :=
  isSheaf_fppf_of_isLocallyQuasicoherent_of_flatBaseChange B E h S hS p hp F hlqc hbc

/-- **The `𝒪_𝒳`-module of Stacks 075R.** A presheaf of `𝒪_𝒳`-modules satisfying (a) and (b)
of Stacks 075R, as an object of `Mod(𝒪_𝒳)` on the fppf site, by
`AlgebraicGeometry.Stack.isSheaf_fppf_of_lqc_flatLfp`. -/
def lqcFbcModule : fppfSiteModules B S hS p hp where
  val := F
  isSheaf := isSheaf_fppf_of_lqc_flatLfp B E h S hS p hp F hlqc hbc

/-- The underlying presheaf of modules of `AlgebraicGeometry.Stack.lqcFbcModule` is `F`. -/
@[simp]
theorem lqcFbcModule_val : (lqcFbcModule B E h S hS p hp F hlqc hbc).val = F :=
  rfl

end Module

/-- The `𝒪_𝒳`-modules on the fppf site of an essentially small category fibred in groupoids have
enough injectives: they form a Grothendieck abelian category. Unlike
`AlgebraicGeometry.Stack.enoughInjectives_fppfSiteModules_of_univLE`, no bound is imposed on the
universes of the objects of `𝒳`, so this applies to an algebraic stack, whose objects live in
`Type (u + 1)`. -/
theorem enoughInjectives_fppfSiteModules_of_essentiallySmall {𝒳 : Type v} [Category.{u} 𝒳]
    [EssentiallySmall.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) :
    EnoughInjectives (fppfSiteModules B S hS p hp) :=
  have := hasSheafifyEssentiallySmallSite.{u}
    (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}
  have := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .fppf
  have := SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (fppfSiteRingSheaf B S hS p hp)
  inferInstance

section EssentiallySmall

variable {𝒳 : Type v} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology

/-- Abelian sheaves on the associated sites of an essentially small category fibred in groupoids
have enough injectives. -/
theorem enoughInjectives_siteKindTopology_of_essentiallySmall (τ : SiteKind) :
    EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{u}) :=
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite _

attribute [local instance] enoughInjectives_siteKindTopology_of_essentiallySmall
  enoughInjectives_fppfSiteModules_of_essentiallySmall
  Stacks.Cohomology.AcyclicCover.evaluation_additive

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
  (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) F)

include hlqc hbc in
/-- **The higher fppf cohomology of the module of Stacks 075R vanishes over the objects lying over
an affine scheme.** For `x` lying over an affine scheme and `i > 0`,
`H^i_{fppf}(x, ℱ) = 0`, cohomology of `𝒪_𝒳`-modules, the right derived functors of the sections
over `x`. -/
theorem isZero_rightDerived_evaluation_of_lqc_flatLfp (x : 𝒳)
    (hx : IsAffineOver B S hS (p.obj x)) (i : ℕ) (hi : 0 < i) :
    IsZero (((SheafOfModules.evaluation.{u} (fppfSiteRingSheaf B S hS p hp)
      (op x)).rightDerived i).obj
      (lqcFbcModule B E h S hS p hp F hlqc hbc)) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hi).symm⟩
  have hu := Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite.{u}
    (BigFppfOver.associatedTopology B S hS p .fppf)
  have h₀ := isZero_sheafCohomology_of_isLocallyQuasicoherent.{u} B E h S hS p hp F hlqc hbc
    (isSheaf_fppf_of_lqc_flatLfp B E h S hS p hp F hlqc hbc) x hx (j + 1) (Nat.succ_pos j)
  have hmax := Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse
    (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})
  have := Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse
    (fppfSiteModules B S hS p hp)
  have h₁ := Stacks.Cohomology.ModuleDirectImageOnACover.isZero_sheafCohomology_chgUniv.{v, u, u,
    max v u} (BigFppfOver.associatedTopology B S hS p .fppf) _ _ _ h₀
  exact Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'
    (BigFppfOver.associatedTopology B S hS p .fppf) (fppfSiteRingSheaf B S hS p hp) x j
    (lqcFbcModule B E h S hS p hp F hlqc hbc) h₁

include hlqc hbc in
/-- **Stacks 075R, clause (1).** Let `ℱ` be a presheaf of `𝒪_𝒳`-modules which is locally
quasi-coherent (**Stacks 06WJ**) and whose comparison maps `c_φ` of **Stacks 06WC** are
isomorphisms along the arrows lying over flat morphisms locally of finite presentation, and let
`ε : 𝒳_{fppf} ⟶ 𝒳_{étale}` be the comparison morphism. Then

`R^iε_*ℱ = 0` for `i > 0`,

that is, `Rε_*ℱ = ε_*ℱ`. Here `ℱ` is the `𝒪_𝒳`-module of the first assertion,
`AlgebraicGeometry.Stack.lqcFbcModule`. -/
@[stacks 075R "clause (1): `Rε_*ℱ = ε_*ℱ`, i.e. `R^iε_*ℱ = 0` for `i > 0`, for the comparison \
`ε : 𝒳_fppf ⟶ 𝒳_étale` and a module satisfying (a) and (b)"]
theorem isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule (i : ℕ) (hi : 0 < i) :
    IsZero (((etaleComparisonPushforward B S hS p hp).rightDerived i).obj
      (lqcFbcModule B E h S hS p hp F hlqc hbc)) := by
  classical
  set Je := BigFppfOver.associatedTopology B S hS p .etale with hJe
  set R := fppfSiteRingSheaf B S hS p hp with hR
  set Re := etaleSiteRingSheaf B S hS p hp with hRe
  set φ := etaleComparisonRingMap B S hS p hp with hφ
  set P := cohPresheafModule (Functor.id 𝒳) R Re φ i (lqcFbcModule B E h S hS p hp F hlqc hbc)
    with hP
  obtain ⟨e⟩ := higherDirectImage_iso_sheafify_cohomologyPresheaf (Functor.id 𝒳) R Re φ i
    (lqcFbcModule B E h S hS p hp F hlqc hbc)
  refine IsZero.of_iso ?_ e
  have hPzero : ∀ V : 𝒳, IsAffineOver B S hS (p.obj V) → IsZero (P.obj (op V)) := by
    intro V hV
    obtain ⟨eV⟩ := cohPresheafModule_evaluation_iso (Functor.id 𝒳) R Re φ i
      (lqcFbcModule B E h S hS p hp F hlqc hbc) V
    refine IsZero.of_iso ?_ eV
    exact Functor.map_isZero _
      (isZero_rightDerived_evaluation_of_lqc_flatLfp B E h S hS p hp F hlqc hbc V hV i hi)
  refine Stacks.Cohomology.ModuleLocalVanishing.isZero_sheafification_of_locallyZero _ P ?_
  intro U x
  obtain ⟨I, y, ψ, hyaff, hcov⟩ := exists_affine_ofArrows_etale B S hS p hp U
  refine Je.superset_covering ?_ hcov
  intro V g hg
  rw [Sieve.mem_ofArrows_iff] at hg
  obtain ⟨j, b, rfl⟩ := hg
  have hsub : Subsingleton (ToType (P.obj (op (y j)))) :=
    ModuleCat.isZero_iff_subsingleton.1 (hPzero (y j) (hyaff j))
  change P.presheaf.map (b ≫ ψ j).op x = P.presheaf.map (b ≫ ψ j).op 0
  have hfac : (b ≫ ψ j).op = (ψ j).op ≫ b.op := rfl
  rw [hfac, P.presheaf.map_comp]
  have hmid : P.presheaf.map (ψ j).op x = P.presheaf.map (ψ j).op 0 :=
    hsub.elim _ _
  simp only [ConcreteCategory.comp_apply, hmid]

/-- **The affine-object vanishing for the modules in `LQCoh^fbc(𝒪_𝒳)`.** The predicate
`AlgebraicGeometry.Stack.HasAffineAcyclicLqcFbcModules`, which the statements of
**Stacks 08IY**, **Stacks 08IZ** and the reduction of **Stacks 075R** in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/EtaleComparisonAcyclicity.lean` take as a
hypothesis, holds on an essentially small category fibred in groupoids: a module with the flat base
change property has in particular hypothesis (b) of Stacks 075R, and
`AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_lqc_flatLfp` applies. -/
theorem hasAffineAcyclicLqcFbcModules : HasAffineAcyclicLqcFbcModules B E h S hS p hp := by
  intro F hF x hx i hi
  exact isZero_rightDerived_evaluation_of_lqc_flatLfp B E h S hS p hp F.val hF.1
    (hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F.val hF.2)
    x hx i hi

end EssentiallySmall

end AlgebraicGeometry.Stack

end
