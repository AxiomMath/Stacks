module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedUnitLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.DerivedExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineEtaleDerivedPushforwardSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionCollections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image on quasi-coherent modules and `Rf_*`

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, with `X` and `Y`
quasi-compact with affine diagonal over `ℤ`.  [Stacks, Tag 0CSR] says that the right derived
functor `Φ` of `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` and the derived direct image `Rf_*` commute with
the comparison functors `D(QCoh(𝒪_-)) ⥤ D_QCoh(𝒪_-)` of [Stacks, Tag 08F1].  This file carries
out the source's proof.

## The proof

The square commutes through the canonical comparison
`Stacks.DerivedCoherator.pushforwardSquareComparison`, which is invertible exactly when the unit
`f_* I ⟶ Rf_* I` is invertible at every K-injective complex `I` of `QCoh(𝒪_X)`
(`AlgebraicGeometry.Space.derivedPushforwardSquareCommutes_iff`).  That condition, for every
`g : U ⟶ Z` with `Z` quasi-compact with affine diagonal, is the property `P(U)`,
`AlgebraicGeometry.Space.PushforwardComputesDerivedOnQuasicoherentKInjectives`, proved by the
induction principle of [Stacks, Tag 08GQ] in the collection of [Stacks, Tag 08GR] (2):

* **(3)(b)** For `U` affine, `g` is affine ([Stacks, Tag 08GB]) and every complex of
  quasi-coherent modules computes `Rg_*` ([Stacks, Tag 08GY]):
  `AlgebraicGeometry.Space.pushforwardComputesDerivedOnQuasicoherentKInjectives_of_isAffineSpace`.
* **The last paragraph.**  For `j : U ⟶ W` étale and `J` K-injective in `QCoh(𝒪_U)`, `j_* J` is
  K-injective in `QCoh(𝒪_W)` ([Stacks, Tag 08BJ]), and `P(U)` for `j` and `j ≫ g` shows that
  `g_*` computes `Rg_*` at `j_* J`:
  `AlgebraicGeometry.Space.pushforwardComputesDerivedAt_quasicoherentPushforward`.
* **(4)** For an elementary distinguished square `(U ⊆ W, V ⟶ W)`, the maps from a K-injective
  `I` to the direct images of K-injective resolutions of `I|_U` and `I|_V` span a distinguished
  triangle of `K(QCoh(𝒪_W))` whose third vertex is the direct image of a K-injective resolution of
  `I|_{U ×_W V}`: both it and the Mayer–Vietoris triangle of [Stacks, Tag 08GW] land in `D(𝒪_W)`
  with isomorphic first arrows (`AlgebraicGeometry.Space.exists_quasicoherentUnit_comp_eq`).
  Two out of three then gives `P(W)`:
  `AlgebraicGeometry.Space.pushforwardComputesDerivedOnQuasicoherentKInjectives_of_square`.

## Where [Stacks, Tag 08H1] enters

The source identifies `D(QCoh(𝒪_W))` with `D_QCoh(𝒪_W)` by [Stacks, Tag 08H1] before running the
induction, and so takes the Mayer–Vietoris triangle of `D(𝒪_W)` to be a triangle of
`D(QCoh(𝒪_W))`.  Here the identification is used exactly there: the third vertex of the triangle
of `K(QCoh(𝒪_W))` is recognised from its image in `D(𝒪_W)` because the derived inclusion is fully
faithful (`AlgebraicGeometry.Space.nonempty_iso_obj₃_of_square`).  The induction is stated with
that full faithfulness as an input,
`AlgebraicGeometry.Space.pushforwardComputesDerivedOnQuasicoherentKInjectives_of_fullyFaithful`.

## Implementation notes

`P(U)` is read on K-injective representatives: `g_*` computes `Rg_*` at a complex `M` when it
carries a K-injective resolution of `M` to a quasi-isomorphism
(`AlgebraicGeometry.Space.PushforwardComputesDerived`), which is independent of the chosen right
derived functor (`AlgebraicGeometry.Space.pushforwardComputesDerived_iff_isIso`).  Two out of
three is run in `K(QCoh(𝒪_W))` on the locus
`AlgebraicGeometry.Space.PushforwardComputesDerivedAt`, through the triangulated functor
`K(QCoh(𝒪_W)) ⥤ K(𝒪_W)`, so no triangulated structure on `Φ` is needed.

`HasDerivedCategory.standard` is a local instance, as it is where the comparison functor
`AlgebraicGeometry.Space.quasicoherentDerivedComparisonSchemeUniverse` of [Stacks, Tag 08F1] is
stated.

## References

* [Stacks Project, Tag 0CSR](https://stacks.math.columbia.edu/tag/0CSR)
* [Stacks Project, Tag 08H1](https://stacks.math.columbia.edu/tag/08H1)
* [Stacks Project, Tag 08GQ](https://stacks.math.columbia.edu/tag/08GQ)
* [Stacks Project, Tag 08GR](https://stacks.math.columbia.edu/tag/08GR)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08GY](https://stacks.math.columbia.edu/tag/08GY)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restriction of quasi-coherent modules along an étale morphism -/

section Restriction

variable {U W : AlgebraicSpaces B S hS} (j : U ⟶ W) (hj : IsEtale B S hS j.hom)

/-- Restriction `F ↦ F|_U` of quasi-coherent modules along an étale morphism `j : U ⟶ W`: the
corestriction of `AlgebraicGeometry.Space.etaleModulePullback`, which preserves quasi-coherence.
-/
def etaleQuasicoherentRestriction :
    QuasicoherentSheaves.{u, u} B S hS W.1 W.2 ⥤ QuasicoherentSheaves.{u, u} B S hS U.1 U.2 :=
  ObjectProperty.lift _ (quasicoherentSheavesι B S hS W ⋙ etaleModulePullback.{u, u} B S hS j hj)
    fun F => isQuasicoherentOnSite_etaleModulePullback B S hS j hj F.obj F.property

/-- Restriction of quasi-coherent modules along an étale morphism is additive. -/
instance etaleQuasicoherentRestriction_additive :
    (etaleQuasicoherentRestriction B S hS j hj).Additive where
  map_add := rfl

/-- Restriction of quasi-coherent modules along an étale morphism preserves finite limits. -/
instance preservesFiniteLimits_etaleQuasicoherentRestriction :
    PreservesFiniteLimits (etaleQuasicoherentRestriction B S hS j hj) :=
  have : PreservesFiniteLimits
      (etaleQuasicoherentRestriction B S hS j hj ⋙ quasicoherentSheavesι B S hS U) :=
    inferInstanceAs (PreservesFiniteLimits
      (quasicoherentSheavesι B S hS W ⋙ etaleModulePullback.{u, u} B S hS j hj))
  preservesFiniteLimits_of_reflects_of_preserves _ (quasicoherentSheavesι B S hS U)

/-- Restriction of quasi-coherent modules along an étale morphism preserves finite colimits. -/
instance preservesFiniteColimits_etaleQuasicoherentRestriction :
    PreservesFiniteColimits (etaleQuasicoherentRestriction B S hS j hj) :=
  have : PreservesFiniteColimits
      (etaleQuasicoherentRestriction B S hS j hj ⋙ quasicoherentSheavesι B S hS U) :=
    inferInstanceAs (PreservesFiniteColimits
      (quasicoherentSheavesι B S hS W ⋙ etaleModulePullback.{u, u} B S hS j hj))
  preservesFiniteColimits_of_reflects_of_preserves _ (quasicoherentSheavesι B S hS U)

variable (hpush : PushforwardPreservesQuasicoherence B S hS j)

/-- The adjunction `(-)|_U ⊣ j_*` restricted to the quasi-coherent modules. -/
def etaleQuasicoherentRestrictionAdjunction :
    etaleQuasicoherentRestriction B S hS j hj ⊣ quasicoherentPushforward B S hS j hpush :=
  (etaleModulePullbackAdjunction B S hS j hj).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

include hj in
/-- **[Stacks, Tag 08BJ] for the direct image of quasi-coherent modules along an étale
morphism.**  Restriction of quasi-coherent modules is exact and left adjoint to `j_*`, so `j_*`
carries K-injective complexes of `QCoh(𝒪_U)` to K-injective complexes of `QCoh(𝒪_W)`. -/
theorem isKInjective_quasicoherentPushforward_obj
    (J : CochainComplex (QuasicoherentSheaves.{u, u} B S hS U.1 U.2) ℤ) [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((quasicoherentPushforward B S hS j hpush).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
    (etaleQuasicoherentRestrictionAdjunction B S hS j hj hpush) J

/-- **[Stacks, Tag 08BJ] for the restriction of modules along an étale morphism.**  Extension by
zero is exact and left adjoint to restriction, so restriction carries K-injective complexes of
`Mod(𝒪_W)` to K-injective complexes of `Mod(𝒪_U)`. -/
theorem isKInjective_etaleModulePullback_obj
    (J : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
    (etaleModuleLowerShriekAdjunction B S hS j hj) J

include hj in
/-- **[Stacks, Tag 08BJ] for the direct image of modules along an étale morphism.**  Restriction
of modules is exact and left adjoint to `j_*`, so `j_*` carries K-injective complexes of
`Mod(𝒪_U)` to K-injective complexes of `Mod(𝒪_W)`. -/
theorem isKInjective_modulePushforward_obj
    (J : CochainComplex (Modules.{u, u} B S hS U.1 U.2) ℤ) [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
    (etaleModulePullbackAdjunction B S hS j hj) J

end Restriction

/-! ### Complexes on which the direct image computes the derived direct image -/

section Computes

variable {W Z : AlgebraicSpaces B S hS} (g : W ⟶ Z)

/-- `g_*` computes `Rg_*` at a complex `M` of `𝒪_W`-modules: `g_*` carries every K-injective
resolution `M ⟶ L` to a quasi-isomorphism.  By
`AlgebraicGeometry.Space.pushforwardComputesDerived_iff_isIso` this says that the unit
`g_* M ⟶ Rg_* M` of any right derived functor of `g_*` is invertible at `M`. -/
def PushforwardComputesDerived (M : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) : Prop :=
  ∀ ⦃L : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ⦄ (t : M ⟶ L), QuasiIso t →
    L.IsKInjective →
      QuasiIso (((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).map t)

/-- `g_*` computes `Rg_*` at `M` exactly when the unit of a right derived functor of `g_*` is
invertible at `M`. -/
theorem pushforwardComputesDerived_iff_isIso
    (Rg : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (α : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    [Rg.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (M : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) :
    PushforwardComputesDerived B S hS g M ↔
      IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) := by
  constructor
  · intro h
    obtain ⟨L, t, hL, ht⟩ := exists_quasiIso_isKInjective_modules B S hS W.1 W.2 M
    exact (Stacks.RightDerivedUnitLocus.isIso_app_quotient_iff_quasiIso_map _ Rg α
      (exists_quasiIso_isKInjective_modules B S hS W.1 W.2) t hL).2 (h t ht hL)
  · intro h L t ht hL
    exact (Stacks.RightDerivedUnitLocus.isIso_app_quotient_iff_quasiIso_map _ Rg α
      (exists_quasiIso_isKInjective_modules B S hS W.1 W.2) t hL).1 h

/-- The total right derived functor `Rg_*` of the direct image of modules `g_*`. -/
abbrev derivedModulePushforwardTotal :
    DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) :=
  haveI := hasRightDerivedFunctor_modulePushforward B S hS g
  ((modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))

/-- The unit of `AlgebraicGeometry.Space.derivedModulePushforwardTotal`. -/
abbrev derivedModulePushforwardTotalUnit :
    (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedModulePushforwardTotal B S hS g :=
  haveI := hasRightDerivedFunctor_modulePushforward B S hS g
  ((modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))

/-- `AlgebraicGeometry.Space.derivedModulePushforwardTotal` is a right derived functor of `g_*`,
with unit `AlgebraicGeometry.Space.derivedModulePushforwardTotalUnit`. -/
instance : (derivedModulePushforwardTotal B S hS g).IsRightDerivedFunctor
    (derivedModulePushforwardTotalUnit B S hS g)
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) := by
  have := hasRightDerivedFunctor_modulePushforward B S hS g
  dsimp only [derivedModulePushforwardTotal, derivedModulePushforwardTotalUnit]
  infer_instance

/-- `g_*` computes `Rg_*` at `M` exactly when it carries one given K-injective resolution of `M`
to a quasi-isomorphism. -/
theorem pushforwardComputesDerived_iff_quasiIso
    {M L : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ} (t : M ⟶ L) [QuasiIso t]
    (hL : L.IsKInjective) :
    PushforwardComputesDerived B S hS g M ↔
      QuasiIso (((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).map t) :=
  (pushforwardComputesDerived_iff_isIso B S hS g _ (derivedModulePushforwardTotalUnit B S hS g)
    M).trans (Stacks.RightDerivedUnitLocus.isIso_app_quotient_iff_quasiIso_map _ _ _
      (exists_quasiIso_isKInjective_modules B S hS W.1 W.2) t hL)

/-- `g_*` computing `Rg_*` is invariant under isomorphism of complexes. -/
theorem PushforwardComputesDerived.of_iso
    {M M' : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ} (e : M ≅ M')
    (h : PushforwardComputesDerived B S hS g M) : PushforwardComputesDerived B S hS g M' := by
  rw [pushforwardComputesDerived_iff_isIso B S hS g _
    (derivedModulePushforwardTotalUnit B S hS g)] at h ⊢
  exact (NatTrans.isIso_app_iff_of_iso _
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso e)).1 h

end Computes

/-- **Composition.**  Let `j : U ⟶ W` be étale and `g : W ⟶ Z`.  If `j_*` computes `Rj_*` at a
complex `M` of `𝒪_U`-modules, then `(j ≫ g)_*` computes `R(j ≫ g)_*` at `M` exactly when `g_*`
computes `Rg_*` at `j_* M`: a K-injective resolution `M ⟶ L` is carried by `j_*` to a
K-injective resolution of `j_* M` ([Stacks, Tag 08BJ]), and `(j ≫ g)_* = g_* ∘ j_*`. -/
theorem pushforwardComputesDerived_comp_iff {U W Z : AlgebraicSpaces B S hS} (j : U ⟶ W)
    (hj : IsEtale B S hS j.hom) (g : W ⟶ Z) (M : CochainComplex (Modules.{u, u} B S hS U.1 U.2) ℤ)
    (hM : PushforwardComputesDerived B S hS j M) :
    PushforwardComputesDerived B S hS (j ≫ g) M ↔
      PushforwardComputesDerived B S hS g
        (((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) := by
  obtain ⟨L, t, hL, ht⟩ := exists_quasiIso_isKInjective_modules B S hS U.1 U.2 M
  have hjt := hM t ht hL
  have hjL : CochainComplex.IsKInjective
      (((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
    have := hL
    exact isKInjective_modulePushforward_obj B S hS j hj L
  have := ht
  have := hjt
  rw [pushforwardComputesDerived_iff_quasiIso B S hS (j ≫ g) t hL,
    pushforwardComputesDerived_iff_quasiIso B S hS g
      (((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).map t) hjL]
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoOfNatIso
    (Functor.mapHomologicalComplexCompIso (modulePushforwardCompIso B S hS j g)
      (ComplexShape.up ℤ)) (Arrow.mk t))).symm

/-! ### The property carried through the induction -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The property of an algebraic space `U` that is carried through the induction of
[Stacks, Tag 0CSR]: for every morphism `g : U ⟶ Z` to a quasi-compact algebraic space with affine
diagonal over `ℤ` and every K-injective complex `I` of quasi-coherent `𝒪_U`-modules, `g_*`
computes `Rg_*` at `I`.  This is the source's `P(U)`, read on K-injective representatives. -/
def PushforwardComputesDerivedOnQuasicoherentKInjectives (U : AlgebraicSpaces B S hS) : Prop :=
  ∀ (Z : AlgebraicSpaces B S hS), IsQuasiCompactWithAffineDiagonal B S hS hZ Z.1 →
    ∀ (g : U ⟶ Z) (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS U.1 U.2) ℤ),
      I.IsKInjective →
        PushforwardComputesDerived B S hS g
          (((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-- **Condition (3)(b) of the induction: the affine case.**  A morphism from an affine algebraic
space to an algebraic space with affine diagonal is affine ([Stacks, Tag 08GB]), and along an
affine morphism every complex of quasi-coherent modules computes its derived direct image
([Stacks, Tag 08GY]). -/
theorem pushforwardComputesDerivedOnQuasicoherentKInjectives_of_isAffineSpace
    (U : AlgebraicSpaces B S hS) (hU : IsAffineSpace B S hS U.1) :
    PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ U := by
  intro Z hZqc g I _
  obtain ⟨T, hT, ⟨e⟩⟩ := hU
  have h₁ : IsAffineHom B S hS (e.inv ≫ g.hom) :=
    isAffineHom_of_affine_source_of_isAffineHom_diag B S hS hZ ⟨T, hT⟩ (e.inv ≫ g.hom) hZqc.2
  have hg : IsAffineHom B S hS g.hom := by
    simpa using isAffineHom_comp B S hS e.hom (e.inv ≫ g.hom) (isAffineHom_of_isIso e.hom) h₁
  rw [pushforwardComputesDerived_iff_isIso B S hS g _ (derivedModulePushforwardTotalUnit B S hS g)]
  exact isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite B S hS g hg _ _ _
    (fun n => (I.X n).property)

/-! ### The unit `I ⟶ j_* J` against the unit of `(-)|_U ⊣ j_*` -/

section UnitComparison

open CategoryTheory.PushforwardMayerVietoris

variable {U W : AlgebraicSpaces B S hS} (j : U ⟶ W) (hj : IsEtale B S hS j.hom)
  (hpush : PushforwardPreservesQuasicoherence B S hS j)

/-- `ι_U(I|_U) ≅ (ι_W I)|_U`: restricting a complex of quasi-coherent modules and then forgetting
quasi-coherence is restricting the underlying complex of modules. -/
def etaleQuasicoherentRestrictionιIso
    (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ) :
    ((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((etaleQuasicoherentRestriction B S hS j hj).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (Functor.mapHomologicalComplexCompIso (ObjectProperty.liftCompιIso _ _ _)
      (ComplexShape.up ℤ)).app I ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (quasicoherentSheavesι B S hS W ⋙ etaleModulePullback.{u, u} B S hS j hj))
      (ComplexShape.up ℤ)).symm.app I

/-- `ι_W(j_* J) ≅ j_*(ι_U J)`: the direct image of quasi-coherent modules is the direct image of
the underlying modules. -/
def quasicoherentPushforwardιIso
    (J : CochainComplex (QuasicoherentSheaves.{u, u} B S hS U.1 U.2) ℤ) :
    ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((quasicoherentPushforward B S hS j hpush).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J) ≅
      ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
  (Functor.mapHomologicalComplexCompIso
      (quasicoherentPushforwardCompιIso B S hS j hpush) (ComplexShape.up ℤ)).app J ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (quasicoherentSheavesι B S hS U ⋙ modulePushforward B S hS j))
      (ComplexShape.up ℤ)).symm.app J

/-- The comparison `j_*(j^* M) ≅ (j^* ⋙ j_*)(M)` of the two ways of applying `j_* ∘ j^*` to a
complex. -/
abbrev restrictPushCompIso :=
  Functor.mapHomologicalComplexCompIso
    (Iso.refl (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j))
    (ComplexShape.up ℤ)

/-- The map `a : I ⟶ j_* J` of complexes of quasi-coherent `𝒪_W`-modules attached to a map
`s : I|_U ⟶ J`: the unit `I ⟶ j_*(I|_U)` followed by `j_* s`. -/
def quasicoherentUnitMap (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ)
    (J : CochainComplex (QuasicoherentSheaves.{u, u} B S hS U.1 U.2) ℤ)
    (s : ((etaleQuasicoherentRestriction B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    I ⟶ ((quasicoherentPushforward B S hS j hpush).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J :=
  ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).preimage
    (unitCochainMap (etaleModulePullbackAdjunction B S hS j hj).unit
        (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
      (restrictPushCompIso B S hS j hj).inv.app _ ≫
      ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((etaleQuasicoherentRestrictionιIso B S hS j hj I).inv ≫
          ((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).map s) ≫
      (quasicoherentPushforwardιIso B S hS j hpush J).inv)

/-- The underlying map of complexes of modules of
`AlgebraicGeometry.Space.quasicoherentUnitMap`. -/
theorem map_quasicoherentUnitMap
    (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ)
    (J : CochainComplex (QuasicoherentSheaves.{u, u} B S hS U.1 U.2) ℤ)
    (s : ((etaleQuasicoherentRestriction B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (quasicoherentUnitMap B S hS j hj hpush I J s) =
      unitCochainMap (etaleModulePullbackAdjunction B S hS j hj).unit
          (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (restrictPushCompIso B S hS j hj).inv.app _ ≫
        ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((etaleQuasicoherentRestrictionιIso B S hS j hj I).inv ≫
            ((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).map s) ≫
        (quasicoherentPushforwardιIso B S hS j hpush J).inv :=
  Functor.map_preimage _ _

/-- The unit of `(-)|_U ⊣ j_*` on complexes is natural. -/
theorem unitCochainMap_comp_restrictPush {M N : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ}
    (t : M ⟶ N) :
    unitCochainMap (etaleModulePullbackAdjunction B S hS j hj).unit M ≫
        (restrictPushCompIso B S hS j hj).inv.app M ≫
          ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
              (ComplexShape.up ℤ)).map t) ≫
          (restrictPushCompIso B S hS j hj).hom.app N =
      t ≫ unitCochainMap (etaleModulePullbackAdjunction B S hS j hj).unit N := by
  rw [show ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
        (ComplexShape.up ℤ)).map t) ≫ (restrictPushCompIso B S hS j hj).hom.app N =
      (restrictPushCompIso B S hS j hj).hom.app M ≫
        ((etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j).mapHomologicalComplex
          (ComplexShape.up ℤ)).map t from (restrictPushCompIso B S hS j hj).hom.naturality t,
    Iso.inv_hom_id_app_assoc]
  have hn := (unitCochainNatTrans (etaleModulePullbackAdjunction B S hS j hj).unit).naturality t
  simp only [Functor.id_map, unitCochainNatTrans_app] at hn
  rw [hn]

/-- **Lifting the restricted resolution.**  For `s : I|_U ⟶ J` a quasi-isomorphism to a
K-injective complex of `QCoh(𝒪_U)` and `t : ι_W I ⟶ E'` a quasi-isomorphism to a K-injective
complex of `Mod(𝒪_W)`, there is a quasi-isomorphism `u : ι_U J ⟶ E'|_U` with `ι_U s ≫ u`
homotopic to `t|_U`: the restriction `E'|_U` is K-injective
(`AlgebraicGeometry.Space.isKInjective_etaleModulePullback_obj`), so maps into it from `ι_U J`
are the maps of `D(𝒪_U)`. -/
theorem exists_lift_restrictedResolution
    (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ)
    (J : CochainComplex (QuasicoherentSheaves.{u, u} B S hS U.1 U.2) ℤ)
    (s : ((etaleQuasicoherentRestriction B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) [QuasiIso s]
    {E' : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ}
    (t : ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ E')
    [QuasiIso t] [E'.IsKInjective] :
    ∃ v : ((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj J ⟶
        ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex (ComplexShape.up ℤ)).obj E',
      QuasiIso v ∧
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            (((etaleQuasicoherentRestrictionιIso B S hS j hj I).inv ≫
              ((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).map s) ≫
              v) =
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
              (ComplexShape.up ℤ)).map t) := by
  let c := ComplexShape.up ℤ
  let pb := etaleModulePullback.{u, u} B S hS j hj
  have : CochainComplex.IsKInjective ((pb.mapHomologicalComplex c).obj E') :=
    isKInjective_etaleModulePullback_obj B S hS j hj E'
  let s' := (etaleQuasicoherentRestrictionιIso B S hS j hj I).inv ≫
    ((quasicoherentSheavesι B S hS U).mapHomologicalComplex c).map s
  let r := (pb.mapHomologicalComplex c).map t
  have hQ : ∀ {M N : CochainComplex (Modules.{u, u} B S hS U.1 U.2) ℤ} (f : M ⟶ N),
      IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ c).map f)) ↔ QuasiIso f := by
    intro M N f
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
  have hQs := (hQ s').2 (by dsimp only [s']; infer_instance)
  have hQr := (hQ r).2 (HomologicalComplex.quasiIso_map_of_preservesHomology _ _)
  obtain ⟨u0, hu0⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ c).obj
      (((quasicoherentSheavesι B S hS U).mapHomologicalComplex c).obj J))
    ((pb.mapHomologicalComplex c).obj E')).surjective
    (inv (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ c).map s')) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ c).map r))
  obtain ⟨v, rfl⟩ := (HomotopyCategory.quotient _ c).map_surjective u0
  refine ⟨v, ?_, ?_⟩
  · rw [← hQ, hu0]
    infer_instance
  · apply (CochainComplex.IsKInjective.Qh_map_bijective _ _).injective
    rw [Functor.map_comp, Functor.map_comp, hu0, IsIso.hom_inv_id_assoc]

/-- The commutativity `a ≫ ψ = t ≫ η_{E'}` in `D(𝒪_W)`, for `a` the quasi-coherent unit map of
`s` and `ψ = j_* v`, given the homotopy `ι_U s ≫ v ≃ t|_U`. -/
theorem Q_map_quasicoherentUnitMap_comp
    (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ)
    (J : CochainComplex (QuasicoherentSheaves.{u, u} B S hS U.1 U.2) ℤ)
    (s : ((etaleQuasicoherentRestriction B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    {E' : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ}
    (t : ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ E')
    (v : ((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj J ⟶
        ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex (ComplexShape.up ℤ)).obj E')
    (hv : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            (((etaleQuasicoherentRestrictionιIso B S hS j hj I).inv ≫
              ((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).map s) ≫
              v) =
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
              (ComplexShape.up ℤ)).map t)) :
    DerivedCategory.Q.map
        (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (quasicoherentUnitMap B S hS j hj hpush I J s)) ≫
      DerivedCategory.Q.map ((quasicoherentPushforwardιIso B S hS j hpush J).hom ≫
        ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).map v ≫
          (restrictPushCompIso B S hS j hj).hom.app E') =
      DerivedCategory.Q.map t ≫
        DerivedCategory.Q.map
          (unitCochainMap (etaleModulePullbackAdjunction B S hS j hj).unit E') := by
  have hh := HomotopyCategory.homotopyOfEq _ _ hv
  have h₁ : ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (quasicoherentUnitMap B S hS j hj hpush I J s) ≫
      (quasicoherentPushforwardιIso B S hS j hpush J).hom ≫
        ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).map v ≫
          (restrictPushCompIso B S hS j hj).hom.app E' =
      unitCochainMap (etaleModulePullbackAdjunction B S hS j hj).unit
          (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (restrictPushCompIso B S hS j hj).inv.app _ ≫
        ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((etaleQuasicoherentRestrictionιIso B S hS j hj I).inv ≫
            ((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).map s) ≫
              v) ≫
        (restrictPushCompIso B S hS j hj).hom.app E' := by
    rw [map_quasicoherentUnitMap]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  have hhom := (Homotopy.ofEq h₁).trans
    (((((modulePushforward B S hS j).mapHomotopy hh).compRight
      ((restrictPushCompIso B S hS j hj).hom.app E')).compLeft
        ((restrictPushCompIso B S hS j hj).inv.app _)).compLeft
          (unitCochainMap (etaleModulePullbackAdjunction B S hS j hj).unit _) |>.trans
      (Homotopy.ofEq (unitCochainMap_comp_restrictPush B S hS j hj t)))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy _ hhom

/-- **The comparison of the quasi-coherent unit with the unit of all modules.**  Let `j : U ⟶ W`
be étale, with `j_*` preserving quasi-coherence and computing `Rj_*` at every K-injective complex
of `QCoh(𝒪_U)`.  Let `I` be a complex of quasi-coherent `𝒪_W`-modules and `t : I ⟶ E'` a
K-injective resolution in `Mod(𝒪_W)`.  Then there are a K-injective complex `J` of `QCoh(𝒪_U)`,
a map `a : I ⟶ j_* J` of complexes of quasi-coherent modules and a quasi-isomorphism
`ψ : j_* J ⟶ j_*(E'|_U)` of complexes of modules such that, in `D(𝒪_W)`, `a ≫ ψ = t ≫ η_{E'}`,
where `η` is the unit of `(-)|_U ⊣ j_*`.

This is how the triangle of K-injective complexes of `QCoh(𝒪_W)` built from `a` is compared with
the Mayer–Vietoris triangle of [Stacks, Tag 08GW] in `D(𝒪_W)`. -/
theorem exists_quasicoherentUnit_comp_eq
    (hJ : ∀ J : CochainComplex (QuasicoherentSheaves.{u, u} B S hS U.1 U.2) ℤ, J.IsKInjective →
      PushforwardComputesDerived B S hS j
        (((quasicoherentSheavesι B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
    (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ)
    {E' : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ}
    (t : ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ E')
    [QuasiIso t] [E'.IsKInjective] :
    ∃ (J : CochainComplex (QuasicoherentSheaves.{u, u} B S hS U.1 U.2) ℤ) (_ : J.IsKInjective)
      (a : I ⟶ ((quasicoherentPushforward B S hS j hpush).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)
      (ψ : ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((quasicoherentPushforward B S hS j hpush).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J) ⟶
        ((etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E'),
      QuasiIso ψ ∧
        DerivedCategory.Q.map
            (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).map a) ≫
          DerivedCategory.Q.map ψ =
        DerivedCategory.Q.map t ≫
          DerivedCategory.Q.map
            (unitCochainMap (etaleModulePullbackAdjunction B S hS j hj).unit E') := by
  obtain ⟨J, s, hJinj, hs⟩ := exists_quasiIso_isKInjective_quasicoherentSheaves B S hS U
    (((etaleQuasicoherentRestriction B S hS j hj).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have := hs
  obtain ⟨v, hv, hsv⟩ := exists_lift_restrictedResolution B S hS j hj I J s t
  have hpv : QuasiIso (((modulePushforward B S hS j).mapHomologicalComplex
      (ComplexShape.up ℤ)).map v) :=
    hJ J hJinj v hv (isKInjective_etaleModulePullback_obj B S hS j hj E')
  exact ⟨J, hJinj, quasicoherentUnitMap B S hS j hj hpush I J s, _, inferInstance,
    Q_map_quasicoherentUnitMap_comp B S hS j hj hpush I J s t v hsv⟩

end UnitComparison

/-! ### The locus of `K(QCoh(𝒪_W))` where `g_*` computes `Rg_*` -/

section GoodLocus

variable {W Z : AlgebraicSpaces B S hS} (g : W ⟶ Z)

/-- An object `X` of `K(QCoh(𝒪_W))` at whose underlying complex of modules `g_*` computes
`Rg_*`. -/
def PushforwardComputesDerivedAt
    (X : HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) :
    Prop :=
  IsIso ((derivedModulePushforwardTotalUnit B S hS g).app
    (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)).obj X))

/-- `g_*` computes `Rg_*` at the class of a complex `M` of `K(QCoh(𝒪_W))` exactly when it computes
`Rg_*` at the underlying complex of modules of `M`. -/
theorem pushforwardComputesDerivedAt_quotient_iff
    (M : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ) :
    PushforwardComputesDerivedAt B S hS g ((HomotopyCategory.quotient _ _).obj M) ↔
      PushforwardComputesDerived B S hS g
        (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) := by
  rw [pushforwardComputesDerived_iff_isIso B S hS g _ (derivedModulePushforwardTotalUnit B S hS g)]
  exact NatTrans.isIso_app_iff_of_iso _
    (((quasicoherentSheavesι B S hS W).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app M)

/-- The locus where `g_*` computes `Rg_*` is closed under isomorphism. -/
theorem PushforwardComputesDerivedAt.of_iso
    {X Y : HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)}
    (e : X ≅ Y) (h : PushforwardComputesDerivedAt B S hS g X) :
    PushforwardComputesDerivedAt B S hS g Y :=
  (NatTrans.isIso_app_iff_of_iso _
    (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)).mapIso e)).1 h

/-- Two out of three, first vertex. -/
theorem pushforwardComputesDerivedAt_obj₁
    (T : Triangle (HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2)
      (ComplexShape.up ℤ))) (hT : T ∈ distTriang _)
    (h₂ : PushforwardComputesDerivedAt B S hS g T.obj₂)
    (h₃ : PushforwardComputesDerivedAt B S hS g T.obj₃) :
    PushforwardComputesDerivedAt B S hS g T.obj₁ :=
  Stacks.RightDerivedUnitLocus.isIso_app_obj₁_of_distinguished _ _ _
    (exists_quasiIso_isKInjective_modules B S hS W.1 W.2)
    (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)).mapTriangle.obj T)
    (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)).map_distinguished
      T hT) h₂ h₃

/-- Two out of three, middle vertex. -/
theorem pushforwardComputesDerivedAt_obj₂
    (T : Triangle (HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2)
      (ComplexShape.up ℤ))) (hT : T ∈ distTriang _)
    (h₁ : PushforwardComputesDerivedAt B S hS g T.obj₁)
    (h₃ : PushforwardComputesDerivedAt B S hS g T.obj₃) :
    PushforwardComputesDerivedAt B S hS g T.obj₂ :=
  Stacks.RightDerivedUnitLocus.isIso_app_obj₂_of_distinguished _ _ _
    (exists_quasiIso_isKInjective_modules B S hS W.1 W.2)
    (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)).mapTriangle.obj T)
    (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)).map_distinguished
      T hT) h₁ h₃

/-- The locus is closed under binary biproducts. -/
theorem pushforwardComputesDerivedAt_biprod
    (X Y : HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
    (hX : PushforwardComputesDerivedAt B S hS g X) (hY : PushforwardComputesDerivedAt B S hS g Y) :
    PushforwardComputesDerivedAt B S hS g (X ⊞ Y) :=
  pushforwardComputesDerivedAt_obj₂ B S hS g (binaryBiproductTriangle X Y)
    (binaryBiproductTriangle_distinguished X Y) hX hY

end GoodLocus

/-- **K-injective complexes are determined by their image in the derived category.**  Two
K-injective complexes whose images in `D(𝒜)` are isomorphic are isomorphic in `K(𝒜)`. -/
theorem nonempty_iso_quotient_of_isKInjective {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
    [HasDerivedCategory 𝒜] (L N : CochainComplex 𝒜 ℤ) [L.IsKInjective] [N.IsKInjective]
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj L) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj N)) :
    Nonempty ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj L ≅
      (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj N) := by
  obtain ⟨f, hf⟩ := (CochainComplex.IsKInjective.Qh_map_bijective _ N).surjective e.hom
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective _ L).surjective e.inv
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · apply (CochainComplex.IsKInjective.Qh_map_bijective _ L).injective
    rw [Functor.map_comp, hf, hg, e.hom_inv_id, CategoryTheory.Functor.map_id]
  · apply (CochainComplex.IsKInjective.Qh_map_bijective _ N).injective
    rw [Functor.map_comp, hf, hg, e.inv_hom_id, CategoryTheory.Functor.map_id]

/-! ### Members of the collection of the induction -/

/-- A quasi-compact algebraic space with affine diagonal over `ℤ` is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_isQuasiCompactWithAffineDiagonal
    (Y : AlgebraicSpaces B S hS) (hY : IsQuasiCompactWithAffineDiagonal B S hS hZ Y.1) :
    IsAbsolutelyQuasiSeparated B S hS hZ Y.1 :=
  IsQuasiCompactWithAffineDiagonal.isAbsolutelyQuasiSeparated B S hS hZ Y
    ⟨Over.mk (𝟙 Y), by intro T φ hφ; simpa using hφ⟩ hY

/-- **[Stacks, Tag 03M9] between quasi-compact spaces with affine diagonal.**  A morphism between
quasi-compact algebraic spaces with affine diagonal over `ℤ` is quasi-compact and quasi-separated
([Stacks, Tag 073B]), so its direct image preserves quasi-coherence. -/
theorem pushforwardPreservesQuasicoherence_of_isQuasiCompactWithAffineDiagonal
    {Y W : AlgebraicSpaces B S hS} (j : Y ⟶ W)
    (hY : IsQuasiCompactWithAffineDiagonal B S hS hZ Y.1)
    (hW : IsQuasiCompactWithAffineDiagonal B S hS hZ W.1) :
    PushforwardPreservesQuasicoherence B S hS j := fun F hF =>
  isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS j
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2
      (isAbsolutelyQuasiSeparated_of_isQuasiCompactWithAffineDiagonal B S hS hZ W hW) hY.1 j.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y.2
      (isAbsolutelyQuasiSeparated_of_isQuasiCompactWithAffineDiagonal B S hS hZ Y hY) j.hom) F hF

/-- **The last paragraph of the proof of [Stacks, Tag 0CSR].**  Let `j : Y ⟶ W` be étale between
quasi-compact algebraic spaces with affine diagonal, with `P(Y)`, and let `g : W ⟶ Z` with `Z`
quasi-compact with affine diagonal.  For a K-injective complex `J` of `QCoh(𝒪_Y)`, `g_*` computes
`Rg_*` at `j_* J`: by `P(Y)` applied to `j` and to `j ≫ g`, and
`AlgebraicGeometry.Space.pushforwardComputesDerived_comp_iff`. -/
theorem pushforwardComputesDerivedAt_quasicoherentPushforward {Y W Z : AlgebraicSpaces B S hS}
    (j : Y ⟶ W) (hj : IsEtale B S hS j.hom) (hpush : PushforwardPreservesQuasicoherence B S hS j)
    (g : W ⟶ Z) (hQ : PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ Y)
    (hW : IsQuasiCompactWithAffineDiagonal B S hS hZ W.1)
    (hZqc : IsQuasiCompactWithAffineDiagonal B S hS hZ Z.1)
    (J : CochainComplex (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) ℤ) (hJ : J.IsKInjective) :
    PushforwardComputesDerivedAt B S hS g ((HomotopyCategory.quotient _ _).obj
      (((quasicoherentPushforward B S hS j hpush).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)) := by
  rw [pushforwardComputesDerivedAt_quotient_iff]
  exact PushforwardComputesDerived.of_iso B S hS g
    (quasicoherentPushforwardιIso B S hS j hpush J).symm
    ((pushforwardComputesDerived_comp_iff B S hS j hj g _ (hQ W hW j J hJ)).1
      (hQ Z hZqc (j ≫ g) J hJ))

/-! ### From complexes of quasi-coherent modules to `D(𝒪_W)` -/

section ToDerived

variable {W : AlgebraicSpaces B S hS}

/-- The class in `D(𝒪_W)` of the underlying complex of modules of a complex of quasi-coherent
modules, read through `K(QCoh(𝒪_W)) ⥤ K(𝒪_W) ⥤ D(𝒪_W)` or through `C(𝒪_W) ⥤ D(𝒪_W)`. -/
def quasicoherentToDerivedIso (M : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ) :
    (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh).obj ((HomotopyCategory.quotient _ _).obj M) ≅
      DerivedCategory.Q.obj
        (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  DerivedCategory.Qh.mapIso
      (((quasicoherentSheavesι B S hS W).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app M) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- `AlgebraicGeometry.Space.quasicoherentToDerivedIso` is natural in the complex. -/
theorem quasicoherentToDerivedIso_naturality
    {M N : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ} (f : M ⟶ N) :
    (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh).map ((HomotopyCategory.quotient _ _).map f) ≫
      (quasicoherentToDerivedIso B S hS N).hom =
    (quasicoherentToDerivedIso B S hS M).hom ≫
      DerivedCategory.Q.map
        (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have h := ((quasicoherentSheavesι B S hS W).mapHomotopyCategoryFactors
    (ComplexShape.up ℤ)).hom.naturality f
  simp only [quasicoherentToDerivedIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.comp_map]
  rw [Functor.comp_map, Functor.comp_map] at h
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc,
    DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc]

end ToDerived

/-- In an additive functor's image, the pair of two maps out of an object agrees with the pair of
their images, through `F(X ⊞ Y) ≅ F X ⊞ F Y`. -/
theorem map_biprodLift_comp_mapBiprod {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] [Preadditive 𝒞]
    [Preadditive 𝒟] [HasBinaryBiproducts 𝒞] [HasBinaryBiproducts 𝒟] (F : 𝒞 ⥤ 𝒟) [F.Additive]
    [PreservesBinaryBiproducts F] {A X Y : 𝒞} {A' X' Y' : 𝒟} (a : A ⟶ X) (b : A ⟶ Y)
    (e : F.obj A ≅ A') (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y') (c : A' ⟶ X') (d : A' ⟶ Y')
    (ha : F.map a ≫ eX.hom = e.hom ≫ c) (hb : F.map b ≫ eY.hom = e.hom ≫ d) :
    F.map (biprod.lift a b) ≫ (F.mapBiprod X Y ≪≫ biprod.mapIso eX eY).hom =
      e.hom ≫ biprod.lift c d := by
  apply biprod.hom_ext
  · simp only [Iso.trans_hom, biprod.mapIso_hom, Functor.mapBiprod_hom, Category.assoc,
      biprod.map_fst, biprod.lift_fst_assoc, ← F.map_comp_assoc, biprod.lift_fst, ha]
  · simp only [Iso.trans_hom, biprod.mapIso_hom, Functor.mapBiprod_hom, Category.assoc,
      biprod.map_snd, biprod.lift_snd_assoc, ← F.map_comp_assoc, biprod.lift_snd, hb]

/-- Two distinguished triangles with isomorphic first arrows have isomorphic third vertices. -/
theorem nonempty_iso_obj₃_of_iso₁₂ {𝒟 : Type*} [Category* 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟]
    [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
    (T₁ T₂ : Triangle 𝒟) (h₁ : T₁ ∈ distTriang 𝒟) (h₂ : T₂ ∈ distTriang 𝒟)
    (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₂ : T₁.obj₂ ≅ T₂.obj₂)
    (comm : T₁.mor₁ ≫ e₂.hom = e₁.hom ≫ T₂.mor₁) : Nonempty (T₁.obj₃ ≅ T₂.obj₃) :=
  ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T₁ T₂ h₁ h₂ e₁ e₂ comm)⟩

/-- **Reflecting an isomorphism of K-injective objects.**  If the derived inclusion
`D(QCoh(𝒪_W)) ⥤ D(𝒪_W)` is fully faithful, an object `C` of `K(QCoh(𝒪_W))` right orthogonal to the
acyclic complexes and a K-injective complex `M` whose images in `D(𝒪_W)` are isomorphic are
isomorphic in `K(QCoh(𝒪_W))`. -/
theorem nonempty_iso_quotient_of_iso_derived {W : AlgebraicSpaces B S hS}
    [((quasicoherentSheavesι B S hS W).mapDerivedCategory).Full]
    [((quasicoherentSheavesι B S hS W).mapDerivedCategory).Faithful]
    {C : HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)}
    (hC : (HomotopyCategory.subcategoryAcyclic _).rightOrthogonal C)
    (M : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ) [M.IsKInjective]
    (e : (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh).obj C ≅
      (((quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh).obj ((HomotopyCategory.quotient _ _).obj M)) :
    Nonempty (C ≅ (HomotopyCategory.quotient _ _).obj M) := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective C
  have : CochainComplex.IsKInjective L := (CochainComplex.isKInjective_iff_rightOrthogonal L).2 hC
  let eD := (quasicoherentSheavesι B S hS W).mapDerivedCategoryFactorsh.app _ ≪≫ e ≪≫
    ((quasicoherentSheavesι B S hS W).mapDerivedCategoryFactorsh.app _).symm
  exact nonempty_iso_quotient_of_isKInjective L M
    (((quasicoherentSheavesι B S hS W).mapDerivedCategory).preimageIso eD)

/-! ### The Mayer–Vietoris step -/

section MayerVietorisStep

open CategoryTheory.PushforwardMayerVietoris

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  (hpU : PushforwardPreservesQuasicoherence B S hS (edsOpenHom B S hS hsq))
  (hpV : PushforwardPreservesQuasicoherence B S hS (edsEtaleHom B S hS hsq))
  (hpP : PushforwardPreservesQuasicoherence B S hS (edsInterHom B S hS hsq))

/-- **The third vertex.**  Let `(U ⊆ W, V ⟶ W)` be an elementary distinguished square and `I` a
K-injective complex of `QCoh(𝒪_W)`, with K-injective resolution `t : I ⟶ E'` in `Mod(𝒪_W)`.  Let
`a_U : I ⟶ j_{U,*}J_U` and `a_V : I ⟶ j_{V,*}J_V` be maps to direct images of K-injective
complexes compatible, through quasi-isomorphisms `ψ_U`, `ψ_V`, with the units of the square, and
let `J_P` be K-injective with `j_{P,*}J_P` quasi-isomorphic to `j_{P,*}(E'|_P)`.  If the derived
inclusion `D(QCoh(𝒪_W)) ⥤ D(𝒪_W)` is fully faithful, the third vertex of a distinguished triangle
on `(a_U, a_V)` in `K(QCoh(𝒪_W))` is isomorphic to `j_{P,*}J_P`.

Both the triangle on `(a_U, a_V)` and the Mayer–Vietoris triangle of [Stacks, Tag 08GW] on `E'`
land in `D(𝒪_W)` with isomorphic first arrows, so their third vertices are isomorphic; full
faithfulness brings the isomorphism back to `D(QCoh(𝒪_W))`, and between K-injective complexes to
`K(QCoh(𝒪_W))`. -/
theorem nonempty_iso_obj₃_of_square
    [((quasicoherentSheavesι B S hS W).mapDerivedCategory).Full]
    [((quasicoherentSheavesι B S hS W).mapDerivedCategory).Faithful]
    (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ℤ) [I.IsKInjective]
    {E' : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ}
    (t : ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ E')
    [QuasiIso t]
    (JU : CochainComplex (QuasicoherentSheaves.{u, u} B S hS
      (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) ℤ) [JU.IsKInjective]
    (aU : I ⟶ ((quasicoherentPushforward B S hS _ hpU).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj JU)
    (ψU : ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((quasicoherentPushforward B S hS _ hpU).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj JU) ⟶
      ((edsRestrictPushOpen B S hS hsq).mapHomologicalComplex (ComplexShape.up ℤ)).obj E')
    [QuasiIso ψU]
    (hU : DerivedCategory.Q.map
          (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).map aU) ≫
        DerivedCategory.Q.map ψU =
      DerivedCategory.Q.map t ≫
        DerivedCategory.Q.map (unitCochainMap (edsAdjOpen B S hS hsq).unit E'))
    (JV : CochainComplex (QuasicoherentSheaves.{u, u} B S hS
      (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) ℤ) [JV.IsKInjective]
    (aV : I ⟶ ((quasicoherentPushforward B S hS _ hpV).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj JV)
    (ψV : ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((quasicoherentPushforward B S hS _ hpV).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj JV) ⟶
      ((edsRestrictPushEtale B S hS hsq).mapHomologicalComplex (ComplexShape.up ℤ)).obj E')
    [QuasiIso ψV]
    (hV : DerivedCategory.Q.map
          (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).map aV) ≫
        DerivedCategory.Q.map ψV =
      DerivedCategory.Q.map t ≫
        DerivedCategory.Q.map (unitCochainMap (edsAdjEtale B S hS hsq).unit E'))
    (JP : CochainComplex (QuasicoherentSheaves.{u, u} B S hS
      (edsInter B S hS hsq).1 (edsInter B S hS hsq).2) ℤ) [JP.IsKInjective]
    (ψP : ((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((quasicoherentPushforward B S hS _ hpP).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj JP) ⟶
      ((edsRestrictPushInter B S hS hsq).mapHomologicalComplex (ComplexShape.up ℤ)).obj E')
    [QuasiIso ψP]
    {C : HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)}
    (β : (HomotopyCategory.quotient _ _).obj
        (((quasicoherentPushforward B S hS _ hpU).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj JU) ⊞
      (HomotopyCategory.quotient _ _).obj
        (((quasicoherentPushforward B S hS _ hpV).mapHomologicalComplex (ComplexShape.up ℤ)).obj JV)
        ⟶ C)
    (γ : C ⟶ ((HomotopyCategory.quotient _ _).obj I)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift ((HomotopyCategory.quotient _ _).map aU)
      ((HomotopyCategory.quotient _ _).map aV)) β γ ∈ distTriang _) :
    Nonempty (C ≅ (HomotopyCategory.quotient _ _).obj
      (((quasicoherentPushforward B S hS _ hpP).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj JP)) := by
  obtain ⟨δ, hδ⟩ := mem_distTriang_unitBiprod_of_natural_shortExact _ _ _ _
    (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq) E'
  let H := (quasicoherentSheavesι B S hS W).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  have hT₁ := H.map_distinguished _ hT
  let eU := quasicoherentToDerivedIso B S hS
      (((quasicoherentPushforward B S hS _ hpU).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj JU) ≪≫
    asIso (DerivedCategory.Q.map ψU)
  let eV := quasicoherentToDerivedIso B S hS
      (((quasicoherentPushforward B S hS _ hpV).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj JV) ≪≫
    asIso (DerivedCategory.Q.map ψV)
  let eI := quasicoherentToDerivedIso B S hS I ≪≫ asIso (DerivedCategory.Q.map t)
  have hcU : H.map ((HomotopyCategory.quotient _ _).map aU) ≫ eU.hom =
      eI.hom ≫ DerivedCategory.Q.map (unitCochainMap (edsAdjOpen B S hS hsq).unit E') := by
    simp only [eU, eI, H, Iso.trans_hom, asIso_hom, Category.assoc, Functor.comp_map]
    rw [reassoc_of% quasicoherentToDerivedIso_naturality B S hS aU, hU]
  have hcV : H.map ((HomotopyCategory.quotient _ _).map aV) ≫ eV.hom =
      eI.hom ≫ DerivedCategory.Q.map (unitCochainMap (edsAdjEtale B S hS hsq).unit E') := by
    simp only [eV, eI, H, Iso.trans_hom, asIso_hom, Category.assoc, Functor.comp_map]
    rw [reassoc_of% quasicoherentToDerivedIso_naturality B S hS aV, hV]
  obtain ⟨e₃⟩ := nonempty_iso_obj₃_of_iso₁₂ _ _ hT₁ hδ eI (H.mapBiprod _ _ ≪≫ biprod.mapIso eU eV)
    (map_biprodLift_comp_mapBiprod H _ _ eI eU eV _ _ hcU hcV)
  have := isKInjective_quasicoherentPushforward_obj B S hS _ (isEtale_edsOpenHom B S hS hsq) hpU JU
  have :=
    isKInjective_quasicoherentPushforward_obj B S hS _ (isEtale_edsEtaleHom B S hS hsq) hpV JV
  have :=
    isKInjective_quasicoherentPushforward_obj B S hS _ (isEtale_edsInterHom B S hS hsq) hpP JP
  have h₂ : (HomotopyCategory.subcategoryAcyclic _).rightOrthogonal
      ((HomotopyCategory.quotient _ _).obj
        (((quasicoherentPushforward B S hS _ hpU).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj JU) ⊞
      (HomotopyCategory.quotient _ _).obj
        (((quasicoherentPushforward B S hS _ hpV).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj JV)) :=
    ObjectProperty.ext_of_isTriangulatedClosed₂ _ _
      (binaryBiproductTriangle_distinguished
        ((HomotopyCategory.quotient _ _).obj
          (((quasicoherentPushforward B S hS _ hpU).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj JU))
        ((HomotopyCategory.quotient _ _).obj
          (((quasicoherentPushforward B S hS _ hpV).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj JV)))
      (CochainComplex.IsKInjective.rightOrthogonal
        (((quasicoherentPushforward B S hS _ hpU).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj JU))
      (CochainComplex.IsKInjective.rightOrthogonal
        (((quasicoherentPushforward B S hS _ hpV).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj JV))
  have hC : (HomotopyCategory.subcategoryAcyclic _).rightOrthogonal C :=
    ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hT
      (CochainComplex.IsKInjective.rightOrthogonal I) h₂
  exact nonempty_iso_quotient_of_iso_derived B S hS hC _
    (e₃ ≪≫ (quasicoherentToDerivedIso B S hS _ ≪≫ asIso (DerivedCategory.Q.map ψP)).symm)

/-- **Condition (4) of the induction: the Mayer–Vietoris step of [Stacks, Tag 0CSR].**  Let
`(U ⊆ W, V ⟶ W)` be an elementary distinguished square of quasi-compact algebraic spaces with
affine diagonal, `P = U ×_W V`, and assume the derived inclusion `D(QCoh(𝒪_W)) ⥤ D(𝒪_W)` is fully
faithful.  If `P` holds for `U`, `V` and `P`, it holds for `W`.

For a K-injective complex `I` of `QCoh(𝒪_W)`, the maps `I ⟶ j_{U,*}J_U ⊕ j_{V,*}J_V` to the direct
images of K-injective resolutions of the restrictions span a distinguished triangle of
`K(QCoh(𝒪_W))` whose third vertex is `j_{P,*}J_P`
(`AlgebraicGeometry.Space.nonempty_iso_obj₃_of_square`); `g_*` computes `Rg_*` at the direct
images by the last paragraph of the source's proof
(`AlgebraicGeometry.Space.pushforwardComputesDerivedAt_quasicoherentPushforward`), hence at `I` by
two out of three. -/
theorem pushforwardComputesDerivedOnQuasicoherentKInjectives_of_square
    [((quasicoherentSheavesι B S hS W).mapDerivedCategory).Full]
    [((quasicoherentSheavesι B S hS W).mapDerivedCategory).Faithful]
    (hW : IsQuasiCompactWithAffineDiagonal B S hS hZ W.1)
    (hUq : IsQuasiCompactWithAffineDiagonal B S hS hZ (edsOpen B S hS hsq).1)
    (hVq : IsQuasiCompactWithAffineDiagonal B S hS hZ (edsEtale B S hS hsq).1)
    (hPq : IsQuasiCompactWithAffineDiagonal B S hS hZ (edsInter B S hS hsq).1)
    (hQU : PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ (edsOpen B S hS hsq))
    (hQV : PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ (edsEtale B S hS hsq))
    (hQP : PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ (edsInter B S hS hsq)) :
    PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ W := by
  intro Z hZqc g I hI
  have := hI
  let hpU := pushforwardPreservesQuasicoherence_of_isQuasiCompactWithAffineDiagonal B S hS hZ
    (edsOpenHom B S hS hsq) hUq hW
  let hpV := pushforwardPreservesQuasicoherence_of_isQuasiCompactWithAffineDiagonal B S hS hZ
    (edsEtaleHom B S hS hsq) hVq hW
  let hpP := pushforwardPreservesQuasicoherence_of_isQuasiCompactWithAffineDiagonal B S hS hZ
    (edsInterHom B S hS hsq) hPq hW
  obtain ⟨E', t, hE', ht⟩ := exists_quasiIso_isKInjective_modules B S hS W.1 W.2
    (((quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have := hE'
  have := ht
  obtain ⟨JU, hJU, aU, ψU, hψU, hU⟩ := exists_quasicoherentUnit_comp_eq B S hS
    (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) hpU (fun J hJ => hQU W hW _ J hJ) I t
  obtain ⟨JV, hJV, aV, ψV, hψV, hV⟩ := exists_quasicoherentUnit_comp_eq B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) hpV (fun J hJ => hQV W hW _ J hJ) I t
  obtain ⟨JP, hJP, -, ψP, hψP, -⟩ := exists_quasicoherentUnit_comp_eq B S hS
    (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq) hpP (fun J hJ => hQP W hW _ J hJ) I t
  have := hJU
  have := hJV
  have := hJP
  have := hψU
  have := hψV
  have := hψP
  obtain ⟨C, β, γ, hT⟩ := distinguished_cocone_triangle
    (biprod.lift ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map aU)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map aV))
  obtain ⟨eC⟩ := nonempty_iso_obj₃_of_square B S hS hsq hpU hpV hpP I t JU aU ψU hU JV aV ψV hV
    JP ψP β γ hT
  have h₂ := pushforwardComputesDerivedAt_biprod B S hS g _ _
    (pushforwardComputesDerivedAt_quasicoherentPushforward B S hS hZ _
      (isEtale_edsOpenHom B S hS hsq) hpU g hQU hW hZqc JU hJU)
    (pushforwardComputesDerivedAt_quasicoherentPushforward B S hS hZ _
      (isEtale_edsEtaleHom B S hS hsq) hpV g hQV hW hZqc JV hJV)
  have h₃ := (pushforwardComputesDerivedAt_quasicoherentPushforward B S hS hZ _
      (isEtale_edsInterHom B S hS hsq) hpP g hQP hW hZqc JP hJP).of_iso B S hS g eC.symm
  exact (pushforwardComputesDerivedAt_quotient_iff B S hS g I).1
    (pushforwardComputesDerivedAt_obj₁ B S hS g _ hT h₂ h₃)

end MayerVietorisStep

/-- If the comparison functor `D(QCoh(𝒪_W)) ⥤ D_QCoh(𝒪_W)` of [Stacks, Tag 08F1] is an
equivalence, the derived inclusion `D(QCoh(𝒪_W)) ⥤ D(𝒪_W)` is fully faithful: it is the
comparison followed by the fully faithful inclusion of `D_QCoh(𝒪_W)`
(`AlgebraicGeometry.Space.quasicoherentDerivedComparisonCompιIso`). -/
theorem full_faithful_mapDerivedCategory_of_isEquivalence (W : AlgebraicSpaces B S hS)
    [(quasicoherentDerivedComparisonSchemeUniverse B S hS W.1 W.2).IsEquivalence] :
    ((quasicoherentSheavesι B S hS W).mapDerivedCategory).Full ∧
      ((quasicoherentSheavesι B S hS W).mapDerivedCategory).Faithful := by
  let e := quasicoherentDerivedComparisonCompιIso B S hS W.1 W.2
  have h₁ : (quasicoherentDerivedComparisonSchemeUniverse B S hS W.1 W.2 ⋙
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).ι).Full :=
    inferInstance
  have h₂ : (quasicoherentDerivedComparisonSchemeUniverse B S hS W.1 W.2 ⋙
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS W.1 W.2).O))).ι).Faithful :=
    inferInstance
  exact ⟨@Functor.Full.of_iso _ _ _ _ _ _ h₁ e, @Functor.Faithful.of_iso _ _ _ _ _ _ h₂ e⟩

/-! ### The induction -/

/-- **The induction of [Stacks, Tag 0CSR], given the full faithfulness of the derived inclusions.**
Let `X` be a quasi-compact algebraic space with affine diagonal over `ℤ`, and assume that for
every quasi-compact algebraic space `W` with affine diagonal the derived inclusion
`D(QCoh(𝒪_W)) ⥤ D(𝒪_W)` is fully faithful.  Then `P(X)` holds: for every `g : X ⟶ Z` with `Z`
quasi-compact with affine diagonal, `g_*` computes `Rg_*` at every K-injective complex of
`QCoh(𝒪_X)`.

This is the induction principle of [Stacks, Tag 08GQ] in the collection of
[Stacks, Tag 08GR] (2), the quasi-compact objects of `X_{spaces, étale}` with affine diagonal:
condition (3)(b) is
`AlgebraicGeometry.Space.pushforwardComputesDerivedOnQuasicoherentKInjectives_of_isAffineSpace`
and condition (4) is
`AlgebraicGeometry.Space.pushforwardComputesDerivedOnQuasicoherentKInjectives_of_square`. -/
theorem pushforwardComputesDerivedOnQuasicoherentKInjectives_of_fullyFaithful
    (hff : ∀ W : AlgebraicSpaces B S hS, IsQuasiCompactWithAffineDiagonal B S hS hZ W.1 →
      ((quasicoherentSheavesι B S hS W).mapDerivedCategory).Full ∧
        ((quasicoherentSheavesι B S hS W).mapDerivedCategory).Faithful)
    (X : AlgebraicSpaces B S hS) (hX : IsQuasiCompactWithAffineDiagonal B S hS hZ X.1) :
    PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ X := by
  have key := qcqs_induction_on_collection B S hS hZ X hX.1
    (isAbsolutelyQuasiSeparated_of_isQuasiCompactWithAffineDiagonal B S hS hZ X hX)
    (fun Y _ => IsQuasiCompactWithAffineDiagonal B S hS hZ Y)
    (fun Y _ => ∀ hY : IsAlgebraicSpace B S hS Y,
      PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ ⟨Y, hY⟩)
    (fun W hW => ⟨hW.1, IsQuasiCompactWithAffineDiagonal.isAbsolutelyQuasiSeparated
      B S hS hZ X W hW⟩)
    (fun W U i hW hUspace hi hUqc =>
      IsQuasiCompactWithAffineDiagonal.of_openImmersion B S hS hZ X W U i hW hUspace hi hUqc)
    (isQuasiCompactWithAffineDiagonal_of_isAffineSpace B S hS hZ X)
    (fun V hV hY => pushforwardComputesDerivedOnQuasicoherentKInjectives_of_isAffineSpace
      B S hS hZ ⟨V.1.left.1, hY⟩ hV)
    (by
      intro W V U f _ hsq hBW hUqc hVaff hPU hPV hPpb hY
      have hUq : IsQuasiCompactWithAffineDiagonal B S hS hZ (edsOpen B S hS hsq).1 :=
        IsQuasiCompactWithAffineDiagonal.of_openImmersion B S hS hZ X W U.toFunctor U.ι hBW
          hsq.isOpenSubspace.1 hsq.isOpenSubspace.2 hUqc
      have hVq : IsQuasiCompactWithAffineDiagonal B S hS hZ (edsEtale B S hS hsq).1 :=
        isQuasiCompactWithAffineDiagonal_of_isAffineSpace B S hS hZ X V hVaff
      have hpbqc : IsQuasiCompactSpace B S hS (pullback U.ι f) :=
        isQuasiCompactSpace_pullback B S hS hZ U.ι f hsq.isOpenSubspace.1
          W.1.left.property hUqc (IsAffineSpace.isQuasiCompactSpace hVaff)
          (isAbsolutelyQuasiSeparated_of_isQuasiCompactWithAffineDiagonal B S hS hZ W.1.left hBW)
      have hpbopen : IsOpenImmersion B S hS (pullback.snd U.ι f) := by
        let Q : MorphismProperty (BigFppfOver B S hS) :=
          MorphismProperty.inverseImage
            (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)
        let _ : Q.presheaf.IsStableUnderBaseChange :=
          MorphismProperty.relative_isStableUnderBaseChange Q
        show Q.presheaf (pullback.snd U.ι f)
        exact MorphismProperty.pullback_snd (P := Q.presheaf) U.ι f hsq.isOpenSubspace.2
      have hPq : IsQuasiCompactWithAffineDiagonal B S hS hZ (edsInter B S hS hsq).1 :=
        IsQuasiCompactWithAffineDiagonal.of_openImmersion B S hS hZ X V (pullback U.ι f)
          (pullback.snd U.ι f)
          (isQuasiCompactWithAffineDiagonal_of_isAffineSpace B S hS hZ X V hVaff)
          (edsInter B S hS hsq).2 hpbopen hpbqc
      obtain ⟨hfull, hfaith⟩ := hff W.1.left hBW
      exact pushforwardComputesDerivedOnQuasicoherentKInjectives_of_square B S hS hZ hsq hBW hUq
        hVq hPq (hPU hsq.isOpenSubspace.1) (hPV hsq.isAlgebraicSpace)
        (hPpb (edsInter B S hS hsq).2))
  exact key ⟨Over.mk (𝟙 X), by intro T φ hφ; simpa using hφ⟩ hX X.2

/-! ### The square -/

section Square

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hX : IsQuasiCompactWithAffineDiagonal B S hS hZ X.1)
  (hY : IsQuasiCompactWithAffineDiagonal B S hS hZ Y.1)
  (Φ : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2))
  (αΦ : (quasicoherentPushforward B S hS f
      (pushforwardPreservesQuasicoherence_of_isQuasiCompactWithAffineDiagonal B S hS hZ f hX
        hY)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Φ)
  [Φ.IsRightDerivedFunctor αΦ
    (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
  (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  [Rf.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]

omit [Φ.IsRightDerivedFunctor αΦ
  (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] in
include hY in
/-- **`P(X)` makes the derived direct image computed on K-injectives.**  If `P(X)` holds, then
for `f : X ⟶ Y` with `Y` quasi-compact with affine diagonal, the unit of `Rf_*` is invertible at
every K-injective complex of `QCoh(𝒪_X)`. -/
theorem derivedPushforwardComputedOnKInjectives_of_computes
    (hP : PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ X) :
    DerivedPushforwardComputedOnKInjectives B S hS f Rf α :=
  fun I hI => (pushforwardComputesDerived_iff_isIso B S hS f Rf α _).1 (hP Y hY f I hI)

/-- **The square of [Stacks, Tag 0CSR], given `P(X)`.**  If `f_*` computes `Rf_*` at every
K-injective complex of `QCoh(𝒪_X)`, the canonical comparison
`Stacks.DerivedCoherator.pushforwardSquareComparison` between `Φ` and `Rf_*` is invertible, and
read through the comparison functors of [Stacks, Tag 08F1] it is the commutative square. -/
def derivedQuasicoherentPushforwardSquareOfComputes
    (hP : PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ X) :
    Φ ⋙ quasicoherentDerivedComparisonSchemeUniverse B S hS Y.1 Y.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι ≅
      quasicoherentDerivedComparisonSchemeUniverse B S hS X.1 X.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⋙ Rf :=
  letI := isGrothendieckAbelian_quasicoherentSheaves_algebraicSpace B S hS X
  haveI : IsIso (Stacks.DerivedCoherator.pushforwardSquareComparison.{u}
      (quasicoherentSheavesι B S hS X) (quasicoherentSheavesι B S hS Y) _
      (modulePushforward B S hS f) (quasicoherentPushforwardCompιIso B S hS f _) Φ αΦ Rf α) :=
    (derivedPushforwardSquareCommutes_iff B S hS f _ Φ αΦ inferInstance Rf α).2
      (derivedPushforwardComputedOnKInjectives_of_computes B S hS hZ f hY Rf α hP)
  Functor.isoWhiskerLeft Φ (quasicoherentDerivedComparisonCompιIso B S hS Y.1 Y.2) ≪≫
    asIso (Stacks.DerivedCoherator.pushforwardSquareComparison.{u}
      (quasicoherentSheavesι B S hS X) (quasicoherentSheavesι B S hS Y) _
      (modulePushforward B S hS f) (quasicoherentPushforwardCompιIso B S hS f _) Φ αΦ Rf α) ≪≫
    Functor.isoWhiskerRight (quasicoherentDerivedComparisonCompιIso B S hS X.1 X.2).symm Rf ≪≫
    Functor.associator _ _ _

end Square

end AlgebraicGeometry.Space

end
