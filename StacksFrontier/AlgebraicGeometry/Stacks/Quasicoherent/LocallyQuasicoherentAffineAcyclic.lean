module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianUniverse
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.ModuleAbelianSectionsUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally quasi-coherent modules have no higher cohomology over affine objects

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u`, the seating of the 2-category of algebraic
stacks, and let `ℱ` be a locally quasi-coherent sheaf of `O_𝒳`-modules on `𝒳_{étale}` with
sections in `Type (u + 1)`. For an object `x` of `𝒳` lying over an affine scheme `U`,

`H^n(x, ℱ) = 0` for `n > 0`.

This is the vanishing used in the affine case of Stacks 0765, whose proof cites Stacks 075F and
Cohomology of Schemes, Lemma 01XB, through Stacks 03DW. Module cohomology over `x` is abelian
cohomology over `x` (Stacks 03FD), which is the étale cohomology of `U` of the restriction
`ℱ|_{U_{étale}}` along the functor `U_{étale} ⥤ 𝒳` of Stacks 06W1 (restriction is exact and
preserves injectives, Stacks 04BH). This restriction is quasi-coherent by definition of local
quasi-coherence (Stacks 06WJ), and quasi-coherent modules on the small étale site of an affine
scheme have no higher cohomology.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_sections_of_isQuasicoherentOnSite`: a
  quasi-coherent module on a small étale site, with sections in `Type (u + 1)`, has no higher
  abelian cohomology over an object with affine underlying scheme.
* `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_isLocallyQuasicoherent`: a locally
  quasi-coherent module on `𝒳_{étale}` has no higher cohomology over an object lying over an
  affine scheme.

## References

* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 075F](https://stacks.math.columbia.edu/tag/075F)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

-- The ambient-universe instances on sheaves of modules state their module universe as a `max`
-- pattern which the module universe below does not match syntactically; the same instances are
-- supplied at explicit universes.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

/-- If `P ⋙ G ≅ H` with `P` exact and carrying injectives to injectives, and `G`, `H` additive,
then vanishing of `Rⁿ G` at `P M` gives vanishing of `Rⁿ H` at `M`. -/
private theorem isZero_rightDerived_of_comp_iso {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
    (P : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [G.Additive] [H.Additive]
    (hP : ∀ I : C, Injective I → Injective (P.obj I)) (e : P ⋙ G ≅ H) (M : C) (n : ℕ)
    (h : IsZero ((G.rightDerived n).obj (P.obj M))) : IsZero ((H.rightDerived n).obj M) := by
  have : P.Additive := Functor.additive_of_preserves_binary_products _
  exact h.of_iso (Functor.rightDerivedObjIsoOfComp P G H hP e M n).symm

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A quasi-coherent module on a small étale site has no higher cohomology over an affine
object**, with its sections in `Type (u + 1)`: for an object `T` of `S_étale` with affine
underlying scheme and `n > 0`, the `n`-th derived functor of abelian sections over `T` vanishes
on the underlying abelian sheaf. -/
@[sga "4 VII 4.4" "more general"]
theorem isZero_rightDerived_sections_of_isQuasicoherentOnSite
    (G : SheafOfModules.{u + 1} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (T : SmallEtale B S hS) (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (n : ℕ) (hn : 0 < n) :
    letI := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} (topology B S hS)
    letI := Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, 0}
      (J := topology B S hS)
    IsZero ((((sheafSections (topology B S hS) AddCommGrpCat.{u + 1}).obj (op T)).rightDerived
      n).obj ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj G)) := by
  let hJ := SmallAffineEtale.isFlatCofinal B S hS
  let R' := Stacks.AffineSiteBaseChange.ringsSheaf hJ
  let J := topology B S hS
  let J' := SmallAffineEtale.topology B S hS
  let j := SmallAffineEtale.inclusion B S hS
  let := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} J
  let := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} J'
  let := AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1,
    u} J'
  let := Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, 0} (J := J)
  let := Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, 0} (J := J')
  let := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, 0} (J := J')
  let := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, 0} R'
  have hds : j.IsDenseSubsite J' J := (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
  let T' : SmallAffineEtale B S hS := ⟨T, hT⟩
  let N := (SmallEtale.sheafAffineRestrictionSucc B S hS).obj G
  have hN : Stacks.ModulesOnACategory.ChaoticComparison.IsCartesianPresheaf N.val :=
    SmallEtale.isCartesianPresheaf_affineRestriction B S hS G (fun g hT₁ hT₂ ↦
      (ConcreteCategory.isIso_iff_bijective _).2
        (bijective_restrictionBaseChange_of_isQuasicoherentOnSite_univ.{u, u + 1} B S hS G hG
          hT₁ hT₂ g))
  have h₁ := SmallAffineEtale.isZero_rightDerived_evaluation_of_isCartesian B S hS N hN T' n hn
  have h₂ := (Stacks.Cohomology.ModuleAbelianSectionsUnivLE.isZero_rightDerived_evaluation_iff.{0}
    J' R' N T' n).1 h₁
  let P := j.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J' J
  have : ((sheafSections J' AddCommGrpCat.{u + 1}).obj (op T')).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : ((sheafSections J AddCommGrpCat.{u + 1}).obj (op T)).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact isZero_rightDerived_of_comp_iso P ((sheafSections J' AddCommGrpCat.{u + 1}).obj (op T'))
    ((sheafSections J AddCommGrpCat.{u + 1}).obj (op T)) (fun _ _ ↦ inferInstance) (Iso.refl _)
    _ n h₂

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section Limits

variable (U : Scheme.{u}) (hU : E.Contains U)

/-- The inclusion of the small étale site of `U` into the slice at `U` of a big fppf site with the
same size cutoff preserves fibre products, as the functor of underlying schemes does
(Stacks 021D). -/
theorem preservesPullbacks_smallEtaleInclusion_fppf :
    PreservesLimitsOfShape WalkingCospan (smallEtaleInclusion B E h U hU) := by
  have h₁ : PreservesLimitsOfShape WalkingCospan
      ((smallEtaleInclusion B E h U hU ⋙ Over.forget _) ⋙ B.inclusion) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (SmallEtale.toScheme E U hU))
  have h₂ : PreservesLimitsOfShape WalkingCospan
      (smallEtaleInclusion B E h U hU ⋙ Over.forget _) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ B.inclusion
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _)

/-- The inclusion of the small étale site of `U` into the slice at `U` of a big fppf site with the
same size cutoff preserves equalizers. -/
theorem preservesEqualizers_smallEtaleInclusion_fppf :
    PreservesLimitsOfShape WalkingParallelPair (smallEtaleInclusion B E h U hU) := by
  have := preservesPullbacks_smallEtaleInclusion_fppf B E h U hU
  have : HasBinaryProducts (SmallEtale E U hU) := hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have : PreservesLimit (Functor.empty.{0} (SmallEtale E U hU))
      (smallEtaleInclusion B E h U hU) :=
    preservesLimit_of_preserves_limit_cone (SmallEtale.finalIsTerminal E U hU)
      ((isLimitMapConeEmptyConeEquiv _ _).symm Over.mkIdTerminal)
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (smallEtaleInclusion B E h U hU) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  have : PreservesLimitsOfShape (Discrete WalkingPair) (smallEtaleInclusion B E h U hU) :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks _
  exact preservesEqualizers_of_preservesPullbacks_and_binaryProducts _

end Limits

variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

attribute [local instance] Stacks.SheafOfModulesEvaluation.evaluation_additive

/-- **A locally quasi-coherent module has no higher cohomology over an object lying over an
affine scheme.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be fibred in groupoids, with objects in
`Type (u + 1)` and morphisms in `Type u`, and `ℱ` a locally quasi-coherent sheaf of
`O_𝒳`-modules on `𝒳_{étale}` with sections in `Type (u + 1)`. For an object `x` lying over an
affine scheme and `n > 0`, `H^n(x, ℱ) = 0`. -/
theorem isZero_rightDerived_evaluation_of_isLocallyQuasicoherent
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hF : IsLocallyQuasicoherent B E h S hS p hp F.val) (x : 𝒳)
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) (n : ℕ) (hn : 0 < n) :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS p
    letI := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)
    IsZero (((SheafOfModules.evaluation.{u + 1} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B)) (op x)).rightDerived n).obj F) := by
  let := hasSheafify_associatedTopology_of_category_succ B S hS p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS p
  let := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)
  let := isEquivalence_overPost B S hS p hp x
  let K := associatedTopology B S hS p (etaleTopology B)
  let R := ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)
  let U := (p.obj x).left.1
  let hU : E.Contains U := contains_base B E h S hS p x
  let J := SmallEtale.topology E U hU
  let q := smallEtaleInclusion B E h U hU ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
  obtain ⟨hq₁, hq₂⟩ := isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp x
  have : q.IsContinuous J K := hq₁
  have : q.IsCocontinuous J K := hq₂
  let := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} J
  let := Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, 0} (J := J)
  let := Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, 0} (J := K)
  let := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, 0} (J := K)
  refine (Stacks.Cohomology.ModuleAbelianSectionsUnivLE.isZero_rightDerived_evaluation_iff.{0}
    K R F x n).2 ?_
  have : PreservesLimitsOfShape WalkingCospan q := by
    have := preservesPullbacks_smallEtaleInclusion_fppf B E h U hU
    infer_instance
  have : PreservesLimitsOfShape WalkingParallelPair q := by
    have := preservesEqualizers_smallEtaleInclusion_fppf B E h U hU
    infer_instance
  have : HasBinaryProducts (SmallEtale E U hU) := hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have : HasEqualizers (SmallEtale E U hU) := hasEqualizers_of_hasPullbacks_and_binary_products
  let P := q.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K
  have : P.IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous q AddCommGrpCat.{u + 1} J
      K).isRightAdjoint
  have : PreservesFiniteColimits P :=
    Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous J K q _
  have : P.PreservesInjectiveObjects :=
    Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous J K q
  have : ((sheafSections J AddCommGrpCat.{u + 1}).obj (op (SmallEtale.final E U hU))).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : ((sheafSections K AddCommGrpCat.{u + 1}).obj (op x)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hT : AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E U hU).obj (SmallEtale.final E U hU)) := hx
  have h₁ := SmallEtale.isZero_rightDerived_sections_of_isQuasicoherentOnSite E U hU
    ((restrictSheafToSmallEtale B E h S hS p hp x).obj F)
    ((isLocallyQuasicoherent_iff B E h S hS p hp F).1 hF x) (SmallEtale.final E U hU) hT n hn
  let e : P ⋙ (sheafSections J AddCommGrpCat.{u + 1}).obj (op (SmallEtale.final E U hU)) ≅
      (sheafSections K AddCommGrpCat.{u + 1}).obj (op x) :=
    (Iso.refl _ : _ ≅ (sheafSections K AddCommGrpCat.{u + 1}).obj
      (op (smallEtaleFinalObject B E h S hS p hp x))) ≪≫
      (sheafSections K AddCommGrpCat.{u + 1}).mapIso
        (smallEtaleFinalObjectIso B E h S hS p hp x).op.symm
  exact SmallEtale.isZero_rightDerived_of_comp_iso P _ _ (fun _ _ ↦ inferInstance) e _ n h₁

end AlgebraicGeometry.Stack

end
