module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LisseEtaleRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedQuasicoherentRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeEtaleFppfDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticPullbackVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LisseEtaleDerivedModuleLowerShriekSheafFlatBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07B9 (1): `g^*` and `Lg_!` for the lisse-étale site

Let `𝒳` be an algebraic stack, `g` the morphism of ringed topoi of **Stacks 0788** for the
lisse-étale site, with `g^*` restriction to the smooth objects and `Lg_!` its left adjoint
(**Stacks 07AS**).  `LQCoh^fbc(𝒪_𝒳)` is the class of modules on `𝒳_étale` with the flat base
change property of **Stacks 0762** read with the pullback of sheaves.

* (1)(a), `AlgebraicGeometry.Stack.LisseEtale.derivedCategoryB_derivedModuleRestriction`;
* (1)(b),
  `AlgebraicGeometry.Stack.LisseEtale.isZero_derivedModuleRestriction_iff_derivedParasitic`,
  through the parasitic modules of `LQCoh^fbc` being those vanishing at the smooth objects
  (Stacks 07AR (1) for the pullback of sheaves,
  `AlgebraicGeometry.Stack.LisseEtale.isParasitic_iff_isZero_lisseRestriction`);
* (1)(c), `AlgebraicGeometry.Stack.LisseEtale.derivedCategoryB_derivedModuleLowerShriek`, from
  Stacks 07B3 (1) by the dévissage of the source.

## References

* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
* [Stacks Project, Tag 07B8](https://stacks.math.columbia.edu/tag/07B8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WeakSerre
open Stacks.Cohomology.DerivedLowerShriek

universe u w t t'

namespace AlgebraicGeometry.Stack.LisseEtale

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  Stacks.hasSheafCompose_forget₂_commRingCat Stacks.essentiallySmall_over

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

section Parasitic

variable {B E h S hS 𝒳}

/-- **The comparison map moves the vanishing of a restriction down an arrow** along which it
induces an isomorphism of sheaves: the sheafified pullback of a zero module is zero. -/
theorem isZero_restrictModuleToSmallEtale_of_isIso_sheafifiedRestrictComparison
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    {x y : 𝒳.val.val.obj} (φ : x ⟶ y)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (𝒳.val.val.p.obj x).left.1
        (contains_base B E h S hS 𝒳.val.val.p x))
      (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F φ hMx))
    (hy : IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids y (etaleTopology B) (etaleTopology_le_topology B) F)) :
    IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids x (etaleTopology B) (etaleTopology_le_topology B) F) := by
  have : (PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids φ
        (etaleTopology B) (etaleTopology_le_topology B))).IsLeftAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids φ
        (etaleTopology B) (etaleTopology_le_topology B))).isLeftAdjoint
  have : (PresheafOfModules.sheafification.{u} (𝟙 (SmallEtale.structureSheaf E
      (𝒳.val.val.p.obj x).left.1 (contains_base B E h S hS 𝒳.val.val.p x)).obj)).IsLeftAdjoint :=
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (SmallEtale.structureSheaf E
      (𝒳.val.val.p.obj x).left.1 (contains_base B E h S hS 𝒳.val.val.p x)).obj)).isLeftAdjoint
  have h1 := Functor.map_isZero (PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids φ
        (etaleTopology B) (etaleTopology_le_topology B))) hy
  have h2 := Functor.map_isZero (PresheafOfModules.sheafification.{u} (𝟙 (SmallEtale.structureSheaf
      E (𝒳.val.val.p.obj x).left.1 (contains_base B E h S hS 𝒳.val.val.p x)).obj)) h1
  exact Functor.map_isZero (SheafOfModules.forget _)
    (h2.of_iso (@asIso _ _ _ _ _ hiso).symm)

/-- **Stacks 07AR** (1), (b) implies (a), for the flat base change property read with the
pullback of sheaves: a module in `LQCoh^fbc(𝒪_𝒳)` on `𝒳_étale` whose sections vanish at every
smooth object of `𝒳` is parasitic.  The library's argument
(`AlgebraicGeometry.Stack.LisseEtale.isParasitic_of_subsingleton_smoothObject`), with the
vanishing carried down the flat arrow by the sheafified comparison map. -/
theorem isParasitic_of_subsingleton_smoothObject_of_sheafFlatBaseChange
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hsheaf : Presheaf.IsSheaf
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F)
    (hvan : ∀ y : 𝒳.val.val.obj, smoothObject.{u, w} B S hS 𝒳 y →
      Subsingleton (F.obj (op y))) :
    IsParasitic.{u, w, u} B S hS 𝒳 .etale F := by
  intro z hz
  obtain ⟨t, s, α, ψ, hs, hψ, hα⟩ :=
    exists_covering_flat_arrow_of_flatObject.{u, w} B S hS 𝒳 hz
  have hfbc : HasSheafFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F := hF.2
  have hiso := (isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B) ψ F
    (hF.1.2 t).choose).2 (hfbc ψ hψ)
  have hzt : Subsingleton (F.obj (op t)) :=
    subsingleton_of_isZero_restrictModuleToSmallEtale B E h S hS F t
      (isZero_restrictModuleToSmallEtale_of_isIso_sheafifiedRestrictComparison F ψ
        (hF.1.2 t).choose hiso
        (isZero_restrictModuleToSmallEtale_of_smoothObject B E h S hS F hvan s hs))
  have hzt' : IsZero (F.presheaf.obj (op t)) := @AddCommGrpCat.isZero_of_subsingleton _ hzt
  have hsep : Presieve.IsSeparatedFor
      (F.presheaf ⋙ coyoneda.obj (op (F.presheaf.obj (op z)))) (Presieve.singleton α) := by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact (hsheaf _ _ hα).isSeparatedFor
  have hid : 𝟙 (F.presheaf.obj (op z)) =
      (0 : F.presheaf.obj (op z) ⟶ F.presheaf.obj (op z)) := by
    refine hsep.ext fun {Y} {f} hf => ?_
    cases hf
    show (𝟙 (F.presheaf.obj (op z))) ≫ F.presheaf.map α.op
        = (0 : F.presheaf.obj (op z) ⟶ F.presheaf.obj (op z)) ≫ F.presheaf.map α.op
    rw [hzt'.eq_zero_of_tgt (F.presheaf.map α.op), comp_zero, comp_zero]
  exact AddCommGrpCat.subsingleton_of_isZero ((IsZero.iff_id_eq_zero _).2 hid)

/-- **Stacks 07AR** (1), for the flat base change property read with the pullback of sheaves: a
module in `LQCoh^fbc(𝒪_𝒳)` on `𝒳_étale` is parasitic exactly when its restriction to the
lisse-étale site vanishes. -/
theorem isParasitic_iff_isZero_lisseRestriction (F : SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
    (hF : locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳 F) :
    IsParasitic.{u, w, u} B S hS 𝒳 .etale F.val ↔ IsZero ((lisseRestriction B S hS 𝒳).obj F) := by
  refine Iff.trans ?_ (isZero_sheafOfModules_iff_forall_subsingleton _).symm
  exact ⟨fun hpar V => subsingleton_of_isParasitic B S hS F.val hpar V.unop.obj V.unop.property,
    fun hvan => isParasitic_of_subsingleton_smoothObject_of_sheafFlatBaseChange F.val F.isSheaf hF
      fun x hx => hvan (op ⟨x, hx⟩)⟩

end Parasitic

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- The category `Mod(𝒪_{𝒳_{lisse,étale}})` of sheaves of modules on the lisse-étale site. -/
abbrev lisseModules :=
  SheafOfModules.{u} (inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι (lisseAmbientRing B S hS 𝒳))

/-- The quasi-coherent modules on the lisse-étale site, `QCoh(𝒪_{𝒳_{lisse,étale}})`: the
modules which are quasi-coherent on that ringed site in the sense of Stacks 03DL. -/
abbrev lisseQuasicoherentModules : ObjectProperty (lisseModules B S hS 𝒳) :=
  fun M => M.IsQuasicoherentOnSite

/-- Quasi-coherence on the lisse-étale site is invariant under isomorphism. -/
instance isClosedUnderIsomorphisms_lisseQuasicoherentModules :
    (lisseQuasicoherentModules B S hS 𝒳).IsClosedUnderIsomorphisms where
  of_iso e h := SheafOfModules.IsQuasicoherentOnSite.of_iso e h

/-- Sheaves of modules on the lisse-étale site of an algebraic stack form a Grothendieck abelian
category, the site being essentially small. -/
instance isGrothendieckAbelian_lisseModules :
    IsGrothendieckAbelian.{u} (lisseModules B S hS 𝒳) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

section Derived

variable [HasDerivedCategory.{t} (etaleModules B S hS 𝒳)]
  [HasDerivedCategory.{t'} (lisseModules B S hS 𝒳)]

/-- The chosen derived category of `AlgebraicGeometry.Stack.etaleModules`, read at the spelling of
the same category in the source of the restriction to the lisse-étale site. -/
local instance hasDerivedCategory_lisseAmbientModules :
    HasDerivedCategory.{t} (SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳)) :=
  inferInstanceAs (HasDerivedCategory.{t} (etaleModules B S hS 𝒳))

/-- The homology of `g^*K` vanishes exactly when the homology of `K` is parasitic. -/
private theorem isZero_homology_derivedModuleRestriction_iff
    (K : DerivedCategory (etaleModules B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB
      (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳) K) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj ((derivedModuleRestriction B S hS 𝒳).obj K)) ↔
      IsParasitic.{u, w, u} B S hS 𝒳 .etale ((DerivedCategory.homologyFunctor _ n).obj K).val :=
  (((lisseRestriction B S hS 𝒳).mapDerivedCategoryHomologyIso n).app K).isZero_iff.trans
    (isParasitic_iff_isZero_lisseRestriction _ (hK n)).symm

/-- **Stacks 07B9** (1)(a).  For `K` in `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` (with the flat base change
property of Stacks 0762 read with the pullback of sheaves), `g^*K` lies in
`D_QCoh(𝒪_{𝒳_{lisse,étale}})`: `H^n(g^*K) = g^*H^n(K)` is quasi-coherent by Stacks 07B1 (1)(b). -/
@[stacks 07B9 "part (1)(a): for F in D_LQCoh^fbc(𝒳_étale, 𝒪_𝒳) the restriction g^*F to the \
lisse-étale site lies in D_QCoh(𝒪_{𝒳_lisse,étale}), for LQCoh^fbc with the flat base change \
property of Stacks 0762 read with the pullback of sheaves, at module universe u, for any \
models of the derived categories"]
theorem derivedCategoryB_derivedModuleRestriction
    (K : DerivedCategory (etaleModules B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB
      (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳) K) :
    DerivedCategoryB.derivedCategoryB (lisseQuasicoherentModules B S hS 𝒳)
      ((derivedModuleRestriction B S hS 𝒳).obj K) := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((lisseRestriction B S hS 𝒳).mapDerivedCategoryHomologyIso n).app K).symm
    (isQuasicoherentOnSite_moduleRestriction _ (hK n))

/-- **Stacks 07B9** (1)(b).  For `K` in `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)`, `g^*K = 0` exactly when
`K` lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)`. -/
@[stacks 07B9 "part (1)(b): for F in D_LQCoh^fbc(𝒳_étale, 𝒪_𝒳), g^*F = 0 if and only if F \
lies in D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳), 𝒫_𝒳 = Parasitic ∩ LQCoh^fbc, for LQCoh^fbc with the flat \
base change property of Stacks 0762 read with the pullback of sheaves, at module universe u, \
for any models of the derived categories"]
theorem isZero_derivedModuleRestriction_iff_derivedParasitic
    (K : DerivedCategory (etaleModules B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB
      (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳) K) :
    IsZero ((derivedModuleRestriction B S hS 𝒳).obj K) ↔
      DerivedCategory.KernelColocalization.derivedInter (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳) K := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  exact forall_congr' fun n =>
    (isZero_homology_derivedModuleRestriction_iff B E h S hS 𝒳 K hK n).trans
      (and_iff_left (hK n)).symm

end Derived

section LowerShriek

/-- `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` (Stacks 0771 (2)
for the étale site,
`AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange`), read at the
spelling of the target of `Lg_!`. -/
theorem isWeakSerre_lisseAmbientModules :
    IsWeakSerre (fun F : SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳) =>
      IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val) := by
  have := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  exact @isWeakSerre_of_isWeakSerreClass _ _ _ _
    (isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)

/-- `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)` is closed under colimits of sequences (Stacks 0771 (5)), read at the
spelling of the target of `Lg_!`. -/
theorem lisseAmbientModules_colimit
    (F : ℕ ⥤ SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳)) [HasColimit F]
    [HasColimitsOfShape (AsSmall.{u} ℕ) (SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))]
    (hF : ∀ n, IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (F.obj n).val) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (colimit F).val := by
  have := isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChange B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (AsSmall.{u} ℕ)
  have hP := @ObjectProperty.prop_colimit _ _
    (fun F : SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳) =>
      IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val) _ _ ‹_›
    ((AsSmall.equiv.{0, 0, u} (C := ℕ)).inverse ⋙ F) _ (fun _ => hF _)
  exact (isWeakSerre_lisseAmbientModules B E h S hS 𝒳).isClosedUnderIsomorphisms.of_iso
    (Functor.Final.colimitIso (AsSmall.equiv.{0, 0, u} (C := ℕ)).inverse F) hP

/-- **Stacks 07B9** (1)(c).  `Lg_!` carries `D_QCoh(𝒪_{𝒳_{lisse,étale}})` into
`D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)`, the flat base change property of Stacks 0762 being read with the
pullback of sheaves.

This is the dévissage of the source (`DerivedCategory.derivedCategoryB_obj_of_isLE_obj`): `Lg_!`
is triangulated, right t-exact (its right adjoint `g^*` is exact) and commutes with direct sums;
`LQCoh^fbc` is a weak Serre subcategory closed under colimits of sequences (Stacks 0771 (2), (5));
and on a quasi-coherent module in degree `0` it is Stacks 07B3 (1)
(`isLocallyQuasicoherentWithSheafFlatBaseChange_homology_derivedModuleLowerShriek`). It is
stated at the standard models of the derived categories, where Stacks 07B3 (1) is. -/
@[stacks 07B9 "part (1)(c): Lg_! carries D_QCoh(𝒪_{𝒳_lisse,étale}) into \
D_LQCoh^fbc(𝒳_étale, 𝒪_𝒳), for the derived lower shriek of Stacks 07AS (2) and LQCoh^fbc with \
the flat base change property of Stacks 0762 read with the pullback of sheaves, at module \
universe u, at the standard models of the derived categories"]
theorem derivedCategoryB_derivedModuleLowerShriek :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
    ∀ H : DerivedCategory (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB (lisseQuasicoherentModules B S hS 𝒳) H →
        DerivedCategoryB.derivedCategoryB
          (fun F : SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳) =>
            IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u} B E h S hS
              𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val)
          ((derivedModuleLowerShriek B S hS 𝒳).obj H) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
  intro H hH
  have := AB5OfSize_shrink.{0, 0, u, u} (SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
  have := AB5OfSize_shrink.{0, 0, u, u} (lisseModules B S hS 𝒳)
  have : PreservesColimitsOfShape (Discrete ℕ) (derivedModuleLowerShriek B S hS 𝒳) :=
    have := (derivedModuleLowerShriekAdjunction B S hS 𝒳).leftAdjoint_preservesColimits
    inferInstance
  exact DerivedCategory.derivedCategoryB_obj_of_isLE_obj (derivedModuleLowerShriek B S hS 𝒳)
    (isWeakSerre_lisseAmbientModules B E h S hS 𝒳)
    (@FlatFppf.hasExactCountableDirectSums_of_isGrothendieckAbelian _ _ _
      (isGrothendieckAbelian_etaleModules B S hS 𝒳))
    (@FlatFppf.hasExactCountableDirectSums_of_isGrothendieckAbelian (lisseModules B S hS 𝒳) _ _
      (isGrothendieckAbelian_lisseModules B S hS 𝒳))
    (fun X n _ => DerivedCategory.isLE_obj_of_adjunction (lisseRestriction B S hS 𝒳)
      (derivedModuleLowerShriekAdjunction B S hS 𝒳) X n)
    (fun F hF => lisseAmbientModules_colimit B E h S hS 𝒳 F hF)
    (fun M hM q => DerivedCategory.derivedCategoryB_obj_singleFunctor
      (derivedModuleLowerShriek B S hS 𝒳) (lisseQuasicoherentModules B S hS 𝒳) _
      (isWeakSerre_lisseAmbientModules B E h S hS 𝒳).isClosedUnderIsomorphisms
      (fun M hM p => isLocallyQuasicoherentWithSheafFlatBaseChange_homology_derivedModuleLowerShriek
        B E h S hS 𝒳 M hM p) M hM q)
    H hH

end LowerShriek

end AlgebraicGeometry.Stack.LisseEtale

