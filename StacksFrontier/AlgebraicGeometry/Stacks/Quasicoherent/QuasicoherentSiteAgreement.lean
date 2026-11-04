module

public import Mathlib.CategoryTheory.Limits.Creates
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorQuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteFiniteLocallyFreeAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKind
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsBigSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFromEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRule
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpace
public import StacksFrontier.CategoryTheory.Sites.LocallySmallSheafification

/-!
# Quasi-coherent modules on a category fibred in groupoids, read on the three sites

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids and let `QCoh(𝒪_𝒳)` be the category
of modules on `(𝒳_fppf, 𝒪_𝒳)` which are quasi-coherent in the sense of Modules on Sites,
Definition 03DL.  A quasi-coherent module is a sheaf for each of the coarser inherited topologies
as well, so it can be read in `Mod(𝒳_Zar, 𝒪_𝒳)`, in `Mod(𝒳_étale, 𝒪_𝒳)` and in `Mod(𝒪_𝒳)`.  This
file proves that the three readings do not distinguish the constructions of Stacks 06WN:

1. `QCoh(𝒪_𝒳)` has colimits, and they are the colimits computed in each of the three module
   categories (and in `LQCoh(𝒪_𝒳)`);
2. the tensor products of two quasi-coherent modules computed in the three module categories
   agree, and the common value is quasi-coherent;
3. the internal homs computed in the three module categories agree, finite local freeness of a
   quasi-coherent module does not depend on which of the three topologies it is asked for, and
   the internal hom out of a finite locally free quasi-coherent module into a quasi-coherent one
   is quasi-coherent.

The source reduces everything to the big sites of the schemes underlying the objects of `𝒳`:
restriction to `𝒳_τ/x = (Sch/U)_τ` commutes with colimits, tensor products and internal homs, and
on `(Sch/U)_τ` the three statements are Descent, Lemma 0GNE.  The proofs below follow it.

* **Colimits.**  Quasi-coherence on `𝒳_τ` is closed under colimits computed in `Mod(𝒳_τ, 𝒪_𝒳)`,
  for every `τ`: quasi-coherence is local, restriction to a slice commutes with colimits, and on
  `(Sch/U)_τ` quasi-coherence is closed under colimits by Descent, Lemma 0GNC.  A colimit in
  `Mod(𝒳_τ, 𝒪_𝒳)` of quasi-coherent fppf modules is therefore quasi-coherent for `τ`, hence an
  fppf sheaf and quasi-coherent for the fppf topology by Stacks 0EM8; so it is the reading of an
  object of `QCoh(𝒪_𝒳)`, and the fully faithful reading functor creates the colimit.
* **Tensor products.**  The tensor product for the fppf topology is the fppf sheafification of
  the tensor product for `τ`.  The latter is quasi-coherent for `τ`, quasi-coherence on a ringed
  site being stable under tensor products (Modules on Sites, Lemma 03L6), hence an fppf sheaf by
  Stacks 0EM8, and so the sheafification does nothing to it.
* **Internal homs and finite local freeness.**  The internal hom of Modules on Sites,
  Section 04TT, is a construction on presheaves of modules, so the three internal homs have the
  same underlying presheaf of modules.  Finite local freeness for the fppf topology gives it for
  `τ` after restricting to `𝒳/x = (Sch/U)_fppf`, where it is the parenthetical of Descent,
  Lemma 0GNE (3); the converse needs nothing.  Quasi-coherence of the internal hom is then
  `AlgebraicGeometry.FibredSite.internalHomSheaf_isQuasicoherent`.

## Main definitions

* `AlgebraicGeometry.FibredSite.toLocallyQuasicoherentModules`: the inclusion of `QCoh(𝒪_𝒳)` into
  `LQCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.FibredSite.sheafTensor`: the tensor product of sheaves of modules on the
  associated `τ`-site.

## Main results

* `AlgebraicGeometry.FibredSite.isClosedUnderColimitsOfShape_isQuasicoherentOnSite_siteKind`:
  quasi-coherence on `(𝒳_τ, 𝒪_𝒳)` is closed under colimits, for each of the five topologies.
* `AlgebraicGeometry.FibredSite.preservesColimitsOfShape_toSiteModules`: reading a quasi-coherent
  module for a coarser topology preserves colimits.
* `AlgebraicGeometry.FibredSite.sheafTensorSiteAgreement`: the comparison of the tensor products
  computed for the fppf topology and for a coarser one.
* `AlgebraicGeometry.FibredSite.isFiniteLocallyFreeOnSite_toSiteModules_iff`: finite local
  freeness of a quasi-coherent module does not depend on the topology.
* `AlgebraicGeometry.FibredSite.quasicoherentModules_colimits_siteAgreement`,
  `AlgebraicGeometry.FibredSite.sheafTensor_quasicoherent_siteAgreement` and
  `AlgebraicGeometry.FibredSite.internalHomSheaf_quasicoherent_siteAgreement`: **Stacks 06WN (1),
  (2) and (3).**

## Implementation notes

No smallness of `𝒳` is assumed: every slice `𝒳/x` is essentially small, which is all
sheafification of abelian presheaves with sections in `Type u` needs
(`AlgebraicGeometry.Stack.hasSheafify_associatedTopology_siteKind`).  For parts
(1) and (3) the category `𝒳` has objects in `Type (u + 1)` and morphisms in `Type u`, the sizes of
the big fppf category of schemes it lies over, because the identification of the slice `𝒳_τ/x`
with `(Sch/U)_τ` as ringed sites is stated in those universes; part (2) holds for `𝒳` in arbitrary
universes.  Colimits are indexed by categories in `Type u`.

The colimit clause compares `QCoh(𝒪_𝒳)` with `Mod(𝒳_τ, 𝒪_𝒳)` for all five inherited topologies
`τ`, which contains the Zariski and the étale one of the source, and with `LQCoh(𝒪_𝒳)` through the
inclusion `AlgebraicGeometry.FibredSite.toLocallyQuasicoherentModules`, which exists because every
quasi-coherent module is locally quasi-coherent
(`AlgebraicGeometry.Stack.isLocallyQuasicoherent_toSiteModules_etale`).

The module universe of the internal hom of a ringed site is the maximum of the universes of the
site and of its modules, so the internal homs of part (3) are sheaves of modules with sections in
`Type (u + 1)`; this is the internal hom of
`AlgebraicGeometry.FibredSite.internalHomSheaf_isQuasicoherent`.

The tensor product on `(𝒳_τ, 𝒪_𝒳)` is the sheafification of the objectwise tensor product of the
underlying presheaves of modules, `Stacks.SheafOfModules.Tensor.sheafTensor`; agreement for two
topologies is an isomorphism of sheaves of modules for the coarser one, since the two tensor
products live in different categories.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.FibredSite

section Sheafification

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- Weak equivalences of abelian presheaves on an associated site of a category fibred in groupoids
are the locally bijective maps, since every slice is essentially small. -/
private theorem wEqualsLocallyBijective_associatedTopology_of_isFiberedInGroupoids
    (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    (BigFppfOver.associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  have : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := essentiallySmall_over B S hS p hp
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over _

/-- The sheaves of modules on an associated site of a category fibred in groupoids have all
colimits indexed by categories in the universe of the schemes. -/
theorem hasColimitsOfSize_sheafOfModules_of_isFiberedInGroupoids (τ : SiteKind) :
    HasColimitsOfSize.{u, u} (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) := by
  have := Stack.hasSheafify_associatedTopology_siteKind B S hS p hp τ
  have := wEqualsLocallyBijective_associatedTopology_of_isFiberedInGroupoids B S hS p hp τ
  infer_instance

end Sheafification

section Colimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- Restriction of sheaves of modules from an associated site of `𝒳` to its slice at an object
preserves colimits; this is Modules on Sites, Lemma 03DC, for the localization `𝒳_τ/x`. -/
theorem preservesColimitsOfShape_overFunctor_siteKind (τ : SiteKind) (x : 𝒳)
    (K : Type u) [Category.{u} K] :
    PreservesColimitsOfShape K
      (SheafOfModules.overFunctor.{u} (ringStructureSheafCore B S hS p hp τ) x) := by
  have := Stack.hasSheafify_associatedTopology_siteKind B S hS p hp τ
  have := wEqualsLocallyBijective_associatedTopology_of_isFiberedInGroupoids B S hS p hp τ
  have := hasWeakSheafify_over B S hS p hp τ x
  have := wEqualsLocallyBijective_over B S hS p hp τ x
  have h : PreservesColimitsOfSize.{u, u} (SheafOfModules.pushforward.{u}
      (𝟙 ((ringStructureSheafCore B S hS p hp τ).over x))) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (Over.forget x) _
  exact h.preservesColimitsOfShape (J := K)

/-- **Quasi-coherence on `(𝒳_τ, 𝒪_𝒳)` is closed under colimits**, for each of the five
topologies: a colimit, computed in `Mod(𝒳_τ, 𝒪_𝒳)`, of quasi-coherent modules is quasi-coherent.

Quasi-coherence may be tested on the slices `𝒳_τ/x` at all objects, which cover the final
object; restriction to a slice commutes with colimits; and the slice with its restricted
structure sheaf is the big site `(Sch/U)_τ` of the scheme below `x`, where quasi-coherence is
closed under colimits by Descent, Lemma 0GNC (2). -/
theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite_siteKind (τ : SiteKind)
    (K : Type u) [Category.{u} K] :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp τ)).IsClosedUnderColimitsOfShape K := by
  have hslice : ∀ x : 𝒳, ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((ringStructureSheafCore B S hS p hp τ).over x)).inverseImage
      (SheafOfModules.overFunctor.{u}
        (ringStructureSheafCore B S hS p hp τ) x)).IsClosedUnderColimitsOfShape K := by
    intro x
    have : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((ringStructureSheafCore B S hS p hp τ).over x)).IsClosedUnderColimitsOfShape K := by
      rw [isQuasicoherentOnSite_over_eq_inverseImage_kind B S hS p hp τ x]
      have := BigFppfOver.isClosedUnderColimitsOfShape_baseIsQuasicoherentOnSite B
        (baseScheme B S hS p x) (contains_baseScheme B S hS p x) τ K
      infer_instance
    have := preservesColimitsOfShape_overFunctor_siteKind B S hS p hp τ x K
    infer_instance
  refine ⟨fun M hM => ?_⟩
  show M.IsQuasicoherentOnSite
  rw [Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite M]
  refine ⟨ULift.{u + 1} 𝒳, fun i => i.down,
    Stacks.SheafOfModules.coversTop_ulift_self _, fun i => ?_⟩
  have h2 : SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp τ) ≤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((ringStructureSheafCore B S hS p hp τ).over i.down)).inverseImage
        (SheafOfModules.overFunctor.{u}
          (ringStructureSheafCore B S hS p hp τ) i.down) :=
    fun N hN => Stacks.SheafOfModules.isQuasicoherentOnSite_over N hN i.down
  have := hslice i.down
  exact ObjectProperty.colimitsOfShape_le _ K M
    (ObjectProperty.colimitsOfShape_monotone K h2 M hM)

/-- `QCoh(𝒪_𝒳)` has all colimits indexed by categories in the universe of the schemes. -/
theorem hasColimitsOfSize_quasicoherentModules_of_isFiberedInGroupoids :
    HasColimitsOfSize.{u, u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) := by
  have := hasColimitsOfSize_sheafOfModules_of_isFiberedInGroupoids B S hS p hp .fppf
  exact ⟨fun K _ =>
    have := isClosedUnderColimitsOfShape_isQuasicoherentOnSite_siteKind B S hS p hp .fppf K
    inferInstance⟩

/-- Colimits in `QCoh(𝒪_𝒳)` are colimits in `Mod(𝒪_𝒳)`: the inclusion preserves them. -/
theorem preservesColimitsOfSize_quasicoherentInclusion_of_isFiberedInGroupoids :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι := by
  have := hasColimitsOfSize_sheafOfModules_of_isFiberedInGroupoids B S hS p hp .fppf
  exact ⟨fun {K} _ =>
    have := isClosedUnderColimitsOfShape_isQuasicoherentOnSite_siteKind B S hS p hp .fppf K
    inferInstance⟩

/-- **Colimits in `QCoh(𝒪_𝒳)` are colimits in `Mod(𝒳_τ, 𝒪_𝒳)`**, for each of the five
topologies: reading a quasi-coherent fppf module for the inherited `τ`-topology preserves
colimits.

The colimit in `Mod(𝒳_τ, 𝒪_𝒳)` of the readings of a diagram of quasi-coherent modules is
quasi-coherent for `τ` (each reading is, by Stacks 0EM8, and quasi-coherence on `𝒳_τ` is closed
under colimits), hence an fppf sheaf and quasi-coherent for the fppf topology by Stacks 0EM8
again.  So it is the reading of an object of `QCoh(𝒪_𝒳)`, and since the reading is fully faithful
it creates the colimit. -/
theorem preservesColimitsOfShape_toSiteModules (τ : SiteKind) (K : Type u) [Category.{u} K] :
    PreservesColimitsOfShape K (toSiteModules.{u, u + 1, u, u} B S hS p hp τ) := by
  have := hasColimitsOfSize_sheafOfModules_of_isFiberedInGroupoids B S hS p hp τ
  have := isClosedUnderColimitsOfShape_isQuasicoherentOnSite_siteKind B S hS p hp τ K
  refine ⟨fun {D} => ?_⟩
  let T := toSiteModules.{u, u + 1, u, u} B S hS p hp τ
  have hL : (colimit (D ⋙ T)).IsQuasicoherentOnSite :=
    ObjectProperty.prop_colimit _ _ (fun k =>
      quasicoherentOnSiteOfLeFppf_siteKind B S hS p hp τ (D.obj k).obj (D.obj k).property)
  have hsh := isSheafFppfOfQuasicoherentOnSite_siteKind B S hS p hp τ _ hL
  let X : quasicoherentModules.{u, u + 1, u, u} B S hS p hp :=
    ⟨⟨(colimit (D ⋙ T)).val, hsh⟩,
      isQuasicoherentOnSite_of_siteRestriction B S hS p hp τ ⟨_, hsh⟩ hL⟩
  have : CreatesColimit D T := createsColimitOfFullyFaithfulOfIso X (Iso.refl _)
  infer_instance

/-- Reading a quasi-coherent module on the inherited étale site gives a locally quasi-coherent
module: the inclusion of `QCoh(𝒪_𝒳)` into `LQCoh(𝒪_𝒳)`.  On underlying sheaves of modules it is
`AlgebraicGeometry.FibredSite.toSiteModules` at the étale topology. -/
noncomputable def toLocallyQuasicoherentModules (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) :
    quasicoherentModules.{u, u + 1, u, u} B S hS p hp ⥤
      Stack.locallyQuasicoherentModules.{u, u + 1, u, u} B E h S hS p hp :=
  ObjectProperty.lift _ (toSiteModules B S hS p hp .etale)
    (fun F => Stack.isLocallyQuasicoherent_toSiteModules_etale B E h S hS p hp F)

/-- The inclusion of `QCoh(𝒪_𝒳)` into `LQCoh(𝒪_𝒳)`, followed by the inclusion of `LQCoh(𝒪_𝒳)`
into `Mod(𝒳_étale, 𝒪_𝒳)`, is the reading of a quasi-coherent module on the inherited étale
site. -/
noncomputable def toLocallyQuasicoherentModulesCompι (E : BigEtaleSite.{u})
    (h : E.cutoff = B.cutoff) :
    toLocallyQuasicoherentModules B S hS p hp E h ⋙
        (Stack.isLocallyQuasicoherent.{u, u + 1, u, u} B E h S hS p hp).ι ≅
      toSiteModules B S hS p hp .etale :=
  ObjectProperty.liftCompιIso _ _ _

/-- **Colimits in `QCoh(𝒪_𝒳)` are colimits in `LQCoh(𝒪_𝒳)`.**  Their image in
`Mod(𝒳_étale, 𝒪_𝒳)` is a colimit there, and the inclusion of `LQCoh(𝒪_𝒳)` into
`Mod(𝒳_étale, 𝒪_𝒳)` is fully faithful, so it reflects colimits. -/
theorem preservesColimitsOfShape_toLocallyQuasicoherentModules (E : BigEtaleSite.{u})
    (h : E.cutoff = B.cutoff) (K : Type u) [Category.{u} K] :
    PreservesColimitsOfShape K (toLocallyQuasicoherentModules B S hS p hp E h) := by
  have : PreservesColimitsOfShape K (toLocallyQuasicoherentModules B S hS p hp E h ⋙
      (Stack.isLocallyQuasicoherent.{u, u + 1, u, u} B E h S hS p hp).ι) :=
    preservesColimitsOfShape_toSiteModules B S hS p hp .etale K
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (Stack.isLocallyQuasicoherent.{u, u + 1, u, u} B E h S hS p hp).ι

/-- **Stacks 06WN (1).**  For a category fibred in groupoids `p : 𝒳 ⥤ (Sch/S)_fppf`, the
category `QCoh(𝒪_𝒳)` has colimits, and they agree with the colimits in `Mod(𝒪_𝒳)`, in
`Mod(𝒳_τ, 𝒪_𝒳)` for each of the coarser inherited topologies — in particular in
`Mod(𝒳_Zar, 𝒪_𝒳)` and `Mod(𝒳_étale, 𝒪_𝒳)` — and in `LQCoh(𝒪_𝒳)`: the inclusion into
`Mod(𝒪_𝒳)`, the reading functors into `Mod(𝒳_τ, 𝒪_𝒳)` and the inclusion into `LQCoh(𝒪_𝒳)`
preserve them.  Colimits are indexed by categories in the universe of the schemes. -/
@[stacks 06WN "(1): QCoh(O_X) has colimits and they agree with colimits in Mod(X_Zar, O_X), \
Mod(X_et, O_X), Mod(O_X) and LQCoh(O_X)"]
theorem quasicoherentModules_colimits_siteAgreement (E : BigEtaleSite.{u})
    (h : E.cutoff = B.cutoff) :
    HasColimitsOfSize.{u, u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) ∧
      PreservesColimitsOfSize.{u, u} (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι ∧
      (∀ τ : SiteKind,
        PreservesColimitsOfSize.{u, u} (toSiteModules.{u, u + 1, u, u} B S hS p hp τ)) ∧
      PreservesColimitsOfSize.{u, u} (toLocallyQuasicoherentModules B S hS p hp E h) :=
  ⟨hasColimitsOfSize_quasicoherentModules_of_isFiberedInGroupoids B S hS p hp,
    preservesColimitsOfSize_quasicoherentInclusion_of_isFiberedInGroupoids B S hS p hp,
    fun τ => ⟨fun {K} _ => preservesColimitsOfShape_toSiteModules B S hS p hp τ K⟩,
    ⟨fun {K} _ => preservesColimitsOfShape_toLocallyQuasicoherentModules B S hS p hp E h K⟩⟩

end Colimits

section FiniteLocallyFree

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **A quasi-coherent module which is finite locally free for the fppf topology is finite
locally free for each coarser inherited topology.**

Finite local freeness may be tested on the slices `𝒳_τ/x` at all objects.  At `x`, over the
scheme `U`, the restriction is the module `x^*𝓕` on `(Sch/U)_τ`, which is the reading for `τ` of
`x^*𝓕` on `(Sch/U)_fppf`; the latter is quasi-coherent (Stacks 06WI) and finite locally free, so
its reading is finite locally free by the parenthetical of Descent, Lemma 0GNE (3). -/
theorem isFiniteLocallyFreeOnSite_comparisonPushforward (τ : SiteKind)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) (hF : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      ((Stacks.SheafOfModules.comparisonPushforward.{u + 1, u, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
        (ringStructureSheafCore B S hS p hp .fppf)).obj M) := by
  refine (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite
    (ringedSite B S hS p hp τ) ((Stacks.SheafOfModules.comparisonPushforward.{u + 1, u, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
        (ringStructureSheafCore B S hS p hp .fppf)).obj M)).2
      ⟨ULift.{u + 1} 𝒳, fun i => i.down, Stacks.SheafOfModules.coversTop_ulift_self _,
        fun i => ?_⟩
  have hNq := (isQuasicoherentOnSite_iff_forall_objectInverseImageKind B S hS p hp .fppf M).1
    hM i.down
  have hNf : SheafOfModules.IsFiniteLocallyFreeOnSite
      (objectInverseImageKind B S hS p hp .fppf i.down M) := by
    refine (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff
      (J' := localizedTopologyKind B S hS p .fppf i.down)
      (localizationEquivalence B S hS p hp i.down)
      (baseRingStructureSheaf B (baseScheme B S hS p i.down)
        (contains_baseScheme B S hS p i.down) .fppf) _).1 ?_
    exact Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_iso
      ((localizationModulesEquivalenceKind B S hS p hp .fppf i.down).counitIso.app
        (M.over i.down)) (hF.over i.down)
  have hNτ := (BigFppfOver.isFiniteLocallyFreeOnSite_restrictTopology_iff B
    (baseScheme B S hS p i.down) (contains_baseScheme B S hS p i.down) τ _ hNq).1 hNf
  have h3 := (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff
      (J' := localizedTopologyKind B S hS p τ i.down)
      (localizationEquivalence B S hS p hp i.down)
      (baseRingStructureSheaf B (baseScheme B S hS p i.down)
        (contains_baseScheme B S hS p i.down) τ) _).2 hNτ
  exact Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_iso
    ((localizationModulesEquivalenceKind B S hS p hp τ i.down).counitIso.app _).symm h3

/-- **Finite local freeness of a quasi-coherent module on `𝒳` does not depend on the topology**:
it holds for the fppf topology exactly when it holds for any one of the coarser inherited
topologies, in particular the étale and the Zariski topology. -/
theorem isFiniteLocallyFreeOnSite_toSiteModules_iff (τ : SiteKind)
    (F : quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :
    SheafOfModules.IsFiniteLocallyFreeOnSite F.obj ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite ((toSiteModules B S hS p hp τ).obj F) :=
  ⟨isFiniteLocallyFreeOnSite_comparisonPushforward B S hS p hp τ F.obj F.property,
    Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS p τ) _ F.obj⟩

/-- The internal hom of two quasi-coherent modules computed in `Mod(𝒳_τ, 𝒪_𝒳)` is the internal
hom computed in `Mod(𝒪_𝒳)`, read for the inherited `τ`-topology.  The internal hom is a
construction on presheaves of modules, so the two are equal. -/
theorem internalHomSheaf_toSiteModules (τ : SiteKind)
    (F G : quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :
    (ringedSite B S hS p hp τ).internalHomSheaf ((toSiteModules B S hS p hp τ).obj F)
        ((toSiteModules B S hS p hp τ).obj G) =
      (Stacks.SheafOfModules.comparisonPushforward.{u + 1, u, u, u + 1}
        (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
        (ringStructureSheafCore B S hS p hp .fppf)).obj
        ((ringedSite B S hS p hp .fppf).internalHomSheaf F.obj G.obj) :=
  rfl

/-- **Stacks 06WN (3).**  Let `𝓕` and `𝓖` be quasi-coherent modules on a category fibred in
groupoids over `(Sch/S)_fppf`.  Then `𝓕` is finite locally free for the fppf topology if and only
if it is for the étale, and if and only if for the Zariski topology (indeed for each of the five
topologies); the internal homs `ℋom(𝓕, 𝓖)` computed in `Mod(𝒳_Zar, 𝒪_𝒳)`, `Mod(𝒳_étale, 𝒪_𝒳)`
and `Mod(𝒪_𝒳)` agree; and when `𝓕` is finite locally free for any one of these topologies the
common value is an object of `QCoh(𝒪_𝒳)`. -/
@[stacks 06WN "(3): for F, G in QCoh(O_X) the internal homs computed in Mod(X_Zar, O_X), \
Mod(X_et, O_X) and Mod(O_X) agree, F being finite locally free does not depend on the topology, \
and for F finite locally free the common value is quasi-coherent"]
theorem internalHomSheaf_quasicoherent_siteAgreement
    (F G : quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :
    (∀ τ : SiteKind, SheafOfModules.IsFiniteLocallyFreeOnSite F.obj ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite ((toSiteModules B S hS p hp τ).obj F)) ∧
    (∀ τ : SiteKind,
      (ringedSite B S hS p hp τ).internalHomSheaf ((toSiteModules B S hS p hp τ).obj F)
          ((toSiteModules B S hS p hp τ).obj G) =
        (Stacks.SheafOfModules.comparisonPushforward.{u + 1, u, u, u + 1}
          (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
          (ringStructureSheafCore B S hS p hp .fppf)).obj
          ((ringedSite B S hS p hp .fppf).internalHomSheaf F.obj G.obj)) ∧
    (∀ τ : SiteKind,
      SheafOfModules.IsFiniteLocallyFreeOnSite ((toSiteModules B S hS p hp τ).obj F) →
        ((ringedSite B S hS p hp .fppf).internalHomSheaf F.obj G.obj).IsQuasicoherentOnSite) :=
  ⟨fun τ => isFiniteLocallyFreeOnSite_toSiteModules_iff B S hS p hp τ F,
    fun τ => internalHomSheaf_toSiteModules B S hS p hp τ F G,
    fun τ hF => internalHomSheaf_isQuasicoherent B S hS p hp F G
      ((isFiniteLocallyFreeOnSite_toSiteModules_iff B S hS p hp τ F).2 hF)⟩

end FiniteLocallyFree

section Tensor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The tensor product of sheaves of modules on the associated `τ`-site of `𝒳`: the
sheafification of the objectwise tensor product of the underlying presheaves of modules. -/
noncomputable abbrev sheafTensor (τ : SiteKind) :
    SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ) ⥤
      SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ) ⥤
        SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ) :=
  letI := Stack.hasSheafify_associatedTopology_siteKind B S hS p hp τ
  letI := (haveI : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := essentiallySmall_over B S hS p hp
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over.{u}
      (BigFppfOver.associatedTopology B S hS p τ))
  Stacks.SheafOfModules.Tensor.sheafTensor.{v, w, u, u, u} (structureSheaf B S hS p hp τ)

/-- The tensor product of two quasi-coherent modules on `(𝒳_τ, 𝒪_𝒳)` is quasi-coherent; this is
Modules on Sites, Lemma 03L6, which holds on any ringed site. -/
theorem isQuasicoherentOnSite_sheafTensor (τ : SiteKind)
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ))
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) :
    (((sheafTensor B S hS p hp τ).obj F).obj G).IsQuasicoherentOnSite :=
  let := Stack.hasSheafify_associatedTopology_siteKind B S hS p hp τ
  let := wEqualsLocallyBijective_associatedTopology_of_isFiberedInGroupoids B S hS p hp τ
  @Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite _ _ _ _ _ _
    (structureSheaf B S hS p hp τ) F G hF hG

/-- **The tensor products computed for the fppf topology and for a coarser one agree.**  For two
quasi-coherent modules, the tensor product computed in `Mod(𝒪_𝒳)`, read for the inherited
`τ`-topology, is the tensor product of the two readings computed in `Mod(𝒳_τ, 𝒪_𝒳)`.

The fppf tensor product is the fppf sheafification of the `τ`-one, and the `τ`-one is already an
fppf sheaf: it is quasi-coherent for `τ`, and a module quasi-coherent for `τ` is an fppf sheaf by
Stacks 0EM8.  The isomorphism is the inverse of the unit of the sheafification adjunction. -/
noncomputable def sheafTensorSiteAgreement (τ : SiteKind)
    (F G : quasicoherentModules.{u, v, w, u} B S hS p hp) :
    (Stacks.SheafOfModules.comparisonPushforward.{v, w, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
        (ringStructureSheafCore B S hS p hp .fppf)).obj
        (((sheafTensor B S hS p hp .fppf).obj F.obj).obj G.obj) ≅
      ((sheafTensor B S hS p hp τ).obj ((toSiteModules B S hS p hp τ).obj F)).obj
        ((toSiteModules B S hS p hp τ).obj G) := by
  letI := Stack.hasSheafify_associatedTopology_siteKind B S hS p hp τ
  letI := (haveI : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := essentiallySmall_over B S hS p hp
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over.{u}
      (BigFppfOver.associatedTopology B S hS p τ))
  letI := Stack.hasSheafify_associatedTopology_siteKind B S hS p hp .fppf
  letI := (haveI : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := essentiallySmall_over B S hS p hp
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over.{u}
      (BigFppfOver.associatedTopology B S hS p .fppf))
  have hle := BigFppfOver.associatedTopology_le_fppf B S hS p τ
  refine Stacks.SheafOfModules.tensorLeftAgreement.{v, w, u, u} hle
    (structureSheaf B S hS p hp .fppf) F.obj G.obj ?_
  have hT := isQuasicoherentOnSite_sheafTensor B S hS p hp τ
    ((toSiteModules B S hS p hp τ).obj F) ((toSiteModules B S hS p hp τ).obj G)
    (quasicoherentOnSiteOfLeFppf_siteKind B S hS p hp τ F.obj F.property)
    (quasicoherentOnSiteOfLeFppf_siteKind B S hS p hp τ G.obj G.property)
  have hsh := isSheafFppfOfQuasicoherentOnSite_siteKind B S hS p hp τ _ hT
  exact (Stacks.SheafOfModules.comparisonAdjunction.{v, w, u, u} hle _
    ).isIso_unit_app_of_iso_rightObj
    (Stacks.SheafOfModules.comparisonPushforwardFullyFaithful.{v, w, u, u} hle _)
    (Y := ⟨_, hsh⟩) (Iso.refl _)

/-- **Stacks 06WN (2).**  For quasi-coherent modules `𝓕` and `𝓖` on a category fibred in
groupoids over `(Sch/S)_fppf`, the tensor products `𝓕 ⊗ 𝓖` computed in `Mod(𝒳_Zar, 𝒪_𝒳)`,
`Mod(𝒳_étale, 𝒪_𝒳)` and `Mod(𝒪_𝒳)` agree — the one computed in `Mod(𝒪_𝒳)`, read for each coarser
topology, is the one computed for that topology — and the common value is an object of
`QCoh(𝒪_𝒳)`; it is moreover quasi-coherent on each of the coarser sites. -/
@[stacks 06WN "(2): for F, G in QCoh(O_X) the tensor products computed in Mod(X_Zar, O_X), \
Mod(X_et, O_X) and Mod(O_X) agree and the common value is quasi-coherent"]
theorem sheafTensor_quasicoherent_siteAgreement
    (F G : quasicoherentModules.{u, v, w, u} B S hS p hp) :
    (∀ τ : SiteKind, Nonempty ((Stacks.SheafOfModules.comparisonPushforward.{v, w, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
        (ringStructureSheafCore B S hS p hp .fppf)).obj
        (((sheafTensor B S hS p hp .fppf).obj F.obj).obj G.obj) ≅
      ((sheafTensor B S hS p hp τ).obj ((toSiteModules B S hS p hp τ).obj F)).obj
        ((toSiteModules B S hS p hp τ).obj G))) ∧
    (((sheafTensor B S hS p hp .fppf).obj F.obj).obj G.obj).IsQuasicoherentOnSite ∧
    (∀ τ : SiteKind, (((sheafTensor B S hS p hp τ).obj
      ((toSiteModules B S hS p hp τ).obj F)).obj
        ((toSiteModules B S hS p hp τ).obj G)).IsQuasicoherentOnSite) :=
  ⟨fun τ => ⟨sheafTensorSiteAgreement B S hS p hp τ F G⟩,
    isQuasicoherentOnSite_sheafTensor B S hS p hp .fppf F.obj G.obj F.property G.property,
    fun τ => isQuasicoherentOnSite_sheafTensor B S hS p hp τ _ _
      (quasicoherentOnSiteOfLeFppf_siteKind B S hS p hp τ F.obj F.property)
      (quasicoherentOnSiteOfLeFppf_siteKind B S hS p hp τ G.obj G.property)⟩

end Tensor

end AlgebraicGeometry.FibredSite
