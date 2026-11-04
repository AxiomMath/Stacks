module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSectionsComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.QuasiCoherentAffineAcyclicity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverSliceContinuity
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EnoughPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct images of a quasi-coherent module from the big fppf site

Let `S` be a scheme contained in a chosen big fppf site `B`, and let `𝓕` be a quasi-coherent
`𝒪_S`-module.  The three comparisons of Stacks 0DEV all live on the *one* category
`(Sch/S) = BigFppfOver B S hS`: the five topologies of `AlgebraicGeometry.SiteKind` are put on
it by `AlgebraicGeometry.BigFppfOver.baseOverTopology`, and the small étale site of `S` is the
full subcategory of its étale objects, by way of the big étale site
`AlgebraicGeometry.BigFppfSite.toBigEtaleSite` that `B` carries (Stacks 03FF), whose cutoff and
covering bound are `B`'s own.  So

* `ε_S : (Sch/S)_fppf ⟶ (Sch/S)_τ` is the identity functor, continuous because the `τ`-topology
  is coarser than the fppf one, and
* `a_S : (Sch/S)_fppf ⟶ S_étale` is the inclusion of the small étale site.

Clauses (6) and (7) of Stacks 0DEW are proved here, and Stacks 0DEX with them.  For clause (6)
the direct image is restriction of sections along the functor, and `𝓕ᵃ` on each of the sites is
the *same* presheaf of modules `(f : T → S) ↦ Γ(T, f⁺𝓕)` of Stacks 03DS restricted along the
presenting functor, so both identifications hold by `rfl`.  Clause (7) is the module-valued
covering criterion
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve` fed by
the affine objects: every object of either site is covered by objects whose total space is
affine, and over such an object the fppf cohomology of `𝓕ᵃ` vanishes in positive degrees by
[Stacks, Tag 03P2].  Stacks 0DEX is then the criterion of [Stacks, Tag 015C]: the two canonical
maps are isomorphisms exactly because the higher direct images vanish and the direct images are
left exact.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseAssociatedSheaf`: `𝓕ᵃ` on `(Sch/S)_τ`.
* `AlgebraicGeometry.BigFppfOver.smallEtaleAssociatedSheaf`: `𝓕ᵃ` on `S_étale`.
* `AlgebraicGeometry.BigFppfOver.epsilonPushforward` and
  `AlgebraicGeometry.BigFppfOver.aPushforward`: the direct images `ε_{S,*}` and `a_{S,*}` of
  sheaves of modules.
* `AlgebraicGeometry.BigFppfOver.smallEtaleToFppf`: the functor `a_S`, with its target ascribed
  as the big fppf category over `S`.
* `AlgebraicGeometry.BigFppfOver.affineOverPresieve` and
  `AlgebraicGeometry.BigFppfOver.smallEtaleAffinePresieve`: the arrows out of the affine objects
  of either site.

## Main results

* `AlgebraicGeometry.BigFppfOver.pushforward_baseAssociatedSheaf`: **Stacks 0DEW, clause (6),
  first half** — `ε_{S,*}𝓕ᵃ = 𝓕ᵃ`, that is `ε_{S,*}a_S^*𝓕 = π_S^*𝓕` at `τ = étale`.
* `AlgebraicGeometry.BigFppfOver.pushforward_smallEtaleAssociatedSheaf`: **Stacks 0DEW, clause
  (6), second half** — `a_{S,*}𝓕ᵃ = 𝓕`, that is `a_{S,*}a_S^*𝓕 = 𝓕`.
* `AlgebraicGeometry.BigFppfOver.isZero_rightDerived_epsilonPushforward` and
  `AlgebraicGeometry.BigFppfOver.isZero_rightDerived_aPushforward`: **Stacks 0DEW, clause (7)** —
  `R^p ε_{S,*}(a_S^*𝓕) = 0` and `R^p a_{S,*}(a_S^*𝓕) = 0` for `p > 0`.
* `AlgebraicGeometry.BigFppfOver.rightAcyclic_epsilonPushforward` and
  `AlgebraicGeometry.BigFppfOver.rightAcyclic_aPushforward`: **Stacks 0DEX** —
  `π_S^*𝓕 ⟶ Rε_{S,*}(a_S^*𝓕)` and `𝓕 ⟶ Ra_{S,*}(a_S^*𝓕)` are isomorphisms.
* `AlgebraicGeometry.BigFppfOver.generate_affineOverPresieve_mem` and
  `AlgebraicGeometry.BigFppfOver.generate_smallEtaleAffinePresieve_mem`: the affine objects of
  the big site resp. of the small étale site cover every object.
* `AlgebraicGeometry.Functor.isContinuous_of_le` and
  `AlgebraicGeometry.Functor.isContinuous_of_le_target`: continuity of a functor of sites is
  antitone in the topology of its source and monotone in that of its target.
* `AlgebraicGeometry.bigEtaleOver_topology_le_fppf`: the localized big étale topology carried by
  a big fppf site is coarser than the localized fppf topology.

## Implementation notes

**What `𝓕ᵃ` is here.**  It is `AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`, the
presheaf of modules of Stacks 03DS over the structure presheaf of global functions, together
with the sheaf condition Stacks 03DT, which is available for all five localized topologies at
once (`isSheaf_sectionsPresheafOfModules_baseOverTopology`) and on the small étale site
(`AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules`).  No sheafification occurs,
so the sections over an object are exactly `Γ(T, f⁺𝓕)`.  This is the description of `𝓕ᵃ` that
the source's proof of clause (6) appeals to: "Part (6) is immediate from the description of the
sheaf `𝓕ᵃ = π_S^*𝓕 = a_S^*𝓕`", the two identifications being clauses (2) and (3) of the same
lemma.  Its identification with the pullback `SheafOfModules.pullback` along the morphism of
ringed sites to `S_Zar` — the spelling `AlgebraicGeometry.BigFppfOver.baseAssociatedModule` of
clauses (4) and (5) — is `AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app` together with
`AlgebraicGeometry.BigFppfOver.isIso_baseSheafification_map_sectionsComparison`, and is not
reproved here.

**Why the second half is the statement `a_{S,*}𝓕ᵃ = 𝓕`.**  The source's `𝓕` is a quasi-coherent
module on `S_étale`, and the first paragraph of its proof replaces it by `𝓕_0ᵃ` for a
quasi-coherent module `𝓕_0` on the scheme `S`, which is legitimate by Descent, Proposition
03DX.  That replacement is made here as well: the `𝓕` of this file is a quasi-coherent module on
the scheme `S` and the right-hand side of the second half is its associated module on `S_étale`.
The library carries 03DX for the small étale site only over essential surjectivity of
`𝓕 ↦ 𝓕ᵃ` (`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`), as the
clauses (4) and (5) in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/QuasiCoherentSmallEtaleBigSite.lean` do.

**The carried hypothesis.**  Clause (7) and 0DEX carry
`[EnoughInjectives (SheafOfModules.{u} 𝒪_fppf)]`.  Without it the right derived functors of
`ε_{S,*}` and `a_{S,*}` are not defined, so this is a well-formedness condition on the
statement rather than a weakening of it; the same hypothesis is carried for the same reason by
`AlgebraicGeometry.bigFppfHigherDirectImage_isParasitic` and its four siblings.  The library
proves enough injectives for sheaves of modules only when the module universe dominates the
objects of the site (`SheafOfModules.enoughInjectives_of_univLE`), whereas the big sites of
schemes carry modules one universe *below* their objects.

**The two continuity lemmas.**  Mathlib's `CategoryTheory.Functor.IsContinuous` is the condition
that restriction along the functor carries sheaves of types to sheaves of types; a sheaf for a
finer topology is a sheaf for a coarser one, which makes the condition antitone in the source
topology and monotone in the target.  Neither direction is in Mathlib and both are needed: the
first makes the identity functor continuous from the `τ`-topology to the fppf one, the second
upgrades the continuity of the small-étale inclusion (Stacks 021G, which lands in the big
*étale* topology) to the fppf topology.

**The topology comparison.**  `AlgebraicGeometry.BigFppfSite.toBigEtaleSite_topology` identifies
the topology of the big étale site carried by `B` with the big étale topology of Stacks 03FF on
`B`'s own category, which is the `τ = étale` member of
`AlgebraicGeometry.BigFppfOver.baseOverTopology`; `baseOverTopology_le_fppf` then supplies the
comparison with the fppf topology.

**Two presentations of one category.**  `BigEtaleOver B.toBigEtaleSite S hS` and
`BigFppfOver B S hS` are the same category, but `toBigEtaleSite` is a definition and instance
search does not unfold it, so a hypothesis stated for one presentation is invisible for the
other.  `smallEtaleToFppf` ascribes the target of `a_S` once and for all, which is what lets the
covering criterion be applied to it; the three instances
`isContinuous_smallEtaleInclusion_fppf`, `hasSheafify_smallEtaleOfBigFppf` and
`wEqualsLocallyBijective_smallEtaleOfBigFppf` restate library instances in the fppf
presentation for the same reason, and `additive_aPushforward` is
`CategoryTheory.SheafOfModules.pushforward_additive` there.

**Where the affine vanishing is converted.**  `isZero_sheafCohomology_baseAssociatedSheaf_affine`
is the one place where the two spellings of the abelian sheaf `𝓕ᵃ` — the one of this file and
the restriction of `AlgebraicGeometry.fpqcOverAssociatedSheaf` used by the Čech comparison — are
identified.  The identification is made at the level of the *sheaf*, by `rfl`, and then rewritten
into the cohomology; comparing the two `CategoryTheory.Sheaf.H'` terms directly exhausts the
elaborator, since it unfolds `CategoryTheory.Abelian.Ext` and with it the `Shrink` instances.

## References

* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
* [Stacks Project, Tag 0DEX](https://stacks.math.columbia.edu/tag/0DEX)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 021G](https://stacks.math.columbia.edu/tag/021G)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.ModuleDirectImageOnACover

universe u

namespace AlgebraicGeometry

/-- **Continuity of a functor of sites is antitone in the topology of its source.**  A sheaf of
types for the finer topology on the target restricts to a sheaf for the finer topology on the
source, hence to one for any coarser topology there. -/
public theorem Functor.isContinuous_of_le {C : Type*} [Category* C] {D : Type*} [Category* D]
    (G : C ⥤ D) {J J' : GrothendieckTopology C} (K : GrothendieckTopology D) (hJ : J ≤ J')
    [G.IsContinuous J' K] : G.IsContinuous J K :=
  ⟨fun F _ _ hS => CategoryTheory.Functor.IsContinuous.op_comp_isSheaf_of_types F _ (hJ _ hS)⟩

/-- **Continuity of a functor of sites is monotone in the topology of its target.**  A sheaf of
types for a finer topology on the target is one for the coarser topology it is continuous
against, so its restriction is still a sheaf on the source. -/
public theorem Functor.isContinuous_of_le_target {C : Type*} [Category* C] {D : Type*}
    [Category* D] (G : C ⥤ D) (J : GrothendieckTopology C) {K K' : GrothendieckTopology D}
    (hK : K ≤ K') [G.IsContinuous J K] : G.IsContinuous J K' :=
  ⟨fun F => CategoryTheory.Functor.IsContinuous.op_comp_isSheaf_of_types (J := J) (K := K)
    ⟨F.obj, F.property.of_le hK⟩⟩

/-- **The big étale topology carried by a big fppf site is coarser than its fppf topology.**
The two live on the one category of Stacks 03FF, and the chosen étale covering families are
chosen fppf covering families. -/
public theorem BigFppfSite.toBigEtaleSite_topology_le (B : BigFppfSite.{u}) :
    B.toBigEtaleSite.topology ≤ B.topology := by
  rw [B.toBigEtaleSite_topology]
  exact B.baseTopology_le_topology .etale

/-- **The localized big étale topology carried by a big fppf site is coarser than the localized
fppf topology.**  The big étale site of Stacks 03FF has `B`'s own category, and its covering
families are those chosen by `B` which are étale coverings. -/
public theorem bigEtaleOver_topology_le_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    BigEtaleOver.topology B.toBigEtaleSite S hS ≤ BigFppfOver.baseOverTopology B S hS .fppf :=
  (bigEtaleOver_topology_eq B.toBigEtaleSite S hS).le.trans
    (Stacks.Sites.over_mono B.toBigEtaleSite_topology_le _)

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : S.Modules) [F.IsQuasicoherent]

/-! ### The change of topology `ε_S` -/

/-- **`𝓕ᵃ` on the big site `(Sch/S)_τ`**: the pullback-sections presheaf of modules of
Stacks 03DS, which is a sheaf for each of the five localized topologies (Stacks 03DT) and has
the same sections and the same restriction maps for all of them. -/
public def baseAssociatedSheaf (τ : SiteKind) :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) :=
  ⟨sectionsPresheafOfModules B S hS F,
    isSheaf_sectionsPresheafOfModules_baseOverTopology B S hS τ F⟩

/-- The identity functor is continuous from each of the five localized topologies to the
localized fppf topology, the former being coarser. -/
public instance isContinuous_id_baseOverTopology (τ : SiteKind) :
    (𝟭 (BigFppfOver B S hS)).IsContinuous (baseOverTopology B S hS τ)
      (baseOverTopology B S hS .fppf) :=
  Functor.isContinuous_of_le (J' := baseOverTopology B S hS .fppf) _ _
    (baseOverTopology_le_fppf B S hS τ)

/-- The structure-sheaf comparison of the change of topology
`ε_S : ((Sch/S)_fppf, 𝒪) ⟶ ((Sch/S)_τ, 𝒪)`: the identity, since the two structure sheaves have
the same underlying presheaf of global functions. -/
public def epsilonStructureMap (τ : SiteKind) :
    FibredSite.baseRingStructureSheaf B S hS τ ⟶
      ((𝟭 (BigFppfOver B S hS)).sheafPushforwardContinuous RingCat.{u}
        (baseOverTopology B S hS τ) (baseOverTopology B S hS .fppf)).obj
          (FibredSite.baseRingStructureSheaf B S hS .fppf) :=
  𝟙 _

/-- **The direct image `ε_{S,*}`** of sheaves of modules along the change of topology from the
big fppf site of `S` to the big `τ`-site: restriction of sections along the identity functor. -/
public abbrev epsilonPushforward (τ : SiteKind) :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS .fppf) ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) :=
  SheafOfModules.pushforward (epsilonStructureMap B S hS τ)

/-- **Stacks 0DEW, clause (6), first half.**  The direct image along
`ε_S : ((Sch/S)_fppf, 𝒪) ⟶ ((Sch/S)_τ, 𝒪)` of the associated module `𝓕ᵃ = a_S^*𝓕` is the
associated module `𝓕ᵃ = π_S^*𝓕` of the big `τ`-site; at `τ = étale` this is
`ε_{S,*}a_S^*𝓕 = π_S^*𝓕`.

Both sides are the presheaf `(f : T → S) ↦ Γ(T, f⁺𝓕)` of Stacks 03DS with its two sheaf
conditions, and the direct image along the identity functor is restriction of sections along
it. -/
@[stacks 0DEW "clause (6), first half, as documented above"]
public theorem pushforward_baseAssociatedSheaf (τ : SiteKind) :
    (epsilonPushforward B S hS τ).obj (baseAssociatedSheaf B S hS F .fppf) =
      baseAssociatedSheaf B S hS F τ :=
  rfl

/-! ### The comparison `a_S` with the small étale site -/

/-- **The functor `a_S`**: the inclusion of the small étale site of `S` into the big fppf
category over `S`.  The ascription of the target is what makes the two presentations of that
category — as the big étale category over `S` for the big étale site carried by `B`, and as the
big fppf category over `S` — the same for instance search. -/
public abbrev smallEtaleToFppf : SmallEtale B.toBigEtaleSite S hS ⥤ BigFppfOver B S hS :=
  SmallEtale.inclusion B.toBigEtaleSite S hS

/-- The inclusion of the small étale site of `S` into the big fppf site of `S` is continuous:
Stacks 021G makes it continuous into the big étale topology, which is coarser than the fppf
one. -/
public instance isContinuous_smallEtaleInclusion_fppf :
    (smallEtaleToFppf B S hS).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS) (baseOverTopology B S hS .fppf) :=
  have _h0 : (smallEtaleToFppf B S hS).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS)
      (BigEtaleOver.topology B.toBigEtaleSite S hS) :=
    (smallEtaleInclusion_isMorphismOfSites B.toBigEtaleSite S hS).toIsContinuous
  Functor.isContinuous_of_le_target _ _ (bigEtaleOver_topology_le_fppf B S hS)

/-- The structure-sheaf comparison of `a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪_S)`: the identity,
the structure sheaf of the small étale site being the restriction of that of the big fppf
site. -/
public def aStructureMap :
    SmallEtale.structureSheaf B.toBigEtaleSite S hS ⟶
      ((smallEtaleToFppf B S hS).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B.toBigEtaleSite S hS) (baseOverTopology B S hS .fppf)).obj
          (FibredSite.baseRingStructureSheaf B S hS .fppf) :=
  𝟙 _

/-- **`𝓕ᵃ` on the small étale site of `S`**: the same pullback-sections presheaf of modules of
Stacks 03DS, restricted to the small étale site, with the sheaf condition of Stacks 03DT
there. -/
public def smallEtaleAssociatedSheaf :
    SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS) :=
  ⟨SmallEtale.sectionsPresheafOfModules B.toBigEtaleSite S hS F,
    SmallEtale.isSheaf_sectionsPresheafOfModules B.toBigEtaleSite S hS F⟩

/-- **The direct image `a_{S,*}`** of sheaves of modules from the big fppf site of `S` to the
small étale site: restriction of sections along the inclusion. -/
public abbrev aPushforward :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS .fppf) ⥤
      SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS) :=
  SheafOfModules.pushforward (F := smallEtaleToFppf B S hS)
    (aStructureMap B S hS)

/-- **Stacks 0DEW, clause (6), second half.**  The direct image along
`a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪_S)` of the associated module `𝓕ᵃ = a_S^*𝓕` is `𝓕`
itself, read on the small étale site as its own associated module: `a_{S,*}a_S^*𝓕 = 𝓕`.

Both sides are the presheaf `(f : T → S) ↦ Γ(T, f⁺𝓕)` of Stacks 03DS, the right-hand side
restricted along the inclusion of the small étale site, and the direct image is exactly that
restriction. -/
@[stacks 0DEW "clause (6), second half, as documented above"]
public theorem pushforward_smallEtaleAssociatedSheaf :
    (aPushforward B S hS).obj (baseAssociatedSheaf B S hS F .fppf) =
      smallEtaleAssociatedSheaf B S hS F :=
  rfl

/-! ### Higher direct images -/

-- A localized big site is essentially small at the universe of its morphisms, so these two
-- supply its `Ext` universe and enough injectives; without them the affine acyclicity used
-- below does not even elaborate.
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

/-- **The localized big étale topology carried by a big fppf site is the étale member of the
family `baseOverTopology`.** -/
public theorem bigEtaleOver_topology_le_baseOverTopology :
    BigEtaleOver.topology B.toBigEtaleSite S hS ≤ baseOverTopology B S hS .etale :=
  le_trans (le_of_eq (bigEtaleOver_topology_eq B.toBigEtaleSite S hS))
    (Stacks.Sites.over_mono (le_of_eq B.toBigEtaleSite_topology) _)

/-- The presieve of all arrows into an object of the big site whose source has affine total
space. -/
public def affineOverPresieve (V : BigFppfOver B S hS) : Presieve V :=
  fun {W} _ => IsAffineOver B S hS W

/-- **Every object of the big site is covered, étale-locally, by objects with affine total
space.**  The big affine étale site is a dense subsite of the big étale site (Stacks 021E), so
the sieve of arrows factoring through an affine object is covering; every such arrow factors
through an arrow out of an affine object. -/
public theorem generate_affineOverPresieve_mem (V : BigFppfOver B S hS) :
    Sieve.generate (affineOverPresieve B S hS V) ∈ baseOverTopology B S hS .etale V := by
  have hsub := (BigAffineEtale.inclusion_isSpecialCocontinuous B.toBigEtaleSite S hS).2
  have hcd := Functor.IsDenseSubsite.isCoverDense
    (BigAffineEtale.topology B.toBigEtaleSite S hS)
    (BigEtaleOver.topology B.toBigEtaleSite S hS)
    (BigAffineEtale.inclusion B.toBigEtaleSite S hS)
  refine bigEtaleOver_topology_le_baseOverTopology B S hS _
    (GrothendieckTopology.superset_covering _ ?_ (hcd.is_cover V))
  rintro X f ⟨⟨Z, lift, map, fac⟩⟩
  exact ⟨_, lift, map, Z.property, fac⟩

variable [EnoughInjectives
  (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS .fppf))]

omit [EnoughInjectives
  (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS .fppf))] in
/-- **The higher fppf cohomology of `𝓕ᵃ` vanishes at an object with affine total space.**  This
is [Stacks, Tag 03P2] at an affine object,
`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`, read for the module `𝓕ᵃ` of this
file: the two abelian sheaves are the same restriction of the presheaf of Stacks 03DS along the
same functor. -/
public theorem isZero_sheafCohomology_baseAssociatedSheaf_affine
    (W : BigFppfOver B S hS) (hW : IsAffineOver B S hS W) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf
        (FibredSite.baseRingStructureSheaf B S hS .fppf)).obj
      (baseAssociatedSheaf B S hS F .fppf)) p W) := by
  have : (overToSlice CoveringTopology.fppf B S hS).IsContinuous
      (overTopology CoveringTopology.fppf B S hS) (Scheme.fpqcTopology.{u}.over S) :=
    isContinuous_overToSlice_fpqc CoveringTopology.fppf B S hS
  have hX : (SheafOfModules.toSheaf
        (FibredSite.baseRingStructureSheaf B S hS .fppf)).obj
        (baseAssociatedSheaf B S hS F .fppf) =
      ((overToSlice CoveringTopology.fppf B S hS).sheafPushforwardContinuous AddCommGrpCat.{u}
        (overTopology CoveringTopology.fppf B S hS) (Scheme.fpqcTopology.{u}.over S)).obj
          (fpqcOverAssociatedSheaf S F) := rfl
  rw [hX]
  exact isZero_sheafCohomology_succ_overAffine S F .fppf B hS W hW p hp

omit [EnoughInjectives
  (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS .fppf))] in
/-- `Ext` for abelian sheaves on one of the five localized topologies, at the universe of the
morphisms of the sheaf category.  This is the universe the comparison of [Stacks, Tag 03FD] for
a site whose objects live above its morphisms measures at. -/
public theorem hasExt_sheaf_baseOverTopology (τ : SiteKind) :
    HasExt.{u + 1} (Sheaf (baseOverTopology B S hS τ) AddCommGrpCat.{u}) :=
  hasExt_morphismUniverse _

/-- `Ext` for sheaves of modules on the big fppf site of `S`, at the universe of the morphisms
of that category. -/
public theorem hasExt_sheafOfModules_fppf :
    HasExt.{u + 1} (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS .fppf)) :=
  hasExt_morphismUniverse _

/-- Evaluating the right derived functors of sections at an object with affine total space gives
zero in positive degrees on `𝓕ᵃ`. -/
private theorem isZero_rightDerived_evaluation_baseAssociatedSheaf_affine
    [HasExt.{u + 1} (Sheaf (baseOverTopology B S hS .fppf) AddCommGrpCat.{u})]
    [HasExt.{u + 1} (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS .fppf))]
    (W : BigFppfOver B S hS) (hW : IsAffineOver B S hS W) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation (FibredSite.baseRingStructureSheaf B S hS .fppf)
      (op W)).rightDerived p).obj (baseAssociatedSheaf B S hS F .fppf)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{u + 1, u, u} _ _ W q _
    (isZero_sheafCohomology_baseAssociatedSheaf_affine B S hS F W hW (q + 1) (by omega))

attribute [local instance] hasExt_sheaf_baseOverTopology hasExt_sheafOfModules_fppf in
/-- **Stacks 0DEW, clause (7), first half.**  The higher direct images along
`ε_S : ((Sch/S)_fppf, 𝒪) ⟶ ((Sch/S)_étale, 𝒪)` of the associated module `𝓕ᵃ = a_S^*𝓕` vanish:
`R^p ε_{S,*}(a_S^*𝓕) = 0` for `p > 0`.

Every object of the big site is covered étale-locally by objects with affine total space, and
there the fppf cohomology of `𝓕ᵃ` vanishes in positive degrees by [Stacks, Tag 03P2]; so the
module-valued criterion
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`
applies. -/
@[stacks 0DEW "clause (7), first half, as documented above"]
public theorem isZero_rightDerived_epsilonPushforward (p : ℕ) (hp : 0 < p) :
    IsZero (((epsilonPushforward B S hS .etale).rightDerived p).obj
      (baseAssociatedSheaf B S hS F .fppf)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  refine isZero_rightDerived_pushforward_of_presieve.{u, u + 1, u, u + 1, u, u}
    (𝟭 (BigFppfOver B S hS)) _ _ (epsilonStructureMap B S hS .etale) (q + 1) _ (fun V ↦ ?_)
  refine ⟨affineOverPresieve B S hS V, generate_affineOverPresieve_mem B S hS V,
    fun W g hg ↦ ?_⟩
  exact isZero_rightDerived_evaluation_baseAssociatedSheaf_affine B S hS F W hg (q + 1) (by omega)

/-- Abelian presheaves on the small étale site of `S` sheafify.  This is
`AlgebraicGeometry.SmallEtale.hasSheafify_smallEtale` for the big étale site carried by `B`,
restated so that instance search sees the size hypothesis in the form `B.Contains S`. -/
public instance hasSheafify_smallEtaleOfBigFppf :
    HasSheafify (SmallEtale.topology B.toBigEtaleSite S hS) AddCommGrpCat.{u} :=
  SmallEtale.hasSheafify_smallEtale B.toBigEtaleSite S hS

/-- Weak equivalences of abelian presheaves on the small étale site of `S` are the locally
bijective maps, restated for the big étale site carried by `B`. -/
public instance wEqualsLocallyBijective_smallEtaleOfBigFppf :
    (SmallEtale.topology B.toBigEtaleSite S hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  SmallEtale.wEqualsLocallyBijective_smallEtale B.toBigEtaleSite S hS

/-- The direct image `a_{S,*}` is additive: it does not change the underlying presheaf, and
addition of morphisms of sheaves of modules is sectionwise. -/
public instance additive_aPushforward : (aPushforward B S hS).Additive where
  map_add := by intros; rfl

/-- The presieve of all arrows into an object of the small étale site whose source is affine. -/
public def smallEtaleAffinePresieve (V : SmallEtale B.toBigEtaleSite S hS) : Presieve V :=
  fun {W} _ => SmallEtale.IsAffine B.toBigEtaleSite S hS W

omit [EnoughInjectives
  (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS .fppf))] in
/-- **Every object of the small étale site is covered by its affine objects** (Stacks 04HR). -/
public theorem generate_smallEtaleAffinePresieve_mem (V : SmallEtale B.toBigEtaleSite S hS) :
    Sieve.generate (smallEtaleAffinePresieve B S hS V) ∈
      SmallEtale.topology B.toBigEtaleSite S hS V := by
  have hsub := (SmallAffineEtale.inclusion_isSpecialCocontinuous B.toBigEtaleSite S hS).2
  have hcd := Functor.IsDenseSubsite.isCoverDense
    (SmallAffineEtale.topology B.toBigEtaleSite S hS)
    (SmallEtale.topology B.toBigEtaleSite S hS)
    (SmallAffineEtale.inclusion B.toBigEtaleSite S hS)
  refine GrothendieckTopology.superset_covering _ ?_ (hcd.is_cover V)
  rintro X f ⟨⟨Z, lift, map, fac⟩⟩
  exact ⟨_, lift, map, Z.property, fac⟩

attribute [local instance] hasExt_sheaf_baseOverTopology hasExt_sheafOfModules_fppf in
/-- **Stacks 0DEW, clause (7), second half.**  The higher direct images along
`a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪_S)` of the associated module `𝓕ᵃ = a_S^*𝓕` vanish:
`R^p a_{S,*}(a_S^*𝓕) = 0` for `p > 0`.

Every object of the small étale site is covered by its affine objects (Stacks 04HR), and over an
object of the big site with affine total space the fppf cohomology of `𝓕ᵃ` vanishes in positive
degrees by [Stacks, Tag 03P2]. -/
@[stacks 0DEW "clause (7), second half, as documented above"]
public theorem isZero_rightDerived_aPushforward (p : ℕ) (hp : 0 < p) :
    IsZero (((aPushforward B S hS).rightDerived p).obj
      (baseAssociatedSheaf B S hS F .fppf)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hsh : HasSheafify (baseOverTopology B S hS .fppf) AddCommGrpCat.{u} :=
    hasSheafify_baseOverTopology B S hS .fppf
  have hsh' : HasSheafify (SmallEtale.topology B.toBigEtaleSite S hS) AddCommGrpCat.{u} :=
    hasSheafify_smallEtaleOfBigFppf B S hS
  refine isZero_rightDerived_pushforward_of_presieve.{u, u + 1, u, u + 1, u, u}
    (smallEtaleToFppf B S hS)
    (FibredSite.baseRingStructureSheaf B S hS .fppf)
    (SmallEtale.structureSheaf B.toBigEtaleSite S hS)
    (aStructureMap B S hS) (q + 1) _ (fun V ↦ ?_)
  refine ⟨smallEtaleAffinePresieve B S hS V, generate_smallEtaleAffinePresieve_mem B S hS V,
    fun W g hg ↦ ?_⟩
  exact isZero_rightDerived_evaluation_baseAssociatedSheaf_affine B S hS F
    ((smallEtaleToFppf B S hS).obj W) hg (q + 1) (by omega)

/-! ### The derived direct images: Stacks 0DEX -/

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] hasExt_sheaf_baseOverTopology hasExt_sheafOfModules_fppf in
/-- **Stacks 0DEX, first half.**  The canonical map
`π_S^*𝓕 = ε_{S,*}(a_S^*𝓕) ⟶ Rε_{S,*}(a_S^*𝓕)` is an isomorphism, that is, `a_S^*𝓕` is right
acyclic for `ε_{S,*}`.

This is the criterion of [Stacks, Tag 015C] applied to clauses (6) and (7) of
[Stacks, Tag 0DEW]: clause (6) identifies the source of the map with `π_S^*𝓕`
(`pushforward_baseAssociatedSheaf`, an equality), and clause (7) supplies the vanishing of the
higher direct images, which is what right acyclicity amounts to for a left exact functor. -/
@[stacks 0DEX "first half, as documented above"]
public theorem rightAcyclic_epsilonPushforward :
    (SheafOfModules.pushforward (F := 𝟭 (BigFppfOver B S hS))
        (epsilonStructureMap B S hS .etale)).rightAcyclic
      (baseAssociatedSheaf B S hS F .fppf) := by
  refine rightAcyclic_pushforward_of_presieve.{u, u + 1, u, u + 1, u, u, u + 1, u + 1}
    (𝟭 (BigFppfOver B S hS)) (FibredSite.baseRingStructureSheaf B S hS .fppf)
    (FibredSite.baseRingStructureSheaf B S hS .etale) (epsilonStructureMap B S hS .etale) _
    (fun p hp V ↦ ?_)
  refine ⟨affineOverPresieve B S hS V, generate_affineOverPresieve_mem B S hS V,
    fun W g hg ↦ ?_⟩
  exact isZero_rightDerived_evaluation_baseAssociatedSheaf_affine B S hS F W hg p hp

attribute [local instance] hasExt_sheaf_baseOverTopology hasExt_sheafOfModules_fppf in
/-- **Stacks 0DEX, second half.**  The canonical map
`𝓕 = a_{S,*}(a_S^*𝓕) ⟶ Ra_{S,*}(a_S^*𝓕)` is an isomorphism, that is, `a_S^*𝓕` is right acyclic
for `a_{S,*}`.

Clause (6) of [Stacks, Tag 0DEW] identifies the source of the map with `𝓕` itself
(`pushforward_smallEtaleAssociatedSheaf`, an equality), and clause (7) supplies the vanishing of
the higher direct images. -/
@[stacks 0DEX "second half, as documented above"]
public theorem rightAcyclic_aPushforward :
    (SheafOfModules.pushforward (F := smallEtaleToFppf B S hS)
        (aStructureMap B S hS)).rightAcyclic
      (baseAssociatedSheaf B S hS F .fppf) := by
  refine rightAcyclic_pushforward_of_presieve.{u, u + 1, u, u + 1, u, u, u + 1, u + 1}
    (smallEtaleToFppf B S hS) (FibredSite.baseRingStructureSheaf B S hS .fppf)
    (SmallEtale.structureSheaf B.toBigEtaleSite S hS) (aStructureMap B S hS) _
    (fun p hp V ↦ ?_)
  refine ⟨smallEtaleAffinePresieve B S hS V, generate_smallEtaleAffinePresieve_mem B S hS V,
    fun W g hg ↦ ?_⟩
  exact isZero_rightDerived_evaluation_baseAssociatedSheaf_affine B S hS F
    ((smallEtaleToFppf B S hS).obj W) hg p hp

end BigFppfOver

end AlgebraicGeometry

end
