module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiChartSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiLiftedSliceDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiProjection

/-!
# The affine opens of `S` inside `(Aff/S)`

Let `S` be a scheme in a big fppf site `B`, and let `(Aff/S) = (Sch/S)_{affine}` be the affine
subcategory of the big fppf category of `S` (Stacks 0H0A for the identity of `(Sch/S)_{fppf}`).
An affine open subscheme of `S` is an affine scheme over `S`, so the small affine Zariski site of
`S` is a full subcategory of `(Aff/S)`; this file constructs the inclusion
`AlgebraicGeometry.ZariskiCharts.affineOpensInclusion` and shows that it is continuous,
cocontinuous and a morphism of sites for the Zariski topologies, at every universe of sheaves of
sets above that of the schemes.

The site condition is deduced as in the proof of Stacks 0H0K: followed by the dense subsite
inclusion `(Aff/S) ⥤ (Sch/S)` of Stacks 0H0B, the functor is the composite of the dense subsite
inclusion of the affine opens into the small Zariski site (Stacks 0F1B) and of the inclusion of
the small Zariski site into the big one (Stacks 020Z), which is a morphism of sites because the
small Zariski site has binary products and fibre products which it preserves and its final
object `S` covers the final object of the big Zariski topos.

## Main definitions

* `AlgebraicGeometry.ZariskiCharts.affineOpensInclusion`: the inclusion of the affine opens of `S`
  into `(Aff/S)`.

## Main results

* `AlgebraicGeometry.ZariskiCharts.affineOpensInclusion_isContinuous`,
  `AlgebraicGeometry.ZariskiCharts.affineOpensInclusion_isCocontinuous`: the inclusion is
  continuous and cocontinuous for the Zariski topologies.
* `AlgebraicGeometry.ZariskiCharts.affineOpensInclusion_isMorphismOfSites`: it defines a morphism
  of sites.

## References

* [Stacks Project, Tag 0H0A](https://stacks.math.columbia.edu/tag/0H0A)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 0F1B](https://stacks.math.columbia.edu/tag/0F1B)
* [Stacks Project, Tag 020Z](https://stacks.math.columbia.edu/tag/020Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u t

namespace AlgebraicGeometry.ZariskiCharts

open AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big Zariski topology of `B` localized at `S`, on the big fppf category of `S`. -/
abbrev bigZariskiOverTopology : GrothendieckTopology (BigFppfOver B S hS) :=
  B.zariskiTopology.over (B.obj hS)

/-- The topology of the big Zariski category of `S` carried by `B` is the localization of the
big Zariski topology of `B`. -/
theorem bigZariskiOver_topology_eq :
    BigZariskiOver.topology B.toBigZariskiSite S (zariskiContains B S hS) =
      bigZariskiOverTopology B S hS :=
  B.bigZariskiOver_topology_toBigZariskiSite S hS

/-- The inclusion of the small Zariski site of `S` into the big fppf category of `S`. -/
abbrev smallZariskiIncl :
    SmallZariski B.toBigZariskiSite S (zariskiContains B S hS) ⥤ BigFppfOver B S hS :=
  SmallZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)

/-- The inclusion of the small Zariski site into the big one is continuous for the localized big
Zariski topology. -/
instance smallZariskiIncl_isContinuous :
    (smallZariskiIncl B S hS).IsContinuous
      (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (bigZariskiOverTopology B S hS) := by
  rw [← bigZariskiOver_topology_eq B S hS]
  exact smallZariskiInclusion_isContinuous B.toBigZariskiSite ⟨S, zariskiContains B S hS⟩

/-- The inclusion of the small Zariski site of a big Zariski site into the big Zariski category
is cocontinuous: it is the functor of Stacks 020Y at the identity. -/
theorem smallZariskiInclusion_isCocontinuous (Bz : BigZariskiSite.{u}) (T : Bz.Schemes) :
    (SmallZariski.inclusion Bz T.obj T.property).IsCocontinuous
      (SmallZariski.topology Bz T.obj T.property)
      (BigZariskiOver.topology Bz T.obj T.property) := by
  have e : smallZariskiToBigZariskiFunctor Bz T T (𝟙 T) =
      SmallZariski.inclusion Bz T.obj T.property := by
    dsimp [smallZariskiToBigZariskiFunctor]
    rw [Over.mapId_eq]
    rfl
  exact e ▸ smallZariskiToBigZariskiFunctor_isCocontinuous Bz T T (𝟙 T)

/-- The inclusion of the small Zariski site into the big one is cocontinuous for the localized
big Zariski topology (Stacks 020Z). -/
instance smallZariskiIncl_isCocontinuous :
    (smallZariskiIncl B S hS).IsCocontinuous
      (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (bigZariskiOverTopology B S hS) := by
  rw [← bigZariskiOver_topology_eq B S hS]
  exact smallZariskiInclusion_isCocontinuous B.toBigZariskiSite ⟨S, zariskiContains B S hS⟩

/-- The inclusion of the small Zariski site into the big one is full. -/
instance smallZariskiIncl_full : (smallZariskiIncl B S hS).Full :=
  ObjectProperty.full_ι _

/-- The inclusion of the small Zariski site into the big one is faithful. -/
instance smallZariskiIncl_faithful : (smallZariskiIncl B S hS).Faithful :=
  ObjectProperty.faithful_ι _

/-- The inclusion of the small Zariski site into the big one preserves fibre products. -/
instance smallZariskiIncl_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (smallZariskiIncl B S hS) :=
  preservesPullbacks_smallZariskiInclusion B.toBigZariskiSite S (zariskiContains B S hS)

/-- The inclusion of the affine opens into the small Zariski site preserves fibre products: it
creates them, fibre products of affine opens over an affine open being affine. -/
instance smallAffineZariskiInclusion_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)) := by
  let G := SmallZariski.toScheme B.toBigZariskiSite S (zariskiContains B S hS)
  let : PreservesLimitsOfShape WalkingCospan G := by
    change PreservesLimitsOfShape WalkingCospan
      (SmallZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
        BigZariskiOver.toScheme B.toBigZariskiSite S (zariskiContains B S hS))
    apply comp_preservesLimitsOfShape
  let : CreatesLimitsOfShape WalkingCospan
      (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)) :=
    affineCreatesPullbacks G
  infer_instance

section Charts

variable (p : BigFppfOver B S hS ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (hp1 : p = 𝟭 (BigFppfOver B S hS))

include hp1 in
/-- The Zariski topology `(Sch/S)` inherits along a functor equal to its identity is the
localized big Zariski topology. -/
theorem associatedTopology_eq_bigZariski :
    Stack.associatedTopology B S hS p B.zariskiTopology = bigZariskiOverTopology B S hS := by
  subst hp1
  exact Functor.inheritedTopology_id _

include hp1 in
/-- The affine opens of `S`, as objects of the big fppf category over `S`, lie over affine
schemes. -/
theorem isAffineObject_smallAffineZariski
    (y : SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS)) :
    IsAffineObject B S hS p
      ((SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
        smallZariskiIncl B S hS).obj y) := by
  subst hp1
  exact y.property

/-- **The affine opens of `S` inside `(Aff/S)`**: the inclusion of the small affine Zariski site
of `S` into the affine subcategory of the big fppf category over `S`. -/
noncomputable def affineOpensInclusion :
    SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS) ⥤
      AffineCategory B S hS p :=
  ObjectProperty.lift _
    (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
      smallZariskiIncl B S hS)
    (isAffineObject_smallAffineZariski B S hS p hp1)

/-- Followed by the inclusion of `(Aff/S)` into `(Sch/S)`, the inclusion of the affine opens is
the inclusion of the affine opens into the small Zariski site followed by the inclusion of the
small Zariski site into the big one. -/
theorem affineOpensInclusion_comp_inclusion :
    affineOpensInclusion B S hS p hp1 ⋙ AffineCategory.inclusion B S hS p =
      SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
        smallZariskiIncl B S hS :=
  rfl

/-- The inclusion of the affine opens of `S` into `(Aff/S)` is full. -/
instance affineOpensInclusion_full : (affineOpensInclusion B S hS p hp1).Full :=
  haveI : (affineOpensInclusion B S hS p hp1 ⋙
      AffineCategory.inclusion B S hS p).Full :=
    inferInstanceAs (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
      smallZariskiIncl B S hS).Full
  Functor.Full.of_comp_faithful _ (AffineCategory.inclusion B S hS p)

/-- The inclusion of the affine opens of `S` into `(Aff/S)` is faithful. -/
instance affineOpensInclusion_faithful : (affineOpensInclusion B S hS p hp1).Faithful :=
  haveI : (affineOpensInclusion B S hS p hp1 ⋙
      AffineCategory.inclusion B S hS p).Faithful :=
    inferInstanceAs (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
      smallZariskiIncl B S hS).Faithful
  Functor.Faithful.of_comp _ (AffineCategory.inclusion B S hS p)

/-- The inclusion of the affine opens of `S` into `(Aff/S)` preserves fibre products. -/
instance affineOpensInclusion_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (affineOpensInclusion B S hS p hp1) := by
  have : PreservesLimitsOfShape WalkingCospan
      (affineOpensInclusion B S hS p hp1 ⋙ AffineCategory.inclusion B S hS p) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
        smallZariskiIncl B S hS))
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (AffineCategory.inclusion B S hS p)

/-- **The rings of functions of `(Aff/S)`, restricted to the affine opens of `S`, are the chart
rings of the small affine Zariski site**: the two presheaves of commutative rings are equal. -/
theorem affineOpensInclusion_op_comp_affineStructureCommPresheaf :
    (affineOpensInclusion B S hS p hp1).op ⋙
        affineStructureCommPresheaf B S hS p =
      (zariskiChartRingedSite B S hS).O.obj := by
  subst hp1
  rfl

/-- The composite of the affine opens into the small Zariski site and of the small Zariski site
into the big one is continuous. -/
instance smallAffineZariski_comp_incl_isContinuous :
    (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
        smallZariskiIncl B S hS).IsContinuous
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (bigZariskiOverTopology B S hS) :=
  Functor.isContinuous_comp _ _ _
    (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS)) _

/-- The composite of the affine opens into the small Zariski site and of the small Zariski site
into the big one is cocontinuous. -/
instance smallAffineZariski_comp_incl_isCocontinuous :
    (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
        smallZariskiIncl B S hS).IsCocontinuous
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (bigZariskiOverTopology B S hS) :=
  isCocontinuous_comp _ _ _ (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))

include hp hp1 in
/-- The affine inclusion of `(Aff/S)` into `(Sch/S)` is a dense subsite inclusion for the
Zariski topologies (Stacks 0H0B). -/
theorem affineInclusion_isDenseSubsite_zariski :
    (AffineCategory.inclusion B S hS p).IsDenseSubsite
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS))
      (bigZariskiOverTopology B S hS) := by
  have := isDenseSubsite_affineInclusion_zariski B S hS p hp
  rwa [associatedTopology_eq_bigZariski B S hS p hp1] at this

include hp hp1 in
/-- **The inclusion of the affine opens of `S` into `(Aff/S)` is continuous** for the Zariski
topologies. -/
theorem affineOpensInclusion_isContinuous :
    (affineOpensInclusion B S hS p hp1).IsContinuous
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS)) := by
  have hd := affineInclusion_isDenseSubsite_zariski B S hS p hp hp1
  have hcp : CoverPreserving
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS))
      (affineOpensInclusion B S hS p hp1) := by
    refine ⟨fun {y} R hR => ?_⟩
    rw [← hd.functorPushforward_mem_iff, ← Sieve.functorPushforward_comp]
    exact (CoverPreserving.of_isContinuous
      (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
        smallZariskiIncl B S hS) _ _).cover_preserve hR
  let _ : Functor.PreservesOneHypercovers.{u + 1} (affineOpensInclusion B S hS p hp1)
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS)) :=
    Functor.PreservesOneHypercovers.of_coverPreserving hcp
  infer_instance

include hp hp1 in
/-- **The inclusion of the affine opens of `S` into `(Aff/S)` is cocontinuous** for the Zariski
topologies: a Zariski covering of an affine open of `S` in `(Aff/S)` is refined by a covering by
affine opens of `S`. -/
theorem affineOpensInclusion_isCocontinuous :
    (affineOpensInclusion B S hS p hp1).IsCocontinuous
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS)) := by
  have hd := affineInclusion_isDenseSubsite_zariski B S hS p hp hp1
  refine ⟨fun {y} R hR => ?_⟩
  rw [← hd.functorPushforward_mem_iff] at hR
  have h := (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS) ⋙
    smallZariskiIncl B S hS).cover_lift
    (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (bigZariskiOverTopology B S hS) hR
  change Sieve.functorPullback
    (affineOpensInclusion B S hS p hp1 ⋙ AffineCategory.inclusion B S hS p)
      (Sieve.functorPushforward (AffineCategory.inclusion B S hS p)
        R) ∈ _ at h
  rwa [Sieve.functorPullback_comp, Sieve.functorPullback_functorPushforward_eq] at h

/-! ### The site condition -/

/-- The inclusion of the small Zariski site into the big one preserves the final object. -/
instance smallZariskiIncl_preservesTerminal :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (smallZariskiIncl B S hS) :=
  preservesTerminal_smallZariskiInclusion B.toBigZariskiSite S (zariskiContains B S hS)

/-- The inclusion of the small Zariski site into the big one preserves binary products, which
are fibre products over the final object `S`. -/
instance smallZariskiIncl_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (smallZariskiIncl B S hS) :=
  have : HasTerminal (SmallZariski B.toBigZariskiSite S (zariskiContains B S hS)) := inferInstance
  preservesBinaryProducts_of_preservesTerminal_and_pullbacks _

/-- **The images of the small Zariski site cover the final object of the big Zariski topos**:
every scheme over `S` maps to the final object `S` of the small Zariski site. -/
theorem coversTop_smallZariskiIncl :
    (bigZariskiOverTopology B S hS).CoversTop (smallZariskiIncl B S hS).obj := by
  intro X
  have h : Sieve.ofObjects (smallZariskiIncl B S hS).obj X = ⊤ := by
    ext Z f
    simp only [Sieve.top_apply, iff_true]
    exact ⟨SmallZariski.final B.toBigZariskiSite S (zariskiContains B S hS),
      ⟨Over.mkIdTerminal.from Z⟩⟩
  rw [h]
  exact (bigZariskiOverTopology B S hS).top_mem X

/-- **The inclusion of the small Zariski site into the big one defines a morphism of sites**,
for sheaves of sets in every universe containing `u + 1` (Stacks 020Z at that universe): it is
continuous, the small Zariski site has binary products and fibre products which it preserves,
and its images cover the final object. -/
theorem smallZariskiIncl_isMorphismOfSites :
    IsMorphismOfSites.{max (u + 1) t} (smallZariskiIncl B S hS)
      (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (bigZariskiOverTopology B S hS) := by
  let : HasBinaryProducts (SmallZariski B.toBigZariskiSite S (zariskiContains B S hS)) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : EssentiallySmall.{u} (BigFppfOver B S hS) := inferInstanceAs
    (EssentiallySmall.{u} (Over (B.obj hS)))
  let : EssentiallySmall.{max (u + 1) t} (BigFppfOver B S hS) :=
    essentiallySmall_lift.{max (u + 1) t, u} _
  let : HasSheafify (bigZariskiOverTopology B S hS) (Type (max (u + 1) t)) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) t} _ _
  let : (bigZariskiOverTopology B S hS).WEqualsLocallyBijective (Type (max (u + 1) t)) :=
    .ofEssentiallySmall.{_, _, _, _, max (u + 1) t} _
  let (Y : (BigFppfOver B S hS)ᵒᵖ) : EssentiallySmall.{max (u + 1) t}
      (CostructuredArrow (smallZariskiIncl B S hS).op Y) :=
    essentiallySmall_lift.{max (u + 1) t, u} _
  let (Q : (SmallZariski B.toBigZariskiSite S (zariskiContains B S hS))ᵒᵖ ⥤
      Type (max (u + 1) t)) : (smallZariskiIncl B S hS).op.HasLeftKanExtension Q := by
    let (Y : (BigFppfOver B S hS)ᵒᵖ) : HasColimitsOfShape
        (CostructuredArrow (smallZariskiIncl B S hS).op Y) (Type (max (u + 1) t)) :=
      hasColimitsOfShape_of_essentiallySmall.{max (u + 1) t} _ _
    let : (smallZariskiIncl B S hS).op.HasPointwiseLeftKanExtension Q :=
      fun Y => by infer_instance
    infer_instance
  exact Stacks.Sites.LowerShriek.isMorphismOfSites_of_coversTop (smallZariskiIncl B S hS) _ _
    (coversTop_smallZariskiIncl B S hS)

include hp hp1 in
/-- **The inclusion of the affine opens of `S` into `(Aff/S)` defines a morphism of sites**, for
sheaves of sets in every universe containing `u + 1`. Followed by the dense subsite inclusion
`(Aff/S) ⥤ (Sch/S)` of Stacks 0H0B it is the composite of the dense subsite inclusion of the
affine opens into the small Zariski site (Stacks 0F1B) and of the morphism of sites of the small
Zariski site into the big one, and a functor which becomes a morphism of sites after a dense
subsite inclusion is one. -/
theorem affineOpensInclusion_isMorphismOfSites :
    IsMorphismOfSites.{max (u + 1) t} (affineOpensInclusion B S hS p hp1)
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS)) := by
  let := affineInclusion_isDenseSubsite_zariski B S hS p hp hp1
  let := affineOpensInclusion_isContinuous B S hS p hp hp1
  let (X : (SmallZariski B.toBigZariskiSite S (zariskiContains B S hS))ᵒᵖ) : HasLimitsOfShape
      (StructuredArrow X
        (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS)).op)
      (Type (max (u + 1) t)) :=
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  let (X : (BigFppfOver B S hS)ᵒᵖ) : HasLimitsOfShape
      (StructuredArrow X (AffineCategory.inclusion B S hS p).op)
      (Type (max (u + 1) t)) :=
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  let := IsMorphismOfSites.ofIsDenseSubsite.{max (u + 1) t}
    (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS))
    (J := SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (K := SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
  let := smallZariskiIncl_isMorphismOfSites.{u, t} B S hS
  have h := isMorphismOfSites_comp.{max (u + 1) t} (bigZariskiOverTopology B S hS)
    (SmallZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS))
    (SmallAffineZariski.inclusion B.toBigZariskiSite S (zariskiContains B S hS))
    (smallZariskiIncl B S hS)
  exact IsMorphismOfSites.of_comp_isDenseSubsite (affineOpensInclusion B S hS p hp1)
    (AffineCategory.inclusion B S hS p) h

end Charts

end AlgebraicGeometry.ZariskiCharts
