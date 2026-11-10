module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.SmoothCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.SyntomicSourceLocalityTransfer

/-!
# Locality of the Koszul property of morphisms of algebraic spaces

The property of being a local complete intersection morphism of algebraic spaces over `S` is
local on the source for the syntomic topology of **Stacks 03YH** (**Stacks 0CHN**) and local on
the base for it (**Stacks 0CHM**, whose source states this for the coarser fpqc topology). The
two together make the Koszul property smooth local on the source-and-target.

## Main results

* `AlgebraicGeometry.Space.isLocalCompleteIntersection_isLocalAtSource_syntomic`:
  **Stacks 0CHN**.
* `AlgebraicGeometry.Space.isLocalCompleteIntersection_isLocalAtTarget_syntomic`: locality on
  the base for syntomic coverings of the target, the syntomic case of **Stacks 0CHM**.
* `AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`: the
  Koszul property of morphisms of algebraic spaces over `S` is smooth local on the
  source-and-target.
* `AlgebraicGeometry.Space.isLocalCompleteIntersection_of_isSyntomic` and
  `AlgebraicGeometry.Space.isLocalCompleteIntersection_of_isSmooth`: a syntomic, and hence a
  smooth, morphism of algebraic spaces is Koszul.

## Implementation notes

Source locality is the syntomic case of the transfer **Stacks 06ER**,
`AlgebraicGeometry.Space.isLocalAtSource_syntomic_of_schemes`, at the Koszul property of
morphisms of schemes. The transfer consumes the schemes case of syntomic source locality,
**Stacks 069P**, which is
`AlgebraicGeometry.isLocalAtSource_syntomic_isLocalCompleteIntersectionMorphism`, together with
étale locality on source and target,
`AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism`, whose own
hypothesis is the étale restriction of the schemes case,
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale`.

Target locality for the syntomic topology is read off from source locality, rather than from the
fpqc transfer: given a syntomic covering `{gᵢ : Yᵢ ⟶ Y}` of the target of `f : X ⟶ Y`, the
family of second projections `{X ×_Y Yᵢ ⟶ X}` is a syntomic covering of the source
(**Stacks 041B**), and the composite of such a projection with `f` is the first projection
`X ×_Y Yᵢ ⟶ Yᵢ` followed by `gᵢ`. The first projection is the base change of `f` along the flat
`gᵢ`, so it is Koszul by **Stacks 06C7** as soon as `f` is, and `gᵢ` is Koszul because it is
syntomic, so the composite is Koszul by **Stacks 06C8**. The other direction of the locality is
Stacks 06C7 on its own, the members of a syntomic covering being flat.

The fpqc case of Stacks 0CHM is not reachable this way: the members of an fpqc covering are flat
but not syntomic, so the composite above need not be Koszul, and the generic fpqc transfer
`AlgebraicGeometry.Space.isLocalAtTarget_fpqc_of_schemes` asks for stability of the property
under base change along an *arbitrary* morphism, which the Koszul property does not have — it is
stable under flat base change only. It is proved instead by the source's own argument —
refine an fpqc covering to one whose members are schemes and apply the schemes case
**Stacks 069N** over an étale chart of the target — as
`AlgebraicGeometry.Space.isLocalCompleteIntersection_isLocalAtTarget_fpqc`. The syntomic case
below is what the smooth source-and-target locality consumes.

A syntomic morphism of schemes is Koszul by the factorization of **Stacks 069K**: near a point
of the source it restricts to a morphism of affine schemes, which by **Stacks 04II** factors as
an immersion into affine space over the target followed by the smooth structure morphism, and
that immersion is regular by **Stacks 067T**, hence Koszul-regular by **Stacks 063K**.

## References

* [Stacks Project, Tag 069K](https://stacks.math.columbia.edu/tag/069K)
* [Stacks Project, Tag 069N](https://stacks.math.columbia.edu/tag/069N)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
* [Stacks Project, Tag 06C7](https://stacks.math.columbia.edu/tag/06C7)
* [Stacks Project, Tag 06C8](https://stacks.math.columbia.edu/tag/06C8)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
* [Stacks Project, Tag 0CHM](https://stacks.math.columbia.edu/tag/0CHM)
* [Stacks Project, Tag 0CHN](https://stacks.math.columbia.edu/tag/0CHN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u v

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A syntomic morphism of algebraic spaces is Koszul -/

/-- A syntomic morphism of algebraic spaces over `S` is a local complete intersection morphism:
both conditions are read on every commuting square of étale charts, where this is the
implication (2) ⇒ (1) of **Stacks 069K** for morphisms of schemes. -/
public theorem isLocalCompleteIntersection_of_isSyntomic
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : IsSyntomic B S hS f) :
    IsLocalCompleteIntersection B S hS f :=
  fun U V a b h ha hb hsq =>
    AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_syntomic (hf U V a b h ha hb hsq)

/-- A smooth morphism of algebraic spaces over `S` is a local complete intersection morphism,
being syntomic. -/
public theorem isLocalCompleteIntersection_of_isSmooth
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : IsSmooth B S hS f) :
    IsLocalCompleteIntersection B S hS f :=
  isLocalCompleteIntersection_of_isSyntomic B S hS f (isSyntomic_of_isSmooth B S hS f hf)

/-! ### Stacks 0CHN -/

/-- **Stacks 0CHN.** The property of being a local complete intersection morphism of algebraic
spaces over `S` is local on the source for the syntomic topology of Stacks 03YH.

The schemes case, Stacks 069P, is
`AlgebraicGeometry.isLocalAtSource_syntomic_isLocalCompleteIntersectionMorphism`; the étale
locality on source and target that the transfer also consumes needs only its étale restriction,
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale`. -/
@[stacks 0CHN]
public theorem isLocalCompleteIntersection_isLocalAtSource_syntomic :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocalCompleteIntersection B S hS f.hom)
      (Topology.precoverage.{u, v} .syntomic B S hS) :=
  have := _root_.AlgebraicGeometry.isLocalAtSource_syntomic_isLocalCompleteIntersectionMorphism.{u}
  isLocalAtSource_syntomic_of_schemes B S hS
    (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
      MorphismProperty Scheme.{u})
    (_root_.AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism
      _root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale)

/-! ### Locality on the base for syntomic coverings of the target -/

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_LCILocality
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The property of being a local complete intersection morphism of algebraic spaces over `S` is
local on the base for the syntomic topology of Stacks 03YH: it may be checked after a syntomic
covering of the target.

This is the syntomic case of Stacks 0CHM, whose statement is for the coarser fpqc topology and
is `AlgebraicGeometry.Space.isLocalCompleteIntersection_isLocalAtTarget_fpqc`; see the module
docstring for why the fpqc case does not follow from the argument used here. -/
public theorem isLocalCompleteIntersection_isLocalAtTarget_syntomic :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocalCompleteIntersection B S hS f.hom)
      (Topology.precoverage.{u, v} .syntomic B S hS) := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ f => IsLocalCompleteIntersection B S hS f.hom
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsLocalCompleteIntersection B S hS f
  let _ : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso B S hS _
  let _ : P.RespectsIso := holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _
  let _ : Q.IsLocalAtSource (Topology.precoverage.{u, v} .syntomic B S hS) :=
    isLocalCompleteIntersection_isLocalAtSource_syntomic B S hS
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff (P := Q) ?_
  intro X Y f R hR
  obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
  obtain ⟨-, -, hsyncover⟩ := hcover
  have hsnd_iff : ∀ i, Q (pullback.snd f (gi i)) ↔ P (pullback.snd f.hom (gi i).hom) := fun i => by
    have hfib := AlgebraicSpaces.isPullback_fiberProduct B S hS f (gi i)
    rw [← Q.cancel_left_of_respectsIso hfib.isoPullback.hom (pullback.snd f (gi i)),
      hfib.isoPullback_hom_snd]
    rfl
  constructor
  · intro hf U g _ hg
    obtain ⟨i⟩ := hg
    exact (hsnd_iff i).2 (isLocalCompleteIntersection_pullback_snd B S hS f (gi i)
      (isFlat_of_isSyntomic B S hS (hsyncover.syntomic i)) hf)
  · intro hall
    have hpb := isSyntomicCovering_pullback_snd B S hS Yi gi f hsyncover
    refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := Q)
      (K := Topology.precoverage.{u, v} .syntomic B S hS)
      (R := Presieve.ofArrows (fun i => AlgebraicSpaces.fiberProduct B S hS (gi i) f)
        (fun i => ObjectProperty.homMk (pullback.snd (gi i).hom f.hom)))
      ⟨I, _, _, rfl, hpb.target_isAlgebraicSpace, hpb.source_isAlgebraicSpace, hpb⟩ ?_
    have hXp : ∀ i : I, IsAlgebraicSpace B S hS (pullback (gi i).hom f.hom) := fun i =>
      isAlgebraicSpace_pullback B S hS (gi i).hom f.hom (Yi i).property X.property Y.property
    have hYp : IsAlgebraicSpace B S hS Y.obj := Y.property
    intro U g hg
    obtain ⟨i⟩ := hg
    have hfst : P (pullback.fst (gi i).hom f.hom) := by
      rw [← P.cancel_left_of_respectsIso (pullbackSymmetry f.hom (gi i).hom).hom,
        pullbackSymmetry_hom_comp_fst]
      exact (hsnd_iff i).1 (hall (gi i) (Presieve.ofArrows.mk i))
    change IsLocalCompleteIntersection B S hS (pullback.snd (gi i).hom f.hom ≫ f.hom)
    rw [← pullback.condition]
    exact isLocalCompleteIntersection_comp B S hS (hXp i) (Yi i).property
      hYp _ _ hfst
      (isLocalCompleteIntersection_of_isSyntomic B S hS _ (hsyncover.syntomic i))

/-! ### Smooth locality on the source and target -/

/-- The property of being a local complete intersection morphism of algebraic spaces over `S` is
smooth local on the source-and-target in the sense of
`AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget` (Stacks 06F8).

The smooth precoverage of Stacks 03YH is contained in the syntomic one, so the two locality
hypotheses of the criterion Stacks 06FB are Stacks 0CHN and the syntomic case of Stacks 0CHM;
the postcomposition hypothesis is Stacks 06C8 together with a smooth morphism being Koszul. -/
public theorem isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget :
    IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ f => IsLocalCompleteIntersection B S hS f) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsLocalCompleteIntersection B S hS f
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    P.inverseImage (ObjectProperty.ι fun F => IsAlgebraicSpace B S hS F)
  let _ : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .syntomic B S hS) :=
    isLocalCompleteIntersection_isLocalAtSource_syntomic B S hS
  let _ : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtSource.of_le (Topology.precoverage_smooth_le_syntomic B S hS)
  let _ : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .syntomic B S hS) :=
    isLocalCompleteIntersection_isLocalAtTarget_syntomic B S hS
  let _ : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Topology.precoverage_smooth_le_syntomic B S hS)
  exact isSmoothLocalOnSourceAndTarget B S hS P
    fun hX hY hZ f g hf hg =>
      isLocalCompleteIntersection_comp B S hS
        hX hY hZ f g hf (isLocalCompleteIntersection_of_isSmooth B S hS g hg)

end Space

end AlgebraicGeometry

end
