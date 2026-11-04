module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.SmoothCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties

/-!
# From separate smooth locality to smooth locality on the source-and-target (Stacks 06FB, 06FC)

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 06FB** is the converse direction
of **Stacks 06F9**: a property of morphisms of algebraic spaces over `S` which is local on the
source and local on the target for the smooth topology of **Stacks 03YH**, and is preserved by
postcomposition with a smooth morphism, is smooth local on the source-and-target in the sense of
**Stacks 06F8**. **Stacks 06FC** then lists the properties this applies to; the case of
*flatness* is proved here, which is the case the flat-fppf site of Chapters 103–104 needs.

The three fields of Stacks 06F8 come out as follows. Precomposition with a smooth morphism is
source locality applied to the two-member family consisting of that morphism and the identity,
which is a smooth covering because the identity alone is already surjective on points; this is
the smooth case of **Stacks 06EQ**. Smooth base change is target locality applied to the same
two-member family on the target, which is the smooth case of **Stacks 06EM**. The pointwise
criterion is trivial in one direction — take both neighbourhoods to be the identity — and in the
other is source locality applied to the family of the chosen smooth neighbourhoods of all the
points of the source, whose composites with the morphism factor as the diagram's morphism
followed by a smooth morphism and so have the property by the postcomposition hypothesis.

For flatness the postcomposition hypothesis is composition of flat morphisms (**Stacks 03MN**)
together with flatness of smooth morphisms (**Stacks 04TA**), and the two locality hypotheses
come from the fpqc ones (**Stacks 06ET**, **Stacks 041W**) by
`CategoryTheory.MorphismProperty.IsLocalAtSource.of_le` and its target analogue, along the
inequality of precoverages that **Stacks 0DFQ** gives for smooth coverings.

## Main results

* `AlgebraicGeometry.Space.pullbackFst_smooth_of_isLocalAtTarget`: **Stacks 06EM**, smooth case.
* `AlgebraicGeometry.Space.smooth_precoverage_le_fpqc`: the smooth precoverage of Stacks 03YH is
  contained in the fpqc one.
* `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget`: **Stacks 06FB**.
* `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_flat`: **Stacks 06FC**, flat case.

## Implementation notes

`pullbackFst_smooth_of_isLocalAtTarget` is the smooth case of Stacks 06EM, in the form of the
first projection out of the fibre product of Stacks 02X2; Stacks 06EM itself, uniformly in the
topology, is `AlgebraicGeometry.Space.prop_fiberProduct_fst_of_isLocalAtTarget`. Stacks 06EQ is
not proved here: its five cases are `AlgebraicGeometry.Space.comp_isFlat`,
`comp_isFlat_isLocallyOfFinitePresentation`,
`comp_isSyntomic`, `comp_isSmooth` and `comp_isEtale` in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/LocalOnSource/Precomposition.lean`.

The index universe of the two locality hypotheses of Stacks 06FB is pinned at `u + 1`, because the
pointwise criterion of Stacks 06F8 is indexed by `AlgebraicGeometry.Space.points`, which lives in
`Type (u + 1)`.

## References

* [Stacks Project, Tag 06EM](https://stacks.math.columbia.edu/tag/06EM)
* [Stacks Project, Tag 06EQ](https://stacks.math.columbia.edu/tag/06EQ)
* [Stacks Project, Tag 06FB](https://stacks.math.columbia.edu/tag/06FB)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

/-! ### A smooth morphism together with the identity is a smooth covering -/

/-- A morphism of algebraic spaces over `S` together with the identity of its target forms a
two-member smooth covering family as soon as the morphism is smooth: the identity alone is
already surjective on points. -/
theorem isSmoothCovering_pair_id
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X : AlgebraicSpaces B S hS} (a : X' ⟶ X) (ha : IsSmooth B S hS a.hom) :
    IsSmoothCovering B S hS
      (fun i : ULift.{v} Bool => ((if i.down then X else X') : AlgebraicSpaces B S hS).obj)
      (fun i => (match i with
        | ⟨true⟩ => 𝟙 X
        | ⟨false⟩ => a :
          ((if i.down then X else X') : AlgebraicSpaces B S hS) ⟶ X).hom) := by
  refine ⟨X.property, ?_, ?_, ?_⟩
  · rintro ⟨b⟩
    cases b with
    | true => exact X.property
    | false => exact X'.property
  · rintro ⟨b⟩
    cases b with
    | true => exact isSmooth_id B S hS X.property
    | false => exact ha
  · exact Set.eq_univ_of_forall fun x =>
      Set.mem_iUnion.mpr ⟨ULift.up true, x, pointsMap_id_apply B S hS x⟩

/-- A smooth morphism `a` completed by the identity of its target is a smooth covering family
(for any precoverage universe) having `a` as a member. -/
private theorem exists_pair_mem_smooth_precoverage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X : AlgebraicSpaces B S hS} (a : X' ⟶ X) (ha : IsSmooth B S hS a.hom) :
    ∃ (Z : ULift.{v} Bool → AlgebraicSpaces B S hS) (g : ∀ i, Z i ⟶ X),
      Presieve.ofArrows Z g ∈ Topology.precoverage.{u, v} .smooth B S hS X ∧
        Presieve.ofArrows Z g a :=
  ⟨fun i => if i.down then X else X',
    fun i => match i with
      | ⟨true⟩ => 𝟙 X
      | ⟨false⟩ => a,
    ⟨ULift.{v} Bool, _, _, rfl, X.property, fun i => (if i.down then X else X').property,
      isSmoothCovering_pair_id B S hS a ha⟩,
    by simpa using Presieve.ofArrows.mk (ULift.up false)⟩

/-! ### Stacks 06EQ, smooth case -/

/-- **Stacks 06EQ**, the smooth case. A property of morphisms of algebraic spaces over `S` which
is local on the source for the smooth topology is preserved by precomposition with a smooth
morphism.

The smooth morphism need not be surjective; it is made a member of a covering family by adding
the identity of its target. -/
theorem precomp_smooth_of_isLocalAtSource
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtSource (Topology.precoverage.{u, v} .smooth B S hS)]
    {X' X Y : AlgebraicSpaces B S hS} (a : X' ⟶ X) (f : X ⟶ Y)
    (ha : IsSmooth B S hS a.hom) (hf : P f) :
    P (a ≫ f) := by
  obtain ⟨Z, g, hcov, hmem⟩ := exists_pair_mem_smooth_precoverage.{u, v} B S hS a ha
  exact MorphismProperty.IsLocalAtSource.comp hcov a hmem hf

/-! ### Stacks 06EM, smooth case -/

/-- **Stacks 06EM**, the smooth case. A property of morphisms of algebraic spaces over `S` which
is local on the target for the smooth topology is preserved by base change along a smooth
morphism, in the form of the first projection out of the fibre product of Stacks 02X2.

Stacks 06EM for every topology of Stacks 03YH is
`AlgebraicGeometry.Space.prop_fiberProduct_fst_of_isLocalAtTarget`. -/
theorem pullbackFst_smooth_of_isLocalAtTarget
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, v} .smooth B S hS)]
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : P f) (hg : IsSmooth B S hS g.hom) :
    P (ObjectProperty.homMk (pullback.fst g.hom f.hom) :
      AlgebraicSpaces.fiberProduct B S hS g f ⟶ Y') := by
  obtain ⟨Yi, q, hcov, hgm⟩ := exists_pair_mem_smooth_precoverage.{u, v} B S hS g hg
  have hFP := AlgebraicSpaces.isPullback_fiberProduct B S hS g f
  have : HasPullback f g := hFP.flip.hasPullback
  have hlocal : P (pullback.snd f g) :=
    MorphismProperty.IsLocalAtTarget.pullbackSnd (P := P)
      (K := Topology.precoverage.{u, v} .smooth B S hS)
      hcov hgm hf
  let e : AlgebraicSpaces.fiberProduct B S hS g f ≅ pullback f g :=
    hFP.isoPullback ≪≫ pullbackSymmetry g f
  have heq : e.hom ≫ pullback.snd f g =
      (ObjectProperty.homMk (pullback.fst g.hom f.hom) :
        AlgebraicSpaces.fiberProduct B S hS g f ⟶ Y') := by
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd, hFP.isoPullback_hom_fst]
  rw [← heq]
  exact (P.cancel_left_of_respectsIso e.hom (pullback.snd f g)).mpr hlocal

/-! ### Stacks 06FB -/

/-! ### Stacks 06FC, flat case -/

/-- The smooth precoverage of Stacks 03YH is contained in the fpqc one: a smooth covering of
algebraic spaces over `S` is an fpqc covering, by the smooth case of Stacks 0DFQ. -/
alias smooth_precoverage_le_fpqc := Topology.precoverage_smooth_le_fpqc

section Flat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06FC**, the flat case. Flatness of morphisms of algebraic spaces over `S` is smooth
local on the source-and-target.

The two locality hypotheses of Stacks 06FB come from the fpqc ones (Stacks 06ET and 041W) along
`AlgebraicGeometry.Space.smooth_precoverage_le_fpqc`, and the postcomposition hypothesis is
composition of flat morphisms (Stacks 03MN) applied to the flatness of a smooth morphism
(Stacks 04TA). -/
@[stacks 06FC "flat"]
theorem isSmoothLocalOnSourceAndTarget_flat :
    IsSmoothLocalOnSourceAndTarget B S hS (fun _ _ f => IsFlat B S hS f) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsFlat B S hS f
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    P.inverseImage (ObjectProperty.ι fun F => IsAlgebraicSpace B S hS F)
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    isFlat_isLocalAtSource_fpqc B S hS
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtSource.of_le (smooth_precoverage_le_fpqc B S hS)
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    isFlat_isLocalAtTarget_fpqc B S hS
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (smooth_precoverage_le_fpqc B S hS)
  exact isSmoothLocalOnSourceAndTarget B S hS P
    (fun hX hY hZ f g hf hg => isFlat_comp B S hS hX hY hZ f g hf
      (isFlat_of_isSmooth B S hS g hg))

end Flat

end AlgebraicGeometry.Space

end
