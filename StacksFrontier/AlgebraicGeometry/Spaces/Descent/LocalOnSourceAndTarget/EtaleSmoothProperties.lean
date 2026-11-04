module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Consequences of étale-smooth locality on the source and target (Stacks 0CG0)

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of morphisms of
algebraic spaces over `S` which is étale-smooth local on the source-and-target
(`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget`, **Stacks 0CFZ**). Then `P` is
étale local on the source and smooth local on the target in Mathlib's sense, and an étale
morphism may be both appended to and cancelled from the target of a morphism with `P`.

These four statements are what **Stacks 0CIF** and the results above it use to transport such a
property to Deligne–Mumford morphisms of algebraic stacks, and they are the étale-smooth
analogue of **Stacks 06F9**.

## Main results

* `AlgebraicGeometry.Space.postcomp_of_etale`: **Stacks 0CG0**, postcomposition with an étale
  morphism preserves the property.
* `AlgebraicGeometry.Space.of_comp_etale`: **Stacks 0CG0**, an étale postcomposition may be
  cancelled.
* `AlgebraicGeometry.Space.isLocalAtSource_etale`: **Stacks 0CG0**, locality at the source for
  the étale topology.
* `AlgebraicGeometry.Space.isLocalAtTarget_smooth`: **Stacks 0CG0**, locality at the target for
  the smooth topology.
* `AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget.respectsIso`: such a property
  respects isomorphisms, which is the part of Mathlib's locality classes that is not about
  covering families.

## Implementation notes

All four statements go through the third clause of
`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget`, which tests the property on an
étale neighbourhood over a smooth target neighbourhood of each point of the source. The
neighbourhood used by `postcomp_of_etale` and `of_comp_etale` is the section
`X ⟶ X ×_Z Y` of the first projection induced by `f`, which is étale because the projection is
the base change of the étale `g` and the two are compatible over `X` (**Stacks 03FV**). For the
two locality statements the target neighbourhood is the identity, resp. the given member of the
covering family, so the fibre product degenerates and the comparison map is an isomorphism.

Respecting isomorphisms is proved from the first clause on the left and from
`postcomp_of_etale` on the right, an isomorphism being étale by
`AlgebraicGeometry.Space.isEtale_of_isIso`; this is why `postcomp_of_etale` comes first in this
module, as it needs no iso-invariance of its own.

The fibre product of `AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget` is
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct`, while Mathlib's locality classes are stated
with `CategoryTheory.Limits.pullback`; the two agree up to a canonical isomorphism, and
`AlgebraicGeometry.Space.prop_pullbackSnd_iff_fibreProductSnd` is the translation, used in both
directions by `isLocalAtTarget_smooth`.

The index type of a covering family is a free universe parameter of
`AlgebraicGeometry.Space.Topology.precoverage` and stays free in the two locality statements.

## References

* [Stacks Project, Tag 0CG0](https://stacks.math.columbia.edu/tag/0CG0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étale postcomposition -/

/-- A morphism into the fibre product `X ×_Z Y` is étale when its first component is étale and
`Y ⟶ Z` is étale. -/
private theorem isEtale_fiberProduct_lift
    {W X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z}
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ g)
    (ha : IsEtale B S hS a.hom) (hg : IsEtale B S hS g.hom) :
    IsEtale B S hS ((AlgebraicSpaces.isPullback_fiberProduct B S hS f g).lift a b w).hom := by
  let T := AlgebraicSpaces.fiberProduct B S hS f g
  let fst : T ⟶ X := ObjectProperty.homMk (pullback.fst f.hom g.hom)
  let snd : T ⟶ Y := ObjectProperty.homMk (pullback.snd f.hom g.hom)
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
  exact isEtale_of_isEtale_over B S hS W.property T.property X.property _ a.hom fst.hom ha
    (isEtale_of_isPullback B S hS snd fst g f hpb.flip hg)
    (congrArg (fun k : W ⟶ X => k.hom) (hpb.lift_fst a b w))

/-- For `f : X ⟶ Y` and étale `g : Y ⟶ Z`, the morphism `X ⟶ X ×_Z Y` induced by `𝟙 X` and `f` is
an étale section of the first projection lifting `f` through the second. -/
private theorem exists_etale_section_fiberProduct
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : IsEtale B S hS g.hom) :
    ∃ e : X ⟶ AlgebraicSpaces.fiberProduct B S hS (f ≫ g) g, IsEtale B S hS e.hom ∧
      e.hom ≫ pullback.fst (f.hom ≫ g.hom) g.hom = 𝟙 X.1 ∧
      e ≫ ObjectProperty.homMk (pullback.snd (f.hom ≫ g.hom) g.hom) = f := by
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS (f ≫ g) g
  exact ⟨hpb.lift (𝟙 X) f (by simp),
    isEtale_fiberProduct_lift B S hS _ _ _ (isEtale_id B S hS X.1) hg,
    congrArg (fun k : X ⟶ X => k.hom) (hpb.lift_fst _ _ _), hpb.lift_snd _ _ _⟩

/-- **Stacks 0CG0**, étale postcomposition. A property of morphisms of algebraic spaces over `S`
which is étale-smooth local on the source-and-target is preserved by postcomposition with an
étale morphism. -/
@[stacks 0CG0 "etale_postcomposition"]
theorem postcomp_of_etale
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : P f) (g : Y ⟶ Z)
    (hg : IsEtale B S hS g.hom) : P (f ≫ g) := by
  obtain ⟨e, he, hfst, hsnd⟩ := exists_etale_section_fiberProduct B S hS f g hg
  refine (hP.iff_forall_exists_etale_smooth_neighborhood (f ≫ g)).mpr fun x => ?_
  refine ⟨Y, X, g, e, x, isSmooth_of_isEtale B S hS Z.property hg, he, ?_, ?_⟩
  · change pointsMap B S hS X.1 (e.hom ≫ pullback.fst (f.hom ≫ g.hom) g.hom) x = x
    rw [hfst]
    exact congrFun (pointsMap_id B S hS X.1) x
  · change P (e ≫ ObjectProperty.homMk (pullback.snd (f.hom ≫ g.hom) g.hom))
    rwa [hsnd]

/-- A property of morphisms of algebraic spaces over `S` which is étale-smooth local on the
source-and-target respects isomorphisms: an isomorphism is étale, so it may be precomposed by
the first clause and postcomposed by `AlgebraicGeometry.Space.postcomp_of_etale`. -/
theorem IsEtaleSmoothLocalOnSourceAndTarget.respectsIso
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P : MorphismProperty (AlgebraicSpaces B S hS)}
    (hP : IsEtaleSmoothLocalOnSourceAndTarget B S hS P) : P.RespectsIso :=
  MorphismProperty.RespectsIso.mk P
    (fun e f hf => hP.precomp_of_etale e.hom f (isEtale_of_isIso B S hS e.hom.hom) hf)
    (fun e f hf =>
      postcomp_of_etale B S hS P hP f hf e.hom (isEtale_of_isIso B S hS e.hom.hom))

/-- **Stacks 0CG0**, cancelling an étale postcomposition. If a property of morphisms of
algebraic spaces over `S` is étale-smooth local on the source-and-target and holds for `f ≫ g`
with `g` étale, then it holds for `f`. -/
@[stacks 0CG0 "etale_postcomposition_permanence"]
lemma of_comp_etale
    {P : MorphismProperty (AlgebraicSpaces B S hS)}
    (hP : IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : IsEtale B S hS g.hom)
    (hfg : P (f ≫ g)) : P f := by
  obtain ⟨s, hs, -, hs_snd⟩ := exists_etale_section_fiberProduct B S hS f g hg
  exact hs_snd ▸ hP.precomp_of_etale s _ hs
    (hP.pullbackSnd_of_smooth (f ≫ g) hfg g (isSmooth_of_isEtale B S hS Z.property hg))

/-! ### Locality at the source for the étale topology -/

/-- **Stacks 0CG0**, étale locality on the source. A property of morphisms of algebraic spaces
over `S` which is étale-smooth local on the source-and-target is local at the source for the
étale topology. -/
@[stacks 0CG0 "etale_local_source"]
theorem isLocalAtSource_etale
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : IsEtaleSmoothLocalOnSourceAndTarget B S hS P) :
    P.IsLocalAtSource (Topology.precoverage.{u, v} .etale B S hS) := by
  have : P.RespectsIso := hP.respectsIso
  refine MorphismProperty.IsLocalAtSource.mk_of_iff (P := P)
    (K := Topology.precoverage.{u, v} .etale B S hS) ?_
  intro X Y f R hR
  obtain ⟨I, Xi, gi, rfl, -, -, hcover⟩ := hR
  refine ⟨fun hf _ _ ⟨i⟩ => hP.precomp_of_etale (gi i) f (hcover.etale i) hf, fun h => ?_⟩
  refine (hP.iff_forall_exists_etale_smooth_neighborhood f).2 fun x => ?_
  have hx : x ∈ ⋃ i, Set.range (pointsMap B S hS (Xi i).1 (gi i).hom) := by
    rw [hcover.jointly_surjective]
    exact Set.mem_univ _
  obtain ⟨i, xi, hxi⟩ := Set.mem_iUnion.mp hx
  let Z := AlgebraicSpaces.fiberProduct B S hS f (𝟙 Y)
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f (𝟙 Y)
  let fst : Z ⟶ X := ObjectProperty.homMk (pullback.fst f.hom (𝟙 Y.1))
  let snd : Z ⟶ Y := ObjectProperty.homMk (pullback.snd f.hom (𝟙 Y.1))
  let e : Xi i ⟶ Z := sq.lift (gi i) (gi i ≫ f) (by simp)
  have e_fst : e ≫ fst = gi i := sq.lift_fst _ _ _
  have e_snd : e ≫ snd = gi i ≫ f := sq.lift_snd _ _ _
  refine ⟨Y, Xi i, 𝟙 Y, e, xi, isSmooth_id_presheaf B S hS Y.1,
    isEtale_fiberProduct_lift B S hS _ _ _ (hcover.etale i) (isEtale_id B S hS Y.1), ?_, ?_⟩
  · change pointsMap B S hS (Xi i).1 (e ≫ fst).hom xi = x
    exact e_fst ▸ hxi
  · change P (e ≫ snd)
    exact e_snd ▸ h ⟨i⟩

/-! ### Locality at the target for the smooth topology -/

/-- The fibre product of two morphisms of algebraic spaces over `S` and their pullback in that
category agree up to a canonical isomorphism, so a morphism property respecting isomorphisms
holds for the second projection out of one exactly when it holds for the second projection out
of the other. -/
theorem prop_pullbackSnd_iff_fibreProductSnd
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    P (pullback.snd f g) ↔
      P (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS f g ⟶ Y') := by
  rw [← (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).isoPullback_hom_snd,
    P.cancel_left_of_respectsIso]

/-- **Stacks 0CG0**, smooth locality on the target. A property of morphisms of algebraic spaces
over `S` which is étale-smooth local on the source-and-target is local at the target for the
smooth topology. -/
@[stacks 0CG0 "smooth_local_target"]
theorem isLocalAtTarget_smooth
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : IsEtaleSmoothLocalOnSourceAndTarget B S hS P) :
    P.IsLocalAtTarget (Topology.precoverage.{u, v} .smooth B S hS) := by
  have : P.RespectsIso := hP.respectsIso
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff (P := P)
    (K := Topology.precoverage.{u, v} .smooth B S hS) ?_
  intro X Y f R hR
  obtain ⟨I, Yi, g, rfl, -, -, hcover⟩ := hR
  constructor
  · rintro hf U g' _ ⟨i⟩
    exact (prop_pullbackSnd_iff_fibreProductSnd B S hS P f (g i)).mpr
      (hP.pullbackSnd_of_smooth f hf (g i) (hcover.smooth i))
  · intro hall
    refine (hP.iff_forall_exists_etale_smooth_neighborhood f).2 fun x => ?_
    have hy : pointsMap B S hS X.obj f.hom x ∈
        ⋃ i, Set.range (pointsMap B S hS (Yi i).obj (g i).hom) := by
      rw [hcover.jointly_surjective]
      exact Set.mem_univ _
    obtain ⟨i, yi, hyi⟩ := Set.mem_iUnion.mp hy
    obtain ⟨xi, hxiX, -⟩ := exists_point_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f (g i)) x yi hyi.symm
    refine ⟨Yi i, AlgebraicSpaces.fiberProduct B S hS f (g i), g i, 𝟙 _, xi,
      hcover.smooth i, isEtale_id B S hS _, ?_, ?_⟩
    · simpa using hxiX
    · simpa using (prop_pullbackSnd_iff_fibreProductSnd B S hS P f (g i)).mp
        (hall (g i) (Presieve.ofArrows.mk i))

end AlgebraicGeometry.Space

end
