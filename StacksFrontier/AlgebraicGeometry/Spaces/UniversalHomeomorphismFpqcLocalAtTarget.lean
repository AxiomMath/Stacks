module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria

/-!
# Being a universal homeomorphism is fpqc local on the base for algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism of algebraic spaces over `S`
is a universal homeomorphism exactly when its base change to every member of some fpqc covering
family of its target is a universal homeomorphism. This is **Stacks 0CFX**.

The decomposition is the source's. A continuous map of topological spaces is a homeomorphism
exactly when it is injective, surjective and open, and each of the three conditions is tested
by the same base changes, so a universal homeomorphism is the same thing as a surjective,
universally injective, universally open morphism (**Stacks 03MV**, **Stacks 03Z2** part (2),
**Stacks 05Z5**). Surjectivity is fpqc local on the base by **Stacks 041Q**, universal
injectivity by **Stacks 041R** and universal openness by **Stacks 041P**, and locality on the
base passes to an infimum of morphism properties.

## Main definitions

* `AlgebraicGeometry.Space.universalHomeomorphismMorphismProperty`: being a universal
  homeomorphism (**Stacks 05Z5**) as a `CategoryTheory.MorphismProperty` on
  `AlgebraicGeometry.AlgebraicSpaces`, the spelling at which locality on the base is stated.

## Main results

* `universalHomeomorphism_iff_isSurjective_and_universallyInjective_and_universallyOpen`, in
  the namespace `AlgebraicGeometry.Space`: a morphism of algebraic spaces over `S` is a
  universal homeomorphism exactly when it is surjective, universally injective and universally
  open.
* `AlgebraicGeometry.Space.universalHomeomorphismMorphismProperty_eq_inf`: the same statement
  as an identity of morphism properties.
* `AlgebraicGeometry.Space.universalHomeomorphism_isLocalAtTarget_fpqc`: **Stacks 0CFX**.
* `AlgebraicGeometry.Space.universalHomeomorphism_isLocalAtTarget_fppf`: the same at the fppf
  precoverage, which is the form the relative properties of Stacks 03YK consume.

## Implementation notes

All four conditions — being a universal homeomorphism, surjectivity, universal injectivity and
universal openness — are read on the point sets of Stacks 03BU with the topology of
Stacks 03BX, and the last three of them are quantified over exactly the base changes that the
first is. So the equivalence is the pointwise decomposition of `IsHomeomorph` into continuity,
openness and bijectivity, the continuity being automatic
(`AlgebraicGeometry.Space.continuous_pointsMap`); the one asymmetry is that surjectivity is
*not* quantified over base changes, so the forward direction specialises to the identity of the
target and the backward direction transports surjectivity along a base change.

Universal injectivity is here recast, through **Stacks 040X**, as surjectivity of the relative
diagonal, which turns its fpqc locality (**Stacks 041R**) into an instance of the fpqc locality
of surjectivity (**Stacks 041Q**) applied to `Δ_f : X ⟶ X ×_Y X`: an fpqc covering `{Y i ⟶ Y}`
pulls back along `X ×_Y X ⟶ Y` to an fpqc covering of `X ×_Y X` whose base changes of `Δ_f` are
the relative diagonals of the base changes of `f`, the identification being the comparison
morphism `Stacks.SeparationLocal.diagonalObjMap` of the relative diagonal objects together with
the two cartesian squares it sits in. The two sides of Mathlib's
`CategoryTheory.MorphismProperty.IsLocalAtTarget` speak of
`CategoryTheory.Limits.pullback.snd` in the category of algebraic spaces whereas those squares
are formed from the presheaf fibre product of Stacks 02X2;
`AlgebraicGeometry.AlgebraicSpaces.hom_pullback_snd_iff` moves between the two.

The three conjuncts are bracketed as `(surjective ⊓ universally injective) ⊓ universally open`,
the order in which the two instances supplied by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.inf` compose without reassociation, which is
why the equivalence above is reassociated rather than used as it stands.

The index universe of a covering family is a free universe parameter of
`AlgebraicGeometry.Space.Topology.precoverage` and stays free here, as it does in Stacks 041Q
and Stacks 041P.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03MV](https://stacks.math.columbia.edu/tag/03MV)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 03Z2](https://stacks.math.columbia.edu/tag/03Z2)
* [Stacks Project, Tag 040X](https://stacks.math.columbia.edu/tag/040X)
* [Stacks Project, Tag 041P](https://stacks.math.columbia.edu/tag/041P)
* [Stacks Project, Tag 041Q](https://stacks.math.columbia.edu/tag/041Q)
* [Stacks Project, Tag 041R](https://stacks.math.columbia.edu/tag/041R)
* [Stacks Project, Tag 05Z5](https://stacks.math.columbia.edu/tag/05Z5)
* [Stacks Project, Tag 0CFX](https://stacks.math.columbia.edu/tag/0CFX)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

open Stacks.SeparationLocal

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_UniversalHomeomorphismFpqcLocalAtTarget :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_UniversalHomeomorphismFpqcLocalAtTarget
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_UniversalHomeomorphismFpqcLocalAtTarget B S hS).has_limit _

/-- Being a universal homeomorphism (**Stacks 05Z5**), as a property of morphisms in the
category of algebraic spaces over `S`. This is the spelling at which locality on the base,
Stacks 03YH, is stated. -/
abbrev universalHomeomorphismMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => UniversalHomeomorphism B S hS f.hom

/-- A morphism of algebraic spaces over `S` is a universal homeomorphism (**Stacks 05Z5**)
exactly when it is surjective, universally injective (**Stacks 03MV**) and universally open
(**Stacks 03Z2**, part (2)).

A continuous map of topological spaces is a homeomorphism exactly when it is injective,
surjective and open, and the maps on points of morphisms of algebraic spaces are automatically
continuous. Universal injectivity and universal openness are quantified over the same base
changes as the homeomorphism condition, so they match conjunct by conjunct; surjectivity is
not, and is read off from the base change along the identity of the target in one direction and
transported along an arbitrary base change in the other. -/
theorem universalHomeomorphism_iff_isSurjective_and_universallyInjective_and_universallyOpen
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    UniversalHomeomorphism B S hS f ↔
      IsSurjective B S hS f ∧ UniversallyInjective B S hS f ∧ UniversallyOpen B S hS f := by
  constructor
  · intro h
    refine ⟨?_, fun Z hZ g => (h Z hZ g).injective, fun Z hZ g => (h Z hZ g).isOpenMap⟩
    have hs := (h Y hY (𝟙 Y)).surjective
    have hcond : pullback.fst (𝟙 Y) f = pullback.snd (𝟙 Y) f ≫ f :=
      (Category.comp_id _).symm.trans (pullback.condition (f := 𝟙 Y) (g := f))
    rw [hcond, pointsMap_comp] at hs
    exact hs.of_comp
  · rintro ⟨hsurj, hinj, hopen⟩
    exact fun Z hZ g =>
      ⟨continuous_pointsMap B S hS _, hopen Z hZ g,
        ⟨hinj Z hZ g,
          surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hsurj⟩⟩

/-- Surjectivity on the point sets of Stacks 03BU, packaged as a morphism property of the
presheaves on the big fppf site of `S`. This is where the relative diagonal of a morphism of
algebraic spaces lives. -/
private abbrev surjectiveOnPointsPresheafProperty :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun _ _ f => IsSurjective B S hS f

/-- An isomorphism of presheaves on the big fppf site of `S` is surjective on points: the map
induced by its inverse is a section of the map it induces. -/
private theorem isSurjective_hom_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    IsSurjective B S hS e.hom := fun y => by
  refine ⟨pointsMap B S hS G e.inv y, ?_⟩
  have h := congrFun (pointsMap_comp B S hS G e.inv e.hom) y
  rw [e.inv_hom_id, pointsMap_id] at h
  exact h.symm

private instance surjectiveOnPointsPresheafProperty_respectsIso :
    (surjectiveOnPointsPresheafProperty B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e _ hf => isSurjective_comp B S hS (isSurjective_hom_of_iso B S hS e) hf)
    (fun e _ hf => isSurjective_comp B S hS hf (isSurjective_hom_of_iso B S hS e))

/-- **Stacks 041R.** Universal injectivity of morphisms of algebraic spaces over `S` is local
on the base for the fpqc topology of Stacks 03YH.

Universal injectivity of `f : X ⟶ Y` is surjectivity of its relative diagonal
`Δ_f : X ⟶ X ×_Y X` by **Stacks 040X**. Pulling a covering `{Y i ⟶ Y}` back along
`X ×_Y X ⟶ Y` gives a covering of `X ×_Y X` whose base changes of `Δ_f` are the relative
diagonals of the base changes of `f`, so Stacks 041Q for surjectivity applies. -/
private theorem isLocalAtTarget_fpqc_universallyInjective :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => UniversallyInjective B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  let Q := surjectiveOnPointsPresheafProperty B S hS
  have heq : (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
      UniversallyInjective B S hS f.hom) = Q.diagonal.inverseImage (ObjectProperty.ι _) := by
    funext X Y f
    exact propext (universallyInjective_iff_isSurjective_diagonal B S hS X.property f.hom)
  have : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        UniversallyInjective B S hS f.hom) := by
    rw [heq]
    infer_instance
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff
    (K := Topology.precoverage.{u, v} .fpqc B S hS) ?_
  intro X Y f R hR
  constructor
  · intro hf U g _ _
    exact universallyInjective_of_isPullback B S hS X.property U.property Y.property f.hom g.hom
      hf (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g).flip)
  · intro hlocal
    obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
    refine (universallyInjective_iff_isSurjective_diagonal B S hS X.property f.hom).mpr ?_
    -- The relative diagonal of `f`, as a morphism of algebraic spaces to `X ×_Y X`.
    let Z : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS f f
    let d : X ⟶ Z := ObjectProperty.homMk (pullback.diagonal f.hom)
    let q : Z ⟶ Y := ObjectProperty.homMk (pullback.fst f.hom f.hom ≫ f.hom)
    -- The covering of `X ×_Y X` obtained by pulling the given covering back along `q`.
    let W : I → AlgebraicSpaces B S hS := fun i ↦ AlgebraicSpaces.fiberProduct B S hS (gi i) q
    let k : ∀ i, W i ⟶ Z := fun i ↦ ObjectProperty.homMk (pullback.snd (gi i).hom q.hom)
    have hmem : Presieve.ofArrows W k ∈ (Topology.precoverage.{u, v} .fpqc B S hS) Z :=
      ⟨I, W, k, rfl, Z.property, fun i ↦ (W i).property,
        isFpqcCovering_pullback B S hS gi q hcover.2.2⟩
    change surjectiveMorphismProperty B S hS d
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (K := Topology.precoverage.{u, v} .fpqc B S hS) hmem ?_
    rintro U g _ ⟨i⟩
    refine (AlgebraicSpaces.hom_pullback_snd_iff B S hS Q d (k i)).mpr ?_
    -- The relative diagonal of the base change of `f` along `g i`, which is surjective.
    have hsurj : Q (pullback.diagonal (pullback.snd f.hom (gi i).hom)) :=
      (AlgebraicSpaces.hom_pullback_snd_iff B S hS Q.diagonal f (gi i)).mp
        ((universallyInjective_iff_isSurjective_diagonal B S hS
          (pullback f (gi i)).property (pullback.snd f (gi i)).hom).mp (hlocal (gi i) (.mk i)))
    -- The diagonal object of that base change is `Y i ×_Y (X ×_Y X)`.
    have hbc := IsPullback.of_hasPullback (gi i).hom q.hom
    let e := (isPullback_diagonalObjMap f.hom (gi i).hom).isoIsPullback _ _ hbc
    have hdiag : IsPullback (pullback.fst f.hom (gi i).hom)
        (pullback.diagonal (pullback.snd f.hom (gi i).hom) ≫ e.hom)
        (pullback.diagonal f.hom) (pullback.snd (gi i).hom q.hom) :=
      (Stacks.SeparationLocal.isPullback_diagonal_pullbackSnd f.hom (gi i).hom).of_iso
        (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp)
        ((isPullback_diagonalObjMap f.hom (gi i).hom).isoIsPullback_hom_snd _ _ hbc).symm
    have hP := IsPullback.of_hasPullback (pullback.diagonal f.hom) (pullback.snd (gi i).hom q.hom)
    let eL := hdiag.isoIsPullback _ _ hP
    have heL := hdiag.isoIsPullback_hom_snd _ _ hP
    refine (Q.cancel_left_of_respectsIso eL.hom
      (pullback.snd (pullback.diagonal f.hom) (pullback.snd (gi i).hom q.hom))).mp ?_
    rw [heL]
    exact MorphismProperty.RespectsIso.postcomp Q e.hom _ hsurj

/-- Being a universal homeomorphism is, as a property of morphisms of algebraic spaces over
`S`, the infimum of surjectivity, universal injectivity (**Stacks 03MV**) and universal
openness (**Stacks 03Z2**, part (2)). -/
theorem universalHomeomorphismMorphismProperty_eq_inf :
    universalHomeomorphismMorphismProperty B S hS =
      (surjectiveMorphismProperty B S hS ⊓
          fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
            UniversallyInjective B S hS f.hom) ⊓
        universallyOpenMorphismProperty B S hS := by
  funext X Y f
  exact propext
    ((universalHomeomorphism_iff_isSurjective_and_universallyInjective_and_universallyOpen
      B S hS Y.property f.hom).trans and_assoc.symm)

/-- **Stacks 0CFX.** Being a universal homeomorphism is, for morphisms of algebraic spaces over
`S`, local on the base for the fpqc topology of Stacks 03YH: such a morphism is a universal
homeomorphism exactly when its base change to every member of some fpqc covering family of its
target is a universal homeomorphism.

A morphism is a universal homeomorphism exactly when it is surjective, universally injective
and universally open, surjectivity is fpqc local on the base by **Stacks 041Q**, universal
injectivity by **Stacks 041R** and universal openness by **Stacks 041P**, so their conjunction
is. -/
@[stacks 0CFX, sga "4 IV 8.5.5" "more general"]
instance universalHomeomorphism_isLocalAtTarget_fpqc :
    (universalHomeomorphismMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have hui : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => UniversallyInjective B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
    isLocalAtTarget_fpqc_universallyInjective.{u, v} B S hS
  have : MorphismProperty.IsLocalAtTarget
      (surjectiveMorphismProperty B S hS ⊓
        fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => UniversallyInjective B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
    MorphismProperty.IsLocalAtTarget.inf _ _
  rw [universalHomeomorphismMorphismProperty_eq_inf]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-- **Stacks 0CFX** at the fppf precoverage: being a universal homeomorphism is local on the
target for the fppf topology of algebraic spaces. This is the form in which Stacks 03YK's
relative properties ask for it, and it follows from the fpqc form because every fppf covering
family of algebraic spaces is an fpqc covering family (**Stacks 0DFQ**). -/
@[sga "4 IV 8.5.5" "partial"]
instance universalHomeomorphism_isLocalAtTarget_fppf :
    (universalHomeomorphismMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
