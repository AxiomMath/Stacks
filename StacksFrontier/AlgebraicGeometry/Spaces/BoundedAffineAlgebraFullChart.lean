module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward
public import StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor

/-!
# A morphism of direct-image algebras, read at the affine étale charts

The declarations here belong to the development of Stacks 081V and are used for Stacks 0823.
Where the notes below name `AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence` or the
functor-level statements, they refer to declarations outside this file and its imports.

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `Y` be an object of
`CategoryTheory.Over X` with representable structure morphism, let `Z` be affine over `X`, and let
`φ : Z.hom_* 𝒪_Z ⟶ Y.hom_* 𝒪_Y` be a morphism of the direct-image algebras of
`AlgebraicGeometry.Space.pushforwardAlgebra`.  **This file reads `φ` at the étale charts of `X`
and builds, at each affine chart, the morphism of schemes over the chart that induces it.**

`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` runs the other way: it computes the chart
value of the direct-image map of a *given* morphism `f : Y ⟶ Z` as pullback of regular functions
along the base-changed morphism `Y ×_X V ⟶ Z ×_X V`.  That is what the faithfulness half of
Stacks 081V consumes, in
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFaithful`: equal direct-image maps have
equal `AlgebraicGeometry.Scheme.Hom.appTop` at a chart, and at an *affine* chart the target
`Z ×_X V` is an affine scheme, so `AlgebraicGeometry.ext_of_isAffine` identifies the two
base-changed morphisms.  The surjectivity the *fullness* half needs is not a cancellation of that
kind: no `f` is given, and one has to be produced.  What this file produces is the chart-local
half of such an `f`.

## Main results

* `AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_algebraHom_app`: **the chart value of
  `φ` is a map of `Γ(V)`-algebras.**  Read through
  `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at source and target, the component of
  `φ` at an étale chart `V` of `X` is a ring map `Γ(Z ×_X V) ⟶ Γ(Y ×_X V)` carrying pullback
  along the cartesian projection `Z ×_X V ⟶ V` to pullback along `Y ×_X V ⟶ V`.  No affineness
  and no chart condition is used.  This is
  `AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app` with the
  morphism over `X` replaced by an arbitrary morphism of direct-image algebras; what stands in for
  `AlgebraicGeometry.Space.fSharp_comp_pushforwardRingMap` is the `comm` field of
  `AlgebraicGeometry.Space.AlgebraSheaf.Hom`, which is exactly that compatibility.
* `AlgebraicGeometry.Space.exists_chartHom_of_algebraHom`: **the chart base change built from
  `φ`.**  At an étale chart `V` of `X` whose scheme is affine there is a morphism of the big fppf
  category `Y ×_X V ⟶ Z ×_X V` which induces the chart value of `φ` on global regular functions
  and which commutes with the two cartesian projections to `V`.  This is the converse, at one
  affine chart, of `AlgebraicGeometry.Space.pushforwardRingMap_app_eq`.
* `AlgebraicGeometry.Space.pushforwardAlgebraMap_eq_of_appTop_smallBaseChangeOverMap_eq`: **the
  recognition principle.**  A morphism `f : Y ⟶ Z` over `X` whose base change to *every* étale
  chart of `X` induces the chart value of `φ` on regular functions has `φ` for its direct-image
  map.  So the direct-image map of a morphism over `X` is determined chartwise, and `φ` is in the
  image of `AlgebraicGeometry.Space.pushforwardAlgebraMap` as soon as some `f` realises the chart
  data.

## Implementation notes

**Why the chart morphism is built in the site and not only in schemes.**
`AlgebraicGeometry.Space.smallBaseChangeOverMap`, which
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` compares against, is a morphism of
`AlgebraicGeometry.BigFppfOver`, not of schemes, and the identities
`AlgebraicGeometry.Space.eq_smallBaseChangeOverMap` pins it down by are identities there.  So the
scheme morphism that `Stacks.Smooth.homEquivOfIsAffine` returns from the ring map has to be lifted
back to the site.  `AlgebraicGeometry.BigFppfOver.toScheme` is faithful but not full — it forgets
a structure morphism to `S` — and the lift is
`AlgebraicGeometry.BigFppfOver.homOfCompEq`, whose hypothesis is commutation with those structure
morphisms.  That hypothesis is supplied by the triangle over the chart: the chart value of `φ` is
a map of `Γ(V)`-algebras, so the scheme morphism lies over `V`, hence over `S`, the two
`CategoryTheory.Over.w` identities of the cartesian projections turning the one into the other.

**Affineness of the target only.**  As in
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFaithful`, it is the base change
`Z ×_X V` of the *target* that has to be an affine scheme —
`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj` is applied to `Z` — because both
`AlgebraicGeometry.ext_of_isAffine` and `Stacks.Smooth.homEquivOfIsAffine` ask it of the target.
Affineness of `Y` as a scheme is never used, and `Y` is not assumed affine over `X` at all; only
representability of its structure morphism is, which is what makes `Y ×_X V` a scheme.  This
matches `Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom`, the scheme-level universal
property, which asks affineness of the target only.

**One spelling throughout, and why the chart morphism is produced by an existential.**  The chart
`(smallBaseChange Y.hom hY).obj V` and the representing object `hY.pullback V.1.hom` are equal
only after unfolding the semireducible `AlgebraicGeometry.Space.smallBaseChange`, so instance
search does not cross between `chartScheme ((smallBaseChange …).obj V)` — the spelling
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` forces on its target — and
`(BigFppfOver.toScheme …).obj (hY.pullback V.1.hom)`, the spelling
`AlgebraicGeometry.Space.smallBaseChangeOverMap` and
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` are stated in.  Both affineness instances are
therefore provided by hand, and the scheme morphism is introduced by
`Classical`-free destructuring of an existential ascribed to the *second* spelling, so that every
later step — the triangle, the lift, and the two conclusions — is in one spelling and the
rewrites keyed on a composite have a single candidate.  For the same reason the last three steps
are terms rather than rewrites: `AlgebraicGeometry.BigFppfOver.toScheme_map_homOfCompEq` is stated
at the second spelling, and a `rw` with it builds a motive that is not type-correct under implicit
transparency.

**What fullness needs beyond this file, and where it is done.**  By
`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor_iff` fullness of the direct-image
functor is surjectivity of `AlgebraicGeometry.Space.pushforwardAlgebraMap` onto the morphisms of
direct-image algebras, so what is needed is a morphism `f : Y ⟶ Z` over `X` realising the chart
data this file produces.  Two steps separate the two, neither taken here; both are taken in
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFull` and
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness`.

* **The chart family is not glued here.**  The morphisms of
  `AlgebraicGeometry.Space.exists_chartHom_of_algebraHom` are produced one affine chart at a time
  and nothing here shows them compatible, let alone that they come from a morphism of sheaves on
  the big fppf site.  The tool that would consume such a family is
  `AlgebraicGeometry.Space.exists_hom_of_chartFamily` of
  `StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Glue`, which turns a family of points
  of a sheaf indexed by *all* the étale charts of an algebraic space, compatible with chart
  morphisms, into a morphism out of that space; or
  `AlgebraicGeometry.Space.exists_hom_of_chartHoms` of
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineChartGluing`, which does the same from a family
  indexed by the affine objects carrying an étale morphism to the space.  Both want the family at
  every chart of the *source* `Y`, and a chart of `Y` maps to `X` by a morphism that is not étale,
  so it is not a chart of `X` and `φ` says nothing at it directly.  Supplying the family there
  means factoring that point of `X` locally through an affine chart of `X`, by
  `AlgebraicGeometry.Space.generate_affineChartPresieve_mem`, building the point over each member
  of the resulting covering sieve, and amalgamating; the compatibility that argument needs is
  `AlgebraicGeometry.Space.chartPoint_eq` of
  `StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFull`, and the amalgamation itself is
  `AlgebraicGeometry.Space.exists_overHom_of_algebraHom` of
  `StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness`, which builds the morphism
  of sheaves one point at a time rather than through either of those two tools.
* **The identification is available at the affine charts only.**
  `AlgebraicGeometry.Space.pushforwardAlgebraMap_eq_of_appTop_smallBaseChangeOverMap_eq` asks for
  the chart identity at every étale chart of `X`, while
  `AlgebraicGeometry.Space.exists_chartHom_of_algebraHom` delivers it at the affine ones, those
  being where the base change of the target is an affine scheme.  Passing between the two is
  separatedness of a sheaf of commutative rings on the small étale site against the covering of a
  chart by the Zariski opens of its scheme —
  `AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology` at the affine opens, whose
  supremum is `⊤`.  That passage is
  `AlgebraicGeometry.Space.sheafHom_eq_of_affineChart` of
  `StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness`, which reads the sheaf
  condition sectionwise through
  `AlgebraicGeometry.Space.eq_of_openChart_restriction_eq_commRingCat` rather than at the level of
  presheaves of types: `AlgebraicGeometry.Space.coversTop_affineCharts` is *not* what is needed
  and `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` does not apply, asking the coefficient
  functor to land in `Type (max v₁ u₁)`, which for this site is `Type (u + 1)`, whereas
  `CategoryTheory.forget CommRingCat.{u}` lands in `Type u`.  Only the converse direction is in
  the tree, as `Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget'` of
  `StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf`.

**No `@[stacks]` attribute is placed.**  The clause of Stacks 081V this file serves is the
*fullness* of the direct-image functor, and fullness is not proved here: what is proved is the
chart reading of an arbitrary morphism of direct-image algebras, which is one of the two inputs
fullness needs.  Fullness itself is
`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor` of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness` and faithfulness is
`AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor`, so clause (a) of
`AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor_iff_bijective`, which asks
that `f ↦ f_*` be bijective, is delivered;
`AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence` remains a hypothesis, its one
remaining clause being essential surjectivity.  The unrestricted
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` is refuted by
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`, so
nothing here is stated over it.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (4)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), parts (1) and (2)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart value of a morphism of direct-image algebras -/

/-- **The chart value of a morphism of direct-image algebras is a map of `Γ(V)`-algebras.**

Let `Y`, `Z` be objects of `CategoryTheory.Over X` with representable structure morphisms, let
`φ : Z.hom_* 𝒪_Z ⟶ Y.hom_* 𝒪_Y` be a morphism of their direct-image algebras, and let `V` be an
étale chart of `X`.  Read through `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at the
source and the target, the component of `φ` at `V` is a ring map `Γ(Z ×_X V) ⟶ Γ(Y ×_X V)`
carrying the pullback of regular functions along the cartesian projection `Z ×_X V ⟶ V` to the
pullback along `Y ×_X V ⟶ V`.

This is `AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app` with the
morphism over `X` replaced by an arbitrary morphism of direct-image algebras.  The proof is the
same: both triangles over the base are
`AlgebraicGeometry.Space.fSharp_app_comp_pushforwardAlgebraSectionsIso`, Stacks 03G8 part (2) at
a single chart, and what joins them is the `comm` field of
`AlgebraicGeometry.Space.AlgebraSheaf.Hom` in place of
`AlgebraicGeometry.Space.fSharp_comp_pushforwardRingMap` — compatibility with the structure maps
`𝒪_X ⟶ f_* 𝒪` being exactly what a morphism of algebra sheaves carries beyond its underlying map
of sheaves of rings.

No affineness is used and no condition on the chart. -/
theorem cartesianProjectionAppTop_comp_algebraHom_app {X : AlgebraicSpaces B S hS} {Y Z : Over X}
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom)
    (φ : pushforwardAlgebra B S hS Z ⟶ pushforwardAlgebra B S hS Y)
    (V : SmallEtale B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map (hZ.snd V.1.hom)).appTop ≫
        (pushforwardAlgebraSectionsIso B S hS Z hZ V).inv ≫
        φ.right.hom.app (op V) ≫
        (pushforwardAlgebraSectionsIso B S hS Y hY V).hom =
      ((BigFppfOver.toScheme B S hS).map (hY.snd V.1.hom)).appTop := by
  have key : (smallEtaleRingedToposHom B S hS Z.hom).fSharp.hom.app (op V) ≫
      φ.right.hom.app (op V) =
      (smallEtaleRingedToposHom B S hS Y.hom).fSharp.hom.app (op V) :=
    ConcreteCategory.hom_ext _ _ (fun r => φ.comm (op V) r)
  rw [← fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Z hZ V,
    ← fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Y hY V]
  exact (cancelRetractionLeft ((smallEtaleRingedToposHom B S hS Z.hom).fSharp.hom.app (op V))
        (pushforwardAlgebraSectionsIso B S hS Z hZ V).hom_inv_id
        (φ.right.hom.app (op V) ≫
          (pushforwardAlgebraSectionsIso B S hS Y hY V).hom)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun m => m ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V).hom) key))

/-! ### The chart base change built from a morphism of direct-image algebras -/

/-- **At an affine chart, a morphism of direct-image algebras is pullback of regular functions
along a morphism of the base-changed charts over the chart.**

Let `Y` be an object of `CategoryTheory.Over X` with representable structure morphism, let `Z` be
affine over `X`, let `φ : Z.hom_* 𝒪_Z ⟶ Y.hom_* 𝒪_Y` be a morphism of their direct-image
algebras, and let `V` be an étale chart of `X` whose underlying scheme is affine.  Then there is a
morphism `Y ×_X V ⟶ Z ×_X V` of the big fppf category whose map on global regular functions is
the chart value of `φ`, read through
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at both ends, and which commutes with the
cartesian projections to `V`.

This is the converse, at one affine chart, of
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq`.  Three facts are consumed.  The base change
`Z ×_X V` of the *target* is an affine scheme, by
`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`, so `Stacks.Smooth.homEquivOfIsAffine`
returns a morphism of schemes with the chart value of `φ` for its
`AlgebraicGeometry.Scheme.Hom.appTop`.  That morphism lies over `V`: the chart value is a map of
`Γ(V)`-algebras by
`AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_algebraHom_app`, and `V`'s own scheme
being affine, `AlgebraicGeometry.ext_of_isAffine` upgrades that to commutation with the two
cartesian projections.  Lying over `V` it lies over `S`, so
`AlgebraicGeometry.BigFppfOver.homOfCompEq` lifts it to the site, where
`AlgebraicGeometry.BigFppfOver.toScheme` being faithful carries the triangle across.

Affineness of `Y` is not assumed and affineness of `Z ×_X V` as a scheme is used only through the
two lemmas above, both of which ask it of the target. -/
theorem exists_chartHom_of_algebraHom {X : AlgebraicSpaces B S hS} {Y : Over X}
    (Z : AffineOver B S hS X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y)
    (V : SmallEtale B S hS X.1)
    (hV : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V)) :
    ∃ m : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom,
      ((BigFppfOver.toScheme B S hS).map m).appTop =
          (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
            φ.right.hom.app (op V) ≫
            (pushforwardAlgebraSectionsIso B S hS Y hY V).hom ∧
        m ≫ hZ.snd V.1.hom = hY.snd V.1.hom := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hZ.pullback V.1.hom)) :=
    isAffine_smallBaseChange_obj B S hS Z.obj.hom hZ Z.property V hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X.1).obj V)) := hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := hV
  obtain ⟨v, hvapp⟩ : ∃ v : (BigFppfOver.toScheme B S hS).obj (hY.pullback V.1.hom) ⟶
      (BigFppfOver.toScheme B S hS).obj (hZ.pullback V.1.hom),
      v.appTop = (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
        φ.right.hom.app (op V) ≫
        (pushforwardAlgebraSectionsIso B S hS Y hY V).hom :=
    ⟨Stacks.Smooth.homEquivOfIsAffine.symm _,
      Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply _⟩
  have htri : v ≫ (BigFppfOver.toScheme B S hS).map (hZ.snd V.1.hom) =
      (BigFppfOver.toScheme B S hS).map (hY.snd V.1.hom) := by
    refine AlgebraicGeometry.ext_of_isAffine ?_
    refine (Scheme.Hom.comp_appTop _ _).trans ?_
    refine Eq.trans (congrArg
      (fun k => ((BigFppfOver.toScheme B S hS).map (hZ.snd V.1.hom)).appTop ≫ k) hvapp) ?_
    exact cartesianProjectionAppTop_comp_algebraHom_app B S hS hY hZ φ V
  have hv : v ≫ B.inclusion.map (hZ.pullback V.1.hom).hom =
      B.inclusion.map (hY.pullback V.1.hom).hom :=
    calc v ≫ B.inclusion.map (hZ.pullback V.1.hom).hom
        = v ≫ B.inclusion.map ((hZ.snd V.1.hom).left ≫ V.1.left.hom) := by
          rw [Over.w]
      _ = (v ≫ (BigFppfOver.toScheme B S hS).map (hZ.snd V.1.hom)) ≫
            B.inclusion.map V.1.left.hom := by
          rw [CategoryTheory.Functor.map_comp, Category.assoc]; rfl
      _ = (BigFppfOver.toScheme B S hS).map (hY.snd V.1.hom) ≫
            B.inclusion.map V.1.left.hom := by rw [htri]
      _ = B.inclusion.map ((hY.snd V.1.hom).left ≫ V.1.left.hom) := by
          rw [CategoryTheory.Functor.map_comp]; rfl
      _ = B.inclusion.map (hY.pullback V.1.hom).hom := by rw [Over.w]
  have hm := BigFppfOver.toScheme_map_homOfCompEq B S hS v hv
  refine ⟨BigFppfOver.homOfCompEq B S hS v hv, (congrArg Scheme.Hom.appTop hm).trans hvapp, ?_⟩
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
  exact (congrArg (· ≫ (BigFppfOver.toScheme B S hS).map (hZ.snd V.1.hom)) hm).trans htri

/-! ### Recognising a morphism of direct-image algebras from the chart base changes -/

/-- **A morphism over `X` whose chart base changes induce the chart values of `φ` has `φ` for its
direct-image map.**

If `f : Y ⟶ Z` is a morphism of `CategoryTheory.Over X` such that, at every étale chart `V` of
`X`, the base-changed morphism `Y ×_X V ⟶ Z ×_X V` of
`AlgebraicGeometry.Space.smallBaseChangeOverMap` induces on global regular functions the chart
value of `φ`, then `AlgebraicGeometry.Space.pushforwardAlgebraMap f = φ`.

The content is `AlgebraicGeometry.Space.pushforwardRingMap_app_eq`, which computes the left-hand
side chartwise and unconditionally; the hypothesis then equates the two chart values after
conjugation by `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`, and cancelling that
isomorphism at both ends leaves the two components equal.  A morphism of
`AlgebraicGeometry.Space.AlgebraSheaf` is determined by its underlying map of sheaves of
commutative rings, its other field being a proposition, so componentwise equality is equality.

This is the recognition principle the fullness half of Stacks 081V needs: with it, exhibiting `φ`
as a direct-image map is exhibiting a morphism over `X` with the prescribed chart base changes,
and `AlgebraicGeometry.Space.exists_chartHom_of_algebraHom` is those base changes at the affine
charts.  Gluing them, and extending the identification from the affine charts to all charts, are
what the implementation notes of this file record as absent. -/
theorem pushforwardAlgebraMap_eq_of_appTop_smallBaseChangeOverMap_eq
    {X : AlgebraicSpaces B S hS} {Y Z : Over X} (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom)
    (φ : pushforwardAlgebra B S hS Z ⟶ pushforwardAlgebra B S hS Y)
    (h : ∀ V : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (smallBaseChangeOverMap B S hS f hY hZ V)).appTop =
        (pushforwardAlgebraSectionsIso B S hS Z hZ V).inv ≫
          φ.right.hom.app (op V) ≫
          (pushforwardAlgebraSectionsIso B S hS Y hY V).hom) :
    pushforwardAlgebraMap B S hS f = φ := by
  refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext (NatTrans.ext (funext fun Vop => ?_)))
  obtain ⟨V⟩ := Vop
  exact (Iso.cancel_iso_hom_right _ _ (pushforwardAlgebraSectionsIso B S hS Y hY V)).mp
    ((Iso.cancel_iso_inv_left (pushforwardAlgebraSectionsIso B S hS Z hZ V) _ _).mp
      ((pushforwardRingMap_app_eq B S hS f hY hZ V).trans (h V)))

end AlgebraicGeometry.Space

end
