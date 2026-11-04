module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.CompletedLocalSpectrum
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingChartPoint

/-!
# The morphism attached to a versal ring at a chart point, and its flatness

In the versal situation of **Stacks 0DQU** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — **Stacks 0DR1** observes that the versal formal object over a
versal ring `A` to `𝒳` at a finite type field-valued point `x₀` comes from a morphism
`Spec A ⟶ 𝒳`, and lists four compatibilities of that morphism with the earlier results of the
section. Its clause (3) concerns the versal ring produced by **Stacks 0DQZ** from a scheme chart
`x : U ⟶ 𝒳` versal at a finite type point `u₀`, namely the completion `𝒪^∧_{U, u₀}`: there the
morphism `Spec(𝒪^∧_{U, u₀}) ⟶ 𝒳` is the composition of the canonical map
`Spec(𝒪^∧_{U, u₀}) ⟶ U` with the given `x`. **Stacks 0DR2** then asserts that the morphism
`Spec A ⟶ 𝒳` is flat for every versal ring `A`.

This file proves clause (3), and proves flatness of the morphism in the chart case — the final
computation of Step III of the proof of Stacks 0DR2, `Spec(𝒪^∧_{U, u₀}) ⟶ U ⟶ 𝒳` with the first
arrow flat because a Noetherian local ring is flat over nothing but itself after completion and
the second flat because the chart is smooth.

The input is the presentation of `𝒪^∧_{U, u₀}` that this part of the tree uses throughout: a
complete local object `xR` of `𝒳` together with a Cartesian arrow `r : xR ⟶ x` whose underlying
morphism of schemes is the canonical map `Spec(𝒪^∧_{U, u₀}) ⟶ U`, read through a ring
isomorphism `e` of the completion onto the chosen complete local base of `xR`. That object `xR`
*is* the morphism `Spec(𝒪^∧_{U, u₀}) ⟶ 𝒳` of Stacks 0DR1: it realizes the formal object the
approximation functor of **Stacks 07X6** attaches to it, so that formal object is effective
(**Stacks 07X7**), and the 1-morphism it names under the 2-Yoneda lemma is the one in question.

## Main results

* `AlgebraicGeometry.Stack.isEffective_and_objectMorphism_completion_factors`: **Stacks 0DR1**,
  the morphism `Spec(𝒪^∧_{U, u₀}) ⟶ 𝒳` and its clause (3).
* `AlgebraicGeometry.Stack.flat_schemeMap_completeLocalRestriction`: the morphism of schemes
  underlying `r` is flat.
* `AlgebraicGeometry.Stack.flatObject_completeLocalRestriction`: the morphism
  `Spec(𝒪^∧_{U, u₀}) ⟶ 𝒳` is flat as soon as `x : U ⟶ 𝒳` is.
* `AlgebraicGeometry.Stack.flatObject_completeLocalRestriction_of_smoothObject`: the same with a
  smooth chart, which is the hypothesis Step III of Stacks 0DR2 arranges.
* `AlgebraicGeometry.Stack.exists_flat_isVersalRingAt_completion_of_isVersalAt`: the two
  conclusions together with the presentation produced rather than supplied — the completion is a
  versal ring to `𝒳` at the point it determines, and the morphism from its spectrum is flat.

## What this file does not contain

Stacks 0DR2 for an arbitrary versal ring is not here, and neither are the clauses (1), (2) and
(4) of Stacks 0DR1. What they need beyond this file:

* the existence of the morphism `Spec A ⟶ 𝒳` for an arbitrary versal ring `A` is effectivity of
  its versal formal object, i.e. essential surjectivity of the approximation functor of
  **Stacks 07X8**; the tree has that functor's faithfulness and its fullness for a represented
  category fibred in groupoids, and nothing else — see the implementation notes of
  `StacksFrontier.Deformation.Artin.FormalObject.ApproximationRepresentable`. Here the morphism is
  not quoted from Stacks 07X8 but is the complete local object the presentation supplies, which
  is why the chart case needs nothing of it.
* clauses (1) and (2) of Stacks 0DR1 are the compatible forms of **Stacks 0DQX** (Lemma 107.2.4)
  and **Stacks 0DQY** (Lemma 107.2.5), neither of which is realized in the tree; clause (4) is
  the compatible form of **Stacks 0DR0** (Lemma 107.2.8, Artin approximation), also absent.
* Steps I and II of the proof of Stacks 0DR2 reduce an arbitrary versal ring to a chart
  completion, and they run on exactly those compatible forms together with descent of flatness
  along the faithfully flat `Spec A' ⟶ Spec A`. So the reduction of the general statement to the
  computation proved here is what is missing, not the computation.

## Implementation notes

Flatness of a 1-morphism `Spec(𝒪^∧_{U, u₀}) ⟶ 𝒳` is `AlgebraicGeometry.Stack.flatObject`
(**Stacks 0H14**), flatness of the 1-morphism an object names under the 2-Yoneda lemma, and the
step from flatness of the morphism of schemes to it is
`AlgebraicGeometry.Stack.flatObject_of_flat`: that lemma is Stacks 0788's closure condition and
its proof is the one Step III gives, composition of 1-morphisms through
`AlgebraicGeometry.Stack.objectMorphismFactorIso`. So the only thing to supply is flatness of the
morphism of schemes underlying `r`, which through the presentation is
`AlgebraicGeometry.Scheme.fromSpecCompletedLocalRing` — flat by
`AlgebraicGeometry.Scheme.flat_fromSpecCompletedLocalRing`, which is the source's "completion of
Noetherian local rings are flat" composed with flatness of `Spec 𝒪_{U, u₀} ⟶ U` — precomposed
with the spectrum of a ring isomorphism.

Two `eqToHom`s separate that morphism of schemes from the one the presentation equation is stated
at: the chosen complete local base of `xR` is compared with `Spec(𝒪^∧_{U, u₀})` only up to the
equality `Deformation.Artin.chosenBase_eq`, and the scheme `x` lies over with `U` only up to
`hx`. Both are eliminated by `subst` in a private lemma with the two objects as variables, as in
`StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily`; no transparency option and no
`MorphismProperty.RespectsIso` instance for flatness of morphisms of schemes is needed.

`IsOpenImmersion` is pinned to the root namespace in the last statement: this module imports the
flat-fppf site, which brings `AlgebraicGeometry.Stack.IsOpenImmersion` — open immersions of
algebraic stacks — into scope, and the unqualified name then resolves to that one.

## References

* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
* [Stacks Project, Tag 0DQU](https://stacks.math.columbia.edu/tag/0DQU)
* [Stacks Project, Tag 0DQZ](https://stacks.math.columbia.edu/tag/0DQZ)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
* [Stacks Project, Tag 0DR2](https://stacks.math.columbia.edu/tag/0DR2)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

section CompleteLocalRestriction

variable (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
  (U : Over D.S) [LocallyOfFiniteType U.hom]
  (x : D.𝒳.val.val.obj)
  (hx : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x = U)
  (u₀ : U.left)
  (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
  (r : xR.obj.1 ⟶ x)
  (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+*
    (Deformation.Artin.chosenBase D.B D.S D.hS D.𝒳.val.val.p xR.obj).R)
  (hrbase : ((eqToHom (Deformation.Artin.chosenBase_eq D.B D.S D.hS
        D.𝒳.val.val.p xR.obj).symm ≫ D.𝒳.val.val.p.map r).left.hom ≫
      eqToHom (congrArg Over.left hx)) =
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
        (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
      U.left.fromSpecStalk u₀)

/-- Flatness of a morphism of schemes is unaffected by postcomposition with the comparison
isomorphism of an equality of its target: the equality can be eliminated, and the comparison
isomorphism is then the identity. -/
private theorem flat_of_comp_eqToHom {X Y Y' : Scheme.{u}} (h : Y = Y') (f : X ⟶ Y)
    (hf : Flat (f ≫ eqToHom h)) : Flat f := by
  subst h
  simpa using hf

omit [LocallyOfFiniteType U.hom] in
/-- Flatness of the morphism of schemes underlying a morphism of the big fppf category over `S`
is unaffected by precomposition with the comparison isomorphism of an equality of objects. -/
private theorem flat_inclusionMap_left_of_eqToHom_comp
    {V V' X : BigFppfOver D.B D.S D.hS} (h : V = V') (m : V' ⟶ X)
    (hm : Flat (D.B.inclusion.map (eqToHom h ≫ m).left)) :
    Flat (D.B.inclusion.map m.left) := by
  subst h
  simpa using hm

include hrbase in
/-- **The restriction of a chart to the completion at a point lies over a flat morphism of
schemes.** Through the presentation `e`, the morphism of schemes underlying `r` is the spectrum
of a ring isomorphism followed by the canonical morphism `Spec(𝒪^∧_{U, u₀}) ⟶ U`, which is flat
because the completion of a Noetherian local ring is flat over it and `Spec 𝒪_{U, u₀} ⟶ U` is
flat. This is the first of the two arrows in the final computation of Step III of the proof of
**Stacks 0DR2**. -/
theorem flat_schemeMap_completeLocalRestriction :
    Flat (D.B.inclusion.map (D.𝒳.val.val.p.map r).left) := by
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have he : Flat (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_bijective e.bijective)
  have hc : Flat (U.left.fromSpecCompletedLocalRing u₀) :=
    AlgebraicGeometry.Scheme.flat_fromSpecCompletedLocalRing u₀
  have hcomp : Flat (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      U.left.fromSpecCompletedLocalRing u₀) := Flat.comp _ _
  have hdef : U.left.fromSpecCompletedLocalRing u₀ =
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
        (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀ := rfl
  rw [hdef, ← hrbase] at hcomp
  have h1 := flat_of_comp_eqToHom (congrArg Over.left hx) _ hcomp
  exact flat_inclusionMap_left_of_eqToHom_comp D
    (Deformation.Artin.chosenBase_eq D.B D.S D.hS D.𝒳.val.val.p xR.obj).symm
    (D.𝒳.val.val.p.map r) h1

omit [LocallyOfFiniteType U.hom] in
include hrbase in
/-- **Stacks 0DR1 at the versal ring of Stacks 0DQZ, and its clause (3).** In the versal
situation, let `x` be an object of `𝒳` over a scheme `U` locally of finite type over `S`, let
`u₀` be a point of `U`, and let `xR` be a complete local object restricting `x` over the
canonical morphism `Spec(𝒪^∧_{U, u₀}) ⟶ U`. Then the formal object `ξ` the approximation functor
of **Stacks 07X6** attaches to `xR` is effective, so the versal formal object of **Stacks 0DQZ**
comes from a morphism `Spec(𝒪^∧_{U, u₀}) ⟶ 𝒳` — the 1-morphism `xR` names under the 2-Yoneda
lemma — and that morphism is the composition of the canonical map `Spec(𝒪^∧_{U, u₀}) ⟶ U` with
the given map `U ⟶ 𝒳`.

The three conclusions are the three halves of the statement: effectivity, which is the preamble
of the remark; the identification of the morphism of the site that `r` lies over with the
canonical morphism `AlgebraicGeometry.Scheme.fromSpecCompletedLocalRing` of the completion, read
through the presentation `e`; and the 2-isomorphism of 1-morphisms, which is the 2-Yoneda
functoriality `AlgebraicGeometry.Stack.objectMorphismFactorIso` of **Stacks 004B** at `r`. As the
remark notes, the diagram only 2-commutes, after a choice of 2-arrow, which is why the third
conclusion is a `Nonempty` of isomorphisms rather than an equality. -/
@[stacks 0DR1 "the morphism Spec(A) ⟶ 𝒳 of the remark at the versal ring A = 𝒪^∧_{U,u₀} of \
Stacks 0DQZ, and clause (3): that morphism is the composition of the canonical map \
Spec(𝒪^∧_{U,u₀}) ⟶ U with the given map U ⟶ 𝒳"]
theorem isEffective_and_objectMorphism_completion_factors
    (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property).obj xR) :
    Deformation.Artin.FormalObject.IsEffective D.B D.S D.hS D.𝒳.val.val.p
        D.𝒳.val.property ξ ∧
      ((eqToHom (Deformation.Artin.chosenBase_eq D.B D.S D.hS
            D.𝒳.val.val.p xR.obj).symm ≫ D.𝒳.val.val.p.map r).left.hom ≫
          eqToHom (congrArg Over.left hx)) =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          U.left.fromSpecCompletedLocalRing u₀ ∧
      Nonempty (objectMorphism D.B D.S D.hS D.𝒳.val
          (Functor.Fiber.mk (a := xR.obj.1) rfl) ≅
        schemeFibredCategoryMap D.B D.S D.hS (D.𝒳.val.val.p.map r) ≫
          objectMorphism D.B D.S D.hS D.𝒳.val (Functor.Fiber.mk (a := x) rfl)) :=
  ⟨⟨xR, ⟨eqToIso hξ.symm⟩⟩, hrbase,
    ⟨objectMorphismFactorIso D.B D.S D.hS D.𝒳.val r⟩⟩

include hrbase in
/-- **The morphism `Spec(𝒪^∧_{U, u₀}) ⟶ 𝒳` is flat when the chart is.** This is the final
computation of Step III of the proof of **Stacks 0DR2**: the morphism is the composition
`Spec(𝒪^∧_{U, u₀}) ⟶ U ⟶ 𝒳` of the previous lemma, the first arrow is flat by
`AlgebraicGeometry.Stack.flat_schemeMap_completeLocalRestriction` and the second by hypothesis,
and flatness of 1-morphisms is stable under composition — which is
`AlgebraicGeometry.Stack.flatObject_of_flat`.

This is not the whole of Stacks 0DR2, which asserts flatness for an arbitrary versal ring at an
arbitrary finite type field-valued point; it is the case of the versal ring that **Stacks 0DQZ**
produces from a chart, and Steps I and II of the source's proof, which reduce the general case to
it, are what the tree lacks. See the section "What this file does not contain" of this module. -/
theorem flatObject_completeLocalRestriction
    (hxflat : flatObject D.B D.S D.hS D.𝒳.val x) :
    flatObject D.B D.S D.hS D.𝒳.val xR.obj.1 :=
  flatObject_of_flat D.B D.S D.hS D.𝒳 r
    (flat_schemeMap_completeLocalRestriction D U x hx u₀ xR r e hrbase) hxflat

include hrbase in
/-- **The morphism `Spec(𝒪^∧_{U, u₀}) ⟶ 𝒳` is flat at a point of a smooth chart.** Step III of
the proof of **Stacks 0DR2** chooses the chart `U ⟶ 𝒳` smooth and surjective, and uses only that
a smooth 1-morphism is flat (**Stacks 04TA**); this is that reading of
`AlgebraicGeometry.Stack.flatObject_completeLocalRestriction`. -/
theorem flatObject_completeLocalRestriction_of_smoothObject
    (hxsmooth : smoothObject.{u, w} D.B D.S D.hS D.𝒳 x) :
    flatObject D.B D.S D.hS D.𝒳.val xR.obj.1 :=
  flatObject_completeLocalRestriction D U x hx u₀ xR r e hrbase
    (flatObject_of_smoothObject.{u, w} D.B D.S D.hS D.𝒳 hxsmooth)

end CompleteLocalRestriction

/-- **Stacks 0DR2 at the versal ring of Stacks 0DQZ, with the presentation produced.** In the
versal situation, let `x` be an object of `𝒳` over a scheme `U` of finite type over `S`, let `u₀`
be a finite type point of `U` whose completed local ring lies in the chosen big fppf site, and
let `Spec Λ ⊆ S` be an affine open containing the image of `u₀`. If `x` is versal at `u₀` and is
a flat object of `𝒳`, then there are a formal object `ξ` of `𝒳`, a presentation `e` of
`𝒪^∧_{U, u₀}` by its complete local base and a `Λ`-algebra structure on that base over `S` for
which `ξ` is effective, realized by a complete local object whose morphism to `𝒳` is flat, and
for which `𝒪^∧_{U, u₀}` is a versal ring to `𝒳` at the point `x₀` determined by `u₀`.

Quasi-compactness of `U ⟶ S` is assumed because it is what
`Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint` needs in order to restrict
`x` over the completion at all, exactly as in
`AlgebraicGeometry.Stack.exists_isVersalRingAt_completion_of_isVersalAt`, whose versal-ring
conclusion this statement repeats; neither Stacks 0DQZ nor Stacks 0DR2 assumes it, so this
declaration carries no tag. Flatness of the chart is also a hypothesis rather than a consequence
of versality: the implication from versality at `u₀` to smoothness of `x` after shrinking `U` is
clause (4) of Stacks 0DQZ, which needs Artin's Axioms, Lemma 98.12.6 (**Stacks 0CXM**) and has no
realization in the tree. -/
theorem exists_flat_isVersalRingAt_completion_of_isVersalAt
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    (U : Over D.S) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (x : D.𝒳.val.val.obj)
    (hx : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x = U)
    (u₀ : U.left) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hC : D.B.Contains
      (Spec (.of (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))))
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (H : Set.range (U.left.fromSpecResidueField u₀ ≫ U.hom).base ⊆ Set.range iΛ.base)
    (hversal : Deformation.Artin.IsVersalAt U
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x hx)
    (hxflat : flatObject D.B D.S D.hS D.𝒳.val x) :
    ∃ (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
      (_e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* ξ.base.R)
      (alg : Algebra Λ ξ.base.R),
      letI := alg
      ∃ hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS,
        (∃ xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p,
          ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
              D.𝒳.val.property).obj xR ∧
            flatObject D.B D.S D.hS D.𝒳.val xR.obj.1) ∧
        IsVersalRingAt D iΛ hiΛ (ξ.level 0) (ξ.basePoint Λ iΛ hΛ)
          (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
          (ξ.completeLocalBase Λ) := by
  have := hiΛ
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  obtain ⟨xR, r, e₀, hr, hrbase₀, hbase₀⟩ :=
    Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint D.B D.S D.hS
      D.𝒳.val.val.p D.𝒳.val.property U x hx u₀ hu₀ hC
  set ξ := (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
    D.𝒳.val.property).obj xR
  obtain ⟨e, hrbase, hbase, hs⟩ := Deformation.Artin.exists_approximationBase_presentation
    D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property U x hx u₀ xR ξ rfl r e₀ hrbase₀ hbase₀
  have hmem : Deformation.Artin.basePoint U u₀ ∈ Set.range iΛ.base :=
    H ⟨IsLocalRing.closedPoint (U.left.residueField u₀), rfl⟩
  obtain ⟨alg, hΛ⟩ := exists_algebra_of_formalBase_mem_range ξ.base iΛ hiΛ (hs ▸ hmem)
  obtain ⟨t, ht⟩ := hmem
  let _ := alg
  let _ := Deformation.Artin.chartResidueAlgebra iΛ U u₀ H
  refine ⟨ξ, e, alg, hΛ, ⟨xR, rfl, ?_⟩, ?_⟩
  · exact flatObject_completeLocalRestriction D U x hx u₀ xR r e₀ hrbase₀ hxflat
  · exact (isVersalRingAt_completeLocalBase D U x hx u₀ xR ξ rfl e
      (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀) rfl hbase r hr hrbase Λ iΛ hiΛ hΛ t ht
      (Deformation.Artin.algebraMap_chartResidueAlgebra iΛ U u₀ H) hversal).2

end AlgebraicGeometry.Stack

end
