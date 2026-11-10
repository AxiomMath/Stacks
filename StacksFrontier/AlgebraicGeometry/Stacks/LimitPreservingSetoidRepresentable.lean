module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProductObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.ProductRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace

/-!
# Part (3) of Stacks 07XN: representability by an algebraic space locally of finite presentation

Stacks 07XN says that, for an algebraic stack `𝒳` over a scheme `S`, the following are
equivalent: (1) `𝒳` is a stack in setoids and its structure morphism `𝒳 ⟶ (Sch/S)_{fppf}` is
limit preserving on objects; (2) `𝒳` is a stack in setoids and is limit preserving; (3) `𝒳` is
representable by an algebraic space locally of finite presentation over `S`.

`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism` proves the implication
(2) ⟹ (1). This file proves the two implications relating (1) and (3), and the composite
(2) ⟹ (3).

Condition (3) is read here as
`AlgebraicGeometry.Stack.IsRepresentableBySpaceLocallyOfFinitePresentation`: representability by
an algebraic space, together with local finite presentation of the structure morphism
`𝒳 ⟶ (Sch/S)_{fppf}` in the relative sense of Stacks 03YK. That is the form in which the two
implications are available, and it is the form a consumer wants: the structure morphism is
representable by algebraic spaces as soon as `𝒳` is representable by an algebraic space
(Stacks 02ZZ at the final object), and Stacks 06CX is exactly the equivalence of its local finite
presentation with its being limit preserving on objects.

## Main definitions

* `AlgebraicGeometry.Stack.IsRepresentableBySpaceLocallyOfFinitePresentation`: condition (3) of
  Stacks 07XN.

## Main results

* `isStackInSetoids_and_isLimitPreservingOnObjects_of_isRepresentableBySpaceLocallyOfFinPres`:
  **Stacks 07XN**, the implication (3) ⟹ (1). Unconditional.
* `isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreservingOnObjects`: condition (3)
  for a category fibred in groupoids *already known* to be representable by an algebraic space
  whose structure morphism is limit preserving on objects. This is Stacks 06CX alone, with no cited
  hypothesis; it is the local-finite-presentation half of (1) ⟹ (3).
* `AlgebraicGeometry.Stack.isRepresentableBySpaceLocallyOfFinitePresentation_of_isStackInSetoids`:
  **Stacks 07XN**, the implication (1) ⟹ (3), with Stacks 04S6 part (3) carried as a hypothesis.
* `AlgebraicGeometry.Stack.isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreserving`:
  **Stacks 07XN**, the implication (2) ⟹ (3), the previous result preceded by the
  implication (2) ⟹ (1).
* `AlgebraicGeometry.Stack.isRepresentableBySpaceLocallyOfFinitePresentation_schemeFibredCategory`:
  condition (3) for the category fibred in groupoids represented by an object of the site whose
  structure morphism is locally of finite presentation.
* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_schemeFibredCategory`: the
  previous result through (3) ⟹ (1) — the structure 1-morphism
  `(Sch/U)_{fppf} ⟶ (Sch/S)_{fppf}` is limit preserving on objects when `U` is locally of finite
  presentation over `S`. This is the step "then `(Sch/V)_{fppf}` is limit preserving by
  Lemma 07XN" in the proof of Stacks 07XX; it carries no tag, being an application of Stacks 07XN
  rather than a clause of any tag's statement.
* `AlgebraicGeometry.Stack.isRepresentableBySpaceLocallyOfFinitePresentation_twoFibreProduct`:
  condition (3) for a 2-fibre product `𝒳 ×_𝒴 𝒵` which is representable by an algebraic space,
  when the structure morphisms of `𝒳` and `𝒵` are limit preserving on objects and `𝒴` is limit
  preserving. This is **Stacks 07XM part (1)** followed by **Stacks 06CX**.
* `isRepresentableBySpaceLocallyOfFinitePresentation_twoFibreProduct_schemeFibredCategory`: the
  previous result at `𝒵 = (Sch/V)_{fppf}`, with the representability hypothesis discharged from
  representability of `𝒳 ⟶ 𝒴` by algebraic spaces. This is the step "so `Z ⟶ S` is locally of
  finite presentation" in the proof of Stacks 07XX — the algebraic space `Z` representing
  `𝒵 = 𝒳 ×_{f, 𝒴, y} (Sch/V)_{fppf}` is locally of finite presentation over `S`. It carries no tag,
  being a step inside the proof of Stacks 07XX rather than a clause of a tag's statement.

## Implementation notes

*What each implication costs.* The setoid half of (3) ⟹ (1) is the implication (3) ⟹ (1)
of Stacks 04SZ, `AlgebraicGeometry.Stack.isStackInSetoids_of_isRepresentableByAlgebraicSpace`,
and the limit-preservation half is Stacks 06CX,
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation`, read at
the structure morphism; neither needs a hypothesis, so (3) ⟹ (1) is unconditional. The
representability half of (1) ⟹ (3) is the implication (1) ⟹ (3) of Stacks 04SZ,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`, which uses the
algebraic-stack condition (and Stacks 04S6 part (3), which is proved); the
local-finite-presentation half is again Stacks 06CX, in the other direction. So (1) ⟹ (3) and
(2) ⟹ (3) carry `IsAlgebraicStack`, and nothing else.

*Index universes.* Limit preservation on objects quantifies over the cofiltered index category,
so the condition at a larger index universe is strictly stronger. The library's form of Stacks
06CX is proved for index categories in the universe `u` of the schemes, so every statement below is
pinned there: the conclusion of (3) ⟹ (1) is limit preservation on objects at index universe
`u` only, and the hypothesis of (1) ⟹ (3) is likewise only needed there. For (2) ⟹ (3) the
hypothesis is `Deformation.Artin.IsLimitPreserving` at index universe `u`, which the
free-universe form of Stacks 07XL specialises to, so nothing is lost in taking it there.

*The 2-fibre product step of Stacks 07XX, and what it costs.* The source's sentence "so `Z ⟶ S` is
locally of finite presentation" is the composite of Stacks 07XM part (1) — which makes the
structure morphism of `𝒵 = 𝒳 ×_{f, 𝒴, y} (Sch/V)_{fppf}` limit preserving on objects out of the
same condition on `𝒳` and on `(Sch/V)_{fppf}` and limit preservation of `𝒴` — with Stacks 06CX,
which turns that into local finite presentation once the structure morphism is known to be
representable by algebraic spaces. **No hypothesis absent from the source is carried.** The
representability of `𝒵` by an algebraic space is the source's own "let `Z` be an algebraic space
representing `𝒵`", and
`isRepresentableBySpaceLocallyOfFinitePresentation_twoFibreProduct_schemeFibredCategory` derives it
exactly as the source does, from representability of `f` by algebraic spaces, through Stacks 0300
and the symmetry of the 2-fibre product in its two factors
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff`). Local finite
presentation of `V ⟶ S` is the source's own reduction step (Criteria for Representability, Lemma
07WI); the source's extra assumptions there — that `V` is affine, and that `S` is locally
Noetherian — are *not* needed and are not asked for, nor is Stacks 04S6: the representing algebraic
space is a hypothesis rather than something to be constructed, so `Bootstrap04S6Spaces` does not
appear. The index universes are pinned at `u` exactly as above, which weakens the two
limit-preservation hypotheses and leaves the conclusion at full strength. The conclusion is
condition (3) of Stacks 07XN, i.e. the relative property of Stacks 03YK for the structure morphism;
the source's literal "`Z ⟶ S` is locally of finite presentation" for one chosen representing space
is the instance of that relative property at the final object of the site, which the library does
not carry as a separate projection.

*What is still missing from Stacks 07XN.* The implications *into* (2) are not proved, here or
anywhere in this library. Both (1) ⟹ (2) and (3) ⟹ (2) ask the colimit comparison
`colim 𝒳_{Tᵢ} ⥤ 𝒳_T` of Stacks 07XL to be an equivalence, not merely essentially surjective; over
the descent conditions of `StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent` the
missing content is `Deformation.Artin.DescentHom` and `Deformation.Artin.DescentEq` for `𝒳`, which
for a stack in setoids amount to *injectivity* of the comparison of sections of the representing
sheaf, where conditions (1) and (3) give only surjectivity. That the gap is real for a general
category fibred in groupoids is
`ObjectwiseLimitPreserving.exists_stack_isLimitPreservingOnObjects_not_isLimitPreserving`
(`StacksFrontier/Examples/Stacks/ObjectwiseLimitPreserving.lean`);
the source closes it for stacks in
setoids in one sentence, and that sentence is what is not formalized.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 07WI](https://stacks.math.columbia.edu/tag/07WI)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07XM](https://stacks.math.columbia.edu/tag/07XM)
* [Stacks Project, Tag 07XN](https://stacks.math.columbia.edu/tag/07XN)
* [Stacks Project, Tag 07XX](https://stacks.math.columbia.edu/tag/07XX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **Condition (3) of Stacks 07XN.** A category fibred in groupoids over the big fppf site of
`S` is *representable by an algebraic space locally of finite presentation* when it is
representable by an algebraic space over `S` and its structure morphism to `(Sch/S)_{fppf}` is
locally of finite presentation in the relative sense of Stacks 03YK.

The structure morphism is representable by algebraic spaces as soon as `𝒳` is representable by
an algebraic space, by Stacks 02ZZ at the final object
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_toTerminalCFG`), so the relative
property can be asked of it with no further hypothesis. The witness argument of
`AlgebraicGeometry.Stack.HasRelativeProperty` is inert, so bundling the representability witness
as an existential loses nothing; this follows the spelling of
`AlgebraicGeometry.Stack.IsRelativelySmooth`. -/
abbrev IsRepresentableBySpaceLocallyOfFinitePresentation : Prop :=
  ∃ h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳,
    HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.locallyOfFinitePresentationProperty B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))
      (isRepresentableByAlgebraicSpaces_toTerminalCFG B S hS 𝒳 h𝒳)

/-- Given a representing algebraic space, condition (3) of Stacks 07XN is limit preservation on
objects of the structure morphism, by Stacks 06CX. -/
private theorem isRepresentableBySpaceLocallyOfFinitePresentation_iff_isLimitPreservingOnObjects
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsRepresentableBySpaceLocallyOfFinitePresentation B S hS 𝒳 ↔
      BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
        (terminalCFG B S hS)
        (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)) :=
  (exists_prop_of_true h𝒳).trans
    (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS 𝒳
      (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))
      (isRepresentableByAlgebraicSpaces_toTerminalCFG B S hS 𝒳 h𝒳)).symm

/-- **Stacks 07XN, the implication (3) ⟹ (1).** A category fibred in groupoids over the big fppf
site of `S` which is representable by an algebraic space locally of finite presentation over `S`
is a stack in setoids whose structure morphism to `(Sch/S)_{fppf}` is limit preserving on
objects.

The setoid clause is the implication (3) ⟹ (1) of Stacks 04SZ, and the limit-preservation clause
is Stacks 06CX read at the structure morphism. Neither algebraicity nor any cited hypothesis is
used. -/
@[stacks 07XN "the implication (3) ⟹ (1), with condition (3) read as \
`IsRepresentableBySpaceLocallyOfFinitePresentation` and limit preservation on objects for \
cofiltered index categories in the universe of the schemes, which is the scope of the library's \
form of Tag 06CX that the proof uses"]
theorem isStackInSetoids_and_isLimitPreservingOnObjects_of_isRepresentableBySpaceLocallyOfFinPres
    (h : IsRepresentableBySpaceLocallyOfFinitePresentation B S hS 𝒳) :
    𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ∧
      BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
        (terminalCFG B S hS)
        (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)) :=
  ⟨isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h.1,
    (isRepresentableBySpaceLocallyOfFinitePresentation_iff_isLimitPreservingOnObjects B S hS 𝒳
      h.1).1 h⟩

/-- **The local-finite-presentation half of Stacks 06CX, in the shape of condition (3) of
Stacks 07XN.** A category fibred in groupoids over the big fppf site of `S` which is represented
by an algebraic space and whose structure morphism to `(Sch/S)_{fppf}` is limit preserving on
objects is representable by an algebraic space locally of finite presentation over `S`.

This is Stacks 06CX read at the structure morphism, which is representable by algebraic spaces
as soon as `𝒳` is representable by an algebraic space (Stacks 02ZZ at the final object). It is
*not* the implication (1) ⟹ (3) of Stacks 07XN: representability by an algebraic space is a
hypothesis here, whereas condition (1) asks only that `𝒳` be a stack in setoids, and recovering
representability from that is what costs the algebraic-stack condition and Stacks 04S6 part (3)
in `AlgebraicGeometry.Stack.isRepresentableBySpaceLocallyOfFinitePresentation_of_isStackInSetoids`
below. -/
theorem isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreservingOnObjects
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳)
    (hlim : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))) :
    IsRepresentableBySpaceLocallyOfFinitePresentation B S hS 𝒳 :=
  (isRepresentableBySpaceLocallyOfFinitePresentation_iff_isLimitPreservingOnObjects B S hS 𝒳
    h𝒳).2 hlim

/-- **Stacks 07XN, the implication (1) ⟹ (3).** An algebraic stack over `S` which is a stack in
setoids and whose structure morphism to `(Sch/S)_{fppf}` is limit preserving on objects is
representable by an algebraic space locally of finite presentation over `S`.

The representability clause is the implication (1) ⟹ (3) of Stacks 04SZ, which uses the
algebraic-stack condition; the local-finite-presentation clause is Stacks 06CX read at the
structure morphism, and costs nothing. -/
theorem isRepresentableBySpaceLocallyOfFinitePresentation_of_isStackInSetoids
    (halg : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hset : 𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS))
    (hlim : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))) :
    IsRepresentableBySpaceLocallyOfFinitePresentation B S hS 𝒳 :=
  isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreservingOnObjects B S hS 𝒳
    (isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS 𝒳 halg hset) hlim

/-- **Stacks 07XN, the implication (2) ⟹ (3).** An algebraic stack over `S` which is a stack in
setoids and is limit preserving is representable by an algebraic space locally of finite
presentation over `S`.

This is the implication (2) ⟹ (1),
`AlgebraicGeometry.Stack.isStackInSetoids_and_isLimitPreservingOnObjects_of_isLimitPreserving`,
followed by the implication (1) ⟹ (3) above. -/
theorem isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreserving
    (halg : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hset : 𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS))
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳) :
    IsRepresentableBySpaceLocallyOfFinitePresentation B S hS 𝒳 :=
  isRepresentableBySpaceLocallyOfFinitePresentation_of_isStackInSetoids B S hS 𝒳 halg hset
    (isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B S hS 𝒳 hlim)

/-- **A slice of the site satisfies condition (3) of Stacks 07XN when the scheme it is sliced
over is locally of finite presentation.** The category fibred in groupoids represented by an
object `U` of the big fppf site of `S` is representable by an algebraic space, and its structure
morphism to `(Sch/S)_{fppf}` is locally of finite presentation in the relative sense of Stacks
03YK, as soon as `U ⟶ S` is locally of finite presentation.

Representability is `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory`
(a slice of the site is the category of elements of the presheaf of Stacks 025Z that the object
represents). For the relative property, the structure morphism of the slice is 2-isomorphic, over
the comparison of the slice of the site over its terminal object with the site itself, to the
1-morphism of represented categories induced by `U ⟶ S/S`; the relative
property of that one is Stacks 04XB read at a represented source and target
(`AlgebraicGeometry.Stack.hasRelativeProperty_schemeFibredCategoryMap`), and the morphism of
representing algebraic spaces it asks about is `yoneda.map` of a morphism of the site, for which
local finite presentation is Stacks 03XP part (1) for a morphism of the site
(`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_yoneda_map`). The transport is Stacks
0457 for the relative property,
`AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences`. -/
theorem isRepresentableBySpaceLocallyOfFinitePresentation_schemeFibredCategory
    (U : BigFppfOver B S hS)
    (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom)) :
    IsRepresentableBySpaceLocallyOfFinitePresentation B S hS
      (schemeFibredCategory B S hS U) := by
  refine ⟨isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U, ?_⟩
  -- The terminal object of the site, and the structure morphism of `U` to it.
  let T : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let g : U ⟶ T := Over.homMk U.hom (by simp [T])
  -- The comparison of the site with its slice over `T`, chosen so that it leaves the underlying
  -- object of the site unchanged; `CategoryTheory.Over.iteratedSliceBackward` composes the
  -- structure morphism with the identity instead, and is isomorphic to it.
  let b : (terminalCFG B S hS).val ⥤ᵇ (schemeFibredCategory B S hS T).val :=
    { toFunctor :=
        { obj := fun V => Over.mk (Over.homMk (V := T) V.hom (by simp [T]))
          map := fun k => Over.homMk k (Over.OverMorphism.ext (Over.w k)) }
      w := rfl }
  have : Functor.IsEquivalence b.toFunctor :=
    ((Over.iteratedSliceEquiv T).symm.changeFunctor
      (NatIso.ofComponents (fun _ => Over.isoMk (Over.isoMk (Iso.refl _)))
        : Over.iteratedSliceBackward T ≅ b.toFunctor)).isEquivalence_functor
  have : Functor.IsEquivalence
      (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 (Over U)))
  -- The 2-isomorphism of the two structure 1-morphisms over that comparison. Both send an object
  -- of the slice over `U` to its underlying object of the site, equipped with a morphism to `T`;
  -- the two morphisms to `T` agree because an object of the slice over `U` names its own
  -- structure morphism.
  let α : BasedFunctor.comp (BasedFunctor.id (schemeFibredCategory B S hS U).val)
        (schemeFibredCategoryMap B S hS g).hom ≅
      BasedFunctor.comp (toTerminalCFG B S hS (schemeFibredCategory B S hS U)) b := by
    refine BasedNatIso.mkNatIso
      (NatIso.ofComponents (fun x => Over.isoMk (Iso.refl _) ?_) ?_) ?_
    · exact Over.OverMorphism.ext ((Category.id_comp _).trans (Over.w x.hom).symm)
    · intro _ _ k
      exact Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
    · intro x
      refine IsHomLift.of_fac _ _ _ rfl rfl ?_
      change (𝟙 x.left : x.left ⟶ x.left) = 𝟙 x.left ≫ 𝟙 x.left ≫ 𝟙 x.left
      simp
  exact hasRelativeProperty_of_equivalences.{u, u, u, u + 1, u + 1, u} B S hS
    (Space.locallyOfFinitePresentationProperty B S hS)
    (Bicategory.InducedBicategory.mkHom
      (toTerminalCFG B S hS (schemeFibredCategory B S hS U)))
    (schemeFibredCategoryMap B S hS g)
    (BasedFunctor.id (schemeFibredCategory B S hS U).val) b α
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g)
    (isRepresentableByAlgebraicSpaces_toTerminalCFG B S hS _
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U))
    (hasRelativeProperty_schemeFibredCategoryMap.{u, u} B S hS
      (Space.locallyOfFinitePresentationProperty B S hS) g
      (Space.isLocallyOfFinitePresentation_yoneda_map B S hS g hU))

/-- **The structure 1-morphism of a slice of the site is limit preserving on objects when the
scheme it is sliced over is locally of finite presentation.** For an object `U` of the big fppf
site of `S` whose structure morphism to `S` is locally of finite presentation, the 1-morphism
`(Sch/U)_{fppf} ⟶ (Sch/S)_{fppf}` satisfies the descent condition of Stacks 06CU.

This is the sentence "then `(Sch/V)_{fppf}` is limit preserving by Lemma 07XN" in the proof of
Stacks 07XX, in the form the rest of that proof uses it: the implication (3) ⟹ (1) of
Stacks 07XN applied to the category fibred in groupoids represented by `U`, whose condition (3) is
`AlgebraicGeometry.Stack.isRepresentableBySpaceLocallyOfFinitePresentation_schemeFibredCategory`.
The source's statement there is the stronger "limit preserving" of Stacks 07XL, which would be
the implication (3) ⟹ (2); that implication is not available in this library (see the module
documentation), and limit preservation on objects is what Stacks 07WI and Stacks 07WH — the
consumers inside the proof of Stacks 07XX — ask for. -/
theorem isLimitPreservingOnObjects_toTerminalCFG_schemeFibredCategory
    (U : BigFppfOver B S hS)
    (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom)) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS
      (schemeFibredCategory B S hS U) (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS (schemeFibredCategory B S hS U))) :=
  (isStackInSetoids_and_isLimitPreservingOnObjects_of_isRepresentableBySpaceLocallyOfFinPres
    B S hS (schemeFibredCategory B S hS U)
    (isRepresentableBySpaceLocallyOfFinitePresentation_schemeFibredCategory B S hS U hU)).2

section TwoFibreProduct

variable (𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (pf : 𝒳 ⟶ 𝒴) (qf : 𝒵 ⟶ 𝒴)

/-- **A 2-fibre product of categories fibred in groupoids limit preserving on objects over a
limit preserving base satisfies condition (3) of Stacks 07XN as soon as it is representable by
an algebraic space at all.** If the structure morphisms of `𝒳` and of `𝒵` to `(Sch/S)_{fppf}`
are limit preserving on objects, `𝒴` is limit preserving, and `𝒳 ×_𝒴 𝒵` is representable by an
algebraic space over `S`, then that algebraic space is locally of finite presentation over `S`.

Stacks 07XM part (1),
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_twoFibreProduct`, makes the
structure morphism of `𝒳 ×_𝒴 𝒵` limit preserving on objects; Stacks 06CX, through
`isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreservingOnObjects`, turns that into
local finite presentation. No cited hypothesis is used, and in particular Stacks 04S6 part (3) is
not: the representing algebraic space is assumed, not constructed.

The representability hypothesis `hrep` is the source's own "let `Z` be an algebraic space
representing `𝒵`" in the proof of Stacks 07XX; it is discharged, as the source discharges it, in
`isRepresentableBySpaceLocallyOfFinitePresentation_twoFibreProduct_schemeFibredCategory` below. The
two limit-preservation hypotheses are taken at cofiltered index categories in the universe `u` of
the schemes, which is all the library's form of Stacks 06CX supports and is the weaker of the two
readings, so nothing is lost. -/
theorem isRepresentableBySpaceLocallyOfFinitePresentation_twoFibreProduct
    (hrep : IsRepresentableByAlgebraicSpace B S hS
      (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 pf qf))
    (h𝒳 : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)))
    (h𝒵 : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒵
      (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒵)))
    (h𝒴 : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒴) :
    IsRepresentableBySpaceLocallyOfFinitePresentation B S hS
      (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 pf qf) :=
  isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreservingOnObjects B S hS _ hrep
    (isLimitPreservingOnObjects_toTerminalCFG_twoFibreProduct.{u, u, u} B S hS 𝒳 𝒴 𝒵 pf qf
      h𝒳 h𝒵 h𝒴)

/-- **The step "so `Z ⟶ S` is locally of finite presentation" in the proof of Stacks 07XX.** Let
`pf : 𝒳 ⟶ 𝒴` be representable by algebraic spaces, let `V` be an object of the big fppf site of
`S` whose structure morphism `V ⟶ S` is locally of finite presentation, and let `y` be an object
of `𝒴` over `V`, that is, a 1-morphism `(Sch/V)_{fppf} ⟶ 𝒴`. If the structure morphism of `𝒳` to
`(Sch/S)_{fppf}` is limit preserving on objects and `𝒴` is limit preserving, then
`𝒵 = 𝒳 ×_{pf, 𝒴, y} (Sch/V)_{fppf}` is representable by an algebraic space `Z` which is locally
of finite presentation over `S`.

This is the source's two sentences "Then `(Sch/V)_{fppf}` is limit preserving by Lemma 07XN, so
`Z ⟶ S` is locally of finite presentation by Lemmas 07XM and 06CX". The first is
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_schemeFibredCategory`, in the
limit-preserving-on-objects form that Stacks 07XM part (1) consumes; the second is
`AlgebraicGeometry.Stack.isRepresentableBySpaceLocallyOfFinitePresentation_twoFibreProduct`. The
representing algebraic space comes from Stacks 0300,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct`, read after exchanging
the two factors of the 2-fibre product
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff`), since
Stacks 0300 is stated with the represented factor first.

**No hypothesis that the source does not have is carried.** All four hypotheses below are the
source's: representability of `pf` by algebraic spaces, local finite presentation of `V ⟶ S`
(the source's own reduction step, Stacks 07WI), limit preservation on objects for `𝒳`, and limit
preservation for `𝒴`. The source's affineness of `V` and locally Noetherian `S` are not needed
and are not assumed, and neither is Stacks 04S6 part (3). The two limit-preservation hypotheses
are read at cofiltered index categories in the universe `u` of the schemes, which is the weaker
reading and is the scope of the library's form of Stacks 06CX.

The conclusion is condition (3) of Stacks 07XN, that is, the relative property of Stacks 03YK
for the structure morphism of `𝒵`. The source's literal statement about one chosen representing
space `Z` is the instance of that relative property at the final object of the site; the library
has no separate projection to it. -/
theorem isRepresentableBySpaceLocallyOfFinitePresentation_twoFibreProduct_schemeFibredCategory
    (V : BigFppfOver B S hS)
    (hV : LocallyOfFinitePresentation (B.inclusion.map V.hom))
    (y : schemeFibredCategory B S hS V ⟶ 𝒴)
    (hpf : IsRepresentableByAlgebraicSpaces B S hS pf.hom)
    (h𝒳 : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)))
    (h𝒴 : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒴) :
    IsRepresentableBySpaceLocallyOfFinitePresentation B S hS
      (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴
        (schemeFibredCategory B S hS V) pf y) :=
  isRepresentableBySpaceLocallyOfFinitePresentation_twoFibreProduct B S hS 𝒳 𝒴
    (schemeFibredCategory B S hS V) pf y
    ((isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff B S hS 𝒴
      (schemeFibredCategory B S hS V) 𝒳 y.hom pf.hom).1
        (isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴
          (schemeFibredCategory B S hS V) 𝒳 y.hom pf.hom hpf
          (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)))
    h𝒳 (isLimitPreservingOnObjects_toTerminalCFG_schemeFibredCategory B S hS V hV) h𝒴

end TwoFibreProduct

end AlgebraicGeometry.Stack

end
