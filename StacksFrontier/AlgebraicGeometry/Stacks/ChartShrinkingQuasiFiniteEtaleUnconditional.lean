module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyLocusOnSpaces
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothDiagramRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalSourceLemmaInstances
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalSourceLemmaUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteNotionsAgree
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange

/-!
# Shrinking a chart to a locally quasi-finite or étale one, unconditionally (Stacks 06ME, 06N2)

`StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingQuasiFiniteEtale.lean` states **Stacks 06ME**
and **Stacks 06N2** with the open locus `W(f)` of **Stacks 06M5** and its compatibility with the
base change along the field-valued point carried as hypotheses. This file proves both with
nothing carried: the locus is produced inside the proof as the locus `W(𝒫, f)` of assertion (A)
of **Stacks 06M3**
(`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces`),
at `𝒫 = ` locally quasi-finite for Stacks 06ME and at `𝒫 = ` unramified for Stacks 06N2, and the
membership of the image of the given point of the fibre is the maximality half of assertion (B),
`AlgebraicGeometry.Stack.pointSet_subset_preimage_of_hasRelativeProperty`. The conclusions are
stated existentially, as the source states them.

## Main results

* `AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite_unconditional`: Stacks 06ME
  at the neighbourhood condition `AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear` its proof
  extracts from `dim_z(F) = 0`; the registration of Stacks 06ME sits on
  `AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite_of_dimensionAtPoint_eq_zero`
  of `StacksFrontier/AlgebraicGeometry/Stacks/FibreQuasiFiniteNearSubstack.lean`.
* `AlgebraicGeometry.Stack.exists_openSubstack_isEtale_unconditional`: **Stacks 06N2**.

## References

* [Stacks, Tag 06ME], [Stacks, Tag 06N2], [Stacks, Tag 06M3], [Stacks, Tag 06M5]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)

variable (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

/-- **Stacks 06ME at the intermediate condition of its own proof.** Let `𝒳` be an algebraic
stack, let `U` be an algebraic space with a 1-morphism `f : U ⟶ 𝒳` which is locally of finite
type, let `Spec k ⟶ 𝒳` be a field-valued point, and let `F = U ×_𝒳 Spec k` with projection
`p : F ⟶ U` and structure 1-morphism `q : F ⟶ Spec k`. If some open substack of `F` containing
`z ∈ |F|` is locally quasi-finite over `Spec k` then, after replacing `U` by an open subspace
containing `p(z)`, the 1-morphism `U ⟶ 𝒳` is locally quasi-finite.

The fibre hypothesis is `AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear`, which is not
the source's `dim_z(F) = 0` but the condition the source's own proof extracts from it by
**Stacks 04NV**. The `@[stacks 06ME]` registration therefore sits not here but on
`AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite_of_dimensionAtPoint_eq_zero`
of `StacksFrontier/AlgebraicGeometry/Stacks/FibreQuasiFiniteNearSubstack.lean`, which is this
declaration composed with
`AlgebraicGeometry.Stack.fibreIsLocallyQuasiFiniteNear_of_dimensionAtPoint_eq_zero`, the step
that takes `dim_z(F) = 0` to the hypothesis below.

The finite-type hypothesis is the source's and nothing is carried: the conclusion is stated
existentially, as the source states it. The source's statement names no open subspace of `U` —
the locus `W(f)`
enters only in the source's *proof*, through Properties of Stacks, Remark 100.9.20(2) — and it
enters here the same way. The `W` exhibited is the locus `W(𝒫, f)` of assertion (A) of
**Stacks 06M3** at `𝒫 = ` locally quasi-finite, supplied by
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces` at
the **Stacks 06M5** entry-(2) instances of
`StacksFrontier/AlgebraicGeometry/Stacks/LocalSourceLemmaInstances.lean`; it is unique
by `AlgebraicGeometry.Stack.eq_of_isRelativePropertyLocus`. The first clause of
`AlgebraicGeometry.Stack.IsRelativePropertyLocus`, that `f` restricted to `W` has the relative
property, gives the local quasi-finiteness of `f|_W` across
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom`; the
second, that every open substack with the property is contained in `W`, is the maximality the
base-change step below consumes.

That `p(z) ∈ |W|` is assertion (B) of Stacks 06M3 — its
maximality half, `AlgebraicGeometry.Stack.pointSet_subset_preimage_of_hasRelativeProperty` — at
the open substack of `F` that the fibre hypothesis supplies, which contains `z` and is locally
quasi-finite over `Spec k`. The finite-type hypothesis is the source's `𝒬` for `f`, turned into
the relative property Stacks 06M3 consumes by **Stacks 06FM**
(`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_relative`), and the base change is
performed at the given 2-fibre product square read over the reversed cospan.

The source's open *subspace* of `U` is rendered as an open substack of the stack of `U`, and both
directions of that passage are now in the library, so the `W` below does come from an open
subspace of `U`:
`AlgebraicGeometry.Stack.exists_isOpenSubspace_property_eq_essImage` exhibits one whose induced
1-morphism has `W` for its essential image and whose point set is `|W|`. The transport of the
local quasi-finiteness below along the **Stacks 0506** factorization of that 1-morphism through
`W.inclusion` is `AlgebraicGeometry.Stack.isLocallyQuasiFinite_comp_of_eq_essImage`, and the
conclusion read on that open subspace is
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isLocallyQuasiFinite`, both of
`StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingOpenSubspace.lean`. -/
theorem exists_openSubstack_isLocallyQuasiFinite_unconditional
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (z : AlgebraicStacks.points B S hS (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g))
    (hz : FibreIsLocallyQuasiFiniteNear.{u, w} B S hS 𝒳 U hU k hk toBase f g z) :
    ∃ W : OpenSubstack (algebraicSpaceStack.{u, w} B S hS U hU),
      AlgebraicStacks.pointsMap B S hS
          (fibreProjection B S hS 𝒳 U hU k hk toBase f g) z ∈ W.pointSet B S hS ∧
        AlgebraicStacks.IsLocallyQuasiFinite B S hS (W.inclusion ≫ f) := by
  obtain ⟨V, hzV, hVqf⟩ := hz
  -- Hypotheses (1) and (2) of the source are read at `ℛ = ⊤`, where every clause is `True`.
  have : (⊤ : MorphismProperty (AlgebraicSpaces B S hS)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    { pullbackSnd := fun _ _ _ => trivial
      of_forall_pullbackSnd := fun _ _ => trivial }
  have : (Space.locallyOfFiniteTypeProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  -- the two 1-morphisms of the cospan and the base change of `f` are representable
  have hf' : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS 𝒳 U hU f
  have hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS
        (fieldPointObject B S hS k hk toBase)) g.hom
  have hD : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquareAlgebraicStacks B S hS f g).swap :=
    Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)
  have hfst : IsRepresentableByAlgebraicSpaces B S hS
      ((twoFibreProductSquareAlgebraicStacks B S hS f g).swap).fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ f.hom g.hom
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS
        ((twoFibreProductSquareAlgebraicStacks B S hS f g).swap))
      (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS _ hD) hf'
  -- `𝒬 = ` locally of finite type for `f`: the universal smooth-diagram test of Stacks 06FS is
  -- the relative property of Stacks 03YK, by Stacks 06FM
  have hQf : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.locallyOfFiniteTypeProperty B S hS) f.hom hf' :=
    (hasPropertyOnEverySmoothDiagram_iff_relative B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (algebraicSpaceStack.{u, w} B S hS U hU).property 𝒳.property f.hom hf').1 hf
  -- the locus `W(𝒫, f)` of assertion (A) of Stacks 06M3, at `𝒫 = ` locally quasi-finite
  obtain ⟨W, hWlocus⟩ :=
    exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces B S hS
    (Space.locallyQuasiFiniteProperty B S hS) (Space.locallyOfFiniteTypeProperty B S hS) ⊤
    (fun _ _ _ _ _ _ => trivial)
    (hasRelativePropertyLocusOnSpaces_isLocallyQuasiFinite B S hS)
    (relativePropertyLocusBaseChange_isLocallyQuasiFinite B S hS) f hf' hQf
  refine ⟨W, ?_,
    (AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom B S hS (W.inclusion ≫ f)
      (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS f hf' W)).2
      hWlocus.1⟩
  exact pointSet_subset_preimage_of_hasRelativeProperty B S hS
    (Space.locallyQuasiFiniteProperty B S hS) (Space.locallyOfFiniteTypeProperty B S hS) ⊤
    (fun _ _ _ _ _ _ => trivial)
    (hasRelativePropertyLocusOnSpaces_isLocallyQuasiFinite B S hS)
    (relativePropertyLocusBaseChange_isLocallyQuasiFinite B S hS)
    hQf (fun _ _ _ _ _ _ => trivial) (hg := hg)
    ((twoFibreProductSquareAlgebraicStacks B S hS f g).swap) hD (hfst := hfst) hWlocus V
    ((AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom B S hS
      (V.inclusion ≫ fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g)
      (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS
        (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g) hfst V)).1 hVqf)
    hzV

/-- **Stacks 06N2.** Let `𝒳` be an algebraic stack, let `U` be an algebraic space with a
1-morphism `f : U ⟶ 𝒳` which is flat and locally of finite presentation, let `Spec k ⟶ 𝒳` be a
field-valued point, and let `F = U ×_𝒳 Spec k` with projection `p : F ⟶ U` and structure
1-morphism `q : F ⟶ Spec k`. If `q` is unramified at `z ∈ |F|` then, after replacing `U` by an
open subspace containing `p(z)`, the 1-morphism `U ⟶ 𝒳` is étale.

The proof is the source's, and nothing is carried. The open substack `W` is the locus `W(𝒫, f)`
of assertion (A) of **Stacks 06M3** at `𝒫 = ` **unramifiedness** — the entry of the list of
**Stacks 06M5** whose base-change clause holds for an *arbitrary* base change, and so the entry
that applies to the base change along a field-valued point. It exists by
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces` at
the entry-(3) instances
`AlgebraicGeometry.Stack.hasRelativePropertyLocusOnSpaces_isUnramified` and
`AlgebraicGeometry.Stack.relativePropertyLocusBaseChange_isUnramified` of
`StacksFrontier/AlgebraicGeometry/Stacks/LocalSourceLemmaUnramified.lean`, the source's `𝒬` being
local finite type, which `f` has because it is locally of finite presentation
(**Stacks 0464**).

The conclusion `p(z) ∈ |W|` is the maximality half of assertion (B),
`AlgebraicGeometry.Stack.pointSet_subset_preimage_of_hasRelativeProperty`, at the open substack
of `F` that the fibre hypothesis supplies. That step consumes unramifiedness in the relative
sense of **Stacks 04XB** while the fibre hypothesis and the étaleness criterion are stated at
`AlgebraicGeometry.Stack.IsUnramified` (**Stacks 0CIT**), and *both* directions of that
comparison are available here because every 1-morphism in sight is representable by algebraic
spaces: `AlgebraicGeometry.Stack.hasRelativeProperty_unramified_of_isUnramified` and
`AlgebraicGeometry.Stack.isUnramified_of_hasRelativeProperty_unramified`, whose étale-smooth
diagram comes from
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isRepresentableByAlgebraicSpaces`
and not from **Stacks 0CIA**. Given that comparison, an open `W` with `hW` and the base-change containment
`hBaseChange` are not needed as hypotheses.

Étaleness of `f|_W` is **Stacks 06LU** for 1-morphisms of algebraic stacks,
`AlgebraicGeometry.Stack.isEtale_fullSubcategoryInclusion_comp_of_isUnramified`, applied to the
restriction of `f` to `W`, which is flat and locally of finite presentation because `f` is. -/
@[stacks 06N2 "after replacing the algebraic space by an open subspace containing the image of \
the given point of the fibre, a flat, locally finitely presented 1-morphism whose fibre over a \
field-valued point is unramified at that point is etale. Nothing is carried: the open substack \
is the locus W(P, f) of assertion (A) of Stacks 06M3 at P = unramified -- the entry of the list \
of Stacks 06M5 whose base-change clause holds for an arbitrary base change, which is why it and \
not the etale entry applies to a base change along a field-valued point -- produced by \
exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces from the entry-(3) \
instances of LocalSourceLemmaUnramified, and \
the conclusion that the image of the given point of the fibre lies in it is the maximality half \
of assertion (B) at the open substack the fibre hypothesis supplies. The comparison of the two \
renderings of unramifiedness, Stacks 0CIT against the relative notion of Stacks 04XB, is \
available in both directions for a 1-morphism representable by algebraic spaces, by \
hasSurjectiveEtaleSmoothDiagram_of_isRepresentableByAlgebraicSpaces, and needs nothing of \
Stacks 0CIA. Stacks 06LU for 1-morphisms of algebraic stacks is not carried but proved, and it \
is what turns the locus into the etaleness of the conclusion"]
theorem exists_openSubstack_isEtale_unconditional
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (z : AlgebraicStacks.points B S hS (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g))
    (hz : FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g z) :
    ∃ W : OpenSubstack (algebraicSpaceStack.{u, w} B S hS U hU),
      AlgebraicStacks.pointsMap B S hS
          (fibreProjection B S hS 𝒳 U hU k hk toBase f g) z ∈ W.pointSet B S hS ∧
        IsEtale B S hS (W.inclusion ≫ f) := by
  obtain ⟨V, hzV, hVunr⟩ := hz
  -- Hypotheses (1) and (2) of the source are read at `ℛ = ⊤`, where every clause is `True`.
  have : (⊤ : MorphismProperty (AlgebraicSpaces B S hS)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    { pullbackSnd := fun _ _ _ => trivial
      of_forall_pullbackSnd := fun _ _ => trivial }
  have : (Space.locallyOfFiniteTypeProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  -- the two 1-morphisms of the cospan and the base change of `f` are representable
  have hf' : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS 𝒳 U hU f
  have hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS
        (fieldPointObject B S hS k hk toBase)) g.hom
  have hD : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquareAlgebraicStacks B S hS f g).swap :=
    Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)
  have hfst : IsRepresentableByAlgebraicSpaces B S hS
      ((twoFibreProductSquareAlgebraicStacks B S hS f g).swap).fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ f.hom g.hom
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS
        ((twoFibreProductSquareAlgebraicStacks B S hS f g).swap))
      (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS _ hD) hf'
  -- `𝒬 = ` locally of finite type for `f`, which is locally of finite presentation
  have hQf : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.locallyOfFiniteTypeProperty B S hS) f.hom hf' :=
    (hasPropertyOnEverySmoothDiagram_iff_relative B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (algebraicSpaceStack.{u, w} B S hS U hU).property 𝒳.property f.hom hf').1
      (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp)
  -- the locus `W(𝒫, f)` of assertion (A) of Stacks 06M3 at `𝒫 = ` unramified
  obtain ⟨W, hWlocus⟩ :=
    exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces B S hS
    (Space.unramifiedMorphismProperty B S hS) (Space.locallyOfFiniteTypeProperty B S hS) ⊤
    (fun _ _ _ _ _ _ => trivial)
    (hasRelativePropertyLocusOnSpaces_isUnramified B S hS)
    (relativePropertyLocusBaseChange_isUnramified B S hS) f hf' hQf
  refine ⟨W, ?_, isEtale_fullSubcategoryInclusion_comp_of_isUnramified B S hS f W hflat hfp
    (isUnramified_of_hasRelativeProperty_unramified B S hS (W.inclusion ≫ f)
      (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS f hf' W)
      (isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS
        (W.inclusion ≫ f)
        (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS f hf' W))
      hWlocus.1)⟩
  exact pointSet_subset_preimage_of_hasRelativeProperty B S hS
    (Space.unramifiedMorphismProperty B S hS) (Space.locallyOfFiniteTypeProperty B S hS) ⊤
    (fun _ _ _ _ _ _ => trivial)
    (hasRelativePropertyLocusOnSpaces_isUnramified B S hS)
    (relativePropertyLocusBaseChange_isUnramified B S hS)
    hQf (fun _ _ _ _ _ _ => trivial) (hg := hg)
    ((twoFibreProductSquareAlgebraicStacks B S hS f g).swap) hD (hfst := hfst) hWlocus V
    (hasRelativeProperty_unramified_of_isUnramified B S hS
      (V.inclusion ≫ fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g)
      (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS
        (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g) hfst V)
      hVunr)
    hzV

end AlgebraicGeometry.Stack

end
