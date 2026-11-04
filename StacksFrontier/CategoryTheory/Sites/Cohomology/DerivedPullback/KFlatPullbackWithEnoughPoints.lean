module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafify
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackOnRingedSpaces
public import StacksFrontier.Homology.KFlat.BaseChange
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackAlongRingedTopoi
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of K-flat complexes on ringed topoi with enough points

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi. If `C` has enough points,
then the degreewise pullback of a K-flat complex of `O'`-modules is a K-flat complex of
`O`-modules. This is Stacks 0DEP, and the source's proof of it is one sentence: it follows from
Stacks 0DEN, Modules on Sites 05V5, and More on Algebra 06Y1.

This file carries out that deduction. Of the three inputs, exactly one is available in this
development; the other two are taken as named hypotheses, so that the contract is auditable and
whoever supplies them closes 0DEP by `exact`.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints.StalkKFlat`: **part (1) of Stacks
  0DEN**, that a K-flat complex on a ringed
  site has K-flat stalks, as a hypothesis on the *target* ringed topos.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints.PullbackStalkBaseChange`: **Stacks 05V5
  at the level of complexes**, that the
  stalk of a degreewise pullback is an extension of scalars of a stalk, as a hypothesis.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints.kFlat_pullback_of_enoughPoints`: the
  K-flatness assertion of Stacks 0DEP,
  granted those two hypotheses.

## Implementation notes

**What is and is not available.** The three inputs of the source's proof are:

* Stacks 0DEN part (2) — enough points, K-flat stalks, hence K-flat — which *is* available, as
  `Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks`, with no hypothesis beyond those
    of the source. It is applied
  on the source topos `X`, which is the one the statement assumes has enough points.
* Stacks 0DEN part (1) — K-flat implies K-flat stalks — which is **not** in the tree in any
  form. It is needed on the *target* topos `Y`, for which the statement assumes nothing about
  points, and that is why part (2) does not serve in its place: the two parts are used at two
  different ringed topoi and under different hypotheses. The implementation notes of the
  Stacks 0DEN development record what part (1) needs and does not have, namely
  Stacks 0E8K (restriction of a K-flat complex to a localization of the site) and, through
  Stacks 06YS and the mapping-cone triangle, Stacks 0G7E — which is itself available in this
  tree only conditionally, on
    `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat` (Stacks 05VD) and
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact` (Stacks 0G6R).  Its
    third predicate,
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.CyclesIsFlat` (Stacks 0G7C), is no longer a
    hypothesis: it is discharged
  unconditionally by `Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`, and
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_pullbackPreserves` is 0G7E
    on the remaining two.
* Stacks 05V5 — the stalk of a module pullback is the base change of the stalk along the stalk
  ring map — which is **not** in the tree at site or topos generality. The ringed-*space*
  analogue is, in full functorial strength, as
  `AlgebraicGeometry.RingedSpace.stalkModulePullbackFunctorIso`.

Stacks 06Y1 is available, as `kFlat_baseChange`, and is applied directly.

**The hypotheses are weaker than the results they stand for, deliberately.** Following the
ringed-space precedent `Stacks.SheafOfModules.KFlatPullback.PullbackStalkComplexes`,
  `PullbackStalkBaseChange` asks
only that *some* point of the target and *some* ring homomorphism carry the comparison, rather
than naming the composite point `q = f ∘ p` and the germ map of `f`. That is weaker, and it
suffices: Stacks 06Y1 preserves K-flatness along an arbitrary ring homomorphism, so no
compatibility of the ring map with `f` is used downstream. Both hypotheses are `Prop`-valued for
the same reason, so that no choice of comparison datum is made here.

**No tag is placed on anything in this file.** `kFlat_pullback_of_enoughPoints` carries two
hypotheses Stacks 0DEP does not have, and neither is inhabited anywhere in this
development, so each is a weakening; a tag here would make the dashboard read as progress on
0DEP. The same judgement is recorded for Stacks 0G7E for the same reason.

**The morphism.** Stacks 0DEP spells the morphism with Tag 01D3's `RingedToposHom`, but
the module pullback of Stacks 03D6 part (2) is defined in this development on
`AlgebraicGeometry.RingedToposSiteHom` — a morphism of ringed topoi presented by a morphism of
the underlying sites — and that is the spelling
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` uses for
the same chapter and section. Unlike 0G7E, nothing here needs `f.u` to be a morphism of sites:
the two inputs that required that hypothesis in 0G7E are Stacks 05VD and 0G6R, and neither is
used on this route.

**Universes.** Both ringed topoi are taken at `RingedTopos.{u, u, u}`: the objects, morphisms
and sections universes agree. This is the narrowing the tagged statement itself carries, and it is forced
independently by `SheafOfModules.pullback` and by
  `Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks`, whose site
and module universes are identified. It is not chosen here.

## References

* [Stacks Project, Tag 0DEP](https://stacks.math.columbia.edu/tag/0DEP)
* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints

/-! ### Part (1) of Stacks 0DEN, as a hypothesis on the target -/

/-- **Stacks 0DEN, part (1), as a hypothesis.** On a ringed topos, a K-flat complex of
`O`-modules has K-flat stalk complex at every point of the site.

This is the half of Stacks 0DEN that is not in the tree. It is stated at one ringed topos,
because that is where it is used: on the *target* of the morphism, about which the statement of
Stacks 0DEP assumes nothing concerning points. Part (2), which *is* available as
`Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks`, is used on the source instead, and
  cannot replace this. -/
def StalkKFlat (Z : AlgebraicGeometry.RingedTopos.{u, u, u})
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasWeakSheafify Z.J AddCommGrpCat.{u}]
    [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor Z.O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Z.O).obj M).Additive]
    [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
        (ComplexShape.up ℤ)] : Prop :=
  ∀ K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ,
    Stacks.SheafOfModules.IsKFlat Z.O K →
      ∀ Φ : Z.J.Point.{u}, CochainComplex.KFlat.{u, u}
        (Stacks.Sheaves.KFlatStalkCriterion.stalkComplex Z.O Φ K)

/-! ### Stacks 05V5 at the level of complexes, as a hypothesis -/

section Pullback

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 05V5 at the level of complexes, as a hypothesis.** For a point `Φ` of the source
site and a complex `K` of modules on the target, the stalk complex of the degreewise pullback
`f^*K` at `Φ` is an extension of scalars of the stalk complex of `K` at some point of the
target site.

In the source the point is the composite `q = f ∘ Φ` and the ring map is the induced map of
stalk rings `O'_q ⟶ O_Φ`; here both are only asked to exist. That is weaker, and it is enough:
Stacks 06Y1 preserves K-flatness along an arbitrary ring homomorphism, so no compatibility of
the ring map with `f` is used downstream. The same weakening is made, for the same reason, in
the ringed-space precedent `Stacks.SheafOfModules.KFlatPullback.PullbackStalkComplexes`. -/
def PullbackStalkBaseChange (f : AlgebraicGeometry.RingedToposSiteHom X Y) : Prop :=
  ∀ (Φ : X.J.Point.{u})
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    ∃ (Ψ : Y.J.Point.{u})
      (φ : Stacks.Sheaves.KFlatStalkCriterion.structureStalk Y.O Ψ →+*
        Stacks.Sheaves.KFlatStalkCriterion.structureStalk X.O Φ),
      Nonempty (Stacks.Sheaves.KFlatStalkCriterion.stalkComplex X.O Φ
          ((KFlatPullback.pullbackComplex f).obj K) ≅
        (CochainComplex.extendScalars φ).obj (Stacks.Sheaves.KFlatStalkCriterion.stalkComplex Y.O Ψ
          K))

/-! ### The K-flatness assertion of Stacks 0DEP -/

section Main

variable [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The K-flatness assertion of Stacks 0DEP**, granted part (1) of Stacks 0DEN on the target
and Stacks 05V5 at the level of complexes.

The proof is the source's. K-flatness of `f^*K` is tested at a point `Φ` of the source site by
part (2) of Stacks 0DEN, which applies because the source site has a conservative family of
points. There the stalk complex of `f^*K` is an extension of scalars of a stalk complex of `K`,
which is K-flat by part (1) of Stacks 0DEN on the target; and extension of scalars preserves
K-flatness, which is Stacks 06Y1.

This declaration carries no tag: `StalkKFlat` and `PullbackStalkBaseChange` are hypotheses the
statement of Stacks 0DEP does not have, and neither is inhabited in this development. -/
theorem kFlat_pullback_of_enoughPoints (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hX : X.J.HasConservativeFamily.{u})
    (hY : StalkKFlat Y) (h05V5 : PullbackStalkBaseChange f)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat Y.O K) :
    Stacks.SheafOfModules.IsKFlat X.O ((KFlatPullback.pullbackComplex f).obj K) := by
  refine Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks X.O hX _ fun Φ => ?_
  obtain ⟨Ψ, φ, ⟨e⟩⟩ := h05V5 Φ K
  exact CochainComplex.KFlat.of_iso e.symm (kFlat_baseChange φ _ (hY K hK Ψ))

end Main

end Pullback

end Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints

end

end
