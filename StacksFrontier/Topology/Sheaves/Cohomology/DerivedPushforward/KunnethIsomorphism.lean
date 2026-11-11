module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap
import StacksCore.Tactic.StacksAttribute

/-!
# Factoring the relative Künneth map through two projection formulas

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of ringed spaces and let `p : W ⟶ X`, `q : W ⟶ Y`
satisfy `q ≫ b = p ≫ a`.  The relative Künneth morphism of Tag 0FLP,

`Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M ⟶ R(p ≫ a)_*(Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`,

is the adjoint transpose of a single map under `L(p ≫ a)^* ⊣ R(p ≫ a)_*`.  The first proof of
Tag 0FLQ instead exhibits a chain of three comparisons, the projection formula for `a`, the
base-change map for the square, and the projection formula for `p`, and asserts without
verification that their composite is the Künneth map.  That verification is what is proved here,
at the level of abstract adjunctions where it lives: transposition under a composite of two
adjunctions turns the two-sided counit map into exactly that chain.

## Main definitions

* `Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight`: the projection-formula map
  `A(H, R G) ⟶ R (B(L H, G))` of an adjunction `L ⊣ R` with the tensor factors in the order
  opposite to `CategoryTheory.adjunctionTensorMap`, so that no
  braiding of the two tensor products is needed to compose the two projection formulas.
* `Stacks.Cohomology.DerivedKunneth.PullbackTensorComparisonComp`: compatibility of the
  monoidality isomorphism of Stacks 079U with the composition isomorphism of Stacks 0D5S.
* `Stacks.Cohomology.DerivedKunneth.kunnethBaseChangeLeg`: the base-change comparison
  `La^*Rb_*M ⟶ Rp_*Lq^*M` of the square, as the transpose of the second counit leg.

## Main results

* `Stacks.Cohomology.DerivedKunneth.homEquiv_comp_bitensor_eq`: for adjunctions `L₁ ⊣ R₁` and
  `L₂ ⊣ R₂`, successive transposition of the two-sided counit map equals the composite of the
  projection-formula map of `L₁ ⊣ R₁`, the transpose of the second leg, and the opposite-order
  projection-formula map of `L₂ ⊣ R₂`.
* `Stacks.Cohomology.DerivedKunneth.isIso_homEquiv_bitensor_comp`: the same transpose, for an
  adjunction merely identified with the composite by two isomorphisms and the transposition
  coherence, is invertible as soon as the three comparisons in the chain are.
* `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` and
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMap_of_projectionFormulas_of_baseChange`:
  for an arbitrary commuting square of ringed spaces, the relative and global Künneth maps at
  `f = p ≫ a` are invertible whenever the three comparisons of the chain are.  These are the
  reduction steps of the first proof of Tag 0FLQ; the tag itself, at a cartesian square of
  schemes under its own hypotheses, is
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme` and
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme`.

## Implementation notes

*Why the comparisons are hypotheses here.*  The quasi-compactness, quasi-separatedness,
Tor-independence and quasi-coherence hypotheses of the source enter its first proof only through
Lemma 36.22.1 (Tag 08EU) and Lemma 36.22.5 (Tag 08IB).  At the generality of this file, an
arbitrary commuting square of ringed spaces, those lemmas do not apply (for a square that is not
cartesian the base change of Tag 08IB is false), so the three comparisons are explicit
hypotheses `hproj₁`, `hproj₂` and `hbase`, alongside the monoidality coherence `hcoh`.  What is
proved is the step the source states and omits: that the composite of those three comparisons is
the Künneth map of Tag 0FLP.  The coherence `hcoh` is proved in general by
`Stacks.Cohomology.DerivedKunneth.pullbackTensorComparisonComp`, and the three comparisons are
discharged at a cartesian square of schemes from the proved Tags 08EU and 08IB in
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/`.

*Where the content lives.*  That identification is a fact about a composite of two adjunctions
and two monoidality comparisons, with no sheaf or derived-category input, so it is proved at that
level of generality in `homEquiv_comp_bitensor_eq`; the geometric statements are single
applications of it.  The opposite-order projection formula `adjunctionTensorMapRight` is what
makes the chain composable without a braiding of the derived tensor product.

*The factorizations are data.*  As in `Stacks.Cohomology.DerivedKunneth.kunnethMap`, the two
projections and the square are taken as data rather than as a fibre product; `f` is specialized
to `p ≫ a`, which is the source's situation and removes the transport along `hp`.

## References

* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedPullback.Composition
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedKunneth

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- The projection-formula map `A(H, R G) ⟶ R (B(L H, G))` of an adjunction `L ⊣ R` equipped
with bifunctors `A` on the source, `B` on the target and a monoidality comparison
`α : A ⋙ L ⟶ (L × L) ⋙ B`: the adjoint transpose of `α` followed by the counit in the *second*
tensor factor.  It is `CategoryTheory.adjunctionTensorMap` with the
two factors interchanged. -/
def adjunctionTensorMapRight {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B) (H : C) (G : D) :
    A.obj (H, R.obj G) ⟶ R.obj (B.obj (L.obj H, G)) :=
  adj.homEquiv _ _ (α.app (H, R.obj G) ≫ B.map (𝟙 (L.obj H) ×ₘ adj.counit.app G))

variable {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}

/-- **The chain of three comparisons is the transpose of the two-sided counit map.**

For adjunctions `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂`, bifunctors `TA`, `TD`, `TE` on the three
categories with monoidality comparisons `α₁` for `L₁` and `α₂` for `L₂`, an object `K` of the
middle category, an object `N` of the first, an object `G` of the last and a morphism
`v : L₂(L₁N) ⟶ G`, successive transposition under `adj₂` and then `adj₁` of

`L₂(α₁) ≫ α₂ ≫ (L₂(ε₁) ⊗ v)`

is the composite of the projection-formula map of `adj₁` at `(K, N)`, the transpose of `v` in
the second tensor factor, and the opposite-order projection-formula map of `adj₂` at `(K, G)`.
This is the verification omitted in the first proof of Tag 0FLQ. -/
theorem homEquiv_comp_bitensor_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (TA : C × C ⥤ C) (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (α₁ : TA ⋙ L₁ ⟶ L₁.prod L₁ ⋙ TD) (α₂ : TD ⋙ L₂ ⟶ L₂.prod L₂ ⋙ TE)
    (K : D) (N : C) (G : E) (v : L₂.obj (L₁.obj N) ⟶ G) :
    adj₁.homEquiv (TA.obj (R₁.obj K, N)) (R₂.obj (TE.obj (L₂.obj K, G)))
        (adj₂.homEquiv (L₁.obj (TA.obj (R₁.obj K, N))) (TE.obj (L₂.obj K, G))
        (L₂.map (α₁.app (R₁.obj K, N)) ≫
          α₂.app (L₁.obj (R₁.obj K), L₁.obj N) ≫
            TE.map (L₂.map (adj₁.counit.app K) ×ₘ v))) =
      CategoryTheory.adjunctionTensorMap adj₁ TA TD α₁ K N ≫
        R₁.map (TD.map (𝟙 K ×ₘ adj₂.homEquiv _ _ v)) ≫
          R₁.map (adjunctionTensorMapRight adj₂ TD TE α₂ K G) := by
  -- The inner transposition is the last two legs of the chain.
  have key : adj₂.homEquiv ((L₁.prod L₁ ⋙ TD).obj (R₁.obj K, N))
        (TE.obj (L₂.obj K, G))
        (α₂.app (L₁.obj (R₁.obj K), L₁.obj N) ≫
          TE.map (L₂.map (adj₁.counit.app K) ×ₘ v)) =
      TD.map (adj₁.counit.app K ×ₘ 𝟙 (L₁.obj N)) ≫
        TD.map (𝟙 K ×ₘ adj₂.homEquiv (L₁.obj N) G v) ≫
          adjunctionTensorMapRight adj₂ TD TE α₂ K G := by
    rw [adjunctionTensorMapRight, ← Category.assoc, ← Functor.map_comp,
      ← Adjunction.homEquiv_naturality_left]
    congr 1
    have hprod : ((adj₁.counit.app K ×ₘ 𝟙 (L₁.obj N)) ≫
        (𝟙 K ×ₘ adj₂.homEquiv (L₁.obj N) G v)) =
        (adj₁.counit.app K ×ₘ adj₂.homEquiv (L₁.obj N) G v) := by
      simp
    rw [hprod]
    have hnat := α₂.naturality (adj₁.counit.app K ×ₘ adj₂.homEquiv (L₁.obj N) G v)
    simp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.id_obj] at hnat
    rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp]
    congr 2
    refine CategoryTheory.Prod.hom_ext (by simp) ?_
    have hcounit := (adj₂.homEquiv (L₁.obj N) G).symm_apply_apply v
    rw [Adjunction.homEquiv_counit] at hcounit
    exact hcounit.symm
  rw [Adjunction.homEquiv_naturality_left, key]
  conv_rhs => rw [CategoryTheory.adjunctionTensorMap,
    ← Category.assoc, ← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_right]
  congr 1
  simp only [Category.assoc]

/-- **The Künneth transpose along a composite is an isomorphism when the chain is.**

The adjunction `adjf : Lf ⊣ Rf` is identified with the composite of `adj₁` and `adj₂` by the two
isomorphisms `cL`, `cR` and the transposition coherence `hcompat`.  `αf` is the monoidality
comparison for `Lf` at one pair of objects, compatible with `α₁` and `α₂` by `hαf`, and the two
legs are `bK`, `gM`, the first of which is the counit of `adj₁` read through `cL`.  Under those
identifications the adjoint transpose of `αf ≫ (bK ⊗ gM)` is the composite of the
projection-formula map of `adj₁`, the transpose of `gM`, and the opposite-order
projection-formula map of `adj₂`, hence invertible as soon as those three are. -/
theorem isIso_homEquiv_bitensor_comp (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {Lf : C ⥤ E} {Rf : E ⥤ C} (adjf : Lf ⊣ Rf)
    (cL : L₁ ⋙ L₂ ≅ Lf) (cR : R₂ ⋙ R₁ ≅ Rf)
    (hcompat : ∀ (Z : C) (T : E) (φ : Lf.obj Z ⟶ T),
      adj₁.homEquiv _ _ (adj₂.homEquiv _ _ (cL.hom.app Z ≫ φ)) ≫ cR.hom.app T =
        adjf.homEquiv Z T φ)
    (TA : C × C ⥤ C) (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (α₁ : TA ⋙ L₁ ⟶ L₁.prod L₁ ⋙ TD) (α₂ : TD ⋙ L₂ ⟶ L₂.prod L₂ ⋙ TE)
    (K : D) (N : C) (Q : E)
    (αf : Lf.obj (TA.obj (R₁.obj K, N)) ⟶ TE.obj (Lf.obj (R₁.obj K), Lf.obj N))
    (gM : Lf.obj N ⟶ Q) (bK : Lf.obj (R₁.obj K) ⟶ L₂.obj K)
    (hbK : bK = cL.inv.app (R₁.obj K) ≫ L₂.map (adj₁.counit.app K))
    (hαf : (cL.hom.app (TA.obj (R₁.obj K, N)) ≫ αf) ≫
        TE.map (cL.inv.app (R₁.obj K) ×ₘ cL.inv.app N) =
      L₂.map (α₁.app (R₁.obj K, N)) ≫ α₂.app (L₁.obj (R₁.obj K), L₁.obj N))
    (hone : IsIso
      (CategoryTheory.adjunctionTensorMap adj₁ TA TD α₁ K N))
    (htwo : IsIso (adj₂.homEquiv (L₁.obj N) Q (cL.hom.app N ≫ gM)))
    (hthree : IsIso (adjunctionTensorMapRight adj₂ TD TE α₂ K Q)) :
    IsIso (adjf.homEquiv _ _ (αf ≫ TE.map (bK ×ₘ gM))) := by
  have hin : cL.hom.app (TA.obj (R₁.obj K, N)) ≫ αf ≫ TE.map (bK ×ₘ gM) =
      L₂.map (α₁.app (R₁.obj K, N)) ≫
        α₂.app (L₁.obj (R₁.obj K), L₁.obj N) ≫
          TE.map (L₂.map (adj₁.counit.app K) ×ₘ (cL.hom.app N ≫ gM)) := by
    have hs : (bK ×ₘ gM) =
        (cL.inv.app (R₁.obj K) ×ₘ cL.inv.app N) ≫
          (L₂.map (adj₁.counit.app K) ×ₘ (cL.hom.app N ≫ gM)) :=
      CategoryTheory.Prod.hom_ext (by simpa using hbK)
        (by simp only [CategoryTheory.prod_comp]; simp)
    rw [hs, Functor.map_comp]
    simp only [← Category.assoc]
    rw [hαf]
  rw [← hcompat, hin, homEquiv_comp_bitensor_eq]
  have h₁ := hone
  have h₂ := htwo
  have h₃ := hthree
  have h₄ : IsIso (𝟙 K ×ₘ adj₂.homEquiv (L₁.obj N) Q (cL.hom.app N ≫ gM)) :=
    ⟨𝟙 K ×ₘ inv (adj₂.homEquiv (L₁.obj N) Q (cL.hom.app N ≫ gM)),
      CategoryTheory.Prod.hom_ext (by simp) (by simp),
      CategoryTheory.Prod.hom_ext (by simp) (by simp)⟩
  infer_instance

/-! ### The relative Künneth map of a composite of two morphisms of ringed spaces -/

section Geometry

attribute [local instance] HasDerivedCategory.standard

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (hq : q ≫ b = p ≫ a)
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Compatibility of the derived pullback-tensor comparison with a composite**, at one pair of
derived modules on the base.  The monoidality isomorphism of Stacks 079U for `L(p ≫ a)^*`, read
through the composition isomorphism of Stacks 0D5S for derived pullback, is the monoidality
isomorphism for `La^*` pulled back along `p` followed by the one for `Lp^*`.  This is a coherence
between Stacks 079U and Stacks 0D5S; it holds for all `P` and `Q`, by
`Stacks.Cohomology.DerivedKunneth.pullbackTensorComparisonComp`. -/
def PullbackTensorComparisonComp
    (P Q : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) : Prop :=
  ((derivedPullbackCompIsoCanonical p a).hom.app
          ((Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).obj (P, Q)) ≫
        (pullbackTensorComparison (p ≫ a)).app (P, Q)) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
        ((derivedPullbackCompIsoCanonical p a).inv.app P ×ₘ
          (derivedPullbackCompIsoCanonical p a).inv.app Q) =
    (derivedPullback p).map ((pullbackTensorComparison a).app (P, Q)) ≫
      (pullbackTensorComparison p).app
        ((derivedPullback a).obj P, (derivedPullback a).obj Q)

/-- The second counit leg of the Künneth map of a composite, read through the composition
isomorphism for derived pullback: the adjoint transpose of this map under `Lp^* ⊣ Rp_*` is the
base-change comparison `La^*Rb_*M ⟶ Rp_*Lq^*M` of Tag 08IB for the square `q ≫ b = p ≫ a`. -/
abbrev kunnethBaseChangeLeg (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullback a).obj ((derivedPushforward b).obj M) ⟶
      (derivedPushforward p).obj ((derivedPullback q).obj M) :=
  (derivedAdjunction p).homEquiv _ _
    ((derivedPullbackCompIsoCanonical p a).hom.app ((derivedPushforward b).obj M) ≫
      (pullbackCounitLeg b q (p ≫ a) hq).app M)

/-- **The relative Künneth map of a composite is invertible when the three comparisons are.**

For `a : X ⟶ S`, `b : Y ⟶ S`, `p : W ⟶ X` and `q : W ⟶ Y` with `q ≫ b = p ≫ a`, the relative
Künneth morphism of Tag 0FLP at `f = p ≫ a`,

`Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M ⟶ Rf_*(Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`,

is an isomorphism as soon as the three comparisons the source's first proof chains together are.
In order they are: the projection formula of Tag 08EU for `a` at `(K, Rb_*M)`; the base-change
comparison `La^*Rb_*M ⟶ Rp_*Lq^*M` of Tag 08IB for the square; and the projection formula of
Tag 08EU for `p` at `(K, Lq^*M)`, read with the two tensor factors interchanged.  What the proof
supplies is the identification of the composite of those three with the Künneth map, which the
source states and omits.

This is the reduction step of the first proof of Tag 0FLQ, for an arbitrary commuting square of
ringed spaces.  The tag's relative conclusion, at a cartesian square of schemes and under the
tag's own hypotheses, is `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme`. -/
theorem isIso_kunnethMap_of_projectionFormulas_of_baseChange
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hcoh : PullbackTensorComparisonComp a p
      ((derivedPushforward a).obj K) ((derivedPushforward b).obj M))
    (hproj₁ : IsIso (projectionFormulaMap a K ((derivedPushforward b).obj M)))
    (hbase : IsIso (kunnethBaseChangeLeg a b p q hq M))
    (hproj₂ : IsIso (adjunctionTensorMapRight (derivedAdjunction p)
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
      (pullbackTensorComparison p) K ((derivedPullback q).obj M))) :
    IsIso (kunnethMap a b p q (p ≫ a) rfl hq K M) :=
  isIso_homEquiv_bitensor_comp (derivedAdjunction a) (derivedAdjunction p)
    (derivedAdjunction (p ≫ a)) (derivedPullbackCompIsoCanonical p a)
    (derivedPushforwardCompIso p a) (derivedAdjunction_comp_homEquiv p a)
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
    (pullbackTensorComparison a) (pullbackTensorComparison p) K
    ((derivedPushforward b).obj M) ((derivedPullback q).obj M)
    ((pullbackTensorComparison (p ≫ a)).app
      ((derivedPushforward a).obj K, (derivedPushforward b).obj M))
    ((pullbackCounitLeg b q (p ≫ a) hq).app M)
    ((pullbackCounitLeg a p (p ≫ a) rfl).app K)
    (by simp [pullbackCounitLeg, pullbackCounitLegComp]) hcoh hproj₁ hbase hproj₂

/-- **The global Künneth map of a composite is invertible when the three comparisons and the
global cup product are.**  Under the hypotheses of
`isIso_kunnethMap_of_projectionFormulas_of_baseChange`, over a base whose `A`-linear global cup
product `κ` is invertible at `(Ra_*K, Rb_*M)`, the global Künneth morphism of Tag 0G7V

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

is an isomorphism.  The source deduces this from the relative statement by applying `RΓ(S, -)` to
its source and target.

The tag's global conclusion, over an affine base, at a cartesian square of schemes, for the
canonical global cup product of Section 0FKU and under the tag's own hypotheses, is
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme`. -/
theorem isIso_kunnethGlobalMap_of_projectionFormulas_of_baseChange
    (κ : Stacks.Cohomology.GlobalKunneth.GlobalCupProduct S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hκ : IsIso (κ.app ((derivedPushforward a).obj K, (derivedPushforward b).obj M)))
    (hcoh : PullbackTensorComparisonComp a p
      ((derivedPushforward a).obj K) ((derivedPushforward b).obj M))
    (hproj₁ : IsIso (projectionFormulaMap a K ((derivedPushforward b).obj M)))
    (hbase : IsIso (kunnethBaseChangeLeg a b p q hq M))
    (hproj₂ : IsIso (adjunctionTensorMapRight (derivedAdjunction p)
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
      (pullbackTensorComparison p) K ((derivedPullback q).obj M))) :
    IsIso (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMap a b p q (p ≫ a) rfl hq κ K M) :=
  Stacks.Cohomology.GlobalKunneth.isIso_kunnethGlobalMap a b p q (p ≫ a) rfl hq κ K M hκ
    (isIso_kunnethMap_of_projectionFormulas_of_baseChange a b p q hq K M hcoh hproj₁ hbase hproj₂)

end Geometry

end Stacks.Cohomology.DerivedKunneth

end
