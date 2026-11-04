module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpCommonIndex
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedSharpAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# A morphism agreeing with another on a first order thickening is determined by its comorphism

Let `Z ⊆ X` be a first order thickening of algebraic spaces over a scheme `S` with inclusion
`i : Z ⟶ X`, and let `c, c' : X ⟶ W` be two morphisms whose restrictions to `Z` are one and the
same morphism `e : Z ⟶ W`.  Their comorphisms read through the thickening,

`𝒪_W ⟶ e_*(i^{-1}𝒪_X)`,

then live in one and the same sheaf of rings, and this file proves that they determine `c`:
**two morphisms agreeing on the thickening whose comorphisms read through the thickening agree
are equal.**

This is the faithfulness the uniqueness half of [Stacks Project, Tag 0CKE] needs, and it is
proved *without* Properties of Spaces, Theorem [Stacks Project, Tag 04KL]: recovering an
arbitrary morphism of algebraic spaces from its morphism of small étale ringed topoi is not
available in this development, but recovering one of two morphisms agreeing on a thickening is,
because the thickening forces the two to factor through **one** étale chart of `W`.

## The argument

Fix an étale chart `P` of `X` with affine underlying scheme carrying an affine chart diagram over
`c` — an affine étale chart `Q` of `W` and a morphism `ε : P ⟶ Q` of the site with
`P ⟶ X --c--> W` equal to `P --ε--> Q ⟶ W`.  Such charts are cover-dense in the small étale site
of `X`, by `AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`.

1. **One chart for both morphisms.**  `Q ⟶ W` is étale, hence formally étale
   ([Stacks Project, Tag 04AL]), and `Z ×_X P ⊆ P` is a first order thickening
   ([Stacks Project, Tag 09ZX]); so [Stacks Project, Tag 0611] produces a *unique* `ε' : P ⟶ Q`
   with `P ⟶ X --c'--> W` equal to `P --ε'--> Q ⟶ W` and with the same restriction to `Z ×_X P`
   as `ε`.  Both morphisms are now read on the same pair of charts.
2. **The two chart morphisms have the same global sections.**  For every étale chart `K` of `Z`
   above `Z ×_X P`, the index of the limit of chart sections attached to `K` and to `ε`
   by `AlgebraicGeometry.Space.chartBaseChangeComp` is determined by its chart morphism
   `K ⟶ Q`, which is the restriction of `ε` to `K` — and that restriction does not change when
   `ε` is replaced by `ε'`.  So the index is **the same for `c` and for `c'`**, and the
   computation of the chart projection at it,
   `AlgebraicGeometry.Space.directImageChartProjection_structureSharpThroughThickening_comp`,
   turns the equality of the two comorphisms into the equality of the two pullbacks of regular
   functions along `ε` and `ε'`.
3. **Hence the two chart morphisms are equal**, `Q` being affine
   (`AlgebraicGeometry.ext_of_isAffine`), and `c` and `c'` agree on `P`.
4. **Hence `c = c'`.**  The charts of the previous step cover, so the morphisms into the sheaf
   `W` agree on every étale chart of `X`; one such chart is a surjective étale atlas, which
   cancels on the left by `AlgebraicGeometry.Space.hom_ext_of_etale_atlas`.

## Main results

* `AlgebraicGeometry.Space.exists_chartHom_agreeing_on_thickening`: **a chart diagram over `c`
  is a chart diagram over `c'` on the same two charts**, with the same restriction to the
  thickening.
* `AlgebraicGeometry.Space.chartPullback_eq_of_structureSharpThroughThickeningAt_eq`: the two
  chart morphisms pull regular functions back in the same way.
* `AlgebraicGeometry.Space.eq_of_structureSharpThroughThickeningAt_eq`: **two morphisms
  agreeing on a first order thickening with equal comorphisms read in the common target are
  equal.**
* `AlgebraicGeometry.Space.eq_of_restrictedSharpThroughThickening_eq`: the same with the
  hypothesis in the transported spelling of
  `AlgebraicGeometry.Space.restrictedSharpThroughThickening`, which is the form the difference
  of two sections of [Stacks Project, Tag 0CKB] produces.

## Implementation notes

**Every index is kept on the `e`-spelling and `e` is substituted away.**  The comorphism read
through the thickening is `AlgebraicGeometry.Space.structureSharpThroughThickening`, whose target
is indexed by the composite `i ≫ c` on the nose; the comparable spelling for two morphisms is
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt`, indexed by a morphism `e` with
`i ≫ c = e`, which carries an `eqToHom`.  As the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` record, putting an
`eqToHom` beside one of these composites is a deterministic `whnf` timeout.  Every statement here
is therefore made with `e` a variable and its proof begins by substituting it; the same
proof with the `eqToHom` left in place exhausts the heartbeat budget.

**The index of the limit of chart sections is pinned by its `right` field.**  The chart
projection at an index `m` takes its values in the sections over `m.right`, so an equality of
indices cannot be rewritten inside an application of the projection: the motive is not type
correct.  The statements below therefore quantify over the *arrow* of the index with its `right`
field fixed to that of the chart of `Z`, and identify two such arrows by
`AlgebraicGeometry.Space.chartBaseChangeMap_injective` — a morphism into the cartesian base
change is determined by the chart morphism it induces.

**The ambient space of the thickening on a chart is passed explicitly.**  In
[Stacks Project, Tag 0611] the ambient algebraic space of the thickening is an implicit argument
determined by the subfunctor; solving for it from `Subfunctor T'.obj` is a higher-order
unification problem and is a deterministic `whnf` timeout.  The argument `T'` is
supplied by name at the call.

**No `@[stacks]` attribute is placed.**  This is the faithfulness of [Stacks Project, Tag 03G8]
restricted to the morphisms agreeing on a thickening, internal to this development; the full
statement is [Stacks Project, Tag 04KL], which this file neither proves nor uses.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL), étale implies formally
  étale.
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611), lifting along a
  formally étale morphism.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX), base change of a
  thickening.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this
  faithfulness is an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ u

namespace AlgebraicGeometry.Space

/-- A morphism which lands in a subfunctor after a second morphism agrees with another morphism
as soon as the two agree on the preimage of that subfunctor.  Stated over an abstract site, as
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSquareZeroValues.lean` require
of these cancellations. -/
private theorem comp_eq_of_mem_preimage {Cc : Type u₁} [Category.{v₁} Cc]
    {F G H K : Ccᵒᵖ ⥤ Type w}
    (Zs : Subfunctor F) (q : G ⟶ F) (p : K ⟶ G)
    (hmem : ∀ (U : Ccᵒᵖ) (x : K.obj U), q.app U (p.app U x) ∈ Zs.obj U)
    {a b : G ⟶ H} (hab : (Zs.preimage q).ι ≫ a = (Zs.preimage q).ι ≫ b) :
    p ≫ a = p ≫ b := by
  have hle : Subfunctor.range p ≤ Zs.preimage q := by
    intro U x hx
    obtain ⟨y, rfl⟩ := hx
    exact hmem U y
  rw [← Subfunctor.lift_ι p hle, Category.assoc, hab, ← Category.assoc, Subfunctor.lift_ι]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The comorphism read at the index attached to a chart of the thickening -/

/-- The comorphism read through the thickening at the tautological index `e = i ≫ c` is the
comorphism read through the thickening: the `eqToHom` of
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt` is then an identity. -/
theorem structureSharpThroughThickeningAt_self (c : X ⟶ W) :
    structureSharpThroughThickeningAt B S hS Z c
        (subspaceInclusion B S hS X Z ≫ c) rfl =
      structureSharpThroughThickening B S hS Z c :=
  Category.comp_id _

/-- **The chart diagram of the common restriction** attached to an étale chart `K` of `Z` above
`Z ×_X P` and to a chart morphism `ε : P ⟶ Q` over `c`: its vertical morphism of schemes is the
restriction of `ε` to `K`, and it is a chart diagram over the restriction `e` of `c` to the
thickening.

It is through this chart diagram that the index at which the two comorphisms are compared is
named, and the only thing the index depends on is the composite `K ⟶ P --ε--> Q`. -/
def thickeningRestrictionChartDiagram (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom)
    (k : StructuredArrow (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P))
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op) :
    ChartDiagram B S hS Z.1.toFunctor W.1 e.hom where
  U := k.right.unop
  V := Q
  g := chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε
  comm := by
    have hk : (k.right.unop).1.hom ≫ (subspaceInclusion B S hS X Z).hom =
        yoneda.map (chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k) ≫ P.1.hom :=
      (chartDiagramOfIndex B S hS (subspaceInclusion B S hS X Z) P k).comm
    have he : e.hom = (subspaceInclusion B S hS X Z).hom ≫ c.hom :=
      congrArg (fun m : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W => m.hom) h.symm
    rw [he, reassoc_of% hk, hε, CategoryTheory.Functor.map_comp_assoc]

/-- **The arrow of the index at which the two comorphisms are compared**: the cartesian form of
`AlgebraicGeometry.Space.thickeningRestrictionChartDiagram`, read as a morphism into the
cartesian base change `Z ×_W Q` with its source fixed to the chart `K` of `Z`. -/
def thickeningRestrictionChartIndex (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom)
    (k : StructuredArrow (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P))
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op) :
    op (chartBaseChange B S hS e Q) ⟶
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op.obj k.right :=
  (chartLift B S hS e
    (thickeningRestrictionChartDiagram B S hS Z c e h Q P ε hε k)).op

/-- The chart morphism of `AlgebraicGeometry.Space.thickeningRestrictionChartIndex` is the
restriction of `ε` to the chart `K` of `Z`.  This is what makes the index common to two
morphisms agreeing on the thickening: it depends on the chart morphism only through that
restriction. -/
theorem chartBaseChangeMap_thickeningRestrictionChartIndex (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom)
    (k : StructuredArrow (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P))
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op) :
    chartBaseChangeMap B S hS e Q
        (StructuredArrow.mk (Y := k.right)
          (thickeningRestrictionChartIndex B S hS Z c e h Q P ε hε k)) =
      chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε :=
  chartBaseChangeMap_indexOfChartDiagram B S hS e
    (thickeningRestrictionChartDiagram B S hS Z c e h Q P ε hε k)

/-- The index of the limit of chart sections attached to a chart of `X` over `X ×_W Q` and a
chart of `Z` over `Z ×_X P` has, as its chart morphism, the composite of the two chart
morphisms.  This is
`AlgebraicGeometry.Space.chartBaseChangeMap_comp_chart` read at the index of a chart diagram. -/
theorem chartBaseChangeMap_comp_indexOfChartDiagram (c : X ⟶ W)
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom)
    (k : StructuredArrow (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P))
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op) :
    chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z ≫ c) Q
        (StructuredArrow.mk
          ((chartBaseChangeComp B S hS (subspaceInclusion B S hS X Z) c Q
            (indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩)).op ≫ k.hom)) =
      chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε :=
  (chartBaseChangeMap_comp_chart B S hS (subspaceInclusion B S hS X Z) c Q
    (indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩) k).trans
    (congrArg (fun m => chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ m)
      (chartBaseChangeMap_indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩))

/-- **An index of the limit of chart sections over `Z ×_W Q` whose chart morphism is the
restriction of `ε` is the index attached to the pair of chart diagrams.**  A morphism into the
cartesian base change is determined by the chart morphism it induces,
`AlgebraicGeometry.Space.chartBaseChangeMap_injective`. -/
theorem eq_chartBaseChangeComp_of_chartBaseChangeMap_eq (c : X ⟶ W)
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom)
    (k : StructuredArrow (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P))
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op)
    (θ : op (chartBaseChange B S hS (subspaceInclusion B S hS X Z ≫ c) Q) ⟶
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op.obj k.right)
    (hθ : chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z ≫ c) Q
        (StructuredArrow.mk (Y := k.right) θ) =
      chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε) :
    θ = (chartBaseChangeComp B S hS (subspaceInclusion B S hS X Z) c Q
      (indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩)).op ≫ k.hom :=
  congrArg Quiver.Hom.op
    (chartBaseChangeMap_injective B S hS (subspaceInclusion B S hS X Z ≫ c)
      (hθ.trans (chartBaseChangeMap_comp_indexOfChartDiagram B S hS Z c Q P ε hε k).symm))

/-- **The comorphism read through the thickening, projected at an index over `Z ×_W Q` whose
chart morphism is the restriction of `ε`**, is the chart projection along `i` of the unit
`η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` at the pullback of the regular function along `ε`.

This is
`AlgebraicGeometry.Space.directImageChartProjection_structureSharpThroughThickening_comp` with
the index described by its chart morphism rather than written out, which is the form in which
two morphisms agreeing on the thickening can be compared at one and the same index. -/
theorem directImageChartProjection_structureSharpThroughThickening_common (c : X ⟶ W)
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom)
    (k : StructuredArrow (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P))
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op)
    (θ : op (chartBaseChange B S hS (subspaceInclusion B S hS X Z ≫ c) Q) ⟶
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op.obj k.right)
    (hθ : chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z ≫ c) Q
        (StructuredArrow.mk (Y := k.right) θ) =
      chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op Q))) :
    (directImageChartProjection B S hS (subspaceInclusion B S hS X Z ≫ c) Q
          (StructuredArrow.mk (Y := k.right) θ)).app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        ((structureSharpThroughThickening B S hS Z c).hom.app (op Q) b) =
      (directImageChartProjection B S hS (subspaceInclusion B S hS X Z) P k).app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        ((thickeningRingUnit B S hS Z).hom.app (op P)
          (chartPullback B S hS c Q
            (indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩) b)) := by
  rw [eq_chartBaseChangeComp_of_chartBaseChangeMap_eq B S hS Z c Q P ε hε k θ hθ]
  exact directImageChartProjection_structureSharpThroughThickening_comp B S hS Z c Q
    (indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩) k b

/-- `AlgebraicGeometry.Space.directImageChartProjection_structureSharpThroughThickening_common`
for the comorphism read in the common target of two morphisms agreeing on the thickening. -/
theorem directImageChartProjection_structureSharpThroughThickeningAt_common (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom)
    (k : StructuredArrow (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P))
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op)
    (θ : op (chartBaseChange B S hS e Q) ⟶
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op.obj k.right)
    (hθ : chartBaseChangeMap B S hS e Q (StructuredArrow.mk (Y := k.right) θ) =
      chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op Q))) :
    (directImageChartProjection B S hS e Q (StructuredArrow.mk (Y := k.right) θ)).app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        ((structureSharpThroughThickeningAt B S hS Z c e h).hom.app (op Q) b) =
      (directImageChartProjection B S hS (subspaceInclusion B S hS X Z) P k).app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        ((thickeningRingUnit B S hS Z).hom.app (op P)
          (chartPullback B S hS c Q
            (indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩) b)) := by
  subst h
  rw [structureSharpThroughThickeningAt_self]
  exact directImageChartProjection_structureSharpThroughThickening_common
    B S hS Z c Q P ε hε k θ hθ b

/-! ### Two chart morphisms agreeing on the thickening -/

/-- **A chart morphism restricted to the thickening does not see which of the two morphisms it
is a chart morphism of.**  For every étale chart `K` of `Z` above `Z ×_X P` the restriction of a
chart morphism to `K` is read off its restriction to `Z ×_X P`, so two chart morphisms with the
same such restriction have the same restriction to `K`.

The chart morphism of `K` lands in the preimage of `Z` in `P`, by the cartesian square of the
base change, so the agreement on that preimage applies. -/
theorem comp_chartBaseChangeMap_eq_of_thickeningRestriction_eq (P : SmallEtale B S hS X.1)
    (Q : SmallEtale B S hS W.1)
    (ε ε' : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hab : (Z.1.preimage P.1.hom).ι ≫ yoneda.map ε =
      (Z.1.preimage P.1.hom).ι ≫ yoneda.map ε')
    (k : StructuredArrow (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P))
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op) :
    chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε =
      chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε' := by
  refine yoneda.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    yoneda_map_chartBaseChangeMap]
  have hwh : ((spacesBaseChange B S hS (subspaceInclusion B S hS X Z)).projection.app
        ((comparisonFunctor B S hS X).obj P)).hom ≫ P.1.hom =
      ((spacesBaseChange B S hS (subspaceInclusion B S hS X Z)).functor.obj
        ((comparisonFunctor B S hS X).obj P)).1.hom.hom ≫ Z.1.ι :=
    congrArg (fun m => m.hom)
      (((spacesBaseChange B S hS (subspaceInclusion B S hS X Z)).isPullback
        ((comparisonFunctor B S hS X).obj P)).w)
  have hmem : ∀ (U : (BigFppfOver B S hS)ᵒᵖ)
      (x : ((SpacesEtale.toSpaces B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).obj
        (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P)).1.obj U),
      P.1.hom.app U
        (((spacesBaseChange B S hS (subspaceInclusion B S hS X Z)).projection.app
          ((comparisonFunctor B S hS X).obj P)).hom.app U x) ∈ Z.1.obj U := by
    intro U x
    have hx := congrArg (fun t => t.app U x) hwh
    exact hx ▸ (((spacesBaseChange B S hS (subspaceInclusion B S hS X Z)).functor.obj
      ((comparisonFunctor B S hS X).obj P)).1.hom.hom.app U x).2
  have key := comp_eq_of_mem_preimage Z.1 P.1.hom
    ((spacesBaseChange B S hS (subspaceInclusion B S hS X Z)).projection.app
      ((comparisonFunctor B S hS X).obj P)).hom hmem hab
  exact congrArg (fun m => ((SpacesEtale.toSpaces B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).map k.hom.unop).hom ≫ m) key

/-- **A chart diagram over `c` is a chart diagram over `c'` on the same two charts.**  The chart
of `W` is étale over `W`, hence formally étale by [Stacks Project, Tag 04AL], and the preimage
of `Z` in the chart `P` is a first order thickening of `P` by [Stacks Project, Tag 09ZX]; so
[Stacks Project, Tag 0611] lifts `c'` through the chart of `W`, uniquely and with the prescribed
restriction to the thickening.

This is the step which makes the whole argument possible without
[Stacks Project, Tag 04KL]: the two morphisms are read on *one* chart of `W`. -/
theorem exists_chartHom_agreeing_on_thickening
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c c' : X ⟶ W)
    (heq : subspaceInclusion B S hS X Z ≫ c = subspaceInclusion B S hS X Z ≫ c')
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom) :
    ∃ ε' : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q,
      P.1.hom ≫ c'.hom = yoneda.map ε' ≫ Q.1.hom ∧
        (Z.1.preimage P.1.hom).ι ≫ yoneda.map ε =
          (Z.1.preimage P.1.hom).ι ≫ yoneda.map ε' := by
  have hf : FormallyEtale
      (ObjectProperty.homMk Q.1.hom :
        (schemeSpaceFunctor B S hS).obj ((SmallEtale.toOver B S hS W.1).obj Q) ⟶ W).hom :=
    formallyEtale_of_etale B S hS Q.1.hom Q.2
  have hT : IsFirstOrderThickening B S hS
      ((schemeSpaceFunctor B S hS).obj ((SmallEtale.toOver B S hS X.1).obj P))
      (Z.1.preimage P.1.hom) :=
    isFirstOrderThickening_preimage B S hS Z.1
      (ObjectProperty.homMk P.1.hom :
        (schemeSpaceFunctor B S hS).obj ((SmallEtale.toOver B S hS X.1).obj P) ⟶ X) hZ
  have hheq : Z.1.ι ≫ c.hom = Z.1.ι ≫ c'.hom :=
    congrArg (fun m : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W => m.hom) heq
  have hsq : ((Z.1.preimage P.1.hom).ι ≫ yoneda.map ε) ≫ Q.1.hom =
      (Z.1.preimage P.1.hom).ι ≫ (P.1.hom ≫ c'.hom) := by
    rw [Category.assoc, ← hε, ← Subfunctor.fromPreimage_ι_assoc, hheq,
      Subfunctor.fromPreimage_ι_assoc]
  obtain ⟨cc, ⟨hcc1, hcc2⟩, -⟩ :=
    FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS
      (T' := (schemeSpaceFunctor B S hS).obj ((SmallEtale.toOver B S hS X.1).obj P))
      (ObjectProperty.homMk Q.1.hom :
        (schemeSpaceFunctor B S hS).obj ((SmallEtale.toOver B S hS W.1).obj Q) ⟶ W) hf
      (Z.1.preimage P.1.hom) hT ((Z.1.preimage P.1.hom).ι ≫ yoneda.map ε)
      (P.1.hom ≫ c'.hom) hsq
  exact ⟨yoneda.preimage cc,
    ((congrArg (fun m => m ≫ Q.1.hom) (yoneda.map_preimage cc)).trans hcc2).symm,
    hcc1.symm.trans (congrArg (fun m => (Z.1.preimage P.1.hom).ι ≫ m)
      (yoneda.map_preimage cc).symm)⟩

/-! ### The two chart morphisms coincide -/

/-- **Two morphisms agreeing on the thickening with equal comorphisms pull regular functions
back along their chart morphisms in the same way.**

The chart projections of the comorphism at the indices attached to the charts of `Z` above
`Z ×_X P` are jointly injective
(`AlgebraicGeometry.Space.directImageChartProjection_ext`), each of those indices is the same
for the two morphisms, and the unit of a thickening is injective on the sections over an étale
chart (`AlgebraicGeometry.Space.bijective_thickeningRingUnit_app`). -/
theorem chartPullback_eq_of_structureSharpThroughThickeningAt_eq
    (hZ : IsThickening B S hS X Z.1) (c c' : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e)
    (hAt : structureSharpThroughThickeningAt B S hS Z c e h =
      structureSharpThroughThickeningAt B S hS Z c' e h')
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε ε' : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom)
    (hε' : P.1.hom ≫ c'.hom = yoneda.map ε' ≫ Q.1.hom)
    (hres : ∀ k : StructuredArrow
        (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) P))
        (comparisonFunctor B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op,
      chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε =
        chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) P k ≫ ε')
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op Q))) :
    chartPullback B S hS c Q (indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩) b =
      chartPullback B S hS c' Q (indexOfChartDiagram B S hS c' ⟨P, Q, ε', hε'⟩) b := by
  refine (bijective_thickeningRingUnit_app B S hS Z hZ (op P)).1 ?_
  refine directImageChartProjection_ext B S hS (subspaceInclusion B S hS X Z) P
    ((sheafCompose (SmallEtale.topology B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
      (CategoryTheory.forget RingCat.{u})).obj
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) fun k => ?_
  refine (directImageChartProjection_structureSharpThroughThickeningAt_common B S hS Z c e h
      Q P ε hε k (thickeningRestrictionChartIndex B S hS Z c e h Q P ε hε k)
      (chartBaseChangeMap_thickeningRestrictionChartIndex B S hS Z c e h Q P ε hε k)
      b).symm.trans ?_
  refine Eq.trans ?_ (directImageChartProjection_structureSharpThroughThickeningAt_common
    B S hS Z c' e h' Q P ε' hε' k (thickeningRestrictionChartIndex B S hS Z c e h Q P ε hε k)
    ((chartBaseChangeMap_thickeningRestrictionChartIndex B S hS Z c e h Q P ε hε k).trans
      (hres k)) b)
  rw [hAt]

/-- `AlgebraicGeometry.Space.chartPullback` at the index of a chart diagram, read on a section:
it is pullback of global sections along the vertical morphism of schemes of the diagram. -/
theorem chartPullback_apply_appTop {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    chartPullback B S hS f V j b =
      (((BigFppfOver.toScheme B S hS).map
        (chartBaseChangeMap B S hS f V j)).appTop).hom b := rfl

/-- **Two chart morphisms into an affine chart which pull regular functions back in the same way
are equal.**  A morphism into an affine scheme is determined by its map of global sections,
`AlgebraicGeometry.ext_of_isAffine`, and the functor to schemes is faithful on the morphisms over
`S`. -/
theorem chartHom_eq_of_chartPullback_eq (c c' : X ⟶ W)
    (Q : SmallEtale B S hS W.1) (P : SmallEtale B S hS X.1)
    (ε ε' : (SmallEtale.toOver B S hS X.1).obj P ⟶ (SmallEtale.toOver B S hS W.1).obj Q)
    (hε : P.1.hom ≫ c.hom = yoneda.map ε ≫ Q.1.hom)
    (hε' : P.1.hom ≫ c'.hom = yoneda.map ε' ≫ Q.1.hom)
    (hQ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj Q)))
    (hpull : ∀ b : ToType ((structureRingSheaf B S hS W).obj.obj (op Q)),
      chartPullback B S hS c Q (indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩) b =
        chartPullback B S hS c' Q (indexOfChartDiagram B S hS c' ⟨P, Q, ε', hε'⟩) b) :
    ε = ε' := by
  have := hQ
  refine (BigFppfOver.toScheme B S hS).map_injective (ext_of_isAffine
    (CommRingCat.hom_ext (RingHom.ext fun b => ?_)))
  have h1 := chartPullback_apply_appTop B S hS c Q
    (indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩) b
  have h2 := chartPullback_apply_appTop B S hS c' Q
    (indexOfChartDiagram B S hS c' ⟨P, Q, ε', hε'⟩) b
  rw [chartBaseChangeMap_indexOfChartDiagram B S hS c ⟨P, Q, ε, hε⟩] at h1
  rw [chartBaseChangeMap_indexOfChartDiagram B S hS c' ⟨P, Q, ε', hε'⟩] at h2
  exact h1.symm.trans ((hpull b).trans h2)

/-! ### From the charts to the two morphisms -/

/-- **Two morphisms agreeing on the thickening with equal comorphisms agree on every chart of
`X` carrying an affine chart diagram.** -/
theorem comp_eq_of_hasAffineChartDiagram
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c c' : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e)
    (hAt : structureSharpThroughThickeningAt B S hS Z c e h =
      structureSharpThroughThickeningAt B S hS Z c' e h')
    (P : SmallEtale B S hS X.1) (hP : HasAffineChartDiagram B S hS c P) :
    P.1.hom ≫ c.hom = P.1.hom ≫ c'.hom := by
  obtain ⟨-, Q, q, hq, hQaff⟩ := hP
  obtain ⟨ε', hε', hrestr⟩ :=
    exists_chartHom_agreeing_on_thickening B S hS Z hZ c c' (h.trans h'.symm) Q P q hq.symm
  have hεeq : q = ε' :=
    chartHom_eq_of_chartPullback_eq B S hS c c' Q P q ε' hq.symm hε' hQaff fun b =>
      chartPullback_eq_of_structureSharpThroughThickeningAt_eq B S hS Z hZ.isThickening c c'
        e h h' hAt Q P q ε' hq.symm hε'
        (fun k => comp_chartBaseChangeMap_eq_of_thickeningRestriction_eq B S hS Z P Q q ε'
          hrestr k) b
  exact hq.symm.trans ((congrArg (fun m => yoneda.map m ≫ Q.1.hom) hεeq).trans hε'.symm)

/-- The sieve of the étale charts of `X` on which two morphisms out of `X` agree. -/
private def agreementChartSieve (c c' : X ⟶ W) (U : SmallEtale B S hS X.1) : Sieve U where
  arrows V _ := V.1.hom ≫ c.hom = V.1.hom ≫ c'.hom
  downward_closed := by
    intro V V' a ha g
    have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map g) ≫ V.1.hom = V'.1.hom :=
      CostructuredArrow.w g.hom
    rw [← hw, Category.assoc, Category.assoc, ha]

/-- **Two morphisms agreeing on the thickening with equal comorphisms agree on every étale chart
of `X`.**  The charts carrying an affine chart diagram are cover-dense, and the morphisms from
the étale charts of `X` into `W` form a sheaf on the small étale site of `X`. -/
theorem comp_eq_chart_of_structureSharpThroughThickeningAt_eq
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c c' : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e)
    (hAt : structureSharpThroughThickeningAt B S hS Z c e h =
      structureSharpThroughThickeningAt B S hS Z c' e h')
    (U : SmallEtale B S hS X.1) :
    U.1.hom ≫ c.hom = U.1.hom ≫ c'.hom := by
  have hsep : Presheaf.IsSeparated (SmallEtale.topology B S hS X.1)
      ((SmallEtale.toOver B S hS X.1).op ⋙ W.1) :=
    (SmallEtale.isSheaf_comp_toOver B S hS X.1 W.2.isSheaf).isSeparated
  have hR : agreementChartSieve B S hS c c' U ∈ SmallEtale.topology B S hS X.1 U :=
    mem_topology_of_hasAffineChartDiagram B S hS c U (agreementChartSieve B S hS c c' U)
      fun {V} _ hV => comp_eq_of_hasAffineChartDiagram B S hS Z hZ c c' e h h' hAt V hV
  have key : (yonedaEquiv (U.1.hom ≫ c.hom) :
      W.1.obj (op ((SmallEtale.toOver B S hS X.1).obj U))) =
      yonedaEquiv (U.1.hom ≫ c'.hom) := by
    refine hsep U (agreementChartSieve B S hS c c' U) hR _ _ ?_
    intro V a ha
    have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map a) ≫ U.1.hom = V.1.hom :=
      CostructuredArrow.w a.hom
    show W.1.map ((SmallEtale.toOver B S hS X.1).map a).op
        (yonedaEquiv (U.1.hom ≫ c.hom)) =
      W.1.map ((SmallEtale.toOver B S hS X.1).map a).op
        (yonedaEquiv (U.1.hom ≫ c'.hom))
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality, ← Category.assoc, ← Category.assoc, hw]
    exact congrArg yonedaEquiv ha
  exact yonedaEquiv.injective key

/-- **Two morphisms agreeing on a first order thickening whose comorphisms read in the common
target agree are equal.**

This is the faithfulness on which the uniqueness half of [Stacks Project, Tag 0CKE] rests, and
it needs neither [Stacks Project, Tag 04KL] nor the identification of the small étale topoi of a
thickening: the comorphisms are compared on affine étale chart diagrams, through which both
morphisms factor by [Stacks Project, Tag 0611]. -/
theorem eq_of_structureSharpThroughThickeningAt_eq
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c c' : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e)
    (hAt : structureSharpThroughThickeningAt B S hS Z c e h =
      structureSharpThroughThickeningAt B S hS Z c' e h') :
    c = c' := by
  obtain ⟨U, f, hfS, hfE⟩ := X.2.exists_atlas
  refine ObjectProperty.hom_ext _
    (hom_ext_of_etale_atlas B S hS X.2.isSheaf W.2.isSheaf f hfS hfE ?_)
  exact comp_eq_chart_of_structureSharpThroughThickeningAt_eq B S hS Z hZ c c' e h h' hAt
    ⟨CostructuredArrow.mk f, hfE⟩

/-- **Two morphisms agreeing on a first order thickening with equal transported comorphisms are
equal.**  This is
`AlgebraicGeometry.Space.eq_of_structureSharpThroughThickeningAt_eq` with the hypothesis in the
spelling `AlgebraicGeometry.Space.restrictedSharpThroughThickening`, which is the one the
difference of two sections of [Stacks Project, Tag 0CKB] produces: the two spellings determine
one another by
`restrictedSharpThroughThickening_eq_iff_structureSharpThroughThickeningAt_eq`. -/
theorem eq_of_restrictedSharpThroughThickening_eq
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (W₀ : ClosedSubspaces B S hS W.1) (c c' : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (heq : restrictedSharpThroughThickening B S hS Z W₀ c e₀ h =
      restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h') :
    c = c' :=
  eq_of_structureSharpThroughThickeningAt_eq B S hS Z hZ c c'
    (e₀ ≫ subspaceInclusion B S hS W W₀) h h'
    ((restrictedSharpThroughThickening_eq_iff_structureSharpThroughThickeningAt_eq
      B S hS Z W₀ c c' e₀ h h').1 heq)

end AlgebraicGeometry.Space

end
