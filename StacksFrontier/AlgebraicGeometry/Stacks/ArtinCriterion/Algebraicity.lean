module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.SetTheory.Cardinal.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatUniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphismRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.CoarserTopology
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCompositeSnd
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindexSnd
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.Deformation.Artin.LimitPreserving
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.SmoothNeighborhood
import all StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStackIsFppfStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.ChartCoproduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.Surjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.Smoothness
import all StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.ChartCoproduct
import all StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.Surjectivity
import all StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.Smoothness

/-!
# Artin's criterion (Stacks 07Y4)

**Stacks 07Y4** is Artin's criterion: a category fibred in groupoids `𝒳` over a locally Noetherian
scheme `S` is an algebraic stack as soon as its diagonal is representable by algebraic spaces, it
satisfies Artin's axioms [-1], [0], [1], [2] and [3], all of its formal objects are effective,
versality is open, and the local rings of `S` at its finite type points are G-rings.

Its proof has two halves. The first is **Stacks 07XY** (Lemma 98.13.8): every finite type
field-valued object of `𝒳` has a *smooth neighbourhood of finite type* — a scheme `U` of finite
type over `S`, an object of `𝒳` over `U` restricting to the given one at a finite type point with
the given residue field, and a 1-morphism `(Sch/U) ⟶ 𝒳` representable by algebraic spaces and
smooth. That half is where every deformation-theoretic hypothesis of 07Y4 is consumed: axioms [2]
and [3], effectivity, openness of versality and the G-ring condition appear nowhere else. The
second half, which is this file and the parts it imports, assembles those neighbourhoods into an
atlas: one takes the coproduct `U = ⨿ U_{k, x₀}` over the finite type field-valued objects — this
is where axiom [-1] enters, bounding the index set so that the coproduct is an object of the chosen
big site — shows the resulting 1-morphism is smooth because it is so on each open piece, and shows
it is surjective because its image is open and contains every finite type point.

The predicates of the criterion are defined in the parts:
`AlgebraicGeometry.Stack.IsSizeBounded` (axiom [-1]) in
`StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.ChartCoproduct`,
`AlgebraicGeometry.Stack.HasSmoothFiniteTypeNeighborhoods` (the conclusion of Stacks 07XY) in
`StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.Surjectivity`, and
`AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces` (the tangent-space half of axiom [3])
in `StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.Smoothness`.

The second half is isolated as
`AlgebraicGeometry.Stack.isAlgebraicStack_of_hasSmoothFiniteTypeNeighborhoods`, which carries the
first half as the hypothesis `hnbhd`, `AlgebraicGeometry.Stack.HasSmoothFiniteTypeNeighborhoods`,
and takes only the hypotheses of Stacks 07Y4 that the second half uses: the diagonal clause, axiom
[-1], the stack clause and axiom [1]. The first half is then supplied from
Stacks 07XY, `Deformation.Artin.exists_smooth_finiteType_neighborhood`, and the two are composed
by `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms`.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms`: **Stacks 07Y4**, Artin's criterion,
  with axiom [0] the étale stack condition of the source.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms_of_isStack`: the same with axiom [0]
  given as the fppf stack condition, which implies the étale one.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_hasSmoothFiniteTypeNeighborhoods`: its second
  half, Stacks 07Y4 with Stacks 07XY taken as a hypothesis.
* `AlgebraicGeometry.Stack.hasSmoothFiniteTypeNeighborhoods_of_artinAxioms`: its first half,
  Stacks 07XY in the shape that hypothesis asks for.

## Implementation notes

*Why the two halves are separate declarations.* `hnbhd` produces, for each finite type
field-valued object, a smooth chart of `𝒳` *through that object*. It is not an atlas: nothing in it
says the charts jointly cover `𝒳`, which is exactly the surjectivity the assembly proves, and it is
not algebraicity of `𝒳`, which also needs the stack and diagonal clauses. Keeping it a named
hypothesis of a separate declaration records which of the source's hypotheses each half consumes:
the axioms
[2] and [3], effectivity, openness of versality and the G-ring condition are used only to
produce `hnbhd`, and never by the assembly.

*The stack clause.* The source's axiom [0] is the étale stack condition, in the family-indexed
rendering `CategoryTheory.Functor.IsStackInGroupoids` of Stacks 02ZI, and that is what the
assembly takes. The source's proof upgrades it to the fppf stack condition through Stacks 076V
once the atlas is built: that is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_isStackInGroupoids_etale_of_smooth`, applied to the
surjective smooth atlas the assembly constructs.

*Universes.* The morphism universe of `𝒳` is free in the assembly:
`AlgebraicGeometry.Stack.isAlgebraicStack_of_hasSmoothFiniteTypeNeighborhoods` and the three
predicates it consumes — `AlgebraicGeometry.Stack.IsSizeBounded`,
`AlgebraicGeometry.Stack.HasSmoothFiniteTypeNeighborhoods` and
`AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces` — are stated at
`CategoryTheory.CatFiberedInGroupoids.{u, vX, u + 1, uX}`. In particular a moduli stack whose
morphisms carry data indexed by the objects of the site — the category of families of curves of
Stacks 0D4Z is one, a morphism of families carrying a morphism of algebraic spaces, i.e. of
presheaves on a site whose objects form a `Type (u + 1)`, so that
`AlgebraicGeometry.curvesFiberedCategory` is a
`CategoryTheory.CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}` — is covered.

Three inputs used to force the pin and no longer do. Stacks 07WI,
`AlgebraicGeometry.Stack.hasRelativeProperty_of_affine_locallyOfFinitePresentation_univ`, which
turns surjectivity at the affine finitely presented stages into the relative property of Stacks
03YK, takes a based functor and a target at free universes; the limit-preservation input it needs
is `AlgebraicGeometry.Stack.isLimitPreservingOverTerminal_of_isLimitPreserving`, whose `𝒳` is
likewise at free universes, in place of the implication (2) ⟹ (1) of Stacks 07XN, which names
`AlgebraicGeometry.Stack.terminalCFG` and so does pin them; and the deformation layer —
`Deformation.Artin.IsLimitPreserving`, `Deformation.Artin.SatisfiesRS`,
`Deformation.Artin.FormalObject` — is at a free morphism universe. The isomorphism-class layer,
`CategoryTheory.PresheafOfCategories.isoClassEquiv`, is applied only to categories over the site
whose morphisms are in the site's universe `u` (those of the `representedMap` section of
`StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.Smoothness`).

Artin's criterion itself, `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms_of_isStack`,
is stated at `CategoryTheory.CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}`, the
assembly being at free object and morphism universes: that is the shape of Stacks 07XY, whose
`𝒳` is a `CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}`.

The index universes of axiom [1] are pinned to contain `u`, as in
`Deformation.Artin.IsLimitPreserving`: the directed systems the proof descends along are indexed by
the poset of finite type subfields of a residue field, which lives in `Type u`.

## References

* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07Y3](https://stacks.math.columbia.edu/tag/07Y3)
* [Stacks Project, Tag 07XY](https://stacks.math.columbia.edu/tag/07XY)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 076V](https://stacks.math.columbia.edu/tag/076V)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v v' v'' w z vX vI wI uX

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open CategoryTheory.Limits

private def reindexSndRepresentingEquivalence
    {C A D X T : Type*} [Category C] [Category A] [Category D] [Category X] [Category T]
    (pA : A ⥤ C) (pD : D ⥤ C) (pX : X ⥤ C) (y : A ⥤ X)
    {g g' : D ⥤ X} (e : g ≅ g')
    (he : ∀ t, pX.IsHomLift (𝟙 (pD.obj t)) (e.hom.app t)) (r : T ⥤ A)
    (E : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst pA pD pX y g') r) :
    StacksRepresentableCFG.EquivalenceOver (TwoFibreProductOver.fst pA pD pX y g) r :=
  (TwoFibreProductOver.reindexSndEquivalenceOver (p𝒳 := pA) (F := y) e he).trans E

private theorem isAlgebraicStack_of_smooth_of_field_models [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, max u vI, max u wI, uX, vX} B S hS 𝒳)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (z : 𝒳.val.p.Fiber W)
    (g : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒳.val)
    (heval : Nonempty ((Functor.twoYonedaEvaluation 𝒳.val.p W).obj g ≅ z))
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g)
    (hmodels : ∀ d : finiteTypeFieldBaseData S,
      ∀ x : 𝒳.val.p.Fiber (fieldBaseOver B S hS d.1),
      ∃ (a : fieldBaseOver B S hS d.1 ⟶ W) (r : x.1 ⟶ z.1),
        𝒳.val.p.IsHomLift a r)
    (hsmooth : ∀ (V : AlgebraicGeometry.BigFppfOver B S hS)
      (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
      (_hy : y ⋙ 𝒳.val.p = Over.map V.hom)
      (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom)
          (schemeFibredCategory B S hS W).val.p 𝒳.val.p y g.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      AlgebraicGeometry.Space.IsSmooth B S hS
        (AlgebraicGeometry.algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor
            B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom) :
    IsAlgebraicStack.{u, u + 1, vX, uX} B S hS 𝒳.val := by
  have hsurj :=
    hasRelativeProperty_of_affine_locallyOfFinitePresentation_univ.{u, vX, uX, u, u + 1, vI, wI}
      B S hS (Space.surjectiveMorphismProperty B S hS) g hrep
      (isLimitPreservingOverTerminal_of_isLimitPreserving.{u, max u vI, max u wI}
        B S hS 𝒳 hlimit)
      (fun V _ hlfp y hy F hF e => by
        let : LocallyOfFinitePresentation (B.inclusion.map V.hom) := hlfp
        exact isSurjective_of_field_models B S hS 𝒳 W z g heval hmodels V y hy F hF
          e.some (hsmooth V y hy F hF e))
  exact isAlgebraicStack_of_isStackInGroupoids_etale_of_smooth.{u, vX, uX, u + 1} B S hS 𝒳.val
    hstack ((hasRepresentableDiagonal_iff B S hS 𝒳).1 hdiag) W g
    (fun V y hy F hF e => ⟨hsurj V y hy F hF e, hsmooth V y hy F hF e⟩)

/-- **Stacks 07Y4, reduced to Stacks 07XY.** A category fibred in groupoids over a locally
Noetherian scheme whose diagonal is representable by algebraic spaces, which satisfies axiom [-1]
and axiom [0] (the étale stack condition), which is limit preserving (axiom [1]), and every finite
type field-valued object of which has a smooth finite type neighbourhood, is an algebraic stack.

This is the whole of the source's proof of Stacks 07Y4 except for its appeal to Stacks 07XY
(Lemma 98.13.8), which is `hnbhd`. -/
public theorem isAlgebraicStack_of_hasSmoothFiniteTypeNeighborhoods [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hsize : IsSizeBounded B S hS 𝒳)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, max u vI, max u wI, uX, vX} B S hS 𝒳)
    (hnbhd : HasSmoothFiniteTypeNeighborhoods B S hS 𝒳) :
    IsAlgebraicStack.{u, u + 1, vX, uX} B S hS 𝒳.val := by
  classical
  let : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_bounded_fieldFiber_index B S hS 𝒳 hsize
  let d (i : I) := (eI i).1
  let k (i : I) := FreeCommRing S.size.out ⧸ (d i).1.2.1.1
  let (i : I) : Field (k i) := fieldBaseField S (d i).1
  let x₀ (i : I) := (eI i).2.out.1
  have hx₀ (i : I) : (𝒳.val.p ⋙ Over.post B.inclusion).obj (x₀ i) =
      Over.mk (fieldBaseMap S (d i).1) :=
    congrArg (Over.post B.inclusion).obj (eI i).2.out.2
  choose U x hx u₀ e r f hU using fun i : I =>
    hnbhd (k i) (fieldBaseMap S (d i).1) (x₀ i) (hx₀ i)
      (d i).2.1 (d i).2.2
      ((fieldBaseMap S (d i).1) (IsLocalRing.closedPoint (k i))) rfl
  have hfiniteU (i : I) : Deformation.Artin.IsFiniteTypeOver B S hS (U i) :=
    ⟨(hU i).1, (hU i).2.1⟩
  let W := finiteTypeCoproduct B S hS U hI hfiniteU
  let j := finiteTypeCoproductι B S hS U hI hfiniteU
  obtain ⟨xW, hxW⟩ := exists_fiber_of_coproduct B S hS 𝒳.val.p hstack U W j
    (Iso.refl _) (fun i => Category.comp_id _) (fun i => ⟨x i, hx i⟩)
  let ev := Functor.twoYonedaEvaluation 𝒳.val.p W
  let : ev.IsEquivalence :=
    Functor.twoYonedaEvaluation_isEquivalence 𝒳.val.p 𝒳.property W
  let g := ev.objPreimage xW
  have hrestr (i : I) : Nonempty (precomposeSchemePoint 𝒳.val.p (j i) g ≅ f i) := by
    apply schemePoint_iso_of_evaluation_iso 𝒳.val.p 𝒳.property (U i)
    exact ⟨precomposeSchemePoint_evaluationIso 𝒳.val.p 𝒳.property (j i) g ≪≫
      Functor.pullbackFiberIso (ev.objObjPreimageIso xW) (j i) ≪≫
      (hxW i).some ≪≫ (hU i).2.2.2.2.2.1.some.symm⟩
  have hmodels₀ (q : Σ d : finiteTypeFieldBaseData S,
      Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS d.1)))) :
      ∃ (a : fieldBaseOver B S hS q.1.1 ⟶ W) (r : q.2.out.1 ⟶ xW.1),
        𝒳.val.p.IsHomLift a r := by
    obtain ⟨i, rfl⟩ := eI.surjective q
    let a := eqToHom (eI i).2.out.2.symm ≫ 𝒳.val.p.map (r i) ≫ eqToHom (hx i)
    have ha : 𝒳.val.p.IsHomLift a (r i) :=
      IsHomLift.of_fac 𝒳.val.p a (r i) (eI i).2.out.2 (hx i) rfl
    obtain ⟨s, hs⟩ := exists_hom_to_glued_object 𝒳.val.p (j i) xW
      ⟨x i, hx i⟩ (hxW i).some (eI i).2.out a (r i) ha
    exact ⟨a ≫ j i, s, hs⟩
  have hmodels' (t : Σ d : finiteTypeFieldBaseData S,
      𝒳.val.p.Fiber (fieldBaseOver B S hS d.1)) :
      ∃ (a : fieldBaseOver B S hS t.1.1 ⟶ W) (r : t.2.1 ⟶ xW.1),
        𝒳.val.p.IsHomLift a r := by
    let y : 𝒳.val.p.Fiber (fieldBaseOver B S hS t.1.1) :=
      Quotient.out (Quotient.mk (isIsomorphicSetoid _) t.2)
    obtain ⟨a, r, hr⟩ : ∃ (a : fieldBaseOver B S hS t.1.1 ⟶ W) (r : y.1 ⟶ xW.1),
        𝒳.val.p.IsHomLift a r := hmodels₀ ⟨t.1, Quotient.mk (isIsomorphicSetoid _) t.2⟩
    have hiso : IsIsomorphic y t.2 := Quotient.mk_out (s := isIsomorphicSetoid _) t.2
    let φ := hiso.some
    let ψ : t.2.1 ⟶ y.1 := φ.inv.1
    have hψ : 𝒳.val.p.IsHomLift (𝟙 (fieldBaseOver B S hS t.1.1)) ψ := φ.inv.2
    exact ⟨a, ψ ≫ r, IsHomLift.comp_lift_id_left' 𝒳.val.p (fieldBaseOver B S hS t.1.1) ψ a r⟩
  have hrep : IsRepresentableByAlgebraicSpaces B S hS g :=
    ((AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes
        B S hS 𝒳).mp
      ((AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf
          B S hS 𝒳).mp hdiag)) W g
  refine isAlgebraicStack_of_smooth_of_field_models.{u, vX, vI, wI} B S hS 𝒳 hdiag hstack hlimit
    W xW g ⟨ev.objObjPreimageIso xW⟩ hrep (fun d x => hmodels' ⟨d, x⟩) ?_
  intro V y hy F hF eF
  apply (isSmooth_algebraicSpaceMap_iff_relocalized B S hS V F hF).mpr
  apply isSmooth_relocalized_of_open_cover B S hS 𝒳.val.p 𝒳.property W
    g.toFunctor g.w U j
    (finiteTypeCoproductι_isOpenImmersion B S hS U hI hfiniteU)
    (finiteTypeCoproductι_jointly_surjective B S hS U hI hfiniteU) V y hy F hF eF.some
  intro i
  obtain ⟨hfi, hsmi⟩ := (hU i).2.2.2.2.2.2
  obtain ⟨G, hG, ⟨eG⟩⟩ := hfi V y hy
  let ε := (hrestr i).some
  let e : (Over.map (j i) ⋙ g.toFunctor) ≅ (f i).toFunctor :=
    (BasedNatTrans.forgetful _ _).mapIso ε
  have he : ∀ t, 𝒳.val.p.IsHomLift (𝟙 ((Over.forget (U i)).obj t)) (e.hom.app t) :=
    fun t => ε.hom.isHomLift' t
  refine ⟨G, hG, ⟨reindexSndRepresentingEquivalence (Over.map V.hom)
    (Over.forget (U i)) 𝒳.val.p y e he _ eG⟩, ?_⟩
  exact (isSmooth_algebraicSpaceMap_iff_relocalized B S hS V G hG).mp
    (hsmi V y hy G hG ⟨eG⟩)

/-! ### Artin's criterion -/

/-- **Stacks 07XY, in the form Artin's criterion consumes it.** The conclusion of Stacks 07XY,
`AlgebraicGeometry.Stack.HasSmoothFiniteTypeNeighborhoods`, holds for a category fibred in
groupoids satisfying the deformation-theoretic hypotheses of Stacks 07Y4.

This is `Deformation.Artin.exists_smooth_finiteType_neighborhood` with its base named as the
object of the site it already is, and its smoothness clause read through the definition of
`AlgebraicGeometry.Stack.IsRelativelySmooth`. -/
public theorem hasSmoothFiniteTypeNeighborhoods_of_artinAxioms [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, max (u + 1) v w, max u v} B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒳)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS 𝒳.val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    HasSmoothFiniteTypeNeighborhoods B S hS 𝒳 := by
  intro k _ i₀ x₀ hx₀ hfinite₀ hqc₀ s hs
  obtain ⟨x, u₀, e, r, f, hfin, hqc, hftp, hcart, hb, heval, hsmooth⟩ :=
    Deformation.Artin.exists_smooth_finiteType_neighborhood.{u, v, w} B S hS 𝒳 k i₀ x₀ hx₀
      hfinite₀ hqc₀ s hs hdiag hlimit hRS
      (htangent k i₀ x₀ hx₀ hfinite₀ hqc₀ s hs) heffective hopen
      (hG s (hs ▸ isFiniteTypePoint_image_of_specField S i₀ hfinite₀))
  exact ⟨𝒳.val.p.obj x, x, rfl, u₀, e, r, f, hfin, hqc, hftp, hcart, hb, heval, hsmooth⟩

/-- **Artin's criterion, with axiom [0] given as the fppf stack condition.** A category fibred in
groupoids over a locally Noetherian scheme `S` is an algebraic stack as soon as its diagonal is
representable by algebraic spaces, it satisfies axiom [-1] (the set-theoretic bound of Stacks
07Y3), the fppf stack condition (which implies axiom [0]), axiom [1] (limit preservation), the
Rim–Schlessinger condition of axiom [2] and the tangent-space half of axiom [3], all of its
formal objects are effective, versality is open, and the local rings of `S` at its finite type
points are G-rings.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms` with the fppf stack condition
weakened to the étale one by `CategoryTheory.Functor.IsStackInGroupoids.of_le`. -/
public theorem isAlgebraicStack_of_artinAxioms_of_isStack [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hsize : IsSizeBounded B S hS 𝒳)
    (hfppf : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, max (u + 1) v w, max u v} B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒳)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS 𝒳.val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicStack.{u, u + 1, max u v, max (u + 1) v w} B S hS 𝒳.val :=
  let : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
  isAlgebraicStack_of_hasSmoothFiniteTypeNeighborhoods.{u, max u v, u, u, max (u + 1) v w} B S hS
    𝒳 hdiag hsize
    ((hfppf.isStackInGroupoids 𝒳.property).of_le
      (fun _ _ hS => etaleTopology_le_topology B _ hS)) hlimit
    (hasSmoothFiniteTypeNeighborhoods_of_artinAxioms B S hS 𝒳 hdiag hlimit hRS htangent
      heffective hopen hG)

/-- **Stacks 07Y4 (Artin's criterion).** Let `S` be a locally Noetherian scheme and let `𝒳` be a
category fibred in groupoids over the big fppf site of `S`. Assume that

1. the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces,
2. `𝒳` satisfies axioms [-1], [0], [1], [2] and [3]: the set-theoretic bound of Stacks 07Y3
   (`hsize`), the stack condition for the étale topology (`hstack`), limit preservation
   (`hlimit`), the Rim–Schlessinger condition (`hRS`) and finite dimensionality of tangent spaces
   (`htangent`),
3. every formal object of `𝒳` is effective,
4. `𝒳` satisfies openness of versality, and
5. `𝒪_{S, s}` is a G-ring for all finite type points `s` of `S`.

Then `𝒳` is an algebraic stack.

Axiom [0] is the source's: `𝒳` is a stack in groupoids for the étale topology. The proof is the
source's: Stacks 07XY produces, through every finite type field-valued object, a smooth finite type
neighbourhood; `AlgebraicGeometry.Stack.isAlgebraicStack_of_hasSmoothFiniteTypeNeighborhoods`
assembles them into a surjective smooth atlas; and Stacks 076V
(`AlgebraicGeometry.Stack.isAlgebraicStack_of_isStackInGroupoids_etale_of_smooth`), where the
étale stack condition of axiom [0] is used, makes `𝒳` an fppf stack and hence an algebraic stack.

Of axiom [3] only the tangent-space half is asked for, which is all Stacks 07XY uses; the index
universe of the stack condition in the conclusion is free. -/
@[stacks 07Y4]
public theorem isAlgebraicStack_of_artinAxioms [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hsize : IsSizeBounded B S hS 𝒳)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, max (u + 1) v w, max u v} B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒳)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS 𝒳.val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicStack.{u, z, max u v, max (u + 1) v w} B S hS 𝒳.val := by
  obtain ⟨hgpd, ⟨hX, -⟩, hΔ, hatlas⟩ :=
    isAlgebraicStack_of_hasSmoothFiniteTypeNeighborhoods.{u, max u v, u, u, max (u + 1) v w}
      B S hS 𝒳 hdiag hsize hstack hlimit
      (hasSmoothFiniteTypeNeighborhoods_of_artinAxioms B S hS 𝒳 hdiag hlimit hRS htangent
        heffective hopen hG)
  exact ⟨hgpd, ⟨hX, hX.isStackInGroupoids hgpd⟩, hΔ, hatlas⟩

end AlgebraicGeometry.Stack

end
