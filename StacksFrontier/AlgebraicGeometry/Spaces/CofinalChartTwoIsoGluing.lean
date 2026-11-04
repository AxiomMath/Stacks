module

public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAtlasReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap

/-!
# Gluing chartwise 2-isomorphisms of small étale ringed topoi over a cofinal family of charts

Let `ψ : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of the small étale ringed topoi
of two algebraic spaces over `S`, let `l : X ⟶ Y` be a morphism of algebraic spaces, and let `P`
be a cofinal class of affine étale charts of `X`
(`AlgebraicGeometry.Space.IsCofinalChartFamily`).  Suppose that over every `P`-chart
`b : h_T ⟶ X` the restriction of `ψ` along `b` is induced by the restriction of `l`, that is,
that `ψ ∘ b_small` is 2-isomorphic to `(b ≫ l)_small`.  This file proves that `ψ` itself is then
induced by `l`:

`AlgebraicGeometry.Space.InducesSmallEtaleRingedToposHom B S hS l ψ`.

This is step 6 of the proof of [Stacks Project, Tag 04KL] — the descent of the 2-isomorphisms —
and it is the companion of
`AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_cofinal`, which glues the *morphism*
out of chartwise morphisms but consumes its chartwise 2-isomorphisms through
[Stacks Project, Tag 04M6] and discards them.  Here the 2-isomorphisms themselves are glued.

## Main definitions

* `AlgebraicGeometry.yonedaSpace`, `…etaleChartToSpace`, `…etaleChartObj` — the
  algebraic space, structure morphism and object of the small étale site attached to a scheme
  chart `b : h_T ⟶ X`.
* `AlgebraicGeometry.Space.chartRestrictionHom` — the morphism of small étale ringed topoi of a
  chart, in the restriction presentation of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRestrictionRingedToposHom.lean`.
* `AlgebraicGeometry.Space.chartInverseImageComparison` — the isomorphism
  `ψ⁻¹(-)|_T ≅ l_small⁻¹(-)|_T` of restrictions to a chart that a chartwise 2-isomorphism
  contains.
* `AlgebraicGeometry.Space.chartSectionsComparison` — its value on sections over the chart
  itself.

## Main results

* `AlgebraicGeometry.Space.chartTwoIso_unique` — **the chartwise 2-isomorphism is unique**, by
  the rigidity of [Stacks Project, Tag 04KK]: that is what makes the chartwise data
  automatically compatible, with no cocycle condition assumed.
* `AlgebraicGeometry.Space.chartInverseImageComparison_restrict` — the comparison over a chart
  restricts to the comparison over a smaller chart.
* `AlgebraicGeometry.Space.chartSectionsComparison_naturality` — hence the values on sections are
  natural in the chart.
* `AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_cofinal` — **the gluing.**

## Implementation notes

### What makes the descent formal

Three things, none of them a gluing argument:

1. The affine `P`-charts are a **dense subsite** of the small étale site of `X`
   (`AlgebraicGeometry.Space.isDenseSubsite_cofinalChartInclusion`), so restriction of sheaves to
   them is fully faithful and
   `CategoryTheory.Functor.IsDenseSubsite.natIsoOfRestriction` produces the isomorphism
   `ψ⁻¹ ≅ l_small⁻¹` of functors from its restriction, naturality in the sheaf included.
2. A 2-isomorphism of ringed topoi **is** a compatible isomorphism of the inverse images
   (`AlgebraicGeometry.RingedToposHom.inverseImage_compat_iff`), so the chartwise data can be
   read on the source and the glued datum can be turned back into a 2-isomorphism.
3. In the restriction presentation of a chart the inverse-image form of the structure map is the
   **identity**, so the structure-map compatibility of the chartwise comparison is carried from
   a chart to a smaller chart by applying the restriction functor and nothing else.

### Why no compatibility hypothesis is needed

Over a chart the 2-isomorphism is *unique*: two of them differ by a 2-automorphism of
`(b ≫ l)_small`, and [Stacks Project, Tag 04KK] says there is none.  So the restriction of the
comparison over a chart to a smaller chart *is* the comparison over the smaller chart, and
naturality in the chart follows.  This is why the hypothesis is the bare existence of a chartwise
2-isomorphism and nothing more.

### The one propositional equality, and where it is absorbed

A morphism of charts `V ⟶ U` of the small étale site carries the commutation
`h_f ≫ b_U = b_V` as a *proof*, so the chart space of `V` composed into `X` is only
propositionally the composite through `U`.  Every statement below is therefore phrased with the
smaller chart written as `yoneda.map f ≫ b` — except
`AlgebraicGeometry.Space.chartSectionsComparison_naturality`, which takes the commutation as a
hypothesis `hbb` on a *variable* chart and substitutes it.  That is what lets the naturality be
applied at an arbitrary morphism of the subsite with no transport appearing anywhere.

### What this does not do, and what Stacks 04KL still owes

This is one step of the proof of [Stacks Project, Tag 04KL] and registers no tag.  It takes the
chartwise 2-isomorphisms as a hypothesis and says nothing about where they come from; producing
them is the other half of the existence argument, and the pieces still missing for it are listed
in the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/ExistenceChain.lean`.  In the
notation there, the chartwise datum of this file is what
`AlgebraicGeometry.Space.reflectTwoIsoSmallEtaleRingedToposHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedSmallEtaleRingedToposConjugate.lean` produces
out of the scheme-side recovery theorem, once the localized ringed topos of `g⁻¹h_V` has been
identified with the small étale ringed topos of a chart — and *that* identification is what is
blocked, at the universe of `AlgebraicGeometry.Space.smallEtaleRingedTopos`, by the obstruction
recorded at
`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/SpacesEtaleChartRelocalizedComparison.lean`.

The cofinality hypothesis `AlgebraicGeometry.Space.IsCofinalChartFamily` is the same one
`AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_cofinal` takes, and for 04KL it is
proved from the surjectivity of `∐ᵢ g⁻¹h_{Vᵢ} ⟶ *` on the small étale site in
`StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartFamilySurjective.lean`
(`AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc`), which also
records this statement with that hypothesis discharged.  That surjectivity is itself proved, from
nothing but a family of étale charts of `Y` covering the final object of the small étale site of
`Y`, in `StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartFamilyInverseImage.lean`; the form of
this statement with the cofinality hypothesis gone is
`AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_coversTop` there.  Nothing here
assumes it of a particular `P`:
`AlgebraicGeometry.Space.isCofinalChartFamily_top` shows `P = ⊤` is cofinal, so the statement
specialises to "chartwise over every affine étale chart implies global", and with
`ψ = l_small` the hypothesis is `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso`, so
neither hypothesis is vacuous.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04KK](https://stacks.math.columbia.edu/tag/04KK)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### A generic whiskering lemma -/

namespace Stacks.CategoryTheory

/-- **Whiskering an isomorphism of functors on the right carries a factorization through it to
the image of that factorization.**  If `A : F ≅ G` and `A.hom.app O ≫ a = a'`, then
`(A ⊗ R).hom.app O ≫ R.map a = R.map a'`.  Purely formal, and isolated so that the geometric
instantiation below is one application with every argument given. -/
theorem isoWhiskerRight_hom_app_comp_map {D : Type*} [Category* D] {E : Type*} [Category* E]
    {E' : Type*} [Category* E'] {F G : D ⥤ E} (A : F ≅ G) (R : E ⥤ E') {O : D} {Z : E}
    {a : G.obj O ⟶ Z} {a' : F.obj O ⟶ Z} (h : A.hom.app O ≫ a = a') :
    (Functor.isoWhiskerRight A R).hom.app O ≫ R.map a = R.map a' := by
  rw [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, ← R.map_comp, h]

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### A scheme chart, read as an algebraic space over `X` and as an object of the site -/

/-- A scheme chart of `X`, read as a morphism of algebraic spaces from the space it
represents. -/
noncomputable abbrev etaleChartToSpace {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1) :
    yonedaSpace B S hS T ⟶ X :=
  ObjectProperty.homMk b

/-- An étale scheme chart of `X`, read as an object of the small étale site of `X`. -/
abbrev etaleChartObj {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b) : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk b, (isEtale_iff_presheaf_of_yoneda B S hS b).1 hb⟩

/-- The morphism of small étale ringed topoi of an étale scheme chart, in the presentation whose
inverse image is restriction along small étale postcomposition. -/
noncomputable abbrev chartRestrictionHom {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b) :
    RingedToposHom (smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
      (smallEtaleRingedTopos B S hS X) :=
  smallEtaleRestrictionRingedToposHom B S hS (etaleChartToSpace B S hS b) hb

/-! ### The chartwise comparison -/

variable (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (l : X ⟶ Y)

/-- **The morphism of ringed topoi of a chart composed with `l`, in the restriction
presentation.**  It is 2-isomorphic to the morphism of ringed topoi of the composite chart
`b ≫ l`, by the composition law of Stacks 03G8 and the identity 2-isomorphism between the two
presentations of the chart. -/
noncomputable def chartPhiTwoIso {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b) :
    SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS l)
        (chartRestrictionHom B S hS b hb))
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l)) :=
  (RingedToposHom.TwoIso.whiskerRight
      (twoIsoSmallEtaleRestrictionRingedToposHom B S hS (etaleChartToSpace B S hS b) hb)
      (smallEtaleRingedToposHom B S hS l)).symm.trans
    (smallEtaleRingedToposHom_compTwoIso B S hS (etaleChartToSpace B S hS b) l)

/-- **A chartwise 2-isomorphism, transported to the restriction presentation of the chart.** -/
noncomputable def chartTwoIsoOfInduces {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b)
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS l)
        (chartRestrictionHom B S hS b hb))
      (smallEtaleComp B S hS ψ (chartRestrictionHom B S hS b hb)) :=
  (chartPhiTwoIso B S hS l b hb).trans
    (t.trans
      (RingedToposHom.TwoIso.whiskerRight
        (twoIsoSmallEtaleRestrictionRingedToposHom B S hS (etaleChartToSpace B S hS b) hb) ψ))

/-- **The chartwise 2-isomorphism is unique.**  Two 2-isomorphisms between the same pair differ
by a 2-automorphism of the target, which is 2-isomorphic to the morphism of ringed topoi of the
morphism of algebraic spaces `b ≫ l`, and [Stacks Project, Tag 04KK] says such a morphism has no
non-trivial 2-endomorphisms.

So no compatibility of the chartwise data has to be assumed: there is nothing to choose. -/
theorem chartTwoIso_unique {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b)
    (t t' : SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS l)
        (chartRestrictionHom B S hS b hb))
      (smallEtaleComp B S hS ψ (chartRestrictionHom B S hS b hb))) :
    t = t' :=
  RingedToposHom.TwoIso.eq_of_rigid_of_twoIso
    (t.symm.trans (chartPhiTwoIso B S hS l b hb))
    (smallEtaleRingedToposHom_twoMorphism_eq_id B S hS (etaleChartToSpace B S hS b ≫ l)) t t'

/-- **The isomorphism of restrictions to a chart contained in a chartwise 2-isomorphism.**  A
2-isomorphism of morphisms of ringed topoi is a compatible isomorphism of the inverse images, and
the inverse image of the restriction presentation of the chart is restriction along small étale
postcomposition, so this is an isomorphism `ψ⁻¹(-)|_T ≅ l_small⁻¹(-)|_T`. -/
noncomputable def chartInverseImageComparison {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b)
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    ψ.toToposHom.inverseImage ⋙
        smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS b) hb ≅
      (smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage ⋙
        smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS b) hb :=
  (chartTwoIsoOfInduces B S hS ψ l b hb t).inverseImageIso

/-- `AlgebraicGeometry.Space.chartInverseImageComparison` unfolded, so that the 2-isomorphism
inside it can be rewritten. -/
theorem chartInverseImageComparison_def {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b)
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    chartInverseImageComparison B S hS ψ l b hb t =
      (chartTwoIsoOfInduces B S hS ψ l b hb t).inverseImageIso :=
  rfl

/-- **The structure-map compatibility of the chartwise comparison.**  Its value at the structure
sheaf of `Y` carries the restriction of the inverse-image form of `l^♯` to the restriction of that
of `ψ^♯`. -/
theorem chartInverseImageComparison_compat {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b)
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    (chartInverseImageComparison B S hS ψ l b hb t).hom.app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O) ≫
        (smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS b) hb).map
          ((smallEtaleRingedTopos B S hS X).forgetRing.map
            (smallEtaleRingedToposHom B S hS l).fSharpInverseImage) =
      (smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS b) hb).map
        ((smallEtaleRingedTopos B S hS X).forgetRing.map ψ.fSharpInverseImage) :=
  ((congrArg
      (fun z => (chartInverseImageComparison B S hS ψ l b hb t).hom.app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
            (smallEtaleRingedTopos B S hS Y).O) ≫ z)
      (forgetRing_map_comp_smallEtaleRestriction_fSharpInverseImage B S hS
        (smallEtaleRingedToposHom B S hS l) (etaleChartToSpace B S hS b) hb)).symm.trans
    (chartTwoIsoOfInduces B S hS ψ l b hb t).inverseImageIso_fSharpInverseImage).trans
      (forgetRing_map_comp_smallEtaleRestriction_fSharpInverseImage B S hS ψ
        (etaleChartToSpace B S hS b) hb)

/-- The whiskering of the chartwise comparison by restriction along a morphism of chart spaces,
read at a sheaf: it is the restriction of the comparison's value there.  Definitional, and
recorded so that the compatibility below never has to be unified against the whiskering. -/
theorem chartInverseImageComparison_whisker_hom_app {T T' : BigFppfOver B S hS}
    (b : yoneda.obj T ⟶ X.1) (hb : IsEtale B S hS b) (fl : T' ⟶ T)
    (hfl : IsEtale B S hS (yoneda.map fl))
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b))))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (Functor.isoWhiskerRight (chartInverseImageComparison B S hS ψ l b hb t)
        (smallEtaleSetRestriction B S hS
          (etaleChartToSpace B S hS (yoneda.map fl)) hfl)).hom.app G =
      (smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS (yoneda.map fl)) hfl).map
        ((chartInverseImageComparison B S hS ψ l b hb t).hom.app G) :=
  rfl

/-- **Restriction along a composite chart is restriction twice**, on morphisms.  Definitional —
`AlgebraicGeometry.Space.smallEtalePostcomp` of a composite is the composite of the
postcompositions and restriction along a composite functor is the composite of the restrictions —
and recorded because the two spellings are not syntactically equal, so
`CategoryTheory.Functor.map_comp` does not fire across them. -/
theorem smallEtaleSetRestriction_chart_comp_map {T T' : BigFppfOver B S hS}
    (b : yoneda.obj T ⟶ X.1) (hb : IsEtale B S hS b) (fl : T' ⟶ T)
    (hfl : IsEtale B S hS (yoneda.map fl)) (hb' : IsEtale B S hS (yoneda.map fl ≫ b))
    {F F' : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (h : F ⟶ F') :
    (smallEtaleSetRestriction B S hS
        (etaleChartToSpace B S hS (yoneda.map fl ≫ b)) hb').map h =
      (smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS (yoneda.map fl)) hfl).map
        ((smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS b) hb).map h) :=
  rfl

/-- **The whiskered chartwise comparison satisfies the structure-map compatibility over the
smaller chart.**  In the restriction presentation the inverse-image form of the structure map of
a chart is the identity, so the structure map of a composite is the restriction of the outer one;
applying the restriction functor to the compatibility over `b` is therefore exactly the
compatibility over `yoneda.map f ≫ b`. -/
theorem chartInverseImageComparison_whisker_compat {T T' : BigFppfOver B S hS}
    (b : yoneda.obj T ⟶ X.1) (hb : IsEtale B S hS b) (fl : T' ⟶ T)
    (hfl : IsEtale B S hS (yoneda.map fl)) (hb' : IsEtale B S hS (yoneda.map fl ≫ b))
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    (Functor.isoWhiskerRight (chartInverseImageComparison B S hS ψ l b hb t)
          (smallEtaleSetRestriction B S hS
            (etaleChartToSpace B S hS (yoneda.map fl)) hfl)).hom.app
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
          (smallEtaleRingedTopos B S hS Y).O) ≫
        (smallEtaleRingedTopos B S hS (yonedaSpace B S hS T')).forgetRing.map
          (RingedToposHom.comp (smallEtaleRingedToposHom B S hS l)
            (chartRestrictionHom B S hS (yoneda.map fl ≫ b) hb')).fSharpInverseImage =
      (smallEtaleRingedTopos B S hS (yonedaSpace B S hS T')).forgetRing.map
        (RingedToposHom.comp ψ
          (chartRestrictionHom B S hS (yoneda.map fl ≫ b) hb')).fSharpInverseImage := by
  rw [chartInverseImageComparison_whisker_hom_app B S hS ψ l b hb fl hfl t,
    forgetRing_map_comp_smallEtaleRestriction_fSharpInverseImage B S hS
      (smallEtaleRingedToposHom B S hS l) (etaleChartToSpace B S hS (yoneda.map fl ≫ b)) hb',
    forgetRing_map_comp_smallEtaleRestriction_fSharpInverseImage B S hS ψ
      (etaleChartToSpace B S hS (yoneda.map fl ≫ b)) hb',
    smallEtaleSetRestriction_chart_comp_map B S hS b hb fl hfl hb',
    smallEtaleSetRestriction_chart_comp_map B S hS b hb fl hfl hb']
  exact Stacks.CategoryTheory.isoWhiskerRight_hom_app_comp_map
    (chartInverseImageComparison B S hS ψ l b hb t)
    (smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS (yoneda.map fl)) hfl)
    (chartInverseImageComparison_compat B S hS ψ l b hb t)

/-- **The restriction of the chartwise comparison along a morphism of charts, read back as a
2-isomorphism over the smaller chart.**  The retyping of the whiskered comparison as a comparison
of the inverse images over the composite chart is definitional — restriction along a composite
chart is restriction twice — and is performed here, in its own declaration. -/
noncomputable def chartTwoIsoOfWhisker {T T' : BigFppfOver B S hS}
    (b : yoneda.obj T ⟶ X.1) (hb : IsEtale B S hS b) (fl : T' ⟶ T)
    (hfl : IsEtale B S hS (yoneda.map fl)) (hb' : IsEtale B S hS (yoneda.map fl ≫ b))
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS l)
        (chartRestrictionHom B S hS (yoneda.map fl ≫ b) hb'))
      (smallEtaleComp B S hS ψ (chartRestrictionHom B S hS (yoneda.map fl ≫ b) hb')) :=
  RingedToposHom.TwoIso.ofInverseImageIso
    (p := smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS l)
      (chartRestrictionHom B S hS (yoneda.map fl ≫ b) hb'))
    (q := smallEtaleComp B S hS ψ (chartRestrictionHom B S hS (yoneda.map fl ≫ b) hb'))
    (Functor.isoWhiskerRight (chartInverseImageComparison B S hS ψ l b hb t)
      (smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS (yoneda.map fl)) hfl))
    (chartInverseImageComparison_whisker_compat B S hS ψ l b hb fl hfl hb' t)

/-- The inverse-image form of `AlgebraicGeometry.Space.chartTwoIsoOfWhisker` is the whiskered
comparison it was built from. -/
theorem chartTwoIsoOfWhisker_inverseImageIso {T T' : BigFppfOver B S hS}
    (b : yoneda.obj T ⟶ X.1) (hb : IsEtale B S hS b) (fl : T' ⟶ T)
    (hfl : IsEtale B S hS (yoneda.map fl)) (hb' : IsEtale B S hS (yoneda.map fl ≫ b))
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    (chartTwoIsoOfWhisker B S hS ψ l b hb fl hfl hb' t).inverseImageIso =
      Functor.isoWhiskerRight (chartInverseImageComparison B S hS ψ l b hb t)
        (smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS (yoneda.map fl)) hfl) :=
  RingedToposHom.TwoIso.inverseImageIso_ofInverseImageIso
    (p := smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS l)
      (chartRestrictionHom B S hS (yoneda.map fl ≫ b) hb'))
    (q := smallEtaleComp B S hS ψ (chartRestrictionHom B S hS (yoneda.map fl ≫ b) hb'))
    (Functor.isoWhiskerRight (chartInverseImageComparison B S hS ψ l b hb t)
      (smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS (yoneda.map fl)) hfl))
    (chartInverseImageComparison_whisker_compat B S hS ψ l b hb fl hfl hb' t)

/-- **The chartwise comparison restricts to the chartwise comparison over a smaller chart.**  The
restriction of the comparison over `b` along a morphism of charts satisfies the structure-map
compatibility over the smaller chart, hence *is* a chartwise comparison there, and the chartwise
comparison is unique. -/
theorem chartInverseImageComparison_restrict {T T' : BigFppfOver B S hS}
    (b : yoneda.obj T ⟶ X.1) (hb : IsEtale B S hS b) (fl : T' ⟶ T)
    (hfl : IsEtale B S hS (yoneda.map fl)) (hb' : IsEtale B S hS (yoneda.map fl ≫ b))
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b))))
    (t' : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS (yoneda.map fl ≫ b) ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS (yoneda.map fl ≫ b))))) :
    chartInverseImageComparison B S hS ψ l (yoneda.map fl ≫ b) hb' t' =
      Functor.isoWhiskerRight (chartInverseImageComparison B S hS ψ l b hb t)
        (smallEtaleSetRestriction B S hS (etaleChartToSpace B S hS (yoneda.map fl)) hfl) := by
  conv_lhs => rw [chartInverseImageComparison_def,
    chartTwoIso_unique B S hS ψ l (yoneda.map fl ≫ b) hb'
      (chartTwoIsoOfInduces B S hS ψ l (yoneda.map fl ≫ b) hb' t')
      (chartTwoIsoOfWhisker B S hS ψ l b hb fl hfl hb' t)]
  exact chartTwoIsoOfWhisker_inverseImageIso B S hS ψ l b hb fl hfl hb' t

/-! ### The chartwise comparison on sections over the chart -/

/-- **The chartwise comparison, read on sections over the chart itself.**  Restriction to a chart
evaluated at the identity chart of the chart space is evaluation at the chart, so this is a
bijection of the sections of `ψ⁻¹G` and of `l_small⁻¹G` over the chart. -/
noncomputable def chartSectionsComparison {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b)
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b))))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (ψ.toToposHom.inverseImage.obj G).obj.obj (op (etaleChartObj B S hS b hb)) ⟶
      ((smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage.obj G).obj.obj
        (op (etaleChartObj B S hS b hb)) :=
  ((chartInverseImageComparison B S hS ψ l b hb t).hom.app G).hom.app (op (selfChart B S hS T))

/-- `AlgebraicGeometry.Space.chartSectionsComparison` unfolded, so that the chartwise comparison
inside it can be rewritten. -/
theorem chartSectionsComparison_eq {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b)
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b))))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    chartSectionsComparison B S hS ψ l b hb t G =
      ((chartInverseImageComparison B S hS ψ l b hb t).hom.app G).hom.app
        (op (selfChart B S hS T)) :=
  rfl

/-- The inverse of `AlgebraicGeometry.Space.chartSectionsComparison`. -/
noncomputable def chartSectionsComparisonInv {T : BigFppfOver B S hS} (b : yoneda.obj T ⟶ X.1)
    (hb : IsEtale B S hS b)
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b))))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    ((smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage.obj G).obj.obj
        (op (etaleChartObj B S hS b hb)) ⟶
      (ψ.toToposHom.inverseImage.obj G).obj.obj (op (etaleChartObj B S hS b hb)) :=
  ((chartInverseImageComparison B S hS ψ l b hb t).inv.app G).hom.app (op (selfChart B S hS T))

/-- **The chartwise comparison on sections is natural in the chart.**  The commutation
`h_f ≫ b = b'` of a morphism of charts is taken as a hypothesis on a *variable* chart `b'` and
substituted, after which the statement is the naturality of the chartwise comparison over `b`
read at the object `h_f` of the small étale site of the chart space, together with
`AlgebraicGeometry.Space.chartInverseImageComparison_restrict`. -/
theorem chartSectionsComparison_naturality {T T' : BigFppfOver B S hS}
    (b : yoneda.obj T ⟶ X.1) (hb : IsEtale B S hS b)
    (b' : yoneda.obj T' ⟶ X.1) (hb' : IsEtale B S hS b')
    (fl : T' ⟶ T) (hfl : IsEtale B S hS (yoneda.map fl))
    (hbb : yoneda.map fl ≫ b = b')
    (t : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b))))
    (t' : SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b' ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b'))))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    chartSectionsComparison B S hS ψ l b hb t G ≫
        ((smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage.obj G).obj.map
          (ObjectProperty.homMk (CostructuredArrow.homMk fl hbb) :
            etaleChartObj B S hS b' hb' ⟶ etaleChartObj B S hS b hb).op =
      (ψ.toToposHom.inverseImage.obj G).obj.map
          (ObjectProperty.homMk (CostructuredArrow.homMk fl hbb) :
            etaleChartObj B S hS b' hb' ⟶ etaleChartObj B S hS b hb).op ≫
        chartSectionsComparison B S hS ψ l b' hb' t' G := by
  subst hbb
  rw [chartSectionsComparison_eq, chartSectionsComparison_eq,
    chartInverseImageComparison_restrict B S hS ψ l b hb fl hfl hb' t t']
  exact (((chartInverseImageComparison B S hS ψ l b hb t).hom.app G).hom.naturality
    (ObjectProperty.homMk (CostructuredArrow.homMk fl (Category.comp_id _)) :
      etaleChartObj B S hS (X := yonedaSpace B S hS T) (yoneda.map fl) hfl ⟶
        selfChart B S hS T).op).symm

/-! ### Gluing over the cofinal family -/

section Glue

variable (P : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X.1) → Prop)
    (τ : ∀ Vc : CofinalChart B S hS P, SmallEtaleTwoIso B S hS
      (smallEtaleRingedToposHom B S hS
        (etaleChartToSpace B S hS Vc.obj.obj.hom ≫ l))
      (smallEtaleComp B S hS ψ
        (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS Vc.obj.obj.hom))))

/-- The étaleness of a chart of the cofinal subcategory, as a morphism of presheaves. -/
theorem isEtale_cofinalChart_hom (Vc : CofinalChart B S hS P) :
    IsEtale B S hS Vc.obj.obj.hom :=
  (isEtale_iff_presheaf_of_yoneda B S hS Vc.obj.obj.hom).2 Vc.obj.property

/-- The étaleness of the morphism of charts underlying a morphism of the cofinal
subcategory. -/
theorem isEtale_yoneda_map_cofinalChart_hom {Vc Vc' : CofinalChart B S hS P} (r : Vc' ⟶ Vc) :
    IsEtale B S hS (yoneda.map r.hom.hom.left) :=
  (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map r.hom.hom.left)).2
    (SmallEtale.presheaf_etale_yoneda_map B S hS r.hom.hom.left Vc'.obj.property
      Vc.obj.property (CostructuredArrow.w r.hom.hom))

/-- **The chartwise comparison on sections, at an object of the cofinal subcategory.** -/
noncomputable def cofinalChartSections (Vc : CofinalChart B S hS P)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (ψ.toToposHom.inverseImage.obj G).obj.obj
        (op ((cofinalChartInclusion B S hS P).obj Vc)) ⟶
      ((smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage.obj G).obj.obj
        (op ((cofinalChartInclusion B S hS P).obj Vc)) :=
  chartSectionsComparison B S hS ψ l Vc.obj.obj.hom
    (isEtale_cofinalChart_hom B S hS P Vc) (τ Vc) G

/-- The chartwise comparison on sections is invertible. -/
instance isIso_cofinalChartSections (Vc : CofinalChart B S hS P)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    IsIso (cofinalChartSections B S hS ψ l P τ Vc G) := by
  change IsIso (((chartInverseImageComparison B S hS ψ l Vc.obj.obj.hom
    (isEtale_cofinalChart_hom B S hS P Vc) (τ Vc)).hom.app G).hom.app
      (op (selfChart B S hS Vc.obj.obj.left)))
  infer_instance

/-- **The chartwise comparison on sections is natural in the chart.** -/
theorem cofinalChartSections_naturality {Vc Vc' : CofinalChart B S hS P} (r : Vc' ⟶ Vc)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    cofinalChartSections B S hS ψ l P τ Vc G ≫
        ((smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage.obj G).obj.map
          ((cofinalChartInclusion B S hS P).map r).op =
      (ψ.toToposHom.inverseImage.obj G).obj.map
          ((cofinalChartInclusion B S hS P).map r).op ≫
        cofinalChartSections B S hS ψ l P τ Vc' G :=
  chartSectionsComparison_naturality B S hS ψ l Vc.obj.obj.hom
    (isEtale_cofinalChart_hom B S hS P Vc) Vc'.obj.obj.hom
    (isEtale_cofinalChart_hom B S hS P Vc') r.hom.hom.left
    (isEtale_yoneda_map_cofinalChart_hom B S hS P r) (CostructuredArrow.w r.hom.hom)
    (τ Vc) (τ Vc') G

/-- Equal morphisms of sheaves have equal components. -/
private theorem sheaf_hom_app_congr {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type u)} {m m' : F ⟶ G} (h : m = m') (X : Cᵒᵖ) :
    m.hom.app X = m'.hom.app X := by
  rw [h]

/-- **The chartwise comparison on sections is natural in the sheaf.** -/
theorem cofinalChartSections_naturality_sheaf (Vc : CofinalChart B S hS P)
    {G G' : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)} (g : G ⟶ G') :
    (ψ.toToposHom.inverseImage.map g).hom.app
          (op ((cofinalChartInclusion B S hS P).obj Vc)) ≫
        cofinalChartSections B S hS ψ l P τ Vc G' =
      cofinalChartSections B S hS ψ l P τ Vc G ≫
        ((smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage.map g).hom.app
          (op ((cofinalChartInclusion B S hS P).obj Vc)) :=
  sheaf_hom_app_congr
    ((chartInverseImageComparison B S hS ψ l Vc.obj.obj.hom
      (isEtale_cofinalChart_hom B S hS P Vc) (τ Vc)).hom.naturality g) _

variable [hcd : (cofinalChartInclusion B S hS P).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- **The chartwise comparison, as a morphism of the restrictions of the two inverse images to
the cofinal subcategory.** -/
noncomputable def cofinalChartRestrictedHom
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    ((cofinalChartInclusion B S hS P).sheafPushforwardContinuous (Type u)
        (cofinalChartTopology B S hS P) (SmallEtale.topology B S hS X.1)).obj
        (ψ.toToposHom.inverseImage.obj G) ⟶
      ((cofinalChartInclusion B S hS P).sheafPushforwardContinuous (Type u)
        (cofinalChartTopology B S hS P) (SmallEtale.topology B S hS X.1)).obj
        ((smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage.obj G) :=
  ObjectProperty.homMk
    { app := fun Vcop => cofinalChartSections B S hS ψ l P τ Vcop.unop G
      naturality := fun _ _ r =>
        (cofinalChartSections_naturality B S hS ψ l P τ r.unop G).symm }

/-- The chartwise comparison is invertible as a morphism of restrictions. -/
instance isIso_cofinalChartRestrictedHom
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    IsIso (cofinalChartRestrictedHom B S hS ψ l P τ G) := by
  have happ : ∀ Vcop : (CofinalChart B S hS P)ᵒᵖ,
      IsIso ((cofinalChartRestrictedHom B S hS ψ l P τ G).hom.app Vcop) :=
    fun Vcop => isIso_cofinalChartSections B S hS ψ l P τ Vcop.unop G
  rw [← ObjectProperty.isIso_hom_iff]
  exact NatIso.isIso_of_isIso_app _

/-- **The chartwise comparison, as an isomorphism of the restrictions of the two inverse-image
functors to the cofinal subcategory.** -/
noncomputable def cofinalChartRestrictedIso :
    ψ.toToposHom.inverseImage ⋙
        (cofinalChartInclusion B S hS P).sheafPushforwardContinuous (Type u)
          (cofinalChartTopology B S hS P) (SmallEtale.topology B S hS X.1) ≅
      (smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage ⋙
        (cofinalChartInclusion B S hS P).sheafPushforwardContinuous (Type u)
          (cofinalChartTopology B S hS P) (SmallEtale.topology B S hS X.1) :=
  NatIso.ofComponents (fun G => asIso (cofinalChartRestrictedHom B S hS ψ l P τ G))
    (fun {_ _} g => ObjectProperty.hom_ext _ (NatTrans.ext (funext fun Vcop =>
      cofinalChartSections_naturality_sheaf B S hS ψ l P τ Vcop.unop g)))


/-- **The glued comparison of the two inverse images.**  Restriction of sheaves to a dense
subsite is fully faithful, so the chartwise isomorphism of restrictions comes from a unique
isomorphism `ψ⁻¹ ≅ l_small⁻¹` of functors on all of the small étale site of `X`, naturality in
the sheaf included. -/
noncomputable def cofinalChartGlobalComparison :
    ψ.toToposHom.inverseImage ≅
      (smallEtaleRingedToposHom B S hS l).toToposHom.inverseImage :=
  Functor.IsDenseSubsite.natIsoOfRestriction (cofinalChartTopology B S hS P)
    (SmallEtale.topology B S hS X.1) (cofinalChartInclusion B S hS P) (Type u)
    (cofinalChartRestrictedIso B S hS ψ l P τ)

/-- The glued comparison restricts to the chartwise one. -/
theorem map_cofinalChartGlobalComparison_hom_app
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    ((cofinalChartInclusion B S hS P).sheafPushforwardContinuous (Type u)
        (cofinalChartTopology B S hS P) (SmallEtale.topology B S hS X.1)).map
        ((cofinalChartGlobalComparison B S hS ψ l P τ).hom.app G) =
      (cofinalChartRestrictedIso B S hS ψ l P τ).hom.app G :=
  Functor.map_preimage _ _

/-- The glued comparison, read on sections over a chart of the cofinal subcategory, is the
chartwise comparison there. -/
theorem cofinalChartGlobalComparison_hom_app_app (Vc : CofinalChart B S hS P)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    ((cofinalChartGlobalComparison B S hS ψ l P τ).hom.app G).hom.app
        (op ((cofinalChartInclusion B S hS P).obj Vc)) =
      cofinalChartSections B S hS ψ l P τ Vc G :=
  sheaf_hom_app_congr (map_cofinalChartGlobalComparison_hom_app B S hS ψ l P τ G) _

/-- **The glued comparison satisfies the structure-map compatibility.**  Restriction to the
cofinal subcategory is faithful, so the identity may be checked over the `P`-charts, where it is
the chartwise compatibility read on sections. -/
theorem cofinalChartGlobalComparison_compat :
    (cofinalChartGlobalComparison B S hS ψ l P τ).hom.app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
            (smallEtaleRingedTopos B S hS Y).O) ≫
        (smallEtaleRingedTopos B S hS X).forgetRing.map
          (smallEtaleRingedToposHom B S hS l).fSharpInverseImage =
      (smallEtaleRingedTopos B S hS X).forgetRing.map ψ.fSharpInverseImage := by
  refine ((cofinalChartInclusion B S hS P).sheafPushforwardContinuous (Type u)
    (cofinalChartTopology B S hS P) (SmallEtale.topology B S hS X.1)).map_injective
    (ObjectProperty.hom_ext _ (NatTrans.ext (funext fun Vcop => ?_)))
  refine Eq.trans (congrArg
    (fun z => z ≫ ((smallEtaleRingedTopos B S hS X).forgetRing.map
        (smallEtaleRingedToposHom B S hS l).fSharpInverseImage).hom.app
          (op ((cofinalChartInclusion B S hS P).obj Vcop.unop)))
    (cofinalChartGlobalComparison_hom_app_app B S hS ψ l P τ Vcop.unop
      ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
        (smallEtaleRingedTopos B S hS Y).O))) ?_
  exact sheaf_hom_app_congr
    (chartInverseImageComparison_compat B S hS ψ l Vcop.unop.obj.obj.hom
      (isEtale_cofinalChart_hom B S hS P Vcop.unop) (τ Vcop.unop)) _

include P τ hcd in
/-- **`ψ` is induced by `l`**, given a chartwise 2-isomorphism over every object of the cofinal
subcategory. -/
theorem inducesSmallEtaleRingedToposHom_of_cofinalChartTwoIso :
    InducesSmallEtaleRingedToposHom B S hS l ψ :=
  ⟨RingedToposHom.TwoIso.ofInverseImageIso
    (p := smallEtaleRingedToposHom B S hS l) (q := ψ)
    (cofinalChartGlobalComparison B S hS ψ l P τ)
    (cofinalChartGlobalComparison_compat B S hS ψ l P τ)⟩

end Glue

/-- **Gluing chartwise 2-isomorphisms of small étale ringed topoi over a cofinal family of
charts.**  Let `ψ` be a morphism of the small étale ringed topoi of two algebraic spaces `X` and
`Y` over `S`, let `l : X ⟶ Y`, and let `P` be a cofinal class of affine étale charts of `X`.  If
over every affine `P`-chart `b : h_T ⟶ X` the restriction of `ψ` along `b` is induced by
`b ≫ l`, then `ψ` is induced by `l`.

This is step 6 of the proof of [Stacks Project, Tag 04KL], the descent of the 2-isomorphisms.
No compatibility of the chartwise 2-isomorphisms is assumed: over a chart the 2-isomorphism is
unique by the rigidity of [Stacks Project, Tag 04KK]. -/
theorem inducesSmallEtaleRingedToposHom_of_cofinal
    (P : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X.1) → Prop)
    (hP : IsCofinalChartFamily B S hS P)
    (ht : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
      ∀ b : yoneda.obj T ⟶ X.1, IsEtale B S hS b → P T b →
        InducesSmallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l)
          (smallEtaleComp B S hS ψ
            (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    InducesSmallEtaleRingedToposHom B S hS l ψ := by
  let := isCoverDense_cofinalChartInclusion B S hS P hP
  exact inducesSmallEtaleRingedToposHom_of_cofinalChartTwoIso B S hS ψ l P
    (fun Vc => (ht Vc.obj.obj.left Vc.property.1 Vc.obj.obj.hom
      (isEtale_cofinalChart_hom B S hS P Vc) Vc.property.2).some)

end AlgebraicGeometry.Space

end
