module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRetarget
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Being separated over the base is stable under change of base (Stacks 050G)

Stacks 050G asserts three things of the change of base of an algebraic stack along a morphism
`g : S ⟶ S'` of the big fppf site: that being quasi-DM, quasi-separated and separated over the
base are each preserved. This file proves all three.

The route is the source's own one-line proof, *"follows immediately from Lemma 050F"*, made
precise. Under the canonical two-fibre-product characterization of Stacks 04X7 the change of
base of `𝒳'` is the 2-fibre product of `𝒳'` and the stack represented by `S/S'` over the stack
represented by `S'/S'`, with the structure morphism of `𝒳'` as one leg; so the structure morphism
of the change of base, read over `S'`, is a base change of the structure morphism of `𝒳'`, and
Stacks 050F applies to it. Three steps are then needed to turn that into the assertion over `S`:

* the witness's leg really is the structure morphism of `𝒳'`
  (`AlgebraicGeometry.Stack.AlgebraicStacks.witness_f_eq_structure`);
* Stacks 050F has to be available at the witness's square rather than at the canonical one,
  which is `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_baseChange_of_isTwoFibreProduct`;
* the condition is a condition on the relative *diagonal*, so the self-product of the relative
  diagonal has to be identified across the change of base, which is
  `CategoryTheory.TwoFibreProductOver.representedFibre_structure_changeBase`, and the resulting
  morphism of algebraic spaces has to be recognised as the same one read over the two bases.

That last recognition is the only step that is not common to the three keys, because it is the
only one that mentions the condition being transferred. For the quasi-DM key it is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`; for the
quasi-separated key it is
`AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor_of` together with
`AlgebraicGeometry.Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_of`; and for the separated
key it is `AlgebraicGeometry.Space.isProper_spacesOverSmallerBaseFunctor_of`, which assembles the
four clauses of Stacks 03ZM.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMOver_changeOfBase`: **Stacks 050G**, the
  quasi-DM key.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparatedOver_changeOfBase`: **Stacks 050G**,
  the quasi-separated key.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparatedOver_changeOfBase`: **Stacks 050G**, the
  separated key.

## Implementation notes

The last step is where the three keys cost different amounts, and the difference is visible in
one line of each definition. `AlgebraicGeometry.Space.IsLocallyQuasiFinite` — the conclusion of
the quasi-DM condition — *is* `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` at
`LocallyOfFiniteType ⊓ LocallyQuasiFinite`, and the independence of that condition from the base
is already proved for an arbitrary morphism property, so the quasi-DM key closes in one term. The
conclusions of the other two conditions are not of that shape:
`AlgebraicGeometry.Space.IsQuasiCompact` quantifies over quasi-compact algebraic spaces mapping to
the target, and `AlgebraicGeometry.Space.IsProper` is a conjunction of four clauses of which the
first is a closed-immersion condition on a diagonal and the last is a condition on the topology of
the point set of every base change. Quasi-compactness and quasi-separatedness are read over two
bases in `StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactSmallerBase.lean`, which is Stacks
03HE
and Stacks 03HL part (3); the separated and universally closed clauses of Stacks 03ZM are read
over two bases in `StacksFrontier/AlgebraicGeometry/Spaces/ProperSmallerBase.lean`, the universally
closed one resting on the comparison of point sets and point topologies of
`StacksFrontier/AlgebraicGeometry/Spaces/PointsSmallerBase.lean`.

`AlgebraicGeometry.Stack.AlgebraicStacks.witness_f_eq_structure`,
`AlgebraicGeometry.Stack.AlgebraicStacks.property_of_heq` and
`AlgebraicGeometry.Stack.AlgebraicStacks.heq_mkHom` are the auxiliary lemmas shared by the proofs
of all three keys of Stacks 050G.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 04X7](https://stacks.math.columbia.edu/tag/04X7)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050G](https://stacks.math.columbia.edu/tag/050G)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- The 1-morphism to the terminal stack carried by the two-fibre-product witness of
Stacks 04X7 *is* the structure morphism of `𝒳'`. The witness pins its underlying functor to the
structure functor read through the iterated-slice equivalence, which is exactly what the
structure morphism is, and a based 1-morphism is determined by its underlying functor. -/
theorem witness_f_eq_structure (𝒳' : AlgebraicStacks.{u, w} B S' hS')
    (W : Stack.ChangeOfBaseTwoFibreProductWitness B S S' hS hS' g 𝒳') :
    W.f = Stack.structureMorphism B S' hS' 𝒳' := by
  apply Bicategory.InducedBicategory.hom_ext
  apply Bicategory.InducedBicategory.hom_ext
  apply BasedCategory.BasedFunctor.ext'
  rw [W.f_underlying]
  rfl

/-- A 1-morphism of algebraic stacks is heterogeneously equal to the one induced by a
1-morphism of the underlying categories fibred in groupoids, once the sources are known equal.
This is what moves a statement about the witness's second leg to a statement about the structural
1-morphism of the correspondence of Stacks 04X5, which lives one level down. -/
theorem heq_mkHom {X X' 𝒴 : AlgebraicStacks.{u, w} B S' hS'} (hX : X = X')
    {f : X ⟶ 𝒴} {h : X'.val ⟶ 𝒴.val} (e : HEq f.hom h) :
    HEq f (Bicategory.InducedBicategory.mkHom h) := by
  subst hX; cases eq_of_heq e; rfl

/-- Transport of a property of morphisms along an equality of sources and a heterogeneous
equality of morphisms. -/
theorem property_of_heq {C : Type*} [CategoryStruct C] (P : ∀ {X Y : C}, (X ⟶ Y) → Prop)
    {X X' Y : C} (hX : X = X') {f : X ⟶ Y} {h : X' ⟶ Y} (e : HEq f h) (hf : P f) : P h := by
  subst X'; cases eq_of_heq e; exact hf

/-- A property of the second leg of the witness of Stacks 04X7 passes to the structural
1-morphism of the correspondence of Stacks 04X5, viewed as a 1-morphism of algebraic stacks. -/
private theorem property_mkHom_changeBaseStructureHom
    (P : ∀ {A C : AlgebraicStacks.{u, w} B S' hS'}, (A ⟶ C) → Prop)
    (𝒳' : AlgebraicStacks.{u, w} B S' hS')
    (W : Stack.ChangeOfBaseTwoFibreProductWitness B S S' hS hS' g 𝒳') (h : P W.square.snd) :
    P (Bicategory.InducedBicategory.mkHom
      (X := changeBaseAlgebraicStack B S S' hS hS' g (Stack.changeOfBase B S S' hS hS' g 𝒳'))
      (Y := Stack.schemeStack B S' hS' (Over.mk g))
      (Stack.changeBaseStructureHom B S S' hS hS' g (Stack.changeOfBase B S S' hS hS' g 𝒳'))) :=
  property_of_heq P W.pt_eq (heq_mkHom B S' hS' (𝒴 := Stack.schemeStack B S' hS' (Over.mk g))
    W.pt_eq W.snd_eq) h

/-- **Stacks 050G, the quasi-DM key.** Being quasi-DM over the base is stable under change of
base scheme. -/
@[stacks 050G "quasi-DM over the base"]
theorem isQuasiDMOver_changeOfBase (𝒳' : AlgebraicStacks.{u, w} B S' hS')
    (h𝒳' : Stack.IsQuasiDMOver B S' hS' 𝒳') :
    Stack.IsQuasiDMOver B S hS (Stack.changeOfBase B S S' hS hS' g 𝒳') := by
  obtain ⟨W⟩ := Stack.changeOfBase_twoFibreProductWitness B S S' hS hS' g 𝒳'
  have hview := property_mkHom_changeBaseStructureHom B S S' hS hS' g
    (fun {A C} f => IsQuasiDM B S' hS' (𝒳 := A) (𝒴 := C) f) 𝒳' W
    (isQuasiDM_baseChange_of_isTwoFibreProduct B S' hS' W.f W.k W.square W.isTwoFibreProduct
      (witness_f_eq_structure B S S' hS hS' g 𝒳' W ▸ h𝒳'))
  intro U y hy F hF he
  obtain ⟨e⟩ := he
  obtain ⟨y', hy', he'⟩ := TwoFibreProductOver.representedFibre_structure_changeBase
    (Stack.changeOfBase B S S' hS hS' g 𝒳').val.val.p g U
    (Stack.structureMorphism B S hS (Stack.changeOfBase B S S' hS hS' g 𝒳')).hom.hom.w
    (Stack.changeBaseStructureHom B S S' hS hS' g
      (Stack.changeOfBase B S S' hS hS' g 𝒳')).hom.w
    y hy (presheafOfCategories (F ⋙ typeToCat)).p e
  have hprop := hview (Over.mk (U.hom ≫ g)) y' hy' F hF he'
  exact (Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
    U.hom S' hS' g (U.hom ≫ g) rfl _ F hF).mp hprop

/-- **Stacks 050G, the quasi-separated key.** Being quasi-separated over the base is stable under
change of base scheme. -/
@[stacks 050G "quasi-separated over the base"]
theorem isQuasiSeparatedOver_changeOfBase (𝒳' : AlgebraicStacks.{u, w} B S' hS')
    (h𝒳' : Stack.IsQuasiSeparatedOver B S' hS' 𝒳') :
    Stack.IsQuasiSeparatedOver B S hS (Stack.changeOfBase B S S' hS hS' g 𝒳') := by
  obtain ⟨W⟩ := Stack.changeOfBase_twoFibreProductWitness B S S' hS hS' g 𝒳'
  have hview := property_mkHom_changeBaseStructureHom B S S' hS hS' g
    (fun {A C} f => IsQuasiSeparated B S' hS' (𝒳 := A) (𝒴 := C) f) 𝒳' W
    (isQuasiSeparated_baseChange_of_isTwoFibreProduct B S' hS' W.f W.k W.square W.isTwoFibreProduct
      (witness_f_eq_structure B S S' hS hS' g 𝒳' W ▸ h𝒳'))
  refine (isQuasiSeparated_iff_forall B S hS _).2 ?_
  intro U y hy F hF he
  obtain ⟨e⟩ := he
  obtain ⟨y', hy', he'⟩ := TwoFibreProductOver.representedFibre_structure_changeBase
    (Stack.changeOfBase B S S' hS hS' g 𝒳').val.val.p g U
    (Stack.structureMorphism B S hS (Stack.changeOfBase B S S' hS hS' g 𝒳')).hom.hom.w
    (Stack.changeBaseStructureHom B S S' hS hS' g
      (Stack.changeOfBase B S S' hS hS' g 𝒳')).hom.w
    y hy (presheafOfCategories (F ⋙ typeToCat)).p e
  have hprop := (isQuasiSeparated_iff_forall B S' hS' _).1 hview
    (Over.mk (U.hom ≫ g)) y' hy' F hF he'
  exact ⟨Space.isQuasiCompact_spacesOverSmallerBaseFunctor_of B U.left.1 S U.left.2 hS
      U.hom S' hS' g (U.hom ≫ g) rfl F hF hprop.1,
    Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_of B U.left.1 S U.left.2 hS
      U.hom S' hS' g (U.hom ≫ g) rfl F hF hprop.2⟩

/-- **Stacks 050G, the separated key.** Being separated over the base is stable under change of
base scheme. -/
@[stacks 050G "separated over the base"]
theorem isSeparatedOver_changeOfBase (𝒳' : AlgebraicStacks.{u, w} B S' hS')
    (h𝒳' : Stack.IsSeparatedOver B S' hS' 𝒳') :
    Stack.IsSeparatedOver B S hS (Stack.changeOfBase B S S' hS hS' g 𝒳') := by
  obtain ⟨W⟩ := Stack.changeOfBase_twoFibreProductWitness B S S' hS hS' g 𝒳'
  have hview := property_mkHom_changeBaseStructureHom B S S' hS hS' g
    (fun {A C} f => IsSeparated B S' hS' (𝒳 := A) (𝒴 := C) f) 𝒳' W
    (isSeparated_baseChange_of_isTwoFibreProduct B S' hS' W.f W.k W.square W.isTwoFibreProduct
      (witness_f_eq_structure B S S' hS hS' g 𝒳' W ▸ h𝒳'))
  intro U y hy F hF he
  obtain ⟨e⟩ := he
  obtain ⟨y', hy', he'⟩ := TwoFibreProductOver.representedFibre_structure_changeBase
    (Stack.changeOfBase B S S' hS hS' g 𝒳').val.val.p g U
    (Stack.structureMorphism B S hS (Stack.changeOfBase B S S' hS hS' g 𝒳')).hom.hom.w
    (Stack.changeBaseStructureHom B S S' hS hS' g
      (Stack.changeOfBase B S S' hS hS' g 𝒳')).hom.w
    y hy (presheafOfCategories (F ⋙ typeToCat)).p e
  have hprop := hview (Over.mk (U.hom ≫ g)) y' hy' F hF he'
  exact Space.isProper_spacesOverSmallerBaseFunctor_of B U.left.1 S U.left.2 hS
    U.hom S' hS' g (U.hom ≫ g) rfl F hF hprop

end AlgebraicGeometry.Stack.AlgebraicStacks

end

/-!
# A condition on the relative diagonal and change of base (Stacks 04X5, 04XB)

Let `g : S ⟶ S'` be a morphism of a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S`. Construction A of **Stacks 04X5**
views `f` as a 1-morphism `changeBase f` over the big fppf site of `S'`
(`AlgebraicGeometry.Stack.changeBaseHom`), and this part of the file compares a condition of
Properties of Stacks, Section 04XB, on the relative diagonal of `f` with the same condition on
the relative diagonal of `changeBase f`.

The conditions it compares are those at a property of morphisms of *schemes* read on étale
charts — `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of **Stacks 03MJ**. That is the
generality in which the comparison is available, because the one thing it needs of the property
is that the étale-chart condition for the structural morphism of a lower-shriek extension does
not depend on the base
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`). Two of the
four separation axioms of **Stacks 04YW** are of this shape: DM is the condition at
unramifiedness (**Stacks 03ZH**, part (1)) and quasi-DM is the condition at local
quasi-finiteness (**Stacks 03XJ**, part (1)), both of which
`StacksFrontier.AlgebraicGeometry.Spaces.Unramified` and
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteType` define as étale-chart conditions.

## Main definitions

* `AlgebraicGeometry.Stack.HasEtaleChartProperty`: the condition of Stacks 04XB at a property of
  morphisms of schemes read on étale charts. It is the quantifier of
  `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**) written out longhand, so that
  neither of that abbreviation's instance hypotheses on the property has to be in scope — they
  are not available at unramifiedness, which is the reason
  `AlgebraicGeometry.Stack.IsDM` is itself stated longhand.
* `AlgebraicGeometry.Stack.relocalizeBaseFunctor`: the comparison 1-morphism from the 2-fibre
  product `𝒳 ×_𝒴 𝒳` viewed over `S'` to the 2-fibre product of the views of `𝒳` and `𝒴` over
  `S'`, that is `CategoryTheory.TwoFibreProductOver.relocalizeBase` read over the site.

## Main results

* `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_changeBaseHom_iff`: a 1-morphism satisfies the
  condition of Stacks 04XB at an étale-chart property exactly when the 1-morphism produced by
  Construction A out of it does.
* `AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor_changeBase`: the relative diagonal of the
  view of `f` over `S'` is the view of the relative diagonal of `f`, followed by the comparison
  1-morphism. This holds on the nose.
* `AlgebraicGeometry.Stack.hasEtaleChartProperty_relativeDiagonal_of_changeBase`: the condition
  of Stacks 04XB at an étale-chart property passes from the relative diagonal of the view of `f`
  over `S'` to the relative diagonal of `f`.

## Implementation notes

**What this adds, and what it does not.** The implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase` record that the two *absolute* diagonals are
not comparable along Construction A: the self-product of `changeBase 𝒳` over the big fppf site of
`S'` is taken over the stack represented by `S'`, and so has the strictly larger object set of
pairs lying over a common `S'`-scheme by two different morphisms to `S`. That obstruction does
*not* apply to the *relative* diagonal of a 1-morphism `f : 𝒳 ⟶ 𝒴`, because the self-product of
`changeBase 𝒳` is then taken over `changeBase 𝒴`, whose comparison isomorphism is still vertical
over the site of `S` — and that is exactly the 2-fibre product that
`CategoryTheory.TwoFibreProductOver.relocalizeBaseEquivalence` identifies with `𝒳 ×_𝒴 𝒳`. So the
relative statement is available where the absolute one is not, and assembling it is the whole
content of this part of the file.

**The two steps.** `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_changeBaseHom_iff` is the
transfer along Construction A for a 1-morphism's own Stacks 04XB condition; it is the argument of
`AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff` with the property left as
a parameter, which costs nothing because the space-level ingredient
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff` is already
general in it. Applying it to the relative diagonal of `f` gives the condition for
`changeBase (Δ_f)`, whose target is `𝒳 ×_𝒴 𝒳` viewed over `S'`; the second step moves from there
to `Δ_{changeBase f}`, whose target is the 2-fibre product formed over `S'`, along
`AlgebraicGeometry.Stack.relocalizeBaseFunctor`. That move is **Stacks 0457** for the Stacks 04XB
condition, `AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, and its 2-commutativity
isomorphism is the identity by
`AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor_changeBase`.

**Only one direction of the second step is proved.**
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` consumes an equivalence
`𝒴' ⥤ᵇ 𝒴` of the targets, and in the direction proved here that equivalence is
`AlgebraicGeometry.Stack.relocalizeBaseFunctor`, which is strictly over the site on the nose. The
opposite direction needs `CategoryTheory.TwoFibreProductOver.unrelocalizeBase` read over the
site, and *that* is strictly over the site only up to the identification recorded in the `hx`
field of an object of the relocalized 2-fibre product, so it is not the same one-line
construction. The direction proved is the one the clauses of **Stacks 050N** consume.

**No tag.** Neither statement here is a numbered result: Stacks 04X5 names only the four clauses
of Stacks 026O, of which the presentation clause is
`AlgebraicGeometry.Stack.hasRelativeProperty_surjective_changeBaseHom_iff` and
`AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff`, and the transfer of a
Stacks 04XB condition on a relative diagonal is a step the source performs inside the proof of
Stacks 050N rather than a lemma of its own.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

section ChartProperty

variable (B' : BigFppfSite.{u}) (T : Scheme.{u}) (hT : B'.Contains T)

/-- **The condition of Stacks 04XB at an étale-chart property.** A 1-morphism of categories fibred
in groupoids over the big fppf site of `T` which is representable by algebraic spaces *has the
étale-chart property `P`* when, for every algebraic space representing its base change along a
scheme-valued point of the target, the scheme morphism in every commuting square of étale scheme
charts of the structural morphism has `P`.

This is the quantifier of `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**) at
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of **Stacks 03MJ**, written out longhand. The
longhand form is the same proposition with no hypothesis on `P` at all, which is what is wanted:
`HasRelativeProperty` asks for stability under base change and locality at the target for the
fppf precoverage, and neither is proved at unramifiedness. -/
abbrev HasEtaleChartProperty (P : MorphismProperty Scheme.{u})
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B' T hT)} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B' T hT)
    (y : BigFppfOver B' U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B' U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B' U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.HoldsOnEveryEtaleChart B' T hT P
        (algebraicSpaceMap B' T hT U
          ((spacesOverSmallerBaseFunctor B' U.left.1 T U.left.2 hT U.hom).obj ⟨F, hF⟩)).hom

end ChartProperty

/-- **A condition of Stacks 04XB at an étale-chart property is unchanged by Construction A.** A
1-morphism of categories fibred in groupoids over the big fppf site of `S` has the étale-chart
property `P` in the relative sense of Stacks 04XB exactly when the 1-morphism over the big fppf
site of `S'` produced by Construction A has it.

This is the argument of `AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff`
with the property left as a parameter. The quantifications over scheme-valued points match up by
`AlgebraicGeometry.Stack.comp_changeBase_p_eq_map` and
`AlgebraicGeometry.Stack.exists_comp_p_eq_map_of_changeBase`, and the ones over representing
algebraic spaces by `CategoryTheory.TwoFibreProductOver.fstEquivalenceOver_trans` and its
converse, so the morphism being tested is the same object on both sides, living over the same
scheme over `S`; what is left is that its étale-chart condition does not depend on whether that
scheme is read over `S` or over `S'`, which is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`. -/
theorem holdsOnEveryEtaleChart_changeBaseHom_iff (P : MorphismProperty Scheme.{u})
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    HasEtaleChartProperty B S' hS' P (changeBaseHom B S S' hS hS' g f) ↔
      HasEtaleChartProperty B S hS P f := by
  constructor
  · intro hbig U y hy F hF hE
    obtain ⟨E⟩ := hE
    have key := hbig ((Over.map g).obj U) y
      (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴.val U y hy) F hF
      ⟨TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.hom.w E⟩
    exact (Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
      U.hom S' hS' g (U.hom ≫ g) rfl P F hF).1 key
  · intro hsmall U' y hy' F hF hE'
    obtain ⟨E'⟩ := hE'
    obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴.val U' y hy'
    rw [← hg, Over.mapComp_eq] at E'
    have key := hsmall (Over.mk h₀) y hy F hF
      ⟨TwoFibreProductOver.fstEquivalenceOver_trans g hy f.hom.w E'⟩
    exact (Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff B U'.left.1 S U'.left.2
      hS h₀ S' hS' g U'.hom hg P F hF).2 key

/-- **The relative diagonal commutes with Construction A.** The relative diagonal of the
1-morphism over the big fppf site of `S'` produced by Construction A out of `f` is the relative
diagonal of `f`, followed by the comparison functor identifying the 2-fibre product `𝒳 ×_𝒴 𝒳`
viewed over `S'` with the 2-fibre product formed over `S'`.

It holds on the nose: both functors send an object `x` to the triple `(x, x)` over the base object
of `x` composed with `g`, together with the identity identification, and the three remaining
fields of an object of a 2-fibre product are propositions. -/
theorem relativeDiagonalBasedFunctor_changeBase
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳.val ⥤ᵇ 𝒴.val) :
    (relativeDiagonalBasedFunctor B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseFunctor B S S' hS hS' g f)).toFunctor =
      (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f).toFunctor ⋙
        TwoFibreProductOver.relocalizeBase g :=
  rfl

/-- **The 2-fibre product `𝒳 ×_𝒴 𝒳` viewed over `S'` is the 2-fibre product formed over `S'`.**
`CategoryTheory.TwoFibreProductOver.relocalizeBase` read as a 1-morphism of categories over the
big fppf site of `S'`; it is strictly over that site on the nose, because both structure functors
send an object to its base object composed with `g`. -/
def relocalizeBaseFunctor
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) :
    (changeBaseFiberedInGroupoids B S S' hS hS' g
        (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom)).val ⥤ᵇ
      (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseHom B S S' hS hS' g f).hom
        (changeBaseHom B S S' hS hS' g f).hom).val where
  toFunctor := TwoFibreProductOver.relocalizeBase g
  w := rfl

/-- `AlgebraicGeometry.Stack.relocalizeBaseFunctor` is an equivalence: it is the forward functor
of `CategoryTheory.TwoFibreProductOver.relocalizeBaseEquivalence`, whose two hypotheses are that
the two legs of the 2-fibre product are strictly over the site, which here are both the
compatibility of `f`. -/
theorem isEquivalence_relocalizeBaseFunctor
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f).toFunctor :=
  (TwoFibreProductOver.relocalizeBaseEquivalence g f.hom.w f.hom.w).isEquivalence_functor

/-- **A condition of Stacks 04XB at an étale-chart property passes from the relative diagonal of
the view of `f` over `S'` to the relative diagonal of `f`.**

The two steps are `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_changeBaseHom_iff`, which
transfers the condition for `changeBase (Δ_f)` back to `Δ_f`, and **Stacks 0457** for the
condition (`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`) along the equivalence
`AlgebraicGeometry.Stack.relocalizeBaseFunctor` of the two targets, whose 2-commutativity
isomorphism is the identity by
`AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor_changeBase`. -/
theorem hasEtaleChartProperty_relativeDiagonal_of_changeBase (P : MorphismProperty Scheme.{u})
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴)
    (h : HasEtaleChartProperty B S' hS' P
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f))) :
    HasEtaleChartProperty B S hS P (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f) := by
  have _ : Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence
      (𝟭 (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.obj))
  have _ : Functor.IsEquivalence
      (relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f).toFunctor :=
    isEquivalence_relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f
  exact (holdsOnEveryEtaleChart_changeBaseHom_iff B S S' hS hS' g P
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).1
    (relativeProperty_of_equivalences B S' hS'
      (fun _ _ k => Space.HoldsOnEveryEtaleChart B S' hS' P k.hom)
      (changeBaseHom B S S' hS hS' g (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).hom
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)).hom
      (BasedFunctor.id _) (relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f) (Iso.refl _) h)

end AlgebraicGeometry.Stack

end
