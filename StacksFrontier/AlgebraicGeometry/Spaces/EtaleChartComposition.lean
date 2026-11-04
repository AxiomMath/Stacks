module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation

/-!
# Composition of an étale-local property of morphisms of algebraic spaces (Stacks 0AML)

Let `S` be a scheme contained in a big fppf site `B`, and let `P` be a property of morphisms of
schemes which is étale local on the source and target (Stacks 04QZ) and stable under
composition. Then the induced property of morphisms of algebraic spaces over `S` -- `P` holds
on every commuting square of étale charts, which is condition (1) of Stacks 03MJ -- is itself
stable under composition.

The proof is the one Stacks 0AML points to, and it is the composition counterpart of the
base-change argument of Stacks 0AMM. Given `f : F ⟶ G` and `g : G ⟶ H`, choose surjective
étale scheme atlases of `G` and of `H` and lift them through `f` and through `g` respectively
(Stacks 02X1): this gives a surjective étale chart `a` of `F` over a chart `b` of `G`, and a
surjective étale chart `d` of `G` over a chart `c` of `H`. The two charts of `G` need not
agree, so `d` is pulled back along the chart `a ≫ f` of `G` -- `d` is representable, being an
étale chart -- which produces a single chart `A` of `F` sitting over `d`, still surjective and
étale because both properties are stable under base change and composition. The underlying
morphism of schemes of `A` over `d` has `P` by the hypothesis on `f`, that of `d` over `c` has
`P` by the hypothesis on `g`, and `P` is stable under composition; so the composite square,
whose chart of the source is the surjective `A`, carries `P`. Stacks 03MJ then upgrades that
one surjective square to every square.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_comp`: the chart-level form of **Stacks
  0AML**.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_isStableUnderComposition`: **Stacks 0AML**,
  as a `CategoryTheory.MorphismProperty.IsStableUnderComposition` on the category of algebraic
  spaces over `S`.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_comp`: **Stacks 03XQ**, the case of
  being locally of finite presentation.

## Implementation notes

The tag is carried by the `CategoryTheory.MorphismProperty.IsStableUnderComposition` form,
which is literally what Stacks 0AML asserts; `holdsOnEveryEtaleChart_comp` is the same
statement spelled out for presheaves together with the hypothesis that each of the three is an
algebraic space, and is where the work is done.

Only the "locally of finite presentation" half of Stacks 03XQ is proved here. The other half,
for morphisms of finite presentation, additionally needs that quasi-compact morphisms of
algebraic spaces are stable under composition (Stacks 03HG) and that quasi-separated ones are
(Stacks 03KQ). Both of those are now available — `AlgebraicGeometry.Space.isQuasiCompact_comp` in
`StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties` and
`AlgebraicGeometry.Space.isQuasiSeparated_comp` in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms` — so the finite-presentation
half is reachable from the three; it is not proved here.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 0AML](https://stacks.math.columbia.edu/tag/0AML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The chart-level form of **Stacks 0AML**: if a property `P` of morphisms of schemes is étale
local on the source and target and stable under composition, and `P` holds on every commuting
square of étale charts of `f : F ⟶ G` and of `g : G ⟶ H`, then it holds on every commuting
square of étale charts of `f ≫ g`. -/
theorem holdsOnEveryEtaleChart_comp
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderComposition]
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : HoldsOnEveryEtaleChart B S hS P f)
    (hg : HoldsOnEveryEtaleChart B S hS P g) :
    HoldsOnEveryEtaleChart B S hS P (f ≫ g) := by
  let T := BigFppfOver.toScheme B S hS
  let QEtale : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  let QSurjective : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) T
  let R := QSurjective.presheaf
  have : QSurjective.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : QSurjective.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
  have : R.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition QSurjective
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hG.exists_atlas
  obtain ⟨W, c, hcSurj, hcEtale⟩ := hH.exists_atlas
  obtain ⟨U, a, α, hα, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V b hbSurj hbEtale
  obtain ⟨V', d, β, hβ, hdSurj, hdEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hG hH g W c hcSurj hcEtale
  -- the chart `a ≫ f` of `G`, rewritten through the square defining `a`
  let aG : yoneda.obj U ⟶ G := yoneda.map α ≫ b
  -- pull the chart `d` of `G` back along it, to compare the two charts of `G`
  let Z := hdEtale.rep.pullback aG
  let p : Z ⟶ V' := hdEtale.rep.fst' aG
  let q : Z ⟶ U := hdEtale.rep.snd aG
  let A : yoneda.obj Z ⟶ F := yoneda.map q ≫ a
  have hpbk := hdEtale.rep.isPullback' aG
  have hpb := hpbk.w
  have hAf : A ≫ f = yoneda.map q ≫ aG := by simp only [A, aG, ← hα, Category.assoc]
  have hqEtale :=
    hdEtale.property aG (yoneda.map p) q hpbk
  have hqSurj :=
    hdSurj.property aG (yoneda.map p) q hpbk
  have hAEtale : QEtale.presheaf A := etale_comp_of_scheme B S hS q a hqEtale haEtale
  have hASurj : R A :=
    MorphismProperty.comp_mem R _ _
      ((presheaf_yoneda_map_iff B S hS inferInstance q).2 hqSurj) haSurj
  have hPp : P (T.map p) := hf Z V' A d p hAEtale hdEtale (hpb.trans hAf.symm)
  have hPβ : P (T.map β) := hg V' W d c β hdEtale hcEtale hβ.symm
  have hPcomp : P (T.map (p ≫ β)) := by
    simpa only [Functor.map_comp] using
      MorphismProperty.IsStableUnderComposition.comp_mem (T.map p) (T.map β) hPp hPβ
  have hcompat : yoneda.map (p ≫ β) ≫ c = A ≫ (f ≫ g) := by
    rw [Functor.map_comp, Category.assoc, ← hβ, ← Category.assoc, hpb, ← Category.assoc A f g,
      hAf, Category.assoc]
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hF hH (f ≫ g)).mpr
    ⟨Z, W, A, c, p ≫ β, hAEtale, hcEtale, hASurj, hcompat, hPcomp⟩

/-- **Stacks 0AML.** A property of morphisms of schemes which is étale local on the source and
target and stable under composition induces a composition stable property of morphisms of
algebraic spaces over `S`, namely the condition that it hold on every commuting square of
étale charts. -/
@[stacks 0AML]
theorem holdsOnEveryEtaleChart_isStableUnderComposition
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderComposition] :
    MorphismProperty.IsStableUnderComposition
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom) :=
  ⟨fun {X Y Z} f g hf hg => by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      holdsOnEveryEtaleChart_comp B S hS P hP X.property Y.property Z.property f.hom g.hom hf hg⟩

/-- **Stacks 03XQ**, the case of being locally of finite presentation: the composite of two
morphisms of algebraic spaces over `S` which are locally of finite presentation is locally of
finite presentation.

Being locally of finite presentation is étale local on the source and target (Stacks 04R3) and
stable under composition (Stacks 01TR), so this is an instance of Stacks 0AML. -/
@[stacks 03XQ "locally of finite presentation"]
theorem isLocallyOfFinitePresentation_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hg : IsLocallyOfFinitePresentation B S hS g) :
    IsLocallyOfFinitePresentation B S hS (f ≫ g) :=
  holdsOnEveryEtaleChart_comp B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hF hG hH f g hf hg

end AlgebraicGeometry.Space

end
