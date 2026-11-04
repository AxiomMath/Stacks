module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Permanence properties of local finite type for algebraic spaces

The four properties of local finite type of a morphism of algebraic spaces that are used to
compare it with other classes of morphisms and with its factors: it is implied by local finite
presentation and hence by smoothness, it is stable under composition and under base change, and
it is inherited by the first factor of a composite that has it.

All four are instances of the general every-étale-chart machinery of Stacks 03MJ, once local
finite type is known to be étale local on the source and target
(`AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget`, Stacks 04R3): the
implications are monotonicity of the chart condition in the tested property of scheme morphisms,
composition is Stacks 0AML, and base change is Stacks 0AMM. Cancellation is the only one with
content beyond instantiation, and even there the content is at the level of schemes: a surjective
étale chart square of the composite is assembled by lifting an atlas of the final target twice,
through `AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift` of Stacks 02X1, and
the scheme morphism it produces is cancelled by Stacks 01T8.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isSmooth`: **Stacks 04AJ**.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation` and
  `AlgebraicGeometry.Space.isFiniteType_of_isFinitePresentation`: **Stacks 0464**.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isSmooth`: **Stacks 06MH**.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_comp`: **Stacks 03XG**, the case of being
  locally of finite type.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_isStableUnderBaseChange`: **Stacks 03XH**, the
  case of being locally of finite type.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp`: **Stacks 0462**.

## Implementation notes

The finite-type halves of Stacks 03XG and 03XH — that a composition, respectively a base change,
of *finite type* morphisms is of finite type — are not stated: they need the corresponding
statements for quasi-compactness, Stacks 03HG and its base-change companion, which this branch
does not carry. The tags therefore name the part proved.

Monotonicity of the chart condition is stated with an explicit implication between properties of
scheme morphisms rather than with `≤` on `CategoryTheory.MorphismProperty`, so that the three
implications below can discharge it by instance synthesis on a bare morphism.

The cancellation argument takes the target chart of the conclusion from the *second* lift rather
than from an atlas of the intermediate space: the chart of the intermediate space has to be one
that already sits in a chart square of the second morphism, and the lift of Stacks 02X1 produces
charts of the source from charts of the target, not the other way round. This is why the atlas is
taken on the final target and lifted twice.

## References

* [Stacks Project, Tag 0462](https://stacks.math.columbia.edu/tag/0462)
* [Stacks Project, Tag 0464](https://stacks.math.columbia.edu/tag/0464)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 06MH](https://stacks.math.columbia.edu/tag/06MH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The every-étale-chart condition is monotone in the tested property of scheme morphisms. -/
theorem holdsOnEveryEtaleChart_mono {P P' : MorphismProperty Scheme.{u}}
    (hPP' : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), P g → P' g)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P' f :=
  fun U V a b h ha hb hab => hPP' _ (hf U V a b h ha hb hab)

/-- **Stacks 04AJ.** A smooth morphism of algebraic spaces over `S` is locally of finite
presentation. -/
@[stacks 04AJ]
theorem isLocallyOfFinitePresentation_of_isSmooth
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsSmooth B S hS f) :
    IsLocallyOfFinitePresentation B S hS f :=
  holdsOnEveryEtaleChart_mono B S hS
    (fun g (_ : AlgebraicGeometry.Smooth g) => by infer_instance)
    hf

/-- **Stacks 0464**, first assertion. A morphism of algebraic spaces over `S` which is locally of
finite presentation is locally of finite type. -/
@[stacks 0464]
theorem isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFiniteType B S hS f :=
  holdsOnEveryEtaleChart_mono B S hS
    (fun g (_ : AlgebraicGeometry.LocallyOfFinitePresentation g) => by infer_instance)
    hf

/-- **Stacks 0464**, second assertion. A morphism of algebraic spaces over `S` of finite
presentation is of finite type. -/
@[stacks 0464]
theorem isFiniteType_of_isFinitePresentation
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsFinitePresentation B S hS f) :
    IsFiniteType B S hS f :=
  ⟨isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1, hf.2.1⟩

/-- **Stacks 06MH.** A smooth morphism of algebraic spaces over `S` is locally of finite
type. -/
@[stacks 06MH]
theorem isLocallyOfFiniteType_of_isSmooth
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsSmooth B S hS f) :
    IsLocallyOfFiniteType B S hS f :=
  isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (isLocallyOfFinitePresentation_of_isSmooth B S hS hf)

/-- **Stacks 03XG**, the case of being locally of finite type: the composite of two morphisms of
algebraic spaces over `S` which are locally of finite type is locally of finite type.

Being locally of finite type is étale local on the source and target (Stacks 04R3) and stable
under composition (Stacks 01T3), so this is an instance of Stacks 0AML. -/
@[stacks 03XG "locally of finite type"]
theorem isLocallyOfFiniteType_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g) :
    IsLocallyOfFiniteType B S hS (f ≫ g) :=
  holdsOnEveryEtaleChart_comp B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget hF hG hH f g hf hg

/-- **Stacks 03XH**, the case of being locally of finite type: being locally of finite type is
stable under base change.

Being locally of finite type is étale local on the source and target (Stacks 04R3) and stable
under base change (Stacks 01T4), so this is an instance of Stacks 0AMM. -/
@[stacks 03XH "locally of finite type"]
theorem isLocallyOfFiniteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyOfFiniteType B S hS f.hom) :=
  holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget

/-- A property of morphisms of schemes which is étale local on the source and target and is
inherited by the first factor of a composite is inherited by the first factor of a composite of
morphisms of algebraic spaces over `S`.

A surjective étale atlas of the final target is lifted along the second morphism, and the
surjective étale chart of the intermediate space so obtained is lifted again along the first
morphism. The resulting two morphisms of the site compose to the morphism of a chart square of
the composite, so the tested property holds of that composite of scheme morphisms, and
cancelling it leaves a surjective étale chart square of the first morphism. -/
theorem holdsOnEveryEtaleChart_of_comp
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hcancel : ∀ {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z), P (u ≫ v) → P u)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hfg : HoldsOnEveryEtaleChart B S hS P (f ≫ g)) :
    HoldsOnEveryEtaleChart B S hS P f := by
  obtain ⟨W, c, hcSurj, hcEtale⟩ := hH.exists_atlas
  obtain ⟨V, b, k, hbk, hbSurj, hbEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hG hH g W c hcSurj hcEtale
  obtain ⟨U, a, h, hah, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V b hbSurj hbEtale
  have hsq : yoneda.map (h ≫ k) ≫ c = a ≫ f ≫ g := by
    rw [Functor.map_comp, Category.assoc, ← hbk, ← Category.assoc, ← hah, Category.assoc]
  have hcomp : P ((BigFppfOver.toScheme B S hS).map (h ≫ k)) :=
    hfg U W a c (h ≫ k) haEtale hcEtale hsq
  have hPh : P ((BigFppfOver.toScheme B S hS).map h) :=
    hcancel _ ((BigFppfOver.toScheme B S hS).map k)
      (by simpa only [Functor.map_comp] using hcomp)
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hF hG f).mpr
    ⟨U, V, a, b, h, haEtale, hbEtale, haSurj, hah.symm, hPh⟩

/-- **Stacks 0462.** If a composite of morphisms of algebraic spaces over `S` is locally of
finite type, then so is its first factor.

This is also the locally-of-finite-type clause of part (1) of **Stacks 0AGC**, whose other
clauses are in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Immersions.lean`. -/
@[stacks 0462, stacks 0AGC "part (1): locally of finite type",
  ega "I 6.6.6" "(v)", ega "IV 1.3.4" "(v)"]
theorem isLocallyOfFiniteType_of_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hfg : IsLocallyOfFiniteType B S hS (f ≫ g)) :
    IsLocallyOfFiniteType B S hS f :=
  holdsOnEveryEtaleChart_of_comp B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (fun _ _ hc => LocallyOfFiniteType.of_comp hc) hF hG hH f g hfg

end AlgebraicGeometry.Space

end
