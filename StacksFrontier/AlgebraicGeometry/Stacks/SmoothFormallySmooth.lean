module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothDottedArrows
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackLift
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.DottedArrows.Defs
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The infinitesimal lifting criterion for smoothness (Stacks 0DP0)

Stacks 0DP0 says that a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is smooth if and
only if it is locally of finite presentation and formally smooth. Formal smoothness of a
1-morphism of algebraic stacks is formal smoothness on objects (Stacks 0DNW, 06D0), so the
statement is
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isSmooth_iff_isLocallyOfFinitePresentation_and_isFormallySmoothOnObjects`.

## Main results

* `CategoryTheory.DottedArrow.ofTwoFibreProduct`: in any bicategory, a dotted arrow for the
  base change of a 2-commutative square along its bottom arrow is a dotted arrow for the square.
* `AlgebraicGeometry.Stack.exists_schemeChart_isSmooth_isSurjectiveOnObjects`: the chart of an
  algebraic stack by an object of the site is representable by algebraic spaces, smooth and
  surjective on objects.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFormallySmoothOnObjects_of_isSmooth`: a smooth
  1-morphism of algebraic stacks is formally smooth on objects.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isSmooth_of_isLocallyOfFinitePresentation_of_isFormallySmoothOnObjects`: a 1-morphism of
  algebraic stacks which is locally of finite presentation and formally smooth on objects is
  smooth.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isSmooth_iff_isLocallyOfFinitePresentation_and_isFormallySmoothOnObjects`: **Stacks 0DP0**.

## Implementation notes

*(1) `⇒` (2)* follows the source. Local finite presentation is Stacks 0DNP. For formal
smoothness, Stacks 0DNY reduces to finding a dotted arrow in every infinitesimal lifting diagram
`(x : T ⟶ 𝒳, j : T ⟶ T', y : T' ⟶ 𝒴, γ)` of Stacks 0DNX. Let `P = T' ×_{y, 𝒴, f} 𝒳` be the
canonical 2-fibre product, an algebraic stack by Stacks 04T2, whose projection `P ⟶ T'` is smooth
by Stacks 075W. The square `(j, x, γ)` factors through `P` by the universal property, and Stacks
0DNZ gives a dotted arrow for the left square; composing it with the projection `P ⟶ 𝒳` is a
dotted arrow for the original square, which is the pasting of
`CategoryTheory.DottedArrow.ofTwoFibreProduct`.

*(2) `⇒` (1)* also follows the source. Choose the chart `a : 𝒰 ⟶ 𝒳` by an object of the site
supplied by the algebraicity of `𝒳` (Stacks 026O): it is representable by algebraic spaces,
smooth and surjective on objects. Being smooth and representable it is formally smooth on
objects (Stacks 04AM read through Stacks 06FM and 06D3, which is
`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_isSmooth_unconditional`), so the composite
`b = a ≫ f` is formally smooth on objects by Stacks 06D2, and it is locally of finite
presentation because both factors are (Stacks 06Q3). Both `a` and `b` are representable by
algebraic spaces, `𝒳` and `𝒴` having representable diagonals, so Stacks 06D3 turns formal
smoothness on objects of `b` into the relative property of Stacks 03YK at formal smoothness,
and the universal smooth-diagram test for local finite presentation becomes the existential one
by Stacks 06FM and thence the relative property. On each base change to an algebraic space over
an object of the site the two relative properties give local finite presentation and formal
smoothness of a morphism of algebraic spaces, which is smoothness by Stacks 04AM; so `b` is
relatively smooth, hence passes the existential smooth-diagram test (Stacks 045F). Composing the
smooth surjective diagram of `b` with the atlas produces a smooth diagram for `f` itself, whose
top horizontal morphism is the one of `b`.

The smooth-diagram tests are `AlgebraicGeometry.Stack.HasPropertyOnSomeSmoothDiagram` and
`.HasPropertyOnEverySmoothDiagram`, which is what
`AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth` (Stacks 075U) and
`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation` (Stacks 06Q2) unfold
to; the `change`s below are those unfoldings, needed because the two tests are stated for a
bare `MorphismProperty` argument which instance search does not see through.

## References

* [Stacks Project, Tag 0DP0](https://stacks.math.columbia.edu/tag/0DP0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory.DottedArrow

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {S T X Y : B} {x : S ⟶ X} {j : S ⟶ T}
  {f : X ⟶ Y} {y : T ⟶ Y} {γ : j ≫ y ≅ x ≫ f}

/-- **A dotted arrow after base change is a dotted arrow.** Let `(x, j, f, y, γ)` be a
2-commutative square, `Q` a 2-commutative square over the cospan `(y, f)` and `F` a morphism to
`Q` from the square itself, read as a 2-commutative square over that cospan. A dotted arrow for
the left square `(F.hom, j, Q.fst, 𝟙)`, whose witness `γ'` is the comparison of `F` at the
first projection, composed with the second projection of `Q`, is a dotted arrow for the square. -/
def ofTwoFibreProduct {Q : TwoCommSq y f}
    (F : TwoCommSq.PreHom (⟨S, j, x, γ⟩ : TwoCommSq y f) Q)
    {γ' : j ≫ 𝟙 T ⟶ F.hom ≫ Q.fst} (D : DottedArrow F.hom j Q.fst (𝟙 T) γ')
    (hγ' : γ' = (ρ_ j).hom ≫ F.isoFst.hom) :
    DottedArrow x j f y γ.hom where
  a := D.a ≫ Q.snd
  α := (α_ j D.a Q.snd).inv ≫ D.α ▷ Q.snd ≫ F.isoSnd.inv
  β := (λ_ y).inv ≫ D.β ▷ y ≫ (α_ D.a Q.fst y).hom ≫ D.a ◁ Q.iso.hom ≫
    (α_ D.a Q.snd f).inv
  compat := by
    have h1 : γ.hom ≫ F.isoSnd.hom ▷ f ≫ (α_ F.hom Q.snd f).hom =
        F.isoFst.hom ▷ y ≫ (α_ F.hom Q.fst y).hom ≫ F.hom ◁ Q.iso.hom := F.compat
    have hγ : γ.hom = F.isoFst.hom ▷ y ≫ (α_ F.hom Q.fst y).hom ≫ F.hom ◁ Q.iso.hom ≫
        (α_ F.hom Q.snd f).inv ≫ F.isoSnd.inv ▷ f := by
      rw [← reassoc_of% h1]
      simp
    have hF : F.isoFst.hom = (ρ_ j).inv ≫ j ◁ D.β ≫ (α_ j D.a Q.fst).inv ≫ D.α ▷ Q.fst := by
      have h2 : (ρ_ j).hom ≫ F.isoFst.hom = j ◁ D.β ≫ (α_ j D.a Q.fst).inv ≫ D.α ▷ Q.fst :=
        hγ'.symm.trans D.compat
      rw [← h2]
      simp
    rw [hγ, hF]
    calc _ = ((ρ_ j).inv ▷ y ≫ (j ◁ D.β) ▷ y ≫ (α_ j D.a Q.fst).inv ▷ y ≫
            (α_ (j ≫ D.a) Q.fst y).hom) ≫ (D.α ▷ (Q.fst ≫ y) ≫ F.hom ◁ Q.iso.hom) ≫
            (α_ F.hom Q.snd f).inv ≫ F.isoSnd.inv ▷ f := by
          bicategory
      _ = ((ρ_ j).inv ▷ y ≫ (j ◁ D.β) ▷ y ≫ (α_ j D.a Q.fst).inv ▷ y ≫
            (α_ (j ≫ D.a) Q.fst y).hom) ≫ ((j ≫ D.a) ◁ Q.iso.hom ≫ D.α ▷ (Q.snd ≫ f)) ≫
            (α_ F.hom Q.snd f).inv ≫ F.isoSnd.inv ▷ f := by
          rw [whisker_exchange]
      _ = _ := by
          bicategory

end CategoryTheory.DottedArrow

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack with representable diagonal has every scheme-valued point representable by
algebraic spaces. -/
private theorem isRepresentableFromSchemes_of_hasRepresentableDiagonal
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h : HasRepresentableDiagonal B S hS 𝒳) : IsRepresentableFromSchemes B S hS 𝒳 :=
  (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mp
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp h)

/-- For a 1-morphism of algebraic stacks representable by algebraic spaces, the existential
smooth-diagram test at smoothness is the relative property at smoothness. -/
private theorem hasPropertyOnSomeSmoothDiagram_isSmooth_iff_relative
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    HasPropertyOnSomeSmoothDiagram B S hS
        (fun {_ _} (q : _ ⟶ _) => Space.IsSmooth B S hS q) f ↔
      HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
        (spaceProperty B S hS fun {_ _} q => Space.IsSmooth B S hS q) f hf := by
  let Psm : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun {_ _} q => Space.IsSmooth B S hS q
  let _ : (spaceProperty B S hS Psm).IsStableUnderBaseChange := by
    simpa [Psm, spaceProperty] using Space.isSmooth_isStableUnderBaseChange B S hS
  let _ : (spaceProperty B S hS Psm).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) := by
    change (Space.smoothMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)
    exact Space.smooth_isLocalAtTarget_fppf B S hS
  exact hasPropertyOnSomeSmoothDiagram_iff_relative B S hS Psm
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) h𝒳 h𝒴 f hf

/-- The chart by an object of the site supplied by the algebraicity of an algebraic stack over
`S` (Stacks 026O), read as a 1-morphism of categories fibred in groupoids: it is representable
by algebraic spaces, it passes the existential smooth-diagram test of Stacks 06FM at smoothness
of morphisms of algebraic spaces, and it is surjective on objects.

Representability is the clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` itself, read
through the representable diagonal. The other two clauses of that definition say that every
algebraic space representing a base change of the chart along a scheme-valued point has
surjective and smooth structural morphism, which is the relative property of Stacks 03YK at
`AlgebraicGeometry.Space.surjectiveMorphismProperty` and at smoothness; Stacks 06D7 turns the
first into surjectivity on objects and Stacks 06FM the second into the smooth-diagram test. -/
theorem exists_schemeChart_isSmooth_isSurjectiveOnObjects
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    ∃ (U : BigFppfOver B S hS) (a : schemeFibredCategory B S hS U ⟶ 𝒳.1),
      IsRepresentableByAlgebraicSpaces B S hS a.hom ∧
        HasPropertyOnSomeSmoothDiagram B S hS
            (fun {_ _} (q : _ ⟶ _) => Space.IsSmooth B S hS q) a ∧
          IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS U).val.p 𝒳.1.val.p
            (CatFiberedInGroupoids.homFunctor a) := by
  rcases 𝒳.property with ⟨hXfib, _, hXdiag, U, atlas, _, hAtlas⟩
  let a0 : schemeFibredCategory B S hS U ⟶ CatFiberedInGroupoids.mk 𝒳.val.val hXfib :=
    Bicategory.InducedBicategory.mkHom atlas
  have hrep : IsRepresentableByAlgebraicSpaces B S hS a0.hom :=
    isRepresentableFromSchemes_of_hasRepresentableDiagonal B S hS 𝒳.val hXdiag U atlas
  exact ⟨U, a0, hrep,
    (hasPropertyOnSomeSmoothDiagram_isSmooth_iff_relative B S hS
      (isDeligneMumfordStack_schemeFibredCategory.{u, w} B S hS U).1 𝒳.property a0 hrep).2
      fun V y hy F hF hEquiv => (hAtlas V y hy F hF hEquiv).2,
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS a0 hrep).mpr
      fun V y hy F hF hEquiv => (hAtlas V y hy F hF hEquiv).1⟩

/-- **A smooth 1-morphism of algebraic stacks is formally smooth on objects** (Stacks 0DP0,
(1) `⇒` (2), the formal smoothness).

By Stacks 0DNY it suffices to find a dotted arrow in an infinitesimal lifting diagram
`(x, j, y, γ)`. The base change `P ⟶ T'` of `f` along `y` is smooth (Stacks 075W) and `P` is an
algebraic stack (Stacks 04T2); the square factors through `P` by the universal property of the
2-fibre product, Stacks 0DNZ gives a dotted arrow for the left square, and
`CategoryTheory.DottedArrow.ofTwoFibreProduct` pastes it into one for `f`. -/
theorem AlgebraicStacks.isFormallySmoothOnObjects_of_isSmooth
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsSmooth B S hS f) :
    IsFormallySmoothOnObjects B S hS 𝒳.1 𝒴.1 f.hom := by
  refine (isFormallySmoothOnObjects_iff_nonempty_dottedArrow f).mpr fun d => ?_
  let y' : schemeStack.{u, w} B S hS d.T' ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom d.y
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} d.y f.hom
  let F := CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} d.y f.hom
    ⟨schemeFibredCategory B S hS d.T, d.j, d.x, CatFiberedInGroupoids.twoIso d.γ⟩
  obtain ⟨D⟩ := exists_dottedArrow_of_isSmooth_of_isFirstOrderThickening B S hS d.T d.T'
    d.affine_T d.affine_T' d.i d.thickening Q.pt
    (isAlgebraicStack_twoFibreProductSquare B S hS y' f) Q.fst
    (AlgebraicStacks.isSmooth_baseChange B S hS f y' _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS y' f) hf)
    d.j d.j_canonical F.hom ((ρ_ d.j).hom ≫ F.isoFst.hom)
  exact ⟨DottedArrow.ofTwoFibreProduct (γ := CatFiberedInGroupoids.twoIso d.γ) F D rfl⟩

/-- **Stacks 0DP0, condition (1) implies condition (2).** A smooth 1-morphism of algebraic
stacks over `S` is locally of finite presentation (Stacks 0DNP) and formally smooth on objects
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFormallySmoothOnObjects_of_isSmooth`). -/
theorem AlgebraicStacks.isLocallyOfFinitePresentation_and_isFormallySmoothOnObjects_of_isSmooth
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsSmooth B S hS f) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∧
      IsFormallySmoothOnObjects B S hS 𝒳.1 𝒴.1 f.hom :=
  ⟨AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS f hf,
    AlgebraicStacks.isFormallySmoothOnObjects_of_isSmooth B S hS f hf⟩

/-- **Stacks 0DP0, condition (2) implies condition (1).** A 1-morphism of algebraic stacks over
`S` which is locally of finite presentation and formally smooth on objects is smooth.

The scheme atlas `a : 𝒰 ⟶ 𝒳` of Stacks 026O is smooth and surjective on objects, so it is
formally smooth on objects, so the composite `a ≫ f` is formally smooth on objects and locally
of finite presentation; both are representable by algebraic spaces, so on every base change to
an algebraic space over an object of the site those two properties become local finite
presentation and formal smoothness of a morphism of algebraic spaces, hence smoothness by
Stacks 04AM. The resulting smooth diagram for `a ≫ f`, composed with the atlas, is a smooth
diagram for `f`. -/
theorem AlgebraicStacks.isSmooth_of_isLocallyOfFinitePresentation_of_isFormallySmoothOnObjects
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hformal : IsFormallySmoothOnObjects B S hS 𝒳.1 𝒴.1 f.hom) :
    AlgebraicStacks.IsSmooth B S hS f := by
  obtain ⟨U, a0, hAtlasRep', haSomeSmooth, hsurjAtlas⟩ :=
    exists_schemeChart_isSmooth_isSurjectiveOnObjects.{u, w} B S hS 𝒳
  rcases 𝒴.property with ⟨_, _, hYdiag, _, _, _, _⟩
  let Ucat := schemeFibredCategory B S hS U
  let 𝒰 : Stack.AlgebraicStacks.{u, w} B S hS :=
    ⟨Ucat, (isDeligneMumfordStack_schemeFibredCategory.{u, w} B S hS U).1⟩
  let a : 𝒰 ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom a0
  let Psm : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun {_ _} q => Space.IsSmooth B S hS q
  have hPsm := Space.isSmoothLocalOnSourceAndTarget_smooth B S hS
  have hRelSmoothA : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS Psm) a0 hAtlasRep' :=
    (hasPropertyOnSomeSmoothDiagram_isSmooth_iff_relative
      B S hS 𝒰.property 𝒳.property a0 hAtlasRep').1 haSomeSmooth
  let b0 : Ucat ⟶ 𝒴.1 := a0 ≫ f.hom
  have hRep_b0 : IsRepresentableByAlgebraicSpaces B S hS b0.hom :=
    isRepresentableFromSchemes_of_hasRepresentableDiagonal B S hS 𝒴.val hYdiag U
      (BasedFunctor.comp a0.hom f.hom.hom)
  let Plfp : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun {_ _} q => Space.IsLocallyOfFinitePresentation B S hS q
  have hPlfp := Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS
  let _ : (spaceProperty B S hS Plfp).IsStableUnderBaseChange := by
    simpa [Plfp, spaceProperty] using
      Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  let _ : (spaceProperty B S hS Plfp).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) := by
    change MorphismProperty.IsLocalAtTarget
      (fun {X Y : AlgebraicSpaces B S hS} (q : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS q.hom)
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)
    exact (Space.isLocallyOfFinitePresentation_isLocalAtTarget_fpqc B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hRelLFP_b : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS Plfp) b0 hRep_b0 :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative
      B S hS Plfp hPlfp 𝒰.property 𝒴.property b0 hRep_b0).mp
      ((hasPropertyOnEverySmoothDiagram_iff_some B S hS Plfp hPlfp 𝒰.property 𝒴.property b0).mp
        (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS a f
          (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a haSomeSmooth) hfp))
  have hformalRel_b : BigFppfOver.IsRelativelyFormallySmooth B S hS b0 :=
    (BigFppfOver.isFormallySmoothOnObjects_iff_isRelativelyFormallySmooth B S hS b0 hRep_b0).mp
      (BigFppfOver.isFormallySmoothOnObjects_comp B S hS Ucat 𝒳.1 𝒴.1 a0 f.hom
        (isFormallySmoothOnObjects_of_isSmooth_unconditional.{u, w} B S hS 𝒰.property 𝒳.property
          a0 hAtlasRep' haSomeSmooth) hformal)
  have hRelSmooth_b : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS Psm) b0 hRep_b0 := by
    intro V y hy F hF hEquiv
    let Fy := (spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩
    have hglfp : Space.IsLocallyOfFinitePresentation B S hS
        (algebraicSpaceMap B S hS V Fy).hom := by
      simpa [Fy, Plfp, spaceProperty] using hRelLFP_b V y hy F hF hEquiv
    simpa [Psm, spaceProperty, Fy] using
      Space.isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth hglfp
        (hformalRel_b V y hy F hF hEquiv)
  let _ : (spaceProperty B S hS Psm).IsStableUnderComposition :=
    ⟨fun {X Y Z} q r hq hr =>
      Space.isSmooth_comp B S hS X.property Y.property Z.property q.hom r.hom hq hr⟩
  obtain ⟨A, A', hA, hA', aA, bA, hAA, ⟨ηA⟩, ⟨hRep_aA, hRel_aA⟩, hsurjCover, hbA, htop⟩ :=
    (hasPropertyOnSomeSmoothDiagram_isSmooth_iff_relative
      B S hS 𝒰.property 𝒴.property b0 hRep_b0).2 hRelSmooth_b
  exact ⟨A, A', hA, hA', aA ≫ a0, bA, hAA, ⟨ηA ≪≫ (α_ aA a0 f.hom).symm⟩,
    ⟨isRepresentableByAlgebraicSpaces_comp B S hS aA a0 hRep_aA hAtlasRep',
      hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS
        (spaceProperty B S hS Psm) aA a0 hRep_aA hAtlasRep' hRel_aA hRelSmoothA⟩,
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS A).val.p Ucat.val.p 𝒳.1.val.p
      (CatFiberedInGroupoids.homFunctor aA) (CatFiberedInGroupoids.homFunctor a0)
      (CatFiberedInGroupoids.homFunctor_comp_p a0) hsurjCover hsurjAtlas, hbA, htop⟩

/-- **Stacks 0DP0 (infinitesimal lifting criterion).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S` is smooth if and only if it is locally of finite presentation and formally
smooth, formal smoothness of a 1-morphism of algebraic stacks being formal smoothness on
objects (Stacks 0DNW). -/
@[stacks 0DP0, ega "0 19.0.1" "more general"]
theorem AlgebraicStacks.isSmooth_iff_isLocallyOfFinitePresentation_and_isFormallySmoothOnObjects
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.IsSmooth B S hS f ↔
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∧
        IsFormallySmoothOnObjects B S hS 𝒳.1 𝒴.1 f.hom :=
  ⟨AlgebraicStacks.isLocallyOfFinitePresentation_and_isFormallySmoothOnObjects_of_isSmooth
      B S hS f,
    fun h => AlgebraicStacks.isSmooth_of_isLocallyOfFinitePresentation_of_isFormallySmoothOnObjects
      B S hS f h.1 h.2⟩

end AlgebraicGeometry.Stack

end
