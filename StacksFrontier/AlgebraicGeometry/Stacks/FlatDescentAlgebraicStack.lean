module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationDescentComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse

/-!
# Descent of flatness for 1-morphisms of algebraic stacks (Stacks 06PZ and 06Q0)

Let `S` be a scheme contained in a big fppf site `B`.

**Stacks 06Q0.** For 1-morphisms `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` of algebraic stacks over `S`, if
the composite `f ≫ g` is flat and `f` is surjective and flat, then `g` is flat.

**Stacks 06PZ.** For `f : 𝒳 ⟶ 𝒴` and a surjective flat `g : 𝒵 ⟶ 𝒴`, if the base change of `f`
along `g` — the first projection of a 2-fibre product of the cospan `(g, f)` — is flat, then `f`
is flat.

Flatness of a 1-morphism of algebraic stacks is **Stacks 06PW**, the existential smooth-diagram
criterion of **Stacks 06FM** at flatness of morphisms of algebraic spaces; flatness of a morphism
of algebraic spaces is **Stacks 03ML**.

Stacks 06Q0 is the descent of flatness across the *first* factor of a composite. The source
proves it by covering `𝒵` by an algebraic space `W`, then `W ×_𝒵 𝒴` by an algebraic space `V`,
then `V ×_𝒴 𝒳` by an algebraic space `U`, observing that `U ⟶ V` is surjective and flat and
`U ⟶ W` is flat, and appealing to the statement for morphisms of algebraic spaces
(**Stacks 05VY** at the structure sheaf). Here the first two coverings are not chosen: the
*universal* form of Stacks 06FM hands the proof an arbitrary smooth diagram `(V, W, a, b, h)`
over `g`, which plays their role, and only the third algebraic stack is presented. Its projection
to `𝒱` is a base change of a base change of `f`, hence surjective by **Stacks 04ZU** and flat by
**Stacks 06PY**; its projection to `𝒲` factors through a base change of the diagram's own smooth
comparison 1-morphism, hence is flat by **Stacks 04TA** and **Stacks 06PX** after pasting the two
2-fibre products (**Stacks 003Q**) to exhibit `(𝒲 ×_𝒵 𝒴) ×_𝒴 𝒳` over the cospan `(b, f ≫ g)`.

Stacks 06PZ then follows from Stacks 06Q0 with no further geometry: the second projection of the
square is surjective by Stacks 04ZU and flat by Stacks 06PY, its composite with `f` is
2-isomorphic to the first projection followed by `g`, and that composite is flat by Stacks 06PX.

## Main definitions

* `AlgebraicGeometry.Space.FlatDescendsAlongSurjectiveFlat`: **Stacks 05VY** at the structure
  sheaf, as a proposition about the site — flatness of a morphism of algebraic spaces over `S`
  descends along a surjective flat morphism.

## Main results

* `AlgebraicGeometry.Stack.isFlat_of_representedChart` and
  `AlgebraicGeometry.Stack.isFlat_of_chart`: flatness passes from a chart of an algebraic stack
  lying over a morphism of algebraic spaces to that morphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_comp_of_isSurjective_of_isFlat`:
  **Stacks 06Q0**, with the space-level descent as a hypothesis.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isFlat_twoFibreProduct_fst`:
  **Stacks 06PZ**, with the space-level descent as a hypothesis.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isSurjective_of_isFlat_comp` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_twoFibreProduct_fst_descent`: the same two
  statements unconditionally, the hypothesis being discharged by
  `AlgebraicGeometry.Space.isFlat_of_comp_of_isSurjective_of_isFlat`, which is **Stacks 05VY**.

## Implementation notes

The space-level descent of Stacks 05VY is taken as the explicit hypothesis
`AlgebraicGeometry.Space.FlatDescendsAlongSurjectiveFlat`. Its shape is the one a proof of
Stacks 05VY at the structure sheaf has: algebraicity of the first two presheaves, the two
hypotheses on the first morphism and flatness of the composite. Nothing else in these proofs is
conditional.

Stacks 06PW is the existential form of the criterion of Stacks 06FM while the proof of
Stacks 06Q0 consumes the universal one, so the goal is moved across the equivalence of parts (1)
and (2) of Stacks 06FM (`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some`) at
the outset; flatness is smooth local on the source-and-target by **Stacks 06FC**, which is what
that equivalence needs. The sibling statement at local finite presentation, **Stacks 06Q9**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_comp_of_fppf`), needs
no such step because Stacks 06Q2 part (1) *is* the universal form.

The two squares of Stacks 06PZ are related by `CategoryTheory.Bicategory.TwoCommSq.swap`, which
exchanges the projections, so the base change of `g` along `f` is read off the same square and no
comparison 1-morphism is built.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q0](https://stacks.math.columbia.edu/tag/06Q0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05VY at the structure sheaf**, as a proposition about the big fppf site of `S`:
whenever `p : X ⟶ Y` is a surjective flat morphism of algebraic spaces over `S` and `p ≫ q` is
flat, `q` is flat. -/
abbrev FlatDescendsAlongSurjectiveFlat : Prop :=
  ∀ ⦃X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄,
    IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
    ∀ (p : X ⟶ Y) (q : Y ⟶ Z),
      IsSurjective B S hS p → IsFlat B S hS p → IsFlat B S hS (p ≫ q) → IsFlat B S hS q

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Flatness passes from a chart by an algebraic space to a morphism of algebraic spaces it
lies over.** Let `h : V ⟶ W` be a morphism of algebraic spaces over `S` and let `u`, `v` be
1-morphisms from the algebraic stack of an algebraic space `T` to those of `V` and of `W` such
that `u` followed by the 1-morphism attached to `h` is 2-isomorphic to `v`. If `u` is surjective
and flat and `v` is flat, then `h` is flat.

Source and target of `u` and of `v` are representable by algebraic spaces, so the third assertion
of **Stacks 06FM** reads the three hypotheses on the induced morphisms `T ⟶ V` and `T ⟶ W`, and
the 2-isomorphism makes the second the first followed by `h`. -/
theorem isFlat_of_representedChart
    (hdescent : Space.FlatDescendsAlongSurjectiveFlat B S hS)
    {T V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (h : V ⟶ W)
    (u : algebraicSpaceStack.{u, w} B S hS T hT ⟶ algebraicSpaceStack.{u, w} B S hS V hV)
    (v : algebraicSpaceStack.{u, w} B S hS T hT ⟶ algebraicSpaceStack.{u, w} B S hS W hW)
    (hcomm : u ≫ (Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1 :
        algebraicSpaceStack.{u, w} B S hS V hV ⟶ algebraicSpaceStack.{u, w} B S hS W hW) ≅ v)
    (husurj : IsSurjective B S hS u)
    (huflat : AlgebraicStacks.IsFlat B S hS u)
    (hvflat : AlgebraicStacks.IsFlat B S hS v) :
    Space.IsFlat B S hS h := by
  let p := representingMap B S hS
    (algebraicSpaceStack.{u, w} B S hS T hT).val (algebraicSpaceStack.{u, w} B S hS V hV).val
    T V (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) u.hom
  let q := representingMap B S hS
    (algebraicSpaceStack.{u, w} B S hS T hT).val (algebraicSpaceStack.{u, w} B S hS W hW).val
    T W (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) v.hom
  have hpSurjSp : Space.IsSurjective B S hS p :=
    isSurjective_representingMap_of_isSurjective.{u, w} B S hS
      (𝒳 := algebraicSpaceStack.{u, w} B S hS T hT)
      (𝒴 := algebraicSpaceStack.{u, w} B S hS V hV) T V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) u husurj
  have hpFlatSp : Space.IsFlat B S hS p :=
    isFlat_representingMap_of_isFlat.{u, w} B S hS
      (𝒳 := algebraicSpaceStack.{u, w} B S hS T hT)
      (𝒴 := algebraicSpaceStack.{u, w} B S hS V hV) T V hT hV
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) u huflat
  have hqFlatSp : Space.IsFlat B S hS q :=
    isFlat_representingMap_of_isFlat.{u, w} B S hS
      (𝒳 := algebraicSpaceStack.{u, w} B S hS T hT)
      (𝒴 := algebraicSpaceStack.{u, w} B S hS W hW) T W hT hW
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) v hvflat
  have hmap : p ≫ h = q :=
    representingMap_comp_eq_of_twoIso B S hS
      (𝒰 := (algebraicSpaceStack.{u, w} B S hS T hT).val) (T := T) (V := V) (W := W)
      (StacksRepresentableCFG.EquivalenceOver.refl _) u.hom v.hom h
      (Bicategory.InducedBicategory.isoHom
        (f := u ≫ Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1) (g := v) hcomm)
  have hpq : Space.IsFlat B S hS (p ≫ h) := by rw [hmap]; exact hqFlatSp
  exact hdescent hT hV p h hpSurjSp hpFlatSp hpq

/-- **Flatness passes from a presented algebraic stack to a morphism of algebraic spaces it lies
over.** Let `h : V ⟶ W` be a morphism of algebraic spaces over `S` and let `𝒰` be an algebraic
stack over `S` with 1-morphisms `u` and `v` to the algebraic stacks of `V` and of `W` such that
`u` followed by the 1-morphism attached to `h` is 2-isomorphic to `v`. If `u` is surjective and
flat and `v` is flat, then `h` is flat.

A smooth surjective chart of `𝒰` by an algebraic space is surjective and flat, by **Stacks
04TA**, so composing with it preserves the three hypotheses — the composition laws **Stacks
04ZT** and **Stacks 06PX** — and
`AlgebraicGeometry.Stack.isFlat_of_representedChart` applies to the composites. -/
theorem isFlat_of_chart
    (hdescent : Space.FlatDescendsAlongSurjectiveFlat B S hS)
    {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (h : V ⟶ W)
    {𝒰 : AlgebraicStacks.{u, w} B S hS}
    (u : 𝒰 ⟶ algebraicSpaceStack.{u, w} B S hS V hV)
    (v : 𝒰 ⟶ algebraicSpaceStack.{u, w} B S hS W hW)
    (hcomm : u ≫ (Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1 :
        algebraicSpaceStack.{u, w} B S hS V hV ⟶ algebraicSpaceStack.{u, w} B S hS W hW) ≅ v)
    (husurj : IsSurjective B S hS u)
    (huflat : AlgebraicStacks.IsFlat B S hS u)
    (hvflat : AlgebraicStacks.IsFlat B S hS v) :
    Space.IsFlat B S hS h := by
  obtain ⟨T, c, hcSmooth, hcSurj⟩ := exists_smooth_surjective_schemeStack B S hS 𝒰
  obtain ⟨e, heSmooth, heSurj⟩ :=
    exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS T
  have hrSmooth : AlgebraicStacks.IsSmooth B S hS (e ≫ c) :=
    AlgebraicStacks.isSmooth_comp B S hS e c heSmooth hcSmooth
  have hrSurj : IsSurjective B S hS (e ≫ c) := isSurjective_comp B S hS e c heSurj hcSurj
  have hrFlat : AlgebraicStacks.IsFlat B S hS (e ≫ c) :=
    AlgebraicStacks.isFlat_of_isSmooth B S hS (e ≫ c) hrSmooth
  exact isFlat_of_representedChart B S hS hdescent
    (isAlgebraicSpace_yoneda B S hS T) hV hW h ((e ≫ c) ≫ u) ((e ≫ c) ≫ v)
    (α_ (e ≫ c) u _ ≪≫ Bicategory.whiskerLeftIso (e ≫ c) hcomm)
    (isSurjective_comp B S hS (e ≫ c) u hrSurj husurj)
    (AlgebraicStacks.isFlat_comp B S hS (e ≫ c) u hrFlat huflat)
    (AlgebraicStacks.isFlat_comp B S hS (e ≫ c) v hrFlat hvflat)

namespace AlgebraicStacks

/-- **Stacks 06Q0.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over
`S`. If `f ≫ g` is flat and `f` is surjective and flat, then `g` is flat.

The descent of flatness along a surjective flat morphism of algebraic spaces (**Stacks 05VY** at
the structure sheaf) is taken as the hypothesis `hdescent`, so this is the general form rather
than the tag. The tag sits on `isFlat_of_isSurjective_of_isFlat_comp` below, which discharges
`hdescent` from [Stacks Project, Tag 05VY]. -/
theorem isFlat_of_comp_of_isSurjective_of_isFlat
    (hdescent : Space.FlatDescendsAlongSurjectiveFlat B S hS)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsFlat B S hS (f ≫ g))
    (hfsurj : Stack.IsSurjective B S hS f)
    (hfflat : IsFlat B S hS f) :
    IsFlat B S hS g := by
  refine (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS g).2
    ((Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsFlat B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      𝒴.property 𝒵.property g.hom).1 ?_)
  intro V W hV hW a b h η _ha _hb hcomp
  -- `D` is `𝒲 ×_𝒵 𝒴` and `E` is `(𝒲 ×_𝒵 𝒴) ×_𝒴 𝒳`, for `𝒲` the algebraic stack of `W`
  let bSt : Stack.algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒵 :=
    Bicategory.InducedBicategory.mkHom b
  let D := Stack.twoFibreProductSquareAlgebraicStacks B S hS bSt g
  have hD : Bicategory.IsTwoFibreProduct D :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bSt g
  let E := Stack.twoFibreProductSquareAlgebraicStacks B S hS D.snd f
  have hE : Bicategory.IsTwoFibreProduct E :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS D.snd f
  -- the pasted rectangle exhibits `E.pt` over the cospan `(bSt, f ≫ g)`
  have hDEfst : IsFlat B S hS (D.paste E).fst :=
    isFlat_baseChange B S hS (f ≫ g) bSt (D.paste E)
      (Bicategory.isTwoFibreProduct_paste hD hE) hfg
  -- `E.fst`, a base change of `f`, inherits surjectivity and flatness
  have hEsurj : Stack.IsSurjective B S hS E.fst :=
    Stack.isSurjective_of_isTwoFibreProduct B S hS E.swap
      (Bicategory.isTwoFibreProduct_swap hE) hfsurj
  have hEflat : IsFlat B S hS E.fst := isFlat_baseChange B S hS f D.snd E hE hfflat
  -- the comparison 1-morphism of the given diagram into `𝒲 ×_𝒵 𝒴`, smooth by the diagram's
  -- own clause
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b g.hom
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b g.hom
  let k₀ : Bicategory.TwoCommSq.PreHom (Stack.diagramCone B S hS g.hom a b h η) Q :=
    Quotient.out (hQ.from (Stack.diagramCone B S hS g.hom a b h η))
  let kSt : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ D.pt :=
    Bicategory.InducedBicategory.mkHom k₀.hom
  have hkSt : IsSmooth B S hS kSt :=
    Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ k₀.hom V hV
      (StacksRepresentableCFG.EquivalenceOver.refl _) (hcomp Q hQ k₀)
      (Space.isSmooth_id B S hS hV)
  -- `R` is `𝒱 ×_{𝒲 ×_𝒵 𝒴} ((𝒲 ×_𝒵 𝒴) ×_𝒴 𝒳)`
  let R := Stack.twoFibreProductSquareAlgebraicStacks B S hS kSt E.fst
  have hR : Bicategory.IsTwoFibreProduct R :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS kSt E.fst
  let hSt : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶
      Stack.algebraicSpaceStack.{u, w} B S hS W hW :=
    Bicategory.InducedBicategory.mkHom (Stack.associatedMap B S hS h).1
  have hKst : hSt ≅ kSt ≫ D.fst :=
    Bicategory.InducedBicategory.isoMk (f := hSt) (g := kSt ≫ D.fst) k₀.isoFst
  refine Stack.isFlat_of_chart B S hS hdescent hV hW h R.fst
    (R.snd ≫ (D.paste E).fst) ?_
    (Stack.isSurjective_of_isTwoFibreProduct B S hS R.swap
      (Bicategory.isTwoFibreProduct_swap hR) hEsurj)
    (isFlat_baseChange B S hS E.fst kSt R hR hEflat)
    (isFlat_comp B S hS R.snd (D.paste E).fst
      (isFlat_of_isSmooth B S hS R.snd
        (isSmooth_baseChange B S hS kSt E.fst R.swap
          (Bicategory.isTwoFibreProduct_swap hR) hkSt)) hDEfst)
  exact Bicategory.whiskerLeftIso R.fst hKst ≪≫ (α_ R.fst kSt D.fst).symm ≪≫
    Bicategory.whiskerRightIso R.iso D.fst ≪≫ α_ R.snd E.fst D.fst

/-- **Stacks 06PZ.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒵 ⟶ 𝒴` be 1-morphisms of algebraic stacks over
`S` with `g` surjective and flat, and let `P` be a 2-fibre product of the cospan `(g, f)`. If the
base change `P.fst` of `f` along `g` is flat, then `f` is flat.

The descent of flatness along a surjective flat morphism of algebraic spaces (**Stacks 05VY** at
the structure sheaf) is taken as the hypothesis `hdescent`, so this is the general form rather
than the tag. The tag sits on `isFlat_twoFibreProduct_fst_descent` below, which discharges
`hdescent` from [Stacks Project, Tag 05VY]. -/
theorem isFlat_of_isFlat_twoFibreProduct_fst
    (hdescent : Space.FlatDescendsAlongSurjectiveFlat B S hS)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hgsurj : Stack.IsSurjective B S hS g)
    (hgflat : IsFlat B S hS g)
    (hfst : IsFlat B S hS P.fst) :
    IsFlat B S hS f := by
  have hsndsurj : Stack.IsSurjective B S hS P.snd :=
    Stack.isSurjective_of_isTwoFibreProduct B S hS P hP hgsurj
  have hsndflat : IsFlat B S hS P.snd :=
    isFlat_baseChange B S hS g f P.swap (Bicategory.isTwoFibreProduct_swap hP) hgflat
  have htotal : IsFlat B S hS (P.snd ≫ f) :=
    (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS (P.snd ≫ f)).2
      (Stack.hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS _
        (Bicategory.InducedBicategory.isoHom P.iso)
        ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS (P.fst ≫ g)).1
          (isFlat_comp B S hS P.fst g hfst hgflat)))
  exact isFlat_of_comp_of_isSurjective_of_isFlat B S hS hdescent P.snd f htotal hsndsurj hsndflat

/-! ### The unconditional forms -/

/-- **Stacks 06Q0.** Let `𝒳 ⟶ 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. If
`𝒳 ⟶ 𝒵` is flat and `𝒳 ⟶ 𝒴` is surjective and flat, then `𝒴 ⟶ 𝒵` is flat.

This is `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_comp_of_isSurjective_of_isFlat` with
its hypothesis discharged by [Stacks Project, Tag 05VY]. -/
@[stacks 06Q0]
theorem isFlat_of_isSurjective_of_isFlat_comp
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsFlat B S hS (f ≫ g))
    (hfsurj : Stack.IsSurjective B S hS f)
    (hfflat : IsFlat B S hS f) :
    IsFlat B S hS g :=
  isFlat_of_comp_of_isSurjective_of_isFlat B S hS
    (fun _ _ _ hX hY p q hs hf hc ↦
      Space.isFlat_of_comp_of_isSurjective_of_isFlat B S hS hX hY p q hs hf hc)
    f g hfg hfsurj hfflat

/-- **Stacks 06PZ.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒵 ⟶ 𝒴` be 1-morphisms of algebraic stacks over
`S` with `g` surjective and flat, and let `P` exhibit `𝒵 ×_𝒴 𝒳`. If the base change
`𝒵 ×_𝒴 𝒳 ⟶ 𝒵` is flat, then `f` is flat.

This is `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isFlat_twoFibreProduct_fst` with its
hypothesis discharged by [Stacks Project, Tag 05VY]. -/
@[stacks 06PZ]
theorem isFlat_twoFibreProduct_fst_descent
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hgsurj : Stack.IsSurjective B S hS g)
    (hgflat : IsFlat B S hS g)
    (hfst : IsFlat B S hS P.fst) :
    IsFlat B S hS f :=
  isFlat_of_isFlat_twoFibreProduct_fst B S hS
    (fun _ _ _ hX hY p q hs hf hc ↦
      Space.isFlat_of_comp_of_isSurjective_of_isFlat B S hS hX hY p q hs hf hc)
    f g P hP hgsurj hgflat hfst

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
