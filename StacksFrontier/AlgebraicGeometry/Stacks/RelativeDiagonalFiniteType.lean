module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# The relative diagonal of a morphism of algebraic stacks is locally of finite type (04XS, part 2)

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over the big fppf site of `S`. Its relative diagonal

`Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`

is representable by algebraic spaces (part (1) of Stacks 04XS), and this file proves that it is
**locally of finite type**, which is part (2) of **Stacks 04XS**. No hypothesis is placed on `f`
beyond `𝒳` and `𝒴` being algebraic stacks; in particular `f` is not assumed representable by
algebraic spaces, which is what distinguishes this from part (2) of Stacks 04YQ.

## Main results

* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.isPullback_relVertHomPresheaf`:
  the cartesian square labelled 04XT, as a square of presheaves — the presheaf of vertical
  morphisms lying over the comparison isomorphism of a point `(x, x', α)` is the fibre product
  `Isom_𝒳(x, x') ×_{Isom_𝒴(f x, f x'), α} U`.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack`:
  **Stacks 04XS, part (2)**.

## Implementation notes

The source's argument is run as it stands. At a scheme-valued point `(x, x', α)` of
`𝒳 ×_{f, 𝒴, f} 𝒳` over a scheme `U` the base change of `Δ_f` is the presheaf
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf`, and the square
04XT exhibits it as the fibre product of
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafMap` — the pushforward of
vertical morphisms along `f` — over the section
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.alphaSection`. That the square is
cartesian is checked presheaf-section by presheaf-section, where it is
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.pushforward_eq_alphaSection_iff`: a
vertical morphism satisfies the fibre condition exactly when its pushforward is the `α`-section.

The two corners on the right are algebraic spaces over `U` by Stacks 045G, applied to `𝒳` and to
`𝒴` at the point of the *absolute* product assembled from the two components by
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.pairFunctor`; the comparison with an
isomorphism presheaf is
`CategoryTheory.Functor.vertHomPresheafIsoIsomPresheafOfPoint`. The apex is an algebraic space by
part (1), in the form
`AlgebraicGeometry.Stack.isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack`.

The finite-type input is **Stacks 04XR**: `Isom_𝒳(x, x') ⟶ U` is locally of finite type. Since
`Isom_𝒳(x, x') ⟶ Isom_𝒴(f x, f x') ⟶ U` is that same morphism — both legs go to the terminal
presheaf of the site of `U` — Stacks 0462 makes `Isom_𝒳(x, x') ⟶ Isom_𝒴(f x, f x')` locally of
finite type, and Stacks 03XH carries it along the base change to the left vertical arrow of the
square. Nothing about `Isom_𝒴` beyond its algebraicity is used, exactly as in the source.

Passing between the property of the representing space read over `U` and read over `S` is
Stacks 04SG, in the form `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` and
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`, as in
`StacksFrontier/AlgebraicGeometry/Stacks/DiagonalLocallyOfFiniteType.lean`, which is the absolute
analogue of this file.

The statement is the one part (2) of Stacks 04YQ is stated in — the §04XB quantifier written out
longhand — with the representability hypothesis on `f` dropped, so that a consumer of part (2) of
Stacks 04XS gets the same `Prop` for an arbitrary 1-morphism.

## References

* [Stacks Project, Tag 0462](https://stacks.math.columbia.edu/tag/0462)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe v₁ u₁ v₂ u₂ v₃ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₃} 𝒴]
  {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}
  {Y : 𝒯 ⥤ RelProd p q F}

/-- The inclusion of the presheaf of vertical morphisms lying over the comparison isomorphism of
`Y` into the presheaf of all vertical morphisms `Y₁ ⟶ Y₂`, i.e. the top arrow
`Isom_𝒳(x, x') ×_{Isom_𝒴(f x, f x'), α} U ⟶ Isom_𝒳(x, x')` of the square 04XT. -/
noncomputable def relVertHomInclusion (hq : q.IsFiberedInGroupoids)
    (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    relVertHomPresheaf hq hp hY hF ⟶ VertHom.presheaf hp (h1' hY) (h2' hY) where
  app _ := ↾fun m => m.1
  naturality _ _ _ := rfl

/-- The comparison isomorphism of `Y` as a section of `Isom_𝒴(f Y₁, f Y₂)`, i.e. the bottom
arrow `U ⟶ Isom_𝒴(f x, f x')` of the square 04XT. -/
noncomputable def alphaTerminalMap (hq : q.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    (⊤_ (𝒯ᵒᵖ ⥤ Type v₃)) ⟶ VertHom.presheaf hq (VertHom.comp_comp_eq hF (h1' hY))
      (VertHom.comp_comp_eq hF (h2' hY)) where
  app a := ↾fun _ => alphaSection hY a.unop
  naturality a a' h := by
    ext _
    exact (restrict_alphaSection hq hY (VertHom.comp_comp_eq hF (h1' hY))
      (VertHom.comp_comp_eq hF (h2' hY)) h.unop).symm

/-- **The square 04XT.** For a point `Y = (x, x', α)` of `X ×_{F, 𝒴, F} X` over `𝒯`, the presheaf
of vertical morphisms `x ⟶ x'` whose image under `F` is `α` is the fibre product

`Isom_X(x, x') ×_{Isom_𝒴(F x, F x'), α} ⊤`

of presheaves on `𝒯`. This is the cartesian square in the proof of Stacks 04XS. -/
theorem isPullback_relVertHomPresheaf (hq : q.IsFiberedInGroupoids)
    (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    IsPullback (relVertHomInclusion hq hp hY hF)
      (terminal.from (relVertHomPresheaf hq hp hY hF))
      (VertHom.presheafMap hq hp (h1' hY) (h2' hY) hF (VertHom.comp_comp_eq hF (h1' hY))
        (VertHom.comp_comp_eq hF (h2' hY)))
      (alphaTerminalMap hq hY hF) := by
  rw [IsPullback.iff_app]
  intro V
  have hterm : IsTerminal ((⊤_ (𝒯ᵒᵖ ⥤ Type v₃)).obj V) :=
    terminalIsTerminal.isTerminalObj ((evaluation 𝒯ᵒᵖ (Type v₃)).obj V)
  have _ : Unique ((⊤_ (𝒯ᵒᵖ ⥤ Type v₃)).obj V) := Types.isTerminalEquivUnique _ hterm
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext m
    exact (pushforward_eq_alphaSection_iff hY hF V.unop m.1).mpr m.2
  · rintro m n ⟨h₁, -⟩
    exact Subtype.ext h₁
  · intro x₂ x₃ hx
    refine ⟨⟨x₂, (pushforward_eq_alphaSection_iff hY hF V.unop x₂).mp hx⟩, rfl,
      Subsingleton.elim _ _⟩

end CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Stack

open CategoryTheory.TwoFibreProductOver.DiagonalFibre
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

universe u t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The left vertical arrow of the square 04XT is locally of finite type.** For a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks and a scheme-valued point `Y = (x, x', α)` of
`𝒳 ×_{f, 𝒴, f} 𝒳` over `U`, the presheaf `Isom_𝒳(x, x') ×_{Isom_𝒴(f x, f x'), α} U` has locally
of finite type structural morphism over `U`.

Stacks 04XR makes `Isom_𝒳(x, x') ⟶ U` locally of finite type, hence Stacks 0462 makes
`Isom_𝒳(x, x') ⟶ Isom_𝒴(f x, f x')` locally of finite type, and Stacks 03XH carries that along
the base change of the square 04XT. -/
theorem isLocallyOfFiniteType_relVertHomPresheaf_of_isAlgebraicStack
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, t} B S hS 𝒴.val)
    (U : BigFppfOver B S hS)
    (Y : BigFppfOver B U.left.1 U.left.2 ⥤
      TwoFibreProductOver 𝒳.val.p 𝒳.val.p 𝒴.val.p f.hom.toFunctor f.hom.toFunctor)
    (hY : Y ⋙ RelProdP 𝒳.val.p 𝒴.val.p f.hom.toFunctor = Over.map U.hom) :
    Space.IsLocallyOfFiniteType B U.left.1 U.left.2
      (terminal.from (relVertHomPresheaf 𝒴.isFiberedInGroupoids 𝒳.isFiberedInGroupoids hY
        f.hom.w)) := by
  classical
  let _ : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let _ : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  obtain ⟨_hfibX, _hstX, hDX, _hatlasX⟩ := id h𝒳
  obtain ⟨_hfibY, _hstY, hDY, _hatlasY⟩ := id h𝒴
  set hp := 𝒳.isFiberedInGroupoids
  set hq := 𝒴.isFiberedInGroupoids
  -- The three presheaves of the square 04XT, and the terminal one.
  set I𝒳 := VertHom.presheaf hp (h1' hY) (h2' hY)
  set I𝒴 := VertHom.presheaf hq (VertHom.comp_comp_eq f.hom.w (h1' hY))
    (VertHom.comp_comp_eq f.hom.w (h2' hY))
  set R := relVertHomPresheaf hq hp hY f.hom.w
  -- The two corners on the right are isomorphism presheaves, hence algebraic spaces (045G).
  set x₁ := Functor.sliceValue 𝒳.val.p U (Y₁' Y) (h1' hY)
  set x₂ := Functor.sliceValue 𝒳.val.p U (Y₂' Y) (h2' hY)
  have cmp𝒳 : I𝒳 ≅ (Over.iteratedSliceBackward U).op ⋙ 𝒳.val.p.isomPresheaf x₁ x₂ :=
    Functor.vertHomPresheafIsoIsomPresheafOfPoint 𝒳.val.p hp U
      (pairFunctor (h1' hY) (h2' hY)) (pairFunctor_comp (h1' hY) (h2' hY))
  have cmp𝒴 : I𝒴 ≅ (Over.iteratedSliceBackward U).op ⋙ 𝒴.val.p.isomPresheaf
      (Functor.sliceValue 𝒴.val.p U (Y₁' Y ⋙ f.hom.toFunctor)
        (VertHom.comp_comp_eq f.hom.w (h1' hY)))
      (Functor.sliceValue 𝒴.val.p U (Y₂' Y ⋙ f.hom.toFunctor)
        (VertHom.comp_comp_eq f.hom.w (h2' hY))) :=
    Functor.vertHomPresheafIsoIsomPresheafOfPoint 𝒴.val.p hq U
      (pairFunctor (VertHom.comp_comp_eq f.hom.w (h1' hY))
        (VertHom.comp_comp_eq f.hom.w (h2' hY)))
      (pairFunctor_comp (VertHom.comp_comp_eq f.hom.w (h1' hY))
        (VertHom.comp_comp_eq f.hom.w (h2' hY)))
  obtain ⟨A, hA, ⟨eA⟩⟩ :=
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp hDX U x₁ x₂
  obtain ⟨A', hA', ⟨eA'⟩⟩ :=
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).mp hDY U _ _
  -- Transport algebraicity along an isomorphism and the full faithfulness of `uliftFunctor`.
  have alg {P Q G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u} (c : P ≅ Q)
      (e : G ⋙ uliftFunctor.{u, u} ≅ Q ⋙ uliftFunctor.{u, u}) :=
    isAlgebraicSpace_of_iso B U.left.1 U.left.2
      (c.trans (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso e).symm)
  have hI𝒳 := alg cmp𝒳 eA hA
  have hI𝒴 := alg cmp𝒴 eA' hA'
  -- The apex is an algebraic space by part (1) of Stacks 04XS.
  obtain ⟨G, hG, ⟨eG⟩⟩ := isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack.{u, u, u + 1}
    B S hS 𝒳 𝒴 f h𝒳 h𝒴 U Y hY
  have hR := alg (Iso.refl R) eG.symm hG
  -- The terminal presheaf is an algebraic space.
  have hT : IsAlgebraicSpace B U.left.1 U.left.2
      (⊤_ ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B U.left.1 U.left.2
      (terminalIsTerminal.uniqueUpToIso
        (Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj U.left.2)))))
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2 (Over.mk (𝟙 (B.obj U.left.2))))
  -- Stacks 04XR, transported along the comparison with the isomorphism presheaf.
  have hlft𝒳 : Space.IsLocallyOfFiniteType B U.left.1 U.left.2 (terminal.from I𝒳) :=
    (Space.isLocallyOfFiniteType_terminal_iff_of_iso B U.left.1 U.left.2 cmp𝒳).mpr
      (isLocallyOfFiniteType_isomPresheaf B S hS 𝒳 h𝒳 U x₁ x₂)
  -- Stacks 0462: the pushforward of vertical morphisms is locally of finite type.
  set pm := VertHom.presheafMap hq hp (h1' hY) (h2' hY) f.hom.w
    (VertHom.comp_comp_eq f.hom.w (h1' hY)) (VertHom.comp_comp_eq f.hom.w (h2' hY))
  have hlftpm : Space.IsLocallyOfFiniteType B U.left.1 U.left.2 pm := by
    refine Space.isLocallyOfFiniteType_of_comp B U.left.1 U.left.2 hI𝒳 hI𝒴 hT pm
      (terminal.from I𝒴) ?_
    rw [show pm ≫ terminal.from I𝒴 = terminal.from I𝒳 from terminal.hom_ext _ _]
    exact hlft𝒳
  -- Stacks 03XH along the base change of the square 04XT.
  have sq := isPullback_relVertHomPresheaf hq hp hY f.hom.w
  let RS : AlgebraicSpaces B U.left.1 U.left.2 := ⟨R, hR⟩
  let XS : AlgebraicSpaces B U.left.1 U.left.2 := ⟨I𝒳, hI𝒳⟩
  let YS : AlgebraicSpaces B U.left.1 U.left.2 := ⟨I𝒴, hI𝒴⟩
  let TS : AlgebraicSpaces B U.left.1 U.left.2 := ⟨⊤_ _, hT⟩
  have sq' : IsPullback
      (ObjectProperty.homMk (relVertHomInclusion hq hp hY f.hom.w) : RS ⟶ XS)
      (ObjectProperty.homMk (terminal.from R) : RS ⟶ TS)
      (ObjectProperty.homMk pm : XS ⟶ YS)
      (ObjectProperty.homMk (alphaTerminalMap hq hY f.hom.w) : TS ⟶ YS) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := Space.locallyOfFiniteTypeProperty B U.left.1 U.left.2) sq' hlftpm

/-- **Stacks 04XS, part (2).** The relative diagonal of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over the big fppf site of `S` is locally of finite type: it is representable by algebraic
spaces, and every algebraic space representing one of its base changes along a scheme-valued
point of `𝒳 ×_{f, 𝒴, f} 𝒳` has locally-of-finite-type structural morphism — the
every-étale-chart form of part (1) of Stacks 03XF.

No hypothesis is placed on `f`; part (2) of Stacks 04YQ is the same statement for a 1-morphism
representable by algebraic spaces. -/
@[stacks 04XS "diagonal_locally_finite_type"]
theorem isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) :
    ∃ _hΔ : IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p
          = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
            (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsLocallyOfFiniteType B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, ?_⟩
  intro U y hy F hF hE
  have hri : (Space.locallyOfFiniteTypeProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := Space.locallyOfFiniteTypeProperty B S hS)
  obtain ⟨e⟩ := (nonempty_equivalenceOver_fst_iff 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hy f.hom.hom.w F).mp hE
  have hiso : relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids hy
      f.hom.hom.w ≅ F :=
    ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso e
  refine (prop_algebraicSpaceMap_iff B S hS (Space.locallyOfFiniteTypeProperty B S hS)
    U F hF).mpr ?_
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) F).mpr ?_
  refine Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2 terminalIsTerminal
    (Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj U.left.2)))) (terminal.from F)
    (Space.toYonedaId B U.left.1 U.left.2 F) ?_
  exact (Space.isLocallyOfFiniteType_terminal_iff_of_iso B U.left.1 U.left.2 hiso).mp
    (isLocallyOfFiniteType_relVertHomPresheaf_of_isAlgebraicStack B S hS 𝒳.val 𝒴.val f.hom
      𝒳.2 𝒴.2 U y hy)

end AlgebraicGeometry.Stack

end
