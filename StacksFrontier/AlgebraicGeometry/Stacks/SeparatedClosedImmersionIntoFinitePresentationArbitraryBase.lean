module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowChangeOfBaseTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.ChangeOfBaseDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowNoetherianReductionInputs
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedClosedImmersionIntoFinitePresentationOverIntegers
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationAbsolute

/-!
# Stacks 0CQ2 over an arbitrary base scheme

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type from an algebraic stack over a scheme
`S` to a quasi-compact quasi-separated algebraic space. Then `f` factors, up to 2-isomorphism, as
a closed immersion `𝒳 ⟶ 𝒳'` followed by a separated 1-morphism of finite presentation
`𝒳' ⟶ Y` (Stacks 0CQ2).

The source's proof writes `Y` as a limit of Noetherian algebraic spaces by absolute Noetherian
approximation (Stacks 07SU), which is a statement over `Spec ℤ`; it is carried out over the base
`Spec ℤ` in
`AlgebraicGeometry.Stack.exists_separated_finitePresentation_closedImmersion_overIntegers`. Over
an arbitrary base `S` we view everything over `Spec ℤ` by Construction A of Stacks 04X5, apply
that result, and carry the factorization back to `S` by Construction B: the stack `𝒳'` over
`Spec ℤ` lies over `S` through `Y`, and the closed immersion commutes with the structure
1-morphisms to `S` because a 2-isomorphism of 1-morphisms into the stack represented by `S` is
an equality (`AlgebraicGeometry.Stack.exists_descent_changeBase`). Separatedness, finite
presentation and being a closed immersion all descend along Construction A.

## Main results

* `AlgebraicGeometry.Stack.exists_descent_changeBase`: a factorization over `S'` of the view of a
  1-morphism over `S` descends to `S`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_changeBase`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_changeBase` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isClosedImmersion_of_changeBase`: these properties
  descend along Construction A.
* `AlgebraicStacks.closedImmersionIntoFinitePresentationStatement_holds_overScheme`:
  Stacks 0CQ2, over an arbitrary base scheme `S`.

## References

* [Stacks Project, Tag 0CQ2](https://stacks.math.columbia.edu/tag/0CQ2)
* [Stacks Project, Tag 0CQ1](https://stacks.math.columbia.edu/tag/0CQ1)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

section ChangeOfBase

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-! ### Properties descending along Construction A -/

namespace AlgebraicStacks

/-- **Local finite presentation descends along Construction A**, for a 1-morphism to the
algebraic stack of an algebraic space. Let `a : U ⟶ 𝒳` be a smooth chart, surjective on objects,
and `h : U ⟶ Y` the representing map of `a ≫ f`. The view of `a` is smooth, hence locally of
finite presentation (Stacks 0DNP), so the view of `a ≫ f` is locally of finite presentation and
so is its representing map, the lower-shriek extension of `h`
(`AlgebraicGeometry.Stack.representingMap_changeBaseHom_eq_relocalizeMap`); then so is `h`
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`), hence `a ≫ f`, and the
chart cancels (`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp_surjective`). -/
theorem isLocallyOfFinitePresentation_of_changeBase
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsLocallyOfFinitePresentation B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f)) :
    IsLocallyOfFinitePresentation B S hS f := by
  obtain ⟨U, hU, a, ha, hasurj⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒳.property
  let a' : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom a
  let A := changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g a'
  have hA : IsLocallyOfFinitePresentation B S' hS' A :=
    isLocallyOfFinitePresentation_of_isSmooth B S' hS' A
      (isSmooth_of_isRelativelySmooth B S' hS' A
        (isRelativelySmooth_changeBaseHom_of_isRelativelySmooth B S S' hS hS' g a ha))
  have hAf := isLocallyOfFinitePresentation_comp B S' hS' A
    (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f) hA hf
  have hP' := prop_representingMap_of_hasPropertyOnSomeSmoothDiagram B S' hS'
    (𝒳 := changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS U))
    (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS Y))
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S' hS' h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S' hS') _ _
    (isAlgebraicSpace_viewOver B S S' hS hS' g U hU)
    (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY)
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g U)
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
    (changeBaseHom B S S' hS hS' g (a ≫ f.hom))
    ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S' hS' _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S' hS')
      (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
        (algebraicSpaceStack.{u, w} B S hS U hU)).property
      (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
        (algebraicSpaceStack.{u, w} B S hS Y hY)).property _).1 hAf)
  rw [representingMap_changeBaseHom_eq_relocalizeMap B S S' hS hS' g U Y (a ≫ f.hom)] at hP'
  have hP := (Space.holdsOnEveryEtaleChart_relocalizeMap_iff B S S' hS hS' g _ _).1 hP'
  refine (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    𝒳.property (algebraicSpaceStack.{u, w} B S hS Y hY).property f.hom).2 ?_
  exact hasPropertyOnSomeSmoothDiagram_of_comp_surjective B S hS _ a f.hom ha hasurj
    (hasPropertyOnSomeSmoothDiagram_of_prop_representingMap B S hS
      (𝒳 := fibredCategory B S hS U) (𝒴 := fibredCategory B S hS Y)
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h) U Y hU hY
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (a ≫ f.hom) hP)

/-- **Quasi-separatedness of a 1-morphism of algebraic stacks (Stacks 04YW) descends along
Construction A**: both conditions of Stacks 04XB on the relative diagonal do, by
`AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_of_changeBase` and
`AlgebraicGeometry.Stack.isQuasiSeparated_relativeDiagonal_of_changeBase`. -/
theorem isQuasiSeparated_of_changeBase {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsQuasiSeparated B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f)) :
    IsQuasiSeparated B S hS f :=
  ⟨isQuasiCompact_relativeDiagonal_of_changeBase B S S' hS hS' g 𝒳.val 𝒴.val f.hom hf.1,
    isQuasiSeparated_relativeDiagonal_of_changeBase B S S' hS hS' g 𝒳.val 𝒴.val f.hom hf.2⟩

/-- **Being a closed immersion of algebraic stacks (Stacks 04YL) descends along Construction A**:
representability by algebraic spaces does
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff`), and so does
the closed-immersion condition of Stacks 04XB
(`AlgebraicGeometry.Stack.isClosedImmersion_changeBaseHom_iff`). -/
theorem isClosedImmersion_of_changeBase {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsClosedImmersion B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f)) :
    IsClosedImmersion B S hS f :=
  ⟨(isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g f.hom.hom).1 hf.1,
    (isClosedImmersion_changeBaseHom_iff B S S' hS hS' g f.hom).1 hf.2⟩

end AlgebraicStacks

/-! ### Descending a factorization along Construction A -/

/-- Two functors to `𝒞/A` which agree after `Over.map g` and are related by a natural
transformation whose components have identity underlying morphisms are equal. -/
private theorem functor_eq_of_overMap_comp_eq {𝒞 : Type*} [Category 𝒞] {A X : 𝒞} (g : A ⟶ X)
    {D : Type*} [Category D] (F₁ F₂ : D ⥤ Over A) (h : F₁ ⋙ Over.map g = F₂ ⋙ Over.map g)
    (α : F₁ ⟶ F₂) (hα : ∀ x, ∃ hx : (F₁.obj x).left = (F₂.obj x).left,
      (α.app x).left = eqToHom hx) :
    F₁ = F₂ := by
  have hobj : ∀ x, F₁.obj x = F₂.obj x := fun x => by
    obtain ⟨hx, hαx⟩ := hα x
    refine CostructuredArrow.obj_ext _ _ hx ?_
    have hw := Over.w (α.app x)
    rw [hαx] at hw
    exact hw
  refine CategoryTheory.Functor.ext hobj fun x y φ => ?_
  apply Over.OverMorphism.ext
  have := congrArg CommaMorphism.left (Functor.congr_hom h φ)
  simpa [Over.eqToHom_left] using this

/-- **A factorization over `S'` of the view of a 1-morphism over `S` descends to `S`.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `φ : 𝒲 ⟶ A(𝒴)` be a 1-morphism of
algebraic stacks over `S'` into Construction A of `𝒴`, and let `ι : A(𝒳) ⟶ 𝒲` satisfy
`ι ≫ φ ≅ A(f)`. Construction B of the pair `(𝒲, φ ≫ (A(𝒴) ⟶ S/S'))` (Stacks 04X5) is an
algebraic stack `𝒲₀` over `S` whose Construction A is `𝒲`; the underlying functors of `φ` and
`ι` are 1-morphisms `φ₀ : 𝒲₀ ⟶ 𝒴` and `ι₀ : 𝒳 ⟶ 𝒲₀` over `S`, the second because the
2-isomorphism `ι ≫ φ ≅ A(f)` has components over identities of the big fppf site of `S'`, hence
over identities of that of `S`; and `ι₀ ≫ φ₀ ≅ f`. Construction A carries `φ₀` and `ι₀` back to
`φ` and `ι`, so every property of 1-morphisms over `S'` that `φ` or `ι` has, the views of `φ₀`
or `ι₀` have. -/
theorem exists_descent_changeBase {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (𝒲 : AlgebraicStacks.{u, w} B S' hS')
    (φ : 𝒲 ⟶ changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒴)
    (ι : changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳 ⟶ 𝒲)
    (e : ι ≫ φ ≅ changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f) :
    ∃ (𝒲₀ : AlgebraicStacks.{u, w} B S hS) (φ₀ : 𝒲₀ ⟶ 𝒴) (ι₀ : 𝒳 ⟶ 𝒲₀),
      Nonempty (ι₀ ≫ φ₀ ≅ f) ∧
      (∀ P : ∀ {𝒜 ℬ : AlgebraicStacks.{u, w} B S' hS'}, (𝒜 ⟶ ℬ) → Prop,
        P φ → P (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ₀)) ∧
      (∀ P : ∀ {𝒜 ℬ : AlgebraicStacks.{u, w} B S' hS'}, (𝒜 ⟶ ℬ) → Prop,
        P ι → P (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g ι₀)) := by
  obtain ⟨⟨⟨X₀, inst, q⟩, hfib⟩, halg⟩ := 𝒲
  obtain ⟨⟨⟨F, hF⟩⟩⟩ := φ
  have hF' : F ⋙ 𝒴.val.val.p ⋙ Over.map g = q := hF
  let 𝒲₀ : AlgebraicStacks.{u, w} B S hS := algebraicStackConstructionB B S S' hS hS' g
    ⟨⟨⟨⟨X₀, inst, q⟩, hfib⟩, halg⟩,
      Bicategory.InducedBicategory.mkHom ⟨F, hF⟩ ≫ changeBaseStructureHom B S S' hS hS' g 𝒴⟩
  let φ₀ : 𝒲₀ ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom ⟨F, rfl⟩)
  let he := AlgebraicStacks.underlyingIso B S' hS' e
  have hFG : (ι.hom.hom.toFunctor ⋙ F ⋙ 𝒴.val.val.p) ⋙ Over.map g =
      (f.hom.hom.toFunctor ⋙ 𝒴.val.val.p) ⋙ Over.map g :=
    (congrArg (ι.hom.hom.toFunctor ⋙ ·) hF').trans
      (ι.hom.hom.w.trans (congrArg (· ⋙ Over.map g) f.hom.hom.w).symm)
  have hw : ι.hom.hom.toFunctor ⋙ F ⋙ 𝒴.val.val.p = 𝒳.val.val.p := by
    refine (functor_eq_of_overMap_comp_eq g (ι.hom.hom.toFunctor ⋙ F ⋙ 𝒴.val.val.p)
      (f.hom.hom.toFunctor ⋙ 𝒴.val.val.p) hFG (Functor.whiskerRight he.hom 𝒴.val.val.p)
      fun x => ⟨by have h := congrArg Comma.left (Functor.congr_obj hFG x); exact h, ?_⟩).trans
        f.hom.hom.w
    have := e.hom.hom.hom.isHomLift' x
    have h2 := IsHomLift.fac' (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒴).val.val.p
      (𝟙 ((changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳).val.val.p.obj x))
      (e.hom.hom.hom.app x)
    have h3 := congrArg CommaMorphism.left h2
    simp only [Category.id_comp, eqToHom_trans, Over.eqToHom_left] at h3
    exact h3
  let ι₀ : 𝒳 ⟶ 𝒲₀ := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom ⟨ι.hom.hom.toFunctor, hw⟩)
  have h𝒲 : changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒲₀ =
      ⟨⟨⟨X₀, inst, q⟩, hfib⟩, halg⟩ := by
    refine Subtype.ext (Subtype.ext ?_)
    show BasedCategory.mk X₀ inst (F ⋙ 𝒴.val.val.p ⋙ Over.map g) = BasedCategory.mk X₀ inst q
    rw [hF']
  have transport : ∀ (P : ∀ {𝒜 ℬ : AlgebraicStacks.{u, w} B S' hS'}, (𝒜 ⟶ ℬ) → Prop)
      {𝒜₁ 𝒜₂ ℬ₁ ℬ₂ : AlgebraicStacks.{u, w} B S' hS'} (h𝒜 : 𝒜₁ = 𝒜₂) (hℬ : ℬ₁ = ℬ₂)
      (a₁ : 𝒜₁ ⟶ ℬ₁) (a₂ : 𝒜₂ ⟶ ℬ₂),
      HEq a₁.hom.hom.toFunctor a₂.hom.hom.toFunctor → P a₂ → P a₁ := by
    intro P 𝒜₁ 𝒜₂ ℬ₁ ℬ₂ h𝒜 hℬ a₁ a₂ ha h
    subst h𝒜 hℬ
    obtain rfl : a₁ = a₂ := Bicategory.InducedBicategory.hom_ext
      (Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' (eq_of_heq ha)))
    exact h
  refine ⟨𝒲₀, φ₀, ι₀, ⟨?_⟩, fun P h => transport P h𝒲 rfl _ _ HEq.rfl h,
    fun P h => transport P rfl h𝒲 _ _ HEq.rfl h⟩
  refine Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso he fun x => ?_))
  exact (Functor.isHomLift_overMap_iff 𝒴.val.val.p g (𝟙 (𝒳.val.val.p.obj x)) (he.hom.app x)
    (Functor.congr_obj hw x) (BasedFunctor.w_obj f.hom.hom x)).1
    (e.hom.hom.hom.isHomLift' x)

end ChangeOfBase

/-! ### Stacks 0CQ2 over an arbitrary base -/

namespace AlgebraicStacks

/-- **Stacks 0CQ2.** Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack over a scheme `S`
to an algebraic space over `S`, with `f` of finite type and separated and `Y` quasi-compact and
quasi-separated. Then there are a separated 1-morphism of finite presentation `f' : 𝒳' ⟶ Y` and a
closed immersion `i : 𝒳 ⟶ 𝒳'` of algebraic stacks over `Y`, that is, with `i ≫ f' ≅ f`.

The source's proof, which approximates `Y` by Noetherian algebraic spaces (Stacks 07SU), takes
place over `Spec ℤ`, where it is
`AlgebraicGeometry.Stack.exists_separated_finitePresentation_closedImmersion_overIntegers`.
Construction A of Stacks 04X5 carries `f` to a separated 1-morphism, locally of finite type,
from a quasi-compact algebraic stack to the view `Λ Y` of `Y` over `Spec ℤ`, which is again
quasi-compact and quasi-separated; the factorization obtained there descends to `S`
(`AlgebraicGeometry.Stack.exists_descent_changeBase`), and separatedness, finite presentation
and being a closed immersion descend along Construction A. -/
@[stacks 0CQ2]
theorem closedImmersionIntoFinitePresentationStatement_holds_overScheme (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    ClosedImmersionIntoFinitePresentationStatement.{u, w} B S hS := by
  intro Y hY 𝒳 f hft hsep hYqc hYqs
  let hZ := B.contains_terminal
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  have hY' := isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g Y hY
  obtain ⟨hΦ, hΦm, hΨ, hΨm⟩ :=
    isFinitePresentation_viewAlgebraicSpaceStackComparisons.{u, w} B S (⊤_ Scheme.{u}) hS hZ g
      Y hY
  have hlft := isLocallyOfFiniteType_comp B (⊤_ Scheme.{u}) hZ _ _
    (isLocallyOfFiniteType_changeBaseHomAlgebraicStacks B S (⊤_ Scheme.{u}) hS hZ g Y hY 𝒳 f
      hft.1)
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ hZ hΦ.1)
  have h𝒳qc := (isQuasiCompactStack_changeBaseAlgebraicStacks_iff B S (⊤_ Scheme.{u}) hS hZ g
    𝒳).2 (isQuasiCompactStack_of_isQuasiCompactMorphism.{u, w} B S hS f hft.2
      (isQuasiCompactStack_fibredCategory.{u, w} B S hS Y hY hYqc _))
  obtain ⟨𝒳'', f'', ι, hsep'', hfp, hι, ⟨e⟩⟩ :=
    exists_separated_finitePresentation_closedImmersion_overIntegers hZ
      ((OverShriek.relocalizePresheafFunctor g).obj Y) hY'
      (changeBaseAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS hZ g 𝒳)
      (changeBaseHomAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS hZ g f ≫
        viewAlgebraicSpaceStackToRelocalized.{u, w} B S (⊤_ Scheme.{u}) hS hZ g Y hY) hlft h𝒳qc
      (isSeparated_comp B _ hZ _ _
        (isProper_relativeDiagonal_changeBase B S (⊤_ Scheme.{u}) hS hZ g _ _ f.hom hsep)
        (isSeparated_of_isMonomorphism B _ hZ _ hΦm))
      (Space.isQuasiCompactSpace_relocalizePresheafFunctor_obj B S (⊤_ Scheme.{u}) hS hZ g Y
        hYqc)
      (Space.isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs)
  have e' : ι ≫ (f'' ≫ relocalizedToViewAlgebraicSpaceStack.{u, w} B S (⊤_ Scheme.{u}) hS hZ g
      Y hY) ≅ changeBaseHomAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS hZ g f :=
    (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso e _ ≪≫
      Bicategory.associator _ _ _ ≪≫
      Bicategory.whiskerLeftIso _
        (viewAlgebraicSpaceStackRoundTripIso B S (⊤_ Scheme.{u}) hS hZ g Y hY) ≪≫
      Bicategory.rightUnitor _
  obtain ⟨𝒳', f', i, ⟨eiso⟩, hPf, hPi⟩ :=
    exists_descent_changeBase B S (⊤_ Scheme.{u}) hS hZ g f 𝒳'' _ ι e'
  have hfp' := isFinitePresentation_comp B _ hZ _ _ hfp hΨ
  have hsep' := isSeparated_comp B _ hZ _ _ hsep'' (isSeparated_of_isMonomorphism B _ hZ _ hΨm)
  refine ⟨𝒳', f', i, ?_, ⟨?_, ?_, ?_⟩, ?_, ⟨eiso⟩⟩
  · exact isSeparated_of_changeBase B S (⊤_ Scheme.{u}) hS hZ g f'
      (hPf (fun φ => IsSeparated B _ hZ φ) hsep')
  · exact isLocallyOfFinitePresentation_of_changeBase B S (⊤_ Scheme.{u}) hS hZ g Y hY 𝒳' f'
      (hPf (fun φ => IsLocallyOfFinitePresentation B _ hZ φ) hfp'.1)
  · exact isQuasiCompactMorphism_of_changeBase B S (⊤_ Scheme.{u}) hS hZ g f'
      (hPf (fun φ => IsQuasiCompactMorphism B _ hZ φ) hfp'.2.1)
  · exact isQuasiSeparated_of_changeBase B S (⊤_ Scheme.{u}) hS hZ g f'
      (hPf (fun φ => IsQuasiSeparated B _ hZ φ) hfp'.2.2)
  · exact isClosedImmersion_of_changeBase B S (⊤_ Scheme.{u}) hS hZ g i
      (hPi (fun φ => IsClosedImmersion B _ hZ φ) hι)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
