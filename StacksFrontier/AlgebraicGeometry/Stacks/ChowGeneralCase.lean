module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowChangeOfBaseCarryBack
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowNoetherianReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.DiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStackAbsolute

/-!
# Chow's lemma for algebraic stacks over an arbitrary base

The change of base of the proof of Chow's lemma for algebraic stacks (Stacks 0CQ8): the source
works over `Spec ℤ`, where Stacks 07SU applies. A Chow cover of the view over `S'` of
`f : 𝒳 ⟶ Y` carries back to one of `f` (`HasChowCover.of_changeBase`), and with the base
`S' = Spec ℤ` this gives Chow's lemma over any base, granted the statements of Stacks 0CQ2,
Stacks 0CN4 and Stacks 0CPZ (`hasChowCover_of_statements`).

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u})

/-- Being locally of finite type depends only on the 2-isomorphism class of a 1-morphism: the
smooth-diagram criterion of Stacks 06FM is reindexed along the 2-isomorphism. -/
theorem isLocallyOfFiniteType_of_twoIso_hom {S : Scheme.{u}} {hS : B.Contains S}
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f g : 𝒳 ⟶ 𝒴) (e : f.hom ≅ g.hom) (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS g := by
  have key := fun k : 𝒳.val ⟶ 𝒴.val =>
    Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property 𝒴.property k
  exact (key g.hom).2 (Stack.hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h) e ((key f.hom).1 hf))

section ChangeOfBase

variable (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- The comparison `Φ` of the view over `S'` of the stack of an algebraic space `F` with the stack
of `Λ F` is proper and surjective: it is a monomorphism of finite presentation, hence separated
and of finite type, universally closed by Stacks 0CPT since composing it with the comparison in
the other direction gives a 1-morphism 2-isomorphic to the identity, and surjective since its
underlying functor is an equivalence. -/
theorem isProper_isSurjective_viewAlgebraicSpaceStackToRelocalized
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    IsProper B S' hS' (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g F hF) ∧
      IsSurjective B S' hS' (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g F hF) := by
  obtain ⟨hfp, hmono, -, hmono'⟩ :=
    isFinitePresentation_viewAlgebraicSpaceStackComparisons.{u, w} B S S' hS hS' g F hF
  exact ⟨⟨isSeparated_of_isMonomorphism B S' hS' _ hmono,
    ⟨isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S' hS' hfp.1, hfp.2.1⟩,
    universallyClosed_of_comp_of_isSeparated B S' hS' _ _
      (universallyClosed_of_iso B S' hS'
        (viewAlgebraicSpaceStackRoundTripIso.{u, w} B S S' hS hS' g F hF).symm
        (universallyClosed_id B S' hS' _))
      (isSeparated_of_isMonomorphism B S' hS' _ hmono')⟩,
    isSurjective_of_isEquivalenceFunctor B S' hS' _
      (StacksRepresentableCFG.EquivalenceOver.isEquivalence_hom_functor
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g F))⟩

/-- The 1-morphism of algebraic stacks of an isomorphism of algebraic spaces is proper and
surjective. -/
theorem isProper_isSurjective_algebraicSpaceStackMap_of_isIso
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (t : X ⟶ Y) [IsIso t] :
    IsProper B S hS (algebraicSpaceStackMap.{u, w} B S hS hX hY t) ∧
      IsSurjective B S hS (algebraicSpaceStackMap.{u, w} B S hS hX hY t) :=
  ⟨(isProper_algebraicSpaceStackMap_iff.{u, w} B S hS hX hY t).2 (Space.isProper_of_isIso B S hS t),
    isSurjective_of_isGerbeOver B S hS _
      (isGerbeOver_algebraicSpaceStackMap_of_isIso.{u, w} hX hY t)⟩

/-- **Surjectivity descends along Construction A**: Construction A does not change the points
(`AlgebraicGeometry.Stack.changeBasePointsEquiv`), compatibly with the maps on points. -/
theorem isSurjective_of_isSurjective_changeBaseHomAlgebraicStacks
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsSurjective B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f)) :
    IsSurjective B S hS f := by
  intro y
  obtain ⟨x, hx⟩ := hf (changeBasePointsEquiv B S S' hS hS' g 𝒴.val.val 𝒴.val.property y)
  obtain ⟨x₀, rfl⟩ := (changeBasePointsEquiv B S S' hS hS' g 𝒳.val.val 𝒳.val.property).surjective x
  exact ⟨x₀, (changeBasePointsEquiv B S S' hS hS' g 𝒴.val.val 𝒴.val.property).injective
    ((changeBasePointsEquiv_pointsMap B S S' hS hS' g 𝒳.val.property 𝒴.val.property
      f.hom.hom x₀).trans hx)⟩

/-- Precomposing a proper surjective 1-morphism `a` out of the stack of `X` with the comparison
`Φ` for `X₀` and the 1-morphism of an isomorphism `Λ X₀ ≅ X` gives a proper surjective
1-morphism. -/
theorem isProper_isSurjective_viewAlgebraicSpaceStackToRelocalized_comp
    {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX₀ : IsAlgebraicSpace B S hS X₀)
    {X : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S' hS' X)
    (e₀ : (OverShriek.relocalizePresheafFunctor g).obj X₀ ≅ X) {𝒳 : AlgebraicStacks.{u, w} B S' hS'}
    (a : algebraicSpaceStack.{u, w} B S' hS' X hX ⟶ 𝒳) (ha : IsProper B S' hS' a)
    (has : IsSurjective B S' hS' a) :
    IsProper B S' hS' (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g X₀ hX₀ ≫
        algebraicSpaceStackMap.{u, w} B S' hS' (isAlgebraicSpace_viewOver B S S' hS hS' g X₀ hX₀)
          hX e₀.hom ≫ a) ∧
      IsSurjective B S' hS' (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g X₀ hX₀ ≫
        algebraicSpaceStackMap.{u, w} B S' hS' (isAlgebraicSpace_viewOver B S S' hS hS' g X₀ hX₀)
          hX e₀.hom ≫ a) := by
  obtain ⟨hΦ, hΦs⟩ := isProper_isSurjective_viewAlgebraicSpaceStackToRelocalized.{u, w}
    B S S' hS hS' g X₀ hX₀
  obtain ⟨he, hes⟩ := isProper_isSurjective_algebraicSpaceStackMap_of_isIso.{u, w}
    B S' hS' (isAlgebraicSpace_viewOver B S S' hS hS' g X₀ hX₀) hX e₀.hom
  exact ⟨isProper_comp B S' hS' _ _ hΦ (isProper_comp B S' hS' _ _ he ha),
    isSurjective_comp B S' hS' _ _ hΦs (isSurjective_comp B S' hS' _ _ hes has)⟩

/-- The representing map of the view `Λ X₀ ⟶ 𝒳 ⟶ Y` of a Chow cover over `S'` is the composite
`Λ X₀ ≅ X ⟶ X̄ ⟶ Λ Y`, by Stacks 04SW. -/
theorem representingMap_viewAlgebraicSpaceStackToRelocalized_comp_eq
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX₀ : IsAlgebraicSpace B S hS X₀)
    {X Xb : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S' hS' X)
    (e₀ : (OverShriek.relocalizePresheafFunctor g).obj X₀ ≅ X)
    (a : algebraicSpaceStack.{u, w} B S' hS' X hX ⟶
      changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳)
    (i : X ⟶ Xb) (p : Xb ⟶ (OverShriek.relocalizePresheafFunctor g).obj Y)
    (ea : a ≫ (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f ≫
        viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g Y hY) ≅
      algebraicSpaceStackMap.{u, w} B S' hS' hX (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY)
        (i ≫ p)) :
    representingMap B S' hS'
      (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
        (algebraicSpaceStack.{u, w} B S hS X₀ hX₀)).val
      (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
        (algebraicSpaceStack.{u, w} B S hS Y hY)).val
      ((OverShriek.relocalizePresheafFunctor g).obj X₀)
      ((OverShriek.relocalizePresheafFunctor g).obj Y)
      (PresheafOfCategories.relocalizeElementsEquivalenceOver g X₀)
      (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
      ((viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g X₀ hX₀ ≫
        algebraicSpaceStackMap.{u, w} B S' hS' (isAlgebraicSpace_viewOver B S S' hS hS' g X₀ hX₀)
          hX e₀.hom ≫ a) ≫ changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f).hom =
      e₀.hom ≫ i ≫ p := by
  have hX₀' := isAlgebraicSpace_viewOver B S S' hS hS' g X₀ hX₀
  have h1 := representingMap_comp B S' hS' _ _ _
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g X₀)
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    ((viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g X₀ hX₀ ≫
      algebraicSpaceStackMap.{u, w} B S' hS' hX₀' hX e₀.hom ≫ a) ≫
        changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f).hom
    (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g Y hY).hom
  rw [representingMap_viewAlgebraicSpaceStackToRelocalized, Category.comp_id] at h1
  rw [← h1]
  have h2 := representingMap_comp B S' hS' _ _ _
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g X₀)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g X₀ hX₀).hom
    (algebraicSpaceStackMap.{u, w} B S' hS' hX₀' hX e₀.hom ≫ a ≫
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f ≫
        viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g Y hY)).hom
  rw [representingMap_viewAlgebraicSpaceStackToRelocalized, Category.id_comp] at h2
  exact h2.trans ((representingMap_congr_twoIso B S' hS' _ _ _ _
    (Bicategory.InducedBicategory.isoHom
      (Bicategory.whiskerLeftIso (algebraicSpaceStackMap.{u, w} B S' hS' hX₀' hX e₀.hom) ea ≪≫
        eqToIso (algebraicSpaceStackMap_comp.{u, w} B S' hS' hX₀' hX _ e₀.hom (i ≫ p)).symm))).trans
    (representingMap_associatedMap B S' hS' _ _ _))

/-- **A Chow cover of the view of `f` over `S'` carries back to `S`.** Let `f : 𝒳 ⟶ Y` be a
1-morphism from an algebraic stack over `S` to an algebraic space, and suppose the conclusion of
Stacks 0CQ8 holds for its view `𝒳 ⟶ Λ Y` over `S'` (Construction A of Stacks 04X5 followed by the
comparison with the stack of the lower-shriek extension `Λ Y`). Then it holds for `f`.

The algebraic spaces `X` and `X̄` of the cover over `S'` lie over the representable presheaf of
`S` through `Λ Y`, so by Stacks 04SG they are `Λ X₀` and `Λ X̄₀`, and the open immersion and the
proper morphism come from morphisms over `S`, which keep their properties. The cover `X ⟶ 𝒳`
becomes a 1-morphism `Λ X₀ ⟶ 𝒳` of the views whose representing map is compatible with the
structural morphisms to `S`, so it commutes on the nose with the structure 1-morphisms to `S/S'`
and comes from a 1-morphism `X₀ ⟶ 𝒳` over `S` (the bijection on 1-morphisms of Stacks 04X5).
It is proper and surjective: separatedness, quasi-compactness, universal closedness and
surjectivity descend along Construction A, and local finite type follows from that of the
composite with `f` by Stacks 06U9. The triangle 2-commutes because both sides have the same
representing map (Stacks 04SW), the lower-shriek extension being faithful. -/
theorem HasChowCover.of_changeBase {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (h : HasChowCover.{u, w} B S' hS' (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY)
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f ≫
        viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g Y hY)) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨X, Xb, hX, hXb, a, i, p, ha, has, hi, hp, ⟨ea⟩⟩ := h
  obtain ⟨Xb₀, hXb₀, e₁, he₁⟩ := Space.exists_relocalize_iso_of_structureMap B S S' hS hS' g hXb
    (p ≫ OverShriek.viewStructureMap g Y)
  obtain ⟨X₀, hX₀, e₀, he₀⟩ := Space.exists_relocalize_iso_of_structureMap B S S' hS hS' g hX
    (i ≫ p ≫ OverShriek.viewStructureMap g Y)
  obtain ⟨i₀, hi₀⟩ := Space.exists_relocalize_map_eq B S S' hS hS' g (e₀.hom ≫ i ≫ e₁.inv)
    (by rw [← he₁]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; exact he₀)
  obtain ⟨p₀, hp₀⟩ := Space.exists_relocalize_map_eq B S S' hS hS' g (G := Y) (e₁.hom ≫ p)
    (by rwa [Category.assoc])
  have hi₀' : Space.IsOpenImmersion B S hS i₀ :=
    (Space.isOpenImmersion_relocalizeMap_iff B S S' hS hS' g i₀).1 <| hi₀ ▸
      Space.isOpenImmersion_comp B S' hS' _ _ (Space.isOpenImmersion_of_isIso B S' hS' _)
        (Space.isOpenImmersion_comp B S' hS' _ _ hi (Space.isOpenImmersion_of_isIso B S' hS' _))
  have hp₀' : Space.IsProper B S hS p₀ :=
    (Space.isProper_relocalize_iff B S hS S' hS' g hXb₀ hY p₀).1 <|
      hp₀ ▸ (Space.isProper_isIso_comp_iff B S' hS' e₁.hom p).2 hp
  let a' := viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g X₀ hX₀ ≫
    algebraicSpaceStackMap.{u, w} B S' hS' (isAlgebraicSpace_viewOver B S S' hS hS' g X₀ hX₀) hX
      e₀.hom ≫ a
  have ha' := isProper_isSurjective_viewAlgebraicSpaceStackToRelocalized_comp B S S' hS hS' g
    hX₀ hX e₀ a ha has
  have hrep := representingMap_viewAlgebraicSpaceStackToRelocalized_comp_eq B S S' hS hS' g
    hY f hX₀ hX e₀ a i p ea
  have hcompat := comp_changeBaseStructureHom_eq_of_representingMap B S S' hS hS' g hX₀ hY a' f
    (by rw [hrep]; simp only [Category.assoc]; exact he₀)
  let aS : algebraicSpaceStack.{u, w} B S hS X₀ hX₀ ⟶ 𝒳 :=
    (algebraicStackConstructionHomEquiv B S S' hS hS' g _ _).symm ⟨a'.hom, hcompat⟩
  have hrepS : representingMap B S hS (fibredCategory B S hS X₀) (fibredCategory B S hS Y) X₀ Y
      (.refl _) (.refl _) (aS ≫ f).hom = i₀ ≫ p₀ := by
    apply Space.relocalize_map_injective B S S' hS hS' g
    rw [Functor.map_comp, hi₀, hp₀,
      ← representingMap_changeBaseHom_eq_relocalizeMap B S S' hS hS' g X₀ Y (aS ≫ f).hom]
    exact hrep.trans (by simp)
  obtain ⟨θ⟩ := hrepS ▸ nonempty_twoIso_associatedMap_representingMap B S hS X₀ Y (aS ≫ f).hom
  have eS : aS ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hX₀ hY (i₀ ≫ p₀) :=
    .symm <| Bicategory.InducedBicategory.isoMk θ
  refine ⟨X₀, Xb₀, hX₀, hXb₀, aS, i₀, p₀,
    ⟨isProper_relativeDiagonal_of_changeBase B S S' hS hS' g _ _ aS.hom ha'.1.1, ⟨?_,
      isQuasiCompactMorphism_of_changeBaseHomAlgebraicStacks B S S' hS hS' g aS ha'.1.2.1.2⟩,
      universallyClosed_of_universallyClosed_constructionAHom B S S' hS hS' g aS ha'.1.2.2⟩,
    isSurjective_of_isSurjective_changeBaseHomAlgebraicStacks B S S' hS hS' g aS ha'.2,
    hi₀', hp₀', ⟨eS⟩⟩
  refine isLocallyOfFiniteType_of_comp B S hS aS f
    (isLocallyOfFiniteType_of_twoIso_hom B _ _ (Bicategory.InducedBicategory.isoHom eS.symm) ?_)
  exact (isLocallyOfFiniteType_algebraicSpaceStackMap_iff.{u, w} B S hS hX₀ hY _).2
    (Space.isLocallyOfFiniteType_comp' B S hS i₀ p₀ hXb₀ hY
      (Space.isLocallyOfFiniteType_of_isEtale' B S hS i₀
        (Space.isEtale_of_isOpenImmersion B S hS hi₀'))
      hp₀'.2.1.1)

end ChangeOfBase

/-- **Chow's lemma for algebraic stacks (Stacks 0CQ8), over any base, granted the statements of
Stacks 0CQ2, Stacks 0CN4 and Stacks 0CPZ over `Spec ℤ`.** Let `f : 𝒳 ⟶ Y` be a 1-morphism from
an algebraic stack to an algebraic space over `S`, with `Y` quasi-compact and quasi-separated and
`f` separated of finite type. Then there are an algebraic space `X` with a proper surjective
1-morphism `X ⟶ 𝒳`, an open immersion `X ⟶ X̄` and a proper morphism `X̄ ⟶ Y` of algebraic
spaces such that `X ⟶ 𝒳 ⟶ Y` is 2-isomorphic to `X ⟶ X̄ ⟶ Y`.

The view of `f` over `Spec ℤ` (Construction A of Stacks 04X5, followed by the comparison with the
stack of `Λ Y`) is separated and of finite type, `Λ Y` is quasi-compact and quasi-separated, so
`AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_overIntegers_of_statements` gives a Chow
cover of the view, which carries back to `S` by
`AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_changeBase`. -/
theorem hasChowCover_of_statements
    (h0CQ2 : ClosedImmersionIntoFinitePresentationStatement.{u, w} B (⊤_ Scheme.{u})
      B.contains_terminal)
    (h0CN4 : FinitePresentationStackDescendsStatement.{u, w} B (⊤_ Scheme.{u})
      B.contains_terminal)
    (h0CPZ : SeparatedAtFiniteStageStatement.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal)
    {S : Scheme.{u}} {hS : B.Contains S} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    HasChowCover.{u, w} B S hS hY f := by
  let hZ := B.contains_terminal
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  have hY' := isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g Y hY
  have hY'qc : Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ
      ((OverShriek.relocalizePresheafFunctor g).obj Y) :=
    Space.isQuasiCompactSpace_relocalizePresheafFunctor_obj B S (⊤_ Scheme.{u}) hS hZ g Y hYqc
  have hY'qs : Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ
      ((OverShriek.relocalizePresheafFunctor g).obj Y) :=
    Space.isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs
  let Φ := viewAlgebraicSpaceStackToRelocalized.{u, w} B S (⊤_ Scheme.{u}) hS hZ g Y hY
  obtain ⟨hΦfp, hΦmono, -, -⟩ :=
    isFinitePresentation_viewAlgebraicSpaceStackComparisons.{u, w} B S (⊤_ Scheme.{u}) hS hZ g Y hY
  let f' := changeBaseHomAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS hZ g f ≫ Φ
  have h𝒳 : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property :=
    isQuasiCompactStack_of_isQuasiCompactMorphism.{u, w} B S hS f hft.2
      (isQuasiCompactStack_fibredCategory.{u, w} B S hS Y hY hYqc _)
  have hsep' : IsSeparated B (⊤_ Scheme.{u}) hZ f' :=
    isSeparated_comp B (⊤_ Scheme.{u}) hZ _ _
      (isProper_relativeDiagonal_changeBase B S (⊤_ Scheme.{u}) hS hZ g _ _ f.hom hsep)
      (isSeparated_of_isMonomorphism B (⊤_ Scheme.{u}) hZ _ hΦmono)
  have hft' : IsFiniteType B (⊤_ Scheme.{u}) hZ f' :=
    ⟨isLocallyOfFiniteType_comp B (⊤_ Scheme.{u}) hZ _ _
      (isLocallyOfFiniteType_changeBaseHomAlgebraicStacks B S (⊤_ Scheme.{u}) hS hZ g Y hY 𝒳 f
        hft.1)
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ hΦfp.1),
    isQuasiCompactMorphism_of_isQuasiCompactStack_absolute.{u, w} B (⊤_ Scheme.{u}) hZ hZ f'
      ((isQuasiCompactStack_changeBaseAlgebraicStacks_iff B S (⊤_ Scheme.{u}) hS hZ g 𝒳).2 h𝒳)
      (isAbsolutelyQuasiSeparated_algebraicSpaceStack B (⊤_ Scheme.{u}) hZ hZ hY' hY'qs)⟩
  exact HasChowCover.of_changeBase B S (⊤_ Scheme.{u}) hS hZ g hY f
    (hasChowCover_overIntegers_of_statements B h0CQ2 h0CN4 h0CPZ hY' hY'qc hY'qs f' hsep' hft')

end AlgebraicGeometry.Stack.AlgebraicStacks

end
