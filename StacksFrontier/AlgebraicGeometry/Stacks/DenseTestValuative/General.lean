module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Stacks 0CQM from Chow's lemma for algebraic stacks

The proof of **Stacks 0CQM** uses Chow's lemma for algebraic stacks (**Stacks 0CQ8**) over the
affine Noetherian charts of the target, to produce a proper surjective cover of the base change
by an algebraic space. This file assembles the proof from the statement of Stacks 0CQ8, taken as
the explicit input `hchow` of an unregistered theorem.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_denseTestExistence_of_chowLemma`:
  Stacks 0CQM, given the statement of Stacks 0CQ8.

## Implementation notes

Chow's lemma is stated for a 1-morphism to the algebraic stack of an algebraic space `Y`; over a
chart `V = Spec A` it is applied with `Y` the presheaf represented by `V` and the 1-morphism
composed with the comparison `V ⟶ Y` whose representing morphism is the identity, which is
separated and of finite type because the identity is.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **The comparison of the stack of a scheme with the stack of the presheaf it represents.**
The 1-morphism `V ⟶ h_V` whose representing morphism is the identity of `h_V` is separated and
of finite type. -/
theorem exists_schemeStack_hom_algebraicSpaceStack_yoneda (V : BigFppfOver B S hS) :
    ∃ c : schemeStack.{u, w} B S hS V ⟶
        algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V),
      IsSeparated B S hS c ∧ IsFiniteType B S hS c := by
  have hyV := isAlgebraicSpace_yoneda B S hS V
  let eV := PresheafOfCategories.sliceElementsEquivalenceOver V
  let eY : StacksRepresentableCFG.EquivalenceOver
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hyV).val.val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p :=
    StacksRepresentableCFG.EquivalenceOver.refl _
  obtain ⟨c, hc⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := schemeStack.{u, w} B S hS V)
    (𝒴 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) hyV) (yoneda.obj V) (yoneda.obj V)
    eV eY (𝟙 _)
  have hid : Space.IsProper B S hS (𝟙 (yoneda.obj V)) :=
    Space.isProper_of_isIso B S hS (𝟙 (yoneda.obj V))
  exact ⟨c,
    (isSeparated_iff_representingMap B S hS (yoneda.obj V) (yoneda.obj V) hyV hyV eV eY c).2
      (hc ▸ hid.1),
    (isLocallyOfFiniteType_iff_representingMap B S hS (yoneda.obj V) (yoneda.obj V)
      hyV hyV eV eY c).2 (hc ▸ hid.2.1.1),
    (isQuasiCompactMorphism_iff_representingMap B S hS (yoneda.obj V) (yoneda.obj V)
      hyV hyV eV eY c).2 (hc ▸ hid.2.1.2)⟩

/-- **Stacks 0CQM, from Chow's lemma for algebraic stacks.** Let `f : 𝒳 ⟶ 𝒴` and
`h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`, with `𝒴` locally Noetherian, `f` and
`h` of finite type, `f` separated, and the image of `|h| : |𝒰| → |𝒳|` dense in `|𝒳|`. If every
2-commutative diagram `Spec K ⟶ 𝒰 ⟶ 𝒳 ⟶ 𝒴`, `Spec A ⟶ 𝒴` with `A` a discrete valuation ring
with fraction field `K` admits a dotted arrow after an extension of `K` and passage to a
dominating valuation ring, then `f` is proper.

The statement of Stacks 0CQ8 is the explicit input `hchow`. -/
theorem isProper_of_denseTestExistence_of_chowLemma
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (h : 𝒰 ⟶ 𝒳)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : letI := Stack.pointTopology B S hS 𝒳.val
      Dense (Set.range (Stack.pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒳.val.property
        h.hom.hom)))
    (hlift : ValuativeCriterion.DenseTestExistence B S hS h f)
    (hchow : ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {𝒳' : AlgebraicStacks.{u, w} B S hS}
      {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y),
      Space.IsQuasiCompactSpace B S hS Y → Space.IsAbsolutelyQuasiSeparated B S hS hZ Y →
      ∀ (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f' → IsFiniteType B S hS f' →
        ∃ (X Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
          (_ : IsAlgebraicSpace B S hS Xbar)
          (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳') (i : X ⟶ Xbar) (g : Xbar ⟶ Y),
          IsProper B S hS a ∧ Stack.IsSurjective B S hS a ∧
          Space.IsOpenImmersion B S hS i ∧ Space.IsProper B S hS g ∧
          Nonempty (a ≫ f' ≅ algebraicSpaceStackMap.{u, w} B S hS hX hY (i ≫ g))) :
    IsProper B S hS f := by
  refine isProper_of_denseTestExistence_of_forall_affine B S hS f h h𝒴 hf hh hsep hdense hlift ?_
  intro A hA a₀ _ g _ P hP
  have hf' : IsFiniteType B S hS P.fst := isFiniteType_baseChange B S hS f g P hP hf
  have hsep' : IsSeparated B S hS P.fst :=
    isSeparated_baseChange_of_isTwoFibreProduct B S hS f g P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hsep
  let V := siteObject B S hS hA a₀
  obtain ⟨c, hcsep, hcft⟩ := exists_schemeStack_hom_algebraicSpaceStack_yoneda.{u, w} B S hS V
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  have hYqc : Space.IsQuasiCompactSpace B S hS (yoneda.obj V) :=
    Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS V
      (inferInstanceAs (IsAffine (Spec A)))
  have hYqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj V) :=
    Space.isAbsolutelyQuasiSeparated_yoneda_obj B S hS hZ V
      (inferInstanceAs (QuasiSeparatedSpace (Spec A)))
  obtain ⟨X, -, hX, -, a, -, -, ha, has, -, -, -⟩ :=
    hchow hZ (isAlgebraicSpace_yoneda B S hS V) hYqc hYqs (P.fst ≫ c)
      (isSeparated_comp B S hS P.fst c hsep' hcsep) (isFiniteType_comp B S hS P.fst c hf' hcft)
  exact exists_schemeCover_of_algebraicSpaceCover B S hS A hA a₀ P.fst hsep' hf' hX a ha has

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
