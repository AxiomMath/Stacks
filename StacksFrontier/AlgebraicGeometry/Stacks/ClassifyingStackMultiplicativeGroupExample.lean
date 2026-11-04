module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.MultiplicativeSmoothDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackClosedSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSmoothStacks
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationAxioms

/-!
# The classifying stack `[Spec k/𝐆_m] ⟶ Spec k` (Remark Stacks 0DS5)

Remark **Stacks 0DS5** observes that, for a 1-morphism `f : 𝒯 ⟶ 𝒳` as in Lemma Stacks 0DS4 with
scheme theoretic image `𝒵`, it need not be that `dim 𝒯 ≥ dim 𝒵`, the fibres of `f` being algebraic
stacks which may have negative dimension; this is illustrated by the morphism
`[Spec k/𝐆_m] ⟶ Spec k` for a field `k`. This file formalizes that example.

Let `𝒬` be (a model of) the classifying stack `[Spec k/𝐆_m]` and let `f : 𝒬 ⟶ Spec k` be its
structure morphism. Then `f` is quasi-compact and locally of finite type (indeed smooth), `𝒬` and
`Spec k` are Jacobson, pseudo-catenary and locally Noetherian, `|𝒬|` is irreducible (it is a
single point), `Spec k` is quasi-separated — so `f` satisfies every hypothesis of Stacks 0DS4 —
the scheme theoretic image of `f` is all of `Spec k`, of dimension `0`, and `dim 𝒬 = -1 < 0`; the
fibre dimension `dim_t(𝒬_{f(t)})` of Stacks 0DRL is `-1` at the point of `𝒬`.

## Main results

* `AlgebraicGeometry.Stack.classifyingStack_multiplicativeGroup_dimension_lt`: **Stacks 0DS5**,
  the example.

## Implementation notes

As everywhere in the library, the classifying stack — a stackification, whose morphisms are one
universe above those of `AlgebraicGeometry.Stack.AlgebraicStacks` — is read at a *model*: an
algebraic stack `𝒬` with an equivalence over the site to `[Spec k/𝐆_m]`. The statement asserts
that a model exists (`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`) and proves the claims
at every model. `𝐆_m` is the multiplicative group algebraic space of Stacks 043J over the final
algebraic space `Spec k`, and `Spec k` as an algebraic stack is the stack of the base scheme of
the site, the target of the structure morphism of Stacks 050D. The scheme theoretic image is the
property `⊤` of the objects of `Spec k`.

## References

* [Stacks Project, Tag 0AFR](https://stacks.math.columbia.edu/tag/0AFR)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRP](https://stacks.math.columbia.edu/tag/0DRP)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
* [Stacks Project, Tag 0DS5](https://stacks.math.columbia.edu/tag/0DS5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))

/-- The algebraic stack `Spec k` of the base scheme of the big fppf site of `Spec k`. -/
abbrev specFieldStack : AlgebraicStacks.{u, w} C (Spec (.of k)) hk :=
  schemeStack.{u, w} C (Spec (.of k)) hk (Over.mk (𝟙 (C.obj hk)))

/-- `Spec k` has a scheme atlas, its identity, with any property `Spec k` has. -/
theorem hasPropertyOnSomeSchemeAtlas_specFieldStack (P : Scheme.{u} → Prop)
    (hP : P (Spec (.of k))) :
    HasPropertyOnSomeSchemeAtlas C (Spec (.of k)) hk P (specFieldStack.{u, w} C hk) :=
  ⟨Over.mk (𝟙 (C.obj hk)), 𝟙 _, isSurjective_id C (Spec (.of k)) hk _,
    AlgebraicStacks.isSmooth_id C (Spec (.of k)) hk _, hP⟩

/-- `Spec k` has exactly one point. -/
theorem subsingleton_points_specFieldStack :
    Subsingleton (points C (Spec (.of k)) hk (specFieldStack.{u, w} C hk).val.val
      (specFieldStack.{u, w} C hk).val.property) := by
  have : Subsingleton (Space.points C (Spec (.of k)) hk
      (yoneda.obj (Over.mk (𝟙 (C.obj hk))))) :=
    inferInstanceAs (Subsingleton (Space.points C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj))
  exact (bijective_spacePointMap_representing C (Spec (.of k)) hk
    (yoneda.obj (Over.mk (𝟙 (C.obj hk)))) (specFieldStack.{u, w} C hk).val
    (PresheafOfCategories.sliceElementsEquivalenceOver _)).2.subsingleton

/-- `Spec k` has dimension `0` at its point. -/
theorem dimensionAtPoint_specFieldStack (h : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk
      (specFieldStack.{u, w} C hk))
    (y : points C (Spec (.of k)) hk (specFieldStack.{u, w} C hk).val.val
      (specFieldStack.{u, w} C hk).val.property) :
    dimensionAtPoint C (Spec (.of k)) hk (specFieldStack.{u, w} C hk) h y = 0 := by
  obtain ⟨x, hx⟩ := (bijective_spacePointMap_representing C (Spec (.of k)) hk
    (yoneda.obj (Over.mk (𝟙 (C.obj hk)))) (specFieldStack.{u, w} C hk).val
    (PresheafOfCategories.sliceElementsEquivalenceOver _)).2 y
  rw [dimensionAtPoint_eq_dimensionSubNat_zero_of_representing C (Spec (.of k)) hk _ h _
    (isAlgebraicSpace_yoneda C (Spec (.of k)) hk _)
    (PresheafOfCategories.sliceElementsEquivalenceOver _) x y hx,
    dimensionAtPoint_of_eq_terminalSpace C hk (F := yoneda.obj (Over.mk (𝟙 (C.obj hk))))
      (isAlgebraicSpace_yoneda C (Spec (.of k)) hk _) rfl x]
  rfl

/-- The full subcategory of all the objects of a category over `𝒮` is equivalent over `𝒮` to the
category. -/
def topEquivalenceOver (𝒳 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk) :
    StacksRepresentableCFG.EquivalenceOver (fullSubcategoryBased 𝒳 ⊤).p 𝒳.val.val.p where
  hom := ⟨ObjectProperty.ι ⊤, rfl⟩
  inv := ⟨ObjectProperty.lift ⊤ (𝟭 _) (fun _ => trivial), rfl⟩
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun f => by change f ≫ 𝟙 _ = 𝟙 _ ≫ f; simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun f => by change f ≫ 𝟙 _ = 𝟙 _ ≫ f; simp)
  unit_over := by
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    exact fun _ => IsHomLift.id rfl
  counit_over := by
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    exact fun _ => IsHomLift.id rfl

variable (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)

/-- The structure morphism of an algebraic stack over `Spec k` to `Spec k`. -/
abbrev toSpecFieldStack : 𝒬 ⟶ specFieldStack.{u, w} C hk := structureMorphism C (Spec (.of k)) hk 𝒬

/-- A morphism from an algebraic space equal to `Spec k` to the presheaf represented by `Spec k`
is an isomorphism, both being final. -/
theorem isIso_of_eq_terminalSpace {F : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (h : F = (Space.terminalSpace C (Spec (.of k)) hk).obj)
    (m : F ⟶ yoneda.obj (Over.mk (𝟙 (C.obj hk)))) : IsIso m := by
  subst h
  have ht := Space.baseTerminal_yonedaIsTerminal C (Spec (.of k)) hk
  exact ⟨⟨𝟙 _, ht.hom_ext _ _, ht.hom_ext _ _⟩⟩

/-- The structure morphism of the stack of an algebraic space equal to `Spec k` is smooth. -/
theorem isSmooth_toSpecFieldStack_of_eq_terminalSpace
    {F : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace C (Spec (.of k)) hk F)
    (h : F = (Space.terminalSpace C (Spec (.of k)) hk).obj) :
    AlgebraicStacks.IsSmooth C (Spec (.of k)) hk
      (toSpecFieldStack C hk (algebraicSpaceStack.{u, w} C (Spec (.of k)) hk F hF)) := by
  refine isSmooth_of_isSmooth_representingMap C (Spec (.of k)) hk F
    (yoneda.obj (Over.mk (𝟙 (C.obj hk)))) hF (isAlgebraicSpace_yoneda C (Spec (.of k)) hk _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver _) _ ?_
  have := isIso_of_eq_terminalSpace C hk h (representingMap C (Spec (.of k)) hk _ _ F
    (yoneda.obj (Over.mk (𝟙 (C.obj hk)))) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (toSpecFieldStack C hk (algebraicSpaceStack.{u, w} C (Spec (.of k)) hk F hF)).hom)
  exact Space.isSmooth_of_isIso C (Spec (.of k)) hk hF
    (isAlgebraicSpace_yoneda C (Spec (.of k)) hk _) _

variable (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property)
  (hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom)
  (e : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p 𝒬.val.val.p)

include hG e in
/-- **The classifying stack of a smooth group is smooth over `Spec k`** (Stacks 0DLS): smoothness
descends along its surjective, flat, locally finitely presented chart, the composite of the chart
with the structure morphism being the structure morphism of `Spec k`. -/
theorem isSmooth_toSpecFieldStack_classifyingModel :
    AlgebraicStacks.IsSmooth C (Spec (.of k)) hk (toSpecFieldStack C hk 𝒬) := by
  have hsm := isSmooth_classifyingGroupoid C hk G hG
  obtain ⟨hrep, hsurj, hflat, hlfp⟩ := quotientModelAtlasFppf (classifyingGroupoid C hk G) 𝒬 e
    (Space.isFlat_of_isSmooth C (Spec (.of k)) hk _ hsm.1)
    (Space.isFlat_of_isSmooth C (Spec (.of k)) hk _ hsm.2)
    (Space.isLocallyOfFinitePresentation_of_isSmooth C (Spec (.of k)) hk hsm.1)
    (Space.isLocallyOfFinitePresentation_of_isSmooth C (Spec (.of k)) hk hsm.2)
  refine AlgebraicStacks.isSmooth_of_comp_of_fppf C (Spec (.of k)) hk
    (classifyingChart C hk G 𝒬 e) _ ?_ hrep hsurj hflat hlfp
  rw [comp_structureMorphism]
  exact isSmooth_toSpecFieldStack_of_eq_terminalSpace C hk _
    (classifyingGroupoid_objects_obj C hk G)

include hG e in
/-- The structure morphism of the classifying stack of a smooth group is locally of finite
type. -/
theorem isLocallyOfFiniteType_toSpecFieldStack_classifyingModel :
    AlgebraicStacks.IsLocallyOfFiniteType C (Spec (.of k)) hk (toSpecFieldStack C hk 𝒬) :=
  AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth C (Spec (.of k)) hk _
    (isSmooth_toSpecFieldStack_classifyingModel C hk 𝒬 G hG e)

/-- An algebraic space equal to `Spec k` is quasi-compact. -/
theorem isQuasiCompactSpace_of_eq_terminalSpace {F : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (h : F = (Space.terminalSpace C (Spec (.of k)) hk).obj) :
    Space.IsQuasiCompactSpace C (Spec (.of k)) hk F := by
  subst h
  exact Space.isQuasiCompactSpace_yoneda_of_isAffine C (Spec (.of k)) hk _
    (inferInstanceAs (IsAffine (Spec (.of k))))

include hG e in
/-- **The structure morphism of the classifying stack of a smooth group is quasi-compact**: the
classifying stack is quasi-compact, being the image of the quasi-compact `Spec k`. -/
theorem isQuasiCompactMorphism_toSpecFieldStack_classifyingModel :
    IsQuasiCompactMorphism C (Spec (.of k)) hk (toSpecFieldStack C hk 𝒬) :=
  isQuasiCompactMorphism_structureMorphism C (Spec (.of k)) hk inferInstance 𝒬
    (isQuasiCompactStack_of_isSurjective C (Spec (.of k)) hk (classifyingChart C hk G 𝒬 e)
      (isQuasiCompactStack_fibredCategory C (Spec (.of k)) hk _
        (classifyingGroupoid C hk G).objects.property
        (isQuasiCompactSpace_of_eq_terminalSpace C hk (classifyingGroupoid_objects_obj C hk G))
        _)
      (isSurjective_classifyingChart C hk G 𝒬 e hG))

include hG e in
/-- **The scheme theoretic image of `BG ⟶ Spec k` is all of `Spec k`.** The whole of `Spec k` is a
closed substack, being the essential image of the identity, and a closed substack through which the
structure morphism factors contains the image of the point of `BG`, hence every point of `Spec k`,
so it is everything by Stacks 050A, `Spec k` being reduced. -/
theorem isSchemeTheoreticImage_toSpecFieldStack_classifyingModel :
    IsSchemeTheoreticImage (toSpecFieldStack C hk 𝒬) ⊤ := by
  have hclosed : IsClosedSubstack (specFieldStack.{u, w} C hk) ⊤ := by
    have h := AlgebraicStacks.isClosedSubstack_essImage (𝟙 (specFieldStack.{u, w} C hk))
      (isThickening_id_schemeStack.{u, w} C (Spec (.of k)) hk _).1
    have hess : (CatFiberedInGroupoids.homFunctor
        (𝟙 (specFieldStack.{u, w} C hk) :
          specFieldStack.{u, w} C hk ⟶ specFieldStack.{u, w} C hk).hom).essImage = ⊤ := by
      ext x
      exact iff_of_true ⟨x, ⟨Iso.refl _⟩⟩ trivial
    rwa [hess] at h
  have := hclosed.1
  refine ⟨hclosed, (factorsThroughSubstack_iff_forall _).2 fun _ => trivial,
    fun Q hQ hfac => ?_⟩
  have := subsingleton_points_specFieldStack.{u, w} C hk
  obtain ⟨x⟩ := nonempty_points_classifyingModel C hk G hG 𝒬 e
  obtain ⟨g, -⟩ := hfac
  have hsurj : IsSurjective C (Spec (.of k)) hk
      (fullSubcategoryInclusion (specFieldStack.{u, w} C hk) Q hQ.2.choose) := fun y =>
    ⟨pointsMap C (Spec (.of k)) hk 𝒬.val.val (Classical.choose 𝒬.property)
      (Classical.choose hQ.2.choose) g x, Subsingleton.elim _ _⟩
  rw [eq_top_of_isClosedSubstack_of_isReducedStack C (Spec (.of k)) hk Q hQ hsurj
    (hasPropertyOnSomeSchemeAtlas_specFieldStack C hk _ inferInstance)]

/-- **The whole of `Spec k`, as a closed substack of itself, has dimension `0`**: the full
subcategory of all objects is equivalent over the site to `Spec k`, so it is represented by the
algebraic space `Spec k`, of dimension `0` at its point. -/
theorem closedSubstackDimension_top_specFieldStack
    (hP : IsClosedSubstack (specFieldStack.{u, w} C hk) ⊤)
    (hA : IsAlgebraicStack.{u, w} C (Spec (.of k)) hk
      (fullSubcategoryBased (specFieldStack.{u, w} C hk) ⊤))
    (hX : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk (specFieldStack.{u, w} C hk)) :
    closedSubstackDimension C (Spec (.of k)) hk (specFieldStack.{u, w} C hk) ⊤ hP hA hX = 0 := by
  let 𝒵 := fullSubcategoryAlgebraicStack (specFieldStack.{u, w} C hk) ⊤ hA
  let h𝒵 := isLocallyNoetherianStack_of_isClosedSubstack C (Spec (.of k)) hk
    (specFieldStack.{u, w} C hk) ⊤ hP hA hX
  let eW : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
      (presheafOfCategories (yoneda.obj (Over.mk (𝟙 (C.obj hk))) ⋙ typeToCat)).p :=
    (topEquivalenceOver.{u, w} C hk (specFieldStack.{u, w} C hk)).trans
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
  have hb := (bijective_spacePointMap_representing C (Spec (.of k)) hk
    (yoneda.obj (Over.mk (𝟙 (C.obj hk)))) 𝒵.val eW).2
  have h0 : ∀ z, dimensionAtPoint C (Spec (.of k)) hk 𝒵 h𝒵 z = 0 := fun z => by
    obtain ⟨x, hx⟩ := hb z
    rw [dimensionAtPoint_eq_dimensionSubNat_zero_of_representing C (Spec (.of k)) hk 𝒵 h𝒵 _
      (isAlgebraicSpace_yoneda C (Spec (.of k)) hk _) eW x z hx,
      dimensionAtPoint_of_eq_terminalSpace C hk (F := yoneda.obj (Over.mk (𝟙 (C.obj hk))))
        (isAlgebraicSpace_yoneda C (Spec (.of k)) hk _) rfl x]
    rfl
  obtain ⟨x₀⟩ : Nonempty (Space.points C (Spec (.of k)) hk (yoneda.obj (Over.mk (𝟙 (C.obj hk))))) :=
    inferInstanceAs (Nonempty (Space.points C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj))
  let z₀ := spacePointMap C (Spec (.of k)) hk (yoneda.obj (Over.mk (𝟙 (C.obj hk)))) 𝒵.val
    (representingEquivalence C (Spec (.of k)) hk _ 𝒵.val eW).functor x₀
  exact le_antisymm (iSup_le fun z => (h0 z).le) ((h0 z₀).symm.le.trans (le_iSup
    (fun z => dimensionAtPoint C (Spec (.of k)) hk 𝒵 h𝒵 z) z₀))

include hG e in
/-- **The fibre of `BG ⟶ Spec k` has dimension `-dim G`** at the point of `BG`: by the dimension
formula Stacks 0DRP for the smooth structure morphism, `dim BG = dim Spec k + dim_t(BG_{f(t)})`,
that is `-n = 0 + dim_t(BG_{f(t)})`. -/
theorem relativeStackDimensionAt_toSpecFieldStack_classifyingModel (n : ℕ)
    (hn : Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (n : WithBot ℕ∞))
    (hX : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk (specFieldStack.{u, w} C hk))
    (t : points C (Spec (.of k)) hk 𝒬.val.val 𝒬.val.property) :
    relativeStackDimensionAt.{u, w} C (Spec (.of k)) hk (toSpecFieldStack C hk 𝒬)
        (isLocallyOfFiniteType_toSpecFieldStack_classifyingModel C hk 𝒬 G hG e)
        (isLocallyNoetherianStack_classifyingModel C hk G hG 𝒬 e) hX t =
      ((-(n : ℤ) : ℤ) : EInt) := by
  have h := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth.{u, w} C (Spec (.of k)) hk
    (toSpecFieldStack C hk 𝒬) (isSmooth_toSpecFieldStack_classifyingModel C hk 𝒬 G hG e)
    (isLocallyOfFiniteType_toSpecFieldStack_classifyingModel C hk 𝒬 G hG e)
    (isLocallyNoetherianStack_classifyingModel C hk G hG 𝒬 e) hX t
  rw [dimensionAtPoint_classifyingModel C hk G hG 𝒬 e n hn, dimensionAtPoint_specFieldStack,
    zero_add] at h
  exact h.symm

/-- The multiplicative group `𝐆_m` over a field `k` (Stacks 043J), as a group algebraic space over
the algebraic space `Spec k`. -/
abbrev multiplicativeGroupOverField : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property :=
  Space.multiplicativeGroupSpace C (Spec (.of k)) hk (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property

/-- **Stacks 0DS5**, the example `[Spec k/𝐆_m] ⟶ Spec k`. Let `k` be a field. The classifying
stack `[Spec k/𝐆_m]` is an algebraic stack, of which a model `𝒬` in the 2-category of algebraic
stacks over `Spec k` exists; and for every such model, the structure morphism `f : 𝒬 ⟶ Spec k`
satisfies the hypotheses of Stacks 0DS4 — it is quasi-compact and locally of finite type, `𝒬` and
`Spec k` are Jacobson, pseudo-catenary and locally Noetherian, `|𝒬|` is irreducible and `Spec k` is
quasi-separated — its scheme theoretic image is all of `Spec k`, of dimension `0`, while
`dim 𝒬 = -1`, so that `dim 𝒬 < dim 𝒵`; and the fibre dimension `dim_t(𝒬_{f(t)})` of Stacks 0DRL is
`-1 < 0` at every point `t` of `𝒬`. -/
@[stacks 0DS5 "the example [Spec k/G_m] → Spec k: it need not be that dim T ≥ dim Z, the fibres \
having negative dimension"]
theorem classifyingStack_multiplicativeGroup_dimension_lt :
    IsAlgebraicStack.{u, w} C (Spec (.of k)) hk
        (classifyingStack C hk (multiplicativeGroupOverField C hk)).val ∧
      (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk, Nonempty
        (StacksRepresentableCFG.EquivalenceOver
          (classifyingStack C hk (multiplicativeGroupOverField C hk)).val.p 𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_e : StacksRepresentableCFG.EquivalenceOver
          (classifyingStack C hk (multiplicativeGroupOverField C hk)).val.p 𝒬.val.val.p),
        ∃ (h𝒯 : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬)
          (h𝒳 : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk (specFieldStack.{u, w} C hk))
          (hf : AlgebraicStacks.IsLocallyOfFiniteType C (Spec (.of k)) hk (toSpecFieldStack C hk 𝒬))
          (hP : IsSchemeTheoreticImage (toSpecFieldStack C hk 𝒬) ⊤),
          IsQuasiCompactMorphism C (Spec (.of k)) hk (toSpecFieldStack C hk 𝒬) ∧
          AlgebraicStacks.IsJacobson C (Spec (.of k)) hk 𝒬 ∧
          AlgebraicStacks.IsJacobson C (Spec (.of k)) hk (specFieldStack.{u, w} C hk) ∧
          AlgebraicStacks.IsPseudoCatenary C (Spec (.of k)) hk 𝒬 ∧
          AlgebraicStacks.IsPseudoCatenary C (Spec (.of k)) hk (specFieldStack.{u, w} C hk) ∧
          @IrreducibleSpace _ (pointTopology C (Spec (.of k)) hk 𝒬.val) ∧
          IsQuasiSeparatedAbs.{u, w, w} C (Spec (.of k)) hk (specFieldStack.{u, w} C hk) ∧
          closedSubstackDimension C (Spec (.of k)) hk (specFieldStack.{u, w} C hk) ⊤ hP.1
            hP.isAlgebraicStack h𝒳 = 0 ∧
          dimension C (Spec (.of k)) hk 𝒬 h𝒯 = ((-1 : ℤ) : EInt) ∧
          dimension C (Spec (.of k)) hk 𝒬 h𝒯 <
            closedSubstackDimension C (Spec (.of k)) hk (specFieldStack.{u, w} C hk) ⊤ hP.1
              hP.isAlgebraicStack h𝒳 ∧
          ∀ t : points C (Spec (.of k)) hk 𝒬.val.val 𝒬.val.property,
            relativeStackDimensionAt.{u, w} C (Spec (.of k)) hk (toSpecFieldStack C hk 𝒬) hf h𝒯
                h𝒳 t =
              ((-1 : ℤ) : EInt) := by
  let G := multiplicativeGroupOverField C hk
  have hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom :=
    Space.isSmooth_multiplicativeGroupSpace C (Spec (.of k)) hk _
  have hn : Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = ((1 : ℕ) : WithBot ℕ∞) :=
    Space.dimension_multiplicativeGroupSpace_terminalSpace C hk
  have hBG := isAlgebraicStack_classifyingStack.{u, w} C hk G hG
  refine ⟨hBG, ⟨AlgebraicStacks.smallModel C (Spec (.of k)) hk _ hBG,
    ⟨AlgebraicStacks.smallModelEquivalenceOver C (Spec (.of k)) hk _ hBG⟩⟩, fun 𝒬 e => ?_⟩
  have h𝒳 : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk (specFieldStack.{u, w} C hk) :=
    hasPropertyOnSomeSchemeAtlas_specFieldStack C hk _ inferInstance
  have hP := isSchemeTheoreticImage_toSpecFieldStack_classifyingModel C hk 𝒬 G hG e
  have hZ := closedSubstackDimension_top_specFieldStack.{u, w} C hk hP.1 hP.isAlgebraicStack h𝒳
  have hdim :
      dimension C (Spec (.of k)) hk 𝒬 (isLocallyNoetherianStack_classifyingModel C hk G hG 𝒬 e) =
      ((-1 : ℤ) : EInt) :=
    dimension_classifyingModel C hk G hG 𝒬 e 1 hn
  refine ⟨isLocallyNoetherianStack_classifyingModel C hk G hG 𝒬 e, h𝒳,
    isLocallyOfFiniteType_toSpecFieldStack_classifyingModel C hk 𝒬 G hG e, hP,
    isQuasiCompactMorphism_toSpecFieldStack_classifyingModel C hk 𝒬 G hG e,
    isJacobson_classifyingModel C hk G hG 𝒬 e,
    hasPropertyOnSomeSchemeAtlas_specFieldStack C hk _ inferInstance,
    isPseudoCatenary_classifyingModel C hk G hG 𝒬 e,
    hasPropertyOnSomeSchemeAtlas_specFieldStack C hk _
      ⟨inferInstance, Scheme.isUniversallyCatenary_spec_of_field k⟩, ?_,
    isQuasiSeparatedAbs_schemeStack_base.{u, w, w} C (Spec (.of k)) hk, hZ, hdim, ?_, fun t =>
      relativeStackDimensionAt_toSpecFieldStack_classifyingModel C hk 𝒬 G hG e 1 hn h𝒳 t⟩
  · let := pointTopology C (Spec (.of k)) hk 𝒬.val
    have := nonempty_points_classifyingModel C hk G hG 𝒬 e
    have := subsingleton_points_classifyingModel C hk G hG 𝒬 e
    exact { isPreirreducible_univ := Set.subsingleton_univ.isPreirreducible
            toNonempty := inferInstance }
  · rw [hdim, hZ, show (0 : EInt) = ((0 : ℤ) : EInt) from rfl, WithBotTop.coe_lt_coe]
    omega

end AlgebraicGeometry.Stack

end
