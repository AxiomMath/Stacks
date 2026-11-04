module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategorySite
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Reading a 1-morphism of algebraic stacks on representing algebraic spaces and schemes

The atlas criteria of **Stacks 04YF** compare a property of schemes along smooth surjective
1-morphisms of algebraic stacks, and every step of that comparison passes between three levels:
a 1-morphism of algebraic stacks, the morphism of algebraic spaces it induces when source and
target are representable, and the morphism of schemes underlying that when the representing
algebraic spaces are themselves representable. This module records the transports between those
levels, and the two descent statements for a smooth-local property of schemes.

* Smoothness (**Stacks 075U**) and surjectivity (**Stacks 04ZS**) of a 1-morphism of algebraic
  stacks are smoothness (**Stacks 03ZC**) and surjectivity (**Stacks 03ME**) of the induced
  morphism of representing presheaves.
* Smoothness and surjectivity of `yoneda.map g` for a morphism `g` of the big fppf category of
  `S` are smoothness and surjectivity of the underlying morphism of schemes.
* A property of schemes local in the smooth topology (**Stacks 0348**) passes down a smooth
  morphism and up a smooth surjective one.

It also records that every algebraic stack carries a smooth surjective 1-morphism from the
algebraic stack of a scheme over `S`, which is the fourth clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` read through Stacks 06FM and Stacks 04XI.

## Main results

* `AlgebraicGeometry.Space.smooth_of_isSmooth_yonedaMap` and
  `AlgebraicGeometry.Space.surjective_of_isSurjective_yonedaMap`: the scheme level.
* `AlgebraicGeometry.Stack.isSmooth_representingMap_of_isSmooth` and
  `AlgebraicGeometry.Stack.isSurjective_representingMap_of_isSurjective`: the algebraic-space
  level.
* `AlgebraicGeometry.Space.exists_smoothPullback`: the base change of a smooth surjective
  morphism of algebraic spaces along a smooth one.
* `AlgebraicGeometry.Stack.isRelativelySmooth_associatedMap` and
  `AlgebraicGeometry.Stack.isSurjectiveOnObjects_associatedMap`: the 1-morphism attached to a
  morphism of algebraic spaces inherits its smoothness and its surjectivity.
* `AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack`: the scheme presentation.
* `AlgebraicGeometry.prop_of_smooth` and `AlgebraicGeometry.prop_of_smooth_surjective`: descent
  of a smooth-local property of schemes.

## References

* [Stacks Project, Tag 0348](https://stacks.math.columbia.edu/tag/0348)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

/-! ### Descent of a smooth-local property of schemes -/

section Descent

variable (P : ObjectProperty Scheme.{u})
  [P.IsLocal (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]

/-- **Stacks 0348, downwards.** A property of schemes local in the smooth topology holds on the
source of a smooth morphism whose target has it. -/
theorem prop_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Smooth f) (hY : P Y) : P X := by
  let Z : Bool → Scheme.{u} := fun b => if b then Y else X
  let g : ∀ b, Z b ⟶ Y := fun b => by
    cases b
    · exact f
    · exact 𝟙 Y
  have hR : Presieve.ofArrows Z g ∈
      Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) Y := by
    refine (Scheme.ofArrows_mem_precoverage_iff (@Smooth : MorphismProperty Scheme.{u})).2
      ⟨fun y => ⟨true, by simp [Z, g]⟩, fun b => ?_⟩
    cases b
    · simpa [Z, g] using hf
    · dsimp [Z, g]
      infer_instance
  exact ObjectProperty.IsLocal.component hR f ⟨false⟩ hY

/-- **Stacks 0348, upwards.** A property of schemes local in the smooth topology holds on the
target of a smooth surjective morphism whose source has it. -/
theorem prop_of_smooth_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Smooth f)
    (hsurj : Function.Surjective f.base) (hX : P X) : P Y := by
  refine ObjectProperty.IsLocal.of_presieve
    ((Scheme.singleton_mem_precoverage_iff (@Smooth : MorphismProperty Scheme.{u}) f).2
      ⟨hsurj, hf⟩) fun _ _ hg => ?_
  cases hg
  exact hX

end Descent

/-! ### The scheme level -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Smoothness of a morphism of representable algebraic spaces is smoothness of the morphism
of schemes.** -/
theorem smooth_of_isSmooth_yonedaMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : IsSmooth B S hS (yoneda.map g)) :
    Smooth ((BigFppfOver.toScheme B S hS).map g) :=
  hg U V (yoneda.map (𝟙 U)) (yoneda.map (𝟙 V)) g
    ((presheaf_yoneda_map_etale_iff B S hS (𝟙 U)).2
      (by simpa using inferInstanceAs (Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj U)))))
    ((presheaf_yoneda_map_etale_iff B S hS (𝟙 V)).2
      (by simpa using inferInstanceAs (Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj V)))))
    (by simp)

/-- **Surjectivity on points of a morphism of representable algebraic spaces is surjectivity of
the morphism of schemes.** -/
theorem surjective_of_isSurjective_yonedaMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : IsSurjective B S hS (yoneda.map g)) :
    Function.Surjective ((BigFppfOver.toScheme B S hS).map g).base := by
  intro v
  obtain ⟨x, hx⟩ := hg ((pointsEquivScheme B S hS V).symm v)
  exact ⟨pointsToScheme B S hS U x, (pointsToScheme_pointsMap B S hS g x).symm.trans
    ((congrArg (pointsToScheme B S hS V) hx).trans
      ((pointsEquivScheme B S hS V).apply_symm_apply v))⟩

/-- **The fibre product of a smooth morphism and a smooth surjective one**, with the two
projections. Both projections are smooth and the one onto the source of the smooth morphism is
in addition surjective. -/
theorem exists_smoothPullback
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (φ : F ⟶ G) (u : H ⟶ G)
    (hφ : IsSmooth B S hS φ) (hu : IsSmooth B S hS u) (huSurj : IsSurjective B S hS u) :
    ∃ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS T)
      (t₁ : T ⟶ F) (t₂ : T ⟶ H),
      IsSmooth B S hS t₁ ∧ IsSurjective B S hS t₁ ∧ IsSmooth B S hS t₂ ∧
        t₁ ≫ φ = t₂ ≫ u := by
  have hsq := AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk φ : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
    (ObjectProperty.homMk u : (⟨H, hH⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
  refine ⟨Limits.pullback φ u, isAlgebraicSpace_pullback B S hS φ u hF hH hG,
    Limits.pullback.fst φ u, Limits.pullback.snd φ u, ?_, ?_, ?_, Limits.pullback.condition⟩
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := smoothMorphismProperty B S hS) hsq.flip hu
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := surjectiveMorphismProperty B S hS) hsq.flip huSurj
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := smoothMorphismProperty B S hS) hsq hφ

end Space

/-! ### The algebraic-space level -/

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth 1-morphism of algebraic stacks representable by algebraic spaces induces a smooth
morphism of those algebraic spaces.** This is the forward half of Stacks 06FM for representable
source and target, at smoothness of morphisms of algebraic spaces; the hypothesis `hsm` is
Stacks 06FC at the smooth case. -/
theorem isSmooth_representingMap_of_isSmooth
    (hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ k => Space.IsSmooth B S hS k))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsSmooth B S hS f) :
    Space.IsSmooth B S hS (representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom) :=
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _ hsm
    𝒳.property 𝒴.property F G hF hG eF eG f.hom).mp hf

/-- **A surjective 1-morphism of algebraic stacks representable by algebraic spaces induces a
surjective morphism of those algebraic spaces.** -/
theorem isSurjective_representingMap_of_isSurjective
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴) (hf : IsSurjective B S hS f) :
    Space.IsSurjective B S hS (representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom) :=
  isSurjective_representingMap_of_isSurjectiveOnObjects B S hS f.hom F G eF eG
    (isSurjectiveOnObjects_of_pointsMap_surjective B S hS f hf)

/-- **Every algebraic stack over `S` has a smooth surjective presentation by a scheme over `S`,
read as a 1-morphism of the 2-category of algebraic stacks**, smooth in the sense of Stacks 075U
and surjective in the sense of Stacks 04ZS. -/
theorem exists_smooth_surjective_schemeStack (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ∃ (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳),
      AlgebraicStacks.IsSmooth B S hS a ∧ IsSurjective B S hS a := by
  obtain ⟨hfib, hstack, hdiag, U, a, hrep, ha⟩ := 𝒳.property
  refine ⟨U, Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom a), ?_, ?_⟩
  · exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hrep
      (fun V y hy G hG he => (ha V y hy G hG he).2)
  · exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS _ hrep).mpr
      (fun V y hy G hG he => (ha V y hy G hG he).1)

/-- The 1-morphism attached to a morphism of algebraic spaces is representable by algebraic
spaces. -/
private theorem isRepresentableByAlgebraicSpaces_associatedMap
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (h : F ⟶ G) :
    IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS h).1.hom :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    (associatedMap B S hS h).1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS G hG)

/-- **The 1-morphism attached to a smooth morphism of algebraic spaces is smooth** in the sense
of Stacks 04XB. -/
theorem isRelativelySmooth_associatedMap
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (h : F ⟶ G) (hh : Space.IsSmooth B S hS h) :
    IsRelativelySmooth B S hS (associatedMap B S hS h).1 := by
  have hrep := isRepresentableByAlgebraicSpaces_associatedMap B S hS hF hG h
  refine (isRelativelySmooth_iff_isSmooth_representingMap B S hS
    (associatedMap B S hS h).1 hrep F G hF hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)).2 ?_
  rw [representingMap_associatedMap B S hS F G h]
  exact hh

/-- **The 1-morphism attached to a surjective morphism of algebraic spaces is surjective on
objects** in the sense of Stacks 06D4. -/
theorem isSurjectiveOnObjects_associatedMap
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (h : F ⟶ G) (hh : Space.IsSurjective B S hS h) :
    IsSurjectiveOnObjects B S hS (fibredCategory B S hS F).val.p
      (fibredCategory B S hS G).val.p
      (CatFiberedInGroupoids.homFunctor (associatedMap B S hS h).1) := by
  have hrep := isRepresentableByAlgebraicSpaces_associatedMap B S hS hF hG h
  refine (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS
    (associatedMap B S hS h).1 hrep).2 ?_
  refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.surjectiveMorphismProperty B S hS)
    (associatedMap B S hS h).1 hrep F G hF hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)).2 ?_
  rw [representingMap_associatedMap B S hS F G h]
  exact hh

end Stack

end AlgebraicGeometry

end
