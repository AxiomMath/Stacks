module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsPoints
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct

/-!
# The existential smooth-diagram criterion implies the universal one

Let `P` be a property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the
big fppf site of `S`. If one diagram of algebraic spaces over `f` with smooth vertical
1-morphisms, the left one surjective on objects, has `P` on its top horizontal morphism, then
*every* such diagram whose comparison to the 2-fibre product is smooth has `P` on its top
horizontal morphism: condition (2) of [Stacks, Tag 06FM] implies condition (1).

## Main results

* `AlgebraicGeometry.Space.prop_of_smooth_surjective_square`: criterion (3) of Stacks 06FA, as an
  implication.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_twoFibreProductSnd` and
  `AlgebraicGeometry.Stack.isRelativelySmooth_twoFibreProductSnd`: representability by algebraic
  spaces and smoothness pass to the second projection of a 2-fibre product.
* `AlgebraicGeometry.Stack.isIso_representingMap_preHom_of_isTwoFibreProduct`: the comparison of
  two 2-fibre products of one cospan induces an isomorphism of representing presheaves.
* `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram`:
  condition (2) of Stacks 06FM implies condition (1).
* `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some`: the equivalence of
  conditions (1) and (2) of Stacks 06FM.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06D5](https://stacks.math.columbia.edu/tag/06D5)
* [Stacks Project, Tag 06FA](https://stacks.math.columbia.edu/tag/06FA)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Criterion (3) of Stacks 06FA, as an implication -/

/-- A property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target holds for `g : X ⟶ Y` as soon as there is one commuting square over `g` with
smooth vertical morphisms, the one over the source surjective, whose top horizontal morphism has
the property. -/
theorem Space.prop_of_smooth_surjective_square
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (g : X ⟶ Y)
    {U₀ V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU₀ : IsAlgebraicSpace B S hS U₀) (hV₀ : IsAlgebraicSpace B S hS V₀)
    (a₀ : U₀ ⟶ X) (b₀ : V₀ ⟶ Y) (h₀ : U₀ ⟶ V₀)
    (ha₀ : Space.IsSmooth B S hS a₀) (ha₀surj : Space.IsSurjective B S hS a₀)
    (hb₀ : Space.IsSmooth B S hS b₀) (hcomm : h₀ ≫ b₀ = a₀ ≫ g) (hPh₀ : P h₀) : P g := by
  have h3 := (Space.smoothLocalOnSourceAndTarget_tfae.{u, u, u} B S hS P hP hX hY g).out 3 1
  exact h3.1 ⟨U₀, V₀, hU₀, hV₀, a₀, b₀, h₀, ha₀, ha₀surj, hb₀, hcomm, hPh₀⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The second projection of a 2-fibre product square -/

/-- The second projection of the canonical 2-fibre product square over a cospan `(g, f)` and the
first projection of the canonical square over the exchanged cospan `(f, g)` have equivalent base
changes along every scheme-valued point of their common target. -/
theorem nonempty_equivalenceOver_twoFibreProductSnd
    {𝒵 𝒴 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) :
    ∀ (W : BigFppfOver B S hS)
      (y : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.obj), y ⋙ 𝒳.val.p = Over.map W.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map W.hom)
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt.val.p
          𝒳.val.p y
          (CatFiberedInGroupoids.homFunctor
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd))
        (TwoFibreProductOver.fst (Over.map W.hom)
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt.val.p
          𝒳.val.p y
          (CatFiberedInGroupoids.homFunctor
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst))) := by
  have hsw : Functor.IsEquivalence (twoFibreProductSwapMap B S hS f g).hom.toFunctor := by
    change Functor.IsEquivalence (TwoFibreProductOver.swap _ _ _ _ _)
    infer_instance
  exact fun W y hy => nonempty_equivalenceOver_fst_of_equivalence_source B S hS
    (twoFibreProductSwapMap B S hS f g).hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst.hom W y hy

/-- The second projection of the canonical 2-fibre product square over a cospan `(g, f)` is
representable by algebraic spaces as soon as `g` is. -/
theorem isRepresentableByAlgebraicSpaces_twoFibreProductSnd
    {𝒵 𝒴 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom) :
    IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd.hom :=
  isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst
    (nonempty_equivalenceOver_twoFibreProductSnd B S hS g f)
    (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒵 𝒴 𝒳 g f
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g) hg)

/-- The second projection of the canonical 2-fibre product square over a cospan `(g, f)` is smooth
as soon as `g` is. -/
theorem isRelativelySmooth_twoFibreProductSnd
    {𝒵 𝒴 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (hg : IsRelativelySmooth B S hS g) :
    IsRelativelySmooth B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd :=
  ⟨isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS g f hg.1,
    relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
      (Space.smoothMorphismProperty B S hS)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd
      (nonempty_equivalenceOver_twoFibreProductSnd B S hS g f)
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.smoothMorphismProperty B S hS) 𝒵 𝒴 𝒳 g f
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
        hg.1 hg.2)⟩

/-! ### Comparing two 2-fibre products of one cospan at the level of representing presheaves -/

/-- The comparison of two 2-fibre products of one cospan induces an isomorphism of representing
presheaves. -/
theorem isIso_representingMap_preHom_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {Q₁ Q₂ : Bicategory.TwoCommSq g f}
    (hQ₁ : Bicategory.IsTwoFibreProduct Q₁) (hQ₂ : Bicategory.IsTwoFibreProduct Q₂)
    (m : Bicategory.TwoCommSq.PreHom Q₁ Q₂)
    (F₁ F₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (e₁ : StacksRepresentableCFG.EquivalenceOver Q₁.pt.val.p
      (presheafOfCategories (F₁ ⋙ typeToCat)).p)
    (e₂ : StacksRepresentableCFG.EquivalenceOver Q₂.pt.val.p
      (presheafOfCategories (F₂ ⋙ typeToCat)).p) :
    IsIso (representingMap B S hS Q₁.pt Q₂.pt F₁ F₂ e₁ e₂ m.hom) := by
  classical
  let n := Quotient.out (hQ₁.from Q₂)
  obtain ⟨ψ₁, -, -⟩ : Bicategory.TwoCommSq.PreHom.Rel (m.comp n)
      (Bicategory.TwoCommSq.PreHom.id Q₁) :=
    Quotient.exact (hQ₁.hom_ext (Quotient.mk _ (m.comp n)) (𝟙 Q₁))
  obtain ⟨ψ₂, -, -⟩ : Bicategory.TwoCommSq.PreHom.Rel (n.comp m)
      (Bicategory.TwoCommSq.PreHom.id Q₂) :=
    Quotient.exact (hQ₂.hom_ext (Quotient.mk _ (n.comp m)) (𝟙 Q₂))
  refine ⟨representingMap B S hS Q₂.pt Q₁.pt F₂ F₁ e₂ e₁ n.hom, ?_, ?_⟩
  · rw [← representingMap_comp B S hS F₁ F₂ F₁ e₁ e₂ e₁ m.hom n.hom]
    exact (representingMap_congr_twoIso B S hS F₁ F₁ e₁ e₁ ψ₁).trans
      (representingMap_id B S hS Q₁.pt F₁ e₁)
  · rw [← representingMap_comp B S hS F₂ F₁ F₂ e₂ e₁ e₂ n.hom m.hom]
    exact (representingMap_congr_twoIso B S hS F₂ F₂ e₂ e₂ ψ₂).trans
      (representingMap_id B S hS Q₂.pt F₂ e₂)

/-- A relatively smooth 1-morphism between categories fibred in groupoids represented by algebraic
spaces induces a smooth morphism of the representing presheaves. -/
private theorem isSmooth_representingMap_of_isRelativelySmooth
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {a : 𝒜 ⟶ 𝒞} (ha : IsRelativelySmooth B S hS a) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    Space.IsSmooth B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) :=
  (isRelativelySmooth_iff_isSmooth_representingMap B S hS a ha.1 F G hF hG eF eG).1 ha

/-! ### Criterion (4) of Stacks 06FA at a base change of the top horizontal morphism -/

/-- Let `h : U ⟶ V` have `P`, let `s : 𝒮 ⟶ V` be a smooth 1-morphism out of a category fibred in
groupoids represented by an algebraic space, and form the canonical 2-fibre product `𝒮 ×_V U`. Then
every smooth morphism of algebraic spaces into the representing presheaf of that 2-fibre product,
composed with the morphism induced by its projection to `𝒮`, has `P`. -/
theorem prop_representingMap_twoFibreProductFst_comp
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (hTop : U ⟶ V) (hPtop : P hTop)
    {𝒮 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (s : 𝒮 ⟶ fibredCategory B S hS V) (hs : IsRelativelySmooth B S hS s)
    (W₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW₃ : IsAlgebraicSpace B S hS W₃)
    (eW₃ : StacksRepresentableCFG.EquivalenceOver 𝒮.val.p
      (presheafOfCategories (W₃ ⋙ typeToCat)).p)
    (W₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW₂ : IsAlgebraicSpace B S hS W₂)
    (eW₂ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒮 (fibredCategory B S hS U)
        (fibredCategory B S hS V) s (associatedMap B S hS hTop).1)
      (presheafOfCategories (W₂ ⋙ typeToCat)).p)
    {WE : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hWE : IsAlgebraicSpace B S hS WE)
    (q : WE ⟶ W₂) (hq : Space.IsSmooth B S hS q) :
    P (q ≫ representingMap B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
        (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
        (associatedMap B S hS hTop).1).fst) := by
  classical
  let β := representingMap B S hS 𝒮 (fibredCategory B S hS V) W₃ V eW₃
    (StacksRepresentableCFG.EquivalenceOver.refl _) s
  let hTopR := representingMap B S hS (fibredCategory B S hS U) (fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS hTop).1
  have hrepTop : hTopR = hTop := representingMap_associatedMap B S hS U V hTop
  have hPtopR : P hTopR := by rwa [hrepTop]
  let _hfibered : (twoFibreProductStructureFunctor B S hS 𝒮 (fibredCategory B S hS U)
      (fibredCategory B S hS V) s (associatedMap B S hS hTop).1).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
      (associatedMap B S hS hTop).1).pt.property.isFibered
  let hfib : Presheaf.fibreProduct β hTopR ≅ W₂ :=
    fibreProductIsoRepresenting B S hS 𝒮 (fibredCategory B S hS U) (fibredCategory B S hS V)
      W₃ U V eW₃ (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) s (associatedMap B S hS hTop).1 W₂ eW₂
  have hfst : hfib.hom ≫ representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).fst =
      Presheaf.fibreProductFst β hTopR :=
    fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS 𝒮
      (fibredCategory B S hS U) (fibredCategory B S hS V) W₃ U V eW₃
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) s (associatedMap B S hS hTop).1 W₂ eW₂
  have hpbalg : IsAlgebraicSpace B S hS (pullback hTopR β) :=
    isAlgebraicSpace_pullback B S hS hTopR β hU hW₃ hV
  let ι := hfib.symm ≪≫ (Presheaf.isPullback_fibreProduct β hTopR).flip.isoPullback
  have hιsnd : ι.hom ≫ pullback.snd hTopR β =
      representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).fst := by
    have hιhom : ι.hom =
        hfib.inv ≫ (Presheaf.isPullback_fibreProduct β hTopR).flip.isoPullback.hom := rfl
    rw [hιhom, Category.assoc,
      (Presheaf.isPullback_fibreProduct β hTopR).flip.isoPullback_hom_snd, ← hfst,
      Iso.inv_hom_id_assoc]
  have hβsm : Space.IsSmooth B S hS β :=
    isSmooth_representingMap_of_isRelativelySmooth B S hS hs hW₃ hV eW₃ _
  have hqιsm : Space.IsSmooth B S hS (q ≫ ι.hom) :=
    Space.isSmooth_comp B S hS hWE hW₂ hpbalg q ι.hom hq
      (Space.isSmooth_of_isIso B S hS hW₂ hpbalg ι.hom)
  have h4 := ((Space.smoothLocalOnSourceAndTarget_tfae.{u, u, u} B S hS P hP hU hV
    hTopR).out 1 4).1 hPtopR
  exact ((Category.assoc q ι.hom (pullback.snd hTopR β)).trans
    (congrArg (fun t => q ≫ t) hιsnd)) ▸ h4 WE W₃ hWE hW₃ β (q ≫ ι.hom) hβsm hqιsm

/-! ### The implication, and the equivalence of conditions (1) and (2) of Stacks 06FM -/

/-- Condition (2) of Stacks 06FM implies condition (1): if some diagram of algebraic spaces over
`f : 𝒳 ⟶ 𝒴` with smooth vertical 1-morphisms and left vertical 1-morphism surjective on objects has
`P` on its top horizontal morphism, then every diagram with smooth vertical 1-morphisms whose
comparison to a 2-fibre product is smooth has `P` on its top horizontal morphism. -/
theorem hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hsome : HasPropertyOnSomeSmoothDiagram B S hS P f) :
    HasPropertyOnEverySmoothDiagram B S hS P f := by
  classical
  obtain ⟨U, V, hU, hV, a, b, hTop, ⟨η⟩, hasm, hasu, hbsm, hPtop⟩ := hsome
  intro U' V' hU' hV' a' b' h' η' ha'sm hb'sm hcomp
  have hUrep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS U) :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU
  have hVrep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS V) :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV
  have hU'rep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS U') :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS U' hU'
  have hV'rep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS V') :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS V' hV'
  let 𝒦 := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' f
  have h𝒦 : Bicategory.IsTwoFibreProduct 𝒦 :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b' f
  let k := Quotient.out (h𝒦.from (diagramCone B S hS f a' b' h' η'))
  have hksm : IsRelativelySmooth B S hS k.hom := hcomp 𝒦 h𝒦 k
  let T₁ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} 𝒦.snd a
  have hT₁ : Bicategory.IsTwoFibreProduct T₁ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} 𝒦.snd a
  let Sq₃ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' b
  have hSq₃ : Bicategory.IsTwoFibreProduct Sq₃ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b' b
  let T₂ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Sq₃.snd
    (associatedMap B S hS hTop).1
  let E := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} T₁.fst k.hom
  have hE : Bicategory.IsTwoFibreProduct E :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} T₁.fst
      k.hom
  have h𝒦sndrep : IsRepresentableByAlgebraicSpaces B S hS 𝒦.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS b' f hb'sm.1
  have hT₁sndrep : IsRepresentableByAlgebraicSpaces B S hS T₁.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS 𝒦.snd a h𝒦sndrep
  have hT₁rep : IsRepresentableByAlgebraicSpace B S hS T₁.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS T₁.pt
      (fibredCategory B S hS U) T₁.snd hT₁sndrep hUrep
  have hSq₃rep : IsRepresentableByAlgebraicSpace B S hS Sq₃.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS V) 𝒴 (fibredCategory B S hS V') b b' Sq₃ hSq₃ hbsm.1 hV'rep
  have hT₁fstrep : IsRepresentableByAlgebraicSpaces B S hS T₁.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS U) 𝒳 𝒦.pt a 𝒦.snd T₁ hT₁ hasm.1
  have hT₁fstsm : IsRelativelySmooth B S hS T₁.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS U) 𝒳 𝒦.pt a 𝒦.snd T₁ hT₁ hasm
  have hT₁fstsu : IsSurjectiveOnObjects B S hS T₁.pt.val.p 𝒦.pt.val.p
      (CatFiberedInGroupoids.homFunctor T₁.fst) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS T₁.fst
      hT₁fstrep).2
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS U) 𝒳 𝒦.pt a 𝒦.snd
        T₁ hT₁ hasm.1
        ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS a
          hasm.1).1 hasu))
  have hSq₃fstsm : IsRelativelySmooth B S hS Sq₃.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS V) 𝒴 (fibredCategory B S hS V') b b' Sq₃ hSq₃ hbsm
  have hSq₃sndsm : IsRelativelySmooth B S hS Sq₃.snd :=
    isRelativelySmooth_twoFibreProductSnd B S hS b' b hb'sm
  have hTopMorrep : IsRepresentableByAlgebraicSpaces B S hS
      ((associatedMap B S hS hTop).1 :
        fibredCategory B S hS U ⟶ fibredCategory B S hS V).hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (associatedMap B S hS hTop).1 hUrep hVrep
  have hT₂ : Bicategory.IsTwoFibreProduct T₂ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      Sq₃.snd (associatedMap B S hS hTop).1
  have hT₂rep : IsRepresentableByAlgebraicSpace B S hS T₂.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS U) (fibredCategory B S hS V) Sq₃.pt
      (associatedMap B S hS hTop).1 Sq₃.snd T₂ hT₂ hTopMorrep hSq₃rep
  have hEfstsm : IsRelativelySmooth B S hS E.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS U') 𝒦.pt T₁.pt k.hom T₁.fst E hE hksm
  have hEsndsm : IsRelativelySmooth B S hS E.snd :=
    isRelativelySmooth_twoFibreProductSnd B S hS T₁.fst k.hom hT₁fstsm
  have hEsndsu : IsSurjectiveOnObjects B S hS E.pt.val.p (fibredCategory B S hS U').val.p
      (CatFiberedInGroupoids.homFunctor E.snd) :=
    isSurjectiveOnObjects_twoFibreProductSnd.{u, u, u} B S hS T₁.pt 𝒦.pt
      (fibredCategory B S hS U') T₁.fst k.hom hT₁fstsu
  have hErep : IsRepresentableByAlgebraicSpace B S hS E.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS E.pt
      (fibredCategory B S hS U') E.snd hEsndsm.1 hU'rep
  let A := CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} b' f a (a ≫ f)
    (Iso.refl (a ≫ f))
  have hA : Bicategory.IsTwoFibreProduct A :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} b' f a (a ≫ f)
      (Iso.refl (a ≫ f))
  let D := CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} b' b
    (associatedMap B S hS hTop).1 (a ≫ f) η
  have hD : Bicategory.IsTwoFibreProduct D :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} b' b
      (associatedMap B S hS hTop).1 (a ≫ f) η
  let cmp := Quotient.out (hD.from A)
  obtain ⟨W₁, hW₁, ⟨eW₁⟩⟩ := hT₁rep
  obtain ⟨W₂, hW₂, ⟨eW₂⟩⟩ := hT₂rep
  obtain ⟨W₃, hW₃, ⟨eW₃⟩⟩ := hSq₃rep
  obtain ⟨WE, hWE, ⟨eWE⟩⟩ := hErep
  have hcmpiso : IsIso (representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom) :=
    isIso_representingMap_preHom_of_isTwoFibreProduct B S hS hA hD cmp W₁ W₂ eW₁ eW₂
  have hEfstsp : Space.IsSmooth B S hS
      (representingMap B S hS E.pt T₁.pt WE W₁ eWE eW₁ E.fst) :=
    isSmooth_representingMap_of_isRelativelySmooth B S hS hEfstsm hWE hW₁ eWE eW₁
  have hcmpsm : Space.IsSmooth B S hS
      (representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom) :=
    @Space.isSmooth_of_isIso B S hS W₁ W₂ hW₁ hW₂
      (representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom) hcmpiso
  let repE := representingMap B S hS E.pt T₁.pt WE W₁ eWE eW₁ E.fst
  let repCmp := representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom
  let repT₂ := representingMap B S hS T₂.pt Sq₃.pt W₂ W₃ eW₂ eW₃ T₂.fst
  let nMor := cmp.hom ≫ T₂.fst
  have hPk : P ((repE ≫ repCmp) ≫ repT₂) :=
    prop_representingMap_twoFibreProductFst_comp B S hS P hP hU hV hTop hPtop Sq₃.snd hSq₃sndsm
      W₃ hW₃ eW₃ W₂ hW₂ eW₂ hWE (repE ≫ repCmp)
      (Space.isSmooth_comp B S hS hWE hW₁ hW₂ repE repCmp hEfstsp hcmpsm)
  have e1 : representingMap B S hS E.pt Sq₃.pt WE W₃ eWE eW₃ (E.fst ≫ nMor)
      = repE ≫ representingMap B S hS T₁.pt Sq₃.pt W₁ W₃ eW₁ eW₃ nMor :=
    representingMap_comp B S hS WE W₁ W₃ eWE eW₁ eW₃ E.fst nMor
  have e2 : representingMap B S hS T₁.pt Sq₃.pt W₁ W₃ eW₁ eW₃ nMor
      = repCmp ≫ repT₂ :=
    representingMap_comp B S hS W₁ W₂ W₃ eW₁ eW₂ eW₃ cmp.hom T₂.fst
  have hPkR : P (representingMap B S hS E.pt Sq₃.pt WE W₃ eWE eW₃
      (E.fst ≫ nMor)) :=
    ((Category.assoc repE repCmp repT₂).trans
      (e1.trans (congrArg (fun t => repE ≫ t) e2)).symm) ▸ hPk
  have ζ : (cmp.hom ≫ T₂.fst) ≫ Sq₃.fst ≅ T₁.fst ≫ 𝒦.fst :=
    Bicategory.associator cmp.hom T₂.fst Sq₃.fst ≪≫ cmp.isoFst.symm
  have ξ : (E.fst ≫ nMor) ≫ Sq₃.fst ≅ E.snd ≫ (associatedMap B S hS h').1 :=
    Bicategory.associator E.fst nMor Sq₃.fst ≪≫ Bicategory.whiskerLeftIso E.fst ζ ≪≫
      (Bicategory.associator E.fst T₁.fst 𝒦.fst).symm ≪≫
      Bicategory.whiskerRightIso E.iso 𝒦.fst ≪≫
      Bicategory.associator E.snd k.hom 𝒦.fst ≪≫
      Bicategory.whiskerLeftIso E.snd k.isoFst.symm
  have hsq : representingMap B S hS E.pt (fibredCategory B S hS V') WE V' eWE
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS V').val.p)
        ((E.fst ≫ nMor) ≫ Sq₃.fst)
      = representingMap B S hS E.pt (fibredCategory B S hS V') WE V' eWE
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS V').val.p)
        (E.snd ≫ (associatedMap B S hS h').1) :=
    representingMap_congr_twoIso (𝒜 := E.pt) (𝒞 := fibredCategory B S hS V') B S hS WE V' eWE
      (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS V').val.p) ξ
  have haasm : Space.IsSmooth B S hS
      (representingMap B S hS E.pt (fibredCategory B S hS U') WE U' eWE
        (StacksRepresentableCFG.EquivalenceOver.refl _) E.snd) :=
    isSmooth_representingMap_of_isRelativelySmooth B S hS hEsndsm hWE hU' eWE _
  have haasurj : Space.IsSurjective B S hS
      (representingMap B S hS E.pt (fibredCategory B S hS U') WE U' eWE
        (StacksRepresentableCFG.EquivalenceOver.refl _) E.snd) :=
    isSurjective_representingMap_of_isSurjectiveOnObjects B S hS E.snd WE U' eWE
      (StacksRepresentableCFG.EquivalenceOver.refl _) hEsndsu
  have hbbsm : Space.IsSmooth B S hS
      (representingMap B S hS Sq₃.pt (fibredCategory B S hS V') W₃ V' eW₃
        (StacksRepresentableCFG.EquivalenceOver.refl _) Sq₃.fst) :=
    isSmooth_representingMap_of_isRelativelySmooth B S hS hSq₃fstsm hW₃ hV' eW₃ _
  have hcommfinal :
      representingMap B S hS E.pt Sq₃.pt WE W₃ eWE eW₃ (E.fst ≫ nMor) ≫
        representingMap B S hS Sq₃.pt (fibredCategory B S hS V') W₃ V' eW₃
          (StacksRepresentableCFG.EquivalenceOver.refl _) Sq₃.fst
      = representingMap B S hS E.pt (fibredCategory B S hS U') WE U' eWE
          (StacksRepresentableCFG.EquivalenceOver.refl _) E.snd ≫ h' := by
    rw [← representingMap_comp (𝒜 := E.pt) (ℬ := Sq₃.pt) (𝒞 := fibredCategory B S hS V')
        B S hS WE W₃ V' eWE eW₃
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS V').val.p)
        (E.fst ≫ nMor) Sq₃.fst, hsq,
      representingMap_comp (𝒜 := E.pt) (ℬ := fibredCategory B S hS U')
        (𝒞 := fibredCategory B S hS V') B S hS WE U' V' eWE
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS U').val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS V').val.p)
        E.snd (associatedMap B S hS h').1,
      representingMap_associatedMap B S hS U' V' h']
  exact Space.prop_of_smooth_surjective_square B S hS P hP hU' hV' h' hWE hW₃ _ _ _ haasm
    haasurj hbbsm hcommfinal hPkR

/-- For a property `P` of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target and a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`: every diagram of
algebraic spaces over `f` with smooth vertical 1-morphisms whose comparison to the 2-fibre product
is smooth has `P` on its top horizontal morphism if and only if some such diagram with left
vertical 1-morphism surjective on objects does. -/
@[stacks 06FM "equivalence of parts (1) and (2)"]
theorem hasPropertyOnEverySmoothDiagram_iff_some
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴) :
    HasPropertyOnEverySmoothDiagram B S hS P f ↔ HasPropertyOnSomeSmoothDiagram B S hS P f :=
  ⟨hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS P h𝒳 h𝒴 f,
    hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS P hP f⟩

end AlgebraicGeometry.Stack

end
