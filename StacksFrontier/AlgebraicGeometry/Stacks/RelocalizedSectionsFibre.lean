module

public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# Sections of a relocalized presheaf over a prescribed morphism

Let `q : Z ⟶ U` be a morphism of a category and let `W` be a presheaf on the slice over `Z`. Its
relocalization `Λ W = (OverShriek.relocalizePresheafFunctor q).obj W` is a presheaf on the slice
over `U`, together with a morphism `w : Λ W ⟶ h_Z` presenting it over `Z`. This file identifies
the sections of `Λ W ⟶ h_Z` over a test object `T` with the values of `W` itself at the fibre
product `T ×_U Z`, once that fibre product is presented as an object of the slice over `U`.

## Main definitions

* `AlgebraicGeometry.Stack.relocalizeFiberEquiv`: sections of `Λ W` over `T` lying over a
  prescribed `g : T ⟶ Z` are sections of `W` over `(T, g)`.
* `AlgebraicGeometry.Stack.relocalizeYonedaFiberEquiv`: the same, for morphisms of presheaves out
  of `h_T`.
* `AlgebraicGeometry.Stack.relocalizeSectionsEquiv`: the identification: sections of
  `Λ W ⟶ h_Z` over `T` are values of `W` at `T ×_U Z`.
* `AlgebraicGeometry.Stack.yonedaBinaryProductIso`: the Yoneda embedding carries a binary product
  of the base to a binary product of presheaves.
* `AlgebraicGeometry.Stack.overBinaryFanIsLimit`: a cartesian square over `U` exhibits its corner
  as the binary product, in the slice over `U`, of the two objects it sits above.

## Main results

* `AlgebraicGeometry.Stack.relocalizeSectionsEquiv_map`: the identification is compatible with
  restriction along a morphism of test objects.
* `AlgebraicGeometry.Stack.relocalizeFiberEquiv_map` and
  `AlgebraicGeometry.Stack.relocalizeYonedaFiberEquiv_map`: the same for the two intermediate
  steps.

## References

* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05YH](https://stacks.math.columbia.edu/tag/05YH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack

/-! ### Sections of a relocalized presheaf -/

section Relocalize

variable {C : Type*} [Category.{u} C] {U Z : C} (q : Z ⟶ U) (W : (Over Z)ᵒᵖ ⥤ Type u)
  (w : (OverShriek.relocalizePresheafFunctor q).obj W ⟶ yoneda.obj (Over.mk q))
  (hw : ∀ T s, (w.app (op T) s).left = s.val.fst)

/-- The sections of a relocalized presheaf `Λ W` over `T` lying over a prescribed morphism
`g : T ⟶ Z` of the base are the sections of `W` over `(T, g)`: a section of `Λ W` over `T` is a
pair consisting of a morphism `T ⟶ Z` and a section of `W` over it, and `w` reads off the first
component. -/
def relocalizeFiberEquiv (T : Over U) (g : T ⟶ Over.mk q) :
    {s : ((OverShriek.relocalizePresheafFunctor q).obj W).obj (op T) //
      w.app (op T) s = g} ≃ W.obj (op (Over.mk g.left)) where
  toFun s := by
    rcases s with ⟨⟨⟨ψ, s⟩, hψ⟩, hs⟩
    obtain rfl : ψ = g.left := (hw T ⟨⟨ψ, s⟩, hψ⟩).symm.trans (congrArg (fun f => f.left) hs)
    exact s
  invFun s := ⟨⟨⟨g.left, s⟩, g.w⟩, Over.OverMorphism.ext (hw T _)⟩
  left_inv s := by
    rcases s with ⟨⟨⟨ψ, s⟩, hψ⟩, hs⟩
    obtain rfl : ψ = g.left := (hw T ⟨⟨ψ, s⟩, hψ⟩).symm.trans (congrArg (fun f => f.left) hs)
    rfl
  right_inv s := rfl

/-- `AlgebraicGeometry.Stack.relocalizeFiberEquiv` is compatible with restriction along a
morphism `T' ⟶ T` of test objects. -/
theorem relocalizeFiberEquiv_map {T T' : Over U} (f : T' ⟶ T) (g : T ⟶ Over.mk q)
    (s : {s : ((OverShriek.relocalizePresheafFunctor q).obj W).obj (op T) //
      w.app (op T) s = g}) :
    relocalizeFiberEquiv q W w hw T' (f ≫ g)
      ⟨((OverShriek.relocalizePresheafFunctor q).obj W).map f.op s.val, by
        rw [NatTrans.naturality_apply, s.property]; rfl⟩ =
      W.map (Over.homMk f.left rfl : Over.mk (f ≫ g).left ⟶ Over.mk g.left).op
        (relocalizeFiberEquiv q W w hw T g s) := by
  rcases s with ⟨⟨⟨ψ, s⟩, hψ⟩, hs⟩
  obtain rfl : ψ = g.left := (hw T ⟨⟨ψ, s⟩, hψ⟩).symm.trans (congrArg (fun f => f.left) hs)
  rfl

/-- The morphisms of presheaves `h_T ⟶ Λ W` lying over a prescribed `g : T ⟶ Z` are the sections
of `W` over `(T, g)`. -/
noncomputable def relocalizeYonedaFiberEquiv (T : Over U) (g : T ⟶ Over.mk q) :
    {s : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor q).obj W // s ≫ w = yoneda.map g} ≃
      W.obj (op (Over.mk g.left)) :=
  (yonedaEquiv.subtypeEquiv (fun s => by
    rw [← yonedaEquiv.injective.eq_iff]
    simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map])).trans
    (relocalizeFiberEquiv q W w hw T g)

/-- `AlgebraicGeometry.Stack.relocalizeYonedaFiberEquiv` is compatible with restriction along a
morphism `T' ⟶ T` of test objects. -/
theorem relocalizeYonedaFiberEquiv_map {T T' : Over U} (f : T' ⟶ T) (g : T ⟶ Over.mk q)
    (s : {s : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor q).obj W //
      s ≫ w = yoneda.map g}) :
    relocalizeYonedaFiberEquiv q W w hw T' (f ≫ g)
      ⟨yoneda.map f ≫ s.val, by rw [Category.assoc, s.property, ← yoneda.map_comp]⟩ =
      W.map (Over.homMk f.left rfl : Over.mk (f ≫ g).left ⟶ Over.mk g.left).op
        (relocalizeYonedaFiberEquiv q W w hw T g s) := by
  have hs : w.app (op T) (yonedaEquiv s.val) = g := by
    rw [← yonedaEquiv_comp, s.property, yonedaEquiv_yoneda_map]
  have h := relocalizeFiberEquiv_map q W w hw f g ⟨yonedaEquiv s.val, hs⟩
  dsimp only [relocalizeYonedaFiberEquiv, Equiv.trans_apply, Equiv.subtypeEquiv]
  convert h using 1
  exact congrArg _ (Subtype.ext (yonedaEquiv_naturality s.val f).symm)

/-- The sections of `Λ W → Z` over `T` in the sense of
`AlgebraicGeometry.Space.SectionsOver` are the sections of `W` over the fibre product
`T ×_U Z`, once that fibre product is presented as an object `V` of the base together with an
identification of `h_V` with `h_T × h_Z`. -/
noncomputable def relocalizeSectionsEquiv (T V : Over U) (g : V ⟶ Over.mk q)
    (e : yoneda.obj V ≅ yoneda.obj T ⨯ yoneda.obj (Over.mk q))
    (he : e.hom ≫ prod.snd = yoneda.map g) :
    {s : yoneda.obj T ⨯ yoneda.obj (Over.mk q) ⟶
      (OverShriek.relocalizePresheafFunctor q).obj W // s ≫ w = prod.snd} ≃
      W.obj (op (Over.mk g.left)) :=
  (e.symm.homFromEquiv.subtypeEquiv (fun s => by
    change s ≫ w = prod.snd ↔ (e.hom ≫ s) ≫ w = yoneda.map g
    rw [← he, Category.assoc, cancel_epi])).trans (relocalizeYonedaFiberEquiv q W w hw V g)

/-- `AlgebraicGeometry.Stack.relocalizeSectionsEquiv` is compatible with restriction along a
morphism `T' ⟶ T` of test objects, the two presentations of the fibre products being related by
`k : V' ⟶ V`. -/
theorem relocalizeSectionsEquiv_map {T T' V V' : Over U} (f : T' ⟶ T) (k : V' ⟶ V)
    (g : V ⟶ Over.mk q) (g' : V' ⟶ Over.mk q) (hk : k ≫ g = g')
    (e : yoneda.obj V ≅ yoneda.obj T ⨯ yoneda.obj (Over.mk q))
    (e' : yoneda.obj V' ≅ yoneda.obj T' ⨯ yoneda.obj (Over.mk q))
    (he : e.hom ≫ prod.snd = yoneda.map g) (he' : e'.hom ≫ prod.snd = yoneda.map g')
    (hemap : e'.hom ≫ prod.map (yoneda.map f) (𝟙 _) = yoneda.map k ≫ e.hom)
    (s : {s : yoneda.obj T ⨯ yoneda.obj (Over.mk q) ⟶
      (OverShriek.relocalizePresheafFunctor q).obj W // s ≫ w = prod.snd}) :
    relocalizeSectionsEquiv q W w hw T' V' g' e' he'
      ⟨prod.map (yoneda.map f) (𝟙 _) ≫ s.val, by simp [Category.assoc, s.property]⟩ =
      W.map (Over.homMk k.left (congrArg (fun t => t.left) hk) :
        Over.mk g'.left ⟶ Over.mk g.left).op
        (relocalizeSectionsEquiv q W w hw T V g e he s) := by
  subst g'
  have hh := relocalizeYonedaFiberEquiv_map q W w hw k g
    ⟨e.hom ≫ s.val, by rw [Category.assoc, s.property, he]⟩
  dsimp only [relocalizeSectionsEquiv, Equiv.trans_apply, Equiv.subtypeEquiv]
  convert hh using 1
  · refine congrArg _ (Subtype.ext ?_)
    show e'.hom ≫ (prod.map (yoneda.map f) (𝟙 _) ≫ s.val) = yoneda.map k ≫ (e.hom ≫ s.val)
    rw [← Category.assoc, hemap, Category.assoc]
  · rfl

end Relocalize

/-! ### Binary products of representables -/

/-- A binary product in the base is carried by the Yoneda embedding to a binary product of
presheaves. -/
noncomputable def yonedaBinaryProductIso {C : Type*} [Category.{u} C] {V T Z : C}
    (a : V ⟶ T) (b : V ⟶ Z) (h : IsLimit (BinaryFan.mk a b)) :
    yoneda.obj V ≅ yoneda.obj T ⨯ yoneda.obj Z := by
  let hy := (isLimitMapConeBinaryFanEquiv yoneda a b) (isLimitOfPreserves yoneda h)
  have h₁ : BinaryFan.IsLimit.lift hy prod.fst prod.snd ≫ yoneda.map a = prod.fst :=
    BinaryFan.IsLimit.lift_fst hy _ _
  have h₂ : BinaryFan.IsLimit.lift hy prod.fst prod.snd ≫ yoneda.map b = prod.snd :=
    BinaryFan.IsLimit.lift_snd hy _ _
  refine
    { hom := prod.lift (yoneda.map a) (yoneda.map b)
      inv := BinaryFan.IsLimit.lift hy prod.fst prod.snd
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · exact BinaryFan.IsLimit.hom_ext hy (by simp [h₁]) (by simp [h₂])
  · exact prod.hom_ext (by simp [h₁]) (by simp [h₂])

/-- The first projection of `AlgebraicGeometry.Stack.yonedaBinaryProductIso`. -/
theorem yonedaBinaryProductIso_fst {C : Type*} [Category.{u} C] {V T Z : C} (a : V ⟶ T)
    (b : V ⟶ Z) (h : IsLimit (BinaryFan.mk a b)) :
    (yonedaBinaryProductIso a b h).hom ≫ prod.fst = yoneda.map a :=
  prod.lift_fst _ _

/-- The second projection of `AlgebraicGeometry.Stack.yonedaBinaryProductIso`. -/
theorem yonedaBinaryProductIso_snd {C : Type*} [Category.{u} C] {V T Z : C} (a : V ⟶ T)
    (b : V ⟶ Z) (h : IsLimit (BinaryFan.mk a b)) :
    (yonedaBinaryProductIso a b h).hom ≫ prod.snd = yoneda.map b :=
  prod.lift_snd _ _

/-- A cartesian square over `U` exhibits its corner as the binary product, in the slice over `U`,
of the two objects it sits above. -/
noncomputable def overBinaryFanIsLimit {C : Type*} [Category C] {U Z : C} (q : Z ⟶ U)
    (T V : Over U) (a : V ⟶ T) (b : V ⟶ Over.mk q)
    (h : IsPullback b.left a.left q T.hom) : IsLimit (BinaryFan.mk a b) :=
  BinaryFan.IsLimit.mk _
    (fun f g => Over.homMk (h.lift g.left f.left (g.w.trans f.w.symm)) (by
      change h.lift g.left f.left _ ≫ V.hom = _
      rw [← b.w, ← Category.assoc, h.lift_fst]
      exact g.w))
    (fun f g => Over.OverMorphism.ext (h.lift_snd _ _ _))
    (fun f g => Over.OverMorphism.ext (h.lift_fst _ _ _))
    (fun f g m hm₁ hm₂ => Over.OverMorphism.ext (h.hom_ext
      ((congrArg (fun k => k.left) hm₂).trans (h.lift_fst _ _ _).symm)
      ((congrArg (fun k => k.left) hm₁).trans (h.lift_snd _ _ _).symm)))

end AlgebraicGeometry.Stack

end
