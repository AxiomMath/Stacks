module

public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheafVertHom

/-!
# A scheme-valued point of a category fibred in groupoids is a chosen-pullback 1-morphism

Let `p : 𝒳 ⥤ 𝒟/X` be fibred in groupoids and let `U` be an object of `𝒟/X`. A 1-morphism
`W : (𝒟/X)/U ⟶ 𝒳` over `𝒟/X`, read on the slice `𝒟/U.left` through
`CategoryTheory.Over.iteratedSliceBackward`, is determined up to a vertical natural isomorphism
by its value at the terminal object: `W` is naturally isomorphic, vertically, to the
chosen-pullback 1-morphism `CategoryTheory.Functor.pullbackSliceFunctor` of that value. This is a
form of the 2-Yoneda lemma.

Consequently, the presheaf of vertical morphisms between the two components of an arbitrary
scheme-valued point of `𝒳 ×_{𝒟/X} 𝒳` is the isomorphism presheaf `Isom(x, y)` for `x`, `y` the
values of the two components at the terminal object.

## Main definitions

* `CategoryTheory.Functor.sliceValue`: the value at the terminal object, as an object of the
  fibre over `U`.
* `CategoryTheory.Functor.sliceValueNatIso`: the vertical natural isomorphism between `W` and the
  chosen-pullback 1-morphism of `CategoryTheory.Functor.sliceValue`.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafIsoOfIso`: the presheaf of
  vertical morphisms is invariant under vertical natural isomorphisms of the two 1-morphisms it
  is taken between.

## Main results

* `CategoryTheory.Functor.vertHomPresheafIsoIsomPresheafOfPoint`: the presheaf of vertical
  morphisms between the two components of a scheme-valued point of `𝒳 ×_{𝒟/X} 𝒳` is the
  isomorphism presheaf of the two values at the terminal object.

## Implementation notes

The terminal object of `𝒟/U.left` is `Over.mk (𝟙 U.left)`, and the unique morphism to it from
`a` is `CategoryTheory.Functor.toMkId`.

`CategoryTheory.Functor.sliceValue` is an `abbrev`: instance search for
`CategoryTheory.Functor.IsStronglyCartesian` has to see through it.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {D : Type u₁} [Category.{v₁} D] {X : D} {Z : Type u₂} [Category.{v₂} Z]

/-- `Over.map U.hom` sends the terminal object of `𝒟/U.left` to `U`. -/
lemma overMap_obj_mkId (U : Over X) :
    (Over.map U.hom).obj (Over.mk (𝟙 U.left)) = U := by
  have h : (Over.map U.hom).obj (Over.mk (𝟙 U.left)) = Over.mk (𝟙 U.left ≫ U.hom) := rfl
  rw [h, Category.id_comp]
  rfl

/-- The unique morphism to the terminal object of `𝒟/U.left`. -/
abbrev toMkId (U : Over X) (a : Over U.left) : a ⟶ Over.mk (𝟙 U.left) :=
  Over.homMk a.hom

/-- The structure morphism of an object `a` of `𝒟/U.left`, read as a morphism of `𝒟/X` from the
image of `a` under `Over.map U.hom` to `U`. -/
abbrev structHom (U : Over X) (a : Over U.left) : (Over.map U.hom).obj a ⟶ U :=
  Over.homMk a.hom

/-- The structure morphism of the image of `a` under `Over.iteratedSliceBackward U` is
`structHom U a`. -/
lemma iteratedSliceBackward_hom (U : Over X) (a : Over U.left) :
    ((Over.iteratedSliceBackward U).obj a).hom = structHom U a := rfl

/-- The image under `Over.map U.hom` of the morphism `toMkId U a` to the terminal object is
`structHom U a`, up to the identification of `(Over.map U.hom).obj (Over.mk (𝟙 U.left))` with
`U`. -/
lemma overMap_map_toMkId (U : Over X) (a : Over U.left) :
    (Over.map U.hom).map (toMkId U a) =
      structHom U a ≫ eqToHom (overMap_obj_mkId U).symm := by
  apply Over.OverMorphism.ext
  simp

section SliceValue

variable (p : Z ⥤ Over X) (U : Over X) (W : Over U.left ⥤ Z)

/-- The value at the terminal object of a 1-morphism from the slice over `U.left`, as an object
of the fibre of `p` over `U`. -/
abbrev sliceValue (hW : W ⋙ p = Over.map U.hom) : p.Fiber U :=
  ⟨W.obj (Over.mk (𝟙 U.left)),
    (Functor.congr_obj hW (Over.mk (𝟙 U.left))).trans (overMap_obj_mkId U)⟩

/-- The image under `W` of the morphism `toMkId U a` to the terminal object lies over
`structHom U a`. -/
lemma isHomLift_map_toMkId (hW : W ⋙ p = Over.map U.hom) (a : Over U.left) :
    p.IsHomLift (structHom U a) (W.map (toMkId U a)) := by
  refine IsHomLift.of_fac' p _ _ (Functor.congr_obj hW a) (sliceValue p U W hW).2 ?_
  have e := Functor.congr_hom hW (toMkId U a)
  simp only [Functor.comp_map] at e
  rw [e, overMap_map_toMkId]
  simp only [Category.assoc, eqToHom_trans]

/-- The image under `W` of `toMkId U a` is strongly cartesian. -/
private lemma isStronglyCartesian_map_toMkId (hp : p.IsFiberedInGroupoids)
    (hW : W ⋙ p = Over.map U.hom) (a : Over U.left) :
    p.IsStronglyCartesian (structHom U a) (W.map (toMkId U a)) := by
  have := isHomLift_map_toMkId p U W hW a
  exact hp.isStronglyCartesian_homLift _ _

variable [p.IsFibered]

/-- The chosen pullback of the value at the terminal object along `structHom U a` is strongly
cartesian. -/
private lemma isStronglyCartesian_pullbackMap_structHom (hp : p.IsFiberedInGroupoids)
    (hW : W ⋙ p = Over.map U.hom) (a : Over U.left) :
    p.IsStronglyCartesian (structHom U a)
      (IsPreFibered.pullbackMap (sliceValue p U W hW).2 (structHom U a)) :=
  hp.isStronglyCartesian_homLift _ _

/-- The comparison isomorphism between the chosen pullback of the value at the terminal object
and the value at an arbitrary object: both are cartesian lifts of the same morphism with the
same target. -/
noncomputable def sliceValueIso (hp : p.IsFiberedInGroupoids)
    (hW : W ⋙ p = Over.map U.hom) (a : Over U.left) :
    (Over.iteratedSliceBackward U ⋙ pullbackSliceFunctor p (sliceValue p U W hW)).obj a ≅
      W.obj a := by
  have := isHomLift_map_toMkId p U W hW a
  have h1 : p.IsStronglyCartesian (structHom U a) (W.map (toMkId U a)) :=
    hp.isStronglyCartesian_homLift _ _
  have h2 : p.IsStronglyCartesian (structHom U a)
      (IsPreFibered.pullbackMap (sliceValue p U W hW).2 (structHom U a)) :=
    hp.isStronglyCartesian_homLift _ _
  have E := IsStronglyCartesian.domainIsoOfBaseIso p
    (g := Iso.refl ((Over.map U.hom).obj a))
    (Category.id_comp (structHom U a)).symm (W.map (toMkId U a))
    (IsPreFibered.pullbackMap (sliceValue p U W hW).2 (structHom U a))
  exact E

/-- The comparison isomorphism `sliceValueIso` followed by the image under `W` of `toMkId U a` is
the chosen cartesian lift of `structHom U a`. -/
lemma sliceValueIso_fac (hp : p.IsFiberedInGroupoids)
    (hW : W ⋙ p = Over.map U.hom) (a : Over U.left) :
    (sliceValueIso p U W hp hW a).hom ≫ W.map (toMkId U a) =
      IsPreFibered.pullbackMap (sliceValue p U W hW).2 (structHom U a) := by
  have h1 := isStronglyCartesian_map_toMkId p U W hp hW a
  have h2 := isStronglyCartesian_pullbackMap_structHom p U W hp hW a
  exact IsStronglyCartesian.fac p (structHom U a) (W.map (toMkId U a))
    (Category.id_comp (structHom U a)).symm
    (IsPreFibered.pullbackMap (sliceValue p U W hW).2 (structHom U a))

/-- The comparison isomorphism `sliceValueIso` is vertical: it lies over the identity. -/
lemma isHomLift_sliceValueIso (hp : p.IsFiberedInGroupoids)
    (hW : W ⋙ p = Over.map U.hom) (a : Over U.left) :
    p.IsHomLift (𝟙 ((Over.map U.hom).obj a)) (sliceValueIso p U W hp hW a).hom := by
  have h1 := isStronglyCartesian_map_toMkId p U W hp hW a
  have h2 := isStronglyCartesian_pullbackMap_structHom p U W hp hW a
  exact IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift p
    (g := Iso.refl ((Over.map U.hom).obj a)) (Category.id_comp (structHom U a)).symm
    (W.map (toMkId U a)) (IsPreFibered.pullbackMap (sliceValue p U W hW).2 (structHom U a))

/-- Any morphism `a' ⟶ a` followed by the morphism `toMkId U a` to the terminal object is
`toMkId U a'`. -/
lemma comp_toMkId (U : Over X) {a' a : Over U.left} (h : a' ⟶ a) :
    h ≫ toMkId U a = toMkId U a' := by
  apply Over.OverMorphism.ext
  simp

/-- The comparison isomorphisms assemble into a natural isomorphism: a 1-morphism from the slice
over `U.left` into `𝒳` is the chosen-pullback 1-morphism of its value at the terminal object. -/
noncomputable def sliceValueNatIso (hp : p.IsFiberedInGroupoids)
    (hW : W ⋙ p = Over.map U.hom) :
    Over.iteratedSliceBackward U ⋙ pullbackSliceFunctor p (sliceValue p U W hW) ≅ W :=
  NatIso.ofComponents (sliceValueIso p U W hp hW) (by
    intro a' a h
    have := isHomLift_map_toMkId p U W hW a
    have h1 : p.IsStronglyCartesian (structHom U a) (W.map (toMkId U a)) :=
      hp.isStronglyCartesian_homLift _ _
    have hl : p.IsHomLift ((Over.map U.hom).map h)
        ((Over.iteratedSliceBackward U ⋙ pullbackSliceFunctor p (sliceValue p U W hW)).map h ≫
          (sliceValueIso p U W hp hW a).hom) := by
      have h3 := isHomLift_sliceValueIso p U W hp hW a
      have h4 : p.IsHomLift ((Over.map U.hom).map h)
          ((Over.iteratedSliceBackward U ⋙
            pullbackSliceFunctor p (sliceValue p U W hW)).map h) :=
        pullbackFiberMap_isHomLift p (sliceValue p U W hW) ((Over.iteratedSliceBackward U).map h)
      have hc : p.IsHomLift ((Over.map U.hom).map h ≫ 𝟙 ((Over.map U.hom).obj a))
          ((Over.iteratedSliceBackward U ⋙
              pullbackSliceFunctor p (sliceValue p U W hW)).map h ≫
            (sliceValueIso p U W hp hW a).hom) := inferInstance
      rwa [Category.comp_id] at hc
    have hr : p.IsHomLift ((Over.map U.hom).map h)
        ((sliceValueIso p U W hp hW a').hom ≫ W.map h) := by
      have h3 := isHomLift_sliceValueIso p U W hp hW a'
      have h5 : p.IsHomLift ((Over.map U.hom).map h) (W.map h) :=
        TwoFibreProductOver.DiagonalFibre.VertHom.isHomLift_map hW h
      have hc : p.IsHomLift (𝟙 ((Over.map U.hom).obj a') ≫ (Over.map U.hom).map h)
          ((sliceValueIso p U W hp hW a').hom ≫ W.map h) := inferInstance
      rwa [Category.id_comp] at hc
    refine IsStronglyCartesian.ext p (structHom U a) (W.map (toMkId U a))
      ((Over.map U.hom).map h) ?_
    rw [Category.assoc, sliceValueIso_fac p U W hp hW a, Category.assoc, ← W.map_comp,
      comp_toMkId, sliceValueIso_fac p U W hp hW a']
    exact pullbackFiberMap_fac p (sliceValue p U W hW) ((Over.iteratedSliceBackward U).map h))

/-- The inverse of the comparison isomorphism `sliceValueIso` lies over the identity. -/
lemma isHomLift_sliceValueIso_inv (hp : p.IsFiberedInGroupoids)
    (hW : W ⋙ p = Over.map U.hom) (a : Over U.left) :
    p.IsHomLift (𝟙 ((Over.map U.hom).obj a)) (sliceValueIso p U W hp hW a).inv := by
  have := isHomLift_sliceValueIso p U W hp hW a
  exact IsHomLift.lift_id_inv p ((Over.map U.hom).obj a) (sliceValueIso p U W hp hW a)

end SliceValue

end CategoryTheory.Functor


namespace CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {Z : Type u₃} [Category.{v₃} Z]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯]
variable {p : Z ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {Z₁ Z₁' Z₂ Z₂' : 𝒯 ⥤ Z}

/-- The presheaf of vertical morphisms is invariant under vertical natural isomorphisms of the
two 1-morphisms it is taken between. -/
noncomputable def presheafIsoOfIso (hp : p.IsFiberedInGroupoids)
    (h₁ : Z₁ ⋙ p = p𝒯) (h₁' : Z₁' ⋙ p = p𝒯) (h₂ : Z₂ ⋙ p = p𝒯) (h₂' : Z₂' ⋙ p = p𝒯)
    (θ₁ : Z₁' ≅ Z₁) (hθ₁ : ∀ a, p.IsHomLift (𝟙 (p𝒯.obj a)) (θ₁.hom.app a))
    (hθ₁' : ∀ a, p.IsHomLift (𝟙 (p𝒯.obj a)) (θ₁.inv.app a))
    (θ₂ : Z₂ ≅ Z₂') (hθ₂ : ∀ a, p.IsHomLift (𝟙 (p𝒯.obj a)) (θ₂.hom.app a))
    (hθ₂' : ∀ a, p.IsHomLift (𝟙 (p𝒯.obj a)) (θ₂.inv.app a)) :
    presheaf hp h₁ h₂ ≅ presheaf hp h₁' h₂' :=
  NatIso.ofComponents
    (fun a => Equiv.toIso
      { toFun := fun φ => ⟨θ₁.hom.app a.unop ≫ φ.1 ≫ θ₂.hom.app a.unop, by
          have := hθ₁ a.unop
          have := φ.2
          have := hθ₂ a.unop
          have hc : p.IsHomLift (𝟙 (p𝒯.obj a.unop) ≫ 𝟙 (p𝒯.obj a.unop) ≫ 𝟙 (p𝒯.obj a.unop))
              (θ₁.hom.app a.unop ≫ φ.1 ≫ θ₂.hom.app a.unop) := inferInstance
          rwa [Category.comp_id, Category.comp_id] at hc⟩
        invFun := fun ψ => ⟨θ₁.inv.app a.unop ≫ ψ.1 ≫ θ₂.inv.app a.unop, by
          have := hθ₁' a.unop
          have := ψ.2
          have := hθ₂' a.unop
          have hc : p.IsHomLift (𝟙 (p𝒯.obj a.unop) ≫ 𝟙 (p𝒯.obj a.unop) ≫ 𝟙 (p𝒯.obj a.unop))
              (θ₁.inv.app a.unop ≫ ψ.1 ≫ θ₂.inv.app a.unop) := inferInstance
          rwa [Category.comp_id, Category.comp_id] at hc⟩
        left_inv := fun _ => by
          apply Subtype.ext
          simp
        right_inv := fun _ => by
          apply Subtype.ext
          simp })
    (by
      intro a a' h
      ext φ
      refine restrict_uniq hp h₁' h₂' h.unop _ _ ?_
      have hfac := restrict_fac hp h₁ h₂ h.unop φ
      have hn₂ := θ₂.hom.naturality h.unop
      have hn₁ := θ₁.hom.naturality h.unop
      change (θ₁.hom.app a'.unop ≫ (restrict hp h₁ h₂ h.unop φ).1 ≫ θ₂.hom.app a'.unop) ≫
          Z₂'.map h.unop
        = Z₁'.map h.unop ≫ θ₁.hom.app a.unop ≫ φ.1 ≫ θ₂.hom.app a.unop
      rw [Category.assoc, Category.assoc, ← hn₂,
        ← Category.assoc (restrict hp h₁ h₂ h.unop φ).1, hfac]
      simp only [← Category.assoc]
      rw [hn₁])

end CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom

namespace CategoryTheory.Functor

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

variable {D : Type u₁} [Category.{v₁} D] {X : D} {Z : Type u₂} [Category.{v₂} Z]

/-- For two 1-morphisms `W₁`, `W₂` from the slice over `U.left` into `𝒳`, both lying over
`Over.map U.hom`, the presheaf of vertical morphisms `W₁ ⟶ W₂` is `Isom(x, y)` for `x`, `y` the
values of `W₁` and `W₂` at the terminal object. -/
noncomputable def vertHomPresheafIsoIsomPresheafOfFunctors (p : Z ⥤ Over X) [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (U : Over X) (W₁ W₂ : Over U.left ⥤ Z)
    (h₁ : W₁ ⋙ p = Over.map U.hom) (h₂ : W₂ ⋙ p = Over.map U.hom) :
    VertHom.presheaf hp h₁ h₂ ≅ (Over.iteratedSliceBackward U).op ⋙
      p.isomPresheaf (sliceValue p U W₁ h₁) (sliceValue p U W₂ h₂) :=
  (VertHom.presheafIsoOfIso hp h₁
      (backward_pullbackSliceFunctor_comp p U (sliceValue p U W₁ h₁))
      h₂
      (backward_pullbackSliceFunctor_comp p U (sliceValue p U W₂ h₂))
      (sliceValueNatIso p U W₁ hp h₁)
      (isHomLift_sliceValueIso p U W₁ hp h₁)
      (isHomLift_sliceValueIso_inv p U W₁ hp h₁)
      (sliceValueNatIso p U W₂ hp h₂).symm
      (isHomLift_sliceValueIso_inv p U W₂ hp h₂)
      (isHomLift_sliceValueIso p U W₂ hp h₂)).trans
    (vertHomPresheafIsoIsomPresheaf p U (sliceValue p U W₁ h₁) (sliceValue p U W₂ h₂) hp)

/-- For a 1-morphism `Y` from the slice over `U.left` into the product of `𝒳` with itself, the
presheaf of vertical morphisms between the two components of `Y` is
`Isom(x, y)` for `x`, `y` the values of those components at the terminal object. -/
noncomputable def vertHomPresheafIsoIsomPresheafOfPoint (p : Z ⥤ Over X) [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (U : Over X) (Y : Over U.left ⥤ Prod' p)
    (hY : Y ⋙ ProdP p = Over.map U.hom) :
    vertHomPresheaf hp hY ≅ (Over.iteratedSliceBackward U).op ⋙
      p.isomPresheaf (sliceValue p U (Y₁' Y) (h1' hY)) (sliceValue p U (Y₂' Y) (h2' hY)) :=
  vertHomPresheafIsoIsomPresheafOfFunctors p hp U (Y₁' Y) (Y₂' Y) (h1' hY) (h2' hY)

end CategoryTheory.Functor

end
