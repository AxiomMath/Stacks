module

public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre

/-!
# The isomorphism presheaf as a presheaf of vertical morphisms

Let `p : 𝒳 ⥤ 𝒮` be a fibred category, `U` an object of `𝒮` and `x`, `y` objects of the fibre of
`p` over `U`. The isomorphism presheaf `Isom(x, y)` is the presheaf on `𝒮/U` whose sections over
`g : V ⟶ U` are the isomorphisms `g^* x ⟶ g^* y` of the fibre over `V`, for the chosen
pullbacks. This file shows that it is the presheaf of *vertical morphisms* between the two
chosen-pullback functors `𝒮/U ⥤ 𝒳`.

Everything is stated over the slice `𝒮/U.left` of a slice `𝒮 = 𝒟/X`, read through
`CategoryTheory.Over.iteratedSliceBackward`.

## Main definitions

* `CategoryTheory.Functor.pullbackSliceFunctor`: the 1-morphism `𝒮/U ⥤ 𝒳` attached to an object
  of the fibre over `U` by the chosen pullbacks, the 1-morphism of the 2-Yoneda lemma for the
  canonical cleavage.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.pairFunctor`: the 1-morphism into the product
  `𝒳 ×_𝒮 𝒳` given by a pair of 1-morphisms into `𝒳`.

## Main results

* `CategoryTheory.Functor.vertHomPresheafIsoIsomPresheaf`: the presheaf of vertical morphisms
  between the chosen-pullback functors of `x` and of `y` is `Isom(x, y)`.

## References

* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor


variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- The chosen-pullback functor `𝒮/U ⥤ 𝒳` attached to an object of the fibre over `U`. -/
noncomputable def pullbackSliceFunctor (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮} (x : p.Fiber U) :
    Over U ⥤ 𝒳 where
  obj g := (pullbackFiber p x g.hom).1
  map h := pullbackFiberMap p x h
  map_id g := pullbackFiberMap_id p x g
  map_comp h₁ h₂ := (pullbackFiberMap_comp p x h₁ h₂).symm

/-- The chosen-pullback functor of an object `x` of the fibre over `U`, followed by `p`, is the
forgetful functor `Over.forget U`. -/
lemma pullbackSliceFunctor_comp (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮} (x : p.Fiber U) :
    pullbackSliceFunctor p x ⋙ p = Over.forget U :=
  CategoryTheory.Functor.ext (fun g => (pullbackFiber p x g.hom).2)
    (fun _ _ h => IsHomLift.fac' p h.left (pullbackFiberMap p x h))

section Comparison

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

variable {D : Type u₁} [Category.{v₁} D] {X : D} {Z : Type u₂} [Category.{v₂} Z]
variable (p : Z ⥤ Over X) [p.IsFibered] (U : Over X) (x y : p.Fiber U)

/-- The chosen-pullback functor of `x`, precomposed with the iterated-slice functor and followed
by `p`, is `Over.map U.hom`. -/
lemma backward_pullbackSliceFunctor_comp :
    (Over.iteratedSliceBackward U ⋙ pullbackSliceFunctor p x) ⋙ p = Over.map U.hom := by
  rw [Functor.assoc, pullbackSliceFunctor_comp]
  exact Over.iteratedSliceBackward_forget U

/-- **The presheaf of vertical morphisms between chosen pullbacks is the isomorphism
presheaf.** For two objects `x`, `y` of the fibre of `p` over `U`, the presheaf on the slice
`𝒮/U.left` of vertical morphisms between the chosen pullbacks of `x` and of `y` is `Isom(x, y)`,
transported along the iterated-slice functor. -/
noncomputable def vertHomPresheafIsoIsomPresheaf (hp : p.IsFiberedInGroupoids) :
    VertHom.presheaf hp (backward_pullbackSliceFunctor_comp p U x)
        (backward_pullbackSliceFunctor_comp p U y) ≅
      (Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y :=
  NatIso.ofComponents
    (fun a => Equiv.toIso
      { toFun := fun φ => ⟨⟨φ.1, φ.2⟩,
          (hp.fiber_isGroupoid ((Over.map U.hom).obj a.unop)).all_isIso ⟨φ.1, φ.2⟩⟩
        invFun := fun m => ⟨m.1.1, m.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (by
      intro a a' h
      ext φ
      refine Subtype.ext (morRestrict_uniq p x y ((Over.iteratedSliceBackward U).map h.unop)
        ⟨φ.1, φ.2⟩ _ ?_)
      change (VertHom.restrict hp (backward_pullbackSliceFunctor_comp p U x)
          (backward_pullbackSliceFunctor_comp p U y) h.unop φ).1 ≫
            IsPreFibered.pullbackMap y.2 ((Over.iteratedSliceBackward U).obj a'.unop).hom
        = pullbackFiberMap p x ((Over.iteratedSliceBackward U).map h.unop) ≫ φ.1 ≫
            IsPreFibered.pullbackMap y.2 ((Over.iteratedSliceBackward U).obj a.unop).hom
      rw [← pullbackFiberMap_fac p y ((Over.iteratedSliceBackward U).map h.unop)]
      have hfac := VertHom.restrict_fac hp (backward_pullbackSliceFunctor_comp p U x)
        (backward_pullbackSliceFunctor_comp p U y) h.unop φ
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ IsPreFibered.pullbackMap y.2
          ((Over.iteratedSliceBackward U).obj a.unop).hom) hfac)).trans (Category.assoc _ _ _))

end Comparison


end CategoryTheory.Functor

namespace CategoryTheory.TwoFibreProductOver.DiagonalFibre


variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯]
variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {Z₁ Z₂ : 𝒯 ⥤ X}

attribute [local implicit_reducible] _root_.CategoryTheory.TwoFibreProductOver.fst
  _root_.CategoryTheory.TwoFibreProductOver.snd

/-- The 1-morphism into the product `𝒳 ×_𝒞 𝒳` given by a pair of 1-morphisms into `𝒳`. -/
def pairFunctor (h₁ : Z₁ ⋙ p = p𝒯) (h₂ : Z₂ ⋙ p = p𝒯) : 𝒯 ⥤ Prod' p where
  obj a :=
    { base := p𝒯.obj a
      x := Z₁.obj a
      y := Z₂.obj a
      hx := Functor.congr_obj h₁ a
      hy := Functor.congr_obj h₂ a
      iso := eqToIso ((Functor.congr_obj h₁ a).trans (Functor.congr_obj h₂ a).symm)
      vertical := by
        refine IsHomLift.of_fac' (𝟭 𝒞) _ _ (Functor.congr_obj h₁ a)
          (Functor.congr_obj h₂ a) ?_
        simp }
  map {a b} f :=
    { hbase := p𝒯.map f
      a := Z₁.map f
      b := Z₂.map f
      ha := VertHom.isHomLift_map h₁ f
      hb := VertHom.isHomLift_map h₂ f
      w := by
        have e₁ := Functor.congr_hom h₁ f
        have e₂ := Functor.congr_hom h₂ f
        simp only [Functor.comp_map] at e₁ e₂
        simp only [eqToIso.hom]
        rw [e₁, e₂]
        simp }
  map_id a := Hom.ext' (Z₁.map_id a) (Z₂.map_id a)
  map_comp f g := Hom.ext' (Z₁.map_comp f g) (Z₂.map_comp f g)

/-- The 1-morphism `pairFunctor h₁ h₂` followed by the projection to `𝒞` is `p𝒯`. -/
lemma pairFunctor_comp (h₁ : Z₁ ⋙ p = p𝒯) (h₂ : Z₂ ⋙ p = p𝒯) :
    pairFunctor h₁ h₂ ⋙ ProdP p = p𝒯 := rfl

/-- The first component of `pairFunctor h₁ h₂` is `Z₁`. -/
lemma fst_pairFunctor (h₁ : Z₁ ⋙ p = p𝒯) (h₂ : Z₂ ⋙ p = p𝒯) :
    Y₁' (pairFunctor h₁ h₂) = Z₁ := rfl

/-- The second component of `pairFunctor h₁ h₂` is `Z₂`. -/
lemma snd_pairFunctor (h₁ : Z₁ ⋙ p = p𝒯) (h₂ : Z₂ ⋙ p = p𝒯) :
    Y₂' (pairFunctor h₁ h₂) = Z₂ := rfl


end CategoryTheory.TwoFibreProductOver.DiagonalFibre

end
