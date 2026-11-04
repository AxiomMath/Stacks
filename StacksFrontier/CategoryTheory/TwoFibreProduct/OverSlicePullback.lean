module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The fibre product over a base of two slices is the slice over the fibre product

Fix a base category `𝒞`, a cospan `a : U ⟶ W`, `b : V ⟶ W` of `𝒞` and a pullback square
`p : Q ⟶ U`, `q : Q ⟶ V` over it. The three slices `𝒞/U`, `𝒞/V` and `𝒞/W` are categories over
`𝒞` through their forgetful functors, `CategoryTheory.Over.map a` and `CategoryTheory.Over.map b`
are 1-morphisms over `𝒞`, and their 2-fibre product
`CategoryTheory.TwoFibreProductOver` in the 2-category of categories over `𝒞` is the slice
`𝒞/Q`.

This is the fibre-product analogue of
`CategoryTheory.TwoFibreProductOver.instIsEquivalenceSliceProd`, which treats the product over the
terminal cospan. It is the elementary input to the identification of the 2-fibre product of the
algebraic stacks represented by three schemes of a big site with the stack represented by their
fibre product: a morphism `T ⟶ Q` is exactly a pair of morphisms `T ⟶ U`, `T ⟶ V` agreeing over
`W`, which is exactly an object of the 2-fibre product of the slices.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.SlicePullback`: the 2-fibre product of `𝒞/U` and `𝒞/V`
  over `𝒞/W`, taken in the 2-category of categories over `𝒞`.
* `CategoryTheory.TwoFibreProductOver.slicePullback`: the comparison functor from `𝒞/Q`, sending
  an object `c : T ⟶ Q` to the pair of its two components, with the identity of `T` as
  comparison isomorphism.

## Main results

* `CategoryTheory.TwoFibreProductOver.slicePullback_comp_structureFunctor`: the comparison
  functor is strictly a 1-morphism over `𝒞`.
* `CategoryTheory.TwoFibreProductOver.instIsEquivalenceSlicePullback`: it is an equivalence.

## Implementation notes

The comparison isomorphism of an object of the 2-fibre product is forced to be the canonical
`eqToHom` between the images of the two components
(`CategoryTheory.TwoFibreProductOver.slicePullback_iso_hom_left`): verticality over the forgetful
functor of `𝒞/W` pins down the morphism of `𝒞` underlying it, and `CategoryTheory.Over.forget` is
faithful, so the morphism of `𝒞/W` is pinned down too. That is why the comparison functor can put
the identity in that field, and why essential surjectivity needs no choice beyond
`CategoryTheory.IsPullback.lift`.

As in `CategoryTheory.TwoFibreProductOver.instIsEquivalenceSliceProd`, equivalence is proved by
fully faithful plus essentially surjective rather than by an explicit quasi-inverse: the round
trip through `CategoryTheory.IsPullback.lift` replaces an object `(T, x, y, φ)` by the pair of
components of the morphism it induces into `Q`, and the two differ only by the `eqToHom`s
recording that the two components lie over `T`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoFibreProductOver

universe v₁ u₁

attribute [local implicit_reducible] fst snd structureFunctor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {Q U V W : 𝒞} {p : Q ⟶ U} {q : Q ⟶ V}
  (a : U ⟶ W) (b : V ⟶ W)

/-- The 2-fibre product of the two slices `𝒞/U` and `𝒞/V` over `𝒞/W`, formed in the
2-category of categories over `𝒞`. -/
abbrev SlicePullback : Type _ :=
  TwoFibreProductOver (Over.forget U) (Over.forget V) (Over.forget W) (Over.map a) (Over.map b)

variable {a b}

/-- The comparison isomorphism of an object of `SlicePullback a b` is the identity of its base,
up to the two equalities recording that the components lie over that base. -/
theorem slicePullback_iso_hom_left (P : SlicePullback a b) :
    P.iso.hom.left = eqToHom P.hx ≫ eqToHom P.hy.symm := by
  have := P.vertical
  have h := IsHomLift.fac' (Over.forget W) (𝟙 P.base) P.iso.hom
  simpa using h

/-- The two components of an object of `SlicePullback a b` agree over `W`, after the two
equalities recording that they lie over the base. -/
theorem slicePullback_comp_eq (P : SlicePullback a b) :
    (eqToHom P.hx.symm ≫ P.x.hom) ≫ a = (eqToHom P.hy.symm ≫ P.y.hom) ≫ b := by
  have hw := Over.w P.iso.hom
  rw [slicePullback_iso_hom_left] at hw
  simp only [Over.map_obj_left, Over.map_obj_hom, Category.assoc] at hw ⊢
  rw [← hw]
  simp

variable (h : IsPullback p q a b)

/-- The comparison functor `𝒞/Q ⥤ 𝒞/U ×_{𝒞/W} 𝒞/V`: an object `c : T ⟶ Q` goes to the pair of
its two components, with the identity of `T` as comparison isomorphism. -/
@[simps! obj_base obj_x obj_y map_hbase]
def slicePullback : Over Q ⥤ SlicePullback a b where
  obj c :=
    { base := c.left
      x := Over.mk (c.hom ≫ p)
      y := Over.mk (c.hom ≫ q)
      hx := rfl
      hy := rfl
      iso := Over.isoMk (Iso.refl c.left) (by simp [Category.assoc, h.w])
      vertical :=
        IsHomLift.of_fac' (Over.forget W) (𝟙 c.left) _ rfl rfl (by simp) }
  map {c c'} f :=
    { hbase := f.left
      a := Over.homMk f.left (by simp only [Over.mk_hom, ← Category.assoc, Over.w])
      b := Over.homMk f.left (by simp only [Over.mk_hom, ← Category.assoc, Over.w])
      ha := IsHomLift.of_fac' (Over.forget U) f.left _ rfl rfl (by simp)
      hb := IsHomLift.of_fac' (Over.forget V) f.left _ rfl rfl (by simp)
      w := by apply Over.OverMorphism.ext; simp }
  map_id c := by
    refine Hom.ext' ?_ ?_ <;> (apply Over.OverMorphism.ext; simp)
  map_comp f g := by
    refine Hom.ext' ?_ ?_ <;> (apply Over.OverMorphism.ext; simp)

attribute [local implicit_reducible] slicePullback

/-- The `𝒞/U`-component of the image of a morphism `f` is `f` itself. -/
@[simp] theorem slicePullback_map_a_left {c c' : Over Q} (f : c ⟶ c') :
    ((slicePullback h).map f).a.left = f.left := rfl

/-- The `𝒞/V`-component of the image of a morphism `f` is `f` itself. -/
@[simp] theorem slicePullback_map_b_left {c c' : Over Q} (f : c ⟶ c') :
    ((slicePullback h).map f).b.left = f.left := rfl

/-- The comparison functor is strictly a 1-morphism of categories over `𝒞`. -/
theorem slicePullback_comp_structureFunctor :
    slicePullback h ⋙ structureFunctor (Over.forget U) (Over.forget V) (Over.forget W)
        (Over.map a) (Over.map b) = Over.forget Q := rfl

/-- The `𝒞/U`-component of a morphism of `SlicePullback a b` is given by its base morphism. -/
private theorem hom_a_left {P P' : SlicePullback a b} (φ : P ⟶ P') :
    (Over.forget U).map φ.a = eqToHom P.hx ≫ φ.hbase ≫ eqToHom P'.hx.symm := by
  have := φ.ha
  exact IsHomLift.fac' (Over.forget U) φ.hbase φ.a

/-- The `𝒞/V`-component of a morphism of `SlicePullback a b` is given by its base morphism. -/
private theorem hom_b_left {P P' : SlicePullback a b} (φ : P ⟶ P') :
    (Over.forget V).map φ.b = eqToHom P.hy ≫ φ.hbase ≫ eqToHom P'.hy.symm := by
  have := φ.hb
  exact IsHomLift.fac' (Over.forget V) φ.hbase φ.b

/-- The comparison functor `slicePullback h` is faithful. -/
instance : (slicePullback h).Faithful where
  map_injective {c c'} {f g} hfg := by
    have hb : ((slicePullback h).map f).hbase = ((slicePullback h).map g).hbase := by rw [hfg]
    exact Over.OverMorphism.ext hb

/-- The comparison functor `slicePullback h` is full. -/
instance : (slicePullback h).Full where
  map_surjective {c c'} φ := by
    have ha := hom_a_left φ
    have hb := hom_b_left φ
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at ha hb
    have hwa : φ.hbase ≫ c'.hom ≫ p = c.hom ≫ p := by
      rw [← ha]; exact Over.w φ.a
    have hwb : φ.hbase ≫ c'.hom ≫ q = c.hom ≫ q := by
      rw [← hb]; exact Over.w φ.b
    have key : φ.hbase ≫ c'.hom = c.hom := by
      refine h.hom_ext ?_ ?_
      · rw [Category.assoc]; exact hwa
      · rw [Category.assoc]; exact hwb
    refine ⟨Over.homMk φ.hbase key, ?_⟩
    refine Hom.ext' ?_ ?_ <;> (apply Over.OverMorphism.ext)
    · simpa using ha.symm
    · simpa using hb.symm

/-- The comparison functor `slicePullback h` is essentially surjective. -/
instance : (slicePullback h).EssSurj where
  mem_essImage P := by
    set k : P.base ⟶ Q := h.lift (eqToHom P.hx.symm ≫ P.x.hom) (eqToHom P.hy.symm ≫ P.y.hom)
      (slicePullback_comp_eq P) with hkdef
    have hkp : k ≫ p = eqToHom P.hx.symm ≫ P.x.hom := h.lift_fst _ _ _
    have hkq : k ≫ q = eqToHom P.hy.symm ≫ P.y.hom := h.lift_snd _ _ _
    refine ⟨Over.mk k, ⟨?_⟩⟩
    refine isoMkVertical (U := P.base)
      { hom := Over.homMk (eqToHom P.hx.symm) (show _ = k ≫ p from hkp.symm)
        inv := Over.homMk (eqToHom P.hx)
          (show eqToHom P.hx ≫ k ≫ p = _ by rw [hkp]; simp)
        hom_inv_id := by apply Over.OverMorphism.ext; simp
        inv_hom_id := by apply Over.OverMorphism.ext; simp }
      { hom := Over.homMk (eqToHom P.hy.symm) (show _ = k ≫ q from hkq.symm)
        inv := Over.homMk (eqToHom P.hy)
          (show eqToHom P.hy ≫ k ≫ q = _ by rw [hkq]; simp)
        hom_inv_id := by apply Over.OverMorphism.ext; simp
        inv_hom_id := by apply Over.OverMorphism.ext; simp }
      (IsHomLift.of_fac' (Over.forget U) (𝟙 P.base) _ rfl P.hx (by simp))
      (IsHomLift.of_fac' (Over.forget V) (𝟙 P.base) _ rfl P.hy (by simp)) ?_
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, slicePullback_iso_hom_left, Over.map_map_left,
      Over.homMk_left, eqToHom_trans]

/-- **The slice over a fibre product is the 2-fibre product of the slices.** -/
instance instIsEquivalenceSlicePullback : (slicePullback h).IsEquivalence :=
  Functor.IsEquivalence.mk

end CategoryTheory.TwoFibreProductOver

end
