module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# The product over the base of two slices is the slice over the product

Fix a base category `𝒞` and two objects `U`, `V` of `𝒞` whose product `U ⨯ V` exists. The two
slices `𝒞/U` and `𝒞/V` are categories over `𝒞` through their forgetful functors, and their
product in the 2-category of categories over `𝒞` — the 2-fibre product
`CategoryTheory.TwoFibreProductOver` taken over the identity functor of `𝒞` — is the slice
`𝒞/(U ⨯ V)`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.SliceProd`: the product over `𝒞` of `𝒞/U` and `𝒞/V`.
* `CategoryTheory.TwoFibreProductOver.sliceProd`: the comparison functor from `𝒞/(U ⨯ V)`,
  sending an object `c : T ⟶ U ⨯ V` to the pair of its two components with the identity
  comparison isomorphism.

## Main results

* `CategoryTheory.TwoFibreProductOver.sliceProd_comp_structureFunctor`: the comparison functor
  is strictly a 1-morphism over `𝒞`.
* `CategoryTheory.TwoFibreProductOver.instIsEquivalenceSliceProd`: it is an equivalence.

## Implementation notes

The comparison isomorphism of an object of a product over `𝒞` is forced to be the canonical
`eqToHom` between the images of the two components
(`CategoryTheory.TwoFibreProductOver.prodOver_iso_hom`), because verticality for the identity
structure functor leaves no room; that is why the functor can put `Iso.refl` in that field and
why essential surjectivity needs no choice beyond `CategoryTheory.Limits.prod.lift`.

Equivalence is proved by fully faithful plus essentially surjective rather than by an explicit
quasi-inverse: the round trip through `prod.lift` replaces an object `(T, a, b, φ)` by
`(T, ⟨a, b⟩ ≫ pr₁, ⟨a, b⟩ ≫ pr₂, 𝟙)`, and the two differ by the `eqToHom`s recording that the
two components lie over `T`, so the unit would carry those anyway.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoFibreProductOver

universe v₁ u₁

attribute [local implicit_reducible] fst snd structureFunctor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] (U V : 𝒞) [HasBinaryProduct U V]

/-- The product over `𝒞` of the two slices `𝒞/U` and `𝒞/V`, i.e. the 2-fibre product of their
forgetful functors over the identity functor of `𝒞`. -/
abbrev SliceProd : Type _ :=
  TwoFibreProductOver (Over.forget U) (Over.forget V) (𝟭 𝒞) (Over.forget U) (Over.forget V)

/-- The comparison functor `𝒞/(U ⨯ V) ⥤ 𝒞/U × 𝒞/V`: an object `c : T ⟶ U ⨯ V` goes to the pair
of its two components, with the identity as comparison isomorphism. -/
noncomputable def sliceProd : Over (U ⨯ V) ⥤ SliceProd U V where
  obj c :=
    { base := c.left
      x := Over.mk (c.hom ≫ prod.fst)
      y := Over.mk (c.hom ≫ prod.snd)
      hx := rfl
      hy := rfl
      iso := Iso.refl c.left
      vertical :=
        IsHomLift.of_fac' (𝟭 𝒞) (𝟙 c.left) (Iso.refl c.left).hom rfl rfl (by simp) }
  map {c c'} f :=
    { hbase := f.left
      a := Over.homMk f.left (by simp only [Over.mk_hom, ← Category.assoc, Over.w])
      b := Over.homMk f.left (by simp only [Over.mk_hom, ← Category.assoc, Over.w])
      ha := IsHomLift.of_fac' (Over.forget U) f.left _ rfl rfl (by simp)
      hb := IsHomLift.of_fac' (Over.forget V) f.left _ rfl rfl (by simp)
      w := by simp }
  map_id c := by
    refine Hom.ext' ?_ ?_ <;> (apply Over.OverMorphism.ext; simp)
  map_comp f g := by
    refine Hom.ext' ?_ ?_ <;> (apply Over.OverMorphism.ext; simp)

attribute [local implicit_reducible] sliceProd

/-- The base of the image of `c` is the source of `c`. -/
@[simp] lemma sliceProd_obj_base (c : Over (U ⨯ V)) : ((sliceProd U V).obj c).base = c.left := rfl

/-- The `𝒞/U`-component of the image of `c` is the first component of `c`. -/
@[simp] lemma sliceProd_obj_x (c : Over (U ⨯ V)) :
    ((sliceProd U V).obj c).x = Over.mk (c.hom ≫ prod.fst) := rfl

/-- The `𝒞/V`-component of the image of `c` is the second component of `c`. -/
@[simp] lemma sliceProd_obj_y (c : Over (U ⨯ V)) :
    ((sliceProd U V).obj c).y = Over.mk (c.hom ≫ prod.snd) := rfl

/-- The comparison isomorphism of the image of `c` is the identity. -/
@[simp] lemma sliceProd_obj_iso (c : Over (U ⨯ V)) :
    ((sliceProd U V).obj c).iso = Iso.refl c.left := rfl

/-- The base morphism of the image of `f` is `f` itself. -/
@[simp] lemma sliceProd_map_hbase {c c' : Over (U ⨯ V)} (f : c ⟶ c') :
    ((sliceProd U V).map f).hbase = f.left := rfl

/-- The `𝒞/U`-component of the image of `f` is `f` itself. -/
@[simp] lemma sliceProd_map_a_left {c c' : Over (U ⨯ V)} (f : c ⟶ c') :
    ((sliceProd U V).map f).a.left = f.left := rfl

/-- The `𝒞/V`-component of the image of `f` is `f` itself. -/
@[simp] lemma sliceProd_map_b_left {c c' : Over (U ⨯ V)} (f : c ⟶ c') :
    ((sliceProd U V).map f).b.left = f.left := rfl

/-- The comparison functor is strictly a 1-morphism of categories over `𝒞`. -/
lemma sliceProd_comp_structureFunctor :
    sliceProd U V ⋙ structureFunctor (Over.forget U) (Over.forget V) (𝟭 𝒞)
        (Over.forget U) (Over.forget V) = Over.forget (U ⨯ V) := rfl

omit [HasBinaryProduct U V] in
/-- The `𝒞/U`-component of a morphism of `𝒞/U × 𝒞/V` is given by the base morphism. -/
private lemma hom_a_left {P Q : SliceProd U V} (φ : P ⟶ Q) :
    (Over.forget U).map φ.a = eqToHom P.hx ≫ φ.hbase ≫ eqToHom Q.hx.symm := by
  have := φ.ha
  exact IsHomLift.fac' (Over.forget U) φ.hbase φ.a

omit [HasBinaryProduct U V] in
/-- The `𝒞/V`-component of a morphism of `𝒞/U × 𝒞/V` is given by the base morphism. -/
private lemma hom_b_left {P Q : SliceProd U V} (φ : P ⟶ Q) :
    (Over.forget V).map φ.b = eqToHom P.hy ≫ φ.hbase ≫ eqToHom Q.hy.symm := by
  have := φ.hb
  exact IsHomLift.fac' (Over.forget V) φ.hbase φ.b

/-- The comparison functor `sliceProd U V` is faithful. -/
instance : (sliceProd U V).Faithful where
  map_injective {c c'} {f g} h := by
    have hb : ((sliceProd U V).map f).hbase = ((sliceProd U V).map g).hbase := by rw [h]
    exact Over.OverMorphism.ext hb

/-- The comparison functor `sliceProd U V` is full. -/
instance : (sliceProd U V).Full where
  map_surjective {c c'} φ := by
    have ha := hom_a_left U V φ
    have hb := hom_b_left U V φ
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at ha hb
    have hwa : φ.hbase ≫ c'.hom ≫ prod.fst = c.hom ≫ prod.fst := by
      have h := Over.w φ.a
      simp only [sliceProd_obj_x, Over.mk_hom] at h
      rw [← ha]
      exact h
    have hwb : φ.hbase ≫ c'.hom ≫ prod.snd = c.hom ≫ prod.snd := by
      have h := Over.w φ.b
      simp only [sliceProd_obj_y, Over.mk_hom] at h
      rw [← hb]
      exact h
    have key : φ.hbase ≫ c'.hom = c.hom := by
      refine prod.hom_ext ?_ ?_
      · rw [Category.assoc]; exact hwa
      · rw [Category.assoc]; exact hwb
    refine ⟨Over.homMk φ.hbase key, ?_⟩
    refine Hom.ext' ?_ ?_ <;> (apply Over.OverMorphism.ext)
    · simpa using ha.symm
    · simpa using hb.symm

/-- The comparison functor `sliceProd U V` is essentially surjective. -/
instance : (sliceProd U V).EssSurj where
  mem_essImage P := by
    refine ⟨Over.mk (prod.lift (eqToHom P.hx.symm ≫ P.x.hom) (eqToHom P.hy.symm ≫ P.y.hom)),
      ⟨?_⟩⟩
    refine isoMkVertical (U := P.base)
      { hom := Over.homMk (eqToHom P.hx.symm) (by simp)
        inv := Over.homMk (eqToHom P.hx) (by simp)
        hom_inv_id := by apply Over.OverMorphism.ext; simp
        inv_hom_id := by apply Over.OverMorphism.ext; simp }
      { hom := Over.homMk (eqToHom P.hy.symm) (by simp)
        inv := Over.homMk (eqToHom P.hy) (by simp)
        hom_inv_id := by apply Over.OverMorphism.ext; simp
        inv_hom_id := by apply Over.OverMorphism.ext; simp }
      (IsHomLift.of_fac' (Over.forget U) (𝟙 P.base) _ rfl P.hx (by simp))
      (IsHomLift.of_fac' (Over.forget V) (𝟙 P.base) _ rfl P.hy (by simp)) ?_
    rw [prodOver_iso_hom P]
    simp

/-- The comparison functor `sliceProd U V` is an equivalence of categories. -/
instance instIsEquivalenceSliceProd : (sliceProd U V).IsEquivalence :=
  Functor.IsEquivalence.mk

end CategoryTheory.TwoFibreProductOver

end
