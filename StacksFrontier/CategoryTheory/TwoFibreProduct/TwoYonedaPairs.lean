module

public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# The 2-fibre product of two represented slices, and the pairs of morphisms it classifies

Let `p : 𝒳 ⥤ 𝒞` be a category fibred in groupoids, let `U`, `U'` be objects of `𝒞` and let `x`,
`x'` be objects of the fibres `𝒳_U`, `𝒳_{U'}`. The 2-Yoneda lemma (Stacks 004B) turns `x` and
`x'` into 1-morphisms `𝒞/U ⟶ 𝒳` and `𝒞/U' ⟶ 𝒳` over `𝒞`, namely
`CategoryTheory.Functor.TwoYoneda.liftFunctor`, and this file describes the 2-fibre product

```text
U ×_{x, 𝒳, x'} U'
```

of the resulting cospan, in the (2,1)-category of categories over `𝒞` — that is, the category
`CategoryTheory.TwoFibreProductOver` of Stacks 0040 taken at the two represented slices.

An object of that 2-fibre product is a quadruple `(T, a, b, φ)` with `T` an object of `𝒞`,
`a : T ⟶ U` and `b : T ⟶ U'` morphisms of `𝒞` and `φ : a^*x ≅ b^*x'` an isomorphism of `𝒳`
vertical over `T`, where `a^*x` is the chosen pullback `liftFunctor` makes. Such a quadruple is
the same thing as a pair of morphisms of `𝒳` out of one object lying over `T`: one morphism to
`x` and one to `x'`.

* From a quadruple to a pair: the two morphisms out of `a^*x` are the chosen cartesian arrow to
  `x`, and the comparison isomorphism followed by the chosen cartesian arrow to `x'`. A morphism
  of quadruples induces a morphism of `𝒳` compatible with both.
* From a pair to a quadruple: a pair `α : y ⟶ x`, `β : y ⟶ x'` determines a quadruple and an
  identification of `y` with the object the quadruple classifies, compatibly with both morphisms.
  Every pair arises this way, with the quadruple lying over `p y`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.twoYonedaPair`: the 2-fibre product of the two slices
  represented by `x` and `x'`.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaPair.chosenHom`: the chosen cartesian arrow
  `a^*x ⟶ x` of the 2-Yoneda functor, with its source spelled as a value of that functor.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaPair.objOf`, `.fstHom`, `.sndHom`: the object of
  `𝒳` a quadruple classifies and the two morphisms out of it.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaPair.quadruple`: the quadruple of a pair of
  morphisms.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaPair.fstIso`: the identification of the source of
  a pair with the object its quadruple classifies.

## Main results

* `CategoryTheory.TwoFibreProductOver.TwoYonedaPair.map_comp_chosenHom`: the chosen cartesian
  arrows are compatible with the functor assembled from them.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaPair.map_comp_fstHom`,
  `.map_comp_sndHom`: the pair attached to a quadruple is functorial in the quadruple.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaPair.fstIso_hom_comp_fstHom`,
  `.fstIso_hom_comp_sndHom`: the pair attached to the quadruple of a pair is the original pair.
* `CategoryTheory.TwoFibreProductOver.TwoYonedaPair.exists_quadruple_of_hom_pair`: every pair of
  morphisms out of an object of `𝒳` arises from a quadruple lying over the image of that object.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 02Y5](https://stacks.math.columbia.edu/tag/02Y5)
-/


@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

attribute [local implicit_reducible] Functor.Fiber

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒞}
  (hp : p.IsFiberedInGroupoids) {U U' : 𝒞} (x : p.Fiber U) (x' : p.Fiber U')

include hp

/-- The 2-fibre product `U ×_{x, 𝒳, x'} U'` of the two slices represented by `x : 𝒳_U` and
`x' : 𝒳_{U'}` through the 2-Yoneda lemma, in the (2,1)-category of categories over `𝒞`.

Its objects are the quadruples `(T, a, b, φ)` of Stacks 0040: an object `T` of `𝒞`, morphisms
`a : T ⟶ U` and `b : T ⟶ U'`, and an isomorphism `φ : a^*x ≅ b^*x'` of `𝒳` vertical over `T`,
the pullbacks being the ones the chosen lifts of `CategoryTheory.Functor.TwoYoneda.liftFunctor`
provide. -/
abbrev twoYonedaPair : Type max u₁ v₁ v₂ :=
  TwoFibreProductOver (Over.forget U) (Over.forget U') p
    (Functor.TwoYoneda.liftFunctor p hp U x) (Functor.TwoYoneda.liftFunctor p hp U' x')

namespace TwoYonedaPair

/-- The chosen cartesian arrow `a^*x ⟶ x` attached by
`CategoryTheory.Functor.TwoYoneda.liftFunctor` to an object `a` of the slice `𝒞/U`, with its
source spelled as the value of that functor at `a`. -/
def chosenHom (a : Over U) : (Functor.TwoYoneda.liftFunctor p hp U x).obj a ⟶ x.1 :=
  (Functor.TwoYoneda.chosenLift p hp U x a).φ

/-- The chosen cartesian arrow is strongly cartesian over the structure morphism of `a`. -/
instance isStronglyCartesian_chosenHom (a : Over U) :
    p.IsStronglyCartesian a.hom (chosenHom hp x a) :=
  (Functor.TwoYoneda.chosenLift p hp U x a).isStronglyCartesian

/-- The chosen cartesian arrows are compatible with the functor assembled from them: for a
morphism `g : a ⟶ a'` of the slice `𝒞/U`, the arrow `liftFunctor` attaches to `g` factors the
chosen cartesian arrow at `a` through the one at `a'`. -/
theorem map_comp_chosenHom {a a' : Over U} (g : a ⟶ a') :
    (Functor.TwoYoneda.liftFunctor p hp U x).map g ≫ chosenHom hp x a' = chosenHom hp x a := by
  rw [Functor.TwoYoneda.liftFunctor_map]
  exact Functor.IsStronglyCartesian.fac p a'.hom
    (Functor.TwoYoneda.chosenLift p hp U x a').φ (Over.w g).symm
    (Functor.TwoYoneda.chosenLift p hp U x a).φ

/-- The object of `𝒳` a quadruple of `U ×_{x, 𝒳, x'} U'` classifies: the chosen pullback `a^*x`
of `x` along the first component `a` of the quadruple. It lies over the base object of the
quadruple. -/
abbrev objOf (P : twoYonedaPair hp x x') : 𝒳 :=
  (Functor.TwoYoneda.liftFunctor p hp U x).obj P.x

/-- The first of the two morphisms a quadruple of `U ×_{x, 𝒳, x'} U'` classifies: the chosen
cartesian arrow `a^*x ⟶ x`, which lies over the first component `a` of the quadruple. -/
def fstHom (P : twoYonedaPair hp x x') : objOf hp x x' P ⟶ x.1 :=
  chosenHom hp x P.x

/-- The second of the two morphisms a quadruple of `U ×_{x, 𝒳, x'} U'` classifies: the
comparison isomorphism `a^*x ≅ b^*x'` of the quadruple followed by the chosen cartesian arrow
`b^*x' ⟶ x'`. It lies over the second component `b` of the quadruple, the comparison
isomorphism being vertical. -/
def sndHom (P : twoYonedaPair hp x x') : objOf hp x x' P ⟶ x'.1 :=
  P.iso.hom ≫ chosenHom hp x' P.y

/-- A morphism of quadruples carries the first classified morphism of its source to the first
classified morphism of its target. -/
theorem map_comp_fstHom {P Q : twoYonedaPair hp x x'} (ψ : P ⟶ Q) :
    (Functor.TwoYoneda.liftFunctor p hp U x).map ψ.a ≫ fstHom hp x x' Q = fstHom hp x x' P :=
  map_comp_chosenHom hp x ψ.a

/-- A morphism of quadruples carries the second classified morphism of its source to the second
classified morphism of its target. -/
theorem map_comp_sndHom {P Q : twoYonedaPair hp x x'} (ψ : P ⟶ Q) :
    (Functor.TwoYoneda.liftFunctor p hp U x).map ψ.a ≫ sndHom hp x x' Q = sndHom hp x x' P := by
  have hw : (Functor.TwoYoneda.liftFunctor p hp U x).map ψ.a ≫ Q.iso.hom =
      P.iso.hom ≫ (Functor.TwoYoneda.liftFunctor p hp U' x').map ψ.b := ψ.w
  rw [sndHom, sndHom, ← Category.assoc, hw, Category.assoc, map_comp_chosenHom hp x' ψ.b]

section Quadruple

variable {y : 𝒳} (a : Over U) (b : Over U') (hb : b.left = a.left) (α : y ⟶ x.1) (β : y ⟶ x'.1)

section

variable [p.IsHomLift a.hom α]

/-- The identification of the source of a pair of morphisms with the chosen pullback `a^*x`: the
unique isomorphism over the identity through which `α` factors as the chosen cartesian arrow
`a^*x ⟶ x`. -/
def fstIso : y ≅ (Functor.TwoYoneda.liftFunctor p hp U x).obj a :=
  have : p.IsStronglyCartesian a.hom α := hp.isStronglyCartesian_homLift a.hom α
  Functor.IsCartesian.domainUniqueUpToIso p a.hom (chosenHom hp x a) α

/-- The identification of the source of a pair of morphisms with the chosen pullback `a^*x` is
vertical: it lies over the identity of `a.left`. -/
instance isHomLift_fstIso_hom : p.IsHomLift (𝟙 a.left) (fstIso hp x a α).hom :=
  have : p.IsStronglyCartesian a.hom α := hp.isStronglyCartesian_homLift a.hom α
  Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift p a.hom (chosenHom hp x a) α

/-- The inverse of that identification is vertical as well. -/
instance isHomLift_fstIso_inv : p.IsHomLift (𝟙 a.left) (fstIso hp x a α).inv :=
  have : p.IsStronglyCartesian a.hom α := hp.isStronglyCartesian_homLift a.hom α
  Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift p a.hom (chosenHom hp x a) α

/-- The identification of the source of a pair with the chosen pullback factors the first
morphism of the pair through the chosen cartesian arrow. -/
@[simp]
theorem fstIso_hom_comp_chosenHom :
    (fstIso hp x a α).hom ≫ chosenHom hp x a = α :=
  have : p.IsStronglyCartesian a.hom α := hp.isStronglyCartesian_homLift a.hom α
  Functor.IsCartesian.fac p a.hom (chosenHom hp x a) α

end

variable [p.IsHomLift a.hom α] [p.IsHomLift b.hom β]

/-- The quadruple of a pair of morphisms: given morphisms `α : y ⟶ x` and `β : y ⟶ x'` of `𝒳`
lying over `a : T ⟶ U` and `b : T ⟶ U'`, the object of `U ×_{x, 𝒳, x'} U'` they determine. Its
base is `T`, its two components are `a` and `b`, and its comparison isomorphism is the composite
`a^*x ≅ y ≅ b^*x'` of the two identifications `α` and `β` provide. -/
def quadruple : twoYonedaPair hp x x' where
  base := a.left
  x := a
  y := b
  hx := rfl
  hy := hb
  iso := (fstIso hp x a α).symm ≪≫ fstIso hp x' b β
  vertical := by
    have h : p.IsHomLift (𝟙 a.left) (fstIso hp x' b β).hom := by
      rw [← hb]; infer_instance
    have h' : p.IsHomLift (𝟙 a.left ≫ 𝟙 a.left)
        ((fstIso hp x a α).inv ≫ (fstIso hp x' b β).hom) := inferInstance
    simpa using h'

/-- The base object of the quadruple of a pair is the common source of the two base
morphisms. -/
@[simp]
theorem quadruple_base : (quadruple hp x x' a b hb α β).base = a.left := rfl

/-- The object of `𝒳` the quadruple of a pair classifies is the chosen pullback `a^*x`. -/
theorem objOf_quadruple :
    objOf hp x x' (quadruple hp x x' a b hb α β) =
      (Functor.TwoYoneda.liftFunctor p hp U x).obj a :=
  rfl

/-- The first morphism attached to the quadruple of a pair `(α, β)`, read through the
identification `fstIso`, is `α`. -/
@[simp]
theorem fstIso_hom_comp_fstHom :
    (fstIso hp x a α).hom ≫ fstHom hp x x' (quadruple hp x x' a b hb α β) = α :=
  fstIso_hom_comp_chosenHom hp x a α

/-- The second morphism attached to the quadruple of a pair `(α, β)`, read through the
identification `fstIso`, is `β`. -/
@[simp]
theorem fstIso_hom_comp_sndHom :
    (fstIso hp x a α).hom ≫ sndHom hp x x' (quadruple hp x x' a b hb α β) = β := by
  show (fstIso hp x a α).hom ≫ ((fstIso hp x a α).symm ≪≫ fstIso hp x' b β).hom ≫
    chosenHom hp x' b = β
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact fstIso_hom_comp_chosenHom hp x' b β

end Quadruple

/-- Every pair of morphisms of `𝒳` out of one object comes from a quadruple over the image of
that object: given `α : y ⟶ x` and `β : y ⟶ x'`, there is an object `P` of `U ×_{x, 𝒳, x'} U'`
whose base is `p y`, together with an isomorphism `e` of `y` with the object `P` classifies
carrying the two morphisms `P` classifies back to `α` and `β`. -/
theorem exists_quadruple_of_hom_pair {y : 𝒳} (α : y ⟶ x.1) (β : y ⟶ x'.1) :
    ∃ (P : twoYonedaPair hp x x') (e : y ≅ objOf hp x x' P), P.base = p.obj y ∧
      e.hom ≫ fstHom hp x x' P = α ∧ e.hom ≫ sndHom hp x x' P = β := by
  have hliftα : p.IsHomLift (Over.mk (p.map α ≫ eqToHom x.2)).hom α :=
    IsHomLift.of_fac' p _ α rfl x.2 (by simp)
  have hliftβ : p.IsHomLift (Over.mk (p.map β ≫ eqToHom x'.2)).hom β :=
    IsHomLift.of_fac' p _ β rfl x'.2 (by simp)
  exact ⟨quadruple hp x x' (Over.mk (p.map α ≫ eqToHom x.2))
      (Over.mk (p.map β ≫ eqToHom x'.2)) rfl α β,
    fstIso hp x (Over.mk (p.map α ≫ eqToHom x.2)) α, rfl,
    fstIso_hom_comp_fstHom hp x x' _ _ rfl α β,
    fstIso_hom_comp_sndHom hp x x' _ _ rfl α β⟩

end TwoYonedaPair

end CategoryTheory.TwoFibreProductOver

end
