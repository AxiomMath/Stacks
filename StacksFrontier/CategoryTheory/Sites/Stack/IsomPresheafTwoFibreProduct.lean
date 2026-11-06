module

public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf

/-!
# `Isom(x, y)` as a 2-fibre product

Let `𝒞` be a category, let `p : 𝒮 ⥤ 𝒞` be a fibred category (Stacks 02XJ), let `U` be an object of
`𝒞` and let `x`, `y` be objects of the fibre category `𝒮_U`. Write `x`, `y : 𝒞/U ⥤ 𝒮` also for the
1-morphisms attached to them by the 2-Yoneda lemma (Stacks 004B), namely `(a : V ⟶ U) ↦ a^* x`.
Stacks 04SI says that the 2-fibre product `𝒮 ×_{𝒮 × 𝒮, (x, y)} 𝒞/U` is fibred in setoids over
`𝒞/U` (Stacks 04SA), and that the presheaf of sets it corresponds to under Stacks 04SC — the
presheaf `a ↦ Ob(fibre over a)/≅` of isomorphism classes of the objects of its fibres — is the
presheaf of isomorphisms `Isom(x, y)` of Stacks 02ZB.

An object of that 2-fibre product lying over `a : V ⟶ U` is a triple `(z, α, β)` with `z` an object
of `𝒮_V` and `α : z ≅ a^* x`, `β : z ≅ a^* y` isomorphisms of `𝒮_V`, and the identification of the
second part sends the class of such a triple to the isomorphism `β ∘ α⁻¹` of `a^* x` with `a^* y`,
which is a section of `Isom(x, y)` over `a`.

## Main results

* `CategoryTheory.Functor.IsomPresheafTwoFibreProduct.proj_isFiberedInSetoids`: Stacks 04SI (1).
* `CategoryTheory.Functor.IsomPresheafTwoFibreProduct.presheafIso`: Stacks 04SI (2), an
  isomorphism of presheaves and so data, not a mere assertion that the two presheaves are
  isomorphic.
* `CategoryTheory.Functor.isFiberedInSetoids_and_isoClassPresheaf_iso_isomPresheaf`: Stacks 04SI,
  the two parts together, the isomorphism of the second pinned by its value `β ∘ α⁻¹` on the class
  of `(z, α, β)`.

## Implementation notes

The source's `𝒮 × 𝒮` is the product in the 2-category of categories over `𝒞`, that is the 2-fibre
product `𝒮 ×_𝒞 𝒮`, and `𝒮 ×_{𝒮 × 𝒮, (x, y)} 𝒞/U` is the 2-fibre product of Stacks 0040 taken in
that 2-category: its structural isomorphism is required to be *vertical*, which is what the
source's own description of the objects as triples `(z, α, β)` with `α`, `β` isomorphisms of the
fibre `𝒮_V` records. That category is `CategoryTheory.TwoFibreProductOver` for the base `𝒞 × 𝒞`,
with `𝒮` and `𝒞/U` over `𝒞 × 𝒞` diagonally (`p.prod' p` and `(Over.forget U).prod' (Over.forget
U)`) and `𝒮 × 𝒮` over `𝒞 × 𝒞` by `p.prod p`: an object is then a pair of objects `z` of `𝒮` and
`a` of `𝒞/U` lying over one and the same `(V, V)`, together with an isomorphism
`(z, z) ≅ (a^* x, a^* y)` of `𝒮 × 𝒮` lying over `𝟙 (V, V)`, which is precisely a pair of vertical
isomorphisms `α`, `β`; and a morphism is a pair `(φ, g)` lying over a single morphism `(g, g)` of
`𝒞 × 𝒞`, that is `φ` lying over `g`. Doubling the base is what lets the *one* structure functor
`p.prod p` impose verticality on both components at once; Mathlib's
`CategoryTheory.Limits.CategoricalPullback` is built from arbitrary isomorphisms and is a different
category, whose presheaf of isomorphism classes is `a ↦ Iso_𝒮(a^* x, a^* y)`, all isomorphisms and
not only the vertical ones.

The projection to `𝒞/U` is `CategoryTheory.TwoFibreProductOver.snd`, `𝒞/U` being the second
factor. The presheaf of Stacks 04SC is `CategoryTheory.Functor.isoClassPresheaf` of that
projection, which needs it to be a fibred category; that instance is
`CategoryTheory.Functor.IsomPresheafTwoFibreProduct.proj_isFibered`, read off the first part, as
it must be, the first part being what provides it.

The 1-morphisms `𝒞/U ⥤ 𝒮` of Stacks 004B are
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` for Mathlib's canonical choice of pullbacks
`CategoryTheory.Functor.chosenPullbacks`, so that their values `a^* x` are the chosen pullbacks out
of which `CategoryTheory.Functor.isomPresheaf` is built, and the two sides of the second part are
presheaves of sections of literally the same morphisms.

The presheaves live in different universes — the objects of the 2-fibre product involve those of
`𝒞`, of `𝒮` and of `𝒞/U`, while a section of `Isom(x, y)` is a morphism of `𝒮` — so the comparison
is with `Isom(x, y)` composed with `CategoryTheory.uliftFunctor`. A section of `Isom(x, y)` over
`a` is a morphism of the fibre `𝒮_{V}` between the chosen pullbacks which is an isomorphism, so
`.down.1.1` is the underlying morphism of `𝒮` of such a section: `ULift.down`, then the inclusion
of the subpresheaf `Isom(x, y) ⊆ Mor(x, y)`, then the inclusion of the fibre into `𝒮`.

## References

* [StacksProject 04SI](https://stacks.math.columbia.edu/tag/04SI)
-/


@[expose] public section

open Opposite

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-! ### The 2-fibre product `𝒮 ×_{𝒮 × 𝒮, (x, y)} 𝒞/U`

An explicit description of the objects and morphisms of the 2-fibre product
`𝒮 ×_{𝒮 × 𝒮, (x, y)} 𝒞/U`, the fact that its projection to `𝒞/U` is fibred in setoids, and the
comparison of its presheaf of isomorphism classes with `Isom(x, y)`.
-/

namespace IsomPresheafTwoFibreProduct

-- The projection of the 2-fibre product, the fibre of a functor and its inclusion, and the
-- 1-morphisms `𝒞/U ⥤ 𝒮` are plain `def`s, so the objects and morphisms of the fibres of the
-- projection are only type-correct after unfolding them.
set_option backward.isDefEq.respectTransparency false

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  TwoFibreProductOver.snd Functor.ChoiceOfPullbacks.sliceFunctor

noncomputable section

/-! #### `IsHomLift` in a product of categories -/

variable (p : 𝒮 ⥤ 𝒞)

/-- The first component of a morphism lifting a morphism of `𝒞 × 𝒞` through `p × p` lifts the
first component. -/
private lemma isHomLift_prod_fst {R S : 𝒞 × 𝒞} {u v : 𝒮 × 𝒮} {f : R ⟶ S} {φ : u ⟶ v}
    (h : (p.prod p).IsHomLift f φ) : p.IsHomLift f.1 φ.1 := by
  obtain ⟨⟩ := h
  exact .map _

/-- The second component of a morphism lifting a morphism of `𝒞 × 𝒞` through `p × p` lifts the
second component. -/
private lemma isHomLift_prod_snd {R S : 𝒞 × 𝒞} {u v : 𝒮 × 𝒮} {f : R ⟶ S} {φ : u ⟶ v}
    (h : (p.prod p).IsHomLift f φ) : p.IsHomLift f.2 φ.2 := by
  obtain ⟨⟩ := h
  exact .map _

/-- A pair of morphisms lifting a pair of morphisms lifts the pair through `p × p`. -/
private lemma isHomLift_prod_mk {R S R' S' : 𝒞} {u v u' v' : 𝒮} {f : R ⟶ S} {g : R' ⟶ S'}
    {φ : u ⟶ v} {ψ : u' ⟶ v'} (hf : p.IsHomLift f φ) (hg : p.IsHomLift g ψ) :
    (p.prod p).IsHomLift (Prod.mkHom f g) (Prod.mkHom φ ψ) := by
  obtain ⟨⟩ := hf
  obtain ⟨⟩ := hg
  exact .map (Prod.mkHom φ ψ)

/-! #### The 2-fibre product and its projection -/

variable [p.IsFibered] {U : 𝒞} (x y : p.Fiber U)

/-- The 2-fibre product `𝒮 ×_{𝒮 × 𝒮, (x, y)} 𝒞/U` of Stacks 04SI. -/
noncomputable abbrev Tot :=
  TwoFibreProductOver (p.prod' p) ((Over.forget U).prod' (Over.forget U)) (p.prod p)
    (Functor.diag 𝒮)
    ((p.chosenPullbacks.sliceFunctor x).prod' (p.chosenPullbacks.sliceFunctor y))

/-- The projection of the 2-fibre product of Stacks 04SI to the slice `𝒞/U`. -/
noncomputable abbrev proj : Tot p x y ⥤ Over U :=
  TwoFibreProductOver.snd (p.prod' p) ((Over.forget U).prod' (Over.forget U)) (p.prod p)
    (Functor.diag 𝒮)
    ((p.chosenPullbacks.sliceFunctor x).prod' (p.chosenPullbacks.sliceFunctor y))

/-- The transition maps of the 1-morphism `𝒞/U ⥤ 𝒮` attached to `z` are the restriction maps of
the chosen pullbacks of `z`. -/
private lemma sliceFunctor_map_eq (z : p.Fiber U) {a b : Over U} (h : a ⟶ b) :
    (p.chosenPullbacks.sliceFunctor z).map h = pullbackFiberMap p z h := rfl

/-! #### The two components of the comparison isomorphism of an object -/

variable {p x y}

/-- The isomorphism `α : z ≅ a^* x` recorded by an object of the 2-fibre product. -/
private def isoFst (P : Tot p x y) : P.x ≅ (pullbackFiber p x P.y.hom).1 :=
  (CategoryTheory.Prod.fst 𝒮 𝒮).mapIso P.iso

/-- The isomorphism `β : z ≅ a^* y` recorded by an object of the 2-fibre product. -/
private def isoSnd (P : Tot p x y) : P.x ≅ (pullbackFiber p y P.y.hom).1 :=
  (CategoryTheory.Prod.snd 𝒮 𝒮).mapIso P.iso

private lemma isHomLift_isoFst_hom (P : Tot p x y) : p.IsHomLift (𝟙 P.y.left) (isoFst P).hom := by
  obtain ⟨base, z, a, hx', hy', i, v⟩ := P
  subst hy'
  exact isHomLift_prod_fst p v

private lemma isHomLift_isoSnd_hom (P : Tot p x y) : p.IsHomLift (𝟙 P.y.left) (isoSnd P).hom := by
  obtain ⟨base, z, a, hx', hy', i, v⟩ := P
  subst hy'
  exact isHomLift_prod_snd p v

private lemma isHomLift_isoFst_inv (P : Tot p x y) : p.IsHomLift (𝟙 P.y.left) (isoFst P).inv := by
  obtain ⟨base, z, a, hx', hy', i, v⟩ := P
  subst hy'
  exact isHomLift_prod_fst p (@IsHomLift.lift_id_inv _ _ _ _ (p.prod p) _ _ _ i v)

private lemma isHomLift_isoSnd_inv (P : Tot p x y) : p.IsHomLift (𝟙 P.y.left) (isoSnd P).inv := by
  obtain ⟨base, z, a, hx', hy', i, v⟩ := P
  subst hy'
  exact isHomLift_prod_snd p (@IsHomLift.lift_id_inv _ _ _ _ (p.prod p) _ _ _ i v)

/-! #### The section of `Isom(x, y)` attached to an object -/

/-- The isomorphism `β ∘ α⁻¹ : a^* x ⟶ a^* y` attached to an object of the 2-fibre product. -/
private def theta (P : Tot p x y) :
    (pullbackFiber p x P.y.hom).1 ⟶ (pullbackFiber p y P.y.hom).1 :=
  (isoFst P).inv ≫ (isoSnd P).hom

private lemma isHomLift_theta (P : Tot p x y) : p.IsHomLift (𝟙 P.y.left) (theta P) :=
  isHomLift_id_comp p _ _ (isHomLift_isoFst_inv P) (isHomLift_isoSnd_hom P)

/-- `β ∘ α⁻¹` as an isomorphism of the fibre `𝒮_{a.left}`, i.e. as a section of `Isom(x, y)`. -/
private def thetaFibIso (P : Tot p x y) :
    pullbackFiber p x P.y.hom ≅ pullbackFiber p y P.y.hom :=
  Fiber.isoMk ((isoFst P).symm ≪≫ isoSnd P) (isHomLift_theta P)

/-- The section of `Isom(x, y)` over `a` attached to an object of the 2-fibre product over `a`. -/
private def sect (P : Tot p x y) : (p.isomPresheaf x y).obj (op P.y) :=
  ⟨(thetaFibIso P).hom, inferInstanceAs (IsIso (thetaFibIso P).hom)⟩

@[simp] private lemma sect_val_val (P : Tot p x y) :
    (sect P).1.1 = (isoFst P).inv ≫ (isoSnd P).hom := rfl

private lemma isomPresheaf_map_val {a b : Over U} (h : a ⟶ b)
    (m : (p.isomPresheaf x y).obj (op b)) :
    ((p.isomPresheaf x y).map h.op m).1 = morRestrict p x y h m.1 := rfl

/-! #### Morphisms of the 2-fibre product -/

private lemma base_compat {P Q : Tot p x y} (χ : P.x ⟶ Q.x) (k : P.y ⟶ Q.y)
    (hχ : p.IsHomLift k.left χ) :
    eqToHom P.hy.symm ≫ ((Over.forget U).prod' (Over.forget U)).map k ≫ eqToHom Q.hy
      = eqToHom P.hx.symm ≫ (p.prod' p).map χ ≫ eqToHom Q.hx := by
  have := hχ
  have hfac := IsHomLift.fac' p k.left χ
  refine Prod.hom_ext ?_ ?_ <;>
    simp [hfac]

/-- A morphism of the 2-fibre product built from its two components. -/
private def homMk {P Q : Tot p x y} (χ : P.x ⟶ Q.x) (k : P.y ⟶ Q.y) (hχ : p.IsHomLift k.left χ)
    (w₁ : χ ≫ (isoFst Q).hom
      = (isoFst P).hom ≫ (p.chosenPullbacks.sliceFunctor x).map k)
    (w₂ : χ ≫ (isoSnd Q).hom
      = (isoSnd P).hom ≫ (p.chosenPullbacks.sliceFunctor y).map k) : P ⟶ Q :=
  TwoFibreProductOver.Hom.mk' χ k (base_compat χ k hχ) (Prod.hom_ext w₁ w₂)

@[simp] private lemma homMk_a {P Q : Tot p x y} (χ : P.x ⟶ Q.x) (k : P.y ⟶ Q.y) (hχ) (w₁) (w₂) :
    (homMk χ k hχ w₁ w₂).a = χ := rfl

@[simp] private lemma homMk_b {P Q : Tot p x y} (χ : P.x ⟶ Q.x) (k : P.y ⟶ Q.y) (hχ) (w₁) (w₂) :
    (homMk χ k hχ w₁ w₂).b = k := rfl

private lemma isHomLift_homMk {P Q : Tot p x y} (χ : P.x ⟶ Q.x) (k : P.y ⟶ Q.y) (hχ) (w₁) (w₂) :
    (proj p x y).IsHomLift k (homMk χ k hχ w₁ w₂) :=
  IsHomLift.of_fac' (proj p x y) k _ rfl rfl (by simp)

private lemma w_fst {P Q : Tot p x y} (Φ : P ⟶ Q) :
    Φ.a ≫ (isoFst Q).hom
      = (isoFst P).hom ≫ (p.chosenPullbacks.sliceFunctor x).map Φ.b := by
  simpa [isoFst] using congr_arg _root_.Prod.fst Φ.w

private lemma w_snd {P Q : Tot p x y} (Φ : P ⟶ Q) :
    Φ.a ≫ (isoSnd Q).hom
      = (isoSnd P).hom ≫ (p.chosenPullbacks.sliceFunctor y).map Φ.b := by
  simpa [isoSnd] using congr_arg _root_.Prod.snd Φ.w

/-- The `𝒮`-component of a morphism of the 2-fibre product is determined by its `𝒞/U`-component. -/
private lemma hom_a_eq {P Q : Tot p x y} (Φ : P ⟶ Q) :
    Φ.a = (isoFst P).hom ≫ (p.chosenPullbacks.sliceFunctor x).map Φ.b ≫ (isoFst Q).inv := by
  rw [← Category.assoc, ← w_fst Φ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma inv_comp_a {P Q : Tot p x y} (Φ : P ⟶ Q) :
    (isoFst P).inv ≫ Φ.a
      = (p.chosenPullbacks.sliceFunctor x).map Φ.b ≫ (isoFst Q).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact w_fst Φ

/-! #### Objects of the 2-fibre product from sections of `Isom(x, y)` -/

variable (p x y)

/-- The isomorphism `a^* x ≅ a^* y` of `𝒮` underlying a section of `Isom(x, y)` over `a`. -/
private def sectIso (a : Over U) (m : (p.isomPresheaf x y).obj (op a)) :
    (pullbackFiber p x a.hom).1 ≅ (pullbackFiber p y a.hom).1 :=
  haveI : IsIso m.1 := m.2
  Fiber.fiberInclusion.mapIso (asIso m.1)

/-- The object `(a^* x, 𝟙, m)` of the 2-fibre product attached to a section `m` of `Isom(x, y)`
over `a`. -/
private def obj' (a : Over U) (m : (p.isomPresheaf x y).obj (op a)) : Tot p x y where
  base := ((Over.forget U).prod' (Over.forget U)).obj a
  x := (pullbackFiber p x a.hom).1
  y := a
  hx := congrArg (fun t : 𝒞 => (t, t)) (pullbackFiber p x a.hom).2
  hy := rfl
  iso := Iso.prod (Iso.refl _) (sectIso p x y a m)
  vertical := isHomLift_prod_mk p (IsHomLift.id (pullbackFiber p x a.hom).2) m.1.2

@[simp] private lemma obj'_y (a : Over U) (m : (p.isomPresheaf x y).obj (op a)) :
    (obj' p x y a m).y = a := rfl

@[simp] private lemma isoFst_obj' (a : Over U) (m : (p.isomPresheaf x y).obj (op a)) :
    isoFst (obj' p x y a m) = Iso.refl _ := rfl

@[simp] private lemma isoSnd_obj'_hom (a : Over U) (m : (p.isomPresheaf x y).obj (op a)) :
    (isoSnd (obj' p x y a m)).hom = m.1.1 := rfl

private lemma sect_obj' (a : Over U) (m : (p.isomPresheaf x y).obj (op a)) :
    sect (obj' p x y a m) = m :=
  Subtype.ext (Subtype.ext (Category.id_comp _))

/-- A morphism `obj' a m ⟶ P` over `h : a ⟶ P.y`, given that `m` is compatible with the section
attached to `P`. -/
private def liftHom (P : Tot p x y) {a : Over U} (h : a ⟶ P.y)
    (m : (p.isomPresheaf x y).obj (op a))
    (hm : m.1.1 ≫ (p.chosenPullbacks.sliceFunctor y).map h
      = (p.chosenPullbacks.sliceFunctor x).map h ≫ theta P) :
    obj' p x y a m ⟶ P :=
  homMk ((p.chosenPullbacks.sliceFunctor x).map h ≫ (isoFst P).inv) h
    (by
      have := isHomLift_isoFst_inv P
      exact IsHomLift.comp_lift_id_right' p h.left _ P.y.left (isoFst P).inv)
    (by simp)
    (by rw [Category.assoc]; exact hm.symm)

private lemma isHomLift_liftHom (P : Tot p x y) {a : Over U} (h : a ⟶ P.y)
    (m : (p.isomPresheaf x y).obj (op a))
    (hm : m.1.1 ≫ (p.chosenPullbacks.sliceFunctor y).map h
      = (p.chosenPullbacks.sliceFunctor x).map h ≫ theta P) :
    (proj p x y).IsHomLift h (liftHom p x y P h m hm) :=
  IsHomLift.of_fac' (proj p x y) h _ rfl rfl (by simp [liftHom])

/-- The object of the 2-fibre product over `a` obtained by restricting `P` along `h : a ⟶ P.y`. -/
private def restrictObj (P : Tot p x y) {a : Over U} (h : a ⟶ P.y) : Tot p x y :=
  obj' p x y a ((p.isomPresheaf x y).map h.op (sect P))

/-- The cartesian morphism `restrictObj P h ⟶ P` over `h`. -/
private def restrictHom (P : Tot p x y) {a : Over U} (h : a ⟶ P.y) : restrictObj p x y P h ⟶ P :=
  liftHom p x y P h ((p.isomPresheaf x y).map h.op (sect P))
    (Functor.fiberInclusion_map_morRestrict_comp_pullbackFiberMap p x y h (sect P).1)

private lemma isHomLift_restrictHom (P : Tot p x y) {a : Over U} (h : a ⟶ P.y) :
    (proj p x y).IsHomLift h (restrictHom p x y P h) :=
  isHomLift_liftHom p x y P h _ _

/-! #### The projection is fibred in setoids -/

variable {p x y}

/-- The `x`-component `α_R ∘ (f^* x) ∘ α_Q⁻¹` of a transition between two objects lies over
`f.left`. -/
private lemma isHomLift_isoFst_transition {Q R : Tot p x y} (f : R.y ⟶ Q.y) :
    p.IsHomLift f.left
      ((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv) := by
  have hR := isHomLift_isoFst_hom R
  have hQ := isHomLift_isoFst_inv Q
  exact isHomLift_comp_of_isHomLift_id p _ _ f.left hR
    (IsHomLift.comp_lift_id_right' p f.left _ Q.y.left (isoFst Q).inv)

private lemma comp_a_eq {P Q R : Tot p x y} (Φ : Q ⟶ P) (Ψ : R ⟶ P) (f : R.y ⟶ Q.y)
    (hf : f ≫ Φ.b = Ψ.b) :
    ((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv) ≫ Φ.a
      = Ψ.a := by
  rw [Category.assoc, Category.assoc, inv_comp_a Φ, ← Category.assoc
    ((p.chosenPullbacks.sliceFunctor x).map f), ← Functor.map_comp, hf, ← Category.assoc,
    ← w_fst Ψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma w_snd_lift {P Q R : Tot p x y} (Φ : Q ⟶ P) (Ψ : R ⟶ P) (f : R.y ⟶ Q.y)
    (hf : f ≫ Φ.b = Ψ.b) :
    ((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv)
        ≫ (isoSnd Q).hom
      = (isoSnd R).hom ≫ (p.chosenPullbacks.sliceFunctor y).map f := by
  -- Both sides become equal after composing with the transition map along `Φ.b`.
  have key : (((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv)
        ≫ (isoSnd Q).hom) ≫ (p.chosenPullbacks.sliceFunctor y).map Φ.b
      = ((isoSnd R).hom ≫ (p.chosenPullbacks.sliceFunctor y).map f)
        ≫ (p.chosenPullbacks.sliceFunctor y).map Φ.b :=
    calc (((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv)
            ≫ (isoSnd Q).hom) ≫ (p.chosenPullbacks.sliceFunctor y).map Φ.b
        = ((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv)
            ≫ ((isoSnd Q).hom ≫ (p.chosenPullbacks.sliceFunctor y).map Φ.b) :=
          Category.assoc _ _ _
      _ = ((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv)
            ≫ (Φ.a ≫ (isoSnd P).hom) := by rw [w_snd Φ]
      _ = (((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv)
            ≫ Φ.a) ≫ (isoSnd P).hom := (Category.assoc _ _ _).symm
      _ = Ψ.a ≫ (isoSnd P).hom := by rw [comp_a_eq Φ Ψ f hf]
      _ = (isoSnd R).hom ≫ (p.chosenPullbacks.sliceFunctor y).map Ψ.b := w_snd Ψ
      _ = (isoSnd R).hom ≫ (p.chosenPullbacks.sliceFunctor y).map (f ≫ Φ.b) := by rw [hf]
      _ = ((isoSnd R).hom ≫ (p.chosenPullbacks.sliceFunctor y).map f)
            ≫ (p.chosenPullbacks.sliceFunctor y).map Φ.b := by
          rw [Functor.map_comp, Category.assoc]
  -- Both sides lie over `f.left`, so the strongly cartesian chosen lift separates them.
  have hSR := isHomLift_isoSnd_hom R
  have hSQ := isHomLift_isoSnd_hom Q
  have hχ := isHomLift_isoFst_transition f
  have hleft : p.IsHomLift f.left
      (((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv)
        ≫ (isoSnd Q).hom) :=
    IsHomLift.comp_lift_id_right' p f.left _ Q.y.left (isoSnd Q).hom
  have hright : p.IsHomLift f.left
      ((isoSnd R).hom ≫ (p.chosenPullbacks.sliceFunctor y).map f) :=
    isHomLift_comp_of_isHomLift_id p _ _ f.left hSR inferInstance
  refine IsStronglyCartesian.ext p Q.y.hom (IsPreFibered.pullbackMap y.2 Q.y.hom) f.left ?_
  have hfac : (p.chosenPullbacks.sliceFunctor y).map Φ.b
      ≫ IsPreFibered.pullbackMap y.2 P.y.hom = IsPreFibered.pullbackMap y.2 Q.y.hom :=
    Functor.ChoiceOfPullbacks.sliceFunctor_map_fac p.chosenPullbacks y Φ.b
  rw [← hfac,
    ← Category.assoc _ ((p.chosenPullbacks.sliceFunctor y).map Φ.b)
      (IsPreFibered.pullbackMap y.2 P.y.hom),
    ← Category.assoc _ ((p.chosenPullbacks.sliceFunctor y).map Φ.b)
      (IsPreFibered.pullbackMap y.2 P.y.hom), key]

private lemma proj_isFiberedInGroupoids (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) :
    (proj p x y).IsFiberedInGroupoids := by
  constructor
  · rintro V W f P rfl
    exact ⟨restrictObj p x y P f, restrictHom p x y P f, isHomLift_restrictHom p x y P f⟩
  · intro P Q R Φ Ψ f hf
    have hf' : f ≫ Φ.b = Ψ.b := hf
    have hχ := isHomLift_isoFst_transition f
    refine ⟨homMk ((isoFst R).hom ≫ (p.chosenPullbacks.sliceFunctor x).map f ≫ (isoFst Q).inv)
      f hχ (by simp) (w_snd_lift Φ Ψ f hf'), ⟨rfl, ?_⟩, ?_⟩
    · exact TwoFibreProductOver.Hom.ext' (comp_a_eq Φ Ψ f hf') hf'
    · rintro X ⟨hX₁, hX₂⟩
      have hXb : X.b = f := hX₁
      refine TwoFibreProductOver.Hom.ext' ?_ hXb
      rw [hom_a_eq X, hXb, homMk_a]

private lemma proj_fiber_isThin (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) (a : Over U) :
    Quiver.IsThin ((proj p x y).Fiber a) := by
  intro A B
  refine ⟨fun X X' => ?_⟩
  have hb : (Fiber.fiberInclusion.map X).b = (Fiber.fiberInclusion.map X').b :=
    (IsHomLift.fac' (proj p x y) (𝟙 a) (Fiber.fiberInclusion.map X)).trans
      (IsHomLift.fac' (proj p x y) (𝟙 a) (Fiber.fiberInclusion.map X')).symm
  refine Fiber.hom_ext (TwoFibreProductOver.Hom.ext' ?_ hb)
  rw [hom_a_eq (Fiber.fiberInclusion.map X), hom_a_eq (Fiber.fiberInclusion.map X'), hb]

/-- **Stacks 04SI (1).** The projection `𝒮 ×_{𝒮 × 𝒮, (x, y)} 𝒞/U ⥤ 𝒞/U` is a category fibred in
setoids over the slice `𝒞/U`. -/
theorem proj_isFiberedInSetoids (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) :
    (proj p x y).IsFiberedInSetoids where
  isFiberedInGroupoids := proj_isFiberedInGroupoids p x y
  fiber_isThin := proj_fiber_isThin p x y

/-- Being fibred in setoids, the projection to `𝒞/U` is in particular a fibred category, so it has
a presheaf of isomorphism classes of the objects of its fibres. -/
instance proj_isFibered (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) :
    (proj p x y).IsFibered :=
  (proj_isFiberedInSetoids p x y).isFiberedInGroupoids.isFibered

/-! #### The presheaf of isomorphism classes is `Isom(x, y)` -/

variable (p x y)

/-- The comparison morphism from the standard object attached to the section of `Isom(x, y)` of
`P` back to `P`. -/
private def objSectHom (P : Tot p x y) : obj' p x y P.y (sect P) ⟶ P :=
  homMk (isoFst P).inv (𝟙 P.y) (isHomLift_isoFst_inv P) (by simp) (by simp)

/-- The inverse comparison morphism. -/
private def objSectInv (P : Tot p x y) : P ⟶ obj' p x y P.y (sect P) :=
  homMk (isoFst P).hom (𝟙 P.y) (isHomLift_isoFst_hom P) (by simp) (by simp)

private lemma isHomLift_objSectHom (P : Tot p x y) :
    (proj p x y).IsHomLift (𝟙 P.y) (objSectHom p x y P) :=
  IsHomLift.of_fac' (proj p x y) (𝟙 P.y) _ rfl rfl (by
    simp only [objSectHom, TwoFibreProductOver.snd_map, homMk_b, eqToHom_refl, Category.comp_id]
    rfl)

/-- The standard object attached to the section of `Isom(x, y)` of `P` is isomorphic to `P`. -/
private def objSectIso (P : Tot p x y) : obj' p x y P.y (sect P) ≅ P where
  hom := objSectHom p x y P
  inv := objSectInv p x y P
  hom_inv_id :=
    TwoFibreProductOver.Hom.ext' (by simp [objSectHom, objSectInv])
      (by simp [objSectHom, objSectInv])
  inv_hom_id :=
    TwoFibreProductOver.Hom.ext' (by simp [objSectHom, objSectInv])
      (by simp [objSectHom, objSectInv])

/-- Every object of the 2-fibre product is isomorphic, in its fibre, to the standard object
attached to its section of `Isom(x, y)`. -/
private lemma isoClassMk_obj'_sect (P : Tot p x y) :
    isoClassMk (proj p x y) (⟨obj' p x y P.y (sect P), rfl⟩ : (proj p x y).Fiber P.y)
      = isoClassMk (proj p x y) (⟨P, rfl⟩ : (proj p x y).Fiber P.y) :=
  isoClassMk_eq_of_iso (Fiber.isoMk (objSectIso p x y P) (isHomLift_objSectHom p x y P))

@[simp] private lemma fiberInclusion_obj_mk {a : Over U} (Q : Tot p x y)
    (hQ : (proj p x y).obj Q = a) :
    Fiber.fiberInclusion.obj (⟨Q, hQ⟩ : (proj p x y).Fiber a) = Q := rfl

/-- The map from sections of `Isom(x, y)` over `a` to isomorphism classes of objects of the fibre
of the 2-fibre product over `a`. -/
private def toClass (a : Over U) (m : ULift.{max u₁ v₁ u₂} ((p.isomPresheaf x y).obj (op a))) :
    (proj p x y).isoClassPresheaf.obj (op a) :=
  isoClassMk (proj p x y) ⟨obj' p x y a m.down, rfl⟩

private lemma toClass_bijective (a : Over U) : Function.Bijective (toClass p x y a) := by
  constructor
  · intro m m' hmm
    obtain ⟨ι⟩ := exists_iso_of_isoClassMk_eq hmm
    have hinst : (proj p x y).IsHomLift (𝟙 a) (Fiber.fiberInclusion.map ι.hom) := ι.hom.2
    have hb : (Fiber.fiberInclusion.map ι.hom).b = 𝟙 a :=
      (IsHomLift.eq_of_isHomLift (proj p x y) _ (Fiber.fiberInclusion.map ι.hom)).symm
    have hIdx : (p.chosenPullbacks.sliceFunctor x).map (𝟙 a)
        = 𝟙 ((p.chosenPullbacks.sliceFunctor x).obj a) :=
      (p.chosenPullbacks.sliceFunctor x).map_id a
    have hIdy : (p.chosenPullbacks.sliceFunctor y).map (𝟙 a)
        = 𝟙 ((p.chosenPullbacks.sliceFunctor y).obj a) :=
      (p.chosenPullbacks.sliceFunctor y).map_id a
    have h1 := w_fst (Fiber.fiberInclusion.map ι.hom)
    have h2 := w_snd (Fiber.fiberInclusion.map ι.hom)
    rw [hb, hIdx] at h1
    rw [hb, hIdy] at h2
    simp only [fiberInclusion_obj_mk, isoFst_obj', Iso.refl_hom, Category.comp_id,
      Category.id_comp] at h1
    simp only [fiberInclusion_obj_mk, isoSnd_obj'_hom, h1] at h2
    have e1 : (m.down).1.1 ≫ 𝟙 ((p.chosenPullbacks.sliceFunctor y).obj a) = (m.down).1.1 :=
      Category.comp_id _
    have e2 : 𝟙 ((p.chosenPullbacks.sliceFunctor x).obj a) ≫ (m'.down).1.1 = (m'.down).1.1 :=
      Category.id_comp _
    refine ULift.ext (Subtype.ext (Subtype.ext ?_))
    rw [← e1, ← h2, e2]
  · intro c
    obtain ⟨A, rfl⟩ := isoClassMk_surjective (U := a) c
    obtain ⟨P, rfl⟩ := A
    exact ⟨ULift.up (sect P), isoClassMk_obj'_sect p x y P⟩

/-- The bijection between sections of `Isom(x, y)` over `a` and isomorphism classes of objects of
the fibre of the 2-fibre product over `a`. -/
private noncomputable def equivAt (a : Over U) :
    ULift.{max u₁ v₁ u₂} ((p.isomPresheaf x y).obj (op a)) ≃
      (proj p x y).isoClassPresheaf.obj (op a) :=
  Equiv.ofBijective _ (toClass_bijective p x y a)

private lemma equivAt_symm_isoClassMk (P : Tot p x y) :
    (equivAt p x y ((proj p x y).obj P)).symm
        (isoClassMk (proj p x y) (⟨P, rfl⟩ : (proj p x y).Fiber ((proj p x y).obj P)))
      = ULift.up (sect P) := by
  rw [Equiv.symm_apply_eq]
  exact (isoClassMk_obj'_sect p x y P).symm

private lemma equivAt_naturality {a a' : Over U} (h : a' ⟶ a)
    (c : (proj p x y).isoClassPresheaf.obj (op a)) :
    (equivAt p x y a').symm ((proj p x y).isoClassPresheaf.map h.op c)
      = ULift.up ((p.isomPresheaf x y).map h.op ((equivAt p x y a).symm c).down) := by
  obtain ⟨A, rfl⟩ := isoClassMk_surjective (U := a) c
  obtain ⟨P, rfl⟩ := A
  rw [equivAt_symm_isoClassMk]
  have hlift := isHomLift_restrictHom p x y P h
  have hsc : (proj p x y).IsStronglyCartesian h (restrictHom p x y P h) :=
    (proj_isFiberedInGroupoids p x y).isStronglyCartesian_homLift h _
  have hstep : (proj p x y).isoClassPresheaf.map h.op
        (isoClassMk (proj p x y) (⟨P, rfl⟩ : (proj p x y).Fiber ((proj p x y).obj P)))
      = isoClassMk (proj p x y) ⟨restrictObj p x y P h, rfl⟩ :=
    (isoClassMk_eq_pullbackFiber_of_isCartesian h ⟨P, rfl⟩ ⟨restrictObj p x y P h, rfl⟩
      (restrictHom p x y P h) hlift inferInstance).symm
  rw [hstep]
  exact (equivAt p x y a').symm_apply_apply _

/-- **Stacks 04SI (2).** The presheaf of isomorphism classes of the objects of the fibres of
`𝒮 ×_{𝒮 × 𝒮, (x, y)} 𝒞/U ⥤ 𝒞/U` — the presheaf of sets that Stacks 04SC attaches to a category
fibred in setoids — is `Isom(x, y)`. The identification sends the class of an object
`(z, α : z ≅ a^* x, β : z ≅ a^* y)` to `β ∘ α⁻¹`; that is
`CategoryTheory.Functor.isFiberedInSetoids_and_isoClassPresheaf_iso_isomPresheaf`. -/
@[no_expose]
noncomputable def presheafIso :
    (proj p x y).isoClassPresheaf ≅ p.isomPresheaf x y ⋙ uliftFunctor.{max u₁ v₁ u₂, v₂} :=
  NatIso.ofComponents (fun a => (Equiv.toIso (equivAt p x y a.unop)).symm)
    (fun {_ _} f => by
      ext c
      exact equivAt_naturality p x y f.unop c)

private lemma presheafIso_hom_app_isoClassMk (P : Tot p x y) :
    (presheafIso p x y).hom.app (op P.y) (isoClassMk (proj p x y) ⟨P, rfl⟩)
      = ULift.up (sect P) :=
  equivAt_symm_isoClassMk p x y P

end

end IsomPresheafTwoFibreProduct

/-- **Stacks 04SI.** Let `𝒞` be a category, let `p : 𝒮 ⥤ 𝒞` be a fibred category, let `U` be an
object of `𝒞` and let `x`, `y` be objects of the fibre category `𝒮_U`. Denote `x`, `y : 𝒞/U ⥤ 𝒮`
also the corresponding 1-morphisms `(a : V ⟶ U) ↦ a^* x` (Stacks 004B). Then

1. the 2-fibre product `𝒮 ×_{𝒮 × 𝒮, (x, y)} 𝒞/U`, whose objects over `a : V ⟶ U` are the triples
   `(z, α : z ≅ a^* x, β : z ≅ a^* y)` with `z` an object and `α`, `β` isomorphisms of `𝒮_V`, is
   fibred in setoids over `𝒞/U`, and
2. `Isom(x, y)` is the presheaf of sets corresponding to that category fibred in setoids
   (Stacks 04SC), namely its presheaf of isomorphism classes of objects of the fibres, the
   identification sending the class of `(z, α, β)` to `β ∘ α⁻¹`.

The second part is an isomorphism of presheaves, hence data: it is
`CategoryTheory.Functor.IsomPresheafTwoFibreProduct.presheafIso`, pinned by the requirement that
it send the class of `(z, α, β)` to `β ∘ α⁻¹`, which determines it, every class being the class
of such a triple. -/
@[no_expose, stacks 04SI]
noncomputable def isFiberedInSetoids_and_isoClassPresheaf_iso_isomPresheaf
    (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) :
    PProd (IsomPresheafTwoFibreProduct.proj p x y).IsFiberedInSetoids
      { e : (IsomPresheafTwoFibreProduct.proj p x y).isoClassPresheaf ≅
          p.isomPresheaf x y ⋙ uliftFunctor.{max u₁ v₁ u₂, v₂} //
        ∀ P : IsomPresheafTwoFibreProduct.Tot p x y,
          (e.hom.app (op P.y) (isoClassMk _ ⟨P, rfl⟩)).down.1.1 = P.iso.inv.1 ≫ P.iso.hom.2 } :=
  ⟨IsomPresheafTwoFibreProduct.proj_isFiberedInSetoids p x y,
    IsomPresheafTwoFibreProduct.presheafIso p x y, fun P => by
    rw [IsomPresheafTwoFibreProduct.presheafIso_hom_app_isoClassMk p x y P]
    rfl⟩

end CategoryTheory.Functor

end
