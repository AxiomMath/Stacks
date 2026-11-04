module

public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.CategoryTheory.Sites.PushforwardSections

/-!
# Computing the pushforward of a presheaf on a category fibred in groupoids

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over a base `𝒞`, and let
`ℱ` be a presheaf on `𝒳`. The pushforward `f_*ℱ` is the right Kan extension of `ℱ` along
`f.op`. Stacks 06W6 computes its value at an object `y` of `𝒴` lying over `V : 𝒞` as the
global sections of the restriction of `ℱ` to the 2-fibre product `(𝒞/V) ×_{y, 𝒴} 𝒳`:

`f_*ℱ(y) = Γ((𝒞/V) ×_{y, 𝒴} 𝒳, pr^{-1}ℱ)`.

## Main results

**Stacks 06W6** itself lives in `StacksFrontier.CategoryTheory.Sites.PushforwardSections`:

* `CategoryTheory.Presheaf.pushforwardSectionsEquiv` is the canonical identification of the
  pushforward at `y` with the global sections of the restricted presheaf on the 2-fibre
  product;
* `CategoryTheory.Presheaf.pushforwardSectionsEquiv_apply`: the section attached to an object
  `(U, x, x', φ)` of the 2-fibre product is obtained by restricting along the comparison
  arrow `φ⁻¹ ≫ (U → V)^* y` and then applying the counit of the right Kan extension. This
  pins the identification down, which naturality alone would not;
* `CategoryTheory.Presheaf.pushforwardSectionsEquiv_naturality`: the identification is
  natural in the presheaf.

This file keeps the comparison of the 2-fibre product with the costructured-arrow category
that the formula is proved from.

## Implementation notes

The right Kan extension of `ℱ` along `f.op` is computed at `op y` as a limit over the
structured-arrow category of `op y` under `f.op`; Mathlib's
`CategoryTheory.Functor.ranObjObjIsoLimit` provides that presentation. Dualising with
`CategoryTheory.costructuredArrowOpEquivalence` turns the index category into the opposite of
the costructured-arrow category `CostructuredArrow f y`, and the 2-fibre product is isomorphic
to that costructured-arrow category: an object of the 2-fibre product is an object `x'` of `𝒳`
over some `U : 𝒞` together with a vertical isomorphism from the chosen pullback `(U → V)^* y`
to `f x'`, and such data is the same as a morphism `f x' ⟶ y` of `𝒴`, the base morphism being
its image in `𝒞`. The inverse construction uses that `p𝒴` is fibred in groupoids to invert the
comparison map supplied by the chosen cartesian lift.

The two functors between the index categories are strictly inverse on objects and compatible
with the projections to `𝒳` on the nose, so the comparison of sections is Mathlib's
`CategoryTheory.Functor.sectionsPrecomp` in both directions, with no transport along an
isomorphism of index categories. That is why the object of the 2-fibre product attached to a
costructured arrow is built with an explicit `eqToHom` for `p𝒴(y) = V` instead of substituting
`V` away: the projections of the resulting object are then the components of the costructured
arrow on the nose.

The identification is an equivalence of types rather than an equality of the two
presentations; its construction does not involve any topology on `𝒳` or `𝒴`.

The chosen pullbacks enter through `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor`,
the 1-morphism `(U ⟶ V) ↦ (U → V)^* y` from the slice `𝒞/V` to `𝒴` which represents `y` by
the 2-Yoneda lemma.

## References

* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
-/

@[expose] public section

open Opposite

namespace CategoryTheory.FibredPushforward

attribute [local implicit_reducible] Functor.Fiber

universe u₁ u₂ u₃ v₁ v₂ v₃ w

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-! ### From the 2-fibre product to the costructured arrows -/

section ToCostructuredArrow

-- The slice functor of a choice of pullbacks is a plain `def`, so the comparison square of a
-- morphism of the 2-fibre product is not type-correct at `implicit` transparency and `rw`
-- declines it. The attribute is confined to this section: elsewhere it would hide
-- `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor_map_isHomLift` from instance search.
attribute [local implicit_reducible] Functor.ChoiceOfPullbacks.sliceFunctor

/-- The comparison arrow `φ⁻¹ ≫ (U → V)^* y : f x' ⟶ y` attached to an object of the 2-fibre
product is natural: a morphism of the 2-fibre product is a morphism of costructured
arrows. -/
lemma toCostructuredArrow_w
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    {P Q : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f}
    (φ : P ⟶ Q) :
    f.map φ.b ≫ (Q.iso.inv ≫ c.map Q.x.hom y) =
      P.iso.inv ≫ c.map P.x.hom y := by
  have h : f.map φ.b ≫ Q.iso.inv = P.iso.inv ≫ (c.sliceFunctor y).map φ.a := by
    calc
      f.map φ.b ≫ Q.iso.inv = P.iso.inv ≫ (P.iso.hom ≫ f.map φ.b) ≫ Q.iso.inv := by simp
      _ = P.iso.inv ≫ ((c.sliceFunctor y).map φ.a ≫ Q.iso.hom) ≫ Q.iso.inv := by
        rw [← φ.w]
      _ = P.iso.inv ≫ (c.sliceFunctor y).map φ.a := by simp [Category.assoc]
  calc
    f.map φ.b ≫ (Q.iso.inv ≫ c.map Q.x.hom y) =
        (f.map φ.b ≫ Q.iso.inv) ≫ c.map Q.x.hom y := by simp [Category.assoc]
    _ = (P.iso.inv ≫ (c.sliceFunctor y).map φ.a) ≫ c.map Q.x.hom y := by rw [h]
    _ = P.iso.inv ≫ c.map P.x.hom y := by
      rw [Category.assoc, Functor.ChoiceOfPullbacks.sliceFunctor_map_fac]

/-- The functor from the 2-fibre product `(𝒞/V) ×_{y, 𝒴} 𝒳` to the costructured arrows
`f x' ⟶ y`, sending `(U, x, x', φ)` to the comparison arrow `φ⁻¹ ≫ (U → V)^* y`. -/
noncomputable def toCostructuredArrow
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V) :
    TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f ⥤
      CostructuredArrow f y.1 where
  obj P := CostructuredArrow.mk (P.iso.inv ≫ c.map P.x.hom y)
  map {P Q} φ :=
    CostructuredArrow.homMk φ.b (toCostructuredArrow_w p𝒳 p𝒴 f c y φ)
  map_id P := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp φ ψ := by
    apply CostructuredArrow.hom_ext
    rfl

/-- The comparison functor is compatible with the projections to `𝒳`. -/
lemma toCostructuredArrow_comp_proj
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V) :
    toCostructuredArrow p𝒳 p𝒴 f c y ⋙ CostructuredArrow.proj f y.1 =
      TwoFibreProductOver.snd (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f :=
  rfl

end ToCostructuredArrow

/-! ### Liftings, with hypotheses in place of instances

The lemmas of `CategoryTheory.Functor.IsHomLift` and
`CategoryTheory.Functor.IsStronglyCartesian` take the liftings they compose as instance
arguments. At the morphisms built below, instance search does not find the lifting supplied by
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor_map_isHomLift`, so the four wrappers
here take it as an ordinary hypothesis and register it locally, where the morphisms are
variables and search succeeds. -/

/-- A vertical morphism followed by one over `u` lies over `u`. -/
lemma isHomLift_vertical_comp {p : 𝒴 ⥤ 𝒞} {a b d : 𝒴} {R S : 𝒞} {u : R ⟶ S}
    {φ : a ⟶ b} {ψ : b ⟶ d} (hφ : p.IsHomLift (𝟙 R) φ) (hψ : p.IsHomLift u ψ) :
    p.IsHomLift u (φ ≫ ψ) := by
  have := hφ
  have := hψ
  exact IsHomLift.comp_lift_id_left' p R φ u ψ

/-- A morphism over `u` followed by a vertical one lies over `u`. -/
lemma isHomLift_comp_vertical {p : 𝒴 ⥤ 𝒞} {a b d : 𝒴} {R S : 𝒞} {u : R ⟶ S}
    {φ : a ⟶ b} {ψ : b ⟶ d} (hφ : p.IsHomLift u φ) (hψ : p.IsHomLift (𝟙 S) ψ) :
    p.IsHomLift u (φ ≫ ψ) := by
  have := hφ
  have := hψ
  exact IsHomLift.comp_lift_id_right' p u φ S ψ

/-- A composite lies over the composite of the base morphisms. -/
lemma isHomLift_comp_eq {p : 𝒴 ⥤ 𝒞} {a b d : 𝒴} {R S T : 𝒞} {u : R ⟶ S} {v : S ⟶ T}
    {w : R ⟶ T} (hw : u ≫ v = w) {φ : a ⟶ b} {ψ : b ⟶ d}
    (hφ : p.IsHomLift u φ) (hψ : p.IsHomLift v ψ) : p.IsHomLift w (φ ≫ ψ) := by
  have := hφ
  have := hψ
  exact hw ▸ IsHomLift.comp p u v φ ψ

/-- Transport a lifting along an equality of base morphisms. -/
lemma isHomLift_of_eq {p : 𝒴 ⥤ 𝒞} {a b : 𝒴} {R S : 𝒞} {u u' : R ⟶ S} (h : u = u')
    {φ : a ⟶ b} (hφ : p.IsHomLift u φ) : p.IsHomLift u' φ := h ▸ hφ

/-- Prefixing the base morphism by an `eqToHom` does not change the lifting. -/
lemma isHomLift_eqToHom_comp {p : 𝒴 ⥤ 𝒞} {a b : 𝒴} {R' R S : 𝒞} (h : R' = R) {u : R ⟶ S}
    {φ : a ⟶ b} (hφ : p.IsHomLift u φ) : p.IsHomLift (eqToHom h ≫ u) φ := by
  have := hφ
  infer_instance

/-- Uniqueness of the factorisation through a strongly cartesian morphism. -/
lemma eq_of_isStronglyCartesian {p : 𝒴 ⥤ 𝒞} {a a' b : 𝒴} {R R' S : 𝒞} (g : R' ⟶ R)
    {u : R ⟶ S} (φ : a ⟶ b) (hsc : p.IsStronglyCartesian u φ) {f' : R' ⟶ S}
    (hf' : f' = g ≫ u) (φ' : a' ⟶ b) (hφ' : p.IsHomLift f' φ') (ψ₁ ψ₂ : a' ⟶ a)
    (h₁ : p.IsHomLift g ψ₁) (h₂ : p.IsHomLift g ψ₂)
    (e₁ : ψ₁ ≫ φ = φ') (e₂ : ψ₂ ≫ φ = φ') : ψ₁ = ψ₂ := by
  have := hsc
  have := hφ'
  have := h₁
  have := h₂
  exact (Functor.IsStronglyCartesian.map_uniq p u φ hf' φ' ψ₁ e₁).trans
    (Functor.IsStronglyCartesian.map_uniq p u φ hf' φ' ψ₂ e₂).symm

/-! ### From the costructured arrows to the 2-fibre product -/

/-- A costructured arrow `Z : f x' ⟶ y` lies over the morphism `p𝒴 Z` of the base. -/
instance isHomLift_costructuredArrow_hom {p𝒴 : 𝒴 ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴} {V : 𝒞}
    (y : p𝒴.Fiber V) (Z : CostructuredArrow f y.1) :
    p𝒴.IsHomLift (p𝒴.map Z.hom ≫ eqToHom y.2) Z.hom :=
  IsHomLift.of_fac' p𝒴 _ Z.hom rfl y.2 (by simp)

/-- The vertical comparison map from `f x'` to the chosen pullback of `y` along `p𝒴 Z`,
supplied by the universal property of the chosen cartesian lift. -/
noncomputable def comparisonHom {p𝒴 : 𝒴 ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴}
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V) (Z : CostructuredArrow f y.1) :
    f.obj Z.left ⟶ (c.obj (p𝒴.map Z.hom ≫ eqToHom y.2) y).1 :=
  Functor.IsStronglyCartesian.map p𝒴 (p𝒴.map Z.hom ≫ eqToHom y.2)
    (c.map (p𝒴.map Z.hom ≫ eqToHom y.2) y)
    (g := 𝟙 (p𝒴.obj (f.obj Z.left))) (Category.id_comp _).symm Z.hom

/-- The comparison map is vertical. -/
instance isHomLift_comparisonHom {p𝒴 : 𝒴 ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴}
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V) (Z : CostructuredArrow f y.1) :
    p𝒴.IsHomLift (𝟙 (p𝒴.obj (f.obj Z.left))) (comparisonHom c y Z) :=
  Functor.IsStronglyCartesian.map_isHomLift p𝒴 (p𝒴.map Z.hom ≫ eqToHom y.2)
    (c.map (p𝒴.map Z.hom ≫ eqToHom y.2) y) (Category.id_comp _).symm Z.hom

/-- The comparison map is compatible with the chosen cartesian lift: composing recovers `Z`. -/
lemma comparisonHom_fac {p𝒴 : 𝒴 ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴}
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V) (Z : CostructuredArrow f y.1) :
    comparisonHom c y Z ≫ c.map (p𝒴.map Z.hom ≫ eqToHom y.2) y = Z.hom :=
  Functor.IsStronglyCartesian.fac p𝒴 (p𝒴.map Z.hom ≫ eqToHom y.2)
    (c.map (p𝒴.map Z.hom ≫ eqToHom y.2) y) (Category.id_comp _).symm Z.hom

/-- Because `p𝒴` is fibred in groupoids, the vertical comparison map is invertible. -/
lemma isIso_comparisonHom {p𝒴 : 𝒴 ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴}
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (Z : CostructuredArrow f y.1) :
    IsIso (comparisonHom c y Z) :=
  Functor.isIso_of_fiber_isGroupoid (h𝒴.fiber_isGroupoid (p𝒴.obj (f.obj Z.left)))
    (comparisonHom c y Z) (isHomLift_comparisonHom c y Z)

/-- The comparison isomorphism between the chosen pullback of `y` along `p𝒴 Z` and `f x'`. -/
noncomputable def comparisonIso {p𝒴 : 𝒴 ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴}
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (Z : CostructuredArrow f y.1) :
    (c.obj (p𝒴.map Z.hom ≫ eqToHom y.2) y).1 ≅ f.obj Z.left :=
  haveI := isIso_comparisonHom c y h𝒴 Z
  (asIso (comparisonHom c y Z)).symm

/-- The inverse of the comparison isomorphism is the comparison map. -/
lemma comparisonIso_inv {p𝒴 : 𝒴 ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴}
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (Z : CostructuredArrow f y.1) :
    (comparisonIso c y h𝒴 Z).inv = comparisonHom c y Z :=
  rfl

/-- The object of the 2-fibre product attached to a costructured arrow `Z : f x' ⟶ y`: the
object `x'` of `𝒳`, over the base object `p𝒴 (f x')`, together with the inverse of the
comparison map to the chosen pullback of `y` along `p𝒴 Z`. -/
noncomputable def ofCostructuredArrowObj
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (Z : CostructuredArrow f y.1) :
    TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f where
  base := p𝒴.obj (f.obj Z.left)
  x := Over.mk (p𝒴.map Z.hom ≫ eqToHom y.2)
  y := Z.left
  hx := rfl
  hy := (Functor.IsFiberedInGroupoids.Factorization.obj_eq_of_comp_eq
    p𝒳 p𝒴 f hf Z.left).symm
  iso := comparisonIso c y h𝒴 Z
  vertical := by
    have := isIso_comparisonHom c y h𝒴 Z
    have : p𝒴.IsHomLift (𝟙 (p𝒴.obj (f.obj Z.left)))
        (asIso (comparisonHom c y Z)).hom := isHomLift_comparisonHom c y Z
    exact IsHomLift.lift_id_inv p𝒴 (p𝒴.obj (f.obj Z.left)) (asIso (comparisonHom c y Z))

/-- The structure morphism of the slice component of
`CategoryTheory.FibredPushforward.ofCostructuredArrowObj`. -/
lemma ofCostructuredArrowObj_x_hom
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (Z : CostructuredArrow f y.1) :
    (ofCostructuredArrowObj p𝒳 p𝒴 f c y h𝒴 hf Z).x.hom =
      p𝒴.map Z.hom ≫ eqToHom y.2 :=
  rfl

/-- The comparison isomorphism of
`CategoryTheory.FibredPushforward.ofCostructuredArrowObj`. -/
lemma ofCostructuredArrowObj_iso
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (Z : CostructuredArrow f y.1) :
    (ofCostructuredArrowObj p𝒳 p𝒴 f c y h𝒴 hf Z).iso = comparisonIso c y h𝒴 Z :=
  rfl

/-- The slice component of the functoriality of
`CategoryTheory.FibredPushforward.ofCostructuredArrowObj`. -/
noncomputable def ofCostructuredArrowMapOver
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    {Z Z' : CostructuredArrow f y.1} (g : Z ⟶ Z') :
    (ofCostructuredArrowObj p𝒳 p𝒴 f c y h𝒴 hf Z).x ⟶
      (ofCostructuredArrowObj p𝒳 p𝒴 f c y h𝒴 hf Z').x :=
  Over.homMk (p𝒴.map (f.map g.left)) (by
    have h := congrArg p𝒴.map (CostructuredArrow.w g)
    rw [Functor.map_comp] at h
    change p𝒴.map (f.map g.left) ≫ p𝒴.map Z'.hom ≫ eqToHom y.2 =
      p𝒴.map Z.hom ≫ eqToHom y.2
    rw [← Category.assoc, h])

/-- The underlying morphism of `CategoryTheory.FibredPushforward.ofCostructuredArrowMapOver`. -/
lemma ofCostructuredArrowMapOver_left
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    {Z Z' : CostructuredArrow f y.1} (g : Z ⟶ Z') :
    (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g).left = p𝒴.map (f.map g.left) :=
  rfl

/-- The comparison square of the functoriality: both sides are liftings of the same base
morphism factoring the same arrow through the chosen cartesian morphism, so they agree. -/
lemma comparisonHom_naturality
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    {Z Z' : CostructuredArrow f y.1} (g : Z ⟶ Z') :
    comparisonHom c y Z ≫
        (c.sliceFunctor y).map (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g) =
      f.map g.left ≫ comparisonHom c y Z' := by
  have hbase : p𝒴.map Z.hom ≫ eqToHom y.2 =
      (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g).left ≫
        (p𝒴.map Z'.hom ≫ eqToHom y.2) := by
    change p𝒴.map Z.hom ≫ eqToHom y.2 =
      p𝒴.map (f.map g.left) ≫ (p𝒴.map Z'.hom ≫ eqToHom y.2)
    have h := congrArg p𝒴.map (CostructuredArrow.w g)
    rw [Functor.map_comp] at h
    rw [← Category.assoc, h]
  have hsl := Functor.ChoiceOfPullbacks.sliceFunctor_map_isHomLift c y
    (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g)
  have h₁ := isHomLift_vertical_comp (isHomLift_comparisonHom c y Z) hsl
  have h₂ : p𝒴.IsHomLift (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g).left
      (f.map g.left ≫ comparisonHom c y Z') :=
    isHomLift_of_eq (ofCostructuredArrowMapOver_left p𝒳 p𝒴 f c y h𝒴 hf g).symm
      (isHomLift_comp_vertical
        (inferInstance : p𝒴.IsHomLift (p𝒴.map (f.map g.left)) (f.map g.left))
        (isHomLift_comparisonHom c y Z'))
  refine eq_of_isStronglyCartesian
    (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g).left
    (c.map (p𝒴.map Z'.hom ≫ eqToHom y.2) y)
    (c.isStronglyCartesian (p𝒴.map Z'.hom ≫ eqToHom y.2) y) hbase Z.hom
    (isHomLift_costructuredArrow_hom y Z) _ _ h₁ h₂ ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (comparisonHom c y Z ≫ ·)
        (Functor.ChoiceOfPullbacks.sliceFunctor_map_fac c y
          (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g))).trans
        (comparisonHom_fac c y Z))
  · rw [Category.assoc, comparisonHom_fac, CostructuredArrow.w]

/-- The functor from the costructured arrows `f x' ⟶ y` to the 2-fibre product
`(𝒞/V) ×_{y, 𝒴} 𝒳`, inverse to `CategoryTheory.FibredPushforward.toCostructuredArrow`. -/
noncomputable def ofCostructuredArrow
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) :
    CostructuredArrow f y.1 ⥤
      TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f where
  obj Z := ofCostructuredArrowObj p𝒳 p𝒴 f c y h𝒴 hf Z
  map {Z Z'} g :=
    { hbase := p𝒴.map (f.map g.left)
      a := ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g
      b := g.left
      ha := IsHomLift.of_fac' (Over.forget V) (p𝒴.map (f.map g.left))
        (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g) rfl rfl (by
          rw [Over.forget_map, ofCostructuredArrowMapOver_left]
          change p𝒴.map (f.map g.left) = 𝟙 _ ≫ p𝒴.map (f.map g.left) ≫ 𝟙 _
          simp)
      hb := IsHomLift.of_fac' p𝒳 (p𝒴.map (f.map g.left)) g.left
        (Functor.IsFiberedInGroupoids.Factorization.obj_eq_of_comp_eq
          p𝒳 p𝒴 f hf Z.left).symm
        (Functor.IsFiberedInGroupoids.Factorization.obj_eq_of_comp_eq
          p𝒳 p𝒴 f hf Z'.left).symm (by
          rw [Functor.IsFiberedInGroupoids.Factorization.map_eq_of_comp_eq p𝒳 p𝒴 f hf]
          simp)
      w := by
        rw [ofCostructuredArrowObj_iso, ofCostructuredArrowObj_iso]
        have key := comparisonHom_naturality p𝒳 p𝒴 f c y h𝒴 hf g
        rw [← comparisonIso_inv c y h𝒴 Z, ← comparisonIso_inv c y h𝒴 Z'] at key
        have key' : (comparisonIso c y h𝒴 Z).inv ≫
            ((c.sliceFunctor y).map (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g) ≫
              (comparisonIso c y h𝒴 Z').hom) = f.map g.left :=
          (Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ (comparisonIso c y h𝒴 Z').hom) key).trans (by simp))
        exact (Iso.inv_comp_eq _).mp key' }
  map_id Z := by
    apply TwoFibreProductOver.Hom.ext'
    · apply Over.OverMorphism.ext
      rw [TwoFibreProductOver.id_a]
      change (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf (𝟙 Z)).left = _
      rw [ofCostructuredArrowMapOver_left]
      simp [ofCostructuredArrowObj]
    · rfl
  map_comp g h := by
    apply TwoFibreProductOver.Hom.ext'
    · apply Over.OverMorphism.ext
      rw [TwoFibreProductOver.comp_a]
      change (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf (g ≫ h)).left =
        (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf g).left ≫
          (ofCostructuredArrowMapOver p𝒳 p𝒴 f c y h𝒴 hf h).left
      rw [ofCostructuredArrowMapOver_left, ofCostructuredArrowMapOver_left,
        ofCostructuredArrowMapOver_left]
      (simp; rfl)
    · rfl

/-- The inverse functor is compatible with the projections to `𝒳`. -/
lemma ofCostructuredArrow_comp_snd
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) :
    ofCostructuredArrow p𝒳 p𝒴 f c y h𝒴 hf ⋙
        TwoFibreProductOver.snd (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f =
      CostructuredArrow.proj f y.1 :=
  rfl

/-- Passing from the costructured arrows to the 2-fibre product and back is the identity. -/
lemma toCostructuredArrow_ofCostructuredArrow_obj
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (Z : CostructuredArrow f y.1) :
    (toCostructuredArrow p𝒳 p𝒴 f c y).obj
      ((ofCostructuredArrow p𝒳 p𝒴 f c y h𝒴 hf).obj Z) = Z := by
  refine CostructuredArrow.obj_ext _ Z rfl ?_
  change f.map (eqToHom (rfl : Z.left = Z.left)) ≫ Z.hom = _
  rw [eqToHom_refl, Functor.map_id, Category.id_comp]
  exact (comparisonHom_fac c y Z).symm

/-- The base object of the 2-fibre product is determined by its slice component. -/
lemma unitLeftEq
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    p𝒴.obj (f.obj P.y) = P.x.left :=
  (Functor.IsFiberedInGroupoids.Factorization.obj_eq_of_comp_eq p𝒳 p𝒴 f hf P.y).trans
    (P.hy.trans P.hx.symm)

section UnitOverCond

-- As in `ToCostructuredArrow` above: the comparison isomorphism of an object of the 2-fibre
-- product is typed through the chosen slice functor, so the factorisation below is not
-- type-correct at `implicit` transparency unless that functor is reducible there.
attribute [local implicit_reducible] Functor.ChoiceOfPullbacks.sliceFunctor

/-- A vertical isomorphism has inverse mapping to an `eqToHom`. -/
private theorem map_inv_eq_eqToHom_of_isHomLift {p : 𝒴 ⥤ 𝒞} {a b : 𝒴} {R : 𝒞} (e : a ≅ b)
    [p.IsHomLift (𝟙 R) e.hom] : p.map e.inv = eqToHom
      ((IsHomLift.codomain_eq p (𝟙 R) e.hom).trans (IsHomLift.domain_eq p (𝟙 R) e.hom).symm) := by
  have := IsHomLift.lift_id_inv p R e
  simpa [eqToHom_trans] using IsHomLift.fac' p (𝟙 R) e.inv

/-- The structure morphism of the slice component of the object attached to the comparison
arrow of `P` is the one of `P`, transported along
`CategoryTheory.FibredPushforward.unitLeftEq`. -/
lemma unitOverCond
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P) ≫ P.x.hom =
      p𝒴.map (P.iso.inv ≫ c.map P.x.hom y) ≫ eqToHom y.2 := by
  have : p𝒴.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have hc := IsHomLift.fac' p𝒴 P.x.hom (c.map P.x.hom y)
  rw [Functor.map_comp, map_inv_eq_eqToHom_of_isHomLift (R := P.base) P.iso, hc]
  simp

end UnitOverCond

/-- The slice component of the unit comparison at `P`. -/
noncomputable def unitOverHom
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    (ofCostructuredArrowObj p𝒳 p𝒴 f c y h𝒴 hf
      ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)).x ⟶ P.x :=
  Over.homMk (eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P)) (unitOverCond p𝒳 p𝒴 f c y hf P)

/-- The slice component of the inverse of the unit comparison at `P`. -/
noncomputable def unitOverInv
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    P.x ⟶ (ofCostructuredArrowObj p𝒳 p𝒴 f c y h𝒴 hf
      ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)).x :=
  Over.homMk (eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P).symm) (by
    change eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P).symm ≫
      (p𝒴.map (P.iso.inv ≫ c.map P.x.hom y) ≫ eqToHom y.2) = P.x.hom
    rw [← unitOverCond p𝒳 p𝒴 f c y hf P]
    simp)

/-- The underlying morphism of `CategoryTheory.FibredPushforward.unitOverHom`. -/
lemma unitOverHom_left
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    (unitOverHom p𝒳 p𝒴 f c y h𝒴 hf P).left = eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P) :=
  rfl

/-- The underlying morphism of `CategoryTheory.FibredPushforward.unitOverInv`. -/
lemma unitOverInv_left
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    (unitOverInv p𝒳 p𝒴 f c y h𝒴 hf P).left =
      eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P).symm :=
  rfl

/-- The two slice components of the unit comparison are mutually inverse. -/
lemma unitOverHom_comp_inv
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    unitOverHom p𝒳 p𝒴 f c y h𝒴 hf P ≫ unitOverInv p𝒳 p𝒴 f c y h𝒴 hf P = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, unitOverHom_left, unitOverInv_left]
  change eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P) ≫
    eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P).symm = 𝟙 (p𝒴.obj (f.obj P.y))
  simp

/-- The comparison arrow of `P` is the comparison map of the costructured arrow it defines:
both are liftings of the identity factoring that arrow through the chosen cartesian
morphism. -/
lemma unitComparison
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    P.iso.inv ≫ (c.sliceFunctor y).map (unitOverInv p𝒳 p𝒴 f c y h𝒴 hf P) =
      comparisonHom c y ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P) := by
  have : p𝒴.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have hslice : p𝒴.obj ((c.sliceFunctor y).obj P.x) = P.x.left := (c.obj P.x.hom y).2
  have hleft₂ : p𝒴.obj (f.obj P.y) = p𝒴.obj ((c.sliceFunctor y).obj P.x) :=
    (unitLeftEq p𝒳 p𝒴 f c y hf P).trans hslice.symm
  have hPinv : p𝒴.IsHomLift (eqToHom hleft₂) P.iso.inv := by
    have := IsHomLift.lift_id_inv p𝒴 P.base P.iso
    rw [← map_inv_eq_eqToHom_of_isHomLift (R := P.base) P.iso]
    infer_instance
  have hsl := Functor.ChoiceOfPullbacks.sliceFunctor_map_isHomLift c y
    (unitOverInv p𝒳 p𝒴 f c y h𝒴 hf P)
  have hslInv : p𝒴.IsHomLift (eqToHom hleft₂.symm)
      ((c.sliceFunctor y).map (unitOverInv p𝒳 p𝒴 f c y h𝒴 hf P)) := by
    refine isHomLift_of_eq ?_ (isHomLift_eqToHom_comp hslice hsl)
    rw [unitOverInv_left, eqToHom_trans]
  have h₁ := isHomLift_comp_eq
    ((eqToHom_trans hleft₂ hleft₂.symm).trans (eqToHom_refl _ _)) hPinv hslInv
  refine eq_of_isStronglyCartesian (𝟙 (p𝒴.obj (f.obj P.y)))
    (c.map (p𝒴.map (P.iso.inv ≫ c.map P.x.hom y) ≫ eqToHom y.2) y)
    (c.isStronglyCartesian (p𝒴.map (P.iso.inv ≫ c.map P.x.hom y) ≫ eqToHom y.2) y)
    (Category.id_comp _).symm (P.iso.inv ≫ c.map P.x.hom y)
    (isHomLift_costructuredArrow_hom y ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)) _ _ h₁
    (isHomLift_comparisonHom c y ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)) ?_ ?_
  · exact (Category.assoc _ _ _).trans (congrArg (P.iso.inv ≫ ·)
      (Functor.ChoiceOfPullbacks.sliceFunctor_map_fac c y
        (unitOverInv p𝒳 p𝒴 f c y h𝒴 hf P)))
  · exact comparisonHom_fac c y ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)

/-- The unit of the comparison: the object obtained from `P` by passing to the costructured
arrows and back maps to `P` by a morphism which is the identity on the `𝒳`-component. -/
noncomputable def ofCostructuredArrowUnitHom
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    ofCostructuredArrowObj p𝒳 p𝒴 f c y h𝒴 hf
      ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P) ⟶ P where
  hbase := eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P) ≫ eqToHom P.hx
  a := unitOverHom p𝒳 p𝒴 f c y h𝒴 hf P
  b := 𝟙 P.y
  ha := IsHomLift.of_fac' (Over.forget V) _ (unitOverHom p𝒳 p𝒴 f c y h𝒴 hf P) rfl P.hx (by
    rw [Over.forget_map, unitOverHom_left]
    change eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P) =
      𝟙 _ ≫ (eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P) ≫ eqToHom P.hx) ≫ eqToHom P.hx.symm
    simp)
  hb := IsHomLift.of_fac' p𝒳 _ (𝟙 P.y)
    (show p𝒳.obj P.y = (ofCostructuredArrowObj p𝒳 p𝒴 f c y h𝒴 hf
        ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)).base from
      (Functor.IsFiberedInGroupoids.Factorization.obj_eq_of_comp_eq p𝒳 p𝒴 f hf P.y).symm)
    P.hy (by
      change p𝒳.map (𝟙 P.y) =
        eqToHom (Functor.IsFiberedInGroupoids.Factorization.obj_eq_of_comp_eq
            p𝒳 p𝒴 f hf P.y).symm ≫
          (eqToHom (unitLeftEq p𝒳 p𝒴 f c y hf P) ≫ eqToHom P.hx) ≫ eqToHom P.hy.symm
      simp)
  w := by
    rw [ofCostructuredArrowObj_iso]
    have key := unitComparison p𝒳 p𝒴 f c y h𝒴 hf P
    rw [← comparisonIso_inv c y h𝒴 ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)] at key
    have h1 : (c.sliceFunctor y).map (unitOverInv p𝒳 p𝒴 f c y h𝒴 hf P) ≫
        (comparisonIso c y h𝒴 ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)).hom =
          P.iso.hom := by
      have key' : P.iso.inv ≫ ((c.sliceFunctor y).map (unitOverInv p𝒳 p𝒴 f c y h𝒴 hf P) ≫
          (comparisonIso c y h𝒴 ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)).hom) = 𝟙 _ :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (comparisonIso c y h𝒴
            ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)).hom) key).trans
            (Iso.inv_hom_id _))
      have h2 := (Iso.inv_comp_eq P.iso).mp key'
      exact h2.trans (Category.comp_id _)
    have hstep := congrArg (c.sliceFunctor y).map
      (unitOverHom_comp_inv p𝒳 p𝒴 f c y h𝒴 hf P)
    rw [Functor.map_comp, Functor.map_id] at hstep
    rw [← h1]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (comparisonIso c y h𝒴
      ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)).hom) hstep).trans ?_
    exact (Category.id_comp _).trans
      ((congrArg ((comparisonIso c y h𝒴
        ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)).hom ≫ ·) (f.map_id P.y)).trans
        (Category.comp_id _)).symm

/-- The unit of the comparison is the identity on the `𝒳`-component. -/
lemma snd_map_ofCostructuredArrowUnitHom
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (c : p𝒴.ChoiceOfPullbacks) {V : 𝒞} (y : p𝒴.Fiber V)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    (TwoFibreProductOver.snd (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f).map
      (ofCostructuredArrowUnitHom p𝒳 p𝒴 f c y h𝒴 hf P) = 𝟙 P.y :=
  rfl

/-! ### Comparison of sections -/

/-- Compatible families of sections over the costructured-arrow category are the same as
compatible families over the 2-fibre product: the two index categories are strictly inverse
on objects, and each projects to `𝒳` on the nose. -/
noncomputable def costructuredArrowSectionsEquiv
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hf : f ⋙ p𝒴 = p𝒳) (c : p𝒴.ChoiceOfPullbacks)
    {V : 𝒞} (y : p𝒴.Fiber V) (ℱ : 𝒳ᵒᵖ ⥤ Type w) :
    ((CostructuredArrow.proj f y.1).op ⋙ ℱ).sections ≃
      ((TwoFibreProductOver.snd (Over.forget V) p𝒳 p𝒴
        (c.sliceFunctor y) f).op ⋙ ℱ).sections :=
  Equiv.ofBijective (Functor.sectionsPrecomp (toCostructuredArrow p𝒳 p𝒴 f c y).op) (by
    constructor
    · intro s₁ s₂ hs
      apply Functor.sections_ext_iff.mpr
      intro Z
      have hval := Functor.sections_ext_iff.mp hs
        (op ((ofCostructuredArrow p𝒳 p𝒴 f c y h𝒴 hf).obj Z.unop))
      have hobj := toCostructuredArrow_ofCostructuredArrow_obj p𝒳 p𝒴 f c y h𝒴 hf Z.unop
      change s₁.val (op ((toCostructuredArrow p𝒳 p𝒴 f c y).obj
          ((ofCostructuredArrow p𝒳 p𝒴 f c y h𝒴 hf).obj Z.unop))) =
        s₂.val (op ((toCostructuredArrow p𝒳 p𝒴 f c y).obj
          ((ofCostructuredArrow p𝒳 p𝒴 f c y h𝒴 hf).obj Z.unop))) at hval
      rwa [hobj] at hval
    · intro t
      refine ⟨Functor.sectionsPrecomp (ofCostructuredArrow p𝒳 p𝒴 f c y h𝒴 hf).op t, ?_⟩
      apply Functor.sections_ext_iff.mpr
      intro P
      have h := t.property
        (Quiver.Hom.op (ofCostructuredArrowUnitHom p𝒳 p𝒴 f c y h𝒴 hf P.unop))
      change ℱ.map ((TwoFibreProductOver.snd (Over.forget V) p𝒳 p𝒴
          (c.sliceFunctor y) f).map
            (ofCostructuredArrowUnitHom p𝒳 p𝒴 f c y h𝒴 hf P.unop)).op (t.val P) = _ at h
      rw [snd_map_ofCostructuredArrowUnitHom] at h
      have h2 : ℱ.map ((𝟙 P.unop.y).op) (t.val P) = t.val P := by
        simp only [op_id, Functor.map_id]
        rfl
      exact h.symm.trans h2)

/-- The value of the comparison of sections at an object of the 2-fibre product is the value
of the original family at the corresponding costructured arrow.

Stating this as its own definitional lemma avoids having to see through the coercion of
`Equiv.ofBijective`, which no `simp` lemma in Mathlib unfolds. -/
lemma costructuredArrowSectionsEquiv_val
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hf : f ⋙ p𝒴 = p𝒳) (c : p𝒴.ChoiceOfPullbacks)
    {V : 𝒞} (y : p𝒴.Fiber V) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    (s : ((CostructuredArrow.proj f y.1).op ⋙ ℱ).sections)
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    (costructuredArrowSectionsEquiv p𝒳 p𝒴 f h𝒴 hf c y ℱ s).val (op P) =
      s.val (op ((toCostructuredArrow p𝒳 p𝒴 f c y).obj P)) :=
  rfl

/-- Dualising: compatible families of sections over the structured arrows `op y ⟶ f.op x`
are the same as compatible families over the opposite of the costructured arrows
`f x ⟶ y`. -/
noncomputable def opSectionsEquiv
    {p𝒴 : 𝒴 ⥤ 𝒞} (f : 𝒳 ⥤ 𝒴)
    {V : 𝒞} (y : p𝒴.Fiber V) (ℱ : 𝒳ᵒᵖ ⥤ Type w) :
    ((StructuredArrow.proj (op y.1) f.op ⋙ ℱ).sections) ≃
      ((CostructuredArrow.proj f y.1).op ⋙ ℱ).sections := by
  let e := CategoryTheory.costructuredArrowOpEquivalence f y.1
  let P := StructuredArrow.proj (op y.1) f.op ⋙ ℱ
  let Q := (CostructuredArrow.proj f y.1).op ⋙ ℱ
  have h : e.functor ⋙ StructuredArrow.proj (op y.1) f.op =
      (CostructuredArrow.proj f y.1).op := rfl
  let hPQ : e.functor ⋙ P ≅ Q :=
    (Functor.associator e.functor (StructuredArrow.proj (op y.1) f.op) ℱ).symm ≪≫
      Functor.isoWhiskerRight (eqToIso h) ℱ
  exact (Equiv.ofBijective (Functor.sectionsPrecomp e.functor)
      (Functor.bijective_sectionsPrecomp e.functor P)).trans
    ((Functor.sectionsFunctor _).mapIso hPQ).toEquiv

/-- The value of the dualising comparison of sections is the value of the original family at
the corresponding structured arrow: the identity map carried along by the identification of
the two index functors acts trivially. -/
lemma opSectionsEquiv_val {p𝒴 : 𝒴 ⥤ 𝒞} (f : 𝒳 ⥤ 𝒴)
    {V : 𝒞} (y : p𝒴.Fiber V) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    (s : (StructuredArrow.proj (op y.1) f.op ⋙ ℱ).sections)
    (Z : (CostructuredArrow f y.1)ᵒᵖ) :
    (opSectionsEquiv f y ℱ s).val Z =
      s.val ((costructuredArrowOpEquivalence f y.1).functor.obj Z) := by
  have h : (opSectionsEquiv f y ℱ s).val Z =
      ℱ.map (𝟙 (op Z.unop.left))
        (s.val ((costructuredArrowOpEquivalence f y.1).functor.obj Z)) :=
    rfl
  rw [h, Functor.map_id]
  rfl

end CategoryTheory.FibredPushforward

end
