module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Automorphisms of the middle object of a distinguished triangle

Let `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` be a distinguished triangle in a pre-triangulated category and
consider the automorphisms of `Y` that do not move `Y ⟶ Z`. Each is of the form
`𝟙 + t ≫ (X ⟶ Y)` for some `t : Y ⟶ X`, by exactness of `Hom(Y, -)` along the triangle, and
every such morphism is an automorphism as soon as `X ⟶ Y` annihilates every morphism
`Y ⟶ X` — the condition `CategoryTheory.Pretriangulated.Triangle.HasSquareZeroMor₁` below,
which in the motivating example says that the ideal cutting out a thickening has square zero.
Two parameters `t` give the same automorphism exactly when they differ by a morphism factoring
through `Z⟦-1⟧ ⟶ X`, so the group of these automorphisms is the cokernel of
`Hom(Y, Z⟦-1⟧) ⟶ Hom(Y, X)`.

This is the mechanism behind the deformation-theoretic statement that the automorphisms of a
lift across a square-zero thickening form a cokernel; see Stacks 0DIZ.

## Main definitions

* `CategoryTheory.Pretriangulated.Triangle.HasSquareZeroMor₁`: the condition that `T.mor₁`
  annihilates every morphism `T.obj₂ ⟶ T.obj₁`.
* `CategoryTheory.Pretriangulated.Triangle.unipotent`: the automorphism `𝟙 + t ≫ T.mor₁`.
* `CategoryTheory.Pretriangulated.Triangle.unipotentHom`: the same, as a group homomorphism
  out of the group of morphisms `T.obj₂ ⟶ T.obj₁` written multiplicatively.
* `CategoryTheory.Pretriangulated.Triangle.autFixingMor₂`: the automorphisms of `T.obj₂`
  fixing `T.mor₂`.
* `CategoryTheory.Pretriangulated.Triangle.invRotateMor₁`: the morphism
  `T.obj₃⟦-1⟧ ⟶ T.obj₁` of the inverse rotation of `T`.
* `CategoryTheory.Pretriangulated.Triangle.connecting`: postcomposition with
  `invRotateMor₁`.

## Main results

* `CategoryTheory.Pretriangulated.Triangle.mem_autFixingMor₂_iff_exists`: an automorphism of
  `T.obj₂` fixes `T.mor₂` exactly when it is unipotent along `T.mor₁`.
* `CategoryTheory.Pretriangulated.Triangle.unipotentHom_range`: the unipotent automorphisms
  are exactly those fixing `T.mor₂`.
* `CategoryTheory.Pretriangulated.Triangle.unipotentHom_ker`: an automorphism `𝟙 + t ≫ T.mor₁`
  is the identity exactly when `t` comes from `T.obj₃⟦-1⟧`.
* `CategoryTheory.Pretriangulated.Triangle.autFixingMor₂MulEquiv`: the resulting presentation
  of the automorphisms fixing `T.mor₂` as a cokernel.

## Implementation notes

The group of morphisms `T.obj₂ ⟶ T.obj₁` is additive and the automorphism group is written
multiplicatively, so the comparison is stated between `Multiplicative (T.obj₂ ⟶ T.obj₁)` and
`Aut T.obj₂`, and the subgroup to quotient by is the image of `connecting` transported along
`AddSubgroup.toSubgroup`.

The inverse rotation of `T` is the triangle `T.obj₃⟦-1⟧ ⟶ T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃`, whose
first morphism is recorded separately as `invRotateMor₁` with its source and target written
out: the projections of `Triangle.invRotate` are identified with `T.obj₃⟦-1⟧` and `T.obj₁`
only after unfolding a semireducible definition, so stating the two facts used about that
morphism as named lemmas is what makes rewriting with it work at all.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated.Triangle

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]

section Unipotent

variable (T : Triangle C)

/-- A triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` has *square-zero first morphism* if the composite
`X ⟶ Y ⟶ X` vanishes for every choice of the second arrow. In the motivating example
`X ⟶ Y` is multiplication by a square-zero ideal and every morphism `Y ⟶ X` factors through
the reduction `Y ⟶ Z`. -/
def HasSquareZeroMor₁ : Prop := ∀ s : T.obj₂ ⟶ T.obj₁, T.mor₁ ≫ s = 0

variable {T}

/-- Two unipotent corrections along a square-zero first morphism compose to zero. -/
theorem HasSquareZeroMor₁.comp_eq_zero (h : T.HasSquareZeroMor₁) (t s : T.obj₂ ⟶ T.obj₁) :
    (t ≫ T.mor₁) ≫ s ≫ T.mor₁ = 0 := by
  rw [Category.assoc, ← Category.assoc T.mor₁, h s, zero_comp, comp_zero]

/-- The automorphism `𝟙 + t ≫ T.mor₁` of the middle object of a triangle with square-zero
first morphism. Its inverse is `𝟙 - t ≫ T.mor₁`. -/
@[simps]
def unipotent (h : T.HasSquareZeroMor₁) (t : T.obj₂ ⟶ T.obj₁) : Aut T.obj₂ where
  asIso :=
    { hom := 𝟙 T.obj₂ + t ≫ T.mor₁
      inv := 𝟙 T.obj₂ - t ≫ T.mor₁
      hom_inv_id := by
        simp only [Preadditive.add_comp, Preadditive.comp_sub, Category.id_comp,
          Category.comp_id, h.comp_eq_zero t t]
        abel
      inv_hom_id := by
        simp only [Preadditive.sub_comp, Preadditive.comp_add, Category.id_comp,
          Category.comp_id, h.comp_eq_zero t t]
        abel }

/-- The unipotent automorphisms `𝟙 + t ≫ T.mor₁`, as a homomorphism from the group of
morphisms `T.obj₂ ⟶ T.obj₁` written multiplicatively. It is a homomorphism because the
product of two unipotent corrections vanishes. -/
@[simps]
def unipotentHom (h : T.HasSquareZeroMor₁) :
    Multiplicative (T.obj₂ ⟶ T.obj₁) →* Aut T.obj₂ where
  toFun t := unipotent h (Multiplicative.toAdd t)
  map_one' := by
    refine Aut.ext (Iso.ext ?_)
    have hl : (unipotent h (Multiplicative.toAdd
        (1 : Multiplicative (T.obj₂ ⟶ T.obj₁)))).asIso.hom =
          𝟙 T.obj₂ + (0 : T.obj₂ ⟶ T.obj₁) ≫ T.mor₁ := rfl
    have hr : (1 : Aut T.obj₂).asIso.hom = 𝟙 T.obj₂ := rfl
    rw [hl, hr, zero_comp, add_zero]
  map_mul' t s := by
    refine Aut.ext (Iso.ext ?_)
    have hl : (unipotent h (Multiplicative.toAdd (t * s))).asIso.hom =
        𝟙 T.obj₂ + (Multiplicative.toAdd t + Multiplicative.toAdd s) ≫ T.mor₁ := rfl
    have hr : (unipotent h (Multiplicative.toAdd t) *
        unipotent h (Multiplicative.toAdd s)).asIso.hom =
          (𝟙 T.obj₂ + Multiplicative.toAdd s ≫ T.mor₁) ≫
            (𝟙 T.obj₂ + Multiplicative.toAdd t ≫ T.mor₁) := rfl
    rw [hl, hr]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.id_comp, Category.comp_id,
      h.comp_eq_zero (Multiplicative.toAdd s) (Multiplicative.toAdd t), add_zero]
    abel

variable (T)

/-- The automorphisms of `T.obj₂` that fix `T.mor₂`, equivalently that induce the identity on
`T.obj₃` through `T.mor₂`. -/
def autFixingMor₂ : Subgroup (Aut T.obj₂) where
  carrier := {φ | φ.asIso.hom ≫ T.mor₂ = T.mor₂}
  mul_mem' {a b} ha hb := by
    change a.asIso.hom ≫ T.mor₂ = T.mor₂ at ha
    change b.asIso.hom ≫ T.mor₂ = T.mor₂ at hb
    exact (Category.assoc b.asIso.hom a.asIso.hom T.mor₂).trans (by rw [ha, hb])
  one_mem' := Category.id_comp T.mor₂
  inv_mem' {a} ha := by
    change a.asIso.hom ≫ T.mor₂ = T.mor₂ at ha
    exact (Iso.inv_comp_eq a.asIso).2 ha.symm

omit [Preadditive C] in
/-- An automorphism `φ` of `T.obj₂` lies in `T.autFixingMor₂` if and only if
`φ.asIso.hom ≫ T.mor₂ = T.mor₂`. -/
theorem mem_autFixingMor₂ {φ : Aut T.obj₂} :
    φ ∈ T.autFixingMor₂ ↔ φ.asIso.hom ≫ T.mor₂ = T.mor₂ := Iff.rfl

/-- The first morphism `T.obj₃⟦-1⟧ ⟶ T.obj₁` of the inverse rotation of `T`, with its source
and target written out. -/
noncomputable def invRotateMor₁ : T.obj₃⟦(-1 : ℤ)⟧ ⟶ T.obj₁ := T.invRotate.mor₁

/-- Postcomposition with `invRotateMor₁`, as a homomorphism of groups of morphisms out of
`T.obj₂`. -/
@[simps]
noncomputable def connecting :
    (T.obj₂ ⟶ T.obj₃⟦(-1 : ℤ)⟧) →+ (T.obj₂ ⟶ T.obj₁) where
  toFun g := g ≫ T.invRotateMor₁
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

end Unipotent

section Distinguished

variable [HasZeroObject C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] {T : Triangle C}

/-- The two consecutive morphisms `T.obj₃⟦-1⟧ ⟶ T.obj₁ ⟶ T.obj₂` of the inverse rotation of a
distinguished triangle compose to zero. -/
theorem invRotateMor₁_comp_mor₁ (hT : T ∈ distTriang C) :
    T.invRotateMor₁ ≫ T.mor₁ = 0 :=
  comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang T hT)

/-- Exactness of `Hom(X, -)` at `T.obj₁` along the inverse rotation of a distinguished
triangle: a morphism into `T.obj₁` killed by `T.mor₁` factors through `T.obj₃⟦-1⟧`. -/
theorem exists_comp_invRotateMor₁ (hT : T ∈ distTriang C) {X : C} (t : X ⟶ T.obj₁)
    (ht : t ≫ T.mor₁ = 0) : ∃ g : X ⟶ T.obj₃⟦(-1 : ℤ)⟧, t = g ≫ T.invRotateMor₁ :=
  Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang T hT) t ht

/-- An automorphism of `T.obj₂` fixes `T.mor₂` exactly when it is unipotent along `T.mor₁`.
The forward implication is exactness of `Hom(T.obj₂, -)` along the triangle. -/
theorem mem_autFixingMor₂_iff_exists (hT : T ∈ distTriang C) (φ : Aut T.obj₂) :
    φ ∈ T.autFixingMor₂ ↔ ∃ t : T.obj₂ ⟶ T.obj₁, φ.asIso.hom = 𝟙 T.obj₂ + t ≫ T.mor₁ := by
  rw [mem_autFixingMor₂]
  constructor
  · intro hφ
    obtain ⟨t, ht⟩ := Triangle.coyoneda_exact₂ T hT (φ.asIso.hom - 𝟙 T.obj₂)
      (by rw [Preadditive.sub_comp, Category.id_comp, hφ, sub_self])
    exact ⟨t, sub_eq_iff_eq_add'.1 ht⟩
  · rintro ⟨t, ht⟩
    rw [ht, Preadditive.add_comp, Category.id_comp, Category.assoc,
      comp_distTriang_mor_zero₁₂ T hT, comp_zero, add_zero]

/-- The unipotent automorphisms along `T.mor₁` are exactly the automorphisms of `T.obj₂`
fixing `T.mor₂`. -/
theorem unipotentHom_range (hT : T ∈ distTriang C) (h : T.HasSquareZeroMor₁) :
    (unipotentHom h).range = T.autFixingMor₂ := by
  refine le_antisymm (fun φ hφ => ?_) (fun φ hφ => ?_)
  · obtain ⟨t, ht⟩ := hφ
    refine (mem_autFixingMor₂_iff_exists hT φ).2 ⟨Multiplicative.toAdd t, ?_⟩
    rw [← ht, unipotentHom_apply, unipotent_asIso_hom]
  · obtain ⟨t, ht⟩ := (mem_autFixingMor₂_iff_exists hT φ).1 hφ
    refine ⟨Multiplicative.ofAdd t, Aut.ext (Iso.ext ?_)⟩
    rw [unipotentHom_apply, unipotent_asIso_hom]
    exact ht.symm

/-- A unipotent automorphism `𝟙 + t ≫ T.mor₁` is the identity exactly when `t` factors
through the morphism `T.obj₃⟦-1⟧ ⟶ T.obj₁` of the inverse rotation of `T`. -/
theorem unipotentHom_ker (hT : T ∈ distTriang C) (h : T.HasSquareZeroMor₁) :
    (unipotentHom h).ker = AddSubgroup.toSubgroup T.connecting.range := by
  have hone : (1 : Aut T.obj₂).asIso.hom = 𝟙 T.obj₂ := rfl
  ext t
  rw [MonoidHom.mem_ker, Multiplicative.mem_toSubgroup, AddMonoidHom.mem_range]
  constructor
  · intro ht
    have h1 : (unipotentHom h t).asIso.hom = (1 : Aut T.obj₂).asIso.hom := by rw [ht]
    rw [unipotentHom_apply, unipotent_asIso_hom, hone] at h1
    obtain ⟨g, hg⟩ := exists_comp_invRotateMor₁ hT (Multiplicative.toAdd t)
      (add_left_cancel (h1.trans (add_zero _).symm))
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, hg⟩
    refine Aut.ext (Iso.ext ?_)
    rw [unipotentHom_apply, unipotent_asIso_hom, hone, ← hg, connecting_apply, Category.assoc,
      invRotateMor₁_comp_mor₁ hT, comp_zero, add_zero]

/-- **The cokernel presentation.** The automorphisms of `T.obj₂` fixing `T.mor₂` are the
cokernel of `Hom(T.obj₂, T.obj₃⟦-1⟧) ⟶ Hom(T.obj₂, T.obj₁)`, by `unipotentHom_range` and
`unipotentHom_ker`. -/
noncomputable def autFixingMor₂MulEquiv (hT : T ∈ distTriang C) (h : T.HasSquareZeroMor₁) :
    Multiplicative (T.obj₂ ⟶ T.obj₁) ⧸ AddSubgroup.toSubgroup T.connecting.range ≃*
      T.autFixingMor₂ :=
  (QuotientGroup.quotientMulEquivOfEq (unipotentHom_ker hT h).symm).trans
    ((QuotientGroup.quotientKerEquivRange (unipotentHom h)).trans
      (MulEquiv.subgroupCongr (unipotentHom_range hT h)))

end Distinguished

end CategoryTheory.Pretriangulated.Triangle

end
