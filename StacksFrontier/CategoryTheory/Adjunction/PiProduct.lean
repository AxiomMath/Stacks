module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Pi.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.SquareZeroExtensionDerivedHom

/-!
# Restriction to the factors of a product decomposition, and its right adjoint

Let `F i : C ⥤ D i` be a family of left adjoints, with right adjoints `G i`, out of a category
`C` with products. The functor `Functor.pi' F : C ⥤ ∀ i, D i` is left adjoint to
`N ↦ ∏ i, (G i).obj (N i)`, because
`Hom((F i M)ᵢ, N) ≃ ∏ᵢ Hom(F i M, N i) ≃ ∏ᵢ Hom(M, G i (N i)) ≃ Hom(M, ∏ᵢ G i (N i))`.

If every counit `F i ∘ G i ⟶ 𝟭` is invertible, every `F k ∘ G i` with `i ≠ k` vanishes, the
`F k` preserve these products, and `Functor.pi' F` is faithful out of a balanced category, then
`Functor.pi' F` is an equivalence. This is the shape of the decomposition of sheaves on a
disjoint union by restriction to the summands.

## Main definitions

* `CategoryTheory.Adjunction.piProductHomEquiv`: the bijection above.
* `CategoryTheory.Adjunction.piProduct`: the adjunction `Functor.pi' F ⊣ (N ↦ ∏ᵢ G i (N i))`.

## Main results

* `CategoryTheory.Adjunction.piProduct_counit_app_apply`: the components of its counit.
* `CategoryTheory.Adjunction.isEquivalence_pi'_of_isZero`: the equivalence criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {ι : Type w} {C : Type u₁} [Category.{v₁} C] {D : ι → Type u₂}
  [∀ i, Category.{v₂} (D i)] {F : ∀ i, C ⥤ D i} {G : ∀ i, D i ⥤ C} (adj : ∀ i, F i ⊣ G i)
  [HasProductsOfShape ι C]

/-- The bijection `Hom((F i M)ᵢ, N) ≃ Hom(M, ∏ᵢ G i (N i))` assembled from the adjunctions
`F i ⊣ G i`. -/
def piProductHomEquiv (M : C) (N : ∀ i, D i) :
    ((Functor.pi' F).obj M ⟶ N) ≃ (M ⟶ ∏ᶜ fun i => (G i).obj (N i)) where
  toFun g := Pi.lift fun i => (adj i).homEquiv M (N i) (g i)
  invFun h i := ((adj i).homEquiv M (N i)).symm (h ≫ Pi.π _ i)
  left_inv g := by
    funext i
    exact (congrArg _ (Pi.lift_π _ i)).trans (Equiv.symm_apply_apply _ _)
  right_inv h := Pi.hom_ext _ _ fun i => (Pi.lift_π _ i).trans (Equiv.apply_symm_apply _ _)

/-- The `i`-th component of `piProductHomEquiv adj M N g` is the transpose of `g i` along
`F i ⊣ G i`. -/
theorem piProductHomEquiv_apply_π (M : C) (N : ∀ i, D i) (g : (Functor.pi' F).obj M ⟶ N)
    (i : ι) : piProductHomEquiv adj M N g ≫ Pi.π _ i = (adj i).homEquiv M (N i) (g i) :=
  Pi.lift_π _ i

/-- The `i`-th component of the inverse of `piProductHomEquiv` at `h` is the transpose of
`h ≫ Pi.π _ i` along `F i ⊣ G i`. -/
theorem piProductHomEquiv_symm_apply (M : C) (N : ∀ i, D i)
    (h : M ⟶ ∏ᶜ fun i => (G i).obj (N i)) (i : ι) :
    (piProductHomEquiv adj M N).symm h i = ((adj i).homEquiv M (N i)).symm (h ≫ Pi.π _ i) :=
  rfl

/-- `piProductHomEquiv` is natural in `M`. -/
theorem piProductHomEquiv_naturality (M' M : C) (N : ∀ i, D i) (f : M' ⟶ M)
    (g : (Functor.pi' F).obj M ⟶ N) :
    piProductHomEquiv adj M' N ((Functor.pi' F).map f ≫ g) = f ≫ piProductHomEquiv adj M N g :=
  Pi.hom_ext _ _ fun i => by
    rw [Category.assoc, piProductHomEquiv_apply_π, piProductHomEquiv_apply_π]
    exact (adj i).homEquiv_naturality_left f (g i)

/-- The functor `Functor.pi' F` is left adjoint to `N ↦ ∏ᵢ G i (N i)`. -/
def piProduct : Functor.pi' F ⊣
    rightAdjointOfEquiv (piProductHomEquiv adj) (piProductHomEquiv_naturality adj) :=
  adjunctionOfEquivRight _ _

/-- The counit of `piProduct` at the factor `k` is `F k` of the projection to `G k (N k)`,
followed by the counit of `F k ⊣ G k`. -/
theorem piProduct_counit_app_apply (N : ∀ i, D i) (k : ι) :
    (piProduct adj).counit.app N k =
      (F k).map (Pi.π (fun i => (G i).obj (N i)) k) ≫ (adj k).counit.app (N k) := by
  show ((adj k).homEquiv _ (N k)).symm
    (𝟙 (∏ᶜ fun i => (G i).obj (N i)) ≫ Pi.π (fun i => (G i).obj (N i)) k) = _
  rw [Category.id_comp, homEquiv_counit]

variable [∀ i, HasZeroMorphisms (D i)]

/-- The counit of `piProduct` is invertible as soon as every counit of `F i ⊣ G i` is, every
`F k ∘ G i` with `i ≠ k` vanishes and the `F k` preserve the products. -/
theorem isIso_piProduct_counit_app [∀ k, PreservesLimitsOfShape (Discrete ι) (F k)]
    (hcounit : ∀ i (N : D i), IsIso ((adj i).counit.app N))
    (hzero : ∀ k i, k ≠ i → ∀ N : D i, IsZero ((F k).obj ((G i).obj N))) (N : ∀ i, D i) :
    IsIso ((piProduct adj).counit.app N) := by
  classical
  refine (isIso_pi_iff _).2 fun k => ?_
  rw [piProduct_counit_app_apply]
  have hl : IsLimit (Fan.mk ((F k).obj (∏ᶜ fun i => (G i).obj (N i)))
      fun i => (F k).map (Pi.π (fun i => (G i).obj (N i)) i)) :=
    isLimitMapConeFanMkEquiv (F k) (fun i => (G i).obj (N i)) (Pi.π _)
      (isLimitOfPreserves (F k) (productIsProduct _))
  have h2 : IsIso ((F k).map (Pi.π (fun i => (G i).obj (N i)) k)) :=
    Stacks.SquareZeroExt.isIso_fan_proj_of_isZero _ hl k fun i hi => hzero k i (Ne.symm hi) (N i)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 (hcounit k (N k))

/-- **The equivalence criterion.** If every counit of `F i ⊣ G i` is invertible, every
`F k ∘ G i` with `i ≠ k` vanishes, the `F k` preserve the products and `Functor.pi' F` is
faithful out of a balanced category, then `Functor.pi' F : C ⥤ ∀ i, D i` is an equivalence. -/
theorem isEquivalence_pi'_of_isZero [Balanced C] [(Functor.pi' F).Faithful]
    [∀ k, PreservesLimitsOfShape (Discrete ι) (F k)]
    (hcounit : ∀ i (N : D i), IsIso ((adj i).counit.app N))
    (hzero : ∀ k i, k ≠ i → ∀ N : D i, IsZero ((F k).obj ((G i).obj N))) :
    (Functor.pi' F).IsEquivalence := by
  have := isIso_piProduct_counit_app adj hcounit hzero
  have : ∀ M, IsIso ((piProduct adj).unit.app M) := fun M => by
    have h := (piProduct adj).left_triangle_components M
    have : IsIso ((Functor.pi' F).map ((piProduct adj).unit.app M) ≫
        (piProduct adj).counit.app _) := by
      rw [h]; exact IsIso.id _
    have : IsIso ((Functor.pi' F).map ((piProduct adj).unit.app M)) :=
      IsIso.of_isIso_comp_right _ ((piProduct adj).counit.app _)
    exact isIso_of_reflects_iso _ (Functor.pi' F)
  exact (piProduct adj).toEquivalence.isEquivalence_functor

end CategoryTheory.Adjunction

end
