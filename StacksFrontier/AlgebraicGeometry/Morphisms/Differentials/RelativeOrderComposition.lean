module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderCategory
public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsChangeOfRings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Differential operators relative to a composite morphism

The order of a differential operator does not increase when the sheaf of rings of scalars
with respect to which it is linear is replaced by a smaller one: for morphisms of sheaves of
rings `χ : O₀ ⟶ O₁` and `φ : O₁ ⟶ O₂`, a differential operator of order at most `k`
relative to `φ` is one of order at most `k` relative to `χ ≫ φ`. For schemes this says that
a differential operator on `X/Y` is a differential operator of the same order on `X/Z`
whenever `X ⟶ Y ⟶ Z`, and in particular that a differential operator on a fibre product
`X ×_S Y` taken relative to the projection to `Y` is one of the same order relative to the
structure morphism to `S`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeStructureSheafCompMap`: the inverse image along
  `f : X ⟶ Y` of the relative structure sheaf map of `g : Y ⟶ Z`, a morphism of sheaves of
  rings `(f ≫ g)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y` on `X`.

## Main results

* `DiffOp.isGlobalDiffOpOfOrder_ringMapComp`: a differential operator of order at most `k`
  relative to `φ` is one of order at most `k` relative to `χ ≫ φ`.
* `AlgebraicGeometry.Scheme.Hom.relativeStructureSheafMap_comp`: the relative structure
  sheaf map of `f ≫ g` factors through the relative structure sheaf map of `f`.
* `AlgebraicGeometry.isGlobalDiffOpOfOrder_comp`: a differential operator of order at most
  `k` on `X/Y` is a differential operator of order at most `k` on `X/Z`, for `X ⟶ Y ⟶ Z`.
* `AlgebraicGeometry.isGlobalDiffOpOfOrder_pullbackSnd`: a differential operator of order at
  most `k` on `X ×_S Y / Y` is one of order at most `k` on `X ×_S Y / S`.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.homOfPullbackSnd`: a
  finite-order differential operator on `X ×_S Y / Y` is a morphism of the category of
  finite-order differential operators on `X ×_S Y / S`.

## References

* [Stacks Project, Tag 09CR](https://stacks.math.columbia.edu/tag/09CR)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat

universe v u w m

namespace DiffOp

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O₀ O₁ O₂ : Sheaf J RingCat.{w}}

/-- A differential operator of order at most `k` relative to `φ : O₁ ⟶ O₂` is a differential
operator of order at most `k` relative to `χ ≫ φ`, for any `χ : O₀ ⟶ O₁`. -/
theorem isGlobalDiffOpOfOrder_ringMapComp (χ : O₀ ⟶ O₁) (φ : O₁ ⟶ O₂) (k : ℕ)
    {F G : SheafOfModules.{max u v w m} O₂} (D : GlobalOp F G)
    (h : IsGlobalDiffOpOfOrder φ k D) : IsGlobalDiffOpOfOrder (χ ≫ φ) k D :=
  fun U ↦ AlgebraicGeometry.SheafOfModules.isDiffOpOfOrder_precompRaw.{v, u, w, m}
    (χ ≫ φ) φ (𝟙 O₂) F F k χ (by simp) (𝟙 F) _ (h U)

end DiffOp

namespace AlgebraicGeometry

/-- The inverse image along `f : X ⟶ Y` of the relative structure sheaf map of `g : Y ⟶ Z`:
a morphism of sheaves of rings `(f ≫ g)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y` on `X`. It is described by the
adjoint morphism `𝒪_Z ⟶ (f ≫ g)_*f⁻¹𝒪_Y`, namely the morphism `𝒪_Z ⟶ g_*𝒪_Y` attached to
`g` followed by the unit of the inverse image–direct image adjunction for `f`. -/
noncomputable abbrev Scheme.Hom.relativeStructureSheafCompMap {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Sheaf.pullback RingCat.{u} (f ≫ g).base).obj Z.ringCatSheaf ⟶
      (Sheaf.pullback RingCat.{u} f.base).obj Y.ringCatSheaf :=
  ((Sheaf.pullbackPushforwardAdjunction RingCat.{u} (f ≫ g).base).homEquiv _ _).symm
    (g.toRingCatSheafHom ≫ (Sheaf.pushforward RingCat.{u} g.base).map
      ((Sheaf.pullbackPushforwardAdjunction RingCat.{u} f.base).unit.app Y.ringCatSheaf))

/-- The relative structure sheaf map of a composite `f ≫ g` of morphisms of schemes factors
through the relative structure sheaf map of `f`. -/
@[ega "I 2.2.2" "partial"]
theorem Scheme.Hom.relativeStructureSheafMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (f ≫ g).relativeStructureSheafMap
      = f.relativeStructureSheafCompMap g ≫ f.relativeStructureSheafMap := by
  have hf : (Sheaf.pullbackPushforwardAdjunction RingCat.{u} f.base).unit.app Y.ringCatSheaf ≫
      (Sheaf.pushforward RingCat.{u} f.base).map f.relativeStructureSheafMap
        = f.toRingCatSheafHom :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have key : ((Sheaf.pullbackPushforwardAdjunction RingCat.{u} (f ≫ g).base).homEquiv _ _)
        (f.relativeStructureSheafCompMap g ≫ f.relativeStructureSheafMap)
      = g.toRingCatSheafHom ≫ (Sheaf.pushforward RingCat.{u} g.base).map
          f.toRingCatSheafHom :=
    (Adjunction.homEquiv_naturality_right _ _ _).trans <|
      (congrArg (· ≫ (Sheaf.pushforward RingCat.{u} (f ≫ g).base).map
          f.relativeStructureSheafMap) (Equiv.apply_symm_apply _ _)).trans <|
        (Category.assoc _ _ _).trans <|
          congrArg (g.toRingCatSheafHom ≫ ·)
            ((((Sheaf.pushforward RingCat.{u} g.base).map_comp _ _).symm).trans
              (congrArg (Sheaf.pushforward RingCat.{u} g.base).map hf))
  exact (Equiv.symm_apply_eq _).2 key.symm

/-- A differential operator of order at most `k` on `X/Y` is a differential operator of
order at most `k` on `X/Z`, for morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`. -/
theorem isGlobalDiffOpOfOrder_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℕ)
    {F G : X.Modules} (D : DiffOp.GlobalOp F G)
    (h : DiffOp.IsGlobalDiffOpOfOrder f.relativeStructureSheafMap k D) :
    DiffOp.IsGlobalDiffOpOfOrder (f ≫ g).relativeStructureSheafMap k D :=
  Scheme.Hom.relativeStructureSheafMap_comp f g ▸
    DiffOp.isGlobalDiffOpOfOrder_ringMapComp.{u, u, u, u}
      (f.relativeStructureSheafCompMap g) f.relativeStructureSheafMap k D h

/-- A differential operator of order at most `k` on `X ×_S Y / Y`, taken relative to the
second projection, is a differential operator of order at most `k` on `X ×_S Y / S`. -/
theorem isGlobalDiffOpOfOrder_pullbackSnd {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (k : ℕ) {F G : (pullback a b).Modules} (D : DiffOp.GlobalOp F G)
    (h : DiffOp.IsGlobalDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k D) :
    DiffOp.IsGlobalDiffOpOfOrder (pullback.fst a b ≫ a).relativeStructureSheafMap k D :=
  (pullback.condition (f := a) (g := b)).symm ▸
    isGlobalDiffOpOfOrder_comp (pullback.snd a b) b k D h

/-- A global operator which is a differential operator of some finite order on
`X ×_S Y / Y`, taken relative to the second projection, is a morphism of the category of
finite-order differential operators on `X ×_S Y / S`. -/
noncomputable def FiniteOrderDifferentialOperatorCategory.homOfPullbackSnd
    {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}
    (F G : FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a))
    (D : DiffOp.GlobalOp F.module G.module)
    (h : ∃ k, DiffOp.IsGlobalDiffOpOfOrder
      (pullback.snd a b).relativeStructureSheafMap k D) : F ⟶ G :=
  ⟨D, h.imp fun k hk ↦ isGlobalDiffOpOfOrder_pullbackSnd a b k D hk⟩

end AlgebraicGeometry

end
