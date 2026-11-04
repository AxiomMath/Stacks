module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinKeyFormula
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme

/-!
# The Gysin identity behind the deformation to the normal cone

Let `M` be a scheme locally of finite type over the base of δ-dimension at most `k + 2`, let
`a` be a function on `M` and `(L, b)` an invertible module with a section whose zero scheme `Z(b)`
is an effective Cartier divisor, and let `N ⊆ Z(b)` be a closed subscheme of δ-dimension at
most `k + 1` meeting `Z(a)` in an effective Cartier divisor of `N`, such that `[Z(b)]` and `[N]`
have the same coefficients away from `Z(a)`. Then

  `b|_{Z(a)}^* a^* [M] = [N ∩ Z(a)]`  in  `CH_k(Z(a) ∩ Z(b))`.

Indeed by [Stacks, Tag 0B73] the left-hand side is `a|_{Z(b)}^* b^* [M] = a|_{Z(b)}^* [Z(b)]`;
`[Z(b)] - [N]` comes from `Z(a) ∩ Z(b)`, where the restriction of `𝒪_M` is trivial so that the
Gysin map kills it; and `a|_{Z(b)}^* [N] = [N ∩ Z(a)]` by [Stacks, Tag 02TB].
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {M : Scheme.{u}} (p : M ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (a : Γ(Scheme.unitModule M, ⊤)) (L : M.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible M.sheaf.obj M.ringCatSheaf.property L]
  (b : Γ(L, ⊤))

/-- The coefficient of the pushforward of a cycle along a closed immersion at an image point. -/
theorem properPushforward_apply_image {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
    (d : ℤ) (c : CycleGroup C sZ d) (z : Z) :
    (properPushforward C sZ sX i hi d c).1 (i z) = c.1 z :=
  properPushforward_apply_image_of_isClosedImmersion C sZ sX i hi d c z

/-- **The Gysin identity of the deformation to the normal cone.** -/
theorem deformation_gysin_identity
    (hM : schemeDeltaDimension C p ≤ ((k + 1 + 1 : ℤ) : EInt))
    (hb : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme M L b))
    (N : (Stacks.Divisors.zeroScheme M L b).subscheme.IdealSheafData)
    (hN : schemeDeltaDimension C
        (N.subschemeι ≫ (Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) ≤
      ((k + 1 : ℤ) : EInt))
    (hNa : Stacks.Divisors.IsEffectiveCartierDivisor
      ((zeroSchemeInter L (Scheme.unitModule M) b a).comap N.subschemeι))
    (hagree : ∀ y : (Stacks.Divisors.zeroScheme M L b).subscheme,
      y ∉ Set.range (zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι.base →
        (fundamentalCycle C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) (k + 1)).1 y =
          (cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
            N.subschemeι (k + 1)).1 y)
    (e : (zeroSchemeInter (Scheme.unitModule M) L a b).subscheme ≅
      (zeroSchemeInter L (Scheme.unitModule M) b a).subscheme)
    (he : e.hom ≫ (zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι ≫
        (Stacks.Divisors.zeroScheme M L b).subschemeι =
      (zeroSchemeInter (Scheme.unitModule M) L a b).subschemeι ≫
        (Stacks.Divisors.zeroScheme M (Scheme.unitModule M) a).subschemeι) :
    chowPushforwardOfIso C ((zeroSchemeInter (Scheme.unitModule M) L a b).subschemeι ≫
          (Stacks.Divisors.zeroScheme M (Scheme.unitModule M) a).subschemeι ≫ p)
        ((zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι ≫
          (Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
        e.hom (iso_zeroSchemeInter_comp_structureMorphism C p _ L a b e he) k
        (gysinChowOfInvertible C
          ((Stacks.Divisors.zeroScheme M (Scheme.unitModule M) a).subschemeι ≫ p) k
          (zeroSchemeRestrictModule (Scheme.unitModule M) L a)
          (restrictSectionToZeroScheme (Scheme.unitModule M) L a b)
          (gysinChowOfInvertible C p (k + 1) (Scheme.unitModule M) a
            (fundamentalChowClass C p (k + 1 + 1)))) =
      QuotientAddGroup.mk' (rationalEquivalences C
        ((zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι ≫
          (Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) k)
        (cycleAssociatedToClosedSubscheme C
          ((zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι ≫
            (Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
          ((N.comap (zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι).subschemeι) k) := by
  rw [gysinChowOfInvertible_comm C p k (Scheme.unitModule M) L a b e he,
    gysinChowOfInvertible_fundamentalChowClass C p (k + 1) L b hM hb]
  -- `[Z(b)] = [N] + (a class from Z(a) ∩ Z(b))`
  let δ : CycleGroup C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) (k + 1) :=
    fundamentalCycle C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) (k + 1) -
      cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
        N.subschemeι (k + 1)
  have hδ : ∀ y : (Stacks.Divisors.zeroScheme M L b).subscheme,
      y ∉ Set.range (zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι.base → δ.1 y = 0 := by
    intro y hy
    change (fundamentalCycle C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) (k + 1)).1 y -
      (cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
        N.subschemeι (k + 1)).1 y = 0
    rw [hagree y hy, sub_self]
  have hδ' := properPushforward_cyclePullbackAlongClosedImmersion_eq C
    ((zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι ≫
      (Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
    ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
    (zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι rfl (k + 1) δ hδ
  have hsplit :
      fundamentalChowClass C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) (k + 1) =
        QuotientAddGroup.mk'
          (rationalEquivalences C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) (k + 1))
          (cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
            N.subschemeι (k + 1)) +
        chowPushforwardOfIsClosedImmersion C _ ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
          (zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι rfl (k + 1)
          (QuotientAddGroup.mk' _ (cyclePullbackAlongClosedImmersion C
            ((zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι ≫
              (Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
            ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p)
            (zeroSchemeInter L (Scheme.unitModule M) b a).subschemeι rfl (k + 1) δ)) := by
    rw [chowPushforwardOfIsClosedImmersion_mk, hδ', ← map_add]
    simp only [δ, add_sub_cancel]
    rfl
  rw [hsplit, map_add, gysinChowOfInvertible_pushforward_eq_zero C
      ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) k
      (zeroSchemeRestrictModule L (Scheme.unitModule M) b)
      (restrictSectionToZeroScheme L (Scheme.unitModule M) b a)
      (Scheme.Modules.pullbackUnitIso (Stacks.Divisors.zeroScheme M L b).subschemeι), add_zero,
    gysinChowOfInvertible_mk]
  have hs : (Stacks.Divisors.sectionsOfTop _ (restrictSectionToZeroScheme L
      (Scheme.unitModule M) b a)).eval (op ⊤) = restrictSectionToZeroScheme L
      (Scheme.unitModule M) b a := Stacks.Divisors.sectionsOfTop_eval_top _ _
  have key := gysinHomomorphismOfInvertible_cycleAssociatedToClosedSubscheme C
    ((Stacks.Divisors.zeroScheme M L b).subschemeι ≫ p) k
    (zeroSchemeRestrictModule L (Scheme.unitModule M) b)
    (Stacks.Divisors.sectionsOfTop _ (restrictSectionToZeroScheme L (Scheme.unitModule M) b a))
    N hN
    (by rw [hs]; exact hNa)
  rw [hs] at key
  exact key

end Stacks.Chow

end
