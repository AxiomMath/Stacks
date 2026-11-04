module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications

/-!
# The isomorphism case of Stacks 02TA for the Gysin system of the first Chern class rule

`Stacks.Chow.GysinSystem.IsNaturalUnderInverseIso` is the case of Stacks 02TA that transports the
Gysin axiom of a bivariant class across the base change of an identity morphism: for an
isomorphism `u : A ⟶ B` over the base with inverse `w` and an invertible module `L` on `A`, the
Gysin map of `(w^*L, w^*s)` on `B` is the Gysin map of `(L, s)` on `A` conjugated by `u` and by a
morphism `j` of the two zero schemes lying over `u`. This file proves it for the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`, whose Gysin map is the one of Stacks 02TO.

The argument applies the proper case of Stacks 02TA,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderProperPushforward`, to the proper morphism
`w : B ⟶ A` and the module `L` on `A` itself, so that no two invertible modules have to be
compared: the module on `B` the conclusion speaks about is `w^*L`, which is the one that
statement produces. Taking the class `u_*α` and using `u ≫ w = 𝟙` collapses `w_* u_* α` to `α`,
and the morphism of Remark 0B6Y for `w` is inverse to `j`, because `j` lies over `u` and a closed
immersion is a monomorphism.

This is the one statement of that case in the library; the Chow cohomology ring of Stacks 0B7E
and the first Chern class of Stacks 0B7B consume it from here.

## Main results

* `Stacks.Chow.GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso` — the isomorphism
  case of Stacks 02TA for `Stacks.Chow.gysinSystemOfInvertible`.

## References

* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

open Stacks.Divisors

/-- **The isomorphism case of Stacks 02TA for the Gysin system of the first Chern class rule**,
with the invertible module on the source of the isomorphism: for an isomorphism `u : A ⟶ B` over
the base with inverse `w`, an invertible module `L` on `A`, a section `s` of it and a morphism `j`
of zero schemes lying over `u`, the Gysin map of `(w^*L, w^*s)` on `B` applied to `u_*α` is
`j_*` of the Gysin map of `(L, s)` on `A` applied to `α`.

Stacks 02TA for the proper morphism `w` and the module `L` on `A` itself,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderProperPushforward`, gives
`i^* w_* β = (j'')_* (i')^* β` for the morphism `j''` of Remark 0B6Y; at `β = u_* α` the left
side collapses since `u ≫ w = 𝟙`, and `j'' ≫ j = 𝟙` because `j` lies over `u` and a closed
immersion is a monomorphism. -/
@[stacks 02TA "the inverse-isomorphism case of the naturality of the Gysin operation of a Gysin \
system, for the system of the first Chern class rule of an invertible module"]
theorem gysinSystemOfInvertible_isNaturalUnderInverseIso (C : ChowSituation.{u}) :
    (gysinSystemOfInvertible C).IsNaturalUnderInverseIso := by
  intro A B pA _ pB _ u _ w huw hu L _ _ s k j _ hj hsq hfac α
  have hw : w = inv u := (IsIso.inv_eq_of_hom_inv_id huw).symm
  have : IsIso w := by rw [hw]; infer_instance
  have hwu : w ≫ u = 𝟙 B := by rw [hw, IsIso.inv_hom_id]
  have hwA : w ≫ pA = pB := by rw [hw, IsIso.inv_comp_eq]; exact hu.symm
  have hj'' : zeroSchemePullbackHom w L s ≫ (Stacks.Divisors.zeroScheme A L s).subschemeι =
      (pullbackZeroScheme w L s).subschemeι ≫ w :=
    zeroSchemePullbackHom_subschemeι w L s
  have hinv : zeroSchemePullbackHom w L s ≫ j = 𝟙 (pullbackZeroScheme w L s).subscheme := by
    refine (cancel_mono (pullbackZeroScheme w L s).subschemeι).1 ?_
    rw [Category.assoc, hsq, ← Category.assoc, hj'', Category.assoc, hwu, Category.comp_id,
      Category.id_comp]
  have hjbase : (zeroSchemePullbackHom w L s ≫ j) ≫
      ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback w).obj L)
        (AlgebraicGeometry.pullbackGlobalSections w L s)).subschemeι ≫ pB) =
      (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback w).obj L)
        (AlgebraicGeometry.pullbackGlobalSections w L s)).subschemeι ≫ pB := by
    rw [hinv, Category.id_comp]
  have hsq' := zeroSchemeSquare_comp_structureMorphism C pB pA w hwA L s
    (zeroSchemePullbackHom w L s) hj''
  have hF := properPushforwardFactorsThroughRationalEquivalence C pB pA w hwA (k + 1)
  have hkey := gysinSystemOfInvertible_isNaturalUnderProperPushforward C pB pA w hwA L s k
    (zeroSchemePullbackHom w L s) hj'' hF
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ hsq' k)
    (chowPushforwardOfIso C pA pB u hu (k + 1) α)
  have hcomp := congrFun (congrArg DFunLike.coe
    (properChowPushforward_comp C pA pB pA u w hu hwA (k + 1)
      (properPushforwardFactorsThroughRationalEquivalence C pA pB u hu (k + 1))
      hF)) α
  rw [AddMonoidHom.coe_comp, Function.comp_apply] at hcomp
  have hid : properChowPushforward C pB pA w hwA (k + 1)
      hF (chowPushforwardOfIso C pA pB u hu (k + 1) α) = α := by
    rw [chowPushforwardOfIso, hcomp,
      properChowPushforward_congr_hom C pA pA huw (by rw [Category.assoc, hwA]; exact hu)
        (Category.id_comp pA) (k + 1) _
        (properPushforwardFactorsThroughRationalEquivalence C pA pA (𝟙 A)
          (Category.id_comp pA) (k + 1)) α,
      properChowPushforward_id]
    rfl
  rw [hid] at hkey
  rw [hkey, ← properChowPushforward_comp_apply C
      ((pullbackZeroScheme w L s).subschemeι ≫ pB)
      ((Stacks.Divisors.zeroScheme A L s).subschemeι ≫ pA)
      ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback w).obj L)
        (AlgebraicGeometry.pullbackGlobalSections w L s)).subschemeι ≫ pB)
      (zeroSchemePullbackHom w L s) j (zeroSchemePullbackHom w L s ≫ j) rfl
      hsq' hj hjbase k
      (properPushforwardFactorsThroughRationalEquivalence C _ _ _ hsq' k) hfac
      (properPushforwardFactorsThroughRationalEquivalence C _ _ _ hjbase k),
    properChowPushforward_congr_hom C _ _ hinv hjbase (Category.id_comp _) k _
      (properPushforwardFactorsThroughRationalEquivalence C _ _ (𝟙 _) (Category.id_comp _) k),
    properChowPushforward_id]
  rfl

end Stacks.Chow.GenuineChern

end
