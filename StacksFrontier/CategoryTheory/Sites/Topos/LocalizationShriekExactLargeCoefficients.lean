module

public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationShriekExact
import StacksCore.Tactic.EgaSgaAttribute

/-! # Exactness of extension by zero on the site of elements, with large coefficients

Let `(C, J)` be a site whose morphisms live in `Type v`, and let `K` be a presheaf of sets on `C`
with values in `Type v`. `StacksFrontier.CategoryTheory.Sites.Topos.LocalizationShriekExact` proves
that extension by zero `j_!` along the projection `j : C/K ⥤ C` from the site of elements of `K`
is exact, and hence that restriction `j⁻¹` preserves injective abelian sheaves, for sheaves of
abelian groups in the universe `v` of the morphisms.

That universe is too small for a site whose objects are larger than its morphisms, such as the
lisse-étale and flat-fppf sites of an algebraic stack, whose objects form a `Type (u + 1)` while
the morphisms form a `Type u`: abelian sheaves on those are taken with coefficients in
`AddCommGrpCat.{max (u + 1) a}`, the universe in which sheafification and enough injectives are
available. This file proves the same statements with coefficients in `AddCommGrpCat.{max v t}`
for an arbitrary `t`.

The argument is unchanged. The value at `U` of the left Kan extension along `j.op` is the colimit
over `CostructuredArrow j.op U`, in which the discrete category on `K(U)` is final
(`Stacks.Sites.LocalizationShriek.Fiber.final`, which involves no coefficients and is reused), so
it is a coproduct indexed by `K(U) : Type v`. Such coproducts exist and are exact in
`AddCommGrpCat.{max v t}`, which satisfies AB4 for families of any size up to `max v t`.

## Main results

All in the namespace `Stacks.Sites.LocalizationShriek.LargeCoefficients`:

* `preservesFiniteLimits_lan`: the left Kan extension of abelian presheaves along `j.op` preserves
  finite limits.
* `preservesMonomorphisms_sheafPullback`: extension by zero preserves monomorphisms.
* `preservesInjectiveObjects_sheafPushforwardContinuous`: restriction to the site of
  elements preserves injective abelian sheaves (Stacks 03F3 (1) for a presheaf of sets, the first
  assertion of Stacks 07A0).

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace Stacks.Sites.LocalizationShriek.LargeCoefficients

variable {C : Type u} [Category.{v} C] (K : Cᵒᵖ ⥤ Type v)

/-- Coproducts indexed by the sections of `K` exist in `AddCommGrpCat.{max v t}`. -/
instance hasColimitsOfShape_discrete (X : Cᵒᵖ) :
    HasColimitsOfShape (Discrete (K.obj X)) AddCommGrpCat.{max v t} :=
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{t, v})

/-- Colimits indexed by the comma category of costructured arrows of `j.op` over `X` exist in
`AddCommGrpCat.{max v t}`: the diagrams are final over the discrete category on `K(X)`. -/
instance hasColimitsOfShape_costructuredArrow (X : Cᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (CostructuredArrow.proj yoneda K).op X)
      AddCommGrpCat.{max v t} :=
  Functor.Final.hasColimitsOfShape_of_final (Fiber.functor K X)

/-- Left Kan extension of abelian presheaves along `j.op` is computed pointwise. -/
instance hasPointwiseLeftKanExtension
    (P : (CostructuredArrow (yoneda (C := C)) K)ᵒᵖ ⥤ AddCommGrpCat.{max v t}) :
    (CostructuredArrow.proj yoneda K).op.HasPointwiseLeftKanExtension P :=
  fun _ => inferInstance

/-- Coproducts indexed by the sections of `K` are exact in `AddCommGrpCat.{max v t}`
(Grothendieck's axiom AB4). -/
theorem hasExactColimitsOfShape_discrete (X : Cᵒᵖ) :
    HasExactColimitsOfShape (Discrete (K.obj X)) AddCommGrpCat.{max v t} :=
  have : AB4OfSize.{v} AddCommGrpCat.{max v t} := AB4OfSize_shrink.{v, t} _
  inferInstance

/-- Colimits of the shape `CostructuredArrow j.op X` in `AddCommGrpCat.{max v t}` are exact: they
are coproducts indexed by the sections of `K`, by finality of the discrete fibre. -/
theorem hasExactColimitsOfShape_costructuredArrow (X : Cᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (CostructuredArrow.proj yoneda K).op X)
      AddCommGrpCat.{max v t} :=
  have := hasExactColimitsOfShape_discrete.{t} K X
  hasExactColimitsOfShape_of_final AddCommGrpCat.{max v t} (Fiber.functor K X)

/-- The left Kan extension of abelian presheaves along `j.op` preserves finite limits. -/
theorem preservesFiniteLimits_lan :
    PreservesFiniteLimits ((CostructuredArrow.proj (yoneda (C := C)) K).op.lan :
      ((CostructuredArrow yoneda K)ᵒᵖ ⥤ AddCommGrpCat.{max v t}) ⥤
        (Cᵒᵖ ⥤ AddCommGrpCat.{max v t})) := by
  apply preservesFiniteLimits_of_evaluation
  intro X
  have := hasExactColimitsOfShape_costructuredArrow.{t} K X
  have : PreservesFiniteLimits
      (colim (J := CostructuredArrow (CostructuredArrow.proj (yoneda (C := C)) K).op X)
        (C := AddCommGrpCat.{max v t})) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  exact preservesFiniteLimits_of_natIso
    (lanCompEvaluationIsoColim (E := AddCommGrpCat.{max v t})
      (CostructuredArrow.proj (yoneda (C := C)) K).op X).symm

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max v t}]

/-- Extension by zero from the site of elements of `K` to `C` preserves finite limits: it is the
left Kan extension along `j.op`, which is left exact, followed by sheafification. -/
theorem preservesFiniteLimits_sheafPullback :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (CostructuredArrow.proj (yoneda (C := C)) K) AddCommGrpCat.{max v t}
      ((CostructuredArrow.proj yoneda K).restrictedTopology J) J) := by
  have := preservesFiniteLimits_lan.{t} K
  have : PreservesFiniteLimits
      ((CostructuredArrow.proj (yoneda (C := C)) K).op.lan ⋙
        presheafToSheaf J AddCommGrpCat.{max v t}) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

/-- Extension by zero preserves monomorphisms, being left exact. -/
theorem preservesMonomorphisms_sheafPullback :
    (Functor.sheafPullbackConstruction.sheafPullback
      (CostructuredArrow.proj (yoneda (C := C)) K) AddCommGrpCat.{max v t}
      ((CostructuredArrow.proj yoneda K).restrictedTopology J) J).PreservesMonomorphisms :=
  have := preservesFiniteLimits_sheafPullback.{t} K J
  preservesMonomorphisms_of_preservesLimitsOfShape _

/-- **Stacks 03F3 (1) for a presheaf of sets, with coefficients in any universe containing the
morphisms of the site.** Restriction of abelian sheaves along the projection `j` from the site of
elements of `K` preserves injective objects: its left adjoint, extension by zero, is exact. -/
@[sga "4 V 2.2" "special case", sga "4 V 2.3.2" "special case"]
theorem preservesInjectiveObjects_sheafPushforwardContinuous :
    ((CostructuredArrow.proj (yoneda (C := C)) K).sheafPushforwardContinuous
      AddCommGrpCat.{max v t}
      ((CostructuredArrow.proj yoneda K).restrictedTopology J) J).PreservesInjectiveObjects :=
  have := preservesMonomorphisms_sheafPullback.{t} K J
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (CostructuredArrow.proj (yoneda (C := C)) K) AddCommGrpCat.{max v t}
      ((CostructuredArrow.proj yoneda K).restrictedTopology J) J)

end Stacks.Sites.LocalizationShriek.LargeCoefficients

end
