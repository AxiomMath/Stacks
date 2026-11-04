module
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The lower shriek of a continuous functor which has a left adjoint

Let `(C, J)` and `(D, K)` be sites and let `G : C ⥤ D` be a continuous functor. Restriction along
`G` sends sheaves on `D` to sheaves on `C` (Stacks 00WW); this is the inverse image functor
`g⁻¹ = G.sheafPushforwardContinuous A J K` of the morphism of topoi `g : Sh(C) ⥤ Sh(D)` attached
to `G` (Stacks 00XO, 00XR), and `g_!` denotes a left adjoint of it (Stacks 00XR (2)).

Suppose `G` has a left adjoint `W : D ⥤ C`. Then restriction along `W` is the left Kan extension
along `G` on presheaves (Stacks 09VQ (5)), so the sheafification of `V ↦ F(W V)` is a left adjoint
of `g⁻¹`: the lower shriek is computed without any colimit. Consequently `g_!` is exact — it
preserves finite limits, since finite limits of sheaves are computed in presheaves, restriction
computes them pointwise and sheafification is left exact (Stacks 00WJ) — and it preserves all
colimits, being a left adjoint. If moreover `W` is continuous, restriction along `W` already lands
in sheaves, so `g_!` is itself a right adjoint (Stacks 00WX) and hence has a left adjoint. If `W`
is cocontinuous and `h : Sh(D) ⥤ Sh(C)` is the morphism of topoi attached to `W`, then
`g_! = h⁻¹` — both are the sheafification of restriction along `W` — and `g⁻¹ = h_*`, that is,
restriction along `G` on sheaves is computed by the right Kan extension along `W`.

## Main results

* `nonempty_adjunction_preservesFiniteLimits_isRightAdjoint_and_iso_sheafPushforwardCocontinuous`
  (in the `CategoryTheory.Adjunction` namespace): the parts of Stacks 08NH, in order, as the four
  conjuncts of one statement, all of them about the functor
  `Λ = sheafToPresheaf J A ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj W.op ⋙ presheafToSheaf K A`,
  the sheafification of restriction along the left adjoint `W`:
  (1)(a) `Λ` is a left adjoint of `G.sheafPushforwardContinuous A J K`, i.e. `Λ` is `g_!`;
  (1)(b) `Λ` preserves finite limits when sheafification for `K` does;
  (2) `Λ` has itself a left adjoint when `W` is continuous;
  (3) `G.sheafPushforwardContinuous A J K ≅ W.sheafPushforwardCocontinuous A K J` when `W` is
  cocontinuous, i.e. `g⁻¹ = h_*`.

## Implementation notes

Departures from the form of the source, none of them weakenings.

* Sheaves take values in an arbitrary category `A` rather than in sets; the source's topoi are the
  case `A = Type (max u₁ v₁ u₂ v₂)`, where every instance hypothesis below holds. The functors are
  Mathlib's: `g⁻¹` is `Functor.sheafPushforwardContinuous`, `h_*` is
  `Functor.sheafPushforwardCocontinuous`
  (the right Kan extension along `W.op`, Stacks 00XK), and a left adjoint of `g⁻¹` is what Mathlib
  calls `Functor.sheafPullback`.
* The source assumes `u` continuous *and* cocontinuous, so that `g` is a morphism of topoi. Only
  continuity is assumed here: cocontinuity of `G` produces `g_*` and enters no part of the
  conclusion, so it is dropped rather than carried as decoration. Continuity of `G` is used
  throughout — it is what makes `g⁻¹` restriction along `G`.
* Continuity is Mathlib's `Functor.IsContinuous`: precomposition with `G.op` preserves sheaves
  (SGA 4 III 1.5). That is the *conclusion* of Stacks 00WW, and it is exactly what `g⁻¹` being
  restriction along `G` requires, so it is the hypothesis here; the source's Definition 00WV
  (coverings go to coverings, compatibly with the fibre products) is strictly stronger, as Stacks
  0H6Z shows, and assuming it would narrow the statement. Cocontinuity is Mathlib's
  `Functor.IsCocontinuous`, which is Stacks 00XI in sieve form. In part (3) continuity of `G` is
  not an extra assumption at all: `CategoryTheory.Adjunction.isContinuous_of_isCocontinuous`
  derives it from `adj` and cocontinuity of `W`.
* Part (1)(a) is stated as an adjunction rather than as an isomorphism with
  `Functor.sheafPullback`: in that form it does not have to assume that `g_!` exists (Stacks 00XR
  (2)), it proves it. For a chosen `g_!`, i.e. an `L ⊣ G.sheafPushforwardContinuous A J K`,
  uniqueness of left adjoints turns the conjunct into `L ≅ Λ`, which is the source's wording, and
  transports (1)(b) and (2) to `L`.
* Part (1)(b) asks for `PreservesFiniteLimits` only: exactness of a functor which is a left adjoint
  by (1)(a) is left exactness, preservation of colimits being automatic.
* Part (2), "`g_!` has a left adjoint", is `Λ.IsRightAdjoint`: Mathlib's `Functor.IsRightAdjoint F`
  asserts that `F` has a *left* adjoint, and `Functor.IsLeftAdjoint F` that it has a right one, so
  `Λ.IsLeftAdjoint` would state the converse of the source, and would already follow from conjunct
  (1)(a) on its own. The left adjoint the source exhibits is `w_s` (Stacks 00WX): for continuous
  `W`, restriction along `W` already lands in sheaves, so `Λ` is
  `W.sheafPushforwardContinuous A K J` and `w_s` is `W.sheafPullback A K J`. Accordingly the three
  binders of the conjunct are exactly those under which
  `CategoryTheory.Functor.sheafPullbackConstruction` builds that left adjoint.
* Part (3) has two halves in the source, `g_! = h⁻¹` and `g⁻¹ = h_*`. The first is conjunct (1)(a):
  for a merely cocontinuous `W` the functor `h⁻¹` is by definition the sheafification of
  restriction along `W`, which is `Λ` on the nose. Only the second half is a further statement.
* The hypotheses each part needs beyond the ambient ones are instance-implicit binders inside that
  conjunct: left exactness of sheafification for (1)(b), continuity of `W` and the existence of the
  sheafification and left Kan extensions that build `w_s` for (2), continuity being replaced by
  cocontinuity of `W` and left by right Kan extensions for (3). This keeps each part stated under
  exactly the hypotheses of the corresponding part of the source.

Faithfulness.

1. No hypothesis is dead: `adj` is used by every conjunct (it is what makes `Λ` the lower shriek),
   `G.IsContinuous J K` is what makes `G.sheafPushforwardContinuous A J K` be `g⁻¹`,
   `HasWeakSheafify K A` is what makes `Λ` exist, and the per-conjunct binders are the extra
   hypotheses of parts (1)(b), (2) and (3) of the source.
2. The sites and coefficients are the source's: `J` on `C`, `K` on `D`, restriction along `W` and
   its sheafification taken for `K`, restriction along `G` for `J`, and no other topology enters.
3. The functors are pinned, not merely asserted to exist: `g_!` is the named composite `Λ`, so
   (1)(a) says that the sheafification of `w^p` *is* the lower shriek, and (3) is an isomorphism
   between two named functors rather than the existence of some isomorphism between adjoints.
4. Not degenerate: `C = D`, `G = W = 𝟭 C`, `J = K` and `A = Type (max u₁ v₁)` satisfy every
   hypothesis of all four parts, with `Λ ≅ 𝟭 (Sheaf J A)`. A witness in which `G` is not an
   equivalence is
   Stacks 00XP: for `U` an open subspace of a topological space `X`, take `C = X_{Zar}`,
   `D = U_{Zar}`, for `G` the continuous functor `V ↦ V ∩ U` and for `W` the inclusion of the opens
   of `U` among those of `X`, which is a left adjoint of `G` and is both continuous and
   cocontinuous, so that all four parts apply; there `g⁻¹` is the pushforward `j_*` and
   `g_! = h⁻¹` is restriction of sheaves to `U`.

## References

* [Stacks 08NH](https://stacks.math.columbia.edu/tag/08NH), `sites-lemma-have-left-adjoint`.
  The identification of restriction along `W` with the left Kan extension along `G` on presheaves
  is Stacks 09VQ, the source's route to part (3) is Stacks 00XX, the left adjoint `w_s` of part (2)
  is Stacks 00WX, and the morphism of topoi attached to a cocontinuous functor is Stacks 00XO.
-/

namespace CategoryTheory.Adjunction

section

universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory Limits Opposite

namespace Stacks.Sites.LowerShriekAdjoint

section Sites

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (A : Type u₃)
  [Category.{v₃} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D) {G : C ⥤ D}
  {W : D ⥤ C}

/-- **Stacks 08NH (1)(a)**: for a continuous `G : C ⥤ D` with left adjoint `W : D ⥤ C`, the
sheafification `Λ` of restriction along `W` is a left adjoint of `g⁻¹`, restriction along `G`;
that is, the lower shriek `g_!` is `F ↦ (w^p F)^#`.

Restriction along `W.op` is left adjoint to restriction along `G.op`, and sheafification for `K`
is left adjoint to the inclusion of sheaves; the composite adjunction restricts along the fully
faithful inclusion `sheafToPresheaf J A` because `g⁻¹` is restriction along `G` on sheaves. -/
private noncomputable def sheafifiedRestrictionAdjunction (adj : W ⊣ G) [G.IsContinuous J K]
    [HasWeakSheafify K A] :
    sheafToPresheaf J A ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj W.op ⋙ presheafToSheaf K A ⊣
      G.sheafPushforwardContinuous A J K :=
  ((Functor.whiskeringLeftAdjunctionOfAdjunction A adj).comp
        (sheafificationAdjunction K A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

end Sites

end Stacks.Sites.LowerShriekAdjoint

@[expose] public section

open Stacks.Sites.LowerShriekAdjoint in
/-- **Stacks 08NH.** Let `(C, J)` and `(D, K)` be sites, let `G : C ⥤ D` be a continuous functor,
and let `W : D ⥤ C` be a left adjoint of `G`. Write
`Λ = sheafToPresheaf J A ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj W.op ⋙ presheafToSheaf K A`
for the functor sending a sheaf `F` on `C` to the sheafification of the presheaf `V ↦ F(W V)`,
that is, of `w^p F`. Then:

1. (a) `Λ` is a left adjoint of `g⁻¹ = G.sheafPushforwardContinuous A J K`, i.e. the lower shriek
   `g_!` is the sheafification of `w^p`;
   (b) `Λ` preserves finite limits, hence is exact, as soon as sheafification for `K` does;
2. if `W` is continuous, then `Λ` has itself a left adjoint, i.e. `Λ.IsRightAdjoint`;
3. if `W` is cocontinuous and `h : Sh(D) ⥤ Sh(C)` is the associated morphism of topoi, then
   `g⁻¹ = h_*`, that is `G.sheafPushforwardContinuous A J K ≅ W.sheafPushforwardCocontinuous A K J`
   (the other half of part (3), `g_! = h⁻¹`, is conjunct 1(a): `h⁻¹` is `Λ`).

The conjuncts are the parts of the source, in order. -/
@[stacks 08NH "Lower shriek of a continuous functor which has a left adjoint.",
  sga "4 III 2.5" "v_*≃u_s and v^*≃u^s",
  sga "4 III 1.3" "special case",
  sga "4 III 2.4" "special case"]
public theorem
  nonempty_adjunction_preservesFiniteLimits_isRightAdjoint_and_iso_sheafPushforwardCocontinuous
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (A : Type u₃) [Category.{v₃} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) {G : C ⥤ D} {W : D ⥤ C} (adj : W ⊣ G)
    [G.IsContinuous J K] [HasWeakSheafify K A] :
    -- (1)(a) `g_!` is the sheafification of `w^p`
    Nonempty
        (sheafToPresheaf J A ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj W.op ⋙ presheafToSheaf K A ⊣
          G.sheafPushforwardContinuous A J K) ∧
      -- (1)(b) `g_!` is exact
      (∀ [HasFiniteLimits A] [PreservesFiniteLimits (presheafToSheaf K A)],
        PreservesFiniteLimits
          (sheafToPresheaf J A ⋙
            (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj W.op ⋙ presheafToSheaf K A)) ∧
      -- (2) if `w` is continuous, then `g_!` has a left adjoint
      (∀ [W.IsContinuous K J] [HasWeakSheafify J A] [∀ F : Dᵒᵖ ⥤ A, W.op.HasLeftKanExtension F],
        (sheafToPresheaf J A ⋙
            (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj W.op ⋙ presheafToSheaf K A).IsRightAdjoint) ∧
      -- (3) if `w` is cocontinuous, then `g⁻¹ = h_*`
      (∀ [W.IsCocontinuous K J] [∀ F : Dᵒᵖ ⥤ A, W.op.HasPointwiseRightKanExtension F],
        Nonempty (G.sheafPushforwardContinuous A J K ≅ W.sheafPushforwardCocontinuous A K J)) := by
  refine ⟨⟨sheafifiedRestrictionAdjunction A J K adj⟩, ?_, ?_, ?_⟩
  · -- (1)(b) the three functors `Λ` is composed of are left exact.
    intro _ _
    have :
      PreservesFiniteLimits ((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj W.op ⋙ presheafToSheaf K A) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  · -- (2) for continuous `W`, `Λ` is restriction along `W`, which is a lower shriek.
    intro _ _ _
    have e :
      sheafToPresheaf J A ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj W.op ⋙ presheafToSheaf K A ≅
        W.sheafPushforwardContinuous A K J :=
      Adjunction.leftAdjointUniq (sheafifiedRestrictionAdjunction A J K adj)
        (adj.sheafPushforwardContinuous K J)
    exact ((W.sheafAdjunctionLowerShriek A K J).ofNatIsoRight e.symm).isRightAdjoint
  · -- (3) `g⁻¹ = h_*`: both are restriction along `G` on underlying presheaves.
    intro _ _
    have e :
      W.sheafPushforwardCocontinuous A K J ⋙ sheafToPresheaf J A ≅
        sheafToPresheaf K A ⋙ (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op :=
      Functor.sheafPushforwardCocontinuousIsoRestriction (A := A) (J := K) (K := J) (adj := adj)
    exact
      ⟨Functor.fullyFaithfulCancelRight (sheafToPresheaf J A)
          ((G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).trans e.symm)⟩

end

end

end CategoryTheory.Adjunction
