module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorClosedImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforwardSupplement

/-!
# Variants of the Quot functor results for pushforward along a closed immersion

The declarations below extend
`StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorClosedImmersionPushforward` and are kept in a module
of their own so that that module stays unchanged. A primed name `X'` is a variant of the declaration
`X` there.

## Main declarations

* `ClosedImmersionQuotInputs'`
* `pushforwardQuotient_injective'`
* `exists_pushforwardQuotient_eq'`
* `isIso_quotFunctorMap'`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS)

/-- **The two inputs of the proof of Stacks 0DP4 which this development does not have**, bundled.

The first field is the *essential-image* assertion of Stacks 04CJ, part (3), in the form the
argument consumes: every quotient of `G_T = π_{T,*}F_T` is a direct image along `π_T`.  In the
source this is the statement that `π_{T,*}` is an equivalence onto the `𝒪_{Y_T}`-modules
annihilated by the ideal cutting out `X_T`, applied to a quotient of `G_T`, which is so
annihilated because `G_T` is.  Only the annihilation half of that assertion is proved in this
development, as `AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`; the
essential-image half is available only as
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`, under its own hypothesis
`hsurj`, which is the essential-image assertion of Stacks 04E5.

The second field is the reverse direction of the morphism of stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of
Stacks 0DN9: the four conditions of Stacks 09TR descend along `π_{T,*}`.  Its forward direction
is the field `pushforwardMem` of
`AlgebraicGeometry.Space.QuotPushforwardSituation.AffinePushforwardQuotInputs`, carried by
Stacks 0DP1 for the same reason. -/
structure ClosedImmersionQuotInputs' (D : QuotPushforwardSituation B S hS) where
  /-- **The essential-image assertion of Stacks 04CJ, part (3) for the situation**: a quotient of
  `G_T` is a direct image along `π_T`. -/
  essImage_quotientModule : ∀ (T : SchemesOver D.base)
      (K : Subobject (D.targetSituation'.baseChangeModule T)),
    (modulePushforward B S hS (D.baseChangeOfMap T)).essImage
      (D.targetSituation'.quotientModule T K)
  /-- **Stacks 0DN9 for the situation, in the reverse direction**: a module whose direct image
  along `π_T` satisfies the four conditions of Stacks 09TR over `T` satisfies them itself. -/
  isQuotModule_of_pushforward : ∀ (T : SchemesOver D.base)
      (Q : Modules.{u, u} B S hS (D.sourceSituation.space T).1 (D.sourceSituation.space T).2),
    D.targetSituation'.IsQuotModule T
        ((modulePushforward B S hS (D.baseChangeOfMap T)).obj Q) →
      D.sourceSituation.IsQuotModule T Q

/-- **The direct image of quotients along a closed immersion is injective**, by full faithfulness
of `π_{T,*}` (Stacks 04CJ). -/
theorem pushforwardQuotient_injective' (c : PushforwardComparison D)
    (hπ : IsClosedImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) :
    Function.Injective (D.pushforwardQuotient' c T) :=
  D.pushforwardQuotient_injective_of_fullyFaithful' c T
    (D.fullyFaithfulPushforwardBaseChangeOfMap hπ T)

/-- **Every member of `Quot_{G/Y/B}(T)` is the direct image of a member of
`Quot_{F/X/B}(T)`.**  The quotient of `G_T` by it is a direct image along `π_T` by the first
carried input, so it is the direct image of a quotient of `F_T`; the four conditions of
Stacks 09TR for that quotient of `F_T` are the second carried input. -/
theorem exists_pushforwardQuotient_eq' (I : D.AffinePushforwardQuotInputs')
    (J : D.ClosedImmersionQuotInputs')
    (hπ : IsClosedImmersion B S hS D.π.hom) (T : SchemesOver D.base)
    (K' : Subobject (D.targetSituation'.baseChangeModule T))
    (hK' : K' ∈ D.targetSituation'.properlySupportedQuotients T) :
    ∃ K ∈ D.sourceSituation.properlySupportedQuotients T,
      D.pushforwardQuotient' I.comparison T K = K' := by
  obtain ⟨K, hconj, ⟨ι⟩⟩ := Functor.exists_conjSubobject_eq (I.comparison.iso T)
    (D.fullyFaithfulPushforwardBaseChangeOfMap hπ T) K' (J.essImage_quotientModule T K')
  exact ⟨K, (D.sourceSituation.mem_properlySupportedQuotients_iff T K).mpr
    (J.isQuotModule_of_pushforward T (D.sourceSituation.quotientModule T K)
      (QuotSituation.IsQuotModule.of_iso ι.symm
        ((D.targetSituation'.mem_properlySupportedQuotients_iff T K').mp hK'))), hconj⟩

/-- **Stacks 0DP4.**  The morphism of Quot functors `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` induced by
the direct image along a closed immersion is an isomorphism: over every test scheme it is a
bijection, injectively by full faithfulness of `π_{T,*}` (Stacks 04CJ) and surjectively by the
two carried inputs. -/
theorem isIso_quotFunctorMap' (I : D.AffinePushforwardQuotInputs')
    (J : D.ClosedImmersionQuotInputs')
    (hπ : IsClosedImmersion B S hS D.π.hom) :
    IsIso (D.quotFunctorMap' I) := by
  have happ : ∀ T, IsIso ((D.quotFunctorMap' I).app T) := fun T => by
    rw [isIso_iff_bijective]
    refine ⟨fun x y hxy => Subtype.ext
      (D.pushforwardQuotient_injective' I.comparison hπ T.unop (congrArg Subtype.val hxy)),
      fun y => ?_⟩
    obtain ⟨K, hK, hconj⟩ := D.exists_pushforwardQuotient_eq' I J hπ T.unop y.1 y.2
    exact ⟨⟨K, hK⟩, Subtype.ext hconj⟩
  exact NatIso.isIso_of_isIso_app _

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
