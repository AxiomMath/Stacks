module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CoefficientHypotheses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.Definition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.TensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of constructible sheaves of modules, without coefficient hypotheses

Let `X` be a scheme and let `Λ` be a Noetherian ring. The tensor product of two constructible
sheaves of `Λ`-modules on `X_étale` is a constructible sheaf of `Λ`-modules. This is Stacks 095I,
stated here for the constructibility predicate `AlgebraicGeometry.IsConstructibleModuleEtaleSheaf`
of Tag 03RW (3), which asks the restriction to each stratum to be of finite type and locally
constant and takes no typeclass argument beyond `Λ` Noetherian.

## Main results

* `AlgebraicGeometry.isConstructibleModuleEtaleSheaf_tensor` — Stacks 095I.

## Implementation notes

The tensor product is the one of `CategoryTheory.Sheaf.monoidalCategory`, the sheafification of
the objectwise tensor product over `Λ`, activated as a local instance as in Tags 093V and 095D.
`ModuleCat.{s} Λ` is monoidal only for `Λ : Type s`, and the small étale site has objects in
`Type (u + 1)`, so the coefficient ring lives in `Type (max (u + 1) w)`; at that universe the
sheafification of the small étale site and of its localizations is found by instance search.

The proof is that of `Stacks.EtaleCohomology.isConstructibleModuleSheaf_tensor`, which carries
the right adjointness of small étale direct image as an instance argument. Here that argument is
proved, by `AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat`, and the
two constructibility predicates are identified by
`AlgebraicGeometry.isConstructibleModuleEtaleSheaf_iff`.

## References

* [Stacks Project, Tag 095I](https://stacks.math.columbia.edu/tag/095I)
* [Stacks Project, Tag 095D](https://stacks.math.columbia.edu/tag/095D)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe w u

attribute [local instance] Sheaf.monoidalCategory

namespace AlgebraicGeometry

/-- **Stacks 095I.** Let `X` be a scheme and `Λ` a Noetherian ring. The tensor product of two
constructible sheaves of `Λ`-modules on `X_étale` is a constructible sheaf of `Λ`-modules. -/
@[stacks 095I]
public theorem isConstructibleModuleEtaleSheaf_tensor (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type (max (u + 1) w)) [CommRing Λ] [IsNoetherianRing Λ]
    (F G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))
    (hF : IsConstructibleModuleEtaleSheaf B X Λ F) (hG : IsConstructibleModuleEtaleSheaf B X Λ G) :
    IsConstructibleModuleEtaleSheaf B X Λ (F ⊗ G) := by
  let : ∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := fun S T f =>
    SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat.{w} B Λ S T f
  exact (isConstructibleModuleEtaleSheaf_iff B X Λ _).2
    (Stacks.EtaleCohomology.isConstructibleModuleSheaf_tensor B X Λ F G
      ((isConstructibleModuleEtaleSheaf_iff B X Λ F).1 hF)
      ((isConstructibleModuleEtaleSheaf_iff B X Λ G).1 hG))

end AlgebraicGeometry

end
