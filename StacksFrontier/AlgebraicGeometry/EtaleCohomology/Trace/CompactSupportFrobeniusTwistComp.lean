module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedTwistEndoComp

/-!
# The canonical Frobenius followed by an endomorphism, as a single twisted endomorphism

For a bounded below complex `K` on `X_étale` and an endomorphism `ψ` of `K`, the endomorphism
`π_X^* ≫ RΓ_c(ψ)` of `RΓ_c(X_k̄, K)` is the derived twisted endomorphism attached to the twist
`τ ≫ π̄_*(ψ|)` of the restriction of `j_! K` to `X̄_k̄`, where `τ` is the canonical Frobenius
twist.  In Step 8 of the proof of [Tag 03UG] this applies with `ψ` the action of a deck
transformation, `(g, π_U^*)` being `π_U^* ∘ g`.

## Main results

* `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius_comp_map_eq_derivedTwistEndo`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **`π_X^* ≫ RΓ_c(ψ)` is the twisted endomorphism of the twist `τ ≫ π̄_*(ψ|)`.** -/
theorem canonicalCompactSupportFrobenius_comp_map_eq_derivedTwistEndo
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (ψ : K ⟶ K) :
    canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard K ≫
        (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map ψ =
      Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (frobeniusDirectImageComp Λ f j kbar p q hcard)
        ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K))
          (Y := (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q
              hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)))
          ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard)
            (ComplexShape.up ℤ)).app
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K).obj) ≫
          (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q
              hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
                ψ))) := by
  rw [Functor.derivedTwistEndo_comp_mapCochainComplexPlus_map,
    ← canonicalCompactSupportFrobenius_eq_derivedTwistEndo]
  rfl

end Stacks.EtaleCohomology

end
