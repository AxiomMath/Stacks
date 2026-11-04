module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningTransitionDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraStructureSystemProof

/-!
# The unit of an algebraized system of algebra sheaves

The structure morphisms `𝒪_{Xₙ} ⟶ ℬₙ` of a cartesian system of quasi-coherent algebra sheaves on
the adic thickenings `Xₙ` are compatible with the transitions, so through the completion
functor of [Stacks, Tag 088F] they come from a single morphism `𝒪_X ⟶ 𝒩` on `X`. This is the unit
of the algebra structure on the algebraization.

## Main results

* `AlgebraicGeometry.unitModuleMap_comp_comp_adicThickeningCompletionTransition`: the structure
  morphisms of the system, read on the algebraization, are compatible with the transitions.
* `AlgebraicGeometry.exists_unit_of_adicAlgebraModuleSystem`: there is a morphism `𝒪_X ⟶ 𝒩`
  restricting to the structure morphism of every `B n`.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Descent (pushUnit pushUnit_app pullbackCompHom
  unit_pullbackPushforwardAdjunction_comp pushforwardCongr_rfl_hom pullbackCongr_rfl_hom)
open Stacks.AlgebraicGeometry.AffineBaseChange (unitObj pullbackUnitIso structureUnitHom
  unit_comp_map_pullbackUnitIso structureUnitHom_comp)

/-! ### The family a cartesian system of algebra sheaves gives -/

section Algebra

open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.RelativeSpec.AlgebraSheaf (unitModuleMap)
open Stacks.Algebraization (HasProperSupport)

/-- Pasting a commutative square `c ≫ d = t ≫ k` onto a factorization `a ≫ b ≫ t = s`. -/
private theorem comp_comp_comp_eq_comp {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    {a : O₁ ⟶ O₂} {b : O₂ ⟶ O₃} {c : O₃ ⟶ O₄} {d : O₄ ⟶ O₅} {t : O₃ ⟶ O₆} {k : O₆ ⟶ O₅}
    {s : O₁ ⟶ O₆} (hcd : c ≫ d = t ≫ k) (hs : a ≫ b ≫ t = s) :
    a ≫ (b ≫ c) ≫ d = s ≫ k := by
  subst hs
  simp [hcd]

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsLocallyNoetherian X] [LocallyOfFiniteType f]
  (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
    AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
  (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
  (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
  (hBtrans : ∀ n, Nonempty
    ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
  (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
  (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
    (AlgebraSheaf.underlyingModule (B 0)))
  (P : Stacks.Algebraization.CoherentModulesProperOver f)
  (e : (adicThickeningCompletionFunctor A I f).obj P ≅
    adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0)

omit [IsLocallyNoetherian X] in
/-- The structure morphisms of a cartesian system of algebra sheaves, read on an algebraization,
are compatible with the transitions: the family `uₙ = 𝒪_{Xₙ} ⟶ ℳₙ ⟶ 𝒩|_{Xₙ}`, the structure
morphism of `B n` followed by the `n`-th component of the inverse of `e`, commutes with the
transitions of the completion of `𝒩`. -/
public theorem unitModuleMap_comp_comp_adicThickeningCompletionTransition (n : ℕ) :
    (pullbackUnitIso (adicBaseChangeSucc A I f n)).inv ≫
        (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map
            (unitModuleMap (B (n + 1)) ≫ e.inv.app (n + 1)) ≫
          (adicThickeningCompletionTransition A I f P.obj.obj n).hom =
      unitModuleMap (B n) ≫ e.inv.app n := by
  refine Eq.trans (congrArg (fun z =>
      (pullbackUnitIso (adicBaseChangeSucc A I f n)).inv ≫ z ≫
        (adicThickeningCompletionTransition A I f P.obj.obj n).hom)
    ((Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map_comp
      (unitModuleMap (B (n + 1))) (e.inv.app (n + 1)))) ?_
  exact comp_comp_comp_eq_comp (e.inv.comm n)
    (unitModuleMap_comp_adicAlgebraModuleSystem_transitionIso A I f hpullback B hqc hBtrans
      hMcoh hM0 n)

/-- Let `(B n)` be a cartesian system of quasi-coherent algebra sheaves on the adic thickenings
whose underlying modules are coherent with proper support at `n = 0`, let `𝒩` be a coherent
module with proper support over an `I`-adically complete Noetherian base, and let `e` identify the
completion of `𝒩` with the system of the underlying modules. Then there is a morphism
`μ : 𝒪_X ⟶ 𝒩` on `X` whose restriction to every `Xₙ` is the structure morphism of `B n`, read
through `e`. -/
public theorem exists_unit_of_adicAlgebraModuleSystem [IsAdicComplete I A] :
    ∃ μ : SheafOfModules.unit X.ringCatSheaf ⟶ P.obj.obj, ∀ n : ℕ,
      (pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).inv ≫
          (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        unitModuleMap (B n) ≫ e.inv.app n :=
  exists_unit_of_adicThickeningTransitionFamily A I f P.obj P.property
    (fun n => unitModuleMap (B n) ≫ e.inv.app n)
    (unitModuleMap_comp_comp_adicThickeningCompletionTransition A I f hpullback B hqc hBtrans
      hMcoh hM0 P e)

end Algebra

end AlgebraicGeometry

end
