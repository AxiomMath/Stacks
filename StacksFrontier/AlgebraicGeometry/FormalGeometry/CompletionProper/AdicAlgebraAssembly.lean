module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningEssSurj
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AlgebraPullbackQuasicoherent

/-!
# Algebraization of adic systems of finite algebras from module-algebra data

Let `A` be a Noetherian ring, `I`-adically complete, and `f : X ⟶ Spec A` a separated morphism
of finite type. This file shows that `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization A I f`
holds as soon as every coherent module on `X` whose completion is the module system of a system of
quasi-coherent algebras on the thickenings carries module-algebra data recovering that system.

## Main results

* `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_hdata`: adic systems of finite
  quasi-coherent algebras over `f` algebraize, given module-algebra data `hdata` on every coherent
  module whose completion is the module system of the algebras.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.AffineAlgebraEquivalence

universe u

namespace AlgebraicGeometry

open Stacks.Algebraization (HasProperSupport)

/-- Let `A` be a Noetherian `I`-adically complete ring and `f : X ⟶ Spec A` a separated morphism
of finite type. Suppose that for every cartesian system `B` of quasi-coherent algebras on the
thickenings with coherent underlying modules, the first with proper support, every coherent module
`P` on `X` with proper support whose completion is isomorphic to the module system of `B` carries
module-algebra data whose algebra sheaf pulls back to each `B n`. Then
`AdicFiniteAlgebraAlgebraization A I f` holds. -/
public theorem adicFiniteAlgebraAlgebraization_of_hdata (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdata : ∀ (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
        AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
      (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
      (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
      (hBtrans : ∀ n, Nonempty
        ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
      (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
      (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
        (AlgebraSheaf.underlyingModule (B 0)))
      (P : Stacks.Algebraization.CoherentModulesProperOver f),
      ((adicThickeningCompletionFunctor A I f).obj P ≅
          adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0) →
        ∃ d : Stacks.FundamentalGroup.ModuleAlgebraData P.obj.obj, ∀ n, Nonempty
          ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj
            (Stacks.FundamentalGroup.algebraSheafOfModule P.obj.obj d) ≅ B n)) :
    AdicFiniteAlgebraAlgebraization A I f :=
  adicFiniteAlgebraAlgebraization_of_h088F_of_hdata A I f
    (isEquivalence_adicThickeningCompletionFunctor A I f) hdata

end AlgebraicGeometry

end
