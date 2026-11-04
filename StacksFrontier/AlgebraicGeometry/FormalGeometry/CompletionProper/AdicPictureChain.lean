module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraStructureSystemProof
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicPictureBridges

/-!
# The chain to Grothendieck existence for finite sheaves of algebras

`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` — Grothendieck existence for finite sheaves of
algebras, the input of [Stacks, Tag 09ZT] — follows from the equivalence of [Stacks, Tag 088F],
the identification of the pullbacks of the completion, and the construction of the algebra data
on the algebraized module. This file states that reduction.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.TwistMultTransport (tensorSheafMap_comp)

universe u

namespace AlgebraicGeometry

/-! ### Grothendieck existence for finite sheaves of algebras from three inputs -/

section Chain

open Stacks.Algebraization (HasProperSupport)
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.AffineAlgebraEquivalence

/-- Let `A` be a Noetherian ring, complete with respect to an ideal `I`, and let
`f : X ⟶ Spec A` be separated, locally of finite type and quasi-compact. Then Grothendieck
existence for finite sheaves of algebras,
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization A I f`, holds provided that:

* `h088F`: the completion functor `AlgebraicGeometry.adicThickeningCompletionFunctor A I f` is an
  equivalence;
* `hpullback`: for every quasi-coherent sheaf of algebras, the module underlying its algebra
  pullback is identified with the module pullback, as in
  `AlgebraicGeometry.AlgebraPullbackModuleIso`;
* `hdata`: every coherent module with proper support whose completion is isomorphic to the module
  system of an adic system `B` of quasi-coherent sheaves of algebras carries a
  `Stacks.FundamentalGroup.ModuleAlgebraData` whose algebra sheaf restricts to `B`. -/
public theorem adicFiniteAlgebraAlgebraization_of_moduleAlgebraData (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
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
  adicFiniteAlgebraAlgebraization_of_systemTransport A I f h088F hpullback
    (adicAlgebraStructureSystemTransport_of_moduleAlgebraData A I f hdata)

end Chain

end AlgebraicGeometry

end
