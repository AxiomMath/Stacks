module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicPictureChain
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraMultiplicationDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraStructureProof
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicPictureBridges
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor square of a coherent module with proper support, in the canonical spelling

The multiplication of an algebra sheaf on `X` is a morphism out of a tensor square of a sheaf of
modules on `X`, and the Stacks 088F equivalence moves such a morphism only once its source is an
object of `Stacks.Algebraization.CoherentModulesProperOver f`. This file records, for the tensor
product bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` of [Stacks, Tag 0GMW], that the
tensor product of two coherent modules is coherent, that its support is contained in the support
of either factor, and that its support is proper over the base as soon as one factor's is.

At a scheme this tensor product and the sheafified tensor product of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace` are the same term after
unfolding (`Stacks.TensorSheafDedup.tensorSheaf_eq`), so the proofs are the corresponding results
for the latter, `AlgebraicGeometry.notMem_supp_tensorSheaf_of_notMem_supp` (Tag 01CB) and
`AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent` (Tag 01CE(6)), applied by `exact`. In
particular `AlgebraicGeometry.tensorBifunctorSquareProperOver` is
`AlgebraicGeometry.tensorSquareProperOver`.

The last result concerns the reduction of `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` to
a `Stacks.FundamentalGroup.ModuleAlgebraData` on the algebraization. Producing that structure
means descending the multiplication of an algebra system along the Stacks 088F equivalence, and
recovering a morphism of modules from a morphism of adic systems is fullness of
`AlgebraicGeometry.adicThickeningCompletionFunctor`. So the data hypothesis should be allowed to
use the equivalence; `adicFiniteAlgebraAlgebraization_of_moduleAlgebraData_of_isEquivalence`
states the reduction in that form.

## Main results

* `AlgebraicGeometry.notMem_supp_tensorSheafBifunctor_of_notMem_supp`,
  `AlgebraicGeometry.isCoherent_tensorBifunctorObj`,
  `AlgebraicGeometry.hasProperSupport_tensorSheafBifunctor`: the support containment, the
  coherence and the proper support of `((sheafTensor _).obj F).obj G`.
* `AlgebraicGeometry.tensorBifunctorSquareProperOver`: the tensor square as an object of
  `Stacks.Algebraization.CoherentModulesProperOver f`, an alias of
  `AlgebraicGeometry.tensorSquareProperOver`.
* `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData_of_isEquivalence`: the
  reduction of `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` to a data hypothesis that may
  use the Stacks 088F equivalence.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Algebraization (HasProperSupport)
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.AffineAlgebraEquivalence (algebraPullback)

universe u

namespace AlgebraicGeometry

/-! ### The support, the coherence and the proper support of a tensor product -/

/-- **The support of a tensor product is contained in the support of either factor**, for the
tensor product bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` of [Stacks, Tag 0GMW].

The stalk of a tensor product at a point is the tensor product of the stalks (Tag 01CB), which
is zero once one factor's stalk is. -/
theorem notMem_supp_tensorSheafBifunctor_of_notMem_supp {X : Scheme.{u}} (F G : X.Modules)
    {y : X} (hy : y ∉ _root_.SheafOfModules.supp F) :
    y ∉ _root_.SheafOfModules.supp
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G) :=
  notMem_supp_tensorSheaf_of_notMem_supp F G hy

/-- **The tensor product of two coherent sheaves of modules on a scheme is coherent**, for the
tensor product bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` of [Stacks, Tag 0GMW]
(Tag 01CE(6)). -/
@[ega "0 5.3.5" "special case"]
theorem isCoherent_tensorBifunctorObj {X : Scheme.{u}} (F G : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent.{u} F) (hG : _root_.SheafOfModules.IsCoherent.{u} G) :
    _root_.SheafOfModules.IsCoherent.{u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G) :=
  @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F G hF hG

/-- **A tensor product has support proper over the base as soon as one factor does**, for the
tensor product bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` of [Stacks, Tag 0GMW].

The support of the tensor product is closed because the tensor product is coherent
(`AlgebraicGeometry.isCoherent_tensorBifunctorObj`), it is contained in the support of the first
factor (`AlgebraicGeometry.notMem_supp_tensorSheafBifunctor_of_notMem_supp`), and a closed subset
of a closed subset proper over the base is proper over the base
(`AlgebraicGeometry.isProperOver_of_le`). -/
theorem hasProperSupport_tensorSheafBifunctor {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F G : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent.{u} F) (hG : _root_.SheafOfModules.IsCoherent.{u} G)
    (hFp : HasProperSupport f F) :
    HasProperSupport f
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G) := by
  have := isCoherent_tensorBifunctorObj F G hF hG
  have : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
      (M := ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G)
  obtain ⟨Z, hZ, hZproper⟩ := hFp
  refine ⟨⟨_root_.SheafOfModules.supp
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G),
    _root_.SheafOfModules.isClosed_supp _⟩, rfl, ?_⟩
  refine isProperOver_of_le f ?_ hZproper
  change _root_.SheafOfModules.supp
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G) ≤ (Z : Set X)
  rw [hZ]
  intro x hx
  by_contra hxF
  exact notMem_supp_tensorSheafBifunctor_of_notMem_supp F G hxF hx

/-- **The tensor square of a coherent module with proper support, as an object of the category the
Stacks 088F equivalence lives on**, written with the tensor product bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` of [Stacks, Tag 0GMW]. This is
`AlgebraicGeometry.tensorSquareProperOver` itself. -/
alias tensorBifunctorSquareProperOver := tensorSquareProperOver

/-! ### The reduction with the equivalence available to the data hypothesis -/

/-- **The reduction of `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` to a `hdata` that may
use the Stacks 088F equivalence.**

This is `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData` with the data
hypothesis `hdata` allowed to assume `(adicThickeningCompletionFunctor A I f).IsEquivalence`.
Building a `Stacks.FundamentalGroup.ModuleAlgebraData` on `P.obj.obj` from the multiplication of
the system, a morphism of systems, uses fullness of
`AlgebraicGeometry.adicThickeningCompletionFunctor`, which the equivalence provides. The
statement is stronger than the one it is built from: a `hdata` proved without the equivalence
gives one here by discarding it. -/
theorem adicFiniteAlgebraAlgebraization_of_moduleAlgebraData_of_isEquivalence
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
    (hdata : (adicThickeningCompletionFunctor A I f).IsEquivalence →
      ∀ (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
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
  adicFiniteAlgebraAlgebraization_of_moduleAlgebraData A I f h088F hpullback (hdata h088F)

end AlgebraicGeometry

end
