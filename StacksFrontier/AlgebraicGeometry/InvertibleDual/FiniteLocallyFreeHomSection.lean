module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DualBasisRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorDualSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.HomSection
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# `ℳ ⊗ ℰ^∨ ≅ 𝓗om(ℰ, ℳ)` for a finite locally free `ℰ` on a scheme

Let `X` be a scheme, `ℰ` a sheaf of `𝒪_X`-modules which is finite locally free of constant rank
`r` ([Stacks, Tag 01C6] clause (3)) and `ℳ` an arbitrary sheaf of `𝒪_X`-modules. Then the
canonical rank-one morphism

  `ℳ ⊗_{𝒪_X} 𝓗om(ℰ, 𝒪_X) ⟶ 𝓗om(ℰ, ℳ)`

is an isomorphism.

## Main results

* `Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_isFiniteLocallyFreeOfRank`: the canonical
  morphism is an isomorphism.
* `Stacks.SheafOfModules.tensorDualIsoSheafHomOfRank`: the isomorphism `ℳ ⊗ ℰ^∨ ≅ 𝓗om(ℰ, ℳ)`.
* `Stacks.SheafOfModules.Scheme.tensorDualIsoSheafHomOfRank`: the same isomorphism, with the
  internal hom written as `Stacks.Algebraization.sheafHomFunctor`.
* `Stacks.SheafOfModules.Scheme.dualTensorIsoSheafHomOfRank`: the isomorphism
  `ℰ^∨ ⊗ ℳ ≅ 𝓗om(ℰ, ℳ)`.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.SheafOfModules

variable {X : Scheme.{u}}

/-- For `ℰ` finite locally free of constant rank and `ℳ` arbitrary, the canonical rank-one
morphism `ℳ ⊗_{𝒪_X} 𝓗om(ℰ, 𝒪_X) ⟶ 𝓗om(ℰ, ℳ)` is an isomorphism. -/
@[ega "0 5.4.2" "special case"]
public theorem isIso_tensorDualToSheafHom_of_isFiniteLocallyFreeOfRank
    (E M : X.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    IsIso (tensorDualToSheafHom X.sheaf.obj X.ringCatSheaf.property E M) := by
  classical
  obtain ⟨q, hq, hr⟩ := hE.exists_isFiniteLocallyFreeOfRankData
  let : ∀ i : q.I, Fintype ((q.generators i).I) :=
    fun i => Fintype.ofEquiv (Fin r) (hr i).some.symm
  refine isIso_tensorDualToSheafHom X.sheaf.obj X.ringCatSheaf.property q.coversTop
    (I := fun i => (q.generators i).I) (fun i => ?_) M
  have := hq.isIso i
  let e := asIso (q.generators i).π
  exact FiniteDualBasis.ofRetract _ _ ⟨e.inv, e.hom, e.inv_hom_id⟩

/-- The isomorphism `ℳ ⊗ ℰ^∨ ≅ 𝓗om(ℰ, ℳ)` on a scheme, for `ℰ` finite locally free of constant
rank and `ℳ` arbitrary, whose underlying morphism is `Stacks.SheafOfModules.tensorDualToSheafHom`.
-/
public def tensorDualIsoSheafHomOfRank (E M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
          X.ringCatSheaf.property⟩).obj M).obj
        (dualSheaf X.sheaf.obj X.ringCatSheaf.property E) ≅
      sheafHom X.sheaf.obj X.ringCatSheaf.property E M :=
  haveI := isIso_tensorDualToSheafHom_of_isFiniteLocallyFreeOfRank E M r
  asIso (tensorDualToSheafHom X.sheaf.obj X.ringCatSheaf.property E M)

/-- The isomorphism `ℳ ⊗ ℰ^∨ ≅ 𝓗om(ℰ, ℳ)` of `Stacks.SheafOfModules.tensorDualIsoSheafHomOfRank`,
with the internal hom written as `Stacks.Algebraization.sheafHomFunctor`. -/
public def Scheme.tensorDualIsoSheafHomOfRank (E M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    Scheme.tensorDualTwist E M ≅ (Stacks.Algebraization.sheafHomFunctor X E).obj M :=
  _root_.Stacks.SheafOfModules.tensorDualIsoSheafHomOfRank E M r

/-- The isomorphism `ℰ^∨ ⊗ ℳ ≅ 𝓗om(ℰ, ℳ)` for `ℰ` finite locally free of constant rank: the
isomorphism `Stacks.SheafOfModules.Scheme.tensorDualIsoSheafHomOfRank` composed with the symmetry
of the tensor product. -/
public def Scheme.dualTensorIsoSheafHomOfRank (E M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
          X.ringCatSheaf.property⟩).obj
        (dualSheaf X.sheaf.obj X.ringCatSheaf.property E)).obj M ≅
      (Stacks.Algebraization.sheafHomFunctor X E).obj M :=
  TensorPresentations.tensorSheafSwap X.toRingedSpace
      (dualSheaf X.sheaf.obj X.ringCatSheaf.property E) M ≪≫
    Scheme.tensorDualIsoSheafHomOfRank E M r

end Stacks.SheafOfModules

end
