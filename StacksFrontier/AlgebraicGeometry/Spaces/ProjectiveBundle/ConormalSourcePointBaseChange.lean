module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceInverseEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceReadingBaseChange

/-!
# Base change of the conormal source read at arbitrary scheme points

Let `q : ℰ ⟶ ℒ` be an invertible quotient of a quasi-coherent module on an algebraic space `X`,
let `x : T ⟶ X` be a scheme point and `h : T' ⟶ T` a morphism of test objects, neither assumed
étale.  The kernel factor of the conormal source read at `x` is the map
`k_x : (x^* Ker q)_Zar ⟶ Ker(q_x)`, the Zariski reading of the comparison of kernels followed by
the exactness of the Zariski reading.  This file proves that the kernel factors at `x` and at
`x ∘ h` are intertwined by the base change of the Zariski reading together with the composition
comparison of Stacks 03LU, and by the kernel base-change comparison
`Stacks.Divisors.quotientKernelBaseChange` of Stacks 0B3V.

## Main definitions

* `AlgebraicGeometry.Space.kernelPointReadingHom`: `k_x : (x^* Ker q)_Zar ⟶ Ker(q_x)`.

## Main results

* `AlgebraicGeometry.Space.kernelPointReadingHom_comp_ι`: compatibility with the kernel
  inclusions.
* `AlgebraicGeometry.Space.kernelPointReadingHom_baseChange`: the base change of the kernel
  factor along an arbitrary `h`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u


namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Kernel

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (Q : InvertibleQuotient X E)

/-- **The kernel factor of the conormal source read at an arbitrary scheme point**:
`(x^* Ker q)_Zar ⟶ Ker(q_x)`, the Zariski reading of the comparison of kernels followed by the
exactness of the Zariski reading. -/
def kernelPointReadingHom (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)) :
        ((BigFppfOver.toScheme B S hS).obj T).Modules) ⟶
      kernel (sectionPointQuotient X E hE Q T x).q :=
  haveI := preservesZeroMorphisms_modulePullback B S hS (pointHom x)
  (zariskiReadingFunctor T).map (kernelComparison Q.q (modulePullback B S hS (pointHom x)) ≫
      (kernelPointBaseChangeIso X E Q T x).hom) ≫
    (zariskiReadingKernelIso T (Q.baseChange (pointHom x) (Iso.refl _)).q).hom

/-- The kernel factor is compatible with the kernel inclusions. -/
theorem kernelPointReadingHom_comp_ι (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    kernelPointReadingHom X E hE Q T x ≫ kernel.ι (sectionPointQuotient X E hE Q T x).q =
      (zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom x)).map (kernel.ι Q.q)) := by
  have := preservesZeroMorphisms_modulePullback B S hS (pointHom x)
  have e1 : (zariskiReadingKernelIso T (Q.baseChange (pointHom x) (Iso.refl _)).q).hom ≫
      kernel.ι ((zariskiReadingFunctor T).map (Q.baseChange (pointHom x) (Iso.refl _)).q) =
      (zariskiReadingFunctor T).map (kernel.ι (Q.baseChange (pointHom x) (Iso.refl _)).q) :=
    preservesKernel_iso_hom_comp_ι _ _
  have e2 : kernelComparison Q.q (modulePullback B S hS (pointHom x)) ≫
      kernel.ι ((modulePullback B S hS (pointHom x)).map Q.q) =
      (modulePullback B S hS (pointHom x)).map (kernel.ι Q.q) :=
    kernelComparison_comp_ι _ _
  have e3 : (kernelPointBaseChangeIso X E Q T x).hom ≫
      kernel.ι (Q.baseChange (pointHom x) (Iso.refl _)).q =
      kernel.ι ((modulePullback B S hS (pointHom x)).map Q.q) :=
    kernelIsoOfEq_hom_comp_ι _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) e1).trans ?_
  refine ((zariskiReadingFunctor T).map_comp _ _).symm.trans ?_
  refine congrArg (zariskiReadingFunctor T).map ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (_ ≫ ·) e3).trans e2

/-- **The kernel factors at `x` and at `x ∘ h` are intertwined**, for arbitrary `x` and `h`, by
the base change of the Zariski reading together with the composition comparison of Stacks 03LU
at `Ker q`, and the kernel base-change comparison `Stacks.Divisors.quotientKernelBaseChange` of
Stacks 0B3V. -/
theorem kernelPointReadingHom_baseChange {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) :
    ((zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
          (pointHom x)).inv.app (kernel Q.q)) ≫
        @inv _ _ _ _ ((zariskiReadingPullbackHom h).app
            ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)))
          (isIso_zariskiReadingPullbackHom_app h _ (isQuasicoherentOnSite_pointPullback X
            (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q) T x))) ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        (kernelPointReadingHom X E hE Q T x) ≫
      (Stacks.Divisors.quotientKernelBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)
        (sectionPointQuotient_baseChange_q X E hE Q x h)).1.hom =
      kernelPointReadingHom X E hE Q T' (yoneda.map h ≫ x) := by
  refine (cancel_mono (kernel.ι (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x)).q)).mp ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (Stacks.Divisors.quotientKernelBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)
        (sectionPointQuotient_baseChange_q X E hE Q x h)).2))).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        (kernelPointReadingHom_comp_ι X E hE Q T x)))))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (pointZariskiModuleBaseChangeIso X E hE x h).inv)
    (map_kernel_ι_comp_pointZariskiModuleBaseChangeIso_hom X E hE Q x h).symm).trans ?_
  refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (pointZariskiModuleBaseChangeIso X E hE x h).hom_inv_id).trans (Category.comp_id _))).trans ?_
  exact (kernelPointReadingHom_comp_ι X E hE Q T' (yoneda.map h ≫ x)).symm

end Kernel

end AlgebraicGeometry.Space

end
