module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalSchemeBaseChange

/-!
# Base change of the kernel factor of the conormal source read at an étale scheme point

Let `q : ℰ ⟶ ℒ` be an invertible quotient of a quasi-coherent module on an algebraic space `X`,
let `x : T ⟶ X` be an étale scheme point, `h : T' ⟶ T` a morphism of test objects with `x ∘ h`
étale, `τ` the morphism of schemes underlying `h` and `φ` the morphism of represented algebraic
spaces.  The conormal source `Ker(q) ⊗ ℒ^{⊗ -1}` read at `x`
(`AlgebraicGeometry.Space.conormalSourceReadingIso`) has the kernel factor
`(x^* Ker q)_Zar ≅ Ker(q_x)`.  This file proves that the kernel factors at `x` and at `x ∘ h` are
intertwined by the base change of the Zariski reading together with the composition comparison
`φ^*x^* ≅ (x ∘ h)^*` of Stacks 03LU, and by the kernel base-change comparison
`Stacks.Divisors.quotientKernelBaseChange` of Stacks 0B3V.  The check is made after composing
with the kernel inclusion, where it is the naturality of the two comparisons at `Ker q ⟶ ℰ`.

## Main definitions

* `AlgebraicGeometry.Space.kernelPointReadingIso`: `(x^* Ker q)_Zar ≅ Ker(q_x)`.

## Main results

* `AlgebraicGeometry.Space.kernelPointReadingIso_hom_comp_ι`: compatibility with the kernel
  inclusions.
* `AlgebraicGeometry.Space.map_kernel_ι_comp_pointZariskiModuleBaseChangeIso_hom`: the
  identifications `((x ∘ h)^*ℳ)_Zar ≅ τ^*(x^*ℳ)_Zar` at `ℰ` and at `Ker q` are compatible with the
  kernel inclusion.
* `AlgebraicGeometry.Space.kernelPointReadingIso_baseChange`: the base change of the kernel
  factor.

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

/-- The comparison of kernels of a kernel-preserving functor, followed by the kernel inclusion,
with every instance argument read off from the term. -/
theorem preservesKernel_iso_hom_comp_ι {C D : Type*} [Category C] [Category D]
    {_ : HasZeroMorphisms C} {_ : HasZeroMorphisms D} (G : C ⥤ D) {_ : G.PreservesZeroMorphisms}
    {X Y : C} (f : X ⟶ Y) {_ : HasKernel f} {_ : HasKernel (G.map f)}
    {_ : PreservesLimit (parallelPair f 0) G} :
    (PreservesKernel.iso G f).hom ≫ kernel.ι (G.map f) = G.map (kernel.ι f) := by
  simp

section Kernel

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (Q : InvertibleQuotient X E)

include hE in
/-- The kernel of the quotient map of an invertible quotient of a quasi-coherent module is
quasi-coherent. -/
theorem isQuasicoherentOnSite_kernel_q : (kernel Q.q).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_kernel_of_isQuasicoherentOnSite X Q.q hE
    (isQuasicoherentOnSite_of_isInvertibleModule X Q.L Q.invertible)

/-- **The kernel factor of the conormal source read at an étale scheme point**:
`(x^* Ker q)_Zar ≅ Ker(q_x)`, the exactness of `x^*` followed by that of the Zariski reading. -/
def kernelPointReadingIso (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
    (hx : IsEtale B S hS x) :
    ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)) :
        ((BigFppfOver.toScheme B S hS).obj T).Modules) ≅
      kernel (sectionPointQuotient X E hE Q T x).q :=
  (zariskiReadingFunctor T).mapIso
      (modulePullbackKernelIso (pointHom x)
          (isFlat_smallEtaleRingedToposHom_of_isEtale B S hS (pointHom x) hx) Q.q ≪≫
        kernelPointBaseChangeIso X E Q T x) ≪≫
    zariskiReadingKernelIso T (Q.baseChange (pointHom x) (Iso.refl _)).q

/-- The kernel factor is compatible with the kernel inclusions. -/
theorem kernelPointReadingIso_hom_comp_ι (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
    (hx : IsEtale B S hS x) :
    (kernelPointReadingIso X E hE Q T x hx).hom ≫ kernel.ι (sectionPointQuotient X E hE Q T x).q =
      (zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom x)).map (kernel.ι Q.q)) := by
  have e1 : (zariskiReadingKernelIso T (Q.baseChange (pointHom x) (Iso.refl _)).q).hom ≫
      kernel.ι ((zariskiReadingFunctor T).map (Q.baseChange (pointHom x) (Iso.refl _)).q) =
      (zariskiReadingFunctor T).map (kernel.ι (Q.baseChange (pointHom x) (Iso.refl _)).q) :=
    preservesKernel_iso_hom_comp_ι _ _
  have e2 : (modulePullbackKernelIso (pointHom x)
        (isFlat_smallEtaleRingedToposHom_of_isEtale B S hS (pointHom x) hx) Q.q).hom ≫
      kernel.ι ((modulePullback B S hS (pointHom x)).map Q.q) =
      (modulePullback B S hS (pointHom x)).map (kernel.ι Q.q) :=
    preservesKernel_iso_hom_comp_ι _ _
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

/-- The identification `(x'^*ℳ)_Zar ≅ τ^*(x^*ℳ)_Zar`, spelled out: the reading of the inverse
composition comparison followed by the inverse of the base change of the Zariski reading. -/
theorem pointZariskiModuleBaseChangeIso_hom_eq
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T)
    (hI : IsIso ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj M))) :
    (pointZariskiModuleBaseChangeIso X M hM x h).hom =
      (zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS
        (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
        (pointHom x)).inv.app M) ≫
        @inv _ _ _ _
          ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj M)) hI :=
  rfl

/-- The base change of the Zariski reading and the composition comparison of Stacks 03LU, inverted
at `ℰ` and at `Ker q`, intertwine the Zariski readings of the pullbacks of the kernel
inclusion. -/
theorem map_kernel_ι_comp_inv_eq {T T' : BigFppfOver B S hS}
    (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    (zariskiReadingFunctor T').map
        ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).map (kernel.ι Q.q)) ≫
        (zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
          (pointHom x)).inv.app E) ≫
        @inv _ _ _ _ ((zariskiReadingPullbackHom h).app
            ((modulePullback B S hS (pointHom x)).obj E))
          (isIso_zariskiReadingPullbackHom_app h _
            (isQuasicoherentOnSite_pointPullback X E hE T x)) =
      ((zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
          (pointHom x)).inv.app (kernel Q.q)) ≫
        @inv _ _ _ _ ((zariskiReadingPullbackHom h).app
            ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)))
          (isIso_zariskiReadingPullbackHom_app h _ (isQuasicoherentOnSite_pointPullback X
            (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q) T x))) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          ((zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom x)).map
            (kernel.ι Q.q))) := by
  have k := map_comp_map_inv_app_comp_inv_eq (modulePullback B S hS (pointHom x)) rfl
    (modulePullback B S hS (pointHom (yoneda.map h ≫ x))) rfl
    (modulePullbackCompIso B S hS
      (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T) (pointHom x))
    (zariskiReadingPullbackHom h) (kernel.ι Q.q)
    (isIso_zariskiReadingPullbackHom_app h _ (isQuasicoherentOnSite_pointPullback X
      (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q) T x))
    (isIso_zariskiReadingPullbackHom_app h _ (isQuasicoherentOnSite_pointPullback X E hE T x))
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at k
  exact k

/-- `map_kernel_ι_comp_inv_eq` with the identification `(x'^*ℰ)_Zar ≅ τ^*(x^*ℰ)_Zar` named. -/
theorem map_kernel_ι_comp_pointZariskiModuleBaseChangeIso_hom {T T' : BigFppfOver B S hS}
    (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    (zariskiReadingFunctor T').map
        ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).map (kernel.ι Q.q)) ≫
        (pointZariskiModuleBaseChangeIso X E hE x h).hom =
      ((zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
          (pointHom x)).inv.app (kernel Q.q)) ≫
        @inv _ _ _ _ ((zariskiReadingPullbackHom h).app
            ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)))
          (isIso_zariskiReadingPullbackHom_app h _ (isQuasicoherentOnSite_pointPullback X
            (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q) T x))) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          ((zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom x)).map
            (kernel.ι Q.q))) :=
  map_kernel_ι_comp_inv_eq X E hE Q x h

/-- **The kernel factors at `x` and at `x ∘ h` are intertwined** by the base change of the
Zariski reading together with the composition comparison of Stacks 03LU at `Ker q`, and the
kernel base-change comparison `Stacks.Divisors.quotientKernelBaseChange` of Stacks 0B3V. -/
theorem kernelPointReadingIso_baseChange {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) (hx : IsEtale B S hS x) (hx' : IsEtale B S hS (yoneda.map h ≫ x)) :
    ((zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
          (pointHom x)).inv.app (kernel Q.q)) ≫
        @inv _ _ _ _ ((zariskiReadingPullbackHom h).app
            ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)))
          (isIso_zariskiReadingPullbackHom_app h _ (isQuasicoherentOnSite_pointPullback X
            (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q) T x))) ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        (kernelPointReadingIso X E hE Q T x hx).hom ≫
      (Stacks.Divisors.quotientKernelBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)
        (sectionPointQuotient_baseChange_q X E hE Q x h)).1.hom =
      (kernelPointReadingIso X E hE Q T' (yoneda.map h ≫ x) hx').hom := by
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
        (kernelPointReadingIso_hom_comp_ι X E hE Q T x hx)))))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (pointZariskiModuleBaseChangeIso X E hE x h).inv)
    (map_kernel_ι_comp_pointZariskiModuleBaseChangeIso_hom X E hE Q x h).symm).trans ?_
  refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (pointZariskiModuleBaseChangeIso X E hE x h).hom_inv_id).trans (Category.comp_id _))).trans ?_
  exact (kernelPointReadingIso_hom_comp_ι X E hE Q T' (yoneda.map h ≫ x) hx').symm

end Kernel

end AlgebraicGeometry.Space

end
