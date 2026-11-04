module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalChartIso

/-!
# Base change of the conormal source `Ker(ℰ → ℒ) ⊗ ℒ^{⊗ -1}` along an arbitrary morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `q : ℳ ⟶ ℒ` a map into an invertible
`𝒪_Y`-module.  The inverse image carries `Ker(q) ⊗ ℒ^{⊗ -1}` to `Ker(f^*q) ⊗ (f^*ℒ)^{⊗ -1}`
through the comparison `f^*Ker(q) ⟶ Ker(f^*q)` of kernels (a map for every `f`, the isomorphism
of `AlgebraicGeometry.Space.modulePullbackKernelTensorInverseIso` when `f` is flat), the
compatibility of `f^*` with tensor products (Stacks 03EL) and the transport of tensor powers.

For an invertible quotient `Q` of `ℰ` on `X` and `g : X' ⟶ X` this is the base-change map of the
source of the conormal isomorphism of Stacks 0B4I, and at a scheme point `x : T ⟶ X` its Zariski
reading is the map from the reading of `x^*(Ker(q) ⊗ ℒ^{⊗ -1})` to the source of Stacks 0B3V on
`T`, which is the reading isomorphism of `AlgebraicGeometry.Space.conormalSourceReadingIso` at
étale points.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackKernelTensorInverseHom`:
  `f^*(Ker(q) ⊗ ℒ^{⊗ -1}) ⟶ Ker(f^*q) ⊗ (f^*ℒ)^{⊗ -1}`.
* `AlgebraicGeometry.Space.sectionConormalSourceBaseChangeHom`: the base change of the source
  of the conormal isomorphism of Stacks 0B4I along `g : X' ⟶ X`.
* `AlgebraicGeometry.Space.conormalSourcePointReadingHom`: the source read at an arbitrary
  scheme point.

## Main results

* `AlgebraicGeometry.Space.modulePullbackKernelTensorInverseIso_hom`: for flat `f` the map is
  the isomorphism of `AlgebraicGeometry.Space.modulePullbackKernelTensorInverseIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor
attribute [instance] preservesZeroMorphisms_modulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section General

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The base change of `Ker(q) ⊗ ℒ^{⊗ -1}` along an arbitrary morphism**:
`f^*(Ker(q) ⊗ ℒ^{⊗ -1}) ≅ f^*Ker(q) ⊗ f^*(ℒ^{⊗ -1}) ⟶ Ker(f^*q) ⊗ (f^*ℒ)^{⊗ -1}`, the comparison
of kernels tensored with the transport of the tensor power. -/
def modulePullbackKernelTensorInverseHom {M L : Modules.{u, u} B S hS Y.1 Y.2} (q : M ⟶ L)
    [hL : IsInvertible (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L] :
    haveI := isInvertible_modulePullback_obj B S hS f L hL
    (modulePullback B S hS f).obj (kernel q ⊗ Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L (-1)) ⟶
      kernel ((modulePullback B S hS f).map q) ⊗ Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        ((modulePullback B S hS f).obj L) (-1) :=
  haveI := isInvertible_modulePullback_obj B S hS f L hL
  (modulePullbackTensorIso B S hS f _ _).hom ≫
    (kernelComparison q (modulePullback B S hS f) ⊗ₘ
      (modulePullbackTensorPowerIso f L (-1)).hom)

/-- For flat `f` the inverse image of a kernel is the kernel, through the comparison map. -/
theorem modulePullbackKernelIso_hom (hf : (smallEtaleRingedToposHom B S hS f).IsFlat)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (q : M ⟶ N) :
    (modulePullbackKernelIso f hf q).hom = kernelComparison q (modulePullback B S hS f) := by
  have : PreservesFiniteLimits (modulePullback B S hS f) :=
    ((exactFunctor_iff _).mp (exactFunctor_modulePullback_of_isFlat B S hS f hf)).1
  exact PreservesKernel.iso_hom _ _

/-- **For flat `f` the base change of `Ker(q) ⊗ ℒ^{⊗ -1}` is the isomorphism of
`AlgebraicGeometry.Space.modulePullbackKernelTensorInverseIso`.** -/
theorem modulePullbackKernelTensorInverseIso_hom
    (hf : (smallEtaleRingedToposHom B S hS f).IsFlat)
    {M L : Modules.{u, u} B S hS Y.1 Y.2} (q : M ⟶ L)
    [hL : IsInvertible (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L] :
    (modulePullbackKernelTensorInverseIso f hf q).hom = modulePullbackKernelTensorInverseHom f q :=
  have := isInvertible_modulePullback_obj B S hS f L hL
  have h₀ : (modulePullbackKernelTensorInverseIso f hf q).hom =
      (modulePullbackTensorIso B S hS f _ _).hom ≫
        ((modulePullbackKernelIso f hf q).hom ⊗ₘ (modulePullbackTensorPowerIso f L (-1)).hom) :=
    rfl
  h₀.trans (congrArg (fun k ↦ (modulePullbackTensorIso B S hS f _ _).hom ≫
    (k ⊗ₘ (modulePullbackTensorPowerIso f L (-1)).hom)) (modulePullbackKernelIso_hom f hf q))

/-- For flat `f` the base change of `Ker(q) ⊗ ℒ^{⊗ -1}` is an isomorphism. -/
theorem isIso_modulePullbackKernelTensorInverseHom
    (hf : (smallEtaleRingedToposHom B S hS f).IsFlat)
    {M L : Modules.{u, u} B S hS Y.1 Y.2} (q : M ⟶ L)
    [hL : IsInvertible (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L] :
    IsIso (modulePullbackKernelTensorInverseHom f q) := by
  rw [← modulePullbackKernelTensorInverseIso_hom f hf q]
  exact Iso.isIso_hom _

end General

section Section

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (Q : InvertibleQuotient X E)

/-- The kernel of `g^*q` is the kernel of the quotient map of the base change of `Q` along `g`
read along the identity of `g^*ℰ`. -/
def kernelBaseChangeIso {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) :
    kernel ((modulePullback B S hS g).map Q.q) ≅ kernel (Q.baseChange g (Iso.refl _)).q :=
  kernelIsoOfEq (Category.id_comp _).symm

/-- **The base change of the source of the conormal isomorphism of Stacks 0B4I** along
`g : X' ⟶ X`: `g^*(Ker(q) ⊗ ℒ^{⊗ -1}) ⟶ Ker(g^*q) ⊗ (g^*ℒ)^{⊗ -1}`, for the base change
`g^*q : g^*ℰ ⟶ g^*ℒ` of the invertible quotient. -/
def sectionConormalSourceBaseChangeHom {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) :
    (modulePullback B S hS g).obj (sectionConormalSource X E Q) ⟶
      sectionConormalSource X' ((modulePullback B S hS g).obj E) (Q.baseChange g (Iso.refl _)) :=
  haveI hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      Q.L :=
    Q.invertible.toAlgebraicGeometry
  haveI := isInvertible_modulePullback_obj B S hS g Q.L hQ
  modulePullbackKernelTensorInverseHom g Q.q ≫
    (tensorIso (C := Modules.{u, u} B S hS X'.1 X'.2) (kernelBaseChangeIso X E Q g)
      (Iso.refl _)).hom

/-- At a scheme point `x : T ⟶ X` the kernel comparison along `x` is the one of
`AlgebraicGeometry.Space.kernelPointBaseChangeIso`. -/
theorem kernelBaseChangeIso_pointHom (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    kernelBaseChangeIso X E Q (pointHom x) = kernelPointBaseChangeIso X E Q T x :=
  rfl

/-- **The source of the conormal isomorphism of Stacks 0B4I read at an arbitrary scheme point
`x : T ⟶ X`**: the Zariski reading of the base change along `x`, followed by the reading
`R_T(Ker(x^*q) ⊗ (x^*ℒ)^{⊗ -1}) ≅ Ker(q_x) ⊗ ℒ_x^{⊗ -1}`. -/
def conormalSourcePointReadingHom (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    haveI := (zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X E hE T x)
      (Q.baseChange (pointHom x) (Iso.refl _))).invertible
    (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
      (sectionConormalSource X E Q)) ⟶
    (kernel (zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X E hE T x)
        (Q.baseChange (pointHom x) (Iso.refl _))).q ⊗
      Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj T).presheaf
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
        (zariskiReadingInvertibleQuotient (isQuasicoherentOnSite_pointPullback X E hE T x)
          (Q.baseChange (pointHom x) (Iso.refl _))).L (-1) :
        ((BigFppfOver.toScheme B S hS).obj T).Modules) :=
  haveI hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      Q.L :=
    Q.invertible.toAlgebraicGeometry
  haveI : IsInvertible (structureCommRings B S hS (yonedaSpace B S hS T))
      (structureRingSheaf B S hS (yonedaSpace B S hS T)).property
      (Q.baseChange (pointHom x) (Iso.refl _)).L :=
    isInvertible_modulePullback_obj B S hS (pointHom x) Q.L hQ
  (zariskiReadingFunctor T).map (modulePullbackKernelTensorInverseHom (pointHom x) Q.q ≫
      (tensorIso (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
        (kernelPointBaseChangeIso X E Q T x) (Iso.refl _)).hom) ≫
    (zariskiReadingKernelTensorInverseIso T (Q.baseChange (pointHom x) (Iso.refl _)).q
      (isQuasicoherentOnSite_pointPullback X E hE T x)).hom

end Section

end AlgebraicGeometry.Space

end
