module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsFinitePresentation
public import StacksFrontier.Deformation.Artin.Approximation

/-!
# Limit preservation on objects for the category fibred in sets attached to a presheaf

Let `S` be a scheme in a big fppf site `B` and let `F` be a set-valued presheaf on the big
fppf category over `S`. This file reduces limit preservation on objects, **Stacks 06CU**, for
the structure morphism of the category `𝒮_F` fibred in sets attached to `F`
(`AlgebraicGeometry.Stack.fibredCategory`, **Stacks 0458**) to a condition on `F` alone:
every section of `F` over an inverse limit of affine objects of the site is the restriction of
a section at some stage, and the stage may be taken below any prescribed index.

## Main definitions

* `AlgebraicGeometry.Stack.DescendsOnAffineLimits`: the condition on `F`.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_fibredCategory`: a presheaf satisfying
  that condition has limit preserving on objects structure morphism.

## References

* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

/-- Transporting a factorization `f' ≫ g = f` along equalities of its three objects. -/
private theorem eqToHom_paste {C : Type*} [Category C] {A P Q Q' R Y : C}
    (hA : A = P) (hQ : Q = Q') (hY : Y = R)
    (f' : P ⟶ Q') (g : Q' ⟶ R) (f : P ⟶ R) (hfg : f' ≫ g = f) :
    eqToHom hA ≫ f' ≫ eqToHom hQ.symm ≫ eqToHom hQ ≫ g ≫ eqToHom hY.symm =
      𝟙 A ≫ eqToHom hA ≫ f ≫ eqToHom hY.symm := by
  subst hA hQ hY
  simp [← hfg]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent of a presheaf along inverse limits of affine objects.** For every cofiltered
inverse system of affine objects of the big fppf site over `S` whose image in schemes has the
cone as its limit, every section of `F` over the cone point is the restriction of a section at
some stage, and the stage may be taken below any prescribed index. -/
public def DescendsOnAffineLimits (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
    ∀ (i : I) (t : F.obj (op ((BigAffineFppf.inclusion B S hS).obj c.pt))),
      ∃ (i' : I) (_j : i' ⟶ i)
        (s : F.obj (op ((BigAffineFppf.inclusion B S hS).obj (D.obj i')))),
        F.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i')).op s = t

/-- If every section of `F` over an inverse limit of affine objects of the site descends to a
stage below a prescribed index, then the structure morphism of the category `𝒮_F` fibred in sets
attached to `F` is limit preserving on objects. -/
@[stacks 06CU "the criterion for the category fibred in sets attached to a set-valued \
presheaf: limit preservation on objects of its structure morphism follows from descent of the \
presheaf's sections along inverse limits of affine objects"]
public theorem isLimitPreservingOnObjects_fibredCategory (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : DescendsOnAffineLimits.{u, v, w} B S hS F) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, v, w} B S hS
      (fibredCategory B S hS F)
      (Deformation.Artin.Approximation.baseFiberedCategory B S hS)
      (Deformation.Artin.Approximation.structureMorphism B S hS
        (fibredCategory B S hS F)) := by
  intro I _ _ D c hc i y x γ hγ
  obtain ⟨i', j, s, hs⟩ := hF I D c hc i (presheafFiberElement B S hS F x)
  have hxbase : (fibredCategory B S hS F).based.p.obj
      (⟨(BigAffineFppf.inclusion B S hS).obj (D.obj i'), Discrete.mk s⟩ :
        (fibredCategory B S hS F).based.obj) =
      (BigAffineFppf.inclusion B S hS).obj (D.obj i') := rfl
  have hfg : (BigAffineFppf.inclusion B S hS).map (c.π.app i') ≫
      (BigAffineFppf.inclusion B S hS).map (D.map j) =
      (BigAffineFppf.inclusion B S hS).map (c.π.app i) := by
    rw [← CategoryTheory.Functor.map_comp, c.w j]
  obtain ⟨δ, hδ⟩ := presheafFiberHom B S hS F
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i')) x
    ⟨⟨(BigAffineFppf.inclusion B S hS).obj (D.obj i'), Discrete.mk s⟩, hxbase⟩ hs
  refine ⟨i', j, ⟨⟨(BigAffineFppf.inclusion B S hS).obj (D.obj i'), Discrete.mk s⟩, hxbase⟩,
    x, δ, 𝟙 x.1,
    eqToHom hxbase ≫ (BigAffineFppf.inclusion B S hS).map (D.map j) ≫ eqToHom y.2.symm,
    (fibredCategory B S hS F).isFiberedInGroupoids.isStronglyCartesian_homLift _ δ,
    IsHomLift.of_fac _ _ _ x.2 x.2 (by simp), inferInstance, ?_, ?_⟩
  · have hlift :
        (Deformation.Artin.Approximation.baseFiberedCategory B S hS).based.p.IsHomLift
        ((BigAffineFppf.inclusion B S hS).map (D.map j))
        (eqToHom hxbase ≫ (BigAffineFppf.inclusion B S hS).map (D.map j) ≫
          eqToHom y.2.symm) := by
      refine IsHomLift.of_fac _ _ _ hxbase y.2 ?_
      show (BigAffineFppf.inclusion B S hS).map (D.map j) =
        (eqToIso hxbase).inv ≫ ((eqToIso hxbase).hom ≫
          (BigAffineFppf.inclusion B S hS).map (D.map j) ≫ (eqToIso y.2).inv) ≫
          (eqToIso y.2).hom
      simp
    exact Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift
      (Deformation.Artin.Approximation.baseFiberedCategory B S hS).isFiberedInGroupoids
      ((BigAffineFppf.inclusion B S hS).map (D.map j))
      (eqToHom hxbase ≫ (BigAffineFppf.inclusion B S hS).map (D.map j) ≫
        eqToHom y.2.symm)
  · have hδfac : (fibredCategory B S hS F).based.p.map δ =
        eqToHom x.2 ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i') ≫
          eqToHom hxbase.symm :=
      IsHomLift.fac' (fibredCategory B S hS F).based.p
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i')) δ
    have hγfac : γ = eqToHom x.2 ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i) ≫
        eqToHom y.2.symm :=
      IsHomLift.fac' (Deformation.Artin.Approximation.baseFiberedCategory B S hS).based.p
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) γ
    show (fibredCategory B S hS F).based.p.map δ ≫
        eqToHom hxbase ≫ (BigAffineFppf.inclusion B S hS).map (D.map j) ≫
          eqToHom y.2.symm =
      (fibredCategory B S hS F).based.p.map (𝟙 x.1) ≫ γ
    rw [hδfac, hγfac, CategoryTheory.Functor.map_id]
    simp only [Category.assoc]
    exact eqToHom_paste x.2 hxbase y.2
      ((BigAffineFppf.inclusion B S hS).map (c.π.app i'))
      ((BigAffineFppf.inclusion B S hS).map (D.map j))
      ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) hfg

end AlgebraicGeometry.Stack

end
