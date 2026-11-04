/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotSeparatedFinitePresentationReduction

/-!
# `Hilb^{P, L}_{X/B} = Quot^{P, L}_{𝒪_X/X/B}`, over the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite presentation over a scheme `S` of a
big fppf site, `L` an invertible `𝒪_X`-module and `P : ℤ → ℤ`. The subfunctor
`Hilb^{P, L}_{X/Y}` of the Hilbert presheaf (Stacks 0CZY) of the families `Z ⊆ X_T` having
Hilbert polynomial `P` with respect to `L`, that is `χ(X_t, 𝒪_{Z_t} ⊗ L_t^{⊗ n}) = P(n)` for every
point `t ∈ T` and every `n ∈ ℤ` (Stacks 0DNF, 0DPG), is the preimage of
`Quot^{P, L}_{𝒪_X/X/Y}` under the identification `Hilb_{X/Y} = Quot_{𝒪_X/X/Y}` of Stacks 0D00.
This file records the induced isomorphism `Hilb^{P, L}_{X/Y} ≅ Quot^{P, L}_{𝒪_X/X/Y}` over `Y`,
and transports along it the statement that `Quot^{P, L}_{𝒪_X/X/Y}` is an algebraic space
separated and of finite presentation over `Y`.

This is the proof of Stacks 0DPI from Stacks 0DPD: "Recall that `Hilb_{X/B} = Quot_{𝒪_X/X/B}`,
see Quot, Lemma 0D00. Thus this lemma is an immediate consequence of Lemma 0DPD."

## Main definitions

* `AlgebraicGeometry.Space.hilbertPolynomialHilbert`: `Hilb^{P, L}_{X/Y}`.
* `AlgebraicGeometry.Space.subfunctorPreimageIsoOfIso`: the preimage of a subfunctor along an
  isomorphism is isomorphic to it; applied to Stacks 0D00 it is
  `Hilb^{P, L}_{X/Y} ≅ Quot^{P, L}_{𝒪_X/X/Y}`.

## Main results

* `AlgebraicGeometry.Space.exists_hilbertPolynomialHilbert_model_of_quot`: a model of
  `Quot^{P, L}_{𝒪_X/X/Y}` which is an algebraic space separated and of finite presentation over
  `Y` gives one of `Hilb^{P, L}_{X/Y}`.

## References

* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0DPI](https://stacks.math.columbia.edu/tag/0DPI)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Preimage

variable {C : Type*} [Category* C] {F G : Cᵒᵖ ⥤ Type (u + 1)} (e : F ≅ G) (Q : Subfunctor G)

/-- The inverse of `Q.fromPreimage e.hom` for an isomorphism `e : F ≅ G`. -/
def subfunctorPreimageIsoOfIsoInv : Q.toFunctor ⟶ (Q.preimage e.hom).toFunctor :=
  Subfunctor.lift (Q.ι ≫ e.inv) (by
    rintro T _ ⟨x, rfl⟩
    change e.hom.app T (e.inv.app T x.1) ∈ Q.obj T
    rw [Iso.inv_hom_id_app_apply]
    exact x.2)

/-- **The preimage of a subfunctor along an isomorphism is isomorphic to it.** -/
def subfunctorPreimageIsoOfIso : (Q.preimage e.hom).toFunctor ≅ Q.toFunctor where
  hom := Q.fromPreimage e.hom
  inv := subfunctorPreimageIsoOfIsoInv e Q
  hom_inv_id := by
    refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_)
    exact Iso.hom_inv_id_app_apply e T x.1
  inv_hom_id := by
    refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_)
    exact Iso.inv_hom_id_app_apply e T x.1

/-- The isomorphism `subfunctorPreimageIsoOfIso e Q` followed by the inclusion `Q.ι` is the
inclusion of `Q.preimage e.hom` followed by `e.hom`. -/
@[reassoc]
theorem subfunctorPreimageIsoOfIso_hom_comp_ι :
    (subfunctorPreimageIsoOfIso e Q).hom ≫ Q.ι = (Q.preimage e.hom).ι ≫ e.hom :=
  rfl

end Preimage

section HilbertPolynomial

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  (L : Modules.{u, u} B S hS X.1 X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L]
  (P : ℤ → ℤ)

/-- **`Hilb^{P, L}_{X/Y}`** (Stacks 0DPG with the numerical invariants of Stacks 0DNF at
`E_n = L^{⊗ n}`): for a morphism `f : X ⟶ Y` of finite presentation, an invertible `𝒪_X`-module
`L` and `P : ℤ → ℤ`, the subfunctor of the Hilbert presheaf of the families `Z ⊆ X_T` (closed
subspaces flat, of finite presentation and proper over the test scheme `T`) having Hilbert
polynomial `P` with respect to `L`, that is `χ(X_t, 𝒪_{Z_t} ⊗ L_t^{⊗ n}) = P(n)` for every point
`t ∈ T` and every `n ∈ ℤ`. As in the source, it is the preimage of `Quot^{P, L}_{𝒪_X/X/Y}`
under the identification `Hilb_{X/Y} = Quot_{𝒪_X/X/Y}` of Stacks 0D00, which sends a family
`Z ⊆ X_T` to the quotient `𝒪_{X_T} ⟶ 𝒪_Z`. -/
def hilbertPolynomialHilbert : Subfunctor (hilbertPresheaf f) :=
  ((structureSheafQuotSituation f hf).hilbertPolynomialQuot L (hL := hL) P).preimage
    (hilbertPresheafIsoQuotSitePresheaf f hf).hom

/-- Membership in `Hilb^{P, L}_{X/Y}`, unfolded: the quotient `𝒪_{X_T} ⟶ 𝒪_Z` of a family
`Z ⊆ X_T` has twisted Euler characteristics `χ(X_t, 𝒪_{Z_t} ⊗ L_t^{⊗ n}) = P(n)`. -/
theorem mem_hilbertPolynomialHilbert_iff {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : (hilbertPresheaf f).obj T) :
    x ∈ (hilbertPolynomialHilbert f hf L P).obj T ↔
      (hilbertPresheafIsoQuotSitePresheaf f hf).hom.app T x ∈
        ((structureSheafQuotSituation f hf).hilbertPolynomialQuot L (hL := hL) P).obj T :=
  Iff.rfl

/-- **Stacks 0DPI from Stacks 0DPD.** A model of `Quot^{P, L}_{𝒪_X/X/Y}` which is an algebraic
space separated and of finite presentation over `Y` is a model of `Hilb^{P, L}_{X/Y}` over `Y`,
through `Hilb^{P, L}_{X/Y} ≅ Quot^{P, L}_{𝒪_X/X/Y}` (Stacks 0D00). -/
theorem exists_hilbertPolynomialHilbert_model_of_quot
    (h : (structureSheafQuotSituation f hf).IsSeparatedFinitePresentationAlgebraicSpaceOver
      ((structureSheafQuotSituation f hf).hilbertPolynomialQuot L (hL := hL) P)) :
    ∃ (M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (e : M ⋙ uliftFunctor.{u + 1, u} ≅ (hilbertPolynomialHilbert f hf L P).toFunctor)
      (p : M ⟶ Y.obj),
      Functor.whiskerRight p uliftFunctor.{u + 1, u} =
          e.hom ≫ (hilbertPolynomialHilbert f hf L P).ι ≫ hilbertPresheafToBase f ∧
        IsAlgebraicSpace B S hS M ∧ IsSeparated B S hS p ∧ IsFinitePresentation B S hS p := by
  obtain ⟨N, halg, hsep, hfp⟩ := h
  let i := subfunctorPreimageIsoOfIso (hilbertPresheafIsoQuotSitePresheaf f hf)
    ((structureSheafQuotSituation f hf).hilbertPolynomialQuot L (hL := hL) P)
  have h1 : (hilbertPolynomialHilbert f hf L P).ι ≫ hilbertPresheafToBase f =
      i.hom ≫ ((structureSheafQuotSituation f hf).hilbertPolynomialQuot L (hL := hL) P).ι ≫
        (structureSheafQuotSituation f hf).quotSitePresheafToBase := by
    rw [subfunctorPreimageIsoOfIso_hom_comp_ι_assoc,
      hilbertPresheafIsoQuotSitePresheaf_hom_comp_quotSitePresheafToBase]
    rfl
  refine ⟨N.presheaf, N.iso ≪≫ i.symm, N.toBase, ?_, halg, hsep, hfp⟩
  refine (N.whiskerRight_toBase).trans ?_
  rw [h1]
  exact (congrArg (N.iso.hom ≫ ·) (i.inv_hom_id_assoc _).symm).trans (Category.assoc _ _ _).symm

end HilbertPolynomial

end AlgebraicGeometry.Space

end
