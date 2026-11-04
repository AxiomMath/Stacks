module

public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Homology.PseudoCoherent.HomFlat
import StacksFrontier.RingTheory.Different.PairingBaseChange

/-!
# Flat base change for the infinitesimal automorphisms of an object

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `A → C`
be a flat homomorphism of `S`-algebras whose spectra lie in the site, let `x` be an object of
`𝒳` over `Spec A` and let `y = x|_{Spec C}`. For an `A`-module `M` the infinitesimal
automorphisms `Inf_x(M)` of the trivial deformation of `x` to `Spec A[M]` form an `A`-linear
functor of `M` (Stacks 07Y9, `Deformation.Artin.InfinitesimalAutomorphismFunctorData`), and
likewise for `y` over `C`. This file proves that `Inf` commutes with the flat base change:
`Inf_x(M) ⊗_A C = Inf_y(C ⊗_A M)`.

The source's argument runs through the automorphism group algebraic space `G → Spec A` of `x`
and its sheaf of differentials: writing `Q = e^*Ω_{G/A}` for the pullback along the neutral
section, the discussion of Stacks 0617 identifies `Inf_x(M) = Hom_A(Q, M)` naturally in `M`,
the hypothesis that the inertia `ℐ_𝒳 → 𝒳` is locally of finite presentation makes `Q` a
finitely presented `A`-module (Stacks 05ZF), and `Ω_{G_C/C}` is the pullback of `Ω_{G/A}`
(Stacks 05ZC), so that `Inf_y(N) = Hom_C(C ⊗_A Q, N)`. Those three inputs are carried here as
the explicit hypotheses collected in `Deformation.Artin.InfHomRepresentation`; the base-change
statement itself is then the flat-base-change bijectivity of the `Hom` comparison, which *is*
available as Stacks 087Q/087R in `StacksFrontier.Homology.PseudoCoherent.HomFlat`. Stacks 05ZF
itself *is* available in this development, in the namespace `AlgebraicGeometry`, as
`Space.isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation`;
what is missing is the passage from it to finite presentation of the `A`-module `e^*Ω_{G/A}`,
which needs Stacks 0617 and 05ZC as well.

## Main definitions

* `Deformation.Artin.algebraOverMap` — the morphism `Spec C ⟶ Spec A` of the big fppf site
  over `S` attached to an `S`-algebra homomorphism `A → C`.
* `Deformation.Artin.InfHomRepresentation` — the input carried rather than proved: that `y` is
  the restriction of `x` along `A → C`, a finitely presented `A`-module `Q` with its base
  change to `C`, and the identifications of `Inf_x` and `Inf_y` with `Hom_A(Q, -)` and
  `Hom_C(C ⊗_A Q, -)`.

## Main results

* `StacksDraft.PseudoCoherence.homBaseChangeComparison_bijective` — the `Hom` base-change
  comparison `Hom_A(Q, M) ⊗_A C → Hom_C(C ⊗_A Q, C ⊗_A M)` is bijective for a finitely
  presented source and a flat algebra. This is the `Hom`-level content of Stacks 087Q/087R in
  the shape used below, restated from
  `Stacks.Discriminant.rTensorHomToHomRTensor_bijective_of_finitePresentation`, whose statement
  is the `Hom` part of `StacksDraft.PseudoCoherence.canonicalExtTensorComparison_bijective`.
* `Deformation.Artin.existsUnique_infFlatBaseChange` — **Stacks 0DNR**: there is a unique
  `C`-linear isomorphism `Inf_x(M) ⊗_A C ≅ Inf_y(N)`, where `N` is a site module identified
  with `C ⊗_A M`, carrying `c ⊗ θ` to the base change of `θ` scaled by `c`.

## Implementation notes

`Inf_x(M)` is a *chosen* object: `Deformation.Artin.infinitesimalAutomorphismFunctor` selects
a member of `Deformation.Artin.InfinitesimalAutomorphismFunctorData`, and the only handle on
its values is the family of bijections with the infinitesimal automorphisms of the trivial
deformations. So the two functors enter as arbitrary members of that structure, exactly as in
Stacks 07YA, and nothing here chooses data from an existence statement: the comparison
isomorphism is *constructed* from the carried identifications and then shown to be the only
one satisfying the characterising equation.

The tensor product is written with the algebra on the left, `C ⊗[A] Inf_x(M)`, because that is
the order carrying Mathlib's `C`-module structure on a scalar extension. The characterising
equation evaluates the resulting `C`-linear map `C ⊗_A Q → C ⊗_A M` on the generators
`a ⊗ q`, so no auxiliary comparison map occurs in the statement; since those generators span
and `c ⊗ θ` spans the source, the equation pins the isomorphism down uniquely.

The hypothesis that the spectra of `A` and `C` lie in the chosen site, and that
`Spec C → Spec A` is a morphism over `S`, are the unbundled form of "`A → C` is a
homomorphism of `S`-algebras" used throughout this development.

## References

* [Stacks Project, Tag 0DNR](https://stacks.math.columbia.edu/tag/0DNR)
* [Stacks Project, Tag 087R](https://stacks.math.columbia.edu/tag/087R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace StacksDraft.PseudoCoherence

universe u₁ u₂ u₃ u₄

/-- The `Hom` base-change comparison `Hom_A(Q, M) ⊗_A C → Hom_C(C ⊗_A Q, C ⊗_A M)` is
bijective when `Q` is a finitely presented `A`-module and `C` is a flat `A`-algebra.

This is the degree-zero, `Hom`-level case of Stacks 087R and carries no tag of its own. It is
restated from `Stacks.Discriminant.rTensorHomToHomRTensor_bijective_of_finitePresentation`,
whose statement is the `Hom` part of Stacks 087Q
(`StacksDraft.PseudoCoherence.canonicalExtTensorComparison_bijective`). -/
public theorem homBaseChangeComparison_bijective
    (A : Type u₁) (C : Type u₂) [CommRing A] [CommRing C] [Algebra A C] [Module.Flat A C]
    (Q : Type u₃) (M : Type u₄) [AddCommGroup Q] [Module A Q]
    [AddCommGroup M] [Module A M] (hQ : Module.FinitePresentation A Q) :
    Function.Bijective (homBaseChangeComparison A C Q M) := by
  have := hQ
  have hφ : Function.Bijective (TensorProduct.rTensorHomToHomRTensor (RingHom.id A) Q M C) :=
    Stacks.Discriminant.rTensorHomToHomRTensor_bijective_of_finitePresentation A Q M C
  let e₁ : (Q →ₗ[A] (M ⊗[A] C)) ≃ₗ[A] (Q →ₗ[A] (C ⊗[A] M)) :=
    LinearEquiv.arrowCongr (LinearEquiv.refl A Q) (TensorProduct.comm A M C)
  let e₂ : (Q →ₗ[A] (C ⊗[A] M)) ≃ₗ[C] ((C ⊗[A] Q) →ₗ[C] (C ⊗[A] M)) :=
    LinearMap.liftBaseChangeEquiv C
  have key : ∀ t, homBaseChangeComparison A C Q M t =
      e₂ (e₁ (TensorProduct.rTensorHomToHomRTensor (RingHom.id A) Q M C t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul f c =>
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a q =>
        rw [homBaseChangeComparison_tmul_apply]
        change _ = e₂ (e₁ _) (a ⊗ₜ[A] q)
        simp [e₁, e₂, TensorProduct.smul_tmul', mul_comm]
      | add z z' hz hz' => simp [map_add, hz, hz']
    | add t t' ht ht' => simp [map_add, ht, ht']
  rw [show ((homBaseChangeComparison A C Q M : _ → _)) = _ from funext key]
  exact (e₂.bijective.comp e₁.bijective).comp hφ

end StacksDraft.PseudoCoherence

namespace Deformation.Artin

open StacksDraft.PseudoCoherence

universe u v w

section FlatBaseChange

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  (toSC : Spec (.of C) ⟶ S) (hC : B.Contains (Spec (.of C)))

/-- The morphism `Spec C ⟶ Spec A` of the big fppf site over `S` attached to an `S`-algebra
homomorphism `A → C`. -/
public def algebraOverMap
    (hAC : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC) :
    algebraOver C B S hS toSC hC ⟶ algebraOver A B S hS toS hA :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap A C))) : B.obj hC ⟶ B.obj hA)
    (ObjectProperty.hom_ext _ hAC)

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x y : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hy : p.obj y = algebraOver C B S hS toSC hC)
  (hp : p.IsFiberedInGroupoids)
  (Dx : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
  (Dy : InfinitesimalAutomorphismFunctorData C B S hS toSC hC p y hy hp)
  (Q QC : Type u) [AddCommGroup Q] [Module A Q] [AddCommGroup QC] [Module C QC]

/-- The input to flat base change for `Inf` that this file carries rather than proves.

The first three fields say that `y` is the restriction `x|_{Spec C}`: the ring map `A → C` is a
map of `S`-algebras, and there is an arrow `y ⟶ x` of `𝒳` lying over the resulting
`Spec C ⟶ Spec A`.

The remaining fields are the conclusions of Stacks 0617, 05ZF and 05ZC for the automorphism
group algebraic space `G → Spec A` of `x`, which this development does not have in that combined
form (Stacks 05ZF alone it does; see the module documentation): `Q` plays the
role of the finitely presented `A`-module `e^*Ω_{G/A}`, `QC` that of `e_C^*Ω_{G_C/C}`,
`baseChangeQ` is the base-change identification of the second with `C ⊗_A Q`, and `homRepX`,
`homRepY` are the resulting descriptions of the two infinitesimal-automorphism functors as
`Hom_A(Q, -)` and `Hom_C(QC, -)`. The finite presentation of `Q` is required separately, as
`Module.FinitePresentation A Q`; it is the form in which the source's hypothesis that
`ℐ_𝒳 → 𝒳` is locally of finite presentation is used. -/
public structure InfHomRepresentation where
  /-- `A → C` is a homomorphism of `S`-algebras. -/
  compatible : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC
  /-- The arrow of `𝒳` exhibiting `y` as a restriction of `x`. -/
  restriction : y ⟶ x
  /-- The arrow lies over `Spec C ⟶ Spec A`, so that `y = x|_{Spec C}`. -/
  restriction_isHomLift :
    p.IsHomLift (algebraOverMap A C B S hS toS hA toSC hC compatible) restriction
  /-- The base change of `Q` to `C`, standing for the base change of `e^*Ω_{G/A}`. -/
  baseChangeQ : (C ⊗[A] Q) ≃ₗ[C] QC
  /-- `Inf_x(M) = Hom_A(Q, M)`. -/
  homRepX : ∀ M : SiteModule A B,
    (Dx.functor.obj M : Type w) ≃ₗ[A] (Q →ₗ[A] (M.obj : Type u))
  /-- `Inf_y(N) = Hom_C(QC, N)`. -/
  homRepY : ∀ N : SiteModule C B,
    (Dy.functor.obj N : Type w) ≃ₗ[C] (QC →ₗ[C] (N.obj : Type u))

variable [Module.Flat A C] [Module.FinitePresentation A Q]

/-- **Stacks 0DNR.** Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`,
let `A → C` be a flat homomorphism of `S`-algebras, let `x` be an object of `𝒳` over `Spec A`
and let `y = x|_{Spec C}`. Then the infinitesimal automorphisms of the trivial deformations of
`x` and of `y` satisfy `Inf_x(M) ⊗_A C = Inf_y(C ⊗_A M)`: there is a unique `C`-linear
isomorphism `C ⊗_A Inf_x(M) ≅ Inf_y(N)`, for `N` a site module identified with `C ⊗_A M`,
which sends `c ⊗ θ` to the base change of `θ` scaled by `c`.

The identification of `Inf_x` with `Hom_A(Q, -)`, of `Inf_y` with `Hom_C(QC, -)`, and of `QC`
with `C ⊗_A Q`, together with the finite presentation of `Q`, are hypotheses: they are the
inputs the source takes from Stacks 0617, 05ZF and 05ZC, which this development does not have in
that combined form. See `Deformation.Artin.InfHomRepresentation`. What is proved here is the flat
base change itself, by Stacks 087R. -/
@[stacks 0DNR]
public theorem existsUnique_infFlatBaseChange
    (D : InfHomRepresentation A C B S hS toS hA toSC hC p x y hx hy hp Dx Dy Q QC)
    (M : SiteModule A B) (N : SiteModule C B)
    (hMN : (C ⊗[A] (M.obj : Type u)) ≃ₗ[C] (N.obj : Type u)) :
    ∃ e : (C ⊗[A] (Dx.functor.obj M : Type w)) ≃ₗ[C] (Dy.functor.obj N : Type w),
      (∀ (c a : C) (θ : (Dx.functor.obj M : Type w)) (q : Q),
        D.homRepY N (e (c ⊗ₜ[A] θ)) (D.baseChangeQ (a ⊗ₜ[A] q)) =
          hMN ((a * c) ⊗ₜ[A] D.homRepX M θ q)) ∧
      ∀ e' : (C ⊗[A] (Dx.functor.obj M : Type w)) ≃ₗ[C] (Dy.functor.obj N : Type w),
        (∀ (c a : C) (θ : (Dx.functor.obj M : Type w)) (q : Q),
          D.homRepY N (e' (c ⊗ₜ[A] θ)) (D.baseChangeQ (a ⊗ₜ[A] q)) =
            hMN ((a * c) ⊗ₜ[A] D.homRepX M θ q)) → e' = e := by
  -- `ρ f` is the base change of `f : Hom_A(Q, M)`, as a `C`-linear map `C ⊗ Q → C ⊗ M`.
  let ρ : (Q →ₗ[A] (M.obj : Type u)) →ₗ[A]
      ((C ⊗[A] Q) →ₗ[C] (C ⊗[A] (M.obj : Type u))) :=
    (homBaseChangeComparison A C Q (M.obj : Type u)).comp
      ((TensorProduct.mk A (Q →ₗ[A] (M.obj : Type u)) C).flip 1)
  let Φ : (C ⊗[A] (Q →ₗ[A] (M.obj : Type u))) →ₗ[C]
      ((C ⊗[A] Q) →ₗ[C] (C ⊗[A] (M.obj : Type u))) := ρ.liftBaseChange C
  -- `Φ` is the `Hom` base-change comparison read in the other tensor order, hence bijective.
  have hΦfun : ∀ t, Φ t =
      homBaseChangeComparison A C Q (M.obj : Type u)
        (TensorProduct.comm A C (Q →ₗ[A] (M.obj : Type u)) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c f =>
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a q =>
        have h₁ : Φ (c ⊗ₜ[A] f) (a ⊗ₜ[A] q) = c • (a ⊗ₜ[A] f q) := by
          change (c • ρ f) (a ⊗ₜ[A] q) = _
          simp [ρ, homBaseChangeComparison_tmul_apply]
        rw [h₁, TensorProduct.smul_tmul', TensorProduct.comm_tmul,
          homBaseChangeComparison_tmul_apply]
        rw [smul_eq_mul, mul_comm c a]
      | add z z' hz hz' => simp [map_add, hz, hz']
    | add t t' ht ht' => simp [map_add, ht, ht']
  have hΦ : Function.Bijective Φ := by
    rw [show ((Φ : _ → _)) = _ from funext hΦfun]
    exact (homBaseChangeComparison_bijective A C Q (M.obj : Type u)
      (inferInstance : Module.FinitePresentation A Q)).comp
      (TensorProduct.comm A C (Q →ₗ[A] (M.obj : Type u))).bijective
  let b₁ : (C ⊗[A] (Dx.functor.obj M : Type w)) ≃ₗ[C]
      (C ⊗[A] (Q →ₗ[A] (M.obj : Type u))) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) (D.homRepX M)
  let b₄ : ((C ⊗[A] Q) →ₗ[C] (C ⊗[A] (M.obj : Type u))) ≃ₗ[C]
      (QC →ₗ[C] (N.obj : Type u)) := LinearEquiv.arrowCongr D.baseChangeQ hMN
  let e₀ : (C ⊗[A] (Dx.functor.obj M : Type w)) ≃ₗ[C] (Dy.functor.obj N : Type w) :=
    b₁.trans ((LinearEquiv.ofBijective Φ hΦ).trans (b₄.trans (D.homRepY N).symm))
  have hchar : ∀ (c a : C) (θ : (Dx.functor.obj M : Type w)) (q : Q),
      D.homRepY N (e₀ (c ⊗ₜ[A] θ)) (D.baseChangeQ (a ⊗ₜ[A] q)) =
        hMN ((a * c) ⊗ₜ[A] D.homRepX M θ q) := by
    intro c a θ q
    have h₄ : b₁ (c ⊗ₜ[A] θ) = c ⊗ₜ[A] D.homRepX M θ :=
      TensorProduct.AlgebraTensorModule.congr_tmul (LinearEquiv.refl C C)
        (D.homRepX M) c θ
    have h₂ : D.homRepY N (e₀ (c ⊗ₜ[A] θ)) = b₄ (Φ (c ⊗ₜ[A] D.homRepX M θ)) := by
      change D.homRepY N ((D.homRepY N).symm (b₄ (Φ (b₁ (c ⊗ₜ[A] θ))))) = _
      rw [LinearEquiv.apply_symm_apply, h₄]
    rw [h₂]
    have h₃ : Φ (c ⊗ₜ[A] D.homRepX M θ) (a ⊗ₜ[A] q) = c • (a ⊗ₜ[A] D.homRepX M θ q) := by
      change (c • ρ (D.homRepX M θ)) (a ⊗ₜ[A] q) = _
      simp [ρ, homBaseChangeComparison_tmul_apply]
    change hMN (Φ (c ⊗ₜ[A] D.homRepX M θ)
      (D.baseChangeQ.symm (D.baseChangeQ (a ⊗ₜ[A] q)))) = _
    rw [LinearEquiv.symm_apply_apply, h₃, TensorProduct.smul_tmul', smul_eq_mul, mul_comm c a]
  refine ⟨e₀, hchar, fun e' he' => ?_⟩
  refine LinearEquiv.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c θ =>
    refine (D.homRepY N).injective (LinearMap.ext fun v => ?_)
    have hspan : ∀ u : C ⊗[A] Q,
        D.homRepY N (e' (c ⊗ₜ[A] θ)) (D.baseChangeQ u) =
          D.homRepY N (e₀ (c ⊗ₜ[A] θ)) (D.baseChangeQ u) := by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul a q => rw [he' c a θ q, hchar c a θ q]
      | add u u' hu hu' => simp [map_add, hu, hu']
    have := hspan (D.baseChangeQ.symm v)
    rwa [LinearEquiv.apply_symm_apply] at this
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

end FlatBaseChange

end Deformation.Artin
