module

public import StacksFrontier.Deformation.Artin.Infinitesimal.FlatBaseChange

/-!
# Flat base change for the tangent functor of an object

Let `𝒳` be an algebraic stack over a scheme `S` whose structure morphism `𝒳 → S` is locally of
finite presentation, let `A → C` be a flat homomorphism of `S`-algebras, let `x` be an object of
`𝒳` over `Spec A` and let `y = x|_{Spec C}`. For an `A`-module `M` the isomorphism classes of
lifts of `x` to the trivial square-zero extension `Spec A[M]` form an `A`-linear functor
`T_x` of `M` (Stacks 07Y9, `Deformation.Artin.TangentFunctorData`), and likewise `T_y` over
`C`. **Stacks 0DNT** is the flat base change `T_x(M) ⊗_A C = T_y(C ⊗_A M)`.

The proof in the source first reduces to the case of an algebraic space `X` locally of finite
presentation over `S`, using the sheaf property of Stacks 0DNS and the exact sequence
`T_{e ∘ u}(M) → T_u(M) ⊕ T_u(M) → T_x(M) → 0` of Stacks 0DNN for a smooth atlas `U → 𝒳`. In that
case `T_x(M) = Hom_A(x^*Ω_{X/S}, M)` by the discussion of Stacks 0617, the module `x^*Ω_{X/S}` is
finitely presented by Stacks 05ZF with base change `y^*Ω_{X/S}`, and the conclusion is the flat
base change of `Hom` out of a finitely presented module, Stacks 087R.

This file proves that last step. Its input, the description of the two tangent functors as
`Hom_A(P, -)` and `Hom_C(PC, -)` with `PC = C ⊗_A P` and `P` finitely presented, is the explicit
datum `Deformation.Artin.TangentHomRepresentation`. Stacks 0DNT itself, without this datum, is
`Deformation.Artin.exists_tangentFlatBaseChange` in
`StacksFrontier.Deformation.Artin.Infinitesimal.TangentFlatBaseChangeStack`, which descends flat
base change from chart points along a faithfully flat finitely presented cover.

## Main definitions

* `Deformation.Artin.TangentHomRepresentation` — the data that `y` is the restriction of `x`
  along `A → C`, a finitely presented `A`-module `P` with its base change to `C`, and the
  identifications of `T_x` and `T_y` with `Hom_A(P, -)` and
  `Hom_C(PC, -)`.

## Main results

* `StacksDraft.PseudoCoherence.existsUnique_homFlatBaseChange` — flat base change for `Hom` out
  of a finitely presented module, transported along chosen identifications of the source and
  target with such a `Hom`: there is a unique `C`-linear isomorphism `C ⊗_A T ≅ U` matching the
  base change of homomorphisms on pure tensors. This is the `Hom`-level content of Stacks 087R
  in the shape the base-change statements of this development use.
* `Deformation.Artin.existsUnique_tangentFlatBaseChange` — **Stacks 0DNT**, final step: there
  is a unique `C`-linear isomorphism `C ⊗_A T_x(M) ≅ T_y(N)`, for `N` a site module identified
  with `C ⊗_A M`, carrying `c ⊗ t` to the base change of `t` scaled by `c`.

## Implementation notes

`T_x(M)` is a *chosen* object: `Deformation.Artin.tangentFunctor` selects a member of
`Deformation.Artin.TangentFunctorData`, and the only handle on its values is the family of
bijections with the isomorphism classes of lifts. So the two functors enter as arbitrary
members of that structure, exactly as in Stacks 07YA and exactly as the sibling statement
`Deformation.Artin.existsUnique_infFlatBaseChange` for `Inf` does; nothing here chooses data
from an existence statement, and the comparison isomorphism is *constructed* from the carried
identifications and then shown to be the only one satisfying the characterising equation.

The tensor product is written with the algebra on the left, `C ⊗[A] T_x(M)`, because that is
the order carrying Mathlib's `C`-module structure on a scalar extension. The characterising
equation evaluates the resulting `C`-linear map `C ⊗_A P → C ⊗_A M` on the generators `a ⊗ q`,
so no auxiliary comparison map occurs in the statement; since those generators span and `c ⊗ t`
spans the source, the equation pins the isomorphism down uniquely.

The hypothesis that the spectra of `A` and `C` lie in the chosen site, and that
`Spec C → Spec A` is a morphism over `S`, are the unbundled form of "`A → C` is a homomorphism
of `S`-algebras". The finite presentation of `P` is the form in which the source's hypothesis
that `𝒳 → S` is locally of finite presentation is used.

The identification `T_x(M) = Hom_A(x^*Ω_{X/S}, M)` is justified in the source by a pointer to
Section 76.17 (Stacks 0617) rather than to a numbered lemma, so
`Deformation.Artin.TangentHomRepresentation` carries no `@[stacks]` key.

## References

* [Stacks Project, Tag 0DNT](https://stacks.math.columbia.edu/tag/0DNT)
* [Stacks Project, Tag 087R](https://stacks.math.columbia.edu/tag/087R)
* [Stacks Project, Tag 0DNR](https://stacks.math.columbia.edu/tag/0DNR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace StacksDraft.PseudoCoherence

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

/-- Flat base change for `Hom` out of a finitely presented module, read through chosen
identifications of the two sides.

Given a flat `A`-algebra `C`, a finitely presented `A`-module `P`, an `A`-module `T`
identified with `Hom_A(P, M)` and a `C`-module `U` identified with `Hom_C(PC, N)`, where
`PC = C ⊗_A P` and `N = C ⊗_A M`, there is exactly one `C`-linear isomorphism
`C ⊗_A T ≅ U` sending `c ⊗ t` to the base change of `t` scaled by `c`.

This is the `Hom`-level case of Stacks 087R, deduced from
`StacksDraft.PseudoCoherence.homBaseChangeComparison_bijective`. -/
public theorem existsUnique_homFlatBaseChange
    (A : Type u₁) (C : Type u₂) [CommRing A] [CommRing C] [Algebra A C] [Module.Flat A C]
    (P : Type u₃) [AddCommGroup P] [Module A P]
    (M : Type u₄) [AddCommGroup M] [Module A M]
    (PC : Type u₅) [AddCommGroup PC] [Module C PC]
    (N : Type u₆) [AddCommGroup N] [Module C N]
    (T : Type u₇) [AddCommGroup T] [Module A T]
    (U : Type u₈) [AddCommGroup U] [Module C U]
    (hP : Module.FinitePresentation A P)
    (sP : (C ⊗[A] P) ≃ₗ[C] PC) (hT : T ≃ₗ[A] (P →ₗ[A] M))
    (hU : U ≃ₗ[C] (PC →ₗ[C] N)) (hMN : (C ⊗[A] M) ≃ₗ[C] N) :
    ∃ e : (C ⊗[A] T) ≃ₗ[C] U,
      (∀ (c a : C) (t : T) (q : P),
        hU (e (c ⊗ₜ[A] t)) (sP (a ⊗ₜ[A] q)) = hMN ((a * c) ⊗ₜ[A] hT t q)) ∧
      ∀ e' : (C ⊗[A] T) ≃ₗ[C] U,
        (∀ (c a : C) (t : T) (q : P),
          hU (e' (c ⊗ₜ[A] t)) (sP (a ⊗ₜ[A] q)) = hMN ((a * c) ⊗ₜ[A] hT t q)) → e' = e := by
  -- `ρ f` is the base change of `f : Hom_A(P, M)`, as a `C`-linear map `C ⊗ P → C ⊗ M`.
  let ρ : (P →ₗ[A] M) →ₗ[A] ((C ⊗[A] P) →ₗ[C] (C ⊗[A] M)) :=
    (homBaseChangeComparison A C P M).comp ((TensorProduct.mk A (P →ₗ[A] M) C).flip 1)
  let Φ : (C ⊗[A] (P →ₗ[A] M)) →ₗ[C] ((C ⊗[A] P) →ₗ[C] (C ⊗[A] M)) := ρ.liftBaseChange C
  have hΦtmul : ∀ (c a : C) (f : P →ₗ[A] M) (q : P),
      Φ (c ⊗ₜ[A] f) (a ⊗ₜ[A] q) = c • (a ⊗ₜ[A] f q) := by
    intro c a f q
    change (c • ρ f) (a ⊗ₜ[A] q) = _
    simp [ρ, homBaseChangeComparison_tmul_apply]
  -- `Φ` is the `Hom` base-change comparison read in the other tensor order, hence bijective.
  have hΦfun : ∀ z, Φ z =
      homBaseChangeComparison A C P M (TensorProduct.comm A C (P →ₗ[A] M) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c f =>
      apply LinearMap.ext
      intro v
      induction v using TensorProduct.inductionOn with
      | tmul a q =>
        rw [hΦtmul, TensorProduct.smul_tmul', TensorProduct.comm_tmul,
          homBaseChangeComparison_tmul_apply]
        rw [smul_eq_mul, mul_comm c a]
      | add v v' hv hv' => simp [map_add, hv, hv']
    | add z z' hz hz' => simp [map_add, hz, hz']
  have hΦ : Function.Bijective Φ := by
    rw [show ((Φ : _ → _)) = _ from funext hΦfun]
    exact (homBaseChangeComparison_bijective A C P M hP).comp
      (TensorProduct.comm A C (P →ₗ[A] M)).bijective
  let b₁ : (C ⊗[A] T) ≃ₗ[C] (C ⊗[A] (P →ₗ[A] M)) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) hT
  let b₄ : ((C ⊗[A] P) →ₗ[C] (C ⊗[A] M)) ≃ₗ[C] (PC →ₗ[C] N) := LinearEquiv.arrowCongr sP hMN
  -- The value of the transported comparison on a pure tensor, at a pure tensor of `C ⊗ P`.
  have hval : ∀ (c a : C) (t : T) (q : P),
      hU ((b₁.trans ((LinearEquiv.ofBijective Φ hΦ).trans (b₄.trans hU.symm))) (c ⊗ₜ[A] t))
          (sP (a ⊗ₜ[A] q)) = hMN ((a * c) ⊗ₜ[A] hT t q) := by
    intro c a t q
    have h₄ : b₁ (c ⊗ₜ[A] t) = c ⊗ₜ[A] hT t :=
      TensorProduct.AlgebraTensorModule.congr_tmul (LinearEquiv.refl C C) hT c t
    have h₂ : hU ((b₁.trans ((LinearEquiv.ofBijective Φ hΦ).trans
        (b₄.trans hU.symm))) (c ⊗ₜ[A] t)) = b₄ (Φ (c ⊗ₜ[A] hT t)) := by
      change hU (hU.symm (b₄ (Φ (b₁ (c ⊗ₜ[A] t))))) = _
      rw [LinearEquiv.apply_symm_apply, h₄]
    rw [h₂]
    change hMN (Φ (c ⊗ₜ[A] hT t) (sP.symm (sP (a ⊗ₜ[A] q)))) = _
    rw [LinearEquiv.symm_apply_apply, hΦtmul, TensorProduct.smul_tmul', smul_eq_mul, mul_comm c a]
  refine ⟨b₁.trans ((LinearEquiv.ofBijective Φ hΦ).trans (b₄.trans hU.symm)), hval, ?_⟩
  intro e' he'
  refine LinearEquiv.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul c t =>
    refine hU.injective (LinearMap.ext fun v => ?_)
    -- Both sides agree on the generators of `C ⊗ P`, and `sP` is onto `PC`.
    have hspan : ∀ u : C ⊗[A] P,
        hU (e' (c ⊗ₜ[A] t)) (sP u) =
          hU ((b₁.trans ((LinearEquiv.ofBijective Φ hΦ).trans
            (b₄.trans hU.symm))) (c ⊗ₜ[A] t)) (sP u) := by
      intro u
      induction u using TensorProduct.inductionOn with
      | tmul a q => rw [he' c a t q, hval c a t q]
      | add u u' hu hu' => simp [map_add, hu, hu']
    have := hspan (sP.symm v)
    rwa [LinearEquiv.apply_symm_apply] at this
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

end StacksDraft.PseudoCoherence

namespace Deformation.Artin

open StacksDraft.PseudoCoherence

universe u v w

section TangentFlatBaseChange

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  (toSC : Spec (.of C) ⟶ S) (hC : B.Contains (Spec (.of C)))

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x y : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hy : p.obj y = algebraOver C B S hS toSC hC)
  (Tx : TangentFunctorData A B S hS toS hA p x hx)
  (Ty : TangentFunctorData C B S hS toSC hC p y hy)
  (P PC : Type u) [AddCommGroup P] [Module A P] [AddCommGroup PC] [Module C PC]

/-- The data identifying the tangent functors `T_x` and `T_y` with `Hom_A(P, -)` and
`Hom_C(PC, -)`, the input to flat base change for `T`.

The first three fields say that `y` is the restriction `x|_{Spec C}`: the ring map `A → C` is a
map of `S`-algebras, and there is an arrow `y ⟶ x` of `𝒳` lying over the resulting
`Spec C ⟶ Spec A`.

The remaining fields are what the source obtains, in the algebraic space case, from the discussion
of Stacks 0617 together with Stacks 05ZF: `P` plays the role of the finitely presented `A`-module
`x^*Ω_{X/S}`, `PC` that of `y^*Ω_{X/S}`, `baseChangeP` is the base-change identification of the
second with `C ⊗_A P`, and `homRepX`, `homRepY` are the resulting descriptions of the two tangent
functors as `Hom_A(P, -)` and `Hom_C(PC, -)`. The finite presentation of `P` is required
separately, as `Module.FinitePresentation A P`; it is the form in which the source's hypothesis
that `𝒳 → S` is locally of finite presentation is used. -/
public structure TangentHomRepresentation where
  /-- `A → C` is a homomorphism of `S`-algebras. -/
  compatible : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC
  /-- The arrow of `𝒳` exhibiting `y` as a restriction of `x`. -/
  restriction : y ⟶ x
  /-- The arrow lies over `Spec C ⟶ Spec A`, so that `y = x|_{Spec C}`. -/
  restriction_isHomLift :
    p.IsHomLift (algebraOverMap A C B S hS toS hA toSC hC compatible) restriction
  /-- The base change of `P` to `C`, standing for the base change of `x^*Ω_{X/S}`. -/
  baseChangeP : (C ⊗[A] P) ≃ₗ[C] PC
  /-- `T_x(M) = Hom_A(P, M)`. -/
  homRepX : ∀ M : SiteModule A B,
    (Tx.functor.obj M : Type max (u + 1) v w) ≃ₗ[A] (P →ₗ[A] (M.obj : Type u))
  /-- `T_y(N) = Hom_C(PC, N)`. -/
  homRepY : ∀ N : SiteModule C B,
    (Ty.functor.obj N : Type max (u + 1) v w) ≃ₗ[C] (PC →ₗ[C] (N.obj : Type u))

variable [Module.Flat A C] [Module.FinitePresentation A P]

/-- **Stacks 0DNT, final step.** Let `𝒳` be an algebraic stack over `S` with `𝒳 → S` locally of
finite presentation, let `A → C` be a flat homomorphism of `S`-algebras, let `x` be an object of
`𝒳` over `Spec A` and let `y = x|_{Spec C}`. Then the tangent functors of `x` and of `y` satisfy
`T_x(M) ⊗_A C = T_y(C ⊗_A M)`: there is a unique `C`-linear isomorphism
`C ⊗_A T_x(M) ≅ T_y(N)`, for `N` a site module identified with `C ⊗_A M`, which sends `c ⊗ t`
to the base change of `t` scaled by `c`.

The identification of `T_x` with `Hom_A(P, -)`, of `T_y` with `Hom_C(PC, -)`, and of `PC` with
`C ⊗_A P`, together with the finite presentation of `P`, are hypotheses, bundled as
`Deformation.Artin.TangentHomRepresentation`; in the source they come from Stacks 0617 and 05ZF
for an algebraic space locally of finite presentation over `S`. The conclusion is then the flat
base change of Stacks 087R; Stacks 0DNT in full is
`Deformation.Artin.exists_tangentFlatBaseChange`. -/
public theorem existsUnique_tangentFlatBaseChange
    (D : TangentHomRepresentation A C B S hS toS hA toSC hC p x y hx hy Tx Ty P PC)
    (M : SiteModule A B) (N : SiteModule C B)
    (hMN : (C ⊗[A] (M.obj : Type u)) ≃ₗ[C] (N.obj : Type u)) :
    ∃ e : (C ⊗[A] (Tx.functor.obj M : Type max (u + 1) v w)) ≃ₗ[C]
        (Ty.functor.obj N : Type max (u + 1) v w),
      (∀ (c a : C) (t : (Tx.functor.obj M : Type max (u + 1) v w)) (q : P),
        D.homRepY N (e (c ⊗ₜ[A] t)) (D.baseChangeP (a ⊗ₜ[A] q)) =
          hMN ((a * c) ⊗ₜ[A] D.homRepX M t q)) ∧
      ∀ e' : (C ⊗[A] (Tx.functor.obj M : Type max (u + 1) v w)) ≃ₗ[C]
          (Ty.functor.obj N : Type max (u + 1) v w),
        (∀ (c a : C) (t : (Tx.functor.obj M : Type max (u + 1) v w)) (q : P),
          D.homRepY N (e' (c ⊗ₜ[A] t)) (D.baseChangeP (a ⊗ₜ[A] q)) =
            hMN ((a * c) ⊗ₜ[A] D.homRepX M t q)) → e' = e :=
  existsUnique_homFlatBaseChange A C P (M.obj : Type u) PC (N.obj : Type u)
    (Tx.functor.obj M : Type max (u + 1) v w) (Ty.functor.obj N : Type max (u + 1) v w)
    inferInstance D.baseChangeP (D.homRepX M) (D.homRepY N) hMN

end TangentFlatBaseChange

end Deformation.Artin

end
