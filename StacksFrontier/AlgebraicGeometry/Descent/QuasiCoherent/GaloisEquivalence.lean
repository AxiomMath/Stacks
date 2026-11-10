module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Galois
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.GaloisDescentEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcStack
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Galois descent for quasi-coherent modules: the transition morphism and its cocycle

Let `f : X ⟶ Y` be a morphism of schemes carrying an action `a` of a finite group `G` over `Y`
whose comparison map `∐_{σ : G} X ⟶ X ×_Y X`, given on the summand indexed by `σ` by
`(𝟙, f_σ)`, is an isomorphism.  A Galois descent system is a quasi-coherent module `ℱ` on `X`
together with isomorphisms `φ_σ : ℱ ≅ f_σ^* ℱ` satisfying `φ_(στ) = f_σ^*(φ_τ) ∘ φ_σ`.

This file builds the transition morphism over `X ×_Y X` attached to such a system, verifies its
cocycle identity over `X ×_Y X ×_Y X`, and deduces that quasi-coherent modules on `Y` are
equivalent to Galois descent systems on `X` when `f` is surjective, finite and étale.

## Main definitions

* `Stacks.Descent.actionHom`: the isomorphism `φ_σ` of a Galois descent system, as a morphism
  from the inverse image of `ℱ` along the identity to its inverse image along `f_σ`.

## Main results

* `Stacks.Descent.actionHomCocycle`: the Galois cocycle condition for
  `Stacks.Descent.actionHom` — transporting `φ_τ` along `f_σ` and composing with `φ_σ` gives
  `φ_(στ)`.
* `Stacks.Descent.transitionCocycle`: a morphism `θ` over a chosen fibre square of `f` whose
  restriction to each summand of `∐_{σ : G} X` is `φ_σ` satisfies the cocycle identity over a
  chosen triple fibre product, as soon as the triple comparison presents that product as the
  coproduct of copies of `X` indexed by `G × G`.
* `Stacks.Descent.transition_pullHom'`: the same morphism read through
  `CategoryTheory.Pseudofunctor.DescentData'.pullHom'`.
* `Stacks.Descent.galoisCoverComparison_ι_comp_fst` and
  `Stacks.Descent.galoisCoverComparison_ι_comp_snd`: the two legs of the Galois cover comparison
  on the summand indexed by `σ`.
* `Stacks.Descent.galoisTripleComparison_ι_p₁`,
  `Stacks.Descent.galoisTripleComparison_ι_p₂` and
  `Stacks.Descent.galoisTripleComparison_ι_p₃`: the three legs of
  `Stacks.Descent.galoisTripleComparison` on the summand indexed by `(σ, τ)` are `𝟙`, `f_σ` and
  `f_(στ)`.
* `Stacks.Descent.galoisDescentFunctor_full`, `Stacks.Descent.galoisDescentFunctor_essSurj` and
  `Stacks.Descent.galoisDescentFunctor_isEquivalence`: the comparison functor of Galois descent
  is full, essentially surjective, and an equivalence.
* `Stacks.Descent.nonempty_equivalence_galoisDescentData`: **Galois descent for quasi-coherent
  modules**, with no hypotheses beyond the Galois situation itself.

## Implementation notes

Every statement about the transition morphism is made at *variable* data: the chosen fibre
products, the comparison morphisms out of the coproducts, and the transition morphism `θ`
itself are all parameters.  This is what keeps the definitional comparisons tractable, and it
is the discipline that
`StacksFrontier/AlgebraicGeometry/Descent/AffineQuasicoherentEffective.lean`
already records for the same pseudofunctor: the identification of
`(AlgebraicGeometry.modulePullbackPseudofunctor.map g.op.toLoc).toFunctor` with
`AlgebraicGeometry.Scheme.Modules.pullback g` is then the generic unfolding of the
pseudofunctor at a variable morphism, whereas at a concrete morphism and a concrete chosen
pullback the kernel does not finish the same conversion.  The transition morphism is produced by
a choice, so its normal form is an entire Zariski gluing, and keeping `θ` a parameter keeps it
from being unfolded.

For the same reason the rearrangement lemmas of the first section are stated for an arbitrary
pseudofunctor rather than for `AlgebraicGeometry.modulePullbackPseudofunctor`, and are applied as
terms: `rw` and `simp` operate at `implicit` transparency, at which the two spellings of the
inverse image are not interchangeable.

The target of `Stacks.Descent.galoisTripleComparison` is spelled
`(Stacks.Descent.galoisChosenPullback₃ f).pullback`, and the legs of the comparison are maps out
of the iterated pullback `(X ×_Y X) ×_X (X ×_Y X)`.  The two spellings are definitionally equal,
but a composite recorded at one of them is not rewritable by `rw` or `simp` at the other, so the
legs are computed on the same morphism with its target spelled as the iterated pullback.

The identification of the image of a descent datum under
`Stacks.Descent.galoisDescentFunctor` with the Galois descent system it was assembled from is
made field by field, and the comparison of the action-indexed isomorphisms is heterogeneous:
reducing `((galoisDescentFunctor G f a).obj D).module` to the component of `D` at the only index
unfolds the comparison functor, and `Stacks.Descent.galoisDescentFunctor_obj_module` records
that reduction once at a variable datum.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 0CDR](https://stacks.math.columbia.edu/tag/0CDR)
* [Stacks Project, Tag 0D1V](https://stacks.math.columbia.edu/tag/0D1V)
-/
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry

open Pseudofunctor.LocallyDiscreteOpToCat

universe w' w v u

namespace Stacks.Descent

/-! ### The pullback dictionary -/

section PullHom

variable {C : Type w} [Category.{w'} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u}}

private lemma conjugateCancel {A B A' B' : C} (α : A ≅ A') (β : B ≅ B') (e : A ⟶ B) :
    α.hom ≫ (α.inv ≫ e ≫ β.hom) ≫ β.inv = e := by simp

private lemma compCongr {A B D : C} {x x' : A ⟶ B} {y y' : B ⟶ D}
    (hx : x = x') (hy : y = y') : x ≫ y = x' ≫ y' := by rw [hx, hy]

private lemma pullHomCongr {X₁ X₂ T U : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {f₁ : T ⟶ X₁} {f₂ : T ⟶ X₂}
    {h k : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    (hk : h = k) (g : U ⟶ T) (g₁ : U ⟶ X₁) (g₂ : U ⟶ X₂)
    (w₁ : g ≫ f₁ = g₁) (w₂ : g ≫ f₂ = g₂) :
    pullHom h g g₁ g₂ w₁ w₂ = pullHom k g g₁ g₂ w₁ w₂ := by rw [hk]

private lemma pullHomCongrMap {X₁ X₂ T U : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {f₁ : T ⟶ X₁} {f₂ : T ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {g g' : U ⟶ T} (hg : g = g') (g₁ : U ⟶ X₁) (g₂ : U ⟶ X₂)
    (w₁ : g ≫ f₁ = g₁) (w₂ : g ≫ f₂ = g₂) (w₁' : g' ≫ f₁ = g₁) (w₂' : g' ≫ f₂ = g₂) :
    pullHom φ g g₁ g₂ w₁ w₂ = pullHom φ g' g₁ g₂ w₁' w₂' := by subst hg; rfl

/-- Pulling back a pulled-back morphism along `k` is pulling back along `k ≫ ψ`. -/
private lemma pullHomPullHomOfComp {X₁ X₂ T V U : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {f₁ : T ⟶ X₁} {f₂ : T ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : V ⟶ T) (k : U ⟶ V) {c : U ⟶ T} (hk : k ≫ ψ = c) (s₁ : V ⟶ X₁) (s₂ : V ⟶ X₂)
    (g₁ : U ⟶ X₁) (g₂ : U ⟶ X₂) (w₁ : ψ ≫ f₁ = s₁) (w₂ : ψ ≫ f₂ = s₂) (v₁ : k ≫ s₁ = g₁)
    (v₂ : k ≫ s₂ = g₂) (u₁ : c ≫ f₁ = g₁) (u₂ : c ≫ f₂ = g₂) :
    pullHom (pullHom φ ψ s₁ s₂ w₁ w₂) k g₁ g₂ v₁ v₂ = pullHom φ c g₁ g₂ u₁ u₂ :=
  (pullHom_pullHom φ ψ s₁ s₂ k g₁ g₂ w₁ w₂ v₁ v₂).trans (pullHomCongrMap φ hk g₁ g₂ _ _ u₁ u₂)

private lemma pullHomComp {X₁ X₂ X₃ T U : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {f₁ : T ⟶ X₁} {f₂ : T ⟶ X₂} {f₃ : T ⟶ X₃}
    (h : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (k : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (g : U ⟶ T) (g₁ : U ⟶ X₁) (g₂ : U ⟶ X₂) (g₃ : U ⟶ X₃)
    (h₁ : g ≫ f₁ = g₁) (h₂ : g ≫ f₂ = g₂) (h₃ : g ≫ f₃ = g₃) :
    pullHom (h ≫ k) g g₁ g₃ h₁ h₃ = pullHom h g g₁ g₂ h₁ h₂ ≫ pullHom k g g₂ g₃ h₂ h₃ := by
  dsimp only [pullHom]
  rw [Functor.map_comp]
  simp

private lemma pullHomEqIff {X₁ X₂ T U : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {f₁ : T ⟶ X₁} {f₂ : T ⟶ X₂}
    (h k : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : U ⟶ T) (g₁ : U ⟶ X₁) (g₂ : U ⟶ X₂) (h₁ : g ≫ f₁ = g₁) (h₂ : g ≫ f₂ = g₂) :
    pullHom h g g₁ g₂ h₁ h₂ = pullHom k g g₁ g₂ h₁ h₂ ↔
      (F.map g.op.toLoc).toFunctor.map h = (F.map g.op.toLoc).toFunctor.map k := by
  dsimp only [pullHom]
  rw [cancel_epi, cancel_mono]

private lemma pullHomMap {Z T U : C} {M N : F.obj (.mk (op Z))} (h : M ⟶ N) (p : T ⟶ Z)
    (g : U ⟶ T) (gp : U ⟶ Z) (w : g ≫ p = gp) :
    pullHom ((F.map p.op.toLoc).toFunctor.map h) g gp gp w w =
      (F.map gp.op.toLoc).toFunctor.map h := by
  let α := Cat.Hom.toNatIso (F.mapComp' p.op.toLoc g.op.toLoc gp.op.toLoc
    (by simpa using congrArg (fun t ↦ t.op.toLoc) w))
  change α.hom.app M ≫
      (F.map p.op.toLoc ≫ F.map g.op.toLoc).toFunctor.map h ≫ α.inv.app N = _
  rw [← Category.assoc, ← α.hom.naturality h, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

end PullHom



end Stacks.Descent

namespace Stacks.Descent

/-! ### The two spellings of inverse image -/

private lemma pullbackMapEq {Z W : Scheme.{u}} (g : Z ⟶ W) {M N : W.Modules} (h : M ⟶ N) :
    (modulePullbackPseudofunctor.{u}.map g.op.toLoc).toFunctor.map h =
      (Scheme.Modules.pullback g).map h := rfl

private lemma pullHomNormalize {Z T : Scheme.{u}} {M N : Z.Modules} (p : Z ⟶ Z) (g : T ⟶ Z)
    (gp : T ⟶ Z) (w : g ≫ p = gp) (h : M ⟶ (Scheme.Modules.pullback p).obj N) :
    pullHom (F := modulePullbackPseudofunctor.{u})
        ((Scheme.Modules.pullbackId Z).hom.app M ≫ h) g g gp (Category.comp_id _) w =
      (Scheme.Modules.pullback g).map h ≫
        (Scheme.Modules.pullbackComp g p).hom.app N ≫
        (Scheme.Modules.pullbackCongr w).hom.app N := by
  have hid := galoisMapComp'_id_hom_app (X₁ := T) (X₃ := Z) g M
  have hinv := galoisMapComp'_inv_app (X₁ := T) (X₂ := Z) (X₃ := Z) p g gp w N
  dsimp only [pullHom]
  rw [hid, hinv]
  change (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Z).inv.app M) ≫
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Z).hom.app M ≫ h) ≫
      ((Scheme.Modules.pullbackComp g p).hom ≫
        (Scheme.Modules.pullbackCongr w).hom).app N = _
  rw [← Functor.map_comp_assoc]
  simp only [Iso.inv_hom_id_app_assoc, NatTrans.comp_app]

/-! ### Gluing an inverse-image morphism along a coproduct presentation -/

private theorem existsHomOfSigmaIsoP {I : Type v} [Finite I] {Z : I → Scheme.{u}}
    {T : Scheme.{u}} (c : (∐ Z) ⟶ T) [IsIso c] (M N : T.Modules) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent)
    (e : ∀ i, (modulePullbackPseudofunctor.{u}.map (Sigma.ι Z i ≫ c).op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.{u}.map (Sigma.ι Z i ≫ c).op.toLoc).toFunctor.obj N) :
    ∃ h : M ⟶ N, ∀ i,
      (modulePullbackPseudofunctor.{u}.map (Sigma.ι Z i ≫ c).op.toLoc).toFunctor.map h = e i :=
  exists_hom_of_sigmaIso c M N hM hN e

private theorem homExtOfSigmaIsoP {I : Type v} [Finite I] {Z : I → Scheme.{u}}
    {T : Scheme.{u}} (c : (∐ Z) ⟶ T) [IsIso c] (M N : T.Modules) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) (h k : M ⟶ N)
    (e : ∀ i, (modulePullbackPseudofunctor.{u}.map (Sigma.ι Z i ≫ c).op.toLoc).toFunctor.map h =
      (modulePullbackPseudofunctor.{u}.map (Sigma.ι Z i ≫ c).op.toLoc).toFunctor.map k) :
    h = k :=
  hom_ext_of_sigmaIso c M N hM hN h k e

private theorem sigmaIsoPullHomExists {I : Type v} [Finite I] {Z : I → Scheme.{u}}
    {T X₁ X₂ : Scheme.{u}} (c : (∐ Z) ⟶ T) [IsIso c]
    (M : X₁.Modules) (N : X₂.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
    (f₁ : T ⟶ X₁) (f₂ : T ⟶ X₂) (g₁ : ∀ i, Z i ⟶ X₁) (g₂ : ∀ i, Z i ⟶ X₂)
    (w₁ : ∀ i, (Sigma.ι Z i ≫ c) ≫ f₁ = g₁ i)
    (w₂ : ∀ i, (Sigma.ι Z i ≫ c) ≫ f₂ = g₂ i)
    (e : ∀ i, (modulePullbackPseudofunctor.{u}.map (g₁ i).op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.{u}.map (g₂ i).op.toLoc).toFunctor.obj N) :
    ∃ h : (modulePullbackPseudofunctor.{u}.map f₁.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.{u}.map f₂.op.toLoc).toFunctor.obj N, ∀ i,
      pullHom (F := modulePullbackPseudofunctor.{u}) h (Sigma.ι Z i ≫ c) (g₁ i) (g₂ i)
        (w₁ i) (w₂ i) = e i := by
  let α : ∀ i, _ ≅ _ := fun i ↦ Cat.Hom.toNatIso
    (modulePullbackPseudofunctor.{u}.mapComp' f₁.op.toLoc (Sigma.ι Z i ≫ c).op.toLoc
      (g₁ i).op.toLoc (by simpa using congrArg (fun t ↦ t.op.toLoc) (w₁ i)))
  let β : ∀ i, _ ≅ _ := fun i ↦ Cat.Hom.toNatIso
    (modulePullbackPseudofunctor.{u}.mapComp' f₂.op.toLoc (Sigma.ι Z i ≫ c).op.toLoc
      (g₂ i).op.toLoc (by simpa using congrArg (fun t ↦ t.op.toLoc) (w₂ i)))
  obtain ⟨h, hh⟩ := existsHomOfSigmaIsoP c
    ((modulePullbackPseudofunctor.{u}.map f₁.op.toLoc).toFunctor.obj M)
    ((modulePullbackPseudofunctor.{u}.map f₂.op.toLoc).toFunctor.obj N)
    (Stacks.Modules.isQuasicoherent_pullback f₁ M hM)
    (Stacks.Modules.isQuasicoherent_pullback f₂ N hN)
    (fun i ↦ (α i).inv.app M ≫ e i ≫ (β i).hom.app N)
  refine ⟨h, fun i ↦ ?_⟩
  dsimp only [pullHom]
  rw [hh]
  exact conjugateCancel ((α i).app M) ((β i).app N) (e i)

private theorem sigmaIsoPullHomExt {I : Type v} [Finite I] {Z : I → Scheme.{u}}
    {T X₁ X₂ : Scheme.{u}} (c : (∐ Z) ⟶ T) [IsIso c]
    (M : X₁.Modules) (N : X₂.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
    (f₁ : T ⟶ X₁) (f₂ : T ⟶ X₂) (g₁ : ∀ i, Z i ⟶ X₁) (g₂ : ∀ i, Z i ⟶ X₂)
    (w₁ : ∀ i, (Sigma.ι Z i ≫ c) ≫ f₁ = g₁ i)
    (w₂ : ∀ i, (Sigma.ι Z i ≫ c) ≫ f₂ = g₂ i)
    (h k : (modulePullbackPseudofunctor.{u}.map f₁.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.{u}.map f₂.op.toLoc).toFunctor.obj N)
    (e : ∀ i, pullHom (F := modulePullbackPseudofunctor.{u}) h (Sigma.ι Z i ≫ c) (g₁ i) (g₂ i)
        (w₁ i) (w₂ i) =
      pullHom (F := modulePullbackPseudofunctor.{u}) k (Sigma.ι Z i ≫ c) (g₁ i) (g₂ i)
        (w₁ i) (w₂ i)) : h = k := by
  refine homExtOfSigmaIsoP c
    ((modulePullbackPseudofunctor.{u}.map f₁.op.toLoc).toFunctor.obj M)
    ((modulePullbackPseudofunctor.{u}.map f₂.op.toLoc).toFunctor.obj N)
    (Stacks.Modules.isQuasicoherent_pullback f₁ M hM)
    (Stacks.Modules.isQuasicoherent_pullback f₂ N hN) h k fun i ↦ ?_
  exact (pullHomEqIff (F := modulePullbackPseudofunctor.{u}) h k (Sigma.ι Z i ≫ c)
    (g₁ i) (g₂ i) (w₁ i) (w₂ i)).1 (e i)

/-! ### The transition morphism attached to a Galois descent system

Everything below is stated at variable data: the chosen fibre products `sq` and `sq₃`, the
comparison morphisms `c` and `c₃` out of the coproducts, and the transition morphism `θ`. -/

section Transition

open GaloisDescentData

variable {G : Type v} [Group G] {X Y : Scheme.{u}} {f : X ⟶ Y}
  {a : Gᵐᵒᵖ →* Aut (Over.mk f)}

/-- The isomorphism `φ_σ` of a Galois descent system, read as a morphism from the inverse image
along the identity to the inverse image along `f_σ`. -/
def actionHom (A : GaloisDescentData G f a) (σ : G) :
    (modulePullbackPseudofunctor.{u}.map (𝟙 X).op.toLoc).toFunctor.obj A.module ⟶
      (modulePullbackPseudofunctor.{u}.map (twist G f a σ).op.toLoc).toFunctor.obj A.module :=
  (Scheme.Modules.pullbackId X).hom.app A.module ≫ (A.φ σ).hom

/-- `Stacks.Descent.actionHom A σ` is the inverse of `Scheme.Modules.pullbackId` followed by
`φ_σ`. -/
lemma actionHom_def (A : GaloisDescentData G f a) (σ : G) :
    actionHom A σ = (Scheme.Modules.pullbackId X).hom.app A.module ≫ (A.φ σ).hom := rfl

/-- `Stacks.Descent.actionHom A σ` is the forward morphism of the composite isomorphism of
`Scheme.Modules.pullbackId` and `φ_σ`. -/
lemma actionHom_eq_iso_hom (A : GaloisDescentData G f a) (σ : G) :
    actionHom A σ = (((Scheme.Modules.pullbackId X).app A.module) ≪≫ A.φ σ).hom := rfl

/-- `Stacks.Descent.actionHom A σ` is an isomorphism. -/
instance isIso_actionHom (A : GaloisDescentData G f a) (σ : G) : IsIso (actionHom A σ) := by
  rw [actionHom_eq_iso_hom]
  exact ((Scheme.Modules.pullbackId X).app A.module ≪≫ A.φ σ).isIso_hom

/-- **The Galois cocycle condition** for `Stacks.Descent.actionHom`: transporting `φ_τ` along
`f_σ` and composing with `φ_σ` gives `φ_(στ)`. -/
lemma actionHomCocycle (A : GaloisDescentData G f a) (σ τ : G) :
    actionHom A σ ≫ pullHom (F := modulePullbackPseudofunctor.{u}) (actionHom A τ)
        (twist G f a σ) (twist G f a σ) (twist G f a (σ * τ))
        (Category.comp_id _) (twist_mul G f a σ τ) = actionHom A (σ * τ) := by
  have hc : (A.φ (σ * τ)).hom = (A.φ σ).hom ≫
      (Scheme.Modules.pullback (twist G f a σ)).map (A.φ τ).hom ≫
      (Scheme.Modules.pullbackComp (twist G f a σ) (twist G f a τ)).hom.app A.module ≫
      (Scheme.Modules.pullbackCongr (twist_mul G f a σ τ)).hom.app A.module := by
    rw [A.cocycle σ τ]
    simp [GaloisDescentData.pullbackMulIso]
  have hn := pullHomNormalize (M := A.module) (N := A.module) (twist G f a τ)
    (twist G f a σ) (twist G f a (σ * τ)) (twist_mul G f a σ τ) (A.φ τ).hom
  simp only [actionHom_def]
  exact (congrArg (fun k ↦ ((Scheme.Modules.pullbackId X).hom.app A.module ≫
      (A.φ σ).hom) ≫ k) hn).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun k ↦ (Scheme.Modules.pullbackId X).hom.app A.module ≫ k) hc).symm)

variable [Finite G] (A : GaloisDescentData G f a) (sq : ChosenPullback f f)
  (θ : (modulePullbackPseudofunctor.{u}.map sq.p₁.op.toLoc).toFunctor.obj A.module ⟶
    (modulePullbackPseudofunctor.{u}.map sq.p₂.op.toLoc).toFunctor.obj A.module)
  (c : (∐ fun _ : G ↦ X) ⟶ sq.pullback)
  (hc₁ : ∀ σ : G, (Sigma.ι (fun _ : G ↦ X) σ ≫ c) ≫ sq.p₁ = 𝟙 X)
  (hc₂ : ∀ σ : G, (Sigma.ι (fun _ : G ↦ X) σ ≫ c) ≫ sq.p₂ = twist G f a σ)
  (hθ : ∀ σ : G, pullHom (F := modulePullbackPseudofunctor.{u}) θ
    (Sigma.ι (fun _ : G ↦ X) σ ≫ c) (𝟙 X) (twist G f a σ) (hc₁ σ) (hc₂ σ) = actionHom A σ)

include hc₁ hc₂ hθ

/-- **The cocycle identity of the transition morphism on the triple fibre product.**  If
`c₃ : ∐_{G × G} X ⟶ X ×_Y X ×_Y X` is an isomorphism whose summand indexed by `(σ, τ)` has legs
`𝟙`, `f_σ` and `f_(στ)`, and `θ` restricts to `Stacks.Descent.actionHom A σ` on the summand of
`c` indexed by `σ`, then `θ` satisfies the cocycle identity over the chosen triple fibre
product. -/
lemma transitionCocycle (sq₃ : ChosenPullback₃ sq sq sq)
    (c₃ : (∐ fun _ : G × G ↦ X) ⟶ sq₃.pullback) [IsIso c₃]
    (h₁ : ∀ p : G × G, (Sigma.ι (fun _ : G × G ↦ X) p ≫ c₃) ≫ sq₃.p₁ = 𝟙 X)
    (h₂ : ∀ p : G × G, (Sigma.ι (fun _ : G × G ↦ X) p ≫ c₃) ≫ sq₃.p₂ = twist G f a p.1)
    (h₃ : ∀ p : G × G,
      (Sigma.ι (fun _ : G × G ↦ X) p ≫ c₃) ≫ sq₃.p₃ = twist G f a (p.1 * p.2)) :
    pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₁₂ sq₃.p₁ sq₃.p₂
        sq₃.p₁₂_p₁ sq₃.p₁₂_p₂ ≫
      pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₂₃ sq₃.p₂ sq₃.p₃
        sq₃.p₂₃_p₂ sq₃.p₂₃_p₃ =
      pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₁₃ sq₃.p₁ sq₃.p₃
        sq₃.p₁₃_p₁ sq₃.p₁₃_p₃ := by
  refine sigmaIsoPullHomExt c₃ A.module A.module A.isQuasicoherent A.isQuasicoherent
    sq₃.p₁ sq₃.p₃ (fun _ ↦ 𝟙 X) (fun p ↦ twist G f a (p.1 * p.2)) h₁ h₃ _ _ fun p ↦ ?_
  obtain ⟨σ, τ⟩ := p
  set k := Sigma.ι (fun _ : G × G ↦ X) (σ, τ) ≫ c₃ with hkdef
  have k₁₂ : k ≫ sq₃.p₁₂ = Sigma.ι (fun _ : G ↦ X) σ ≫ c := by
    refine sq.hom_ext ?_ ?_
    · rw [Category.assoc, ChosenPullback₃.p₁₂_p₁, hkdef, h₁ (σ, τ), hc₁ σ]
    · rw [Category.assoc, ChosenPullback₃.p₁₂_p₂, hkdef, h₂ (σ, τ), hc₂ σ]
  have k₂₃ : k ≫ sq₃.p₂₃ = twist G f a σ ≫ Sigma.ι (fun _ : G ↦ X) τ ≫ c := by
    refine sq.hom_ext ?_ ?_
    · rw [Category.assoc, ChosenPullback₃.p₂₃_p₂, hkdef, h₂ (σ, τ), Category.assoc,
        hc₁ τ, Category.comp_id]
    · rw [Category.assoc, ChosenPullback₃.p₂₃_p₃, hkdef, h₃ (σ, τ), Category.assoc,
        hc₂ τ, twist_mul]
  have k₁₃ : k ≫ sq₃.p₁₃ = Sigma.ι (fun _ : G ↦ X) (σ * τ) ≫ c := by
    refine sq.hom_ext ?_ ?_
    · rw [Category.assoc, ChosenPullback₃.p₁₃_p₁, hkdef, h₁ (σ, τ), hc₁ (σ * τ)]
    · rw [Category.assoc, ChosenPullback₃.p₁₃_p₃, hkdef, h₃ (σ, τ), hc₂ (σ * τ)]
  have hsplit := pullHomComp (F := modulePullbackPseudofunctor.{u})
    (pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₁₂ sq₃.p₁ sq₃.p₂
      sq₃.p₁₂_p₁ sq₃.p₁₂_p₂)
    (pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₂₃ sq₃.p₂ sq₃.p₃
      sq₃.p₂₃_p₂ sq₃.p₂₃_p₃)
    k (𝟙 X) (twist G f a σ) (twist G f a (σ * τ)) (h₁ (σ, τ)) (h₂ (σ, τ)) (h₃ (σ, τ))
  have a₁ : pullHom (F := modulePullbackPseudofunctor.{u})
      (pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₁₂ sq₃.p₁ sq₃.p₂
        sq₃.p₁₂_p₁ sq₃.p₁₂_p₂) k (𝟙 X) (twist G f a σ) (h₁ (σ, τ)) (h₂ (σ, τ)) =
      actionHom A σ :=
    (pullHomPullHomOfComp θ _ k k₁₂ _ _ _ _ _ _ _ _ (hc₁ σ) (hc₂ σ)).trans (hθ σ)
  have a₃ : pullHom (F := modulePullbackPseudofunctor.{u})
      (pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₁₃ sq₃.p₁ sq₃.p₃
        sq₃.p₁₃_p₁ sq₃.p₁₃_p₃) k (𝟙 X) (twist G f a (σ * τ)) (h₁ (σ, τ)) (h₃ (σ, τ)) =
      actionHom A (σ * τ) :=
    (pullHomPullHomOfComp θ _ k k₁₃ _ _ _ _ _ _ _ _ (hc₁ (σ * τ)) (hc₂ (σ * τ))).trans
      (hθ (σ * τ))
  have a₂ : pullHom (F := modulePullbackPseudofunctor.{u})
      (pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₂₃ sq₃.p₂ sq₃.p₃
        sq₃.p₂₃_p₂ sq₃.p₂₃_p₃) k (twist G f a σ) (twist G f a (σ * τ))
        (h₂ (σ, τ)) (h₃ (σ, τ)) =
      pullHom (F := modulePullbackPseudofunctor.{u}) (actionHom A τ) (twist G f a σ)
        (twist G f a σ) (twist G f a (σ * τ)) (Category.comp_id _) (twist_mul G f a σ τ) :=
    (pullHomPullHomOfComp θ _ k k₂₃ _ _ _ _ _ _ _ _
      (by rw [Category.assoc, hc₁ τ, Category.comp_id])
      (by rw [Category.assoc, hc₂ τ, twist_mul])).trans
    ((pullHomPullHomOfComp θ (Sigma.ι (fun _ : G ↦ X) τ ≫ c) (twist G f a σ) rfl _ _ _ _ _ _
      _ _ _ _).symm.trans
      (pullHomCongr (F := modulePullbackPseudofunctor.{u}) (hθ τ) (twist G f a σ)
        (twist G f a σ) (twist G f a (σ * τ)) (Category.comp_id _) (twist_mul G f a σ τ)))
  exact (hsplit.trans ((compCongr a₁ a₂).trans (actionHomCocycle A σ τ))).trans a₃.symm

end Transition

/-! ### The quasi-coherent descent datum attached to a Galois descent system -/

section Datum

open GaloisDescentData Pseudofunctor.DescentData'

variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} {f : X ⟶ Y}
  {a : Gᵐᵒᵖ →* Aut (Over.mk f)} (A : GaloisDescentData G f a) (sq : ChosenPullback f f)
  (θ : (modulePullbackPseudofunctor.{u}.map sq.p₁.op.toLoc).toFunctor.obj A.module ⟶
    (modulePullbackPseudofunctor.{u}.map sq.p₂.op.toLoc).toFunctor.obj A.module)
  (c : (∐ fun _ : G ↦ X) ⟶ sq.pullback)
  (hc₁ : ∀ σ : G, (Sigma.ι (fun _ : G ↦ X) σ ≫ c) ≫ sq.p₁ = 𝟙 X)
  (hc₂ : ∀ σ : G, (Sigma.ι (fun _ : G ↦ X) σ ≫ c) ≫ sq.p₂ = twist G f a σ)
  (hθ : ∀ σ : G, pullHom (F := modulePullbackPseudofunctor.{u}) θ
    (Sigma.ι (fun _ : G ↦ X) σ ≫ c) (𝟙 X) (twist G f a σ) (hc₁ σ) (hc₂ σ) = actionHom A σ)

include hc₁ hc₂ hθ

/-- The transition morphism, read through `Pseudofunctor.DescentData'.pullHom'` between the
inverse images along the identity and along `f_σ`. -/
lemma transition_pullHom' (σ : G) :
    pullHom' (F := modulePullbackPseudofunctor.{u}) (f := galoisFamily f)
        (sq := fun _ _ ↦ sq) (obj := fun _ ↦ A.module) (obj' := fun _ ↦ A.module)
        (fun _ _ ↦ θ) f (i₁ := .unit) (i₂ := .unit) (𝟙 X) (twist G f a σ)
        (Category.id_comp _) (twist_comp G f a σ) = actionHom A σ :=
  (pullHom'_eq_pullHom (F := modulePullbackPseudofunctor.{u}) (f := galoisFamily f)
    (sq := fun _ _ ↦ sq) (obj := fun _ ↦ A.module) (obj' := fun _ ↦ A.module)
    (hom := fun _ _ ↦ θ) (i₁ := .unit) (i₂ := .unit) f (𝟙 X) (twist G f a σ)
    (Sigma.ι (fun _ : G ↦ X) σ ≫ c) (Category.id_comp _) (twist_comp G f a σ)
    (hc₁ σ) (hc₂ σ)).trans (hθ σ)

end Datum

/-! ### The legs of the Galois cover comparison and of its triple analogue -/

section Shape

open GaloisDescentData

variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (a : Gᵐᵒᵖ →* Aut (Over.mk f)) [IsIso (galoisCoverComparison f a)]

omit [IsIso (galoisCoverComparison f a)] in
/-- The first leg of the Galois cover comparison on the summand indexed by `σ`, with the
summand inclusion absorbed into the composite. -/
theorem galoisCoverComparison_ι_comp_fst (σ : G) :
    (Sigma.ι (fun _ : G ↦ X) σ ≫ galoisCoverComparison f a) ≫ pullback.fst f f = 𝟙 X := by
  rw [Category.assoc]
  exact galoisCoverComparison_ι_fst f a σ

omit [IsIso (galoisCoverComparison f a)] in
/-- The second leg of the Galois cover comparison on the summand indexed by `σ`, with the
summand inclusion absorbed into the composite. -/
theorem galoisCoverComparison_ι_comp_snd (σ : G) :
    (Sigma.ι (fun _ : G ↦ X) σ ≫ galoisCoverComparison f a) ≫ pullback.snd f f =
      twist G f a σ := by
  rw [Category.assoc]
  exact galoisCoverComparison_ι_snd f a σ

/-- `Stacks.Descent.galoisTripleComparison` with its target spelled as the iterated pullback
`(X ×_Y X) ×_X (X ×_Y X)` instead of as `(galoisChosenPullback₃ f).pullback`. -/
private def galoisTripleComparisonPullback :
    (∐ fun _ : G × G ↦ X) ⟶ pullback (pullback.snd f f) (pullback.fst f f) :=
  galoisTripleComparison f a

/-- The triple comparison, written out as the composite of the three isomorphisms it is built
from, in the spelling of `Stacks.Descent.galoisTripleComparisonPullback`. -/
private lemma galoisTripleComparisonPullback_eq :
    galoisTripleComparisonPullback f a =
      (Limits.Sigma.map fun p : G × G ↦ galoisTripleFiberMap f a p.1 p.2) ≫
        (Sigma.desc fun p : G × G ↦ pullback.map (twist G f a p.1) (𝟙 X)
          (galoisTripleFirstMap f a) (galoisTripleSecondMap f a)
          (Sigma.ι (fun _ : G ↦ X) p.1) (Sigma.ι (fun _ : G ↦ X) p.2) (𝟙 X)
          (by simp [galoisTripleFirstMap]) (by simp [galoisTripleSecondMap])) ≫
        pullback.map (galoisTripleFirstMap f a) (galoisTripleSecondMap f a)
          (pullback.snd f f) (pullback.fst f f)
          (galoisCoverComparison f a) (galoisCoverComparison f a) (𝟙 X)
          (by rw [galoisCoverComparison_snd_eq_firstMap]; simp)
          (by rw [galoisCoverComparison_fst_eq_secondMap]; simp) :=
  rfl

/-- The first projection of the chosen triple fibre product, read on the summand indexed by
`(σ, τ)`: it is the summand `σ` of the Galois cover comparison. -/
private lemma galoisTripleComparisonPullback_ι_fst (σ τ : G) :
    (Sigma.ι (fun _ : G × G ↦ X) (σ, τ) ≫ galoisTripleComparisonPullback f a) ≫
        pullback.fst (pullback.snd f f) (pullback.fst f f) =
      Sigma.ι (fun _ : G ↦ X) σ ≫ galoisCoverComparison f a := by
  rw [galoisTripleComparisonPullback_eq]
  simp [galoisTripleFiberMap, pullback.map]

/-- The second projection of the chosen triple fibre product, read on the summand indexed by
`(σ, τ)`: it is `f_σ` followed by the summand `τ` of the Galois cover comparison. -/
private lemma galoisTripleComparisonPullback_ι_snd (σ τ : G) :
    (Sigma.ι (fun _ : G × G ↦ X) (σ, τ) ≫ galoisTripleComparisonPullback f a) ≫
        pullback.snd (pullback.snd f f) (pullback.fst f f) =
      twist G f a σ ≫ Sigma.ι (fun _ : G ↦ X) τ ≫ galoisCoverComparison f a := by
  rw [galoisTripleComparisonPullback_eq]
  simp [galoisTripleFiberMap, pullback.map]

/-- **The first leg of the triple comparison.**  On the summand indexed by `(σ, τ)` the
projection of `X ×_Y X ×_Y X` to the first factor is the identity. -/
theorem galoisTripleComparison_ι_p₁ (σ τ : G) :
    (Sigma.ι (fun _ : G × G ↦ X) (σ, τ) ≫ galoisTripleComparison f a) ≫
      (galoisChosenPullback₃ f).p₁ = 𝟙 X := by
  change (Sigma.ι (fun _ : G × G ↦ X) (σ, τ) ≫ galoisTripleComparisonPullback f a) ≫
    pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f = 𝟙 X
  rw [← Category.assoc, galoisTripleComparisonPullback_ι_fst,
    galoisCoverComparison_ι_comp_fst]

/-- **The second leg of the triple comparison.**  On the summand indexed by `(σ, τ)` the
projection of `X ×_Y X ×_Y X` to the second factor is `f_σ`. -/
theorem galoisTripleComparison_ι_p₂ (σ τ : G) :
    (Sigma.ι (fun _ : G × G ↦ X) (σ, τ) ≫ galoisTripleComparison f a) ≫
      (galoisChosenPullback₃ f).p₂ = twist G f a σ := by
  change (Sigma.ι (fun _ : G × G ↦ X) (σ, τ) ≫ galoisTripleComparisonPullback f a) ≫
    pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f = twist G f a σ
  rw [← Category.assoc, galoisTripleComparisonPullback_ι_fst,
    galoisCoverComparison_ι_comp_snd]

/-- **The third leg of the triple comparison.**  On the summand indexed by `(σ, τ)` the
projection of `X ×_Y X ×_Y X` to the third factor is `f_(στ)`. -/
theorem galoisTripleComparison_ι_p₃ (σ τ : G) :
    (Sigma.ι (fun _ : G × G ↦ X) (σ, τ) ≫ galoisTripleComparison f a) ≫
      (galoisChosenPullback₃ f).p₃ = twist G f a (σ * τ) := by
  change (Sigma.ι (fun _ : G × G ↦ X) (σ, τ) ≫ galoisTripleComparisonPullback f a) ≫
    pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f =
      twist G f a (σ * τ)
  rw [← Category.assoc, galoisTripleComparisonPullback_ι_snd, Category.assoc,
    galoisCoverComparison_ι_comp_snd, twist_mul]

end Shape

/-! ### The descent datum attached to a Galois descent system -/

section DirectDatum

open GaloisDescentData

variable {G : Type v} [Group G] {X Y : Scheme.{u}} {f : X ⟶ Y}
  {a : Gᵐᵒᵖ →* Aut (Over.mk f)}

/-- The isomorphism `φ_σ` carried by a descent datum for the one-element family `{f}`, written
out through `CategoryTheory.Pseudofunctor.DescentData.hom`. -/
private lemma galoisIso_hom_eq
    (D : modulePullbackPseudofunctor.{u}.DescentData (galoisFamily f)) (σ : G) :
    (galoisIso (a := a) D σ).hom =
      (Scheme.Modules.pullbackId X).inv.app (D.obj .unit) ≫
        D.hom (i₁ := .unit) (i₂ := .unit) f (𝟙 X) (twist G f a σ)
          (Category.id_comp f) (twist_comp G f a σ) := rfl

/-- Two Galois descent systems with the same module and heterogeneously equal action-indexed
isomorphisms are equal. -/
private lemma galoisObjExt {A B : GaloisDescentData G f a} (hm : A.module = B.module)
    (h : ∀ σ : G, A.φ σ ≍ B.φ σ) : A = B := by
  obtain ⟨m₁, q₁, φ₁, c₁⟩ := A
  obtain ⟨m₂, q₂, φ₂, c₂⟩ := B
  change m₁ = m₂ at hm
  subst hm
  exact Obj.ext rfl (heq_of_eq (funext fun σ ↦ eq_of_heq (h σ)))

/-- `Stacks.Descent.galoisDescentFunctor_obj_φ` as a heterogeneous equality. -/
private lemma galoisDescentFunctor_obj_φ_heq
    (D : QuasicoherentDescentData (galoisFamily f)) (σ : G) :
    ((galoisDescentFunctor G f a).obj D).φ σ ≍ galoisIso (a := a) D.obj σ :=
  heq_of_eq (galoisDescentFunctor_obj_φ D σ)

/-- For functors `P` and `Q`, an isomorphism `e₁` and `h ≫ u₂ = e₁.hom ≫ Q.map h`, if
`(e₁.hom ≫ d₁) ≫ P.map h = h ≫ u₂ ≫ d₂` then `Q.map h ≫ d₂ = d₁ ≫ P.map h`. -/
private lemma galoisRearrangeCommInv {C : Type*} [Category C] (P Q : C ⥤ C) {M₁ M₂ : C}
    (h : M₁ ⟶ M₂) (e₁ : M₁ ≅ Q.obj M₁) (u₂ : M₂ ⟶ Q.obj M₂)
    (d₁ : Q.obj M₁ ⟶ P.obj M₁) (d₂ : Q.obj M₂ ⟶ P.obj M₂)
    (hnat : h ≫ u₂ = e₁.hom ≫ Q.map h)
    (hcomm : (e₁.hom ≫ d₁) ≫ P.map h = h ≫ u₂ ≫ d₂) :
    Q.map h ≫ d₂ = d₁ ≫ P.map h := by
  rw [← cancel_epi e₁.hom, ← Category.assoc e₁.hom (Q.map h) d₂, ← hnat,
    ← Category.assoc e₁.hom d₁ (P.map h), hcomm, Category.assoc]

variable (A : GaloisDescentData G f a) (sq : ChosenPullback f f)
  (θ : (modulePullbackPseudofunctor.{u}.map sq.p₁.op.toLoc).toFunctor.obj A.module ⟶
    (modulePullbackPseudofunctor.{u}.map sq.p₂.op.toLoc).toFunctor.obj A.module)

/-- The transition morphism of a Galois descent system over an arbitrary pair of legs: the
morphism `θ` over the chosen fibre square, pulled back along the induced lift. -/
private def galoisTransition {W : Scheme.{u}} (q : W ⟶ Y) (g₁ g₂ : W ⟶ X)
    (hg₁ : g₁ ≫ f = q) (hg₂ : g₂ ≫ f = q) :
    (modulePullbackPseudofunctor.{u}.map g₁.op.toLoc).toFunctor.obj A.module ⟶
      (modulePullbackPseudofunctor.{u}.map g₂.op.toLoc).toFunctor.obj A.module :=
  pullHom (F := modulePullbackPseudofunctor.{u}) θ
    (sq.isPullback.lift g₁ g₂ (by rw [hg₁, hg₂])) g₁ g₂
    (sq.isPullback.lift_fst g₁ g₂ (by rw [hg₁, hg₂]))
    (sq.isPullback.lift_snd g₁ g₂ (by rw [hg₁, hg₂]))

/-- The transition morphism is computed by any lift of the pair of legs to the chosen fibre
square. -/
private lemma galoisTransition_eq {W : Scheme.{u}} (q : W ⟶ Y) (g₁ g₂ : W ⟶ X)
    (hg₁ : g₁ ≫ f = q) (hg₂ : g₂ ≫ f = q) (p : W ⟶ sq.pullback)
    (hp₁ : p ≫ sq.p₁ = g₁) (hp₂ : p ≫ sq.p₂ = g₂) :
    galoisTransition A sq θ q g₁ g₂ hg₁ hg₂ =
      pullHom (F := modulePullbackPseudofunctor.{u}) θ p g₁ g₂ hp₁ hp₂ :=
  pullHomCongrMap (F := modulePullbackPseudofunctor.{u}) θ
    (sq.hom_ext
      ((sq.isPullback.lift_fst g₁ g₂ (by rw [hg₁, hg₂])).trans hp₁.symm)
      ((sq.isPullback.lift_snd g₁ g₂ (by rw [hg₁, hg₂])).trans hp₂.symm))
    g₁ g₂ (sq.isPullback.lift_fst g₁ g₂ (by rw [hg₁, hg₂]))
    (sq.isPullback.lift_snd g₁ g₂ (by rw [hg₁, hg₂])) hp₁ hp₂

/-- Pulling the transition morphism back along a morphism of bases. -/
private lemma galoisTransition_pullHom {W' W : Scheme.{u}} (g : W' ⟶ W) (q : W ⟶ Y)
    (q' : W' ⟶ Y) (g₁ g₂ : W ⟶ X) (hg₁ : g₁ ≫ f = q) (hg₂ : g₂ ≫ f = q)
    (gg₁ gg₂ : W' ⟶ X) (hgg₁ : g ≫ g₁ = gg₁) (hgg₂ : g ≫ g₂ = gg₂)
    (hq₁ : gg₁ ≫ f = q') (hq₂ : gg₂ ≫ f = q') :
    pullHom (F := modulePullbackPseudofunctor.{u})
        (galoisTransition A sq θ q g₁ g₂ hg₁ hg₂) g gg₁ gg₂ hgg₁ hgg₂ =
      galoisTransition A sq θ q' gg₁ gg₂ hq₁ hq₂ := by
  have hp₁ : sq.isPullback.lift g₁ g₂ (by rw [hg₁, hg₂]) ≫ sq.p₁ = g₁ :=
    sq.isPullback.lift_fst g₁ g₂ (by rw [hg₁, hg₂])
  have hp₂ : sq.isPullback.lift g₁ g₂ (by rw [hg₁, hg₂]) ≫ sq.p₂ = g₂ :=
    sq.isPullback.lift_snd g₁ g₂ (by rw [hg₁, hg₂])
  have hgp₁ : (g ≫ sq.isPullback.lift g₁ g₂ (by rw [hg₁, hg₂])) ≫ sq.p₁ = gg₁ := by
    rw [Category.assoc, hp₁, hgg₁]
  have hgp₂ : (g ≫ sq.isPullback.lift g₁ g₂ (by rw [hg₁, hg₂])) ≫ sq.p₂ = gg₂ := by
    rw [Category.assoc, hp₂, hgg₂]
  rw [galoisTransition_eq A sq θ q' gg₁ gg₂ hq₁ hq₂ _ hgp₁ hgp₂,
    galoisTransition_eq A sq θ q g₁ g₂ hg₁ hg₂ _ hp₁ hp₂]
  exact pullHom_pullHom (F := modulePullbackPseudofunctor.{u}) θ
    (sq.isPullback.lift g₁ g₂ (by rw [hg₁, hg₂])) g₁ g₂ g gg₁ gg₂ hp₁ hp₂ hgg₁ hgg₂

/-- The transition morphism over a leg `ψ` of a chosen triple fibre product, for any lift `φ`
of the pair of legs to the triple fibre product. -/
private lemma galoisTransitionLeg {V W : Scheme.{u}} (ψ : V ⟶ sq.pullback) (s₁ s₂ : V ⟶ X)
    (w₁ : ψ ≫ sq.p₁ = s₁) (w₂ : ψ ≫ sq.p₂ = s₂) (q : W ⟶ Y) (g₁ g₂ : W ⟶ X)
    (hq₁ : g₁ ≫ f = q) (hq₂ : g₂ ≫ f = q) (φ : W ⟶ V) (hφ₁ : φ ≫ s₁ = g₁)
    (hφ₂ : φ ≫ s₂ = g₂) :
    galoisTransition A sq θ q g₁ g₂ hq₁ hq₂ =
      pullHom (F := modulePullbackPseudofunctor.{u})
        (pullHom (F := modulePullbackPseudofunctor.{u}) θ ψ s₁ s₂ w₁ w₂) φ g₁ g₂ hφ₁ hφ₂ :=
  (galoisTransition_eq A sq θ q g₁ g₂ hq₁ hq₂ (φ ≫ ψ)
      (by rw [Category.assoc, w₁, hφ₁]) (by rw [Category.assoc, w₂, hφ₂])).trans
    (pullHom_pullHom (F := modulePullbackPseudofunctor.{u}) θ ψ s₁ s₂ φ g₁ g₂ w₁ w₂ hφ₁ hφ₂).symm

end DirectDatum

section DirectDatumAssembly

open GaloisDescentData

variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} {f : X ⟶ Y}
  {a : Gᵐᵒᵖ →* Aut (Over.mk f)} (A : GaloisDescentData G f a) (sq : ChosenPullback f f)
  (θ : (modulePullbackPseudofunctor.{u}.map sq.p₁.op.toLoc).toFunctor.obj A.module ⟶
    (modulePullbackPseudofunctor.{u}.map sq.p₂.op.toLoc).toFunctor.obj A.module)
  (c : (∐ fun _ : G ↦ X) ⟶ sq.pullback)
  (hc₁ : ∀ σ : G, (Sigma.ι (fun _ : G ↦ X) σ ≫ c) ≫ sq.p₁ = 𝟙 X)
  (hc₂ : ∀ σ : G, (Sigma.ι (fun _ : G ↦ X) σ ≫ c) ≫ sq.p₂ = twist G f a σ)
  (hθ : ∀ σ : G, pullHom (F := modulePullbackPseudofunctor.{u}) θ
    (Sigma.ι (fun _ : G ↦ X) σ ≫ c) (𝟙 X) (twist G f a σ) (hc₁ σ) (hc₂ σ) = actionHom A σ)
  (sq₃ : ChosenPullback₃ sq sq sq)
  (c₃ : (∐ fun _ : G × G ↦ X) ⟶ sq₃.pullback) [IsIso c₃]
  (h₁ : ∀ p : G × G, (Sigma.ι (fun _ : G × G ↦ X) p ≫ c₃) ≫ sq₃.p₁ = 𝟙 X)
  (h₂ : ∀ p : G × G, (Sigma.ι (fun _ : G × G ↦ X) p ≫ c₃) ≫ sq₃.p₂ = twist G f a p.1)
  (h₃ : ∀ p : G × G, (Sigma.ι (fun _ : G × G ↦ X) p ≫ c₃) ≫ sq₃.p₃ = twist G f a (p.1 * p.2))

include hc₁ hc₂ hθ

/-- The transition morphism along the identity of `X` and `f_σ` is the action of `σ`. -/
private lemma galoisTransition_actionHom (σ : G) :
    galoisTransition A sq θ f (𝟙 X) (twist G f a σ) (Category.id_comp f)
        (twist_comp G f a σ) = actionHom A σ :=
  (galoisTransition_eq A sq θ f (𝟙 X) (twist G f a σ) (Category.id_comp f)
    (twist_comp G f a σ) (Sigma.ι (fun _ : G ↦ X) σ ≫ c) (hc₁ σ) (hc₂ σ)).trans (hθ σ)

include h₁ h₂ h₃

/-- **The cocycle identity of the transition morphism over an arbitrary base.** -/
private lemma galoisTransition_comp {W : Scheme.{u}} (q : W ⟶ Y) (g₁ g₂ g₃ : W ⟶ X)
    (hg₁ : g₁ ≫ f = q) (hg₂ : g₂ ≫ f = q) (hg₃ : g₃ ≫ f = q) :
    galoisTransition A sq θ q g₁ g₂ hg₁ hg₂ ≫ galoisTransition A sq θ q g₂ g₃ hg₂ hg₃ =
      galoisTransition A sq θ q g₁ g₃ hg₁ hg₃ := by
  obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ := sq₃.exists_lift g₁ g₂ g₃ q hg₁ hg₂ hg₃
  exact (compCongr
        (galoisTransitionLeg A sq θ sq₃.p₁₂ _ _ sq₃.p₁₂_p₁ sq₃.p₁₂_p₂ q g₁ g₂ hg₁ hg₂ φ hφ₁ hφ₂)
        (galoisTransitionLeg A sq θ sq₃.p₂₃ _ _ sq₃.p₂₃_p₂ sq₃.p₂₃_p₃ q g₂ g₃ hg₂ hg₃ φ hφ₂
          hφ₃)).trans
    (((pullHomComp (F := modulePullbackPseudofunctor.{u})
          (pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₁₂ sq₃.p₁ sq₃.p₂
            sq₃.p₁₂_p₁ sq₃.p₁₂_p₂)
          (pullHom (F := modulePullbackPseudofunctor.{u}) θ sq₃.p₂₃ sq₃.p₂ sq₃.p₃
            sq₃.p₂₃_p₂ sq₃.p₂₃_p₃) φ g₁ g₂ g₃ hφ₁ hφ₂ hφ₃).symm.trans
        (pullHomCongr (F := modulePullbackPseudofunctor.{u})
          (transitionCocycle A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃) φ g₁ g₃ hφ₁ hφ₃)).trans
      (galoisTransitionLeg A sq θ sq₃.p₁₃ _ _ sq₃.p₁₃_p₁ sq₃.p₁₃_p₃ q g₁ g₃ hg₁ hg₃ φ hφ₁
        hφ₃).symm)

/-- The transition morphism over the diagonal of the chosen fibre square is the identity. -/
private lemma galoisTransition_diag (p₀ : X ⟶ sq.pullback) (w₁ : p₀ ≫ sq.p₁ = 𝟙 X)
    (w₂ : p₀ ≫ sq.p₂ = 𝟙 X) :
    pullHom (F := modulePullbackPseudofunctor.{u}) θ p₀ (𝟙 X) (𝟙 X) w₁ w₂ = 𝟙 _ := by
  have hone := galoisTransition_comp A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃ f (𝟙 X) (𝟙 X)
    (twist G f a 1) (Category.id_comp f) (Category.id_comp f) (twist_comp G f a 1)
  have hact := galoisTransition_actionHom A sq θ c hc₁ hc₂ hθ 1
  have hp := galoisTransition_eq A sq θ f (𝟙 X) (𝟙 X) (Category.id_comp f)
    (Category.id_comp f) p₀ w₁ w₂
  refine (cancel_mono (actionHom A 1)).1 ?_
  exact ((compCongr hp.symm hact.symm).trans (hone.trans hact)).trans
    (Category.id_comp (actionHom A 1)).symm

/-- **The transition morphism is the identity on the diagonal.** -/
private lemma galoisTransition_self {W : Scheme.{u}} (q : W ⟶ Y) (g : W ⟶ X)
    (hg : g ≫ f = q) : galoisTransition A sq θ q g g hg hg = 𝟙 _ := by
  have w₁ : sq.isPullback.lift (𝟙 X) (𝟙 X) rfl ≫ sq.p₁ = 𝟙 X :=
    sq.isPullback.lift_fst (𝟙 X) (𝟙 X) rfl
  have w₂ : sq.isPullback.lift (𝟙 X) (𝟙 X) rfl ≫ sq.p₂ = 𝟙 X :=
    sq.isPullback.lift_snd (𝟙 X) (𝟙 X) rfl
  have hgw₁ : (g ≫ sq.isPullback.lift (𝟙 X) (𝟙 X) rfl) ≫ sq.p₁ = g := by
    rw [Category.assoc, w₁, Category.comp_id]
  have hgw₂ : (g ≫ sq.isPullback.lift (𝟙 X) (𝟙 X) rfl) ≫ sq.p₂ = g := by
    rw [Category.assoc, w₂, Category.comp_id]
  have hmap := pullHomMap (F := modulePullbackPseudofunctor.{u}) (𝟙 A.module) (𝟙 X) g g
    (Category.comp_id g)
  have hone : pullHom (F := modulePullbackPseudofunctor.{u})
      (𝟙 ((modulePullbackPseudofunctor.{u}.map (𝟙 X).op.toLoc).toFunctor.obj A.module))
      g g g (Category.comp_id g) (Category.comp_id g) = 𝟙 _ :=
    (pullHomCongr (F := modulePullbackPseudofunctor.{u})
      (CategoryTheory.Functor.map_id (modulePullbackPseudofunctor.{u}.map (𝟙 X).op.toLoc).toFunctor
        A.module) g g g (Category.comp_id g) (Category.comp_id g)).symm.trans
      (hmap.trans (CategoryTheory.Functor.map_id
        (modulePullbackPseudofunctor.{u}.map g.op.toLoc).toFunctor A.module))
  exact (galoisTransition_eq A sq θ q g g hg hg _ hgw₁ hgw₂).trans
    ((pullHom_pullHom (F := modulePullbackPseudofunctor.{u}) θ
        (sq.isPullback.lift (𝟙 X) (𝟙 X) rfl) (𝟙 X) (𝟙 X) g g g w₁ w₂
        (Category.comp_id g) (Category.comp_id g)).symm.trans
      ((pullHomCongr (F := modulePullbackPseudofunctor.{u})
          (galoisTransition_diag A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃ _ w₁ w₂)
          g g g (Category.comp_id g) (Category.comp_id g)).trans hone))

/-- **The quasi-coherent descent datum attached to a Galois descent system.** -/
private def galoisDescentDatum :
    modulePullbackPseudofunctor.{u}.DescentData (galoisFamily f) where
  obj _ := A.module
  hom _ q _ _ g₁ g₂ hg₁ hg₂ := galoisTransition A sq θ q g₁ g₂ hg₁ hg₂
  pullHom_hom _ _ g q q' hq _ _ g₁ g₂ hg₁ hg₂ gg₁ gg₂ hgg₁ hgg₂ :=
    galoisTransition_pullHom A sq θ g q q' g₁ g₂ hg₁ hg₂ gg₁ gg₂ hgg₁ hgg₂
      (by rw [← hgg₁, Category.assoc, hg₁, hq]) (by rw [← hgg₂, Category.assoc, hg₂, hq])
  hom_self _ q _ g hg := galoisTransition_self A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃ q g hg
  hom_comp _ q _ _ _ g₁ g₂ g₃ hg₁ hg₂ hg₃ :=
    galoisTransition_comp A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃ q g₁ g₂ g₃ hg₁ hg₂ hg₃

private lemma galoisIso_galoisDescentDatum (σ : G) :
    galoisIso (a := a) (galoisDescentDatum A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃) σ = A.φ σ := by
  apply Iso.ext
  rw [galoisIso_hom_eq]
  change (Scheme.Modules.pullbackId X).inv.app A.module ≫
      galoisTransition A sq θ f (𝟙 X) (twist G f a σ) (Category.id_comp f)
        (twist_comp G f a σ) = (A.φ σ).hom
  rw [galoisTransition_actionHom A sq θ c hc₁ hc₂ hθ σ, actionHom_def]
  exact Iso.inv_hom_id_app_assoc (Scheme.Modules.pullbackId X) A.module (A.φ σ).hom

/-- The descent datum of `θ` as an object of the quasi-coherent descent data of `{f}`: its
only component is the module of `A`, which is quasi-coherent. -/
private def galoisQcohDatum : QuasicoherentDescentData (galoisFamily f) :=
  ⟨galoisDescentDatum A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃, fun _ ↦ A.isQuasicoherent⟩

/-- The module underlying the image of the descent datum of `θ` is the module of `A`. -/
private lemma galoisDescentFunctor_obj_galoisQcohDatum_module :
    ((galoisDescentFunctor G f a).obj
      (galoisQcohDatum A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃)).module = A.module :=
  galoisDescentFunctor_obj_module (G := G) _

/-- The image of the descent datum of `θ` carries the action-indexed isomorphisms of `A`. -/
private lemma galoisDescentFunctor_obj_galoisQcohDatum_φ (σ : G) :
    ((galoisDescentFunctor G f a).obj
      (galoisQcohDatum A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃)).φ σ ≍ A.φ σ :=
  (galoisDescentFunctor_obj_φ_heq (G := G)
      (galoisQcohDatum A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃) σ).trans
    (heq_of_eq (galoisIso_galoisDescentDatum A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃ σ))

/-- **The image of the descent datum of `θ` is the Galois descent system it was built from.** -/
private lemma galoisDescentFunctor_obj_galoisQcohDatum :
    (galoisDescentFunctor G f a).obj
      (galoisQcohDatum A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃) = A :=
  galoisObjExt
    (galoisDescentFunctor_obj_galoisQcohDatum_module A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃)
    (galoisDescentFunctor_obj_galoisQcohDatum_φ A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃)

/-- **A Galois descent system is the image of a quasi-coherent descent datum.** -/
private theorem essImage_galoisDescentDatum :
    (galoisDescentFunctor G f a).essImage A :=
  galoisDescentFunctor_obj_galoisQcohDatum A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃ ▸
    Functor.obj_mem_essImage (galoisDescentFunctor G f a)
      (galoisQcohDatum A sq θ c hc₁ hc₂ hθ sq₃ c₃ h₁ h₂ h₃)

end DirectDatumAssembly

/-! ### Fullness of the comparison functor -/

section Fullness

open GaloisDescentData

variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} {f : X ⟶ Y}
  {a : Gᵐᵒᵖ →* Aut (Over.mk f)} (sq : ChosenPullback f f)
  (c : (∐ fun _ : G ↦ X) ⟶ sq.pullback)
  (hc₁ : ∀ σ : G, (Sigma.ι (fun _ : G ↦ X) σ ≫ c) ≫ sq.p₁ = 𝟙 X)
  (hc₂ : ∀ σ : G, (Sigma.ι (fun _ : G ↦ X) σ ≫ c) ≫ sq.p₂ = twist G f a σ)

include hc₁ hc₂

omit hc₁ hc₂ in
/-- The compatibility over the chosen fibre square, pulled back along a lift `p`, is the
compatibility over the base `q` of the lifted legs `g₁` and `g₂`. -/
private lemma galoisCommPullHomIff
    {D₁ D₂ : modulePullbackPseudofunctor.{u}.DescentData (galoisFamily f)}
    (h : D₁.obj .unit ⟶ D₂.obj .unit)
    {W : Scheme.{u}} (p : W ⟶ sq.pullback) (g₁ g₂ : W ⟶ X)
    (hp₁ : p ≫ sq.p₁ = g₁) (hp₂ : p ≫ sq.p₂ = g₂) (q : W ⟶ Y)
    (hg₁ : g₁ ≫ f = q) (hg₂ : g₂ ≫ f = q) :
    pullHom (F := modulePullbackPseudofunctor.{u})
        ((modulePullbackPseudofunctor.{u}.map sq.p₁.op.toLoc).toFunctor.map h ≫
          D₂.hom (i₁ := .unit) (i₂ := .unit) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂) p g₁ g₂ hp₁ hp₂ =
      pullHom (F := modulePullbackPseudofunctor.{u})
        (D₁.hom (i₁ := .unit) (i₂ := .unit) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ ≫
          (modulePullbackPseudofunctor.{u}.map sq.p₂.op.toLoc).toFunctor.map h) p g₁ g₂ hp₁ hp₂ ↔
    (modulePullbackPseudofunctor.{u}.map g₁.op.toLoc).toFunctor.map h ≫
        D₂.hom (i₁ := .unit) (i₂ := .unit) q g₁ g₂ hg₁ hg₂ =
      D₁.hom (i₁ := .unit) (i₂ := .unit) q g₁ g₂ hg₁ hg₂ ≫
        (modulePullbackPseudofunctor.{u}.map g₂.op.toLoc).toFunctor.map h := by
  have hpq : p ≫ sq.p = q := by rw [← sq.hp₁, ← Category.assoc, hp₁, hg₁]
  rw [pullHomComp (F := modulePullbackPseudofunctor.{u}) _ _ p g₁ g₁ g₂ hp₁ hp₁ hp₂,
    pullHomComp (F := modulePullbackPseudofunctor.{u}) _ _ p g₁ g₂ g₂ hp₁ hp₂ hp₂,
    pullHomMap (F := modulePullbackPseudofunctor.{u}) h sq.p₁ p g₁ hp₁,
    pullHomMap (F := modulePullbackPseudofunctor.{u}) h sq.p₂ p g₂ hp₂,
    D₂.pullHom_hom p sq.p q hpq (i₁ := .unit) (i₂ := .unit) sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ g₁ g₂
      hp₁ hp₂,
    D₁.pullHom_hom p sq.p q hpq (i₁ := .unit) (i₂ := .unit) sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ g₁ g₂
      hp₁ hp₂]

/-- The compatibility of a morphism of Galois descent systems with the transition morphisms
over the chosen fibre square, read on the summand indexed by `σ`. -/
private lemma galoisCommSummand
    {D₁ D₂ : modulePullbackPseudofunctor.{u}.DescentData (galoisFamily f)}
    (h : D₁.obj .unit ⟶ D₂.obj .unit)
    (hcomm : ∀ σ : G, (galoisIso (a := a) D₁ σ).hom ≫
        (Scheme.Modules.pullback (twist G f a σ)).map h = h ≫ (galoisIso (a := a) D₂ σ).hom)
    (σ : G) :
    pullHom (F := modulePullbackPseudofunctor.{u})
        ((modulePullbackPseudofunctor.{u}.map sq.p₁.op.toLoc).toFunctor.map h ≫
          D₂.hom (i₁ := .unit) (i₂ := .unit) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂)
        (Sigma.ι (fun _ : G ↦ X) σ ≫ c) (𝟙 X) (twist G f a σ) (hc₁ σ) (hc₂ σ) =
      pullHom (F := modulePullbackPseudofunctor.{u})
        (D₁.hom (i₁ := .unit) (i₂ := .unit) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ ≫
          (modulePullbackPseudofunctor.{u}.map sq.p₂.op.toLoc).toFunctor.map h)
        (Sigma.ι (fun _ : G ↦ X) σ ≫ c) (𝟙 X) (twist G f a σ) (hc₁ σ) (hc₂ σ) := by
  have hc := hcomm σ
  rw [galoisIso_hom_eq, galoisIso_hom_eq] at hc
  exact (galoisCommPullHomIff sq h (Sigma.ι (fun _ : G ↦ X) σ ≫ c) (𝟙 X) (twist G f a σ)
    (hc₁ σ) (hc₂ σ) f (Category.id_comp f) (twist_comp G f a σ)).2
    (galoisRearrangeCommInv (Scheme.Modules.pullback (twist G f a σ))
      (Scheme.Modules.pullback (𝟙 X)) h
      ((Scheme.Modules.pullbackId X).app (D₁.obj .unit)).symm
      ((Scheme.Modules.pullbackId X).inv.app (D₂.obj .unit)) _ _
      ((Scheme.Modules.pullbackId X).inv.naturality h) hc)

/-- The compatibility of a morphism of Galois descent systems with the transition morphisms
over the chosen fibre square. -/
private lemma galoisCommChosen (hciso : IsIso c)
    {D₁ D₂ : modulePullbackPseudofunctor.{u}.DescentData (galoisFamily f)}
    (hq₁ : (D₁.obj .unit).IsQuasicoherent) (hq₂ : (D₂.obj .unit).IsQuasicoherent)
    (h : D₁.obj .unit ⟶ D₂.obj .unit)
    (hcomm : ∀ σ : G, (galoisIso (a := a) D₁ σ).hom ≫
        (Scheme.Modules.pullback (twist G f a σ)).map h = h ≫ (galoisIso (a := a) D₂ σ).hom) :
    (modulePullbackPseudofunctor.{u}.map sq.p₁.op.toLoc).toFunctor.map h ≫
        D₂.hom (i₁ := .unit) (i₂ := .unit) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ =
      D₁.hom (i₁ := .unit) (i₂ := .unit) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ ≫
        (modulePullbackPseudofunctor.{u}.map sq.p₂.op.toLoc).toFunctor.map h := by
  have := hciso
  exact sigmaIsoPullHomExt c (D₁.obj .unit) (D₂.obj .unit) hq₁ hq₂ sq.p₁ sq.p₂
    (fun _ ↦ 𝟙 X) (fun σ ↦ twist G f a σ) hc₁ hc₂ _ _
    (galoisCommSummand sq c hc₁ hc₂ h hcomm)

/-- **A morphism of Galois descent systems is a morphism of descent data.** -/
private lemma galoisCommGeneral (hciso : IsIso c)
    {D₁ D₂ : modulePullbackPseudofunctor.{u}.DescentData (galoisFamily f)}
    (hq₁ : (D₁.obj .unit).IsQuasicoherent) (hq₂ : (D₂.obj .unit).IsQuasicoherent)
    (h : D₁.obj .unit ⟶ D₂.obj .unit)
    (hcomm : ∀ σ : G, (galoisIso (a := a) D₁ σ).hom ≫
        (Scheme.Modules.pullback (twist G f a σ)).map h = h ≫ (galoisIso (a := a) D₂ σ).hom)
    {W : Scheme.{u}} (q : W ⟶ Y) (g₁ g₂ : W ⟶ X) (hg₁ : g₁ ≫ f = q) (hg₂ : g₂ ≫ f = q) :
    (modulePullbackPseudofunctor.{u}.map g₁.op.toLoc).toFunctor.map h ≫
        D₂.hom (i₁ := .unit) (i₂ := .unit) q g₁ g₂ hg₁ hg₂ =
      D₁.hom (i₁ := .unit) (i₂ := .unit) q g₁ g₂ hg₁ hg₂ ≫
        (modulePullbackPseudofunctor.{u}.map g₂.op.toLoc).toFunctor.map h := by
  obtain ⟨p, hp₁, hp₂⟩ := sq.isPullback.exists_lift g₁ g₂ (by rw [hg₁, hg₂])
  exact (galoisCommPullHomIff sq h p g₁ g₂ hp₁ hp₂ q hg₁ hg₂).1
    (pullHomCongr (F := modulePullbackPseudofunctor.{u})
      (galoisCommChosen sq c hc₁ hc₂ hciso hq₁ hq₂ h hcomm) p g₁ g₂ hp₁ hp₂)

end Fullness

/-! ### Galois descent for quasi-coherent modules -/

section Equivalence

open GaloisDescentData

variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (a : Gᵐᵒᵖ →* Aut (Over.mk f))

private lemma galoisCoverComparison_ι_comp_p₁ (σ : G) :
    (Sigma.ι (fun _ : G ↦ X) σ ≫ galoisCoverComparison f a) ≫
      (galoisChosenPullback f).p₁ = 𝟙 X :=
  galoisCoverComparison_ι_comp_fst f a σ

private lemma galoisCoverComparison_ι_comp_p₂ (σ : G) :
    (Sigma.ι (fun _ : G ↦ X) σ ≫ galoisCoverComparison f a) ≫
      (galoisChosenPullback f).p₂ = twist G f a σ :=
  galoisCoverComparison_ι_comp_snd f a σ

variable [hiso : IsIso (galoisCoverComparison f a)]

include hiso

/-- **The comparison functor of Galois descent is full.** -/
instance galoisDescentFunctor_full : (galoisDescentFunctor G f a).Full where
  map_surjective {D₁ D₂} ψ := by
    refine ⟨ObjectProperty.homMk { hom := fun _ ↦ ψ.hom, comm := ?_ }, ?_⟩
    · intro W q i₁ i₂ g₁ g₂ hg₁ hg₂
      obtain ⟨⟩ := i₁
      obtain ⟨⟩ := i₂
      exact galoisCommGeneral (galoisChosenPullback f) (galoisCoverComparison f a)
        (galoisCoverComparison_ι_comp_p₁ f a) (galoisCoverComparison_ι_comp_p₂ f a) hiso
        (D₁.property .unit) (D₂.property .unit) ψ.hom (fun σ ↦ ψ.comm σ) q g₁ g₂ hg₁ hg₂
    · apply GaloisDescentData.Hom.ext
      rfl

/-- **The comparison functor of Galois descent is essentially surjective.** -/
instance galoisDescentFunctor_essSurj : (galoisDescentFunctor G f a).EssSurj where
  mem_essImage A := by
    have : IsIso (galoisTripleComparison f a) := galoisTripleComparison_isIso f a
    obtain ⟨θ, hθ⟩ := sigmaIsoPullHomExists (galoisCoverComparison f a)
      A.module A.module A.isQuasicoherent A.isQuasicoherent
      (galoisChosenPullback f).p₁ (galoisChosenPullback f).p₂
      (fun _ ↦ 𝟙 X) (fun σ ↦ twist G f a σ)
      (galoisCoverComparison_ι_comp_p₁ f a) (galoisCoverComparison_ι_comp_p₂ f a)
      (fun σ ↦ actionHom A σ)
    exact essImage_galoisDescentDatum A (galoisChosenPullback f) θ
      (galoisCoverComparison f a) (galoisCoverComparison_ι_comp_p₁ f a)
      (galoisCoverComparison_ι_comp_p₂ f a) hθ (galoisChosenPullback₃ f)
      (galoisTripleComparison f a)
      (fun p ↦ galoisTripleComparison_ι_p₁ f a p.1 p.2)
      (fun p ↦ galoisTripleComparison_ι_p₂ f a p.1 p.2)
      (fun p ↦ galoisTripleComparison_ι_p₃ f a p.1 p.2)

/-- **The comparison functor of Galois descent is an equivalence.** -/
instance galoisDescentFunctor_isEquivalence :
    (galoisDescentFunctor G f a).IsEquivalence := { }

/-- **Galois descent for quasi-coherent modules.**  For a surjective finite étale morphism
`f : X ⟶ Y` carrying an action of a finite group `G` over `Y` which identifies `∐_{σ : G} X`
with `X ×_Y X`, quasi-coherent modules on `Y` are the same thing as Galois descent systems
on `X`. -/
@[stacks 0D1V, sga "4½ Arcata 1.5.1" "a), b), c) equivalence"]
theorem nonempty_equivalence_galoisDescentData [IsFinite f] [Etale f] [Surjective f] :
    Nonempty ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ≌
      GaloisDescentData G f a) :=
  nonempty_equivalence_galoisDescentData_of_isStack f a inferInstance

end Equivalence

end Stacks.Descent

end

end

