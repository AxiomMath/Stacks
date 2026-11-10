module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Algebra.Algebra.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence

/-!
# Finite type of the direct image along a finite morphism

Let `f : Z ⟶ X` be a finite morphism with `X` locally Noetherian and let `G` be a quasi-coherent
`𝒪_Z`-module of finite type. Then `f_* G` is of finite type. This is the finiteness step behind
the coherence assertion of [Stacks, Tag 01Y6], which is
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`.

## Main results

* `AlgebraicGeometry.isFiniteType_pushforward_of_isFinite`: the direct image of a quasi-coherent
  module of finite type along a finite morphism is of finite type.

## Implementation notes

The argument is the one already used for a closed immersion in
`StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence`, with its
one surjectivity step replaced. On an affine open `V` of `X` the sections of `f_* G` are the
sections of `G` on `f ⁻¹ᵁ V` with scalars restricted along `f.app V`, by
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.specModulePushforwardIso`. For a closed
immersion `f.app V` is surjective and the module stays finite because every scalar of the target
is hit; for a finite morphism `f.app V` is instead a *finite* ring map, and the module stays
finite by transitivity of module-finiteness over the tower `Γ(X, V) → Γ(Z, f ⁻¹ᵁ V) → M`. That
is the algebra content of [Stacks, Tag 00GJ], and `AlgebraicGeometry.IsFinite.finite_app` is
what supplies finiteness of the ring map.

Coherence itself is not deduced here. It follows from finiteness of type and quasi-coherence
through `Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`,
i.e. (2) ⇒ (1) of [Stacks, Tag 01XZ], and that deduction is carried out once in
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`.

Note that the locally Noetherian hypothesis on the *source* is not assumed: it is implied by
finiteness over a locally Noetherian base, which is [Stacks, Tag 01T6], but the proof below does
not use it, so it is not asked for.

## References

* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 00GJ](https://stacks.math.columbia.edu/tag/00GJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.ClosedImmersionCoherence

universe u

namespace AlgebraicGeometry

/-- **Module-finiteness composes with restriction of scalars along a finite ring map.** If
`f : R →+* S` is a finite ring map and `M` is a finite `S`-module, then `M` is finite over `R`
when viewed as an `R`-module through `f`. This is [Stacks, Tag 00GJ]. -/
theorem finite_restrictScalars_of_finite_hom {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) (M : ModuleCat.{u} S) (h : Module.Finite S M) :
    Module.Finite R ((ModuleCat.restrictScalars f).obj M) := by
  let _ : Algebra R S := f.toAlgebra
  have : Module.Finite R S := hf
  change @Module.Finite R (M : Type u) _ _ (Module.compHom (M : Type u) f)
  let _ : Module R (M : Type u) := Module.compHom (M : Type u) f
  have : IsScalarTower R S (M : Type u) := ⟨fun r s m => mul_smul (f r) s m⟩
  exact Module.Finite.trans S (M : Type u)

/-- **Finite type ascends along a finite morphism.** On every affine open `V` of the target the
sections of the direct image are the sections of the module on `f ⁻¹ᵁ V`, finite over
`Γ(Z, f ⁻¹ᵁ V)` and hence, the ring map `f.app V` being finite, over `Γ(X, V)` itself. -/
theorem isFiniteType_pushforward_of_isFinite {Z X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Z ⟶ X) [IsFinite f] (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ((Scheme.Modules.pushforward f).obj G).IsFiniteType := by
  refine isFiniteType_of_cover_isFiniteTildeOn _ (fun V : X.affineOpens => (V : X.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top X)) (fun V => V.2) fun V => ?_
  refine isFiniteTildeOn_of_finite_specModule _ _ V.2 ?_
  have h2 := finite_restrictScalars_of_finite_hom (f.app (V : X.Opens)).hom
    (IsFinite.finite_app f (V : X.Opens) V.2) (specModule G (V.2.preimage f))
    (finite_specModule G (V.2.preimage f))
  exact Module.Finite.equiv
    (specModulePushforwardIso f G V.2 (V.2.preimage f)).symm.toLinearEquiv

end AlgebraicGeometry

end
