module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Localization.Free
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.SpecTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.RingTheory.Module.LocallyFree.Field
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite locally free morphisms of a given rank over an affine base

A morphism to an affine scheme is finite locally free of rank `d` exactly when it is affine and
the global sections of its source are a finite locally free module of rank `d` over the global
sections of its target.

## Main results

* `Stacks.Morphisms.sheafOfModules_isFiniteLocallyFreeOfRank_iff_module` identifies the
  sheaf-level condition on the direct image of the structure sheaf with the module-level
  condition on the global sections, for a morphism to the spectrum of a ring.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine` is the same statement for
  an arbitrary affine target.
* `AlgebraicGeometry.finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank` combines the
  latter with the module-level field case: the global sections of a scheme finite locally free of
  rank `r` over a field form a vector space of dimension exactly `r`.

## Implementation notes

Both statements are the rank-indexed companions of
`Stacks.Morphisms.sheafOfModules_isFiniteLocallyFree_iff_module`, and the first is proved the
same way: over the spectrum of a ring the direct image of the structure sheaf of an affine
morphism is quasi-coherent, hence the module sheaf of its global sections, and the sheaf-to-module
bridge of Tag 05JM turns finite local freeness of rank `d` of that sheaf into finite local
freeness of rank `d` of the global sections as a module.

The passage from `Spec` of a ring to an arbitrary affine target is by composing with
`AlgebraicGeometry.Scheme.isoSpec`, which leaves the source — and therefore the module of global
sections — untouched, and changes the ring homomorphism inducing the algebra structure only by
cancelling `AlgebraicGeometry.Scheme.ΓSpecIso` against itself. The algebra structure is taken as
an argument together with the equation identifying its structure map, rather than being fixed to
`Scheme.Hom.appTop`, so that the statement can be used against whichever instance the caller
already has in scope.

The module-level field case is `Module.IsFiniteLocallyFreeOfRank.finite_and_finrank_eq`, proved
once and for all in `StacksFrontier.RingTheory.Module.LocallyFree.Field`; it is combined with the
sheaf-to-module bridge here, which is where every consumer in this development reaches it from.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

/-- For a morphism to the spectrum of a ring with affine source, the direct image of the
structure sheaf is finite locally free of rank `d` exactly when the global sections of the source
form a finite locally free module of rank `d` over that ring. -/
theorem sheafOfModules_isFiniteLocallyFreeOfRank_iff_module {R : CommRingCat.{u}}
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsAffineHom f] (d : ℕ) :
    letI := ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom.toAlgebra
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (pushforwardStructureSheaf f) d ↔
      Module.IsFiniteLocallyFreeOfRank ↑R ↑Γ(X, ⊤) d := by
  let : Algebra ↑R ↑Γ(X, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom.toAlgebra
  let M : (Spec R).Modules := pushforwardStructureSheaf f
  have hqc : M.IsQuasicoherent := by
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
    exact Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f _
  have : IsIso (Scheme.Modules.fromTildeΓ (R := R) M) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ M).mp hqc
  let e : M ≅ AlgebraicGeometry.tilde (moduleSpecΓFunctor.obj M) :=
    (asIso (Scheme.Modules.fromTildeΓ (R := R) M)).symm
  exact ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff M d).symm.trans
    ⟨.of_iso e, .of_iso e.symm⟩).trans
    (tilde_isFiniteLocallyFreeOfRank_iff ↑R ↑(moduleSpecΓFunctor.obj M) d)

/-- A morphism to an affine scheme is finite locally free of rank `d` exactly when it is affine
and the global sections of its source form a finite locally free module of rank `d` over the
global sections of its target. -/
@[sga "1 I 4.10" "special case"]
theorem isFiniteLocallyFreeOfRank_iff_module_of_isAffine {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsAffineHom f] (d : ℕ) [alg : Algebra ↑Γ(S, ⊤) ↑Γ(X, ⊤)]
    (halg : algebraMap ↑Γ(S, ⊤) ↑Γ(X, ⊤) = f.appTop.hom) :
    IsFiniteLocallyFreeOfRank f d ↔
      Module.IsFiniteLocallyFreeOfRank ↑Γ(S, ⊤) ↑Γ(X, ⊤) d := by
  have hφ : (Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ (f ≫ S.isoSpec.hom).appTop = f.appTop := by
    simp only [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id_assoc]
  obtain rfl : alg =
      ((Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ (f ≫ S.isoSpec.hom).appTop).hom.toAlgebra := by
    refine Algebra.algebra_ext _ _ fun r ↦ ?_
    rw [hφ]
    exact DFunLike.congr_fun halg r
  have h1 : IsFiniteLocallyFreeOfRank (f ≫ S.isoSpec.hom) d ↔ IsFiniteLocallyFreeOfRank f d :=
    (IsFiniteLocallyFreeOfRank.property d).cancel_right_of_respectsIso f S.isoSpec.hom
  rw [← h1, isFiniteLocallyFreeOfRank_iff, and_iff_right (inferInstance : IsAffineHom _)]
  exact sheafOfModules_isFiniteLocallyFreeOfRank_iff_module (f ≫ S.isoSpec.hom) d

end Stacks.Morphisms

namespace AlgebraicGeometry

/-- The global sections of a scheme that is finite locally free of rank `r` over a field form a
vector space of dimension exactly `r` over that field. The module structure is the one induced
by the morphism, as in `Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis`. -/
theorem finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank {k : Type u} [Field k]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) (r : ℕ)
    [h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r] :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    Module.Finite k Γ(Z, ⊤) ∧ Module.finrank k Γ(Z, ⊤) = r := by
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  have : IsAffineHom p := h.toIsAffineHom
  exact Module.IsFiniteLocallyFreeOfRank.finite_and_finrank_eq
    ((Stacks.Morphisms.sheafOfModules_isFiniteLocallyFreeOfRank_iff_module p r).mp
      h.toIsFiniteLocallyFreeOfRank)

end AlgebraicGeometry

end
