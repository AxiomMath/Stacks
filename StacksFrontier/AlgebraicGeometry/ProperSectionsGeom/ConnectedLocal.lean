module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Etale.Field
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections

/-!
# Global functions on a connected proper scheme over a field

Let `X` be a proper scheme over a field `k`. Clause (2) of [Stacks, Tag 0BUG] presents
`Γ(X, 𝒪_X)` as a finite product of Artinian local `k`-algebras with one factor for each connected
component of `X`. This file proves the one-component case: for `X` *connected* and proper over
`k`, `Γ(X, 𝒪_X)` is an Artinian local ring. The clause itself, for an arbitrary proper `X`, is
`componentwiseArtinianDecomposition` in
`StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Components`.

Two consequences are recorded, both used by [Stacks, Tag 0GK5]: for `X` reduced the local ring is
a field, and for `X` geometrically reduced that field is separable over `k`.

## Main results

All of these live in the namespace `Stacks.AlgebraicGeometry.ProperSectionsGeom`.

* `isArtinianRing_and_isLocalRing_globalSections_of_connectedSpace`: the one-component case of
  clause (2). `Γ(X, 𝒪_X)` is Artinian and local.
* `isField_globalSections_of_connectedSpace_of_isReduced`: the special case of clauses (2) and
  (3) at one connected component. For `X` reduced, `Γ(X, 𝒪_X)` is a field.
* `isSeparable_globalSections_of_connectedSpace_of_geometricallyReduced`: the special case of
  clauses (2), (3) and (4) at one connected component. For `X` geometrically reduced, that field
  is separable over `k`.

## Implementation notes

Artinianness is clause (1), `moduleFinite_globalSections_of_isProper`, together with the fact
that a module-finite algebra over a field is an Artinian ring.

Locality does not use clause (1). An idempotent global section of a scheme whose space is
preconnected is `0` or `1` (`ProperGeomConnected.isIdempotentElem_eq_zero_or_one`), and
`Γ(X, 𝒪_X)` is integral over `k` for `X` proper
(`ProperGeomConnected.isIntegral_toSpecΓ_algebraMap`, from Mathlib's
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`); a nontrivial algebra integral over a
field with no idempotents other than `0` and `1` is local of Krull dimension zero
(`Stacks.RingTheory.IntegralOverField.isLocalRing_and_krullDimLE_zero`).

The reduced case is then Mathlib's `IsArtinianRing.isField_of_isReduced_of_isLocalRing`. The
separable case takes the finite etale algebra of
`etale_globalSections_of_geometricallyReduced` — clauses (1), (3) and (4) — and reads
separability off it through `Algebra.FormallyEtale.iff_isSeparable`, which applies because the
ring is now known to be a field.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0GK5](https://stacks.math.columbia.edu/tag/0GK5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.ProperSectionsGeom

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The ring of global functions on a *connected* scheme proper over a field is an Artinian local
ring.

This is the one-component case of clause (2) of [Stacks, Tag 0BUG], which presents the global
functions of an arbitrary proper `X` as a product of Artinian local `k`-algebras indexed by the
connected components of `X`. The clause in full, for an arbitrary proper `X`, is
`componentwiseArtinianDecomposition` in
`StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Components`. -/
theorem isArtinianRing_and_isLocalRing_globalSections_of_connectedSpace
    [IsProper f] [ConnectedSpace X] :
    IsArtinianRing Γ(X, ⊤) ∧ IsLocalRing Γ(X, ⊤) := by
  let alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hfin : Module.Finite k Γ(X, ⊤) := moduleFinite_globalSections_of_isProper k f
  have hne : Nonempty ((⊤ : X.Opens) : Type u) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have hnt : Nontrivial Γ(X, ⊤) := Scheme.component_nontrivial X ⊤
  have hint : Algebra.IsIntegral k Γ(X, ⊤) := ⟨fun x => by
    rw [_root_.IsIntegral, RingHom.algebraMap_toAlgebra]
    exact ProperGeomConnected.isIntegral_toSpecΓ_algebraMap f x⟩
  have hidem : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he =>
    ProperGeomConnected.isIdempotentElem_eq_zero_or_one
      (by rw [TopologicalSpace.Opens.coe_top]; exact isPreconnected_univ) he
  exact ⟨isArtinian_of_tower k inferInstance,
    (Stacks.RingTheory.IntegralOverField.isLocalRing_and_krullDimLE_zero (K := k) hidem).2⟩

/-- The ring of global functions on a connected *reduced* scheme proper over a field is a
field.

This is clauses (2) and (3) read at a single connected component: a reduced Artinian local ring
is a field. The clauses in full are `componentwiseArtinianDecomposition` (clause (2)) and
`globalSectionsFieldDecomposition_of_isReduced` (clause (3)). -/
@[stacks 0BUG "special case of clauses (2) and (3): X connected and reduced, where the ring of \
global functions is a field"]
theorem isField_globalSections_of_connectedSpace_of_isReduced
    [IsProper f] [ConnectedSpace X] [AlgebraicGeometry.IsReduced X] : IsField Γ(X, ⊤) := by
  obtain ⟨hart, hloc⟩ := isArtinianRing_and_isLocalRing_globalSections_of_connectedSpace k f
  have hred : _root_.IsReduced Γ(X, ⊤) := AlgebraicGeometry.IsReduced.component_reduced ⊤
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing Γ(X, ⊤)

/-- The field of global functions on a connected *geometrically reduced* scheme proper over a
field `k` is separable over `k`.

This is clauses (2), (3) and (4) read at a single connected component. The clauses in full are
stated by other declarations, among them `GlobalSectionsFieldDecomposition.factor_isSeparable`
(clause (4)). -/
@[stacks 0BUG "special case of clauses (2), (3) and (4): X connected and geometrically reduced, \
where the field of global functions is separable over k"]
theorem isSeparable_globalSections_of_connectedSpace_of_geometricallyReduced
    [IsProper f] [ConnectedSpace X] [GeometricallyReduced f] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Algebra.IsSeparable k Γ(X, ⊤) := by
  let alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hXred : AlgebraicGeometry.IsReduced X := self_of_isIntegral_of_geometrically
    (P := AlgebraicGeometry.IsReduced)
    (inferInstance : GeometricallyReduced f).geometrically_isReduced
  let fieldΓ : Field Γ(X, ⊤) := (isField_globalSections_of_connectedSpace_of_isReduced k f).toField
  obtain ⟨hetale, hfin⟩ := etale_globalSections_of_geometricallyReduced k f
  have hft : Algebra.FiniteType k Γ(X, ⊤) := Module.Finite.finiteType Γ(X, ⊤)
  exact (Algebra.FormallyEtale.iff_isSeparable k Γ(X, ⊤)).mp hetale.formallyEtale

end Stacks.AlgebraicGeometry.ProperSectionsGeom

end
