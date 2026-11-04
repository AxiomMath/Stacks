module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.SheafyTraceIsIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalDerivedHom.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Global duality for `Rf^!`

Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes and let `Λ` be a torsion ring. [Stacks, Tag 0GLD] states that for every
`K ∈ D(Y_étale, Λ)` and `L ∈ D(X_étale, Λ)` the map of [Stacks, Tag 0GLB] induces an isomorphism

`RHom_X(L, Rf^!K) ⟶ RHom_Y(Rf_!L, K)`

of global derived homs.

## The proof

The source's. The global derived hom is `RHom_X(L, M) = RΓ(X, RHom_Λ(L, M))` by the construction
of [Stacks, Tag 0B6E] (`Stacks.EtaleCohomology.etaleGlobalDerivedHom`), so

`RHom_X(L, Rf^!K) = RΓ(X, RHom_Λ(L, Rf^!K)) = RΓ(Y, Rf_*RHom_Λ(L, Rf^!K))`

by Leray (`Stacks.EtaleCohomology.etaleGlobalDerivedHomLerayIso`), and
`RHom_Y(Rf_!L, K) = RΓ(Y, RHom_Λ(Rf_!L, K))`. The map is `RΓ(Y, -)` of the map of
[Stacks, Tag 0GLB] (`Stacks.EtaleCohomology.derivedUpperShriekUnboundedSheafyTrace`), which is an
isomorphism by [Stacks, Tag 0GLC]
(`Stacks.EtaleCohomology.isIso_derivedUpperShriekUnboundedSheafyTrace`).

## Main definitions

* `Stacks.EtaleCohomology.derivedUpperShriekUnboundedGlobalTrace`: the map
  `RHom_X(L, Rf^!K) ⟶ RHom_Y(Rf_!L, K)` induced by the map of [Stacks, Tag 0GLB].

## Main results

* `Stacks.EtaleCohomology.isIso_derivedUpperShriekUnboundedGlobalTrace`: [Stacks, Tag 0GLD].

## Implementation notes

As for [Stacks, Tag 0GLC], `Rf_! = Rf̄_* ∘ j_!` and its right adjoint `Rf^!` of
[Stacks, Tag 0G2C] are computed through a compactification `j`; one exists by
[Stacks, Tag 0F41], and the statement holds for every one. A torsion ring is one in which
`m = 0` for some integer `m ≥ 1`. The global derived homs are read in `D(Λ)`.

## References

* [Stacks Project, Tag 0GLD](https://stacks.math.columbia.edu/tag/0GLD)
* [Stacks Project, Tag 0GLC](https://stacks.math.columbia.edu/tag/0GLC)
* [Stacks Project, Tag 0GLB](https://stacks.math.columbia.edu/tag/0GLB)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable {Λ : Type r} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f)) (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-- **The map `RHom_X(L, Rf^!K) ⟶ RHom_Y(Rf_!L, K)` induced by [Stacks, Tag 0GLB]**: Leray
`RHom_X(L, Rf^!K) = RΓ(Y, Rf_*RHom_Λ(L, Rf^!K))`, followed by `RΓ(Y, -)` of the map
`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`. -/
def derivedUpperShriekUnboundedGlobalTrace (L : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    ((etaleGlobalDerivedHom.{u, r} Λ X).obj (op L)).obj
        ((derivedUpperShriekUnbounded.{u, r} Λ j hΛ).obj K) ⟶
      ((etaleGlobalDerivedHom.{u, r} Λ Y).obj
        (op ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj L))).obj K :=
  (etaleGlobalDerivedHomLerayIso.{u, r} Λ f L
      ((derivedUpperShriekUnbounded.{u, r} Λ j hΛ).obj K)).hom ≫
    (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y).map
      (derivedUpperShriekUnboundedSheafyTrace.{u, r} f j hΛ L K)

/-- **The defining composite**: Leray followed by `RΓ(Y, -)` of the map of
[Stacks, Tag 0GLB]. -/
theorem derivedUpperShriekUnboundedGlobalTrace_eq (L : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    derivedUpperShriekUnboundedGlobalTrace.{u, r} f j hΛ L K =
      (etaleModuleDerivedGlobalSectionsUnboundedLerayIso.{u, r} Λ f).hom.app
          (((etaleDerivedHom.{u, r} Λ X).obj (op L)).obj
            ((derivedUpperShriekUnbounded.{u, r} Λ j hΛ).obj K)) ≫
        (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y).map
          (derivedUpperShriekUnboundedSheafyTrace.{u, r} f j hΛ L K) :=
  rfl

/-- **[Stacks, Tag 0GLD].** Let `f : X ⟶ Y` be a separated finite type morphism of quasi-compact
and quasi-separated schemes and let `Λ` be a torsion ring (`m = 0` in `Λ` for some `m ≥ 1`). Then
`f` has a compactification `j : X ⟶ X̄` over `Y`, and for every compactification `j`, every
`K ∈ D(Y_étale, Λ)` and every `L ∈ D(X_étale, Λ)` the map of [Stacks, Tag 0GLB] induces an
isomorphism `RHom_X(L, Rf^!K) ⟶ RHom_Y(Rf_!L, K)` of global derived homs
`RHom_X(-, -) = RΓ(X, RHom_Λ(-, -))` ([Stacks, Tag 0B6E]), with `Rf_! = Rf̄_* ∘ j_!` and `Rf^!`
its right adjoint of [Stacks, Tag 0G2C]. -/
@[stacks 0GLD, sga "7 XIII 2.1.6" "more general"]
theorem isIso_derivedUpperShriekUnboundedGlobalTrace (Λ : Type) [CommRing Λ]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) ∧
      ∀ (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, 0} Λ Y))
        (L : DerivedCategory (EtaleModules.{u, 0} Λ X)),
        IsIso (derivedUpperShriekUnboundedGlobalTrace.{u, 0} f j hΛ L K) := by
  obtain ⟨hj, h0GLC⟩ := isIso_derivedUpperShriekUnboundedSheafyTrace Λ hΛ f
  refine ⟨hj, fun j K L => ?_⟩
  have := h0GLC j K L
  exact IsIso.comp_isIso' inferInstance
    (Functor.map_isIso (etaleModuleDerivedGlobalSectionsUnbounded.{u, 0} Λ Y)
      (derivedUpperShriekUnboundedSheafyTrace.{u, 0} f j hΛ L K))

end Stacks.EtaleCohomology

end
