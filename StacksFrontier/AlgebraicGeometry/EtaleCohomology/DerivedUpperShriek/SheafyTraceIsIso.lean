module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.EtaleSheafyTraceIsIso
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.TorsionProjectionFormula
import StacksCore.Tactic.StacksAttribute

/-!
# The sheafy trace map is an isomorphism

Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes and let `Λ` be a torsion ring. [Stacks, Tag 0GLC] states that for every
`K ∈ D(Y_étale, Λ)` and `L ∈ D(X_étale, Λ)` the map of [Stacks, Tag 0GLB]

`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`

(`Stacks.EtaleCohomology.derivedUpperShriekUnboundedSheafyTrace`) is an isomorphism.

## The proof

The source's. The map induces a bijection on `Hom_Y(M, -)` for every `M`, by the string of
equalities

```
Hom_Y(M, Rf_*RHom(L, Rf^!K)) = Hom_X(f^{-1}M, RHom(L, Rf^!K))      (Tag 07A6)
                             = Hom_X(f^{-1}M ⊗^L L, Rf^!K)          (Tag 08J9)
                             = Hom_Y(Rf_!(f^{-1}M ⊗^L L), K)         (Rf_! ⊣ Rf^!)
                             = Hom_Y(M ⊗^L Rf_!L, K)                 (Tag 0GL5)
                             = Hom_Y(M, RHom(Rf_!L, K))             (Tag 08J9)
```

and the composite of these bijections is composition with the map. That argument, and the
identification of the projection map it uses with the map of [Stacks, Tag 0GL5], are
`Stacks.EtaleCohomology.isIso_etaleSheafyTrace_of_isIso_tensorMap`; the projection formula
itself is `Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedTensorMap`.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedUpperShriekUnboundedSheafyTrace`: [Stacks, Tag 0GLC].

## Implementation notes

As for [Stacks, Tag 0GL5], `Rf_! = Rf̄_* ∘ j_!` and `Rf^!` (the right adjoint of
[Stacks, Tag 0G2C]) are computed through a compactification `j`; one exists by
[Stacks, Tag 0F41], and the statement holds for every one. A torsion ring is one in which
`m = 0` for some integer `m ≥ 1`.

## References

* [Stacks Project, Tag 0GLC](https://stacks.math.columbia.edu/tag/0GLC)
* [Stacks Project, Tag 0GLB](https://stacks.math.columbia.edu/tag/0GLB)
* [Stacks Project, Tag 0GL5](https://stacks.math.columbia.edu/tag/0GL5)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 0GLC].** Let `f : X ⟶ Y` be a separated finite type morphism of quasi-compact
and quasi-separated schemes and let `Λ` be a torsion ring (`m = 0` in `Λ` for some `m ≥ 1`). Then
`f` has a compactification `j : X ⟶ X̄` over `Y`, and for every compactification `j`, every
`K ∈ D(Y_étale, Λ)` and every `L ∈ D(X_étale, Λ)` the map
`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)` of [Stacks, Tag 0GLB], with `Rf_! = Rf̄_* ∘ j_!` and
`Rf^!` its right adjoint of [Stacks, Tag 0G2C], is an isomorphism. -/
@[stacks 0GLC, sga "7 XIII 2.1.6" "more general"]
theorem isIso_derivedUpperShriekUnboundedSheafyTrace (Λ : Type) [CommRing Λ]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) ∧
      ∀ (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, 0} Λ Y))
        (L : DerivedCategory (EtaleModules.{u, 0} Λ X)),
        IsIso (derivedUpperShriekUnboundedSheafyTrace.{u, 0} f j hΛ L K) := by
  obtain ⟨m, hm, hmΛ⟩ := hΛ
  have h0GL5 := isIso_derivedLowerShriekUnboundedTensorMap Λ m hm hmΛ f
  refine ⟨h0GL5.1, fun j K L => ?_⟩
  have := isLeftAdjoint_derivedLowerShriekUnbounded.{u, 0} Λ j ⟨m, hm, hmΛ⟩
  exact isIso_etaleSheafyTrace_of_isIso_tensorMap Λ f j L (fun M => h0GL5.2 j L M) K

end Stacks.EtaleCohomology

end
