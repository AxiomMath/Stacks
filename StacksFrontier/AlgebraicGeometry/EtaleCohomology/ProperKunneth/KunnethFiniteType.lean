module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperKunneth.KunnethTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperKunneth.SeparablyClosedPointCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteTypeAbsolute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed
import StacksCore.Tactic.StacksAttribute

/-!
# Künneth for a proper factor over a separably closed field, `ℤ/nℤ` coefficients (Stacks 0F14 (2))

Let `k` be a separably closed field, `X` a proper scheme over `k`, `Y` a scheme of finite type over
`k`, with structure morphisms `f : X ⟶ Spec k` and `g : Y ⟶ Spec k` and projections
`pr₁ : X ×_k Y ⟶ X`, `pr₂ : X ×_k Y ⟶ Y`, and `n ≥ 1`. For `E ∈ D(X_étale, ℤ/nℤ)` and
`K ∈ D(Y_étale, ℤ/nℤ)`, unbounded, [Stacks, Tag 0F14] (2) asserts

`RΓ(X ×_k Y, pr₁⁻¹E ⊗^L_{ℤ/nℤ} pr₂⁻¹K) = RΓ(X, E) ⊗^L_{ℤ/nℤ} RΓ(Y, K)`.

Over `Spec k`, `k` separably closed, global sections identify `D((Spec k)_étale, ℤ/nℤ)` with
`D(ℤ/nℤ)`, and the derived direct images to `Spec k` are the derived global sections; the
statement is the invertibility of the Künneth map
`Rf_*E ⊗^L Rg_*K ⟶ R(pr₂ ≫ g)_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)` of
`Stacks.EtaleCohomology.etaleKunnethCompositeMap`.

## The proof

The source's: [Stacks, Tag 0F0G] for the proper `pr₂`, proper base change for unbounded objects
with `ℤ/nℤ` coefficients ([Stacks, Tag 0F0C]) and [Stacks, Tag 0F12] for `Y`
(`isIso_etaleKunnethCompositeMap_zmod_of_etaleCohomologicalDimension_lt_top`), the last using
`cd(Y) < ∞`. That is [Stacks, Tag 0F10] (2), `k` being separably closed and so of cohomological
dimension `0`; it bounds the cohomological dimension of `g` because the stalk of
`Rⁿg_*F` at the point of `Spec k` is `Hⁿ(Y, F)`
(`AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_lt_top_of_isSepClosed`).

## Main results

* `Stacks.EtaleCohomology.isIso_etaleKunnethCompositeMap_zmod_of_finiteType`:
  **[Stacks, Tag 0F14] (2)**.

## References

* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

universe u

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 0F14] (2).** Let `k` be a separably closed field, `f : X ⟶ Spec k` proper,
`g : Y ⟶ Spec k` of finite type, and `n ≥ 1`. For `E ∈ D(X_étale, ℤ/nℤ)` and
`K ∈ D(Y_étale, ℤ/nℤ)`, unbounded, the Künneth map
`RΓ(X, E) ⊗^L_{ℤ/nℤ} RΓ(Y, K) = Rf_*E ⊗^L Rg_*K ⟶ R(pr₂ ≫ g)_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)
= RΓ(X ×_k Y, pr₁⁻¹E ⊗^L pr₂⁻¹K)` in `D((Spec k)_étale, ℤ/nℤ) = D(ℤ/nℤ)` is an
isomorphism. -/
@[stacks 0F14 "(2); on D((Spec k)_et, ℤ/nℤ), which global sections identify with D(ℤ/nℤ) for k
separably closed, so that the direct images to Spec k are the derived global sections",
  sga "4½ Th_finitude 1.11" "Künneth arrow RΓ(X"]
theorem isIso_etaleKunnethCompositeMap_zmod_of_finiteType (n : ℕ) (hn : 0 < n) (k : Type u)
    [Field k] [IsSepClosed k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g]
    (E : DerivedCategory (EtaleModules.{u, 0} (ZMod n) X))
    (K : DerivedCategory (EtaleModules.{u, 0} (ZMod n) Y)) :
    IsIso (etaleKunnethCompositeMap.{u, 0} (ZMod n) f g (pullback.fst f g) (pullback.snd f g)
      pullback.condition E K) := by
  have : CompactSpace Y := Scheme.compactSpace_of_finiteType k g
  have : QuasiSeparatedSpace Y := Scheme.quasiSeparatedSpace_of_finiteType k g
  have hk : Scheme.etaleCohomologicalDimension (Spec (.of k)) < ⊤ :=
    (Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed k).trans_lt ENat.top_pos
  exact isIso_etaleKunnethCompositeMap_zmod_of_etaleCohomologicalDimension_lt_top n hn k f g
    (Scheme.Hom.etaleCohomologicalDimension_lt_top_of_isSepClosed g
      (Scheme.etaleCohomologicalDimension_lt_top_of_finiteType k g hk)) E K

end Stacks.EtaleCohomology

end
