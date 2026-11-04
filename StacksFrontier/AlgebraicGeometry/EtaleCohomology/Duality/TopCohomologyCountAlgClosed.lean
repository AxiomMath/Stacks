module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationNeighbourhood
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationNeighbourhoodExists
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyElementaryFibration

/-!
# The top compactly supported cohomology of a smooth variety over an algebraically closed field

Let `k` be an algebraically closed field and `N ≥ 1` invertible in `k`. For `W` smooth irreducible
of relative dimension `e` over `k`, noetherian, and any compactification `j : W → X̄`,

`H^{2e}_c(W, ℤ/N) = Ext^{2e}_X̄(ℤ/N, j_! ℤ/N) ≅ ℤ/N`.

For `Y` connected, smooth and proper of relative dimension `d` over `k` and a prime `ℓ` invertible
in `k`, `H^{2d}(Y, ℤ/ℓ^{m+1}) ≅ ℤ/ℓ^{m+1}`.

The derived categories are those of the standard model `HasDerivedCategory.standard`.

## Main results

* `Stacks.EtaleCohomology.nonempty_ext_top_addEquiv_zmod_of_isAlgClosed`:
  `Ext^{2e}_X̄(ℤ/N, j_! ℤ/N) ≅ ℤ/N` for `W` smooth irreducible of relative dimension `e`.
* `Stacks.EtaleCohomology.nonempty_ext_unitSheaf_top_addEquiv_zmod_pow`:
  `H^{2d}(Y, ℤ/ℓ^{m+1}) ≅ ℤ/ℓ^{m+1}` for `Y` connected, smooth and proper of relative dimension
  `d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **`H^{2e}_c(W, ℤ/N) ≅ ℤ/N`** for `N` invertible in an algebraically closed field `k` and `W`
smooth irreducible of relative dimension `e` over `k`, noetherian, through any compactification
`j : W → X̄`: `Ext^{2e}_X̄(ℤ/N, j_! ℤ/N) ≅ ℤ/N`. -/
theorem nonempty_ext_top_addEquiv_zmod_of_isAlgClosed (N : ℕ) [NeZero N] (hN : IsUnit (N : k))
    (e : ℕ) (W : Scheme.{u}) (p : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e p]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk p)) :
    Nonempty (Ext (unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj (unitSheaf (X := W) N))
        (2 * e) ≃+ ZMod N) :=
  nonempty_ext_top_addEquiv_zmod N hN
    (existsDenseElementaryFibration_of_neighbourhood (existsElementaryFibrationNeighbourhood k))
    (higherDirectImageTwoOfElementaryFibration k N) e W p jc

/-- **`H^{2d}(Y, ℤ/ℓ^{m+1}) ≅ ℤ/ℓ^{m+1}`** for `Y` connected, smooth of relative dimension `d` and
proper over an algebraically closed field `k` in which the prime `ℓ` is invertible. -/
theorem nonempty_ext_unitSheaf_top_addEquiv_zmod_pow (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsProper g] (d : ℕ)
    [SmoothOfRelativeDimension d g] [ConnectedSpace Y] (m : ℕ) :
    Nonempty (Ext (unitSheaf (X := Y) (ℓ ^ (m + 1))) (unitSheaf (ℓ ^ (m + 1))) (2 * d) ≃+
      ZMod (ℓ ^ (m + 1))) :=
  have : NeZero (ℓ ^ (m + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  natCard_ext_unitSheaf_top_pow ℓ hℓ g d m
    (existsDenseElementaryFibration_of_neighbourhood (existsElementaryFibrationNeighbourhood k))
    (higherDirectImageTwoOfElementaryFibration k (ℓ ^ (m + 1)))

end Stacks.EtaleCohomology

end
