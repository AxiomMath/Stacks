module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyPointClassReduction

/-!
# Nonvanishing of the class of a point in top compactly supported cohomology: the three parts

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k` and `Λ = ℤ/ℓ`. For `W`
smooth irreducible of relative dimension `e` over `k` with a compactification `j : W → X̄`, and a
`k`-point `i : P → N` closed in an open `n : N → W`, the class of `P` is *nonzero*
(`Stacks.EtaleCohomology.PointClassNonzeroAt`) when some class
`γ₀ ∈ Ext^{2e}_N(i_* Λ_P, (n ≫ j)⁻¹ j_! Λ_W)` and some `z ∈ Ext⁰_X̄(Λ, (n ≫ j)_! i_* Λ_P)` have
`z ∘ (n ≫ j)_! γ₀ ≠ 0` in `H^{2e}_c(W)`. By
`Stacks.EtaleCohomology.topCohomologyPointClassNonzero_of_exists` this, for every point, gives the
nonvanishing for every purity class, hence `Stacks.EtaleCohomology.TopCohomologyPointClass`.

The proof has three parts, stated here:

* the case of curves (`Stacks.EtaleCohomology.CurvePointClassNonzero`): the Kummer divisor class
  of a local parameter maps to the class of `𝒪(P)`, of degree one;
* the moving lemma (`Stacks.EtaleCohomology.PointClassNonzeroMoving`): if the class of one point
  of `W` is nonzero, so is the class of every point, through a smooth curve joining two points;
* the step through an elementary fibration (compatibility of point classes with the Leray
  isomorphism), which produces one point with nonzero class.

## Main definitions

* `Stacks.EtaleCohomology.PointClassNonzeroAt`.
* `Stacks.EtaleCohomology.CurvePointClassNonzero`.
* `Stacks.EtaleCohomology.PointClassNonzeroMoving`.

## Main results

* `Stacks.EtaleCohomology.topCohomologyPointClassNonzero_of_pointClassNonzeroAt`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

/-- **The class of the point `i : P → N ⊆ W` is nonzero in `H^{2e}_c(W)`**: some class
`γ₀ ∈ Ext^{2e}_N(i_* Λ_P, (n ≫ j)⁻¹ j_! Λ_W)` and some `z ∈ Ext⁰_X̄(Λ, (n ≫ j)_! i_* Λ_P)` have
`z ∘ (n ≫ j)_! γ₀ ≠ 0`. -/
def PointClassNonzeroAt (e : ℕ) {W : Scheme.{u}} (f : W ⟶ Spec (.of k))
    (jc : CompactificationOf (Over.mk f)) {N P : Scheme.{u}} (n : N ⟶ W) [IsOpenImmersion n]
    (i : P ⟶ N) : Prop :=
  ∃ (γ₀ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ))) (2 * e))
    (z : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))) 0),
    z.comp (Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
      (n ≫ jc.immersion)) _ _ (2 * e) γ₀) (zero_add _) ≠ 0

variable (k)

/-- **The class of a point of a smooth curve is nonzero in `H²_c`**: for every smooth irreducible
curve `W` over `k`, noetherian, with a compactification, and every `k`-point `i : P → N` closed in
an open `N ⊆ W`, `Stacks.EtaleCohomology.PointClassNonzeroAt` holds in degree `2`. (The Kummer
divisor class of a local parameter at `P` maps to the class of `𝒪(P)`, of degree one.) -/
def CurvePointClassNonzero : Prop :=
  ∀ (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk f))
    (N P : Scheme.{u}) (n : N ⟶ W) [IsOpenImmersion n] (i : P ⟶ N) [IsClosedImmersion i]
    [IrreducibleSpace P] [SmoothOfRelativeDimension 0 (i ≫ n ≫ f)],
    PointClassNonzeroAt ℓ 1 f jc n i

/-- **The moving lemma for point classes**: for `W` smooth irreducible of relative dimension `e`
over `k`, noetherian, with a compactification, if the class of one `k`-point of `W` is nonzero in
`H^{2e}_c(W)`, so is the class of every `k`-point. (Join the two points by a smooth irreducible
curve `C`, with a purity class of `C` on an open containing both; the two point classes of `C`
generate `H²_c(C)`, and the Gysin map of `C` carries them to the two point classes of `W`.) -/
def PointClassNonzeroMoving : Prop :=
  ∀ (e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk f)),
    (∃ (N' P' : Scheme.{u}) (n' : N' ⟶ W) (_ : IsOpenImmersion n') (i' : P' ⟶ N')
      (_ : IsClosedImmersion i') (_ : IrreducibleSpace P')
      (_ : SmoothOfRelativeDimension 0 (i' ≫ n' ≫ f)), PointClassNonzeroAt ℓ e f jc n' i') →
    ∀ (N P : Scheme.{u}) (n : N ⟶ W) [IsOpenImmersion n] (i : P ⟶ N) [IsClosedImmersion i]
      [IrreducibleSpace P] [SmoothOfRelativeDimension 0 (i ≫ n ≫ f)],
      PointClassNonzeroAt ℓ e f jc n i

variable {k}

/-- **Point classes are nonzero for every purity class once they are nonzero for some class**, at
every point (`Stacks.EtaleCohomology.topCohomologyPointClassNonzero_of_exists`). -/
theorem topCohomologyPointClassNonzero_of_pointClassNonzeroAt
    (h : ∀ (e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
      [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
      (jc : CompactificationOf (Over.mk f))
      (N P : Scheme.{u}) (n : N ⟶ W) [IsOpenImmersion n] (i : P ⟶ N) [IsClosedImmersion i]
      [IrreducibleSpace P] [SmoothOfRelativeDimension 0 (i ≫ n ≫ f)],
      PointClassNonzeroAt ℓ e f jc n i) :
    TopCohomologyPointClassNonzero ℓ k :=
  topCohomologyPointClassNonzero_of_exists ℓ
    fun e W f _ _ _ jc N P n _ i _ _ _ _ _ => h e W f jc N P n i

end Stacks.EtaleCohomology

end
