module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.IntegralBaseSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.IntegralImageAssembly

/-!
# The induction step of Stacks 02TT over an integral base, with no finiteness hypothesis

`Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_of_isIntegral` is the induction
step of the second part of the proof of Stacks 02TT: over an integral base `Y`, flat pullback
along an affine-space bundle is surjective as soon as it is surjective over every base of
strictly smaller delta-dimension. It carries a hypothesis `dim_δ(Y) = n` for an integer `n`,
because the strict decrease it extracts from passing to the complement of a trivializing open
subscheme (`Stacks.Chow.schemeDeltaDimension_lt_of_range_eq_compl`) is only available at a finite
delta-dimension.

That hypothesis is free. An integral scheme is irreducible, so its delta-dimension — a supremum
over its irreducible components — is attained at the single component and is the relative
dimension of the generic point, an integer. This file records the induction step with the
hypothesis discharged, which is the form the devissage of Stacks 02TT applies after its first
step has replaced an arbitrary base by the integral closed subschemes carrying the images of the
components of a class.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_isIntegral_of_forall_schemeDeltaDimension_lt` — the
  induction step of Stacks 02TT over an integral base, carrying no finiteness hypothesis.

## Implementation notes

No `@[stacks 02TT]` attribute is placed here. This is one step of that proof, and the two steps
that are formalized carry the tag already, in
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity`; the devissage itself
is still a hypothesis there.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-- **The induction step of Stacks 02TT over an integral base, unconditionally.** Let
`f : X ⟶ Y` be an affine-space bundle of rank `r` with `Y` integral and locally of finite type
over the base of chapter 42. Assume

* flat pullback along the projection of affine `r`-space is surjective in degree `k` over every
  base, and
* flat pullback in degree `k` is surjective along every affine-space bundle of rank `r` whose
  base has strictly smaller delta-dimension than `Y`.

Then flat pullback along `f` is surjective in degree `k`.

This is `Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_of_isIntegral` with its
hypothesis `dim_δ(Y) = n` supplied by
`Stacks.Chow.exists_schemeDeltaDimension_eq_of_irreducibleSpace`: an integral scheme is
irreducible, so its delta-dimension is the relative dimension of its generic point and in
particular an integer. -/
theorem flatPullbackChow_surjective_isIntegral_of_forall_schemeDeltaDimension_lt
    (C : ChowSituation.{u})
    (htriv : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (r : ℕ) (j : ℤ),
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin r); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin r); B) ↘ B) rfl r
        (relativeDimension_affineSpaceOver B r) j))
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (hbundle : IsAffineSpaceBundle f r) (k : ℤ)
    (hsmaller : ∀ (Z W : Scheme.{u}) (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sW : W ⟶ C.S)
      [LocallyOfFiniteType sW] (g : W ⟶ Z) [LocallyOfFiniteType g] [AlgebraicGeometry.Flat g]
      (hgb : g ≫ sZ = sW) (hg : AlgebraicGeometry.RelativeDimension g r),
      IsAffineSpaceBundle g r → schemeDeltaDimension C sZ < schemeDeltaDimension C sY →
      Function.Surjective (flatPullbackChowOfRelativeDimension C sW sZ g hgb r hg k)) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) :=
  let ⟨_, hn⟩ := exists_schemeDeltaDimension_eq_of_irreducibleSpace C sY
  flatPullbackChow_surjective_of_isAffineSpaceBundle_of_isIntegral C htriv sY f r hf hbundle k
    hn hsmaller

end Stacks.Chow

end
