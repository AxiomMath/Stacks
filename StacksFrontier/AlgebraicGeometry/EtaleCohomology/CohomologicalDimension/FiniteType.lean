module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineHigherDirectImageSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineOpensReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteTypeReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TrdegSupportVanishingUnconditional

/-!
# Finite cohomological dimension of schemes of finite type over a field

[Stacks, Tag 0F10]: let `K` be a field.

1. If `f : X ⟶ Y` is a morphism of schemes of finite type over `K`, then `cd(f) < ∞`.
2. If `cd(K) < ∞`, then `cd(X) < ∞` for every scheme `X` of finite type over `K`.

Here `cd(f)` is the cohomological dimension of a morphism ([Stacks, Tag 0F0Z]),
`AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension`. `cd(X)` is the cohomological
dimension of a scheme ([Stacks, Tag 0F0Q]), `AlgebraicGeometry.Scheme.etaleCohomologicalDimension`.
`cd(K)` is `cd(Spec K)`, which [Stacks, Tag 0F0Q] calls the cohomological dimension of the
ring `K`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isEtaleHigherDirectImageBound_of_isAffine`: the affine
  case of part (1).
* `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_lt_top_of_finiteType`:
  **part (1)**, from the affine case through the reduction
  `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_lt_top_of_finiteType_of_isAffine`
  (in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteTypeReduction`).

Part (2), `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_lt_top_of_finiteType`, is
proved in the module
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteTypeAbsolute`.

## Proof

Part (1) follows the source. The question is local on `Y`
(`Scheme.Hom.etaleCohomologicalDimension_lt_top_of_openCover`), so `Y` may be taken affine.
The induction principle of [Stacks, Tag 08DR], with the relative Mayer--Vietoris sequence of
[Stacks, Tag 0EYK] as its step
(`Scheme.Hom.etaleCohomologicalDimension_lt_top_of_isAffine_source`), reduces to an affine source.
Then the morphism is affine, and [Stacks, Tag 0F0X] says `R^q f_*F` is supported in `E_{a - q}(Y)`.
Here `a` bounds the transcendence degrees of all residue fields of the source
(`AlgebraicGeometry.exists_trdeg_residueField_le`), so `E_{a - q}(Y)` is empty for `q > a`. The
input [Stacks, Tag 0F0W] of [Stacks, Tag 0F0X] is
`AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_trdegLESet`.

Part (2) follows the source too. The induction principle of [Stacks, Tag 08DR], with the
Mayer--Vietoris sequence of [Stacks, Tag 0A50] as its step
(`Scheme.etaleCohomologicalDimension_lt_top_of_isAffineOpen`), reduces to an affine scheme.
There [Stacks, Tag 0F0V] bounds `cd(X)` by `dim X + cd(K)`, which is finite.

## Implementation notes

The structure morphisms are given as morphisms to `Spec K` that are locally of finite type
and quasi-compact, i.e. of finite type. The quasi-compactness and quasi-separatedness that the
definitions of `cd` require are consequences: a scheme of finite type over a field is
Noetherian. They are constructed in the statements, not assumed.

## References

* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **The affine case of part (1).** A morphism `g : Z ⟶ V` of affine schemes of finite type
over a field `K` has a finite bound on the higher direct images of torsion sheaves. It is
affine, the transcendence degrees of the residue fields of `Z` are bounded by some `a`
(`AlgebraicGeometry.exists_trdeg_residueField_le`), so every sheaf on `Z` is supported in
`E_a(Z)`, and [Stacks, Tag 0F0X] gives `R^q g_* F = 0` for `q > a`. -/
theorem Hom.exists_isEtaleHigherDirectImageBound_of_isAffine (K : Type u) [Field K]
    {Z V : Scheme.{u}} [IsAffine Z] [IsAffine V] (gX : Z ⟶ Spec (.of K))
    [LocallyOfFiniteType gX] (gY : V ⟶ Spec (.of K)) [LocallyOfFiniteType gY] (g : Z ⟶ V)
    (hfg : g ≫ gY = gX) : ∃ d : ℕ, IsEtaleHigherDirectImageBound g d := by
  have : QuasiCompact gX := @quasiCompact_of_compactSpace _ _ gX inferInstance inferInstance
  have : IsAffineHom g := isAffineHom_of_isAffine g
  obtain ⟨a, ha⟩ := exists_trdeg_residueField_le K gX
  exact ⟨a, fun F hF q hq =>
    isZero_rightDerived_etaleAbelianDirectImage_of_lt K gX gY
      g hfg a F hF (fun z _ => ha z) q (by exact_mod_cast hq)⟩

/-- **Stacks Project, Tag 0F10, part (1).** A morphism `f : X ⟶ Y` of schemes of finite type
over a field `K` has finite cohomological dimension: `cd(f) < ∞`. -/
@[stacks 0F10 "(1): cd(f) < ∞ for a morphism of schemes of finite type over a field"]
theorem Hom.etaleCohomologicalDimension_lt_top_of_finiteType (K : Type u) [Field K]
    {X Y : Scheme.{u}} (x : X ⟶ Spec (.of K)) [LocallyOfFiniteType x] [QuasiCompact x]
    (y : Y ⟶ Spec (.of K)) [LocallyOfFiniteType y] [QuasiCompact y] (f : X ⟶ Y)
    (hf : f ≫ y = x) :
    haveI := quasiCompact_of_finiteType K x y f
    haveI := quasiSeparated_of_finiteType K x f
    f.etaleCohomologicalDimension < ⊤ :=
  Hom.etaleCohomologicalDimension_lt_top_of_finiteType_of_isAffine K x y f hf
    fun gX _ gY _ g hg => Hom.exists_isEtaleHigherDirectImageBound_of_isAffine K gX gY g hg

end AlgebraicGeometry.Scheme

end
