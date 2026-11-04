module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasiAffineDivisorRepresentation

/-!
# Extending an invertible module across a factorial locus: the affine-chart step

Let `W` be a Noetherian scheme and `V ⊆ W` an open subscheme which is quasi-affine. If the local
ring `𝒪_{W, x}` is a unique factorization domain at every point `x` outside `V`, then every
invertible `𝒪_V`-module is the restriction of an invertible `𝒪_W`-module.

This is the local step of [Stacks, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9) — the
part of its proof that produces an extension over one affine chart. The tag itself is
`AlgebraicGeometry.exists_isInvertible_pullback_iso_of_isLocallyNoetherian`.

## The argument

The proof has three steps:

* `V` is quasi-affine and Noetherian, so the invertible module `L` on it is the invertible sheaf
  of a single effective Cartier divisor `D ⊆ V`, by the quasi-affine case of Tag 0AYM
  (`Stacks.Divisors.exists_isEffectiveCartierDivisor_iso_invertibleSheaf_of_isQuasiAffine`);
* `D` extends to an effective Cartier divisor `D' ⊆ W` with `D'|_V = D`, by Tag 0BD8
  (`AlgebraicGeometry.exists_isEffectiveCartierDivisor_comap_eq`) — this is where the unique
  factorization hypothesis outside `V` is used, and the only place;
* `𝒪_W(D')` is invertible (Tag 01WX (1)) and restricts to `𝒪_V(D'|_V) = 𝒪_V(D) ≅ L`, because the
  invertible sheaf of a divisor commutes with a pullback along which the divisor pulls back —
  Tag 0C4U (`Stacks.Divisors.invertibleSheafPullbackIso`), whose hypothesis holds for the open
  immersion `V.ι` because it is flat (`Stacks.Divisors.isPullbackDefined_of_flat`).

Restriction to the open subscheme is written as pullback along the canonical open immersion
`V.ι`, which is the spelling Tag 0BD8 and Tag 0C4U are both stated at.

## Main results

* `AlgebraicGeometry.exists_isInvertible_pullback_iso_of_isQuasiAffine_of_uniqueFactorization`:
  the extension, for a quasi-affine open of a Noetherian scheme.
* `AlgebraicGeometry.exists_isInvertible_pullback_iso_of_isAffine_of_uniqueFactorization`: the
  same for an arbitrary open of a Noetherian *affine* scheme, where quasi-affineness is
  automatic.

## References

* [Stacks Project, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9)
* [Stacks Project, Tag 0BD8](https://stacks.math.columbia.edu/tag/0BD8)
* [Stacks Project, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM)
* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The affine-chart step of [Stacks, Tag 0BD9].** Let `W` be a Noetherian scheme and `V ⊆ W`
a quasi-affine open subscheme whose complement consists of points with unique factorization local
rings. Then every invertible `𝒪_V`-module is the restriction of an invertible `𝒪_W`-module. -/
theorem exists_isInvertible_pullback_iso_of_isQuasiAffine_of_uniqueFactorization
    {W : Scheme.{u}} [IsNoetherian W] (V : W.Opens) [V.toScheme.IsQuasiAffine]
    (L : V.toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property L]
    (hUFD : ∀ x : W, x ∉ V → UniqueFactorizationMonoid (W.presheaf.stalk x)) :
    ∃ M : W.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property M ∧
        Nonempty (L ≅ (Scheme.Modules.pullback V.ι).obj M) := by
  have : IsNoetherian V.toScheme := (isNoetherian_iff V.toScheme).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨D, hD, ⟨e⟩⟩ :=
    Stacks.Divisors.exists_isEffectiveCartierDivisor_iso_invertibleSheaf_of_isQuasiAffine
      V.toScheme L
  obtain ⟨D', hD', hcomap⟩ := exists_isEffectiveCartierDivisor_comap_eq V D hD hUFD
  have : Stacks.Divisors.IsPullbackDefined V.ι D' :=
    Stacks.Divisors.isPullbackDefined_of_flat V.ι D' hD'
  exact ⟨Stacks.Divisors.invertibleSheaf' D', inferInstance,
    ⟨e.trans ((eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hcomap.symm)).trans
      (Stacks.Divisors.invertibleSheafPullbackIso V.ι D').symm)⟩⟩

/-- **The affine-chart step of [Stacks, Tag 0BD9], on an affine chart.** Every invertible module
on an open subscheme of a Noetherian affine scheme whose complementary points have unique
factorization local rings is the restriction of an invertible module. -/
theorem exists_isInvertible_pullback_iso_of_isAffine_of_uniqueFactorization
    {W : Scheme.{u}} [IsNoetherian W] [IsAffine W] (V : W.Opens) (L : V.toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property L]
    (hUFD : ∀ x : W, x ∉ V → UniqueFactorizationMonoid (W.presheaf.stalk x)) :
    ∃ M : W.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property M ∧
        Nonempty (L ≅ (Scheme.Modules.pullback V.ι).obj M) := by
  have : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (V : Set W))
  have : V.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion V.ι
  exact exists_isInvertible_pullback_iso_of_isQuasiAffine_of_uniqueFactorization V L hUFD

end AlgebraicGeometry

end
