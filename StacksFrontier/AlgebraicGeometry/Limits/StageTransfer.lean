module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeOverZ

/-!
# Transferring Tag 0E21 from a stage back to the limit

The Stacks proof of [Stacks, Tag 0E21] writes a scheme `X` carrying an ample invertible sheaf as
a limit `X = lim Xᵢ` of schemes of finite type over `ℤ` with affine transition morphisms
([Stacks, Tag 01ZA]), descends the ample sheaf and the open subscheme to one stage
([Stacks, Tag 09MT], [Stacks, Tag 0B8W], [Stacks, Tag 01Z4]), and then says "we may replace
`X, W, L` by `Xᵢ, Wᵢ, Lᵢ`".

That sentence is a *reduction*, and reading it as one leaves a step unwritten: the conclusion of
the tag is a statement about `X`, so whatever is proved at the stage has to be carried back along
the projection `p : X ⟶ Xᵢ`. This file is that step. It is independent of how the stage was
obtained — no limit, no cofiltered index category and no descent appears below, only a single
affine morphism `p` together with the data that the descent produces: an ample invertible sheaf
`M` on the target, an isomorphism `L ≅ p^* M`, and an open `V` with `W = p⁻¹ V`.

Each of the three conclusions of the tag transfers by its own mechanism, and the only one that
uses `p` being affine is the first:

* `X_s` is affine because `X_s = p⁻¹ (Y_{s'})` — this is
  `AlgebraicGeometry.Scheme.Modules.nonvanishingOpen_pullbackTensorPowerIso` for the pulled-back
  section — and the preimage of an affine open along an affine morphism is affine
  (`AlgebraicGeometry.IsAffineOpen.preimage`);
* `X_s ⊆ W` because taking preimages is monotone and `W = p⁻¹ V`;
* `Spec A ⟶ W` factors through `X_s` because its composite with `p` factors through `Y_{s'}`, and
  a morphism whose image lies in an open subscheme factors through it
  (`AlgebraicGeometry.exists_factorsThrough_of_range_subset`).

## Main results

* `exists_affine_nonvanishingOpen_factorsThrough_of_pullback`, in the namespace
  `AlgebraicGeometry.Scheme.Modules`: [Stacks, Tag 0E21] for `X`, given the tag at an affine
  target `Y` of finite type over `ℤ` and the descent data relating the two.

## Implementation notes

The statement at the target is
`AlgebraicGeometry.Scheme.Modules.exists_affine_nonvanishingOpen_containing_range`, whose
hypothesis is finite *presentation* over `ℤ`; it is applied here at the finite-*type* hypothesis
that Noetherian approximation delivers, through the instance
`AlgebraicGeometry.isLocallyNoetherian_terminal`.

Ampleness is a hypothesis on `M` and *not* on `L`: the tag's `hL : IsAmple X L` is spent only to
produce the stage, which here is given. So nothing below needs `X` to be quasi-compact or
quasi-separated.

The isomorphism is oriented `L ≅ p^* M`, which is the orientation
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit_of_qcqs`
([Stacks, Tag 0B8W] (2)) produces; the section is carried across it by
`Stacks.SheafOfModules.Invertible.tensorPowerCongr`. The invertibility of `p^* M` is not found by
instance search and is supplied inside the proof by [Stacks, Tag 0B8L], which is why it does not
appear in the statement.

No `@[stacks 0E21]` attribute is attached. This file removes one of the two obstructions that sit
between Noetherian approximation and the tag, and the other one remains: [Stacks, Tag 07RN] has
no inhabitant in this repository, so no stage exists to apply this to.

## References

* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- **[Stacks, Tag 0E21] transferred from a stage back to the limit.**

Let `p : X ⟶ Y` be an affine morphism onto a scheme `Y` of finite type over `ℤ`, let `M` be an
ample invertible sheaf on `Y`, let `L` be an invertible sheaf on `X` isomorphic to `p^* M`, and
let `W = p⁻¹ V` for an open `V ⊆ Y`.  Then Tag 0E21 holds for `X`, `L` and `W`: for a family of
points of `W` parametrised by an integral algebra over a field, some positive tensor power of `L`
has a global section `s` with `X_s` affine, `X_s ⊆ W`, and `Spec A ⟶ W` factoring through `X_s`.

These hypotheses are exactly what the Stacks proof of the tag obtains from Noetherian
approximation and descent: `p` is the projection from the limit to a stage, affine because the
transition morphisms are, `M` and `V` are the descended sheaf and open, and the isomorphism is
the descent datum. -/
theorem exists_affine_nonvanishingOpen_factorsThrough_of_pullback
    (k : Type v) (A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.IsIntegral k A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsAffineHom p]
    [LocallyOfFiniteType (terminal.from Y)]
    (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M]
    (hM : IsAmple Y M)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (e : L ≅ (Scheme.Modules.pullback p).obj M)
    (V : Y.Opens) (W : X.Opens) (hW : W = p ⁻¹ᵁ V)
    (f : Spec (CommRingCat.of A) ⟶ (W : Scheme.{u})) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
      ∃ U : X.Opens,
        U = nonvanishingOpen
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
        IsAffineOpen U ∧ U ≤ W ∧
        ∃ g : Spec (CommRingCat.of A) ⟶ (U : Scheme.{u}), g ≫ U.ι = f ≫ W.ι := by
  -- push the family of points down to `Y` and factor it through `V`
  have hVrange : Set.range (f ≫ W.ι ≫ p).base ⊆ (V : Set Y) := by
    rintro _ ⟨y, rfl⟩
    exact hW.le (f.base y).property
  obtain ⟨f', hf'⟩ := exists_factorsThrough_of_range_subset V (f ≫ W.ι ≫ p) hVrange
  -- the tag at the stage
  obtain ⟨n, hn, s, haff, hsV, hrange⟩ :=
    exists_affine_nonvanishingOpen_containing_range k A Y M hM V f'
  -- carry the section back along `p` and across the descent datum
  have ip : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback p).obj M) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback p.toLRSHom.toShHom M
  have ep := tensorPowerCongr X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property
    ((Scheme.Modules.pullback p).obj M) L e.symm n
  refine ⟨n, hn, SheafOfModules.sectionsMap ep.hom
    (SheafOfModules.sectionsMap (pullbackTensorPowerIso p M n).hom
      (modulePullbackSection p.toLRSHom _ s)), p ⁻¹ᵁ nonvanishingOpen
        (tensorPower Y.toRingedSpace.presheaf
          (structureSheafRing Y.toRingedSpace).property M (n : ℤ)) s, ?_, ?_, ?_, ?_⟩
  · exact ((TopologicalSpace.Opens.ext
      (nonvanishingLocus_sectionsMap X.toRingedSpace ep _)).trans
        (nonvanishingOpen_pullbackTensorPowerIso p M n s)).symm
  · exact haff.preimage p
  · rw [hW]
    exact fun x hx => hsV hx
  · refine exists_factorsThrough_of_range_subset _ (f ≫ W.ι) ?_
    rintro _ ⟨y, rfl⟩
    have h1 := hrange ⟨y, rfl⟩
    rw [hf'] at h1
    simpa using h1

end AlgebraicGeometry.Scheme.Modules

end
