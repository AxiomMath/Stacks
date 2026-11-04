module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MultiplierCancellation

/-!
# A relation between the sections `t_i` is a relation between the multipliers of Tag 0BD7

`Stacks.InvertiblePullback.restrictₛₗ_eq_smul_of_isPullMeromorphicFamily` transports a relation
between the meromorphic multipliers `g_i` of [Stacks, Tag 0BD7] down to the regular sections
`t_i` they produce. This file is the converse direction, which is the one the penultimate
paragraph of the proof actually needs: the sections `t_i` and `t_j` are two generators of an
invertible `ℒ` on the overlap of their generating loci, so they differ there by a section `c` of
`𝒪_X`, and that relation has to be pushed back up to the multipliers before the uniqueness
sentence can be applied to them.

## Main results

* `Stacks.InvertiblePullback.restrict_pullback_eq_mul_of_isPullMeromorphicFamily`: if `t_i` and
  `t_j` differ on `W` by `c : 𝒪_X(W)`, then the pullbacks of `g_i` and `g_j` differ on `W` by
  the image of `c` in `𝒦_X(W)`.

## Implementation notes

The scalar `c` lives in `𝒪_X(W)` and acts on `𝒦_X(ℒ)(W)` through the restriction of scalars of
`AlgebraicGeometry.meromorphicSectionSheafAsModule`, while the conclusion multiplies by its
image in `𝒦_X(W)`; the two actions are equal by `rfl` but neither spelling of the scalar finds
the other's instance. The linearity steps are therefore stated with the target element bound as
a variable of the `𝒦_X`-module type and supplied by `rfl` at the call site: that fixes the
instance at elaboration time instead of leaving it to be searched for at the wrong type.

The last step is a chain of `Eq.trans` rather than a `rw`. The two spellings of multiplication
by `s` — the one `AlgebraicGeometry.IsRegularMeromorphicSection` carries and the one
`AlgebraicGeometry.meromorphicSectionSheaf` produces — are equal only by `rfl`, so `rw` cannot
see through them and a `rw` of the linearity step is a deterministic `whnf` timeout.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Meromorphic

universe u

namespace Stacks.InvertiblePullback

/-- **A relation between the sections is a relation between the multipliers.** If `t_i` and `t_j`
differ on an open `W` of both preimages by a section `c` of `𝒪_X`, then the pullbacks of the
multipliers `g_i` and `g_j` differ there by the image of `c`, the factor `s` being regular. -/
theorem restrict_pullback_eq_mul_of_isPullMeromorphicFamily
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (L : _root_.SheafOfModules.{u} (_root_.structureSheafRing X.toRingedSpace))
    (s : MeromorphicSection X.sheaf L) {ι : Type*} {A : ι → Y.Opens}
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier)))
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamily f L s g t)
    (i j : ι) {W : Opens X.toRingedSpace.carrier}
    (hWi : W ≤ (f ⁻¹ᵁ A i : X.Opens)) (hWj : W ≤ (f ⁻¹ᵁ A j : X.Opens))
    (c : X.presheaf.obj (op W))
    (hc : L.val.restrictₛₗ (homOfLE hWi).op (t i)
      = c • L.val.restrictₛₗ (homOfLE hWj).op (t j)) :
    ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.totalQuotientSheaf).obj.map (homOfLE hWi).op).hom
          (((Scheme.ringSheafPullbackOfFlat f).hom.app (op (A i))).hom (g i))
      = ((toTotalQuotientRingSheaf X).hom.app (op W)).hom c *
        ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.totalQuotientSheaf).obj.map (homOfLE hWj).op).hom
            (((Scheme.ringSheafPullbackOfFlat f).hom.app (op (A j))).hom (g j)) := by
  have key : ∀ (k : ι) (hWk : W ≤ (f ⁻¹ᵁ A k : X.Opens)),
      (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app (op W)).hom
          (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.totalQuotientSheaf).obj.map (homOfLE hWk).op).hom
              (((Scheme.ringSheafPullbackOfFlat f).hom.app (op (A k))).hom (g k)))
        = (((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom
            (L.val.restrictₛₗ (homOfLE hWk).op (t k)) :
              ↑((meromorphicSectionSheaf X.sheaf L).val.obj (op W))) := by
    intro k hWk
    rw [← restrict_pullbackMeromorphicMul_val_app f L s (A k) hWk (g k), ht k]
    exact (PresheafOfModules.naturality_apply (toMeromorphicSectionSheafAsModule X L).val
      (homOfLE hWk).op (t k)).symm
  have hlin : ∀ (y : ↑(L.val.obj (op W)))
      (v : ↑((meromorphicSectionSheaf X.sheaf L).val.obj (op W))),
      ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom y = v →
      ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom (c • y)
        = ((toTotalQuotientRingSheaf X).hom.app (op W)).hom c • v := by
    rintro y v rfl
    exact LinearMap.map_smul ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom c y
  have hmul : ∀ (z : ↑((Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf).obj.obj (op W)))
      (v : ↑((meromorphicSectionSheaf X.sheaf L).val.obj (op W))),
      (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app (op W)).hom z = v →
      (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app (op W)).hom
          (((toTotalQuotientRingSheaf X).hom.app (op W)).hom c * z)
        = ((toTotalQuotientRingSheaf X).hom.app (op W)).hom c • v := by
    rintro z v rfl
    rw [← smul_eq_mul]
    exact map_smul _ _ _
  have hstep := hlin (L.val.restrictₛₗ (homOfLE hWj).op (t j)) _ rfl
  exact CategoryTheory.SheafOfModules.app_injective_of_mono hs (op W)
    (((key i hWi).trans (congrArg (fun y =>
        ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom y) hc)).trans
      (hstep.trans (hmul _ _ (key j hWj)).symm))

end Stacks.InvertiblePullback

end
