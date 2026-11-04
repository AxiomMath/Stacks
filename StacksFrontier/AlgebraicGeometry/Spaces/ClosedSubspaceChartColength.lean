module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthStructureSheaf

/-!
# The multiplicity of a closed subspace at a geometric point, as a colength on an affine chart

Let `Y ⊆ X` be a closed subspace of an algebraic space, `ȳ` a geometric point of `Y` and `U` an
*affine* étale scheme chart of `X` which is a small étale neighbourhood of the image of `ȳ`, with
marked point `a`.  Then the length of `𝒪_Y` at `ȳ` — the multiplicity with which a component of
`Y` enters the cycle `[Y]_k` of Stacks 0EE9 — is the colength in `𝒪_{U, a}` of the stalk at `a`
of the defining ideal of `Y` on `U`:

  `length_{𝒪_{Y, ȳ}}(𝒪_{Y, ȳ})  =  length_{𝒪_{U, a}}(𝒪_{U, a} / 𝓘_a)`,  `𝓘 = I(Y)(U)`.

## Main results

* `AlgebraicGeometry.Space.geometricLength_unit_eq_length_quotient_definingIdealAt`: the
  identity above, with the defining ideal written as
  `AlgebraicGeometry.Space.definingIdealAt`, the ideal of `𝒪_X(U)` cut out by `Y`.

## Implementation notes

Three facts from the library are composed.
`AlgebraicGeometry.Space.geometricLength_unit_eq_length_chartLocalRing` — Stacks 0EE1 for the
structure sheaf — moves the geometric length of `𝒪_Y` to the local ring of *any* scheme chart of
`Y` at the induced point, and the chart taken is the base change `Y ×_X U`, which
`AlgebraicGeometry.Space.SmallEtaleNeighborhood.baseChange` produces.
`AlgebraicGeometry.Space.length_chartLocalRing_baseChange` turns that length into the colength in
`𝒪_{U, a}` of the stalk of the ideal sheaf of the closed immersion of chart schemes
`Y ×_X U ⟶ U`; its affine-open hypothesis is discharged with `U` itself, which is where
affineness of the chart is used and nowhere else.  Finally that stalk is the image of the global
ideal: `AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ` on the affine open `⊤`,
`AlgebraicGeometry.Scheme.Hom.ker_apply` — whose `QuasiCompact` hypothesis is supplied by the
closed immersion — and `AlgebraicGeometry.Space.definingIdealAt_eq_ker`, which is stated against
the very same morphism of chart schemes.

No quasi-coherence of anything is needed: the module whose length is taken is the structure
sheaf of `Y`, not a pushforward of it.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (Y : Subfunctor X) (hY : IsClosedSubspace B S hS Y)

/-- **The multiplicity of a closed subspace at a geometric point is a colength on an affine
étale chart of the ambient space.**  For a closed subspace `Y ⊆ X`, a geometric point `ȳ` of `Y`
and an affine small étale neighbourhood `A` of its image in `X` whose marked point projects to
`a`, the length of `𝒪_Y` at `ȳ` is the colength in `𝒪_{A, a}` of the stalk at `a` of the
defining ideal of `Y` over `A`.

The ambient point is carried as the variable `a` with the equation `ha` identifying it, exactly
as in `AlgebraicGeometry.Space.length_chartLocalRing_baseChange`, so that the dependent types of
the statement stay correct; `AlgebraicGeometry.Space.chartPoint_baseChange` discharges `ha` with
`a` the marked point of `A`. -/
theorem geometricLength_unit_eq_length_quotient_definingIdealAt
    (z : GeometricPoint B S hS Y.toFunctor)
    (A : SmallEtaleNeighborhood (geometricPointMap (closedSubspaceHom B S hS hX Y hY).hom z))
    (haff : IsAffine (chartScheme A.chart))
    (a : chartScheme A.chart)
    (ha : ((BigFppfOver.toScheme B S hS).map (hY.2.rep.snd A.chart.1.hom)).base
      (chartPoint B S hS Y.toFunctor
        ((SmallEtaleNeighborhood.baseChange B S hS (closedSubspaceHom B S hS hX Y hY)
          hY.2.rep z).obj A)) = a) :
    geometricLength B S hS ⟨Y.toFunctor, hY.1⟩ z (SheafOfModules.unit _) =
      Module.length ↥((chartScheme A.chart).presheaf.stalk a)
        (↥((chartScheme A.chart).presheaf.stalk a) ⧸
          Ideal.map ((chartScheme A.chart).presheaf.germ ⊤ a trivial).hom
            (definingIdealAt B S hS ⟨X, hX⟩ ⟨Y, hY⟩ (op A.chart))) := by
  let : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hY.2.rep.snd A.chart.1.hom)) :=
    hY.2.property_snd A.chart.1.hom
  have hideal : AlgebraicGeometry.IdealSheafData.stalk
      (Scheme.Hom.ker ((BigFppfOver.toScheme B S hS).map (hY.2.rep.snd A.chart.1.hom))) a =
      Ideal.map ((chartScheme A.chart).presheaf.germ ⊤ a trivial).hom
        (definingIdealAt B S hS ⟨X, hX⟩ ⟨Y, hY⟩ (op A.chart)) := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ
        (Scheme.Hom.ker ((BigFppfOver.toScheme B S hS).map (hY.2.rep.snd A.chart.1.hom))) a
        ⟨⊤, isAffineOpen_top (chartScheme A.chart)⟩ trivial,
      AlgebraicGeometry.Scheme.Hom.ker_apply
        ((BigFppfOver.toScheme B S hS).map (hY.2.rep.snd A.chart.1.hom))
        ⟨⊤, isAffineOpen_top (chartScheme A.chart)⟩,
      definingIdealAt_eq_ker B S hS ⟨X, hX⟩ ⟨Y, hY⟩ A.chart]
    rfl
  rw [geometricLength_unit_eq_length_chartLocalRing B S hS ⟨Y.toFunctor, hY.1⟩ z
      ((SmallEtaleNeighborhood.baseChange B S hS (closedSubspaceHom B S hS hX Y hY)
        hY.2.rep z).obj A),
    length_chartLocalRing_baseChange B S hS (closedSubspaceHom B S hS hX Y hY)
      (isClosedImmersion_closedSubspaceHom B S hS hX Y hY) z A a ha ⊤
      (isAffineOpen_top (chartScheme A.chart)) trivial]
  exact congrArg (fun I : Ideal ↥((chartScheme A.chart).presheaf.stalk a) =>
    Module.length ↥((chartScheme A.chart).presheaf.stalk a)
      (↥((chartScheme A.chart).presheaf.stalk a) ⧸ I)) hideal

end AlgebraicGeometry.Space

end
