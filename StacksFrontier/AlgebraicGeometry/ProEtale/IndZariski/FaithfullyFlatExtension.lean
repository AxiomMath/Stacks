module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.Permanence
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.IdentifiesLocalRingsIndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitIndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitUniversal
public import StacksCore.Tactic.StacksAttribute

/-!
# Faithfully flat ind-Zariski extensions of a map identifying local rings

A ring map `A → B` identifying local rings becomes ind-Zariski after a faithfully flat
ind-Zariski extension of its target.

## Main results

* `AlgebraicGeometry.ProEtale.exists_faithfullyFlat_indZariski_extension`: the extension.

## Implementation notes

The extension is the w-localization `B → B_w` of Tag 0975, which is faithfully flat and
ind-Zariski. Since `Spec B_w` is w-local, the composite `A → B_w` factors uniquely through the
w-localization `A → A_w` by a map whose induced map of spectra is w-local, and that map
`A_w → B_w` identifies local rings; so it is ind-Zariski by Tag 097F, and therefore so is
`A → A_w → B_w`.

Both rings lie in their own universe, and the index universe of each ind-Zariski presentation
is raised to their maximum so that the three assertions speak of one notion.

## References

* [Stacks Project, Tag 097G](https://stacks.math.columbia.edu/tag/097G)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace AlgebraicGeometry.ProEtale

/-- A map identifying local rings becomes ind-Zariski after a faithfully flat
ind-Zariski extension of its target. -/
@[stacks 097G]
theorem exists_faithfullyFlat_indZariski_extension
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : letI := f.toAlgebra; Algebra.IdentifiesLocalRings A B) :
    ∃ (B' : Type v) (_ : CommRing B') (g : B →+* B'),
      g.FaithfullyFlat ∧
        (letI := g.toAlgebra; IsIndZariski.{v, v, max u v} B B') ∧
        (letI := (g.comp f).toAlgebra;
          IsIndZariski.{u, v, max u v} A B') := by
  let := f.toAlgebra
  let Bw := stratificationColimitRing (A := B)
  let g : B →+* Bw := stratificationColimitAlgebraMap
  let : Algebra B Bw := g.toAlgebra
  let : Algebra A Bw := (g.comp f).toAlgebra
  have : IsScalarTower A B Bw := .of_algebraMap_eq' (by ext a; rfl)
  have hB : IsIndZariski.{v, v, max u v} B Bw :=
    indZariski_lift_index_universe.{v, v, v, max u v} B Bw
      (stratificationColimit_isIndZariski (A := B))
  have hAB_local : Algebra.IdentifiesLocalRings A Bw :=
    identifiesLocalRings_comp A B Bw hf
      (identifiesLocalRings_of_isIndZariski B Bw hB)
  obtain ⟨j, hj, _⟩ := existsUnique_wLocal_lift A Bw (g.comp f)
  let : Algebra A (stratificationColimitRing (A := A)) :=
    stratificationColimitAlgebraMap.toAlgebra
  let : Algebra (stratificationColimitRing (A := A)) Bw := j.toAlgebra
  have hTower : IsScalarTower A (stratificationColimitRing (A := A)) Bw :=
    .of_algebraMap_eq
      (fun x => congrArg (fun φ : A →+* Bw => φ x) hj.1.symm)
  have hAw_local : Algebra.IdentifiesLocalRings
      (stratificationColimitRing (A := A)) Bw :=
    identifiesLocalRings_of_left_of_comp A _ Bw
      (identifiesLocalRings_of_isIndZariski A _
        stratificationColimit_isIndZariski)
      hAB_local
  let : WLocalSpace (PrimeSpectrum (stratificationColimitRing (A := A))) :=
    stratificationLimitScheme_wLocal (A := A)
  let : WLocalSpace (PrimeSpectrum Bw) := stratificationLimitScheme_wLocal (A := B)
  have hAwInd : IsIndZariski (stratificationColimitRing (A := A)) Bw :=
    isIndZariski_of_wLocalMap_identifiesLocalRings hAw_local hj.2
  refine ⟨Bw, inferInstance, g, stratificationColimit_faithfullyFlat, hB, ?_⟩
  simpa [g, hj.1] using Algebra.IsIndZariski.comp A
    (stratificationColimitRing (A := A)) Bw stratificationColimit_isIndZariski hAwInd

end AlgebraicGeometry.ProEtale

end
