module

public import Mathlib.FieldTheory.FinTrdeg
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.TranscendenceDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre

/-!
# Finiteness of the residue-field transcendence degree of a germ

For a morphism of schemes which is locally of finite type, the residue-field transcendence
degree at every point of the source is finite: the germ morphism induced at that point has
the residue-field transcendence degree of Tag 04NK equal to a natural number.

## Main results

* `AlgebraicGeometry.MorphismOfGerms.exists_natCast_hasResidueFieldTranscendenceDegree`: the
  germ morphism induced by a locally-finite-type scheme morphism at a point of its source
  has a finite residue-field transcendence degree.

## Implementation notes

The witness representative is the canonical one on the whole source scheme used by
`AlgebraicGeometry.MorphismOfGerms.ofSchemeHom`; its distinguished-point equality is
`rfl`, so the residue-field congruence appearing in the definition of Tag 04NK's property
is the identity and the induced algebra structure is literally the one coming from
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`.

Finiteness comes from `AlgebraicGeometry.residueField_essFiniteType_of_locallyOfFiniteType`:
the residue-field extension is essentially of finite type, hence has finite transcendence
degree by Mathlib's `FinTrdeg` instance for essentially-finite-type extensions.

## References

* [Stacks Project, Tag 04NK](https://stacks.math.columbia.edu/tag/04NK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.MorphismOfGerms

/-- A morphism of schemes which is locally of finite type has a finite residue-field
transcendence degree at every point of its source: the induced germ morphism satisfies the
condition of Tag 04NK for some natural number. -/
theorem exists_natCast_hasResidueFieldTranscendenceDegree {U V : Scheme.{u}} (g : U ⟶ V)
    [LocallyOfFiniteType g] (u : U) :
    ∃ n : ℕ, HasResidueFieldTranscendenceDegree (n : ℕ∞) (ofSchemeHom g u) := by
  classical
  let gr : Representative (⟨U, u⟩ : GermOfScheme.{u}) ⟨V, g u⟩ :=
    { source := ⊤
      mem_source := by simp
      hom := U.topIso.hom ≫ g
      map_point := rfl }
  let xg : gr.source.toScheme := ⟨u, gr.mem_source⟩
  have : LocallyOfFiniteType gr.hom := inferInstanceAs (LocallyOfFiniteType (U.topIso.hom ≫ g))
  let _ : Algebra (V.residueField (g u)) (gr.source.toScheme.residueField xg) :=
    (gr.hom.residueFieldMap xg).hom.toAlgebra
  have : Algebra.EssFiniteType (V.residueField (g u)) (gr.source.toScheme.residueField xg) :=
    residueField_essFiniteType_of_locallyOfFiniteType gr.hom xg
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0 (V.residueField (g u)) (gr.source.toScheme.residueField xg))
  exact ⟨n, gr, rfl, (congrArg Cardinal.toENat hn).trans (Cardinal.toENat_nat n)⟩

end AlgebraicGeometry.MorphismOfGerms

end
