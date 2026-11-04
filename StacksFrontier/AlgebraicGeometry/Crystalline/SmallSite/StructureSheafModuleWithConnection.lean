module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompleteComparisonStatements
public import StacksFrontier.AlgebraicGeometry.DeRham.StructureSheafTwistedDifferential
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent

/-!
# The structure sheaf as a coherent module with integrable connection

In the situation of [Stacks, Tag 07MZ] — `(A, I, γ)` a divided power ring with `A` Noetherian and
`p`-adically complete, `S = Spec(A)`, `Y` proper and smooth over `S` — the structure sheaf `𝒪_Y`
with its canonical relative connection `∇(b) = 1 ⊗ d b` is a coherent `𝒪_Y`-module equipped with
an integrable connection and the twisted de Rham differential of that connection, that is, a
`...SmallSite.Situation07MZ.CoherentModuleWithConnection`.

That bundle is what `...SmallSite.DeRhamComparison07MZ` existentially quantifies over, so this
file is what makes that statement one you can tell apart from a true-but-empty one: the
existential is over a type now known to be inhabited.

Three of the bundle's six fields come from
`StacksFrontier.AlgebraicGeometry.DeRham.StructureSheafConnection` and
`StacksFrontier.AlgebraicGeometry.DeRham.StructureSheafTwistedDifferential`: the canonical
connection, its twisted de Rham differential, and the square-zero property of that differential
together with the integrability it implies.  The one remaining field, coherence of `𝒪_Y`, is the
content of this file: `S = Spec(A)` is affine with `A` Noetherian, so `S` is locally Noetherian;
`Y ⟶ S` is proper, hence locally of finite type, so `Y` is locally Noetherian; and the structure
sheaf of a locally Noetherian scheme is coherent by
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`.

## Main definitions

Everything lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MZ`.

* `structureCoherentModuleWithConnection` — **the structure sheaf of `Y`, with its canonical
  connection, as a coherent module with integrable connection.**

## Main results

* `isLocallyNoetherian_base` and `isLocallyNoetherian_source` — in the situation of the remark
  the base `S` and the scheme `Y` are locally Noetherian.
* `isCoherent_structureSheaf` — **`𝒪_Y` is coherent**, [Stacks, Tag 01BV].

## What is and is not proved

What is proved is that the bundle `...SmallSite.DeRhamComparison07MZ` quantifies over is
inhabited, by the structure sheaf with its canonical connection.  Nothing here proves that
statement itself, or any part of it: the comparison
`RΓ(Cris(X/S), ℱ) = RΓ(Y, ℱ_Y ⊗ Ω^•_{Y/S})` relates a *given* crystal to a module with
connection built from it, and the module exhibited here is not built from a crystal at all.  Its
role is exactly to show that the target of that existential is not empty.

Nor is the structure sheaf claimed to be the `ℱ_Y` attached to any particular crystal; it is the
one attached to the structure crystal `𝒪_{X/S}` in the source, but the identification of `ℱ_Y`
with anything is the mod-`p^e` conjunct of clause (1) of the remark, which this library cannot
state — see the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompleteComparisonStatements`.

A propositional inhabitation lemma is deliberately *not* added: it would be a wrapper around the
witness below and strictly less informative than it, and a consumer wanting the propositional
form should write `⟨T.structureCoherentModuleWithConnection⟩`.

## References

* [Stacks Project, Tag 07MZ](https://stacks.math.columbia.edu/tag/07MZ)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MZ

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MZ S)

include T

/-- **In the situation of [Stacks, Tag 07MZ] the base `S` is locally Noetherian**: it is the
spectrum of the Noetherian ring `A`, so the one-element affine cover by the whole space has
Noetherian ring of sections. -/
theorem isLocallyNoetherian_base : IsLocallyNoetherian S.S.scheme :=
  have := T.isAffine
  AlgebraicGeometry.isLocallyNoetherian_of_affine_cover
    (S := fun _ : Unit => (⟨⊤, isAffineOpen_top S.S.scheme⟩ : S.S.scheme.affineOpens))
    (by simp) (fun _ => T.isNoetherianRing)

/-- **In the situation of [Stacks, Tag 07MZ] the scheme `Y` is locally Noetherian**: it is
locally of finite type over the locally Noetherian base, being proper over it. -/
theorem isLocallyNoetherian_source : IsLocallyNoetherian T.Y :=
  have := T.isProper
  have := T.isLocallyNoetherian_base
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian T.toBase

/-- **In the situation of [Stacks, Tag 07MZ] the structure sheaf of `Y` is coherent**,
[Stacks, Tag 01BV]: `Y` is locally Noetherian. -/
theorem isCoherent_structureSheaf :
    _root_.SheafOfModules.IsCoherent (_root_.SheafOfModules.unit T.Y.ringCatSheaf) :=
  have := T.isLocallyNoetherian_source
  Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit T.Y

/-- **The structure sheaf of `Y` with its canonical relative connection, as a coherent module
with integrable connection in the situation of [Stacks, Tag 07MZ]**: the module is `𝒪_Y`, which
is coherent because `Y` is locally Noetherian; the connection is
`AlgebraicGeometry.Scheme.Hom.structureModuleConnection`, `∇(b) = 1 ⊗ d b`; its twisted de Rham
differential is
`AlgebraicGeometry.Scheme.Hom.structureTwistedDeRhamDifferential`; and that differential squares
to zero, which gives both the complex property and integrability of the connection. -/
def structureCoherentModuleWithConnection : T.CoherentModuleWithConnection where
  module := _root_.SheafOfModules.unit T.Y.ringCatSheaf
  isCoherent := T.isCoherent_structureSheaf
  connection := AlgebraicGeometry.Scheme.Hom.structureModuleConnection T.toBase
  differential := AlgebraicGeometry.Scheme.Hom.structureTwistedDeRhamDifferential T.toBase
  isComplex :=
    AlgebraicGeometry.Scheme.Hom.structureTwistedDeRhamDifferential_isComplex T.toBase
  isIntegrable :=
    AlgebraicGeometry.Scheme.Hom.isIntegrable_structureModuleConnection T.toBase

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MZ

end

end
