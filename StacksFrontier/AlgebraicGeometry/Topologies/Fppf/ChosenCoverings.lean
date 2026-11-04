module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.BigSite
public import StacksCore.Tactic.StacksAttribute

/-!
# The Zariski, étale, smooth and syntomic sites carried by a chosen big fppf site

Having chosen a big fppf site `Sch_fppf`, one does *not* repeat the construction of a
size-bounded category of schemes for the coarser topologies. The big Zariski, étale, smooth
and syntomic sites are declared to have the *same* underlying category `Sch_κ`, and their
covering families are the sub-collection of the chosen fppf covering families which happen
to be coverings for the respective topology.

This file records those four sub-collections, the precoverage each presents, and the
Grothendieck topology each generates.

## Main definitions

* `AlgebraicGeometry.BigFppfSite.zariskiCovering`,
  `AlgebraicGeometry.BigFppfSite.etaleCovering`,
  `AlgebraicGeometry.BigFppfSite.smoothCovering` and
  `AlgebraicGeometry.BigFppfSite.syntomicCovering` are the four sub-collections of the
  chosen fppf covering families of a big fppf site.
* `AlgebraicGeometry.BigFppfSite.chosenPrecoverage` presents an arbitrary collection of
  covering families of `Sch_κ` as a precoverage, and the four `*Precoverage`
  abbreviations apply it to the four sub-collections.
* `AlgebraicGeometry.BigFppfSite.zariskiTopology`,
  `AlgebraicGeometry.BigFppfSite.etaleTopology`,
  `AlgebraicGeometry.BigFppfSite.smoothTopology` and
  `AlgebraicGeometry.BigFppfSite.syntomicTopology` are the topologies they generate.

## Main results

* `AlgebraicGeometry.BigFppfSite.mem_chosenPrecoverage_iff`: membership in `chosenPrecoverage`
  is characterized by a presenting covering family.
* `AlgebraicGeometry.BigFppfSite.isFppfCovering_of_isZariskiCovering`: a Zariski covering family
  of `Sch_κ` is an fppf covering family.
* `AlgebraicGeometry.BigFppfSite.zariskiCovering_has_representative`: every Zariski covering
  family of `Sch_κ` is combinatorially equivalent to a chosen one.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfSite

variable (B : BigFppfSite.{u})

/-! ### The four sub-collections of the chosen fppf covering families -/

/-- The chosen Zariski covering families of `Sch_κ` are the chosen fppf covering families which are
Zariski coverings. -/
@[stacks 03FF "Zariski coverings"]
abbrev zariskiCovering (E : Covering B.Schemes) : Prop :=
  B.IsCovering E ∧ IsZariskiCovering E

/-- The chosen étale covering families of `Sch_κ` are the chosen fppf covering families which are
étale coverings. -/
@[stacks 03FF "étale coverings", sga "4 VII 1.2" "Cov X: étale coverings"]
abbrev etaleCovering (E : Covering B.Schemes) : Prop :=
  B.IsCovering E ∧ IsEtaleCovering E

/-- The chosen smooth covering families of `Sch_κ` are the chosen fppf covering families which are
smooth coverings. -/
@[stacks 03FF "smooth coverings"]
abbrev smoothCovering (E : Covering B.Schemes) : Prop :=
  B.IsCovering E ∧ SmoothCovering B.cutoff E

/-- The chosen syntomic covering families of `Sch_κ` are the chosen fppf covering families which
are syntomic coverings. -/
@[stacks 03FF "syntomic coverings"]
abbrev syntomicCovering (E : Covering B.Schemes) : Prop :=
  B.IsCovering E ∧ SyntomicCovering B.cutoff E

/-! ### The topologies they generate -/

/-- The precoverage presented by a chosen collection `P` of covering families of `Sch_κ`: a
presieve is covering exactly when some family in `P` presents it. -/
def chosenPrecoverage (P : Covering B.Schemes → Prop) : Precoverage B.Schemes where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X, R = E.presieve₀ ∧ P ⟨X, E⟩}

/-- Membership in `chosenPrecoverage` is characterized by a presenting covering family. -/
theorem mem_chosenPrecoverage_iff {P : Covering B.Schemes → Prop} {X : B.Schemes}
    {R : Presieve X} :
    R ∈ B.chosenPrecoverage P X ↔
      ∃ E : PreZeroHypercover.{u + 1} X, R = E.presieve₀ ∧ P ⟨X, E⟩ :=
  Iff.rfl

/-- The precoverage presented by the chosen Zariski covering families. -/
abbrev zariskiPrecoverage : Precoverage B.Schemes := B.chosenPrecoverage B.zariskiCovering

/-- The precoverage presented by the chosen étale covering families. -/
abbrev etalePrecoverage : Precoverage B.Schemes := B.chosenPrecoverage B.etaleCovering

/-- The precoverage presented by the chosen smooth covering families. -/
abbrev smoothPrecoverage : Precoverage B.Schemes := B.chosenPrecoverage B.smoothCovering

/-- The precoverage presented by the chosen syntomic covering families. -/
abbrev syntomicPrecoverage : Precoverage B.Schemes := B.chosenPrecoverage B.syntomicCovering

/-- The big Zariski topology carried by a chosen big fppf site. -/
@[stacks 03FF "Zariski topology"]
abbrev zariskiTopology : GrothendieckTopology B.Schemes :=
  B.zariskiPrecoverage.toGrothendieck

/-- The big étale topology carried by a chosen big fppf site. -/
@[stacks 03FF "étale topology", sga "4 VII 1.2" "étale topology on (Sch)"]
abbrev etaleTopology : GrothendieckTopology B.Schemes :=
  B.etalePrecoverage.toGrothendieck

/-- The big smooth topology carried by a chosen big fppf site. -/
@[stacks 03FF "smooth topology"]
abbrev smoothTopology : GrothendieckTopology B.Schemes :=
  B.smoothPrecoverage.toGrothendieck

/-- The big syntomic topology carried by a chosen big fppf site. -/
@[stacks 03FF "syntomic topology"]
abbrev syntomicTopology : GrothendieckTopology B.Schemes :=
  B.syntomicPrecoverage.toGrothendieck

/-! ### Representatives among the chosen Zariski covering families -/

/-- A Zariski covering family of `Sch_κ` is an fppf covering family. -/
theorem isFppfCovering_of_isZariskiCovering {E : Covering B.Schemes}
    (hE : IsZariskiCovering E) : IsFppfCovering (κ := B.cutoff) E := by
  change E.2.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion E.1
  rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
  exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hE

/-- Every Zariski covering family of `Sch_κ` is combinatorially equivalent to a chosen Zariski
covering family. -/
@[stacks 03FF "Zariski representatives"]
theorem zariskiCovering_has_representative (E : Covering B.Schemes)
    (hE : IsZariskiCovering E) :
    ∃ E' : Covering B.Schemes, B.zariskiCovering E' ∧ Covering.CombEquiv E E' := by
  obtain ⟨E', hE', hcomb⟩ :=
    B.fppf_has_representative E (B.isFppfCovering_of_isZariskiCovering hE)
  refine ⟨E', ⟨hE', ?_⟩, hcomb⟩
  obtain ⟨U, F⟩ := E
  obtain ⟨W, F'⟩ := E'
  obtain ⟨hobj, hce⟩ := hcomb
  cases hobj
  change (F'.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology U.1
  change (F.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology U.1 at hE
  rw [PreZeroHypercover.presieve₀_map] at hE ⊢
  rwa [← PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hce]

/-! ### The projections of the four sub-collections -/

/-- A chosen Zariski covering family is a chosen fppf covering family. -/
theorem isCovering_of_zariskiCovering {E : Covering B.Schemes} (hE : B.zariskiCovering E) :
    B.IsCovering E := hE.1

/-- A chosen Zariski covering family is a Zariski covering. -/
theorem isZariskiCovering_of_zariskiCovering {E : Covering B.Schemes}
    (hE : B.zariskiCovering E) : IsZariskiCovering E := hE.2

/-- A chosen étale covering family is a chosen fppf covering family. -/
theorem isCovering_of_etaleCovering {E : Covering B.Schemes} (hE : B.etaleCovering E) :
    B.IsCovering E := hE.1

/-- A chosen étale covering family is an étale covering. -/
theorem isEtaleCovering_of_etaleCovering {E : Covering B.Schemes} (hE : B.etaleCovering E) :
    IsEtaleCovering E := hE.2

/-- A chosen smooth covering family is a chosen fppf covering family. -/
theorem isCovering_of_smoothCovering {E : Covering B.Schemes} (hE : B.smoothCovering E) :
    B.IsCovering E := hE.1

/-- A chosen smooth covering family is a smooth covering. -/
theorem smoothCovering_of_smoothCovering {E : Covering B.Schemes}
    (hE : B.smoothCovering E) : SmoothCovering B.cutoff E := hE.2

/-- A chosen syntomic covering family is a chosen fppf covering family. -/
theorem isCovering_of_syntomicCovering {E : Covering B.Schemes} (hE : B.syntomicCovering E) :
    B.IsCovering E := hE.1

/-- A chosen syntomic covering family is a syntomic covering. -/
theorem syntomicCovering_of_syntomicCovering {E : Covering B.Schemes}
    (hE : B.syntomicCovering E) : SyntomicCovering B.cutoff E := hE.2

end AlgebraicGeometry.BigFppfSite
