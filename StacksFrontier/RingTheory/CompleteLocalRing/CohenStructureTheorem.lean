module

public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem.CoefficientRing
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem.PowerSeriesRing
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem.RegularSubring

/-!
# The Cohen structure theorem

This file re-exports its parts:

* `CohenStructureTheorem.CoefficientRing`: a complete local ring has a coefficient ring, and if
  its maximal ideal is finitely generated it is a quotient of a power series ring in finitely many
  variables over a field or over a Cohen ring
  (`IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries`, Stacks 032A);
* `CohenStructureTheorem.PowerSeriesRing`: the maximal ideal of a power series ring over a local
  ring, its completeness, and substitution into power series;
* `CohenStructureTheorem.RegularSubring`: a Noetherian complete local domain is finite over a
  regular power series subring (`IsLocalRing.exists_injective_finite_mvPowerSeries`,
  Stacks 032D).
-/
