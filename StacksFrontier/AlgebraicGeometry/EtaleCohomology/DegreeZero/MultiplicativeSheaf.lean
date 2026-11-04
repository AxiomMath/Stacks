module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Degree-zero étale cohomology of the multiplicative sheaf

Degree-zero cohomology of the multiplicative sheaf on the small étale site of a scheme is
canonically the group of global units: this is the first of the displayed identifications of
[Stacks, Tag 03QV], namely `H^0_étale(S_étale, 𝐆_m) = Γ(S, 𝒪_S^*)`.

## Main results

* `AlgebraicGeometry.etaleH0UnitsAddEquiv` identifies degree-zero cohomology of the small étale
  sheaf of units with the group of units of global functions, written additively.

## Implementation notes

Degree-zero sheaf cohomology is sections over a terminal object
(`CategoryTheory.Sheaf.H.equiv₀`), the small étale site of `S` has `S / S` for a terminal object
(`AlgebraicGeometry.SmallEtale.finalIsTerminal`), and the sections of the sheaf of units there
are the units of `Γ(S, 𝒪_S)`.  The field hypothesis of the source is unnecessary for this
identification: it is the degree-zero equality of the displayed chain, which the source itself
states for an arbitrary scheme `S`.

The group of units is written additively, as `Additive Γ(S, 𝒪_S)ˣ`, because that is the shape in
which the multiplicative sheaf is an abelian sheaf and therefore has cohomology at all.

## References

* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})]

/-- **Stacks 03QV, the degree-zero identification for `𝐆_m`**: `H^0_étale(S_étale, 𝐆_m)` is the
group `Γ(S, 𝒪_S^*)` of units of global functions, written additively.  Degree-zero sheaf
cohomology is sections over a terminal object, and `S / S` is terminal in the small étale site
of `S`. -/
def etaleH0UnitsAddEquiv :
    Sheaf.H.{w, u}
      (unitsSheaf (SmallEtale.topology B S hS) (SmallEtale.toScheme B S hS)
        (unitsPresheaf_isSheaf_smallEtale B S hS)) 0 ≃+
      Additive (Scheme.Γ.obj (op S))ˣ :=
  Sheaf.H.equiv₀ _ (SmallEtale.finalIsTerminal B S hS)

end AlgebraicGeometry

end
