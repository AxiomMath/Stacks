module

public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupCoherentNonzero

/-!
# The middle group of Tag 0FDF is inhabited by a genuine scheme and is not the zero group

The two identifications of [Stacks, Tag 0FDF] stated in
`StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupBoundedCoherent` quantify over a
`HasDerivedCategory` structure on `Coh(𝒪_X)`, and an identification of two groups is compatible
with both of them being zero. Neither defect is visible from the statements alone: the
first would make the statements vacuous, the second would make them empty. This file rules out
both for the middle group `K₀(D^b(Coh(𝒪_X)))`.

## Main results

* `AlgebraicGeometry.coherentModulesHasDerivedCategory`: a named inhabitant of the
  `HasDerivedCategory` datum of the middle group, assuming nothing about `X`.
* `AlgebraicGeometry.exists_ne_zero_K0_bounded`: the middle group is nonzero whenever `K'₀(X)`
  is, by transport along the first identification of Tag 0FDF.
* `AlgebraicGeometry.exists_ne_zero_K0_boundedCoherent`: the same for the right-hand group
  `K₀(D^b_Coh(𝒪_X))`, by transport along the second identification.
* `AlgebraicGeometry.exists_ne_zero_K0_bounded_standard`: the two measurements combined — the
  middle group at the canonically constructed derived category, with no `HasDerivedCategory`
  hypothesis at all.

## Implementation notes

The datum is discharged by `CategoryTheory.HasDerivedCategory.standard`, which needs only that
`Coh(𝒪_X)` be abelian (`AlgebraicGeometry.coherentModulesAbelian`, [Stacks, Tag 01Y0]). It lands
at the universe `max u (u+1) = u+1`, which is why the statements below fix `.{u + 1}`; the
tagged identifications themselves remain polymorphic in that universe.

The nonzero-ness hypothesis is left as a hypothesis rather than instantiated here. `K'₀(X) ≠ 0`
is a statement about the *left*-hand group of Tag 0FDF's chain, i.e. about Tag 0FDG's definition,
and the witness for it over a field is
`Stacks.AlgebraicGeometry.GrothendieckGroupAffine.exists_ne_zero_coherentKZero_specRat`, proved
for [Stacks, Tag 0FDH] in
`StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupCoherentNonzero`. Re-deriving it here
would duplicate that argument; applying the transports below to it gives
`K₀(D^b(Coh(𝒪_{Spec ℚ}))) ≠ 0` and `K₀(D^b_Coh(𝒪_{Spec ℚ})) ≠ 0` in one step each.

## References

* [Stacks Project, Tag 0FDF](https://stacks.math.columbia.edu/tag/0FDF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u d

namespace AlgebraicGeometry

/-- **The `HasDerivedCategory` datum of the middle group of Tag 0FDF is inhabited**, with
nothing assumed about the scheme `X`: the coherent modules on `X` form an abelian category, so
`CategoryTheory.HasDerivedCategory.standard` applies to them. Without this, the hypothesis
`[HasDerivedCategory (Coh(𝒪_X))]` carried by
`AlgebraicGeometry.exists_addEquiv_coherentKZero_K0_bounded` would not be known to be
satisfiable at any scheme at all. -/
@[instance_reducible]
def coherentModulesHasDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :=
  HasDerivedCategory.standard _

/-- **The middle group of Tag 0FDF is nonzero whenever `K'₀(X)` is.** The first identification
of Tag 0FDF, `AlgebraicGeometry.exists_addEquiv_coherentKZero_K0_bounded`, is an isomorphism of
additive groups, so it carries a nonzero class of `K'₀(X)` to a nonzero class of
`K₀(D^b(Coh(𝒪_X)))`. -/
theorem exists_ne_zero_K0_bounded (X : Scheme.{u})
    [HasDerivedCategory.{d} (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)]
    (h : ∃ x : CoherentKZero X, x ≠ 0) :
    ∃ x : Pretriangulated.K0
      (DerivedCategory.Bounded (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)),
      x ≠ 0 := by
  obtain ⟨e, -⟩ := exists_addEquiv_coherentKZero_K0_bounded X
  exact h.imp' e fun _ => e.map_ne_zero_iff.2

/-- **The right-hand group of Tag 0FDF is nonzero whenever `K'₀(X)` is.** Same transport, along
the second identification `AlgebraicGeometry.exists_addEquiv_coherentKZero_K0`. -/
theorem exists_ne_zero_K0_boundedCoherent (X : Scheme.{u})
    [HasDerivedCategory.{d} (SheafOfModules.{u} X.ringCatSheaf)]
    (h : ∃ x : CoherentKZero X, x ≠ 0) :
    ∃ x : Pretriangulated.K0 (DerivedCategoryB.derivedCategoryBBounded
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).FullSubcategory, x ≠ 0 := by
  obtain ⟨e, -, -⟩ := exists_addEquiv_coherentKZero_K0 X
  exact h.imp' e fun _ => e.map_ne_zero_iff.2

/-- **The middle group of Tag 0FDF, at the canonically constructed derived category, is nonzero
whenever `K'₀(X)` is.** This carries no `HasDerivedCategory` hypothesis: the datum is supplied
by `AlgebraicGeometry.coherentModulesHasDerivedCategory`. So the middle group of the source's
chain is a group one can write down for any scheme, and it is not the zero group as soon as the
left-hand group of the chain is not. -/
theorem exists_ne_zero_K0_bounded_standard (X : Scheme.{u})
    (h : ∃ x : CoherentKZero X, x ≠ 0) :
    letI := coherentModulesHasDerivedCategory X
    ∃ x : Pretriangulated.K0
      (DerivedCategory.Bounded (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)),
      x ≠ 0 :=
  let := coherentModulesHasDerivedCategory X
  exists_ne_zero_K0_bounded X h

/-- **The middle group of Tag 0FDF is nonzero at a scheme that exists:
`K₀(D^b(Coh(𝒪_{Spec ℚ}))) ≠ 0`.** This is
`AlgebraicGeometry.exists_ne_zero_K0_bounded_standard` with its remaining hypothesis
discharged by
`Stacks.AlgebraicGeometry.GrothendieckGroupAffine.exists_ne_zero_coherentKZero_specRat`, the
witness, from [Stacks, Tag 0FDH], that `K'₀(Spec ℚ) ≠ 0`. Nothing is assumed: the
`HasDerivedCategory` datum comes from
`AlgebraicGeometry.coherentModulesHasDerivedCategory`, so the middle group of the source's
chain is exhibited, at a named scheme, as a group that is not zero. -/
theorem exists_ne_zero_K0_bounded_specRat :
    letI := coherentModulesHasDerivedCategory (Spec (CommRingCat.of ℚ))
    ∃ x : Pretriangulated.K0 (DerivedCategory.Bounded
      (Stacks.SheafOfModules.CoherentModules (Spec (CommRingCat.of ℚ)).ringCatSheaf)),
      x ≠ 0 :=
  exists_ne_zero_K0_bounded_standard _
    Stacks.AlgebraicGeometry.GrothendieckGroupAffine.exists_ne_zero_coherentKZero_specRat

end AlgebraicGeometry

end
