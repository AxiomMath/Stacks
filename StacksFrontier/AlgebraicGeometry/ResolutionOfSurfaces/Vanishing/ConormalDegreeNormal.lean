module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ConormalDegree

/-!
# The conormal degree of a divisor in the special fibre, without the degree hypothesis

`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Vanishing/ConormalDegree.lean` proves the
clauses of [Stacks, Tag 0AXA] — positivity of `deg(𝒞_{Z/X}|_{C_i})` at a component `C_i ⊆ Z`
carrying a nonzero section of the restricted conormal sheaf with a zero, and the non-triviality
of `𝒞_{Z/X}` derived from it — with part (2) of [Stacks, Tag 0B40] as an explicit hypothesis
`hpos : VanishingSectionDegreePos κ`. That statement is a theorem of the library,
`AlgebraicGeometry.vanishingSectionDegreePos`, valid over every field; this file records the
three clauses with it supplied, so that they carry only the hypotheses of the geometry.

## Main results

The elided prefix is `AlgebraicGeometry.VanishingSituation`.

* `conormalOnComponent_degree_pos`: `deg(𝒞_{Z/X}|_{C_i}) > 0`.
* `exists_component_conormalOnComponent_degree_pos`: the same in the source's existential form.
* `not_isTrivial_conormalSheaf_of_component_section`: `𝒞_{Z/X}` is not trivial.

## References

* [Stacks Project, Tag 0AXA](https://stacks.math.columbia.edu/tag/0AXA)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.VanishingSituation

variable (V : VanishingSituation.{u})

/-- **The conormal sheaf of `Z` has positive degree on a component `C_i ⊆ Z` which carries a
nonzero section of it with a zero.** In Situation [Stacks, Tag 0AX8] with `X` normal, every
component of the special fibre of dimension one, and `Z` a nonempty effective Cartier divisor
contained in the special fibre. -/
theorem conormalOnComponent_degree_pos [IsNormal V.X]
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (I : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (i : Fin V.numberOfComponents) (hCi : componentInSource V i ⊆ I.supportSet)
    (s : (conormalOnComponent V I i).sections) (hs : s.eval (op ⊤) ≠ 0)
    (hzero : ∃ y : componentScheme V i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
      (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V I i) s) :
    0 < invertibleCurveDegree (V.base.residueField V.closedPoint)
      (componentToSpecResidueField V i)
      (topologicalKrullDim_componentScheme_le_one V hdim i) (conormalOnComponent V I i) :=
  invertibleCurveDegree_conormalOnComponent_pos V hdim I hne hZs
    (vanishingSectionDegreePos (V.base.residueField V.closedPoint)) i hCi s hs hzero

/-- **Some component `C_i ⊆ Z` has `deg(𝒞_{Z/X}|_{C_i}) > 0`**, as soon as some component
contained in `Z` carries a nonzero section of the restricted conormal sheaf with a zero. -/
theorem exists_component_conormalOnComponent_degree_pos [IsNormal V.X]
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (I : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (hsec : ∃ (i : Fin V.numberOfComponents) (_ : componentInSource V i ⊆ I.supportSet)
      (s : (conormalOnComponent V I i).sections), s.eval (op ⊤) ≠ 0 ∧
        ∃ y : componentScheme V i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
          (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V I i) s) :
    ∃ i : Fin V.numberOfComponents, componentInSource V i ⊆ I.supportSet ∧
      0 < invertibleCurveDegree (V.base.residueField V.closedPoint)
        (componentToSpecResidueField V i)
        (topologicalKrullDim_componentScheme_le_one V hdim i) (conormalOnComponent V I i) :=
  exists_component_subset_invertibleCurveDegree_pos V hdim I hne hZs
    (vanishingSectionDegreePos (V.base.residueField V.closedPoint)) hsec

/-- **The conormal sheaf of `Z` is not trivial**, as soon as some component `C_i ⊆ Z` carries a
nonzero section of the restricted conormal sheaf with a zero. -/
theorem not_isTrivial_conormalSheaf_of_component_section [IsNormal V.X]
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (I : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (i : Fin V.numberOfComponents) (hCi : componentInSource V i ⊆ I.supportSet)
    (s : (conormalOnComponent V I i).sections) (hs : s.eval (op ⊤) ≠ 0)
    (hzero : ∃ y : componentScheme V i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
      (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V I i) s) :
    ¬ SheafOfModules.IsTrivial I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      (Stacks.Conormal.conormalSheaf I.subschemeι) :=
  not_isTrivial_conormalSheaf V hdim I hne hZs
    (vanishingSectionDegreePos (V.base.residueField V.closedPoint)) i hCi s hs hzero

end AlgebraicGeometry.VanishingSituation

end
