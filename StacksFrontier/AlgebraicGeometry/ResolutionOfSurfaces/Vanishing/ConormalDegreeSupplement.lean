module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ConormalDegree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Fibres.SectionsFromFibre
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.ModulePullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentFactorization
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentFactorizationSupplement

/-!
# Further results on `ConormalDegree`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ConormalDegree` that need imports
beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.VanishingSituation

variable (V : VanishingSituation.{u})

/-- Each component of the special fibre, with its reduced induced structure, has dimension at
most one. Unlike `AlgebraicGeometry.VanishingSituation.topologicalKrullDim_componentScheme_le_one`
this needs nothing beyond Situation [Stacks, Tag 0AX8], through
`AlgebraicGeometry.VanishingSituation.topologicalKrullDim_component_le_one`. -/
theorem topologicalKrullDim_componentScheme_le_one_unconditional
    (i : Fin V.numberOfComponents) : topologicalKrullDim (componentScheme V i) ≤ 1 :=
  ((componentSchemeHomeo V i).isHomeomorph.topologicalKrullDim_eq).trans_le
    (V.topologicalKrullDim_component_le_one i)

/-- The degree clause of [Stacks, Tag 0AXA] at a component carrying a section with a zero.

In Situation [Stacks, Tag 0AX8] with `X` normal, let `Z ⊆ X` be a nonempty effective Cartier
divisor contained set theoretically in the special fibre, and let `C_i` be a component of the
special fibre contained in `Z`. If the restriction `𝒞_{Z/X}|_{C_i}` of the conormal sheaf of `Z`
has a nonzero global section with a zero, then `deg(𝒞_{Z/X}|_{C_i}) > 0`.

The component `C_i`, with its reduced induced structure, is an integral scheme proper over the
residue field `κ` of the closed point of the base, of dimension at most one by
`AlgebraicGeometry.VanishingSituation.topologicalKrullDim_component_le_one`, which needs nothing
beyond Situation 0AX8; the restricted conormal sheaf is invertible because `ℐ_Z` is. Part (2) of
[Stacks, Tag 0B40], the hypothesis `hpos` (`AlgebraicGeometry.VanishingSectionDegreePos`), then
gives the conclusion; it is quantified over every proper integral scheme of dimension at most one
over `κ` and every invertible sheaf on it, so it mentions none of `X`, `Z` or `C_i`.

The section `s` is an input here. In the source its construction is the substance of the
argument: the function of [Stacks, Tag 0AX9] raised to a power read off from the valuations of
the local rings at the generic points of the components, after replacing `Z` by `e_i Z`
([Stacks, Tags 02OP, 0AYX]) and using that `Z` is `(S_1)` ([Stacks, Tags 0B3S, 0346, 0B3M]) to
see that the function is a section of `ℐ_Z`. -/
theorem invertibleCurveDegree_conormalOnComponent_pos_unconditional [IsNormal V.X]
    (I : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (hpos : VanishingSectionDegreePos (V.base.residueField V.closedPoint))
    (i : Fin V.numberOfComponents) (hCi : componentInSource V i ⊆ I.supportSet)
    (s : (conormalOnComponent V I i).sections) (hs : s.eval (op ⊤) ≠ 0)
    (hzero : ∃ y : componentScheme V i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
      (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V I i) s) :
    0 < invertibleCurveDegree (V.base.residueField V.closedPoint)
      (componentToSpecResidueField V i)
      (topologicalKrullDim_componentScheme_le_one_unconditional V i)
      (conormalOnComponent V I i) := by
  -- `hne` and `hZs` enter only through the construction of the section, and `hCi` only through
  -- the identification of the restricted conormal sheaf.
  have : I.supportSet.Nonempty := hne
  have : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint) := hZs
  have : componentInSource V i ⊆ I.supportSet := hCi
  exact hpos (componentScheme V i) (componentToSpecResidueField V i) inferInstance
    inferInstance (topologicalKrullDim_componentScheme_le_one_unconditional V i)
    (conormalOnComponent V I i) inferInstance s hs hzero

/-- The precise clause of [Stacks, Tag 0AXA], in the source's existential form.

The hypothesis is that *some* component contained in `Z` carries a nonzero global section of
the restricted conormal sheaf with a zero; the conclusion is the source's: there is an `i` with
`C_i ⊆ Z` and `deg(𝒞_{Z/X}|_{C_i}) > 0`. Part (2) of [Stacks, Tag 0B40] is the hypothesis
`hpos`. -/
theorem exists_component_subset_invertibleCurveDegree_pos_unconditional [IsNormal V.X]
    (I : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (hpos : VanishingSectionDegreePos (V.base.residueField V.closedPoint))
    (hsec : ∃ (i : Fin V.numberOfComponents) (_ : componentInSource V i ⊆ I.supportSet)
      (s : (conormalOnComponent V I i).sections), s.eval (op ⊤) ≠ 0 ∧
        ∃ y : componentScheme V i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
          (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V I i) s) :
    ∃ i : Fin V.numberOfComponents, componentInSource V i ⊆ I.supportSet ∧
      0 < invertibleCurveDegree (V.base.residueField V.closedPoint)
        (componentToSpecResidueField V i)
        (topologicalKrullDim_componentScheme_le_one_unconditional V i)
        (conormalOnComponent V I i) := by
  obtain ⟨i, hCi, s, hs, hz⟩ := hsec
  exact ⟨i, hCi,
    invertibleCurveDegree_conormalOnComponent_pos_unconditional V I hne hZs hpos i hCi s hs hz⟩

/-- The non-triviality clause of [Stacks, Tag 0AXA], derived from the degree clause.

If the conormal sheaf of `Z` in `X` were trivial, its restriction to a component `C_i ⊆ Z`
would be isomorphic to the structure sheaf of `C_i` and so would have degree zero, which
contradicts the positivity of that degree. Part (2) of [Stacks, Tag 0B40] is the hypothesis
`hpos`. -/
theorem not_isTrivial_conormalSheaf_unconditional [IsNormal V.X]
    (I : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (hpos : VanishingSectionDegreePos (V.base.residueField V.closedPoint))
    (i : Fin V.numberOfComponents) (hCi : componentInSource V i ⊆ I.supportSet)
    (s : (conormalOnComponent V I i).sections) (hs : s.eval (op ⊤) ≠ 0)
    (hzero : ∃ y : componentScheme V i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
      (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V I i) s) :
    ¬ SheafOfModules.IsTrivial I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      (Stacks.Conormal.conormalSheaf I.subschemeι) := by
  rintro ⟨e⟩
  have hdeg :=
    invertibleCurveDegree_conormalOnComponent_pos_unconditional V I hne hZs hpos i hCi s hs hzero
  have hiso : conormalOnComponent V I i ≅
      SheafOfModules.unit (componentScheme V i).ringCatSheaf :=
    (conormalOnComponentIso V I i hCi).symm ≪≫
      Stacks.AmplePullback.modulePullbackIsoUnitModule (componentToDivisor V I i hCi) _ e
  rw [invertibleCurveDegree_eq_zero_of_iso_unit (V.base.residueField V.closedPoint)
    (componentToSpecResidueField V i) _ _ hiso] at hdeg
  exact absurd hdeg (lt_irrefl 0)

end AlgebraicGeometry.VanishingSituation

end
