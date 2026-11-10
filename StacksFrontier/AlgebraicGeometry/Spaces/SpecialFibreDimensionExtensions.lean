module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpecialFibreDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralModification
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationSpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModificationSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.RingTheory.SpecialFibreDimension
public import StacksFrontier.Topology.Irreducible.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralModificationExtensions

/-!
# Additions to `SpecialFibreDimension`

Declarations this development adds alongside
`StacksFrontier.AlgebraicGeometry.Spaces.SpecialFibreDimension`, kept in their own module so that
the base file is unchanged: 5 declaration(s) that the base file does not have, with the section
variables, namespaces and options they are stated in.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] [IsLocalRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))

/-- The special fibre of a morphism of algebraic spaces to `Spec A`, for `A` local, is an
algebraic space: it is the base change of that morphism along the residue-field point. -/
theorem isAlgebraicSpace_fieldFibre_residueFieldPoint
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hA)) :
    IsAlgebraicSpace B (Spec (.of A)) hA
      (fieldFibre B (Spec (.of A)) hA f (residueFieldPoint A B hA)) :=
  isAlgebraicSpace_fieldFibre hX
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hA _) f (residueFieldPoint A B hA)

/-- **Stacks 0AYJ, case (4)**, with the algebraicity of the special fibre supplied rather than
assumed: it is the base change of `f` along the residue-field point, so
`AlgebraicGeometry.Space.isAlgebraicSpace_fieldFibre_residueFieldPoint` provides it and
`AlgebraicGeometry.Space.dimension_fieldFibre_add_one_le_ringKrullDim` applies. -/
@[stacks 0AYJ "case (4), X decent, at the source's hypotheses"]
theorem dimension_fieldFibre_add_one_le_ringKrullDim' [IsDomain A] [IsNoetherianRing A]
    (hdim : 1 ≤ ringKrullDim A)
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f)
    (hdec : IsDecentSpace B (Spec (.of A)) hA X)
    (hgen : ∀ x : points B (Spec (.of A)) hA X,
      x ∈ genericPoints (points B (Spec (.of A)) hA X) ↔
        pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
            (pointsMap B (Spec (.of A)) hA X f x) = genericPoint (Spec (.of A))) :
    dimension B (Spec (.of A)) hA
        (fieldFibre B (Spec (.of A)) hA f (residueFieldPoint A B hA))
        (isAlgebraicSpace_fieldFibre_residueFieldPoint A B hA hX f) + 1
      ≤ ringKrullDim A :=
  dimension_fieldFibre_add_one_le_ringKrullDim A B hA hdim hX f hf hdec hgen
    (isAlgebraicSpace_fieldFibre_residueFieldPoint A B hA hX f)

/-- **Stacks 0AYJ, case (3)**, with the algebraicity of the special fibre supplied rather than
assumed, by `AlgebraicGeometry.Space.isAlgebraicSpace_fieldFibre_residueFieldPoint`; this is
`AlgebraicGeometry.Space.dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace` with
that witness. -/
@[stacks 0AYJ "case (3), X integral, at the source's hypotheses"]
theorem dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace'
    [IsDomain A] [IsNoetherianRing A] (hdim : 1 ≤ ringKrullDim A)
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f)
    (hint : IsIntegralSpace B (Spec (.of A)) hA X)
    (hone : ∃! x : points B (Spec (.of A)) hA X,
      pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
        (pointsMap B (Spec (.of A)) hA X f x) = genericPoint (Spec (.of A))) :
    dimension B (Spec (.of A)) hA
        (fieldFibre B (Spec (.of A)) hA f (residueFieldPoint A B hA))
        (isAlgebraicSpace_fieldFibre_residueFieldPoint A B hA hX f) + 1
      ≤ ringKrullDim A :=
  dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace A B hA hdim hX f hf hint hone
    (isAlgebraicSpace_fieldFibre_residueFieldPoint A B hA hX f)

/-- **Stacks 0AYJ, case (2).** Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension at
least one and let `f : X → Spec A` be an alteration of algebraic spaces, Stacks 0ADA. Then the
special fibre `X_κ` has dimension at most `dim(A) - 1`.

This is case (3). An alteration is proper, hence locally of finite type, and its source is
integral, so all that is needed is that exactly one point of `|X|` lies over the generic point
of `Spec A`. Being an alteration, `f` is quasi-finite at the generic point of `|X|` by
Stacks 0ADB, and condition (5) of Stacks 0AD5 turns that into the statement that the generic
point is the only point of `|X|` above the generic point of `|Spec A|`; the comparison map
from the points of the representable base to `Spec A` is injective, so that is uniqueness of
the point above `genericPoint (Spec A)`. -/
@[stacks 0AYJ "case (2), f an alteration"]
theorem dimension_fieldFibre_add_one_le_ringKrullDim_of_isAlteration
    [IsDomain A] [IsNoetherianRing A] (hdim : 1 ≤ ringKrullDim A)
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hA))
    (halt : IsAlteration B (Spec (.of A)) hA f) :
    dimension B (Spec (.of A)) hA
        (fieldFibre B (Spec (.of A)) hA f (residueFieldPoint A B hA))
        (isAlgebraicSpace_fieldFibre_residueFieldPoint A B hA
          (halt.isAlgebraicSpace_source B (Spec (.of A)) hA) f) + 1
      ≤ ringKrullDim A := by
  have hXalg : IsAlgebraicSpace B (Spec (.of A)) hA X :=
    halt.isAlgebraicSpace_source B (Spec (.of A)) hA
  have hXint : IsIntegralSpace B (Spec (.of A)) hA X :=
    halt.isIntegralSpace_source B (Spec (.of A)) hA
  have hTalg : IsAlgebraicSpace B (Spec (.of A)) hA
      (yoneda.obj (baseTerminal B (Spec (.of A)) hA)) :=
    isAlgebraicSpace_yoneda B (Spec (.of A)) hA _
  have hTint : IsIntegralSpace B (Spec (.of A)) hA
      (yoneda.obj (baseTerminal B (Spec (.of A)) hA)) :=
    halt.isIntegralSpace_target B (Spec (.of A)) hA
  have hproper : IsProper B (Spec (.of A)) hA f := halt.isProper B (Spec (.of A)) hA
  have hdom : IsDominant B (Spec (.of A)) hA f := halt.isDominant B (Spec (.of A)) hA
  have hlft : IsLocallyOfFiniteType B (Spec (.of A)) hA f :=
    (hproper.isFiniteType B (Spec (.of A)) hA).1
  have _ : QuasiSober (points B (Spec (.of A)) hA X) :=
    quasiSober_points_of_isDecentSpace B (Spec (.of A)) hA hXalg hXint.isDecentSpace
  have _ : IrreducibleSpace (points B (Spec (.of A)) hA X) := hXint.irreducibleSpace
  -- The generic point of `|X|`.
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober
    (IrreducibleSpace.isIrreducible_univ (points B (Spec (.of A)) hA X)) isClosed_univ
  -- The generic point of `Spec A`, read as a point of the representable base.
  set e := schemePointsHomeomorph B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
  have hηmap : pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
      (e.symm (genericPoint (Spec (.of A)))) = genericPoint (Spec (.of A)) :=
    e.apply_symm_apply _
  have hη : IsGenericPoint (e.symm (genericPoint (Spec (.of A))))
      (Set.univ : Set (points B (Spec (.of A)) hA
        (yoneda.obj (baseTerminal B (Spec (.of A)) hA)))) := by
    have h := (genericPoint_spec (Spec (.of A))).image e.symm.continuous
    rwa [Set.image_univ, e.symm.surjective.range_eq, closure_univ] at h
  -- Stacks 0ADB and condition (5) of Stacks 0AD5.
  have huniq : ∀ x : points B (Spec (.of A)) hA X,
      pointsMap B (Spec (.of A)) hA X f x = e.symm (genericPoint (Spec (.of A))) → x = ξ :=
    (isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq B (Spec (.of A)) hA hXalg hTalg hTint f
        hlft hdom hξ hη).mp
      ((isAlteration_iff_isQuasiFiniteAt B (Spec (.of A)) hA hXalg hTalg hXint hTint f
        hproper hdom hξ hη).mp halt)
  have hξmap : pointsMap B (Spec (.of A)) hA X f ξ = e.symm (genericPoint (Spec (.of A))) :=
    pointsMap_eq_of_isGenericPoint B (Spec (.of A)) hA hTalg hTint.isDecentSpace f hdom hξ hη
  refine dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace' A B hA hdim hXalg f
    hlft hXint ⟨ξ, ?_, fun x hx ↦ ?_⟩
  · change pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
        (pointsMap B (Spec (.of A)) hA X f ξ) = genericPoint (Spec (.of A))
    rw [hξmap]
    exact hηmap
  · refine huniq x (injective_pointsToScheme B (Spec (.of A)) hA _ ?_)
    rw [hηmap]
    exact hx

/-- **Stacks 0AYJ.** Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension at least one
and let `f : X → Spec A` be a morphism of algebraic spaces satisfying at least one of: (1) `f`
is a modification, Stacks 0AD8; (2) `f` is an alteration, Stacks 0ADA; (3) `f` is locally of
finite type, `X` is integral, and exactly one point of `|X|` maps to the generic point of
`Spec A`; (4) `f` is locally of finite type, `X` is decent, and the points of `|X|` mapping to
the generic point of `Spec A` are the generic points of the irreducible components of `|X|`.
Then the special fibre `X_κ` has dimension at most `dim(A) - 1`.

The source's hypothesis is this disjunction, and the four clauses are four theorems (clause (1)
is `dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralModification`,
the others are above), so the proof is the case distinction. Clause (1) needs no decency witness:
`AlgebraicGeometry.Space.IsIntegralModification` derives it from the integrality it asserts.
The source also assumes `f`
quasi-separated in clause (3); that is omitted, because
`AlgebraicGeometry.Space.dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace`
does not need it. -/
@[stacks 0AYJ]
theorem dimension_fieldFibre_add_one_le_ringKrullDim_of_alteration_or_generic
    [IsDomain A] [IsNoetherianRing A] (hdim : 1 ≤ ringKrullDim A)
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hA))
    (hf :
      IsIntegralModification B (Spec (.of A)) hA hX
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA _)
        (isIntegralSpace_yoneda_baseTerminal A B hA) f ∨
      IsAlteration B (Spec (.of A)) hA f ∨
      (IsLocallyOfFiniteType B (Spec (.of A)) hA f ∧
        IsIntegralSpace B (Spec (.of A)) hA X ∧
        ∃! x : points B (Spec (.of A)) hA X,
          pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
            (pointsMap B (Spec (.of A)) hA X f x) = genericPoint (Spec (.of A))) ∨
      (IsLocallyOfFiniteType B (Spec (.of A)) hA f ∧
        IsDecentSpace B (Spec (.of A)) hA X ∧
        ∀ x : points B (Spec (.of A)) hA X,
          x ∈ genericPoints (points B (Spec (.of A)) hA X) ↔
            pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
              (pointsMap B (Spec (.of A)) hA X f x) = genericPoint (Spec (.of A)))) :
    dimension B (Spec (.of A)) hA
        (fieldFibre B (Spec (.of A)) hA f (residueFieldPoint A B hA))
        (isAlgebraicSpace_fieldFibre_residueFieldPoint A B hA hX f) + 1
      ≤ ringKrullDim A := by
  rcases hf with hmod | halt | ⟨hlft, hint, hone⟩ | ⟨hlft, hdec, hgen⟩
  · exact dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralModification A B hA hdim hX
      f hmod
  · exact dimension_fieldFibre_add_one_le_ringKrullDim_of_isAlteration A B hA hdim f halt
  · exact dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace' A B hA hdim hX f hlft
      hint hone
  · exact dimension_fieldFibre_add_one_le_ringKrullDim' A B hA hdim hX f hlft hdec hgen

end Space

end AlgebraicGeometry

end
