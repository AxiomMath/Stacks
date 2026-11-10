module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Impurities
public import StacksCore.Tactic.StacksAttribute

/-!
# Purity along a fibre and relative purity

A finite type quasi-coherent module is *pure along the fibre over `s`* when no impurity occurs
over an elementary étale neighbourhood of `s`, and *universally pure along that fibre* when no
impurity occurs after any base change at all. Imposing either condition at every point of the
base gives the relative notions, and applying them to the structure sheaf gives the
corresponding notions for the scheme.

## Main definitions

* `AlgebraicGeometry.IsPureAlong` expresses purity along the fibre over the chosen point.
* `AlgebraicGeometry.IsUniversallyPureAlong` expresses universal purity along that fibre.
* `AlgebraicGeometry.IsSchemePureAlong` applies purity along a fibre to the structure sheaf.
* `AlgebraicGeometry.IsUniversallyPureRelative` and `AlgebraicGeometry.IsPureRelative` impose
  the corresponding condition at every point of the base.
* `AlgebraicGeometry.IsSchemePureRelative` applies relative purity to the structure sheaf.

## Main results

* `AlgebraicGeometry.structureSheaf_isFiniteType`: the structure sheaf is of finite type as a
  module over itself, which is one of the two properties needed to apply the purity predicates
  to it.

## Implementation notes

The elementary étale neighbourhood associated to an impurity diagram uses its base-change
scheme, its specialized point and its structure morphism. Relative purity takes an unpointed
morphism and module and builds a pre-pure situation only after quantifying over a point of the
base; in particular relative purity over an empty base is vacuous. The predicates are
abbreviations so that clients can use their quantified impurity formulations directly. The six
abbreviations `IsPureAlong`, `IsUniversallyPureAlong`, `IsSchemePureAlong`,
`IsUniversallyPureRelative`, `IsPureRelative` and `IsSchemePureRelative` formalize parts (1)
through (6) of the source.

Quasi-coherence of the structure sheaf is
`Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`.

## References

* [Stacks Project, Tag 05J4](https://stacks.math.columbia.edu/tag/05J4)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The structure sheaf, as a module over itself, is a free sheaf on one generator. -/
noncomputable abbrev structureSheafFreeIso (X : Scheme.{u}) :
    SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit.{u} X.ringCatSheaf :=
  Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit.{u} X.ringCatSheaf)

/-- The forward morphism of `structureSheafFreeIso X` is an isomorphism. -/
instance (X : Scheme.{u}) : IsIso (structureSheafFreeIso X).hom :=
  (structureSheafFreeIso X).isIso_hom

/-- The forward morphism of `structureSheafFreeIso X` is an epimorphism. -/
instance (X : Scheme.{u}) : Epi (structureSheafFreeIso X).hom := by infer_instance

/-- The canonical single generating section of the structure sheaf as a module. -/
noncomputable abbrev structureSheafGenerators (X : Scheme.{u}) :
    (SheafOfModules.unit.{u} X.ringCatSheaf).GeneratingSections :=
  (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) PUnit.{u + 1}).ofEpi
    (structureSheafFreeIso X).hom

/-- The canonical generating sections of the structure sheaf are of finite type. -/
instance (X : Scheme.{u}) : (structureSheafGenerators X).IsFiniteType where
  finite := by
    change Finite PUnit.{u + 1}
    infer_instance

/-- The structure sheaf of a scheme is of finite type as a module over itself. -/
theorem structureSheaf_isFiniteType (X : Scheme.{u}) :
    (SheafOfModules.unit.{u} X.ringCatSheaf).IsFiniteType := by
  let G := structureSheafGenerators X
  have _ : G.IsFiniteType := inferInstance
  let q := G.localGeneratorsData
  refine { exists_localGeneratorsData := ⟨q, ?_⟩ }
  constructor
  intro i
  constructor
  dsimp only [q, SheafOfModules.GeneratingSections.localGeneratorsData]
  change Finite G.I
  infer_instance

/-- Replace the distinguished base point in a pre-pure situation. -/
abbrev PrePureSituation.atPoint (P : PrePureSituation.{u}) (s : P.S) :
    PrePureSituation.{u} where
  S := P.S
  X := P.X
  f := P.f
  F := P.F
  s := s

/-- A finite type quasi-coherent module is pure along the fibre over the chosen point if no
impurity occurs over an elementary étale neighbourhood of that point. -/
@[stacks 05J4 "part (1)"]
abbrev IsPureAlong (P : PrePureSituation.{u}) : Prop :=
  ∀ (D : ImpurityDiagram P) (h : Etale D.g),
    EtaleNeighborhood.IsElementary
        ({ scheme := D.T
           point := D.t
           toBase := D.g
           etale_toBase := h
           map_point := D.mapsToChosenPoint } : EtaleNeighborhood P.S P.s) →
      ¬ IsImpurity P D

/-- A finite type quasi-coherent module is universally pure along the fibre over the chosen
point if no impurity occurs after any base change. -/
@[stacks 05J4 "part (2)"]
abbrev IsUniversallyPureAlong (P : PrePureSituation.{u}) : Prop :=
  ∀ D : ImpurityDiagram P, ¬ IsImpurity P D

/-- The scheme `X` is pure along the fibre over `s` when its structure sheaf is pure there. -/
@[stacks 05J4 "part (3)"]
abbrev IsSchemePureAlong {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (s : S) : Prop :=
  IsPureAlong
    ({ S := S
       X := X
       f := f
       F := SheafOfModules.unit.{u} X.ringCatSheaf
       isFiniteType := structureSheaf_isFiniteType X
       isQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
       s := s } : PrePureSituation)

/-- A finite type quasi-coherent module is universally pure relative to the base if it is
universally pure along every fibre. -/
@[stacks 05J4 "part (4)"]
abbrev IsUniversallyPureRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] : Prop :=
  ∀ s : S, IsUniversallyPureAlong
    ({ S := S
       X := X
       f := f
       F := F
       s := s } : PrePureSituation)

/-- A finite type quasi-coherent module is pure relative to the base if it is pure along every
fibre. -/
@[stacks 05J4 "part (5)"]
abbrev IsPureRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] : Prop :=
  ∀ s : S, IsPureAlong
    ({ S := S
       X := X
       f := f
       F := F
       s := s } : PrePureSituation)

/-- The scheme `X` is pure relative to `S` when its structure sheaf is pure relative to the
base. -/
@[stacks 05J4 "part (6)"]
abbrev IsSchemePureRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] : Prop :=
  ∀ s : S, IsSchemePureAlong f s

end AlgebraicGeometry
