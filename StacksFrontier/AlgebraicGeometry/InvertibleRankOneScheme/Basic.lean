module

public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneIff.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invertible modules on a scheme are the locally trivial ones

On a ringed space all of whose stalks are local rings, a sheaf of modules is invertible exactly
when it is finite locally free of rank one, exactly when it is locally isomorphic to the structure
sheaf. On a scheme the hypothesis on the stalks holds automatically. This file states these
equivalences for `Stacks.Ample.IsInvertibleModule`, `Stacks.SheafOfModules.IsInvertible` and
`Stacks.SheafOfModules.Invertible.IsLocallyTrivial`.

## Main results

* `Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_iff`:
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` and
  `Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank` agree.
* `Stacks.InvertibleRankOneScheme.isInvertible_iff_isLocallyTrivial`: on a ringed space all of
  whose stalks are local rings, a sheaf of modules is invertible exactly when some covering of the
  terminal open trivializes it.
* `Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one`: an
  `𝒪_X`-module on a scheme is invertible exactly when it is finite locally free of rank one.
* `Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isLocallyTrivial`: an `𝒪_X`-module on a
  scheme is invertible exactly when it is locally trivial.
* `Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one` and
  `Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isLocallyTrivial`: the same two
  equivalences for `Stacks.SheafOfModules.IsInvertible`.
* `Stacks.InvertibleRankOneScheme.isInvertibleModule_of_isFiniteLocallyFreeOfRank_one`: a finite
  locally free `𝒪_X`-module of rank one on a scheme is invertible.
* `Stacks.InvertibleRankOneScheme.exists_mem_isoUnit_over` and
  `Stacks.InvertibleRankOneScheme.isInvertibleModule_of_forall_exists_mem_isoUnit_over`: an
  `𝒪_X`-module `L` on a scheme is invertible exactly when every point has an open neighbourhood
  `U` with `L|_U ≅ 𝒪_U`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v u₁

namespace Stacks.InvertibleRankOneScheme

/-! ### Finite locally free modules of rank `r` -/

section Classes

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank M r` holds exactly when
`Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank M r` does: both assert that there are
local generators forming locally free data all of whose indexing types are equivalent to
`Fin r`. -/
theorem isFiniteLocallyFreeOfRank_iff (M : SheafOfModules.{u} R) (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank M r ↔
      Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank M r :=
  ⟨fun h ↦ ⟨h.exists_isFiniteLocallyFreeOfRankData⟩,
    fun h ↦ ⟨h.exists_isFiniteLocallyFreeOfRankData⟩⟩

end Classes

/-! ### Invertible modules on a ringed space -/

/-- On a ringed space all of whose stalks `𝒪_{X, x}` are local rings, a sheaf of modules is
invertible exactly when some covering of the terminal open trivializes it. -/
theorem isInvertible_iff_isLocallyTrivial (X : RingedSpace.{u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
        (structureSheaf X.sheaf).property L ↔
      Stacks.SheafOfModules.Invertible.IsLocallyTrivial L := by
  refine (Stacks.InvertibleRankOneIff.isInvertible_iff_isFiniteLocallyFreeOfRank_one X L).trans
    ((isFiniteLocallyFreeOfRank_iff L 1).trans ?_)
  exact (Stacks.SheafOfModules.Invertible.isLocallyTrivial_iff_isFiniteLocallyFreeOfRank_one
    L).symm

/-! ### Invertible modules on a scheme -/

/-- A finite locally free `𝒪_X`-module of rank one on a scheme is invertible. -/
instance isInvertibleModule_of_isFiniteLocallyFreeOfRank_one (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := X.Opens)
      (J := Opens.grothendieckTopology X) L 1] :
    Stacks.Ample.IsInvertibleModule X L :=
  Stacks.InvertibleRankOneIff.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace L

section Scheme

variable (X : Scheme.{u}) (L : X.Modules)

/-- An `𝒪_X`-module on a scheme is invertible exactly when it is finite locally free of rank
one. -/
theorem isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one :
    Stacks.Ample.IsInvertibleModule X L ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := X.Opens)
        (J := Opens.grothendieckTopology X) L 1 :=
  Stacks.InvertibleRankOneIff.isInvertible_iff_isFiniteLocallyFreeOfRank_one X.toRingedSpace L

/-- An invertible `𝒪_X`-module on a scheme is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
    [Stacks.Ample.IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := X.Opens)
      (J := Opens.grothendieckTopology X) L 1 :=
  (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one X L).mp inferInstance

/-- An `𝒪_X`-module `L` on a scheme is invertible exactly when there is a covering of `X` over
each member of which `L` is isomorphic to the structure sheaf. -/
theorem isInvertibleModule_iff_isLocallyTrivial :
    Stacks.Ample.IsInvertibleModule X L ↔
      Stacks.SheafOfModules.Invertible.IsLocallyTrivial L :=
  isInvertible_iff_isLocallyTrivial X.toRingedSpace L

/-- An invertible `𝒪_X`-module on a scheme is locally trivial. -/
instance isLocallyTrivial_of_isInvertibleModule [Stacks.Ample.IsInvertibleModule X L] :
    Stacks.SheafOfModules.Invertible.IsLocallyTrivial L :=
  (isInvertibleModule_iff_isLocallyTrivial X L).mp inferInstance

/-- An `𝒪_X`-module on a scheme is invertible in the sense of
`Stacks.SheafOfModules.IsInvertible` exactly when it is finite locally free of rank one. -/
theorem stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one :
    Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := X.Opens)
        (J := Opens.grothendieckTopology X) L 1 :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ L).trans
    (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one X L)

/-- An `𝒪_X`-module on a scheme is invertible in the sense of
`Stacks.SheafOfModules.IsInvertible` exactly when it is locally trivial. -/
@[ega "IV 21.13.16" "more general"]
theorem stacksIsInvertible_iff_isLocallyTrivial :
    Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L ↔
      Stacks.SheafOfModules.Invertible.IsLocallyTrivial L :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ L).trans
    (isInvertibleModule_iff_isLocallyTrivial X L)

/-! ### Pointwise triviality -/

/-- For an invertible `𝒪_X`-module `L` on a scheme, every `x : X` has an open neighbourhood `U`
with `L|_U ≅ 𝒪_U`. -/
theorem exists_mem_isoUnit_over [Stacks.Ample.IsInvertibleModule X L] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty (L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  obtain ⟨I, Y, hY, e⟩ := (isLocallyTrivial_of_isInvertibleModule X L).exists_trivializing_cover
  have hx : x ∈ ⨆ i, Y i := ((Opens.coversTop_iff _ Y).mp hY) ▸ Opens.mem_top x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨Y i, hi, e i⟩

/-- An `𝒪_X`-module `L` on a scheme such that every point has an open neighbourhood `U` with
`L|_U ≅ 𝒪_U` is invertible. -/
theorem isInvertibleModule_of_forall_exists_mem_isoUnit_over
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))) :
    Stacks.Ample.IsInvertibleModule X L := by
  choose U hU e using h
  refine (isInvertibleModule_iff_isLocallyTrivial X L).mpr ⟨X, U, ?_, e⟩
  exact (Opens.coversTop_iff _ U).mpr
    (TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩))

end Scheme

end Stacks.InvertibleRankOneScheme

end
