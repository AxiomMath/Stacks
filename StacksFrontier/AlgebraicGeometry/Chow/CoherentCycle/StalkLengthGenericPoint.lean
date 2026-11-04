module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitStalkMathlibLinearEquiv
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.SupportGenericPointLength
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A local ring of a scheme has finite length over itself only at a generic point

Let `X` be a locally Noetherian scheme and `u` a point of it.  The local ring `𝒪_{X, u}` has
finite length as a module over itself exactly when `u` is a generic point of an irreducible
component of `X`.

This is `Stacks.Chow.exists_isGenericPoint_component_supp_iff_length` — the scheme-level content
of Stacks 0EE4 — read at the structure sheaf, whose support is the whole space.  The two
readings needed are that the stalk of the structure sheaf as a module over itself is the local
ring (`Stacks.SheafOfModules.FlatShortExact.unitAbStalkLinearEquivScheme`), and that a point with
no proper generization is a generic point
(`TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq`).

The consequence actually used downstream is the contrapositive: **away from the generic points
the length is `⊤`**, and `ENat.toNat ⊤ = 0`.  That is how a multiplicity defined as the
`ENat.toNat` of such a length vanishes at a point which is not a component.

## Main results

* `Stacks.Chow.length_stalk_ne_top_iff_mem_genericPoints`: the length of `𝒪_{X, u}` over itself
  is finite exactly at the generic points.
* `Stacks.Chow.length_stalk_eq_top_of_notMem_genericPoints`: away from them it is `⊤`.
* `Stacks.Chow.toNat_length_stalk_eq_zero_of_notMem_genericPoints`: hence its `ENat.toNat`
  is zero there.

## References

* [Stacks Project, Tag 00L5](https://stacks.math.columbia.edu/tag/00L5)
* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **The local ring of a locally Noetherian scheme has finite length over itself exactly at a
generic point of an irreducible component.**

The structure sheaf is supported everywhere (`AlgebraicGeometry.mem_supp_structureSheaf`), so the
generic points of the components of its support are the generic points of the components of `X`;
and its stalk at `u`, as a module over itself, is `𝒪_{X, u}`
(`Stacks.SheafOfModules.FlatShortExact.unitAbStalkLinearEquivScheme`).  So this is
`Stacks.Chow.exists_isGenericPoint_component_supp_iff_length` at the structure sheaf, the
positivity half of whose right-hand side is automatic because a local ring is nonzero. -/
@[ega "IV 3.1.4" "Final clause for F = O_X", ega "IV 4.7.7" "F = O_X", sga "6 X 1.1.2" "F = O_X"]
theorem length_stalk_ne_top_iff_mem_genericPoints {X : Scheme.{u}} [IsLocallyNoetherian X]
    (u : X) :
    Module.length (X.presheaf.stalk u) (X.presheaf.stalk u) ≠ ⊤ ↔ u ∈ genericPoints X := by
  have hsupp : SheafOfModules.supp (SheafOfModules.unit X.ringCatSheaf) = Set.univ :=
    Set.eq_univ_of_forall (mem_supp_structureSheaf X)
  have hgen : (∃ Z : irreducibleComponents
        (SheafOfModules.supp (SheafOfModules.unit X.ringCatSheaf) : Set X),
      IsGenericPoint u (Subtype.val '' Z.1 : Set X)) ↔ u ∈ genericPoints X := by
    rw [TopologicalSpace.exists_isGenericPoint_irreducibleComponents_iff
        (SheafOfModules.isClosed_supp _) u, hsupp,
      TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq]
    simp
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace)
    (SheafOfModules.unit X.ringCatSheaf) u
  let : Module (X.presheaf.stalk u)
      ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).stalk u) :=
    Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace)
      (SheafOfModules.unit X.ringCatSheaf) u
  have hlen : Module.length (X.presheaf.stalk u)
        ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).stalk u) =
      Module.length (X.presheaf.stalk u) (X.presheaf.stalk u) :=
    (Stacks.SheafOfModules.FlatShortExact.unitAbStalkLinearEquivScheme X u).length_eq
  have hpos : 0 < Module.length (X.presheaf.stalk u) (X.presheaf.stalk u) :=
    Module.length_pos_iff.mpr inferInstance
  have key := exists_isGenericPoint_component_supp_iff_length
    (SheafOfModules.unit X.ringCatSheaf) u
  rw [hgen, hlen] at key
  exact ⟨fun h => key.mpr ⟨h, hpos⟩, fun h => (key.mp h).1⟩

/-- **Away from the generic points the local ring has infinite length over itself**, the
contrapositive of `Stacks.Chow.length_stalk_ne_top_iff_mem_genericPoints`. -/
theorem length_stalk_eq_top_of_notMem_genericPoints {X : Scheme.{u}} [IsLocallyNoetherian X]
    (u : X) (hu : u ∉ genericPoints X) :
    Module.length (X.presheaf.stalk u) (X.presheaf.stalk u) = ⊤ :=
  not_ne_iff.mp fun h => hu ((length_stalk_ne_top_iff_mem_genericPoints u).mp h)

/-- **A multiplicity read as the `ENat.toNat` of the length of the local ring over itself
vanishes away from the generic points**, because `ENat.toNat ⊤ = 0`. -/
theorem toNat_length_stalk_eq_zero_of_notMem_genericPoints {X : Scheme.{u}}
    [IsLocallyNoetherian X] (u : X) (hu : u ∉ genericPoints X) :
    (Module.length (X.presheaf.stalk u) (X.presheaf.stalk u)).toNat = 0 := by
  rw [length_stalk_eq_top_of_notMem_genericPoints u hu]
  rfl

end Stacks.Chow

end
