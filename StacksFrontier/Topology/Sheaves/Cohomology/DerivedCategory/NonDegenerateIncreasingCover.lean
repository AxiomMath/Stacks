module

public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemFromGlobalComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedExhaustion
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.NonDegenerateGradedDualWitness

/-!
# A carrier on which the increasing cover of Tag 0D6B is not degenerate

`Stacks.DerivedGlueing.eq_top_of_isGreatest` says that an increasing cover `W : E → Opens X`
whose index order has a greatest element `g` has `W g = ⊤`, so the glueing problem of
[Stacks, Tag 0D6B] is solved at that stage by the prescribed object itself.  A nonempty *finite*
linear order has a greatest element, and on a carrier where every increasing chain of opens
stabilises a cover of this shape eventually has one; so a datum of that tag certifies nothing
unless the carrier admits an infinite strictly increasing chain of **proper** opens whose union
is everything.  In particular the carrier may not be quasi-compact, which rules out every affine
`Spec`, and with it `Stacks.DerivedGlueing.specULiftProdRingedSpace` and
`Stacks.SheafOfModules.OnSpace.specULiftIntRingedSpace`, the development's two existing concrete
ringed spaces.

This file names such a carrier and exhibits the chain on it.  The space is `ℕ` with the discrete
topology, placed at an arbitrary universe by `ULift`; the structure sheaf is the skyscraper sheaf
of the ring `ℤ` at the point `0`, which is a sheaf of commutative rings on any space whatever
(`skyscraperPresheaf_isSheaf` asks only for a terminal object in the target).  The stages are the
initial segments `W n = {x | x < n}`, open because the topology is discrete.  Together with
`Stacks.DerivedGlueing.exists_glueing_of_globalFiltration` this gives an instance of the assembly
half of [Stacks, Tag 0D6B] in which no binder is discharged degenerately: the index order has no
greatest element, the stages increase *strictly*, no stage is `⊤`, they cover, and the
coefficient complex is not zero.

## Main definitions

* `Stacks.DerivedGlueing.natLine`: the ringed space, `ℕ` discrete with the skyscraper sheaf `ℤ`
  at `0`.
* `Stacks.DerivedGlueing.natStage`: the stages `W n`, indexed by `ULift ℕ` so that the order lies
  in the universe the colimit of the system is indexed by.
* `Stacks.DerivedGlueing.natLineComplex`: the complex `𝒪[0]`.

## Main results

* `Stacks.DerivedGlueing.natStage_strictMono`, `natStage_ne_top`, `iSup_natStage`,
  `nat_not_isGreatest`: the four facts that stop `Stacks.DerivedGlueing.eq_top_of_isGreatest`
  from collapsing the datum.
* `Stacks.DerivedGlueing.not_isZero_natLineComplex_X_zero`: the coefficient complex is not the
  zero complex, so the system is not the zero system.
* `Stacks.DerivedGlueing.exists_glueing_natLine`: the assembly half of [Stacks, Tag 0D6B] with
  every binder discharged at that datum.

## Implementation notes

The structure sheaf is a skyscraper, so `Γ(U)` is the zero ring for every open `U` missing the
point `0` — in particular for `W 0 = ∅`.  Every stage `W n` with `n ≥ 1` does contain the point
and has `Γ(W n) = ℤ`.  What this carrier is for is the *order-theoretic* degeneracy criterion,
which is the one [Stacks, Tag 0D6B] has: it is the first non-quasi-compact ringed space in the
development, and the first increasing cover by proper opens.  A structure sheaf nonzero on every
nonempty open would need the sheaf of functions on a discrete space in `CommRingCat`, which this
development does not carry.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe u

attribute [local instance] Classical.propDecidable
attribute [local instance 10000] HasDerivedCategory.standard

/-- **The discrete space `ℕ`, carrying the skyscraper sheaf of rings `ℤ` at `0`.** -/
def natLine : RingedSpace.{u, u} where
  carrier := TopCat.of (ULift.{u} ℕ)
  presheaf := skyscraperPresheaf (X := TopCat.of (ULift.{u} ℕ))
    (⟨0⟩ : ULift.{u} ℕ) (CommRingCat.of (ULift.{u} ℤ))
  IsSheaf := skyscraperPresheaf_isSheaf (X := TopCat.of (ULift.{u} ℕ)) _ _

/-- Every subset of the carrier is open: the topology is discrete. -/
theorem isOpen_natLine (s : Set (natLine.{u}).carrier) : IsOpen s :=
  isOpen_discrete (α := ULift.{u} ℕ) s

/-- The stage `W n` of the increasing cover: the points below `n`.  The index is `ULift ℕ`
rather than `ℕ` so that the order lives in the same universe as the ringed space, which is what
the colimit of the system is indexed by. -/
def natStage (n : ULift.{u} ℕ) : Opens (natLine.{u}).carrier :=
  ⟨{x : ULift.{u} ℕ | x.down < n.down}, isOpen_natLine _⟩

/-- A point `x` lies in the stage `natStage n` if and only if `x < n`. -/
theorem mem_natStage {n x : ULift.{u} ℕ} : x ∈ natStage.{u} n ↔ x.down < n.down := Iff.rfl

/-- **The stages increase.** -/
theorem natStage_mono : Monotone (natStage.{u}) :=
  fun _ _ h _ hx => lt_of_lt_of_le hx h

/-- No stage `natStage n` contains the point `n`. -/
private theorem not_mem_natStage_self (n : ULift.{u} ℕ) : n ∉ natStage.{u} n :=
  lt_irrefl n.down

/-- **The stages increase strictly**, so the cover is not constant. -/
theorem natStage_strictMono : StrictMono (natStage.{u}) := by
  intro m n hmn
  refine lt_of_le_of_ne (natStage_mono hmn.le) fun heq => not_mem_natStage_self m ?_
  rw [heq]
  exact hmn

/-- **No stage is the whole space**, so `Stacks.DerivedGlueing.eq_top_of_isGreatest` does not
collapse this datum. -/
theorem natStage_ne_top (n : ULift.{u} ℕ) : natStage.{u} n ≠ ⊤ := fun h =>
  not_mem_natStage_self n (h ▸ trivial)

/-- **The stages cover the space.** -/
theorem iSup_natStage : (⨆ n : ULift.{u} ℕ, natStage.{u} n) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  exact Opens.mem_iSup.mpr ⟨⟨x.down + 1⟩, Nat.lt_succ_self _⟩

/-- **The index order has no greatest element.** -/
theorem nat_not_isGreatest : ¬ ∃ g : ULift.{u} ℕ, ∀ n : ULift.{u} ℕ, n ≤ g :=
  fun ⟨g, hg⟩ => Nat.not_succ_le_self g.down (hg ⟨g.down + 1⟩)

/-! ### A complex that is not zero -/

/-- **The global sections of the structure sheaf of `natLine` are `ULift ℤ`**, the skyscraper
point lying in every nonempty open and in particular in `⊤`. -/
theorem natLine_sections_top :
    (underlyingRingSheaf natLine.{u}).obj.obj (op ⊤) =
      (forget₂ CommRingCat.{u} RingCat.{u}).obj (CommRingCat.of (ULift.{u} ℤ)) := by
  show (forget₂ CommRingCat.{u} RingCat.{u}).obj
      ((skyscraperPresheaf (X := TopCat.of (ULift.{u} ℕ)) (⟨0⟩ : ULift.{u} ℕ)
        (CommRingCat.of (ULift.{u} ℤ))).obj (op ⊤)) = _
  congr 1
  simp

/-- In the ring of global sections of the structure sheaf of `natLine`, `1 ≠ 0`. -/
theorem one_ne_zero_natLine :
    (1 : (underlyingRingSheaf natLine.{u}).obj.obj (op ⊤)) ≠ 0 := by
  rw [natLine_sections_top]
  intro h
  have h' : (1 : ULift.{u} ℤ) = 0 := h
  exact absurd (congrArg ULift.down h') (by decide)

/-- **The structure sheaf of `natLine`, as a module over itself, is not a zero object.** -/
theorem not_isZero_unit_natLine :
    ¬ IsZero (SheafOfModules.unit (underlyingRingSheaf natLine.{u})) :=
  Stacks.SheafOfModules.not_isZero_unit_of_one_ne_zero (op ⊤) one_ne_zero_natLine

/-- **The complex `𝒪[0]` on `natLine`.** -/
def natLineComplex : CochainComplex (SheafOfModules.{u} (underlyingRingSheaf natLine.{u})) ℤ :=
  (HomologicalComplex.single (SheafOfModules.{u} (underlyingRingSheaf natLine.{u}))
      (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit (underlyingRingSheaf natLine.{u}))

/-- **The witness complex is not zero in degree zero.** -/
theorem not_isZero_natLineComplex_X_zero : ¬ IsZero ((natLineComplex.{u}).X 0) := fun h =>
  not_isZero_unit_natLine (h.of_iso
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (underlyingRingSheaf natLine.{u}))).symm)

/-! ### The non-degenerate instance -/

/-- **The assembly half of [Stacks, Tag 0D6B] at a datum that nothing collapses.** -/
theorem exists_glueing_natLine (S : LocallyGiven natLine.{u}) :
    ∃ (G : OpenDerivedCategory natLine.{u} ⊤)
      (sigma : ∀ α : ULift.{u} ℕ, (S.restriction (natStage α) ⊤ le_top).obj G ≅
        DerivedCategory.Q.obj (globalFiltrationLocal natStage.{u} natLineComplex.{u} α))
      (rho : ∀ (β α : ULift.{u} ℕ) (h : β ≤ α),
        (S.restriction (natStage β) (natStage α) (natStage_mono h)).obj
            (DerivedCategory.Q.obj (globalFiltrationLocal natStage.{u} natLineComplex.{u} α)) ≅
          DerivedCategory.Q.obj (globalFiltrationLocal natStage.{u} natLineComplex.{u} β)),
      ∀ (β α : ULift.{u} ℕ) (h : β ≤ α),
        (S.restrictionComp (natStage β) (natStage α) ⊤ (natStage_mono h) le_top).hom.app G ≫
            (S.restriction (natStage β) (natStage α) (natStage_mono h)).map (sigma α).hom ≫
              (rho β α h).hom =
          (sigma β).hom :=
  exists_glueing_of_globalFiltration natStage.{u} (fun _ _ h => natStage_mono h)
    natLineComplex.{u} S

end Stacks.DerivedGlueing

end
