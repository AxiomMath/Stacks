module

public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluingSlice
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.MatrixCocycle

/-!
# The matrix cocycle of a family of comparisons of free charts over the overlaps

`Stacks.SheafOfModules.MatrixCocycle` glues a sheaf of modules out of transition *matrices*: for
every pair of members of the family and every open below both, a matrix of sections of the sheaf
of rings, compatible with restriction, the identity on the diagonal and multiplicative along
triples. What a descent argument produces instead is, for every pair of members, one
*isomorphism* of the two free charts over the overlap — a morphism of sheaves of modules on the
slice site `Opens(X)/(U k ⊓ U l)`.

This file reads such a family as a matrix cocycle. The passage is
`Stacks.SheafOfModules.localModuleHomOfOver`, which gives the components of a slice morphism over
every open below the overlap together with their compatibility with restriction, followed by
`Stacks.SheafOfModules.freeCoord`, the coordinates of a section of a free sheaf of modules.

## Main definitions

* `Stacks.SheafOfModules.overlapApp`: the component of an overlap comparison at an open below two
  members of the family.
* `Stacks.SheafOfModules.overlapEntry`: its matrix, the coordinates of the image of a tautological
  section.
* `Stacks.SheafOfModules.matrixCocycleOfOverlap`: **the matrix cocycle of the family.**

## Main results

* `Stacks.SheafOfModules.freeCoord_overlapApp_freeMk`: **the component of an overlap comparison is
  multiplication by its matrix**, on a section written in coordinates. This is the one
  computation; the three laws of a matrix cocycle follow from it together with the naturality of
  `Stacks.SheafOfModules.localModuleHomOfOver`.

## Implementation notes

The diagonal hypothesis is stated as `φ k k = 𝟙 _`, which type-checks because the source and the
target of `φ k k` are both the `k`-th chart over `U k ⊓ U k`; the open is only propositionally
`U k`, and nothing forces it to be rewritten.

The cocycle hypothesis is stated on *components*, not on the slice morphisms: `φ k l` lives over
`U k ⊓ U l` and `φ l j` over `U l ⊓ U j`, so the two can only be composed after both have been
restricted to an open below all three members, and the restriction of a slice morphism to a
smaller open is exactly what `Stacks.SheafOfModules.localModuleHomOfOver` computes. A consumer
holding an equality of slice morphisms over the triple overlap obtains the component form by
`congrArg`.

The index types are `ULift (Fin (m k))`, as in `Stacks.SheafOfModules.MatrixCocycle`, so that the
`Fintype` and `DecidableEq` instances the coordinates need are the canonical ones.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace SheafOfModules

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}}
  {O : Sheaf (Opens.grothendieckTopology ((X : TopCat) : Type u)) RingCat.{u}}
  {K : Type u} (V : K → Opens X) (m : K → ℕ)
  (φ : ∀ k l : K, (MatrixCocycle.chart (O := O) (m := m) k).over (V k ⊓ V l) ⟶
    (MatrixCocycle.chart (O := O) (m := m) l).over (V k ⊓ V l))

/-- **The component of an overlap comparison at an open below two members of the family.** -/
noncomputable def overlapApp (k l : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l) :
    (MatrixCocycle.chart (O := O) (m := m) k).val.obj (op W) ⟶
      (MatrixCocycle.chart (O := O) (m := m) l).val.obj (op W) :=
  (localModuleHomOfOver (V k ⊓ V l) (φ k l)).app W (le_inf hk hl)

/-- **The transition matrix of an overlap comparison**: the coordinates of the image of the `a`-th
tautological section of the `k`-th chart. -/
noncomputable def overlapEntry (k l : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l)
    (a : ULift.{u} (Fin (m k))) (b : ULift.{u} (Fin (m l))) : ToType (O.obj.obj (op W)) :=
  freeCoord (op W) (overlapApp V m φ k l hk hl
    (freeMk (op W) fun c => if a = c then 1 else 0)) b

/-- **The component of an overlap comparison is multiplication by its matrix**, on a section
written in coordinates: a section with coordinates `d` is the combination of the tautological
sections with coefficients `d`, and both the component and taking coordinates are linear. -/
theorem freeCoord_overlapApp_freeMk (k l : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l)
    (d : ULift.{u} (Fin (m k)) → ToType (O.obj.obj (op W))) (b : ULift.{u} (Fin (m l))) :
    freeCoord (op W) (overlapApp V m φ k l hk hl (freeMk (op W) d)) b
      = ∑ a, d a * overlapEntry V m φ k l hk hl a b := by
  have hfc : ∀ e : ToType ((MatrixCocycle.chart (O := O) (m := m) l).val.obj (op W)),
      freeCoord (S := O) (op W) e b = (freeProj b).val.app (op W) e := fun _ => rfl
  rw [hfc, ← freeMk_eq_sum_smul_single (op W) d]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun a _ => congrArg (fun y => d a * y) (hfc _).symm

/-- **The matrix cocycle of a family of comparisons of the free charts over the overlaps.**

Compatibility with restriction is the naturality of
`Stacks.SheafOfModules.localModuleHomOfOver`; the diagonal law is the hypothesis that `φ k k` is
the identity; and the cocycle law is the component form of `φ l j ∘ φ k l = φ k j`, read through
`Stacks.SheafOfModules.freeCoord_overlapApp_freeMk`. -/
noncomputable def matrixCocycleOfOverlap
    (hid : ∀ k : K, φ k k = 𝟙 _)
    (hcomp : ∀ (k l j : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l) (hj : W ≤ V j)
      (x : ToType ((MatrixCocycle.chart (O := O) (m := m) k).val.obj (op W))),
      overlapApp V m φ l j hl hj (overlapApp V m φ k l hk hl x)
        = overlapApp V m φ k j hk hj x) :
    MatrixCocycle O V m where
  entry k l _W hk hl a b := overlapEntry V m φ k l hk hl a b
  entry_res k l _W _W' hk hl hW a b := by
    have hnat := (localModuleHomOfOver (V k ⊓ V l) (φ k l)).naturality (le_inf hk hl) hW
      (freeMk (op _W) fun c => if a = c then 1 else 0)
    have hres : res (MatrixCocycle.chart (O := O) (m := m) l) (homOfLE hW)
          (overlapApp V m φ k l hk hl (freeMk (op _W) fun c => if a = c then 1 else 0))
        = overlapApp V m φ k l (hW.trans hk) (hW.trans hl)
            (freeMk (op _W') fun c => if a = c then 1 else 0) :=
      Eq.trans hnat.symm (congrArg
        (fun y => overlapApp V m φ k l (hW.trans hk) (hW.trans hl) y)
        (res_freeMk_single (S := O) (ι := ULift.{u} (Fin (m k))) (homOfLE hW) a))
    rw [overlapEntry, overlapEntry, ← freeCoord_res, hres]
  entry_self k _W hk a b := by
    rw [overlapEntry, overlapApp, hid k]
    exact congrFun (freeCoord_freeMk (S := O) (op _) _) b
  entry_mul k l j _W hk hl hj a c := by
    have h1 : overlapApp V m φ k l hk hl (freeMk (op _W) fun e => if a = e then 1 else 0)
        = freeMk (op _W) (overlapEntry V m φ k l hk hl a) :=
      (freeMk_freeCoord (S := O) (op _W) _).symm
    have h2 : overlapEntry V m φ k j hk hj a c
        = freeCoord (op _W) (overlapApp V m φ l j hl hj
            (freeMk (op _W) (overlapEntry V m φ k l hk hl a))) c := by
      rw [overlapEntry, ← hcomp k l j hk hl hj, h1]
    rw [h2, freeCoord_overlapApp_freeMk V m φ l j hl hj]

end Stacks.SheafOfModules

end
