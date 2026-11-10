module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusPowerTrivialization
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Modules.ReducedFiniteLocallyFree

/-!
# Invertibility of a reflexive module on an open meeting the isomorphism locus

Let `ℱ` be a coherent module on an integral locally Noetherian normal scheme `X` and `s` a global
section, with isomorphism locus `U` as in [Stacks, Tag 0EBN].  The fibre rank of `ℱ` is one at
every point of `U`, and an open `V` of `X` whose complement has codimension at least two contains
the generic point.  Consequently, if `ℱ|_V` is finite locally free and `V` meets `U`, then `ℱ|_V`
is invertible.

## Main results

* `Stacks.AlgebraicGeometry.ReflexivePowers.fiberRank_eq_one_of_mem_sectionIsomorphismOpen`: the
  fibre rank of `ℱ` is one at every point of the isomorphism locus of `s`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.fiberRank_genericPoint_eq_one`: if `U` is nonempty,
  the fibre rank of `ℱ` at the generic point is one.
* `Stacks.AlgebraicGeometry.ReflexivePowers.codimension_closureSingleton_genericPoint`: the
  generic point of an irreducible space has codimension zero.
* `Stacks.AlgebraicGeometry.ReflexivePowers.genericPoint_mem_of_forall_two_le_codimension`: an
  open whose complement has codimension at least two contains the generic point, hence is dense.
* `Stacks.AlgebraicGeometry.ReflexivePowers.isInvertible_restrict_of_isFiniteLocallyFree`:
  `ℱ|_V` is invertible as soon as it is finite locally free and `V` meets the isomorphism locus
  of `s`.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
* [Stacks Project, Tag 02I3](https://stacks.math.columbia.edu/tag/02I3)
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

/-! ### The fibre rank over the isomorphism locus -/

/-- A nonempty open of an integral scheme contains the generic point. -/
private theorem genericPoint_mem_of_mem {X : Scheme.{u}} [IsIntegral X] (W : X.Opens) {x : X}
    (hx : x ∈ W) : genericPoint X ∈ W :=
  ((genericPoint_spec X).specializes (Set.mem_univ x)).mem_open W.isOpen hx

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
  [F.IsCoherent] (s : F.sections)

/-- The fibre rank of `ℱ` is one at every point of the isomorphism locus of `s`. -/
theorem fiberRank_eq_one_of_mem_sectionIsomorphismOpen {z : X}
    (hz : z ∈ AlgebraicGeometry.sectionIsomorphismOpen X F s) :
    Scheme.Modules.fiberRank F z = 1 := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.sectionIsomorphismOpen X F s).ι).obj F) 1 :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (restrictUnitSectionIso X F s)
      (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit
        (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme)
  have h := Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.restrictFunctor
      (AlgebraicGeometry.sectionIsomorphismOpen X F s).ι).obj F) 1
    (⟨z, hz⟩ : (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme)
  exact (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict
    (AlgebraicGeometry.sectionIsomorphismOpen X F s).ι F
    (⟨z, hz⟩ : (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme)).symm.trans h

/-- The generic point lies in the isomorphism locus of `s` as soon as that locus is nonempty. -/
theorem genericPoint_mem_sectionIsomorphismOpen
    [hU : Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme] :
    genericPoint X ∈ AlgebraicGeometry.sectionIsomorphismOpen X F s :=
  genericPoint_mem_of_mem _ hU.some.2

/-- If the isomorphism locus of `s` is nonempty, the fibre rank of `ℱ` at the generic point is
one. -/
theorem fiberRank_genericPoint_eq_one
    [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme] :
    Scheme.Modules.fiberRank F (genericPoint X) = 1 :=
  fiberRank_eq_one_of_mem_sectionIsomorphismOpen X F s
    (genericPoint_mem_sectionIsomorphismOpen X F s)

/-! ### An open whose complement has codimension at least two is dense -/

variable {X}

/-- The closure of the generic point of an irreducible space has codimension zero. -/
theorem codimension_closureSingleton_genericPoint {T : Type u} [TopologicalSpace T]
    [IrreducibleSpace T] [QuasiSober T] :
    codimension (IrreducibleCloseds.closureSingleton (genericPoint T)) = 0 := by
  rw [codimension_eq_coheight]
  refine Order.coheight_eq_zero.mpr fun A hA => ?_
  change (A : Set T) ⊆ (IrreducibleCloseds.closureSingleton (genericPoint T) : Set T)
  rw [show (IrreducibleCloseds.closureSingleton (genericPoint T) : Set T) = Set.univ from
    genericPoint_spec T]
  exact Set.subset_univ _

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- An open whose complement has codimension at least two contains the generic point. -/
theorem genericPoint_mem_of_forall_two_le_codimension (V : X.Opens)
    (hV : ∀ x : X, x ∉ V →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    genericPoint X ∈ V := by
  by_contra hx
  have h := hV _ hx
  rw [codimension_closureSingleton_genericPoint (T := X)] at h
  exact absurd h (by decide)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- An open whose complement has codimension at least two meets every nonempty open, in the
generic point. -/
theorem nonempty_inf_of_forall_two_le_codimension (V : X.Opens)
    (hV : ∀ x : X, x ∉ V →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) (W : X.Opens) {x : X}
    (hx : x ∈ W) : genericPoint X ∈ V ⊓ W :=
  ⟨genericPoint_mem_of_forall_two_le_codimension V hV,
    genericPoint_mem_of_mem W hx⟩

/-! ### The upgrade to invertibility -/

variable (X)

/-- If `ℱ|_V` is finite locally free and some point `y` of `V` lies in the isomorphism locus of
`s`, then `ℱ|_V` is invertible. -/
theorem isInvertible_restrict_of_isFiniteLocallyFree (V : X.Opens)
    (hfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (y : V.toScheme) (hy : V.ι.base y ∈ AlgebraicGeometry.sectionIsomorphismOpen X F s) :
    Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F) := by
  have : Nonempty V.toScheme := ⟨y⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have := hfree
  exact Scheme.Modules.isInvertible_of_fiberRank_eq_one
    ((Scheme.Modules.restrictFunctor V.ι).obj F) y
    ((Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict V.ι F y).trans
      (fiberRank_eq_one_of_mem_sectionIsomorphismOpen X F s hy))

end Stacks.AlgebraicGeometry.ReflexivePowers

end

end
