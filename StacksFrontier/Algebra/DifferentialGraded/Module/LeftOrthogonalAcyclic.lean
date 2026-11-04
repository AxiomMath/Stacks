module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DirectSumHomotopy
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleHom
public import StacksCore.Tactic.StacksAttribute

/-! # Modules with property (P) are orthogonal to the acyclic modules

Let `(A, d)` be a differential graded algebra and let `P` be a right differential graded
`A`-module with property (P). Then `Hom_{K(A, d)}(P, N) = 0` for every acyclic differential
graded `A`-module `N`; that is, `P` lies in the left orthogonal of the acyclic objects of the
homotopy category. This is Stacks Tag 09KM, and it is what makes the modules with property (P)
the collection to which the construction of the left derived functors is applied.

## Main results

* `DifferentialGradedModule.leftOrthogonal_acyclic_directSumShifts`: a direct sum of shifts of
  the algebra is orthogonal on the left to the acyclic modules.
* `DifferentialGradedModule.leftOrthogonal_acyclic_of_propertyP`: Stacks Tag 09KM.

## Implementation notes

The proof is the assembly of three parts, each of which lives elsewhere. A shift of the regular
module is orthogonal on the left to the acyclic modules
(`DifferentialGradedModule.leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule`,
Tag 09K1); orthogonality passes
to a direct sum (`DifferentialGradedModule.leftOrthogonal_acyclic_of_directSum`), which gives
it for the graded pieces of a property-(P) filtration, since those are direct sums of shifts;
and orthogonality passes from the bottom stage and the graded pieces to the filtered module
(`DifferentialGradedModule.leftOrthogonal_acyclic_of_admissibleFiltration`), which is the
telescope argument of Tag 09KL carried out on homotopies.

The statement is about a module *equipped with* a property-(P) filtration rather than one
merely admitting one, which is how `DifferentialGradedModule.PropertyPFiltration` presents the
notion; the two differ only by `Nonempty`, and Tag 09KP produces the structure itself.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`, following `DifferentialGradedModule`.
The Stacks statement carries no such restriction.

## References

* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- The two encodings of the sign `(-1)^n` agree. -/
private alias negOnePow_cast := Unbundled.negOnePow_cast

variable {A : DifferentialGradedAlgebra R}

/-- The `j`-th coprojection intertwines the differential of a shift of the algebra with the
componentwise differential of a direct sum of shifts.

This is the compatibility with the differentials of `directSumShiftsInj` below, but stated over
the bare direct sum `⨁ _ : ι, A.A` and with the differential of the direct sum written out as
the `DirectSum.toModule` it is. That spelling is what makes the statement usable: the carrier of
`directSumShifts A k` is this direct sum only up to unfolding at default transparency, which is
more than instance search performs, so `Module R (directSumShifts A k).M` does not synthesize
and no rewrite can be set up against it. Here every instance is the honest one, and the
structure field discharges the lemma by `exact`, which does check definitional equality at
default transparency. -/
theorem lof_comp_shift_d (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (k : ι → ℤ) (j : ι) :
    (DirectSum.lof R ι (fun _ : ι => A.A) j).comp (((k j).negOnePow : ℤ) • A.d)
      = (DirectSum.toModule R ι (⨁ _ : ι, A.A) (fun i =>
            (DirectSum.lof R ι (fun _ : ι => A.A) i).comp
              (((-1 : ℤ) ^ (k i).natAbs) • A.d))).comp
          (DirectSum.lof R ι (fun _ : ι => A.A) j) :=
  LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof, LinearMap.smul_apply,
      negOnePow_cast]

/-- The `j`-th coprojection of a direct sum of shifts of the algebra. -/
def directSumShiftsInj (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (k : ι → ℤ) (j : ι) : shift (regularModule A) (k j) ⟶ directSumShifts A k where
  toFun := DirectSum.lof R ι (fun _ => A.A) j
  map_smul x a := by
    change DirectSum.of (fun _ : ι => A.A) j (MulOpposite.op a • x)
      = MulOpposite.op a • DirectSum.of (fun _ : ι => A.A) j x
    exact (map_smul (DirectSum.lof (MulOpposite A.A) ι (fun _ : ι => A.A) j)
      (MulOpposite.op a) x)
  map_grading n x hx := by
    intro i
    by_cases h : j = i
    · subst h
      change DirectSum.of (fun _ : ι => A.A) j x j ∈ A.grading (n + k j)
      rw [DirectSum.of_eq_same]
      exact hx
    · change DirectSum.of (fun _ : ι => A.A) j x i ∈ A.grading (n + k i)
      rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      exact (A.grading (n + k i)).zero_mem
  map_d := lof_comp_shift_d A k j

/-- A direct sum of shifts of the algebra is orthogonal on the left to the acyclic differential
graded modules. -/
theorem leftOrthogonal_acyclic_directSumShifts (A : DifferentialGradedAlgebra R)
    {ι : Type u} [DecidableEq ι] (k : ι → ℤ) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (directSumShifts A k)) :=
  leftOrthogonal_acyclic_of_directSum (directSumShiftsInj A k)
    (LinearEquiv.refl (MulOpposite A.A) (⨁ _ : ι, A.A))
    (fun _ _ => rfl)
    (fun _ _ hz j => hz j)
    (fun j => leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule A (k j))

/-- **Stacks Tag 09KM.** *"Let `(A, d)` be a differential graded algebra. Let `P` be a
differential graded `A`-module with property (P). Then `Hom_{K(Mod_(A,d))}(P, N) = 0` for all
acyclic differential graded `A`-modules `N`."*

Here the vanishing of all those hom-sets is phrased as membership of `P` in the left orthogonal
of the acyclic objects of the homotopy category, which says that every morphism out of `P` into
an object satisfying `acyclic'` is zero; since every object of `HomotopyCategory A` is the image
of a differential graded module, the two readings agree. -/
@[stacks 09KM]
theorem leftOrthogonal_acyclic_of_propertyP {P : DifferentialGradedModule A}
    (F : PropertyPFiltration P) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P) := by
  have hQ : ∀ i, (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj
      (@directSumShifts _ _ _ _ (F.quotientDecidableEq i) (F.quotientShift i))) := fun i =>
    @leftOrthogonal_acyclic_directSumShifts _ _ _ _ (F.quotientDecidableEq i) (F.quotientShift i)
  have hbot : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (F.F 0)) :=
    leftOrthogonal_acyclic_of_iso A (F.bottomMap.isoOfBijective F.bottom_bijective).symm
      (@leftOrthogonal_acyclic_directSumShifts _ _ _ _ F.bottomDecidableEq F.bottomShift)
  exact leftOrthogonal_acyclic_of_admissibleFiltration F.F
    (fun i => @directSumShifts _ _ _ _ (F.quotientDecidableEq i) (F.quotientShift i))
    F.ι F.incl F.quotientMap F.injective F.incl_comp F.admissible F.quotient_surjective
    F.quotient_ker F.exhaustive hbot hQ

end DifferentialGradedModule

end
