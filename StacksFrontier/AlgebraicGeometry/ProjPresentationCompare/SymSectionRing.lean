module

public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.HomogeneousProduct
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Basic

/-!
# The two graded rings of sections of `Sym(E)` are isomorphic, by the identity on summands

Over an open `U` of a scheme `X` and for a quasi-coherent `𝒪_X`-module `E`, the two
relative-`Proj` substrates of this repository both form the graded ring of homogeneous sections of
`Sym(E)` as the direct sum `⨁_{n ≥ 0} Sym^n(E)(U)` of the same homogeneous section groups. This
file builds the isomorphism of graded rings between them that is the identity on each summand.

It is not a definitional identity. `Stacks.SymGraded.situationSheafGradedAlgebra` *constructs* its
graded-ring structure from the algebra's homogeneous multiplication, while
`Stacks.RelativeProj.Situation.sectionRingGradedRing` selects one from an existence statement with
`Classical.choice`; the two agree only through the characterizing equations
`Stacks.RelativeProj.Situation.SectionRingStructure.mul_homogeneous` and `one_homogeneous`.

## Main definitions

* `Stacks.SymGraded.situationSectionRingHom` and
  `Stacks.SymGraded.situationSectionRingHomInv`: the two ring homomorphisms, each built from its
  values on the homogeneous summands.
* `Stacks.SymGraded.situationGradedHom`: the first of them, as a homomorphism of graded rings.

## Main results

* `Stacks.SymGraded.situationSectionRingHomInv_hom` and
  `Stacks.SymGraded.situationSectionRingHom_inv`: **the two are mutually inverse.**
* `Stacks.SymGraded.situationSectionRingHomInv_mem`: the second carries the selected grading into
  the constructed one.
* `Stacks.SymGraded.situationGradedHom_res`: the comparison commutes with restriction of
  homogeneous sections.
* `Stacks.SymGraded.situationSectionRingHom_strHom`: it commutes with the maps from the structure
  sheaf.

## Implementation notes

Each homomorphism is `DirectSum.toSemiring` of the family of summand inclusions of the *other*
substrate, so its two hypotheses are exactly the unit and the homogeneous product of the target —
`Stacks.RelativeProj.Situation.one_eq` and `of_mul_of` on one side,
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.one_eq` and `of_mul_of` on the
other. Nothing else about either ring structure is used, and in particular the two are never
compared with each other: that comparison is what the elaborator cannot afford, one of them being
behind a `Classical.choice`. That these maps are the identity on the carrier is then a
consequence — `situationSectionRingHomInv_hom` — rather than their definition.

For the same reason every statement here is its own declaration: a single proof mentioning both
ring structures at every step does not fit in the elaborator's heartbeat budget.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.SymGraded

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)
  (U : X.Opens)

/-- **The constructed graded ring of sections maps to the selected one**, by the identity on each
homogeneous summand. -/
public def situationSectionRingHom :
    (situationSheafGradedAlgebra E hqc).sectionRing U →+* (symSituation E).sectionRing U :=
  DirectSum.toSemiring (fun n => DirectSum.of ((symSituation E).sectionPieces U) n)
    (Stacks.RelativeProj.Situation.one_eq (symSituation E) U).symm
    (fun {i j} a b =>
      (Stacks.RelativeProj.Situation.of_mul_of (symSituation E) U i j a b).symm)

/-- **The selected graded ring of sections maps to the constructed one**, by the identity on each
homogeneous summand. -/
public def situationSectionRingHomInv :
    (symSituation E).sectionRing U →+* (situationSheafGradedAlgebra E hqc).sectionRing U :=
  DirectSum.toSemiring
    (fun n => DirectSum.of ((situationSheafGradedAlgebra E hqc).sectionPieces U) n)
    ((congrArg (DirectSum.of ((situationSheafGradedAlgebra E hqc).sectionPieces U) 0)
      ((Stacks.RelativeProj.Situation.sectionRingStructure (symSituation E)).one_homogeneous
        U)).trans ((situationSheafGradedAlgebra E hqc).one_eq U).symm)
    (fun {i j} a b =>
      (congrArg (DirectSum.of ((situationSheafGradedAlgebra E hqc).sectionPieces U) (i + j))
        (eq_of_heq ((Stacks.RelativeProj.Situation.sectionRingStructure
          (symSituation E)).mul_homogeneous U i j a b))).trans
            ((situationSheafGradedAlgebra E hqc).of_mul_of U a b).symm)

/-- On a homogeneous summand the first homomorphism is the summand inclusion. -/
public theorem situationSectionRingHom_of {i : ℕ}
    (a : (situationSheafGradedAlgebra E hqc).sectionPieces U i) :
    situationSectionRingHom E hqc U
        (DirectSum.of ((situationSheafGradedAlgebra E hqc).sectionPieces U) i a) =
      DirectSum.of ((symSituation E).sectionPieces U) i a :=
  DirectSum.toSemiring_of _ _ _ i a

/-- On a homogeneous summand the second homomorphism is the summand inclusion. -/
public theorem situationSectionRingHomInv_of {i : ℕ}
    (a : (symSituation E).sectionPieces U i) :
    situationSectionRingHomInv E hqc U (DirectSum.of ((symSituation E).sectionPieces U) i a) =
      DirectSum.of ((situationSheafGradedAlgebra E hqc).sectionPieces U) i a :=
  DirectSum.toSemiring_of _ _ _ i a

/-- Two additive maps between direct sums that compose to the identity on each summand
compose to the identity. -/
private theorem comp_apply_eq_of_forall_of {ι : Type*} [DecidableEq ι] {A B : ι → Type*}
    [∀ i, AddCommMonoid (A i)] [∀ i, AddCommMonoid (B i)]
    (f : DirectSum ι A →+ DirectSum ι B) (g : DirectSum ι B →+ DirectSum ι A)
    (h : ∀ i a, g (f (DirectSum.of A i a)) = DirectSum.of A i a) (x : DirectSum ι A) :
    g (f x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i a => exact h i a
  | add z w hz hw => simp [hz, hw]

/-- **The second homomorphism undoes the first.** -/
public theorem situationSectionRingHomInv_hom
    (x : (situationSheafGradedAlgebra E hqc).sectionRing U) :
    situationSectionRingHomInv E hqc U (situationSectionRingHom E hqc U x) = x :=
  comp_apply_eq_of_forall_of (situationSectionRingHom E hqc U).toAddMonoidHom
    (situationSectionRingHomInv E hqc U).toAddMonoidHom
    (fun _ a => (congrArg (situationSectionRingHomInv E hqc U)
      (situationSectionRingHom_of E hqc U a)).trans (situationSectionRingHomInv_of E hqc U a)) x

/-- **The first homomorphism undoes the second.** -/
public theorem situationSectionRingHom_inv (y : (symSituation E).sectionRing U) :
    situationSectionRingHom E hqc U (situationSectionRingHomInv E hqc U y) = y :=
  comp_apply_eq_of_forall_of (situationSectionRingHomInv E hqc U).toAddMonoidHom
    (situationSectionRingHom E hqc U).toAddMonoidHom
    (fun _ a => (congrArg (situationSectionRingHom E hqc U)
      (situationSectionRingHomInv_of E hqc U a)).trans (situationSectionRingHom_of E hqc U a)) y

/-- **The first homomorphism, as a homomorphism of graded rings.** -/
public def situationGradedHom :
    (situationSheafGradedAlgebra E hqc).grading U →+*ᵍ (symSituation E).sectionRingGrading U where
  __ := situationSectionRingHom E hqc U
  map_mem := by
    rintro i x ⟨a, rfl⟩
    exact ⟨a, (situationSectionRingHom_of E hqc U a).symm⟩

/-- **The comparison commutes with restriction of homogeneous sections.** -/
public theorem situationGradedHom_res (U V : X.Opens) (h : U ≤ V) :
    (situationGradedHom E hqc U).comp ((situationSheafGradedAlgebra E hqc).res h) =
      (Stacks.RelativeProj.Situation.gradedSectionRestriction (symSituation E) U V h).comp
        (situationGradedHom E hqc V) := by
  refine GradedRingHom.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | of n y =>
    have h1 : ((situationSheafGradedAlgebra E hqc).res h)
        (DirectSum.of ((situationSheafGradedAlgebra E hqc).sectionPieces V) n y) =
        DirectSum.of ((situationSheafGradedAlgebra E hqc).sectionPieces U) n
          ((situationSheafGradedAlgebra E hqc).resPiece h n y) :=
      (situationSheafGradedAlgebra E hqc).resRingHom_of h y
    have h2 := Stacks.RelativeProj.Situation.gradedSectionRestriction_of (symSituation E) U V h n y
    exact ((congrArg (situationSectionRingHom E hqc U) h1).trans
      (situationSectionRingHom_of E hqc U _)).trans
        ((congrArg
          (Stacks.RelativeProj.Situation.gradedSectionRestriction (symSituation E) U V h)
            (situationSectionRingHom_of E hqc V y)).trans h2).symm
  | add z w hz hw =>
    exact (map_add _ z w).trans
      ((congrArg₂ (fun p q : (symSituation E).sectionRing U => p + q) hz hw).trans
        (map_add _ z w).symm)

/-- **The comparison commutes with the maps from the structure sheaf.** -/
public theorem situationSectionRingHom_strHom (r : Γ(X, U)) :
    situationSectionRingHom E hqc U ((situationSheafGradedAlgebra E hqc).strHom U r) =
      (symSituation E).sectionRingBaseMap U r :=
  (congrArg (situationSectionRingHom E hqc U)
    ((situationSheafGradedAlgebra E hqc).strHom_apply U r)).trans
      ((situationSectionRingHom_of E hqc U _).trans
        ((Stacks.RelativeProj.Situation.sectionRingStructure
          (symSituation E)).baseMap_apply U r).symm)

/-- The second homomorphism carries the selected grading into the constructed one. -/
public theorem situationSectionRingHomInv_mem (i : ℕ) (y : (symSituation E).sectionRing U)
    (hy : y ∈ (symSituation E).sectionRingGrading U i) :
    situationSectionRingHomInv E hqc U y ∈ (situationSheafGradedAlgebra E hqc).grading U i := by
  obtain ⟨a, rfl⟩ := hy
  exact ⟨a, (situationSectionRingHomInv_of E hqc U a).symm⟩

end Stacks.SymGraded

end
