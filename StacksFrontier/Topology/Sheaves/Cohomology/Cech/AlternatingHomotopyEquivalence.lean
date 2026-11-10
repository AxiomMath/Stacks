module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.GroupTheory.FreeAbelianGroup
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ChainHomotopy
import StacksCore.Tactic.StacksAttribute

/-!
# The alternating Čech complex is homotopy equivalent to the Čech complex

Fix a linearly ordered index set `I`, a family `U : I → Opens X` of open subsets of a
topological space and an abelian presheaf `F`. Signed sorting of the index tuples is a
projection `π` from the usual Čech cochains onto the alternating ones, and `c` is the
inclusion of the ordered cochains back; the composite `c ∘ π` is an endomorphism of the usual
Čech complex which is the identity on the alternating subcomplex.

That endomorphism is homotopic to the identity, and that is the content of this file. The
homotopy is built where it is visible: over each open `V`, the formal tuples whose
intersections contain `V` span a chain complex, the "supported chains" over `V`, and coning at
a vertex of a tuple contracts the cycles of that complex. Applied recursively to the
difference between the identity and signed sorting, coning produces a chain homotopy which is
compatible with restriction of `V`; pairing the resulting formal chains against sections of
`F` turns it into a homotopy of Čech cochains. Nothing is assumed about the family `U`: it
need not cover anything.

## Main definitions

* `Stacks.Cech.cechComparisonProjection`: the endomorphism `c ∘ π` of the usual Čech complex.

## Main results

* `Stacks.Cech.cechComparisonProjection_homotopic_id`: `c ∘ π` is homotopic to the identity.
* `Stacks.Cech.alternatingCechInclusion_homotopyEquivalence`: the canonical inclusion of the
  alternating Čech complex into the usual one is a homotopy equivalence, with `c ∘ π` as a
  homotopy inverse.

## Implementation notes

The usual and alternating Čech complexes, and the inclusion of the second into the first, are
the explicit models `Stacks.Cech.cechComplex`, `Stacks.Cech.alternatingCechComplex` and
`Stacks.Cech.alternatingCechInclusion` of Tag 01FH; the cochain-level operations `cechD`, `c`,
`pi` and `alternatingSubgroup` are those of Tag 01FJ.

The homotopy equivalence is asserted for the inclusion into that explicit model, and not for
its composite with a comparison isomorphism to Mathlib's `CategoryTheory.cechComplexFunctor`.
Tag 01FH supplies the degreewise comparison `Stacks.Cech.cechComplexObjIso`, and
`Stacks.Cech.cechComplexIso` -- in
`StacksFrontier.Topology.Sheaves.Cohomology.Cech.ComplexComparison`, which imports this file's
dependencies rather than this file -- assembles those comparisons into an isomorphism of
complexes. Being a homotopy equivalence is invariant under composition with an isomorphism of
complexes, so the statement for the composite follows from the one proved here.

The chain-level constructions are stated for the "probe" presheaf as well as for `F`: a
presheaf whose sections over `W` are the functions on the proofs that `V ≤ W`. Evaluating the
universal supported chain against it recovers a formal chain from its pairings, which is how
identities between formal chains are deduced from identities between Čech cochains.

## References

* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace Stacks.Cech

open Stacks.Cech.ChainHomotopy

universe u v w

variable {X : TopCat.{u}} {I : Type v} [LinearOrder I]
  (U : I → Opens X) (F : TopCat.Presheaf Ab.{w} X)


/-- The comparison `c` from ordered to usual Čech cochains, composed with the
projection `π` from usual to ordered cochains. -/
noncomputable def cechComparisonProjection :
    cechComplex U F ⟶ cechComplex U F :=
  CochainComplex.ofHom
    (fun p => AddCommGrpCat.ofHom
      ((CechCochains.c U F p).comp (CechCochains.pi U F p)))
    (fun p => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      simp only [cechComplex_d]
      change CechCochains.cechD U F p
          (CechCochains.c U F p (CechCochains.pi U F p s)) =
        CechCochains.c U F (p + 1)
          (CechCochains.pi U F (p + 1) (CechCochains.cechD U F p s))
      rw [← CechCochains.c_chainMap U F p (CechCochains.pi U F p s)]
      congr 1)

private noncomputable def cochainHomotopyComponent (i j : ℕ) :
    (cechComplex U F).X i ⟶ (cechComplex U F).X j :=
  if h : j + 1 = i then h ▸ AddCommGrpCat.ofHom (cochainHomotopy U F j) else 0

private theorem cochainHomotopyComponent_succ (j : ℕ) :
    cochainHomotopyComponent U F (j + 1) j =
      AddCommGrpCat.ofHom (cochainHomotopy U F j) := by
  simp only [cochainHomotopyComponent, dite_true]

/-- The endomorphism `c ∘ π` is homotopic to the identity on the usual Čech
complex. -/
@[stacks 01FM "c after projection is homotopic to the identity"]
theorem cechComparisonProjection_homotopic_id :
    Nonempty (Homotopy (cechComparisonProjection U F)
      (𝟙 (cechComplex U F))) := by
  refine ⟨Homotopy.symm
    { hom := cochainHomotopyComponent U F
      zero := fun _ _ h => dite_eq_right h
      comm := ?_ }⟩
  intro i
  rw [Homotopy.dNext_cochainComplex, cochainHomotopyComponent_succ]
  cases i with
  | zero =>
    rw [Homotopy.prevD_zero_cochainComplex, add_zero]
    simp only [cechComplex_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    change s = cochainHomotopy U F 0 (CechCochains.cechD U F 0 s) +
      CechCochains.c U F 0 (CechCochains.pi U F 0 s)
    rw [cochainHomotopy_zero, zero_add, comparison_zero]
  | succ p =>
    rw [Homotopy.prevD_succ_cochainComplex, cochainHomotopyComponent_succ]
    simp only [cechComplex_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    change s = cochainHomotopy U F (p + 1) (CechCochains.cechD U F (p + 1) s) +
      CechCochains.cechD U F p (cochainHomotopy U F p s) +
        CechCochains.c U F (p + 1) (CechCochains.pi U F (p + 1) s)
    rw [cochainHomotopy_identity, sub_add_cancel]

/-- The canonical inclusion of alternating Čech cochains into the usual Čech complex is a
homotopy equivalence: the signed-sorting projection is a homotopy inverse. -/
@[stacks 01FM "the canonical inclusion is a homotopy equivalence"]
theorem alternatingCechInclusion_homotopyEquivalence
    (G : TopCat.Presheaf Ab.{max v w} X) :
    (HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.up ℕ))
      (alternatingCechInclusion U G) := by
  let q : cechComplex U G ⟶ alternatingCechComplex U G :=
    CochainComplex.ofHom
      (fun p => AddCommGrpCat.ofHom
        (((CechCochains.c U G p).comp (CechCochains.pi U G p)).codRestrict
          (CechCochains.alternatingSubgroup U G p)
          (fun s => CechCochains.c_isAlternating U G p (CechCochains.pi U G p s))))
      (fun p => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        apply Subtype.ext
        simp only [alternatingCechComplex_d, cechComplex_d]
        change CechCochains.cechD U G p
            (CechCochains.c U G p (CechCochains.pi U G p s)) =
          CechCochains.c U G (p + 1)
            (CechCochains.pi U G (p + 1) (CechCochains.cechD U G p s))
        rw [← CechCochains.c_chainMap U G p (CechCochains.pi U G p s)]
        congr 1)
  let e : HomotopyEquiv (alternatingCechComplex U G) (cechComplex U G) :=
    { hom := alternatingCechInclusion U G
      inv := q
      homotopyHomInvId := Homotopy.ofEq (by
        apply HomologicalComplex.Hom.ext
        funext p
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        apply Subtype.ext
        change CechCochains.c U G p (CechCochains.pi U G p s.1) = s.1
        exact CechCochains.c_pi_of_isAlternating U G p s.1 s.2)
      homotopyInvHomId := by
        convert (cechComparisonProjection_homotopic_id U G).some using 1
        apply HomologicalComplex.Hom.ext
        funext p
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        rfl }
  exact e.homotopyEquivalences_hom

end Stacks.Cech
