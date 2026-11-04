module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEOfIsLESingle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.TrivialRange
public import StacksFrontier.Homology.DerivedCategory.PerfectApproximation
import StacksCore.Tactic.StacksAttribute

/-!
# The induction on `n - m` that proves pseudo-coherence from the top degree down

Let `(C, O)` be a ringed site and let `m` be an integer.  Stacks 08HE (2) ⇒ (1), and with it
Stacks 0DII, is proved by descending induction on the top nonvanishing cohomological degree `n` of
an object `E` of `D(O)`: one produces a morphism `K ⟶ E` with `K` `m`-pseudo-coherent, surjective
on `Hⁿ`, whose cone has no cohomology in any degree `≥ n`, applies the induction hypothesis to the
cone and concludes with Stacks 08FV.

This file is the recursion, separated from the production of the morphism.  The object that
descends is `n`, the measure is `(n + 1 - m).toNat`, and the recursion bottoms out at `n < m`,
where the base case
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isZero_homology` applies.

## What is a hypothesis and why

The step of the induction is **not** a statement about `E` alone: in Stacks 08HE the morphism
`K ⟶ E` exists because `ε^*E` is `m`-pseudo-coherent (through Stacks 08FX and 08HD) and because
`Hⁿ(E)` is quasi-coherent, and both of those have to hold of the cone as well for the recursion to
continue.  The standing hypotheses are therefore abstracted into a single predicate `P` on objects
of `D(O)`, which the step is required to carry from `E` to the cone.  Nothing is assumed about `P`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_distTriang_isZero_homology_obj₃_of_epi`: the bridge from a
  morphism to the triangle the recursion consumes — a morphism `K ⟶ E` that is surjective on `Hⁿ`,
  with `K` and `E` having no cohomology above `n`, sits in a distinguished triangle whose third
  vertex has no cohomology in any degree `≥ n`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep`: **the recursion.**

## Implementation notes

The cone computation is not reproved here: it is
`DerivedCategory.HomologySequence.isZero_homology_obj₃_of_epi_top`
(`StacksFrontier/Homology/DerivedCategory/PerfectApproximation.lean`), which is exactly the
three-term long exact sequence argument this step needs and which substitutes without recovery —
it is stated for an arbitrary abelian category with a derived category and carries no sheaf
hypotheses.

The recursion is run as an induction on a natural number bounding the measure rather than by
well-founded recursion on `ℤ`, so that the base case is a single `Nat.rec` branch and the step
needs no `decreasing_by`.  The bound is `≤ k` rather than `= k` so that the induction hypothesis
applies to the cone without an auxiliary monotonicity lemma.

## References

* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u w d

namespace AlgebraicGeometry.RingedSite

section Cone

variable {A : Type u} [Category.{w} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- **A morphism surjective on top cohomology sits in a distinguished triangle whose third vertex
has no cohomology from that degree on.**  Let `f : K ⟶ E` be a morphism of `D(A)` with `K` and `E`
having no cohomology in degrees `> n` and with `Hⁿ(f)` an epimorphism.  Then `f` is the first
morphism of a distinguished triangle `K ⟶ E ⟶ Q ⟶ K⟦1⟧` with `Hʲ(Q) = 0` for every `j ≥ n`.

This is the bridge between the production of the morphism, which is geometric, and the recursion
below, which is not.  The cone computation is
`DerivedCategory.HomologySequence.isZero_homology_obj₃_of_epi_top`. -/
public theorem exists_distTriang_isZero_homology_obj₃_of_epi {K E : DerivedCategory A} (n : ℤ)
    (f : K ⟶ E)
    (hK : ∀ j : ℤ, n < j → IsZero ((DerivedCategory.homologyFunctor A j).obj K))
    (hE : ∀ j : ℤ, n < j → IsZero ((DerivedCategory.homologyFunctor A j).obj E))
    (hf : Epi ((DerivedCategory.homologyFunctor A n).map f)) :
    ∃ (Q : DerivedCategory A) (g : E ⟶ Q) (h : Q ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory A) ∧
        ∀ j : ℤ, n ≤ j → IsZero ((DerivedCategory.homologyFunctor A j).obj Q) := by
  obtain ⟨Q, g, h, hT⟩ := distinguished_cocone_triangle f
  exact ⟨Q, g, h, hT,
    DerivedCategory.HomologySequence.isZero_homology_obj₃_of_epi_top _ hT n hK hE hf⟩

end Cone

section Site

variable (X : RingedSite.{u, u, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory

omit [∀ U : X.C, HasDerivedCategory.{d}
  (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))] in
/-- **The induction on `n - m` of Stacks 08HE (2) ⇒ (1).**  Let `(C, O)` be a ringed site, let `m`
be an integer and let `P` be any predicate on objects of `D(O)` — in the application it records
the standing hypotheses that make the step possible, namely that `ε^*E` is `m`-pseudo-coherent and
that the cohomology sheaves of `E` are quasi-coherent.

Suppose that for every `E` satisfying `P` whose cohomology vanishes above some `n ≥ m` there is a
distinguished triangle whose second vertex is `E`, whose first vertex is `m`-pseudo-coherent, and
whose third vertex both satisfies `P` and has no cohomology in any degree `≥ n`.  Then every `E`
satisfying `P` with cohomology vanishing above some degree is `m`-pseudo-coherent.

The recursion decreases `(n + 1 - m).toNat`: the third vertex has cohomology vanishing above
`n - 1`, and at `n < m` the conclusion is the base case
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isZero_homology`.  The conclusion for `E` is
read off the third and first vertices by Stacks 08FV part (2),
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_two_general`. -/
public theorem isPseudoCoherentFrom_of_descentStep (m : ℤ)
    (P : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) → Prop)
    (hstep : ∀ (F : DerivedCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℤ), m ≤ n → P F →
      (∀ j : ℤ, n < j →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj F)) →
      ∃ T : Triangle
          (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
        T ∈ distTriang
            (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ∧
          Nonempty (T.obj₂ ≅ F) ∧ X.IsPseudoCoherentFrom T.obj₁ m ∧ P T.obj₃ ∧
          ∀ j : ℤ, n ≤ j →
            IsZero ((DerivedCategory.homologyFunctor
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj T.obj₃))
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℤ)
    (hE : ∀ j : ℤ, n < j →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj E))
    (hP : P E) :
    X.IsPseudoCoherentFrom E m := by
  suffices H : ∀ k : ℕ, ∀ n : ℤ, (n + 1 - m).toNat ≤ k →
      ∀ F : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
        (∀ j : ℤ, n < j →
          IsZero ((DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj F)) →
          P F → X.IsPseudoCoherentFrom F m from
    H (n + 1 - m).toNat n le_rfl E hE hP
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk F hF hPF
    by_cases hnm : n < m
    · exact X.isPseudoCoherentFrom_of_isZero_homology F m fun j hj => hF j (by omega)
    · obtain ⟨T, hT, ⟨e⟩, hone, hPthree, hthree⟩ := hstep F n (by omega) hPF hF
      exact isPseudoCoherentFrom_of_iso X m
        (isPseudoCoherentFrom_of_distinguished_two_general X m T hT hone
          (ih (n - m).toNat (by omega) (n - 1) (by omega) T.obj₃
            (fun j hj => hthree j (by omega)) hPthree)) e.symm

end Site

end AlgebraicGeometry.RingedSite

end
