module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingNaturality

/-!
# Lifting a finite sum of local pure tensors through a subcomplex

Let `(C, O)` be a ringed site, let `j : 𝒦 ⟶ ℳ` be a map of cochain complexes of `O`-modules, and
let a section of `Tot(ℳ ⊗ 𝒩)` over an object `W` be written as a finite sum of local pure tensors
`∑ a ⊗ b`. If each `a` lifts along `j`, then the corresponding sum of pure tensors in
`Tot(𝒦 ⊗ 𝒩)` maps, under `Tot(j ⊗ 1)`, to the section itself.

This is the step the source of the first assertion of Stacks 0FPV performs on the coevaluation:
"let `𝒦 ⊆ ℳ` be any subcomplex of `O`-modules containing the sections `fᵢ`. Since
`Tot(𝒦 ⊗ 𝒩) ⊂ Tot(ℳ ⊗ 𝒩)` by flatness of the modules `𝒩^n`, we see that `η` factors through
`η̃ : O ⟶ Tot(𝒦 ⊗ 𝒩)`." The containment is
`Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f`; the factorisation of the section
itself is what is proved here.

## Main results

* `AlgebraicGeometry.RingedSite.tensorComplexMap_sum_tensorComplexSection_lift`: the statement
  above.

## Implementation notes

The ringed-space form of this is
`Stacks.Cohomology.LeftDualPerfect.mapBifunctorMap_lift_eq`
(`Topology/Sheaves/Cohomology/PerfectComplexes/TotalComplexLocalSections.lean:209`). It is **not**
generalized in place here, and the reason is that it is written in a different vocabulary: it
spells a local pure tensor as `HomologicalComplex.ιMapBifunctor` applied to
`Stacks.Cohomology.LeftDualPerfect.pureTensor`, and restriction as that file's own `res` for
`W ≤ V` of opens. Generalizing it would mean generalizing the five lemmas of its proof chain
(`pureTensor`, `res_pureTensor`, `res_sum`, `mapBifunctorMap_ι_pureTensor`,
`res_sum_ι_pureTensor`) to arrows of a site, which would install a second site-wide pure-tensor
vocabulary beside the one this directory already has — `tensorComplexSection`, with
`tensorComplexSection_restrict` for restriction along an arrow and
`tensorComplexMap_tensorComplexSection` for the induced map of total complexes. So the statement
is made once, in the vocabulary that already exists, and the two spellings are identified by
`AlgebraicGeometry.RingedSite.tensorComplexSection_eq_ι`.

**The statement carries no restriction, and that is deliberate.** The ringed-space form restricts
from `V` to `W` inside the statement, which forces the awkward half: a presheaf-of-modules
restriction `M.val.map g.op` lands in `(ModuleCat.restrictScalars …).obj (M.val.obj (op W))`
rather than in `M.val.obj (op W)`, so a sum of pure tensors built from restricted sections is only
type-correct up to unfolding `restrictScalars`, and `rw` reports the goal as not type-correct at
`implicit` transparency. The producer does not need it anyway: the sections
`AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection` hands back already live over
the member of the covering sieve. A consumer which must restrict first restricts the sections —
with `PresheafOfModules.restrictₛₗ`, the spelling that has the right target type and the one
`Stacks.Sites.ExtensionByZero.exists_sieve_subcomplex` uses — and applies this at the smaller
object.

The degree `c` is arbitrary rather than `0`: nothing in the argument uses the degree, and the
consumer wants `c = 0` only because the coevaluation lands there.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory

variable (X : RingedSite.{u, u, u})
variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable
  {A B K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The lift of a decomposed section through a subcomplex.** If each section `a p` of `A` lifts
along `j : K ⟶ A` to `y p`, then the sum of the pure tensors `y p ⊗ b p` in `Tot(K ⊗ B)` is
carried by `Tot(j ⊗ 1)` to the sum of the pure tensors `a p ⊗ b p` in `Tot(A ⊗ B)`.

The index shape — a `Fintype` with degree functions `t`, `r` summing to `c` — is the one
`AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection` produces, whose sections live
over the member of the covering sieve rather than over the object below it. There is accordingly
no restriction in the statement: a consumer that has to restrict first does so to the sections,
and applies this at the smaller object. -/
theorem tensorComplexMap_sum_tensorComplexSection_lift (j : K ⟶ A) (c : ℤ) {W : X.C}
    {κ : Type} [Fintype κ] (t r : κ → ℤ) (h : ∀ p, t p + r p = c)
    (a : ∀ p, (A.X (t p)).val.obj (op W)) (b : ∀ p, (B.X (r p)).val.obj (op W))
    (y : ∀ p, (K.X (t p)).val.obj (op W))
    (hy : ∀ p, (j.f (t p)).val.app (op W) (y p) = a p) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map j).app B ≫
          ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (𝟙 B)).f c).val.app (op W)
        (∑ p, tensorComplexSection X (t p) (r p) c (h p) (y p) (b p)) =
      ∑ p, tensorComplexSection X (t p) (r p) c (h p) (a p) (b p) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [tensorComplexMap_tensorComplexSection, hy]
  rfl

end AlgebraicGeometry.RingedSite

end
