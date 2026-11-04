module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingIsomorphism

/-!
# The currying isomorphism of Stacks 0A90 on local sections is the double evaluation

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be complexes of `O`-modules. The currying
isomorphism of Stacks 0A90,
`SheafHom(K, SheafHom(L, M)) ≅ SheafHom(Tot(K ⊗_O L), M)`, is given on local sections by
`AlgebraicGeometry.RingedSite.curryFun`. On a local pure tensor, the curried section evaluated at
`k ⊗ l` is the section evaluated at `k` and then at `l`,

`(curryFun α)(k ⊗ l) = (α(k))(l)`,

with no sign and no hypothesis.

## Main results

* `AlgebraicGeometry.RingedSite.applyHomSectionOver_curryFun_tensorComplexSection`: the curried
  section evaluated at a local pure tensor is the double evaluation.
* `AlgebraicGeometry.RingedSite.applyHomSectionOver_curryFun_tensorComplexSection_over`: the same
  over an arbitrary arrow of the site.

## Implementation notes

The intermediate degrees `c = t + r`, `q = t + n` and `d` are explicit binders rather than
`by omega` side conditions: a proof term produced by `omega` inside a statement is not the one a
caller's goal carries, and `rw` then misses the pattern.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The currying isomorphism of Stacks 0A90 on local sections is the double evaluation: the
curried section `curryFun X U α`, evaluated at the pure tensor of `k` and `l`, is `α` evaluated at
`k` and then at `l`. -/
theorem applyHomSectionOver_curryFun_tensorComplexSection
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {n : ℤ} (U : X.C)
    (α : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U))
    (t r c d q : ℤ) (htr : t + r = c) (hcd : c + n = d) (htq : t + n = q)
    (hrd : r + q = d) (k : (K.X t).val.obj (op U)) (l : (L.X r).val.obj (op U)) :
    applyHomSectionOver X
        (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M) U U
        (𝟙 U) n c d hcd (curryFun X U α) (tensorComplexSection X t r c htr k l) =
      applyHomSection X (sheafHomComplex X L M) U q r d hrd
        (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U U (𝟙 U) n t q
          htq α k) l := by
  rw [applyHomSectionOver_curryFun X U α c d hcd t r htr (𝟙 U) k l,
    ← curryRule_degree X U α t r d q htq hrd (𝟙 U) k l]

/-- The currying isomorphism of Stacks 0A90 is the double evaluation over an arbitrary arrow
`g : W ⟶ U` of the site: the curried section, evaluated over `g` at the pure tensor of `k` and
`l`, is `α` evaluated over `g` at `k` and then at `l`. -/
theorem applyHomSectionOver_curryFun_tensorComplexSection_over
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {n : ℤ} (U : X.C)
    (α : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U))
    (t r c d q : ℤ) (htr : t + r = c) (hcd : c + n = d) (htq : t + n = q)
    (hrd : r + q = d) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    applyHomSectionOver X
        (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) M) U W
        g n c d hcd (curryFun X U α) (tensorComplexSection X t r c htr k l) =
      applyHomSection X (sheafHomComplex X L M) W q r d hrd
        (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g n t q
          htq α k) l := by
  rw [applyHomSectionOver_curryFun X U α c d hcd t r htr g k l,
    ← curryRule_degree X U α t r d q htq hrd g k l]

end AlgebraicGeometry.RingedSite

end
