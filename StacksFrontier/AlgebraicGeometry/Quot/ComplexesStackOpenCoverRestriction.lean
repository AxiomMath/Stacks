module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBoundedCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackOpenCoverLimitPreserving

/-!
# `Complexes_{X/B}` is algebraic as soon as its restrictions over an open covering of `S` are

The paragraph "Choose an affine open covering `S = ⋃ U_i` ... we set `W = ∐ W_i`" of the proof of
Stacks 0DLN, for `𝒳 = Complexes_{X/B}` of Stacks 0DLE. If the restrictions
`𝒳 ×_{(Sch/S)_fppf} (Sch/U_i)_fppf` to the members of an open covering of `S` are algebraic
stacks, then so is `𝒳`. The atlases of the restrictions are locally of finite type over `S`
because `𝒳` is limit preserving (Stacks 0DLJ), and the isomorphism classes of objects of `𝒳`
over the spectra of fields are few
(`AlgebraicGeometry.Space.ComplexesSituation.exists_bound_mk_quotient_fiber`); the rest is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_isAlgebraicStack_restrictSquare_openCover_largeHoms`.

The total category of `Complexes_{X/B}` has its morphisms in the universe `u + 1`, while the
restriction `AlgebraicGeometry.Stack.restrictSquare` is formed at the universes of the site. The
restrictions are therefore taken of a small model `𝒴` of `𝒳`, a category fibred in groupoids at
the universes of the site together with an equivalence `e` over the site with `𝒳`; one such
model is `CategoryTheory.BasedCategory.shrinkHoms`, available because the diagonal is
representable (`AlgebraicGeometry.Stack.locallySmall_of_isAlgebraicSpaceIsomPresheaf`).

The hypotheses on `𝒳` itself are those of the source's lemmas, carried as hypotheses as in
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_charts`: fibred in groupoids
(Stacks 0DLF), the fppf stack condition (Stacks 0DLH), the diagonal (Stacks 0DLG) and limit
preservation (Stacks 0DLJ).

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_restrictSquare_openCover`.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u z t

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory

/-- **`Complexes_{X/B}` from algebraic restrictions over an open covering of `S`.** Let `𝒴` be a
small model of `𝒳 = Complexes_{X/B}`, with an equivalence `e` over the site. If `𝒳` is fibred in
groupoids (Stacks 0DLF), a stack for the fppf topology (Stacks 0DLH) with diagonal representable
by algebraic spaces (Stacks 0DLG) and limit preserving (Stacks 0DLJ), and the restrictions
`𝒴 ×_{(Sch/S)_fppf} (Sch/U_i)_fppf` to the members of an open covering `{U_i ⟶ S}` are algebraic
stacks, then `𝒳` is an algebraic stack. -/
theorem isAlgebraicStack_of_restrictSquare_openCover (D : ComplexesSituation B S hS)
    (h0DLF : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLH : (complexesFunctor D).IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS))
    (h0DLG : Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) h0DLF))
    (h0DLJ : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) h0DLF))
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p (complexesBasedCategory D).p)
    {ι : Type u} (U : ι → BigFppfOver B S hS)
    (hopen : ∀ i, AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (U i).hom))
    (hcover : ∀ s : S, ∃ i, s ∈ Set.range (B.inclusion.map (U i).hom))
    (halg : ∀ i, Stack.IsAlgebraicStack.{u, t} B S hS
      (Stack.restrictSquare B S hS 𝒴 (U i)).pt.val) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) := by
  let : (complexesFunctor D).IsFibered := h0DLF.isFibered
  exact Stack.isAlgebraicStack_of_isAlgebraicStack_restrictSquare_openCover_largeHoms B S hS h0DLF
    (Functor.isStack_of_isStackInGroupoids h0DLH) h0DLG h0DLJ 𝒴 e U hopen hcover halg
    (exists_bound_mk_quotient_fiber D)

end AlgebraicGeometry.Space.ComplexesSituation

end
