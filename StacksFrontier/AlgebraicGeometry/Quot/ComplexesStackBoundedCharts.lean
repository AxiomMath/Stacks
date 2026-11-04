module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityReduction
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackSizeBound
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackBoundedCharts
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective

/-!
# `Complexes_{X/B}` is algebraic as soon as it has a jointly surjective family of smooth charts

The step "set `W = ∐ W_i`; we obtain a surjective smooth morphism `W → 𝒳`" of the proof of
Stacks 0DLN, for `𝒳 = Complexes_{X/B}` of Stacks 0DLE: smooth 1-morphisms `(Sch/W i) ⟶ 𝒳` from
schemes `W i` locally of finite type over `S`, jointly surjective on field objects, make `𝒳` an
algebraic stack, whatever the number and the sizes of the `W i`. The set-theoretic input, that
the isomorphism classes of objects of `𝒳` over the spectra of fields are few, is
`AlgebraicGeometry.Space.ComplexesSituation.exists_mk_quotient_fiber_le`; the rest is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_boundedCharts_largeHoms`.

The hypotheses on `𝒳` itself are those of the source: fibred in groupoids (Stacks 0DLF), the fppf
stack condition (Stacks 0DLH) and the diagonal (Stacks 0DLG), carried as hypotheses as in
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`. Nothing here is
registered.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_charts`.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u z

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory

/-- The fibres of `Complexes_{X/B}` over the spectra of fields of cardinality at most `size S`
have boundedly many isomorphism classes, by one cardinal below the cutoff of the site. -/
theorem exists_bound_mk_quotient_fiber (D : ComplexesSituation B S hS) :
    ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k], U.left.1 = Spec (.of k) →
        #k ≤ S.size →
        Cardinal.lift.{u, u + 1}
            #(Quotient (isIsomorphicSetoid ((complexesBasedCategory D).p.Fiber U))) ≤
          Cardinal.lift.{u + 1, u} κ := by
  obtain ⟨μ, hμ, h⟩ := exists_mk_quotient_fiber_le D
  have hsl := B.cutoff_isStrongPrelimit
  refine ⟨2 ^ 2 ^ 2 ^ max S.size μ, hsl (hsl (hsl (max_lt hS hμ))), fun U k _ hU hk => ?_⟩
  refine (h U k hU).trans (Cardinal.lift_le.mpr ?_)
  have hsize : ((BigFppfOver.toScheme B S hS).obj U).size ≤ S.size := by
    show (U.left.1).size ≤ S.size
    rw [hU, Scheme.size_Spec]
    exact max_le S.aleph0_le_size hk
  exact power_le_power_left two_ne_zero (power_le_power_left two_ne_zero
    (power_le_power_left two_ne_zero (max_le_max hsize le_rfl)))

/-- **`Complexes_{X/B}` from a jointly surjective family of smooth charts.** If `Complexes_{X/B}`
is fibred in groupoids (Stacks 0DLF), a stack for the fppf topology (Stacks 0DLH) with diagonal
representable by algebraic spaces (Stacks 0DLG), and admits smooth 1-morphisms `(Sch/W i) ⟶ 𝒳`,
jointly surjective on field objects, from schemes `W i` locally of finite type over `S`, then it is
an algebraic stack. -/
theorem isAlgebraicStack_of_charts (D : ComplexesSituation B S hS)
    (h0DLF : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLH : (complexesFunctor D).IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS))
    (h0DLG : Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) h0DLF))
    {ι : Type u} (W : ι → BigFppfOver B S hS)
    (a : ∀ i, (Stack.schemeFibredCategory B S hS (W i)).val ⥤ᵇ complexesBasedCategory D)
    (hsmooth : ∀ i (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ (complexesBasedCategory D).obj)
      (_hy : y ⋙ (complexesBasedCategory D).p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom)
          (Stack.schemeFibredCategory B S hS (W i)).val.p (complexesBasedCategory D).p y
          (a i).toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsSmooth B S hS (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom)
    (hlft : ∀ i, LocallyOfFiniteType (B.inclusion.map (W i).hom))
    (hsurj : ∀ (U : BigFppfOver B S hS), Stack.IsFieldObject B S hS U →
      ∀ (y : (complexesBasedCategory D).obj), (complexesBasedCategory D).p.obj y = U →
        ∃ (i : ι) (V : BigFppfOver B S hS), Stack.IsFieldObject B S hS V ∧
          ∃ (f : V ⟶ U) (x : (Stack.schemeFibredCategory B S hS (W i)).val.obj),
            (Stack.schemeFibredCategory B S hS (W i)).val.p.obj x = V ∧
            ∃ α : (a i).obj x ⟶ y, (complexesBasedCategory D).p.IsHomLift f α) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) := by
  let : (complexesFunctor D).IsFibered := h0DLF.isFibered
  exact Stack.isAlgebraicStack_of_boundedCharts_largeHoms B S hS h0DLF
    (Functor.isStack_of_isStackInGroupoids h0DLH) h0DLG W a hsmooth hlft hsurj
    (exists_bound_mk_quotient_fiber D)

end AlgebraicGeometry.Space.ComplexesSituation

end
