module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolOrder
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineOrders
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# A prime cycle cut out by a global function is rationally equivalent to zero

Let `Z` be an integral scheme locally of finite type over the base scheme `S` of chapter 42 of
the Stacks Project, of delta-dimension `m`, and let `w ∈ Z` be a point of relative dimension
`m - 1`. Let `t ∈ Γ(Z, ⊤)` be a global function whose germ at `w` generates the maximal ideal of
the local ring `𝒪_{Z,w}`, and which is invertible at every point outside the closed subset
`closure {w}`. Then the prime cycle `[closure {w}]` of the integral closed subscheme attached to
`w` is rationally equivalent to zero on `Z`.

The reason is that `t`, read as a nonzero element of the function field `R(Z)` through
`AlgebraicGeometry.Scheme.germToFunctionField`, has principal divisor exactly `[closure {w}]`:
its order of vanishing is `1` at `w`, because the germ generates the maximal ideal there, and
`0` at every other point, either because the point has codimension different from one — where
`AlgebraicGeometry.Scheme.ord` is zero by convention — or because the germ of `t` is a unit
there. The second case is where the support hypothesis enters: a codimension-one point at which
`t` is not invertible would lie in `closure {w}`, hence have relative dimension strictly below
that of `w`, while codimension one forces it to be `m - 1`, which is the relative dimension of
`w` itself.

With that cycle identity in hand the statement is Stacks 02RW applied to the one-element family
consisting of `Z` itself, which is `Stacks.Chow.isRationallyEquivalentToZero_of_eq_principalCycle`.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZero_primeCycle_of_span_germ_eq_maximalIdeal` — the prime
  cycle of a point of relative dimension `m - 1` cut out by such a global function is rationally
  equivalent to zero.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Order

universe u

namespace Stacks.Chow

section PrincipalPrimeCycle

variable (C : ChowSituation.{u}) {Z : Scheme.{u}} (p : Z ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral Z]

/-- On an integral scheme every irreducible component is the whole space, so the generic point of
a component is the generic point of the scheme. -/
private theorem genericPoint_irreducibleComponents_eq (W : irreducibleComponents Z) :
    W.2.1.genericPoint = genericPoint Z := by
  have hη : IsGenericPoint W.2.1.genericPoint (W : Set Z) :=
    W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)
  have hWuniv : (W : Set Z) = Set.univ := by
    simpa [irreducibleComponents_eq_singleton] using W.2
  exact IsGenericPoint.eq (Eq.trans hη hWuniv) (genericPoint_spec Z)

/-- On an integral scheme of delta-dimension `m` over the base, every irreducible component has
relative dimension `m` at its generic point: there is only one component, and the
delta-dimension of the scheme is computed at its generic point. -/
private theorem relativeDimension_genericPoint_irreducibleComponents {m : ℤ}
    (hm : schemeDeltaDimension C p = (m : EInt)) (W : irreducibleComponents Z) :
    relativeDimension C.dimensionFunction p W.2.1.genericPoint = m := by
  rw [genericPoint_irreducibleComponents_eq W]
  exact WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C p).symm.trans hm)

/-- **A prime cycle cut out by a global function is rationally equivalent to zero.**

Let `Z` be integral of delta-dimension `m` over the base, let `w ∈ Z` have relative dimension
`m - 1`, and let `t` be a nonzero global function on `Z` whose germ at `w` generates the maximal
ideal of `𝒪_{Z,w}` and which is invertible at every point outside `closure {w}`. Then `t` is a
local equation for the prime cycle of `w`: its principal divisor is that prime cycle, so the
prime cycle is rationally equivalent to zero by Stacks 02RW. -/
theorem isRationallyEquivalentToZero_primeCycle_of_span_germ_eq_maximalIdeal {m : ℤ}
    (hm : schemeDeltaDimension C p = (m : EInt)) (w : Z)
    (hw : relativeDimension C.dimensionFunction p w = m - 1)
    (t : Γ(Z, ⊤)) (ht : t ≠ 0)
    (hmax : Ideal.span {(Z.presheaf.germ ⊤ w trivial).hom t} =
      IsLocalRing.maximalIdeal (Z.presheaf.stalk w))
    (hsupp : ∀ z : Z, ¬ IsUnit ((Z.presheaf.germ ⊤ z trivial).hom t) →
      z ∈ closure ({w} : Set Z)) :
    IsRationallyEquivalentToZero C p (m - 1)
      (cycleAssociatedToClosedSubscheme C p (integralComponentAt w).subschemeι (m - 1)) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨w, trivial⟩⟩
  -- the codimension of `w` is one
  have hco : coheight w = 1 :=
    coheight_eq_one_of_relativeDimension_eq_sub_one C p
      (relativeDimension_genericPoint_irreducibleComponents C p hm) hw
  -- the delta-dimension of the prime cycle of `w`
  have hDim : schemeDeltaDimension C ((integralComponentAt w).subschemeι ≫ p)
      = ((m - 1 : ℤ) : EInt) :=
    schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C p w hw
  -- the rational function cut out by `t`
  set f : Z.functionField := Z.germToFunctionField ⊤ t with hfdef
  have hf : f ≠ 0 := fun h ↦
    ht (Scheme.germToFunctionField_injective Z ⊤ (by simpa [hfdef] using h))
  -- the prime cycle of `w` is the principal divisor of `t`
  have hcycle : (cycleAssociatedToClosedSubscheme C p
      (integralComponentAt w).subschemeι (m - 1)).1 = principalCycle Z f := by
    refine Function.locallyFinsuppWithin.ext fun z ↦ ?_
    rw [principalCycle_apply]
    by_cases hz1 : coheight z = 1
    · by_cases hzw : z = w
      · subst hzw
        rw [cycleAssociatedToClosedSubscheme_integralComponentAt_self C p z hDim,
          ord_eq_ringOrd_germ hz1 (V := ⊤) trivial t ht
            (n := 1) (by simpa using ord_eq_one_of_span_eq_maximalIdeal hmax)]
        norm_num
      · have hunit : IsUnit ((Z.presheaf.germ ⊤ z trivial).hom t) := by
          by_contra hnu
          have hlt := relativeDimension_lt_of_mem_closure_of_ne C p (hsupp z hnu) hzw
          have hzdim : relativeDimension C.dimensionFunction p z = m - 1 :=
            (deltaDimension_closure_singleton C p z).symm.trans
              (deltaDimension_closure_singleton_eq_sub_one C p hm hz1)
          rw [hw, hzdim] at hlt
          omega
        rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p (m - 1) w hzw,
          ord_eq_ringOrd_germ hz1 (V := ⊤) trivial t ht (n := 0) (ord_eq_zero_of_isUnit hunit)]
        norm_num
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hz1 f]
      exact cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p (m - 1) w
        fun h ↦ hz1 (h ▸ hco)
  exact isRationallyEquivalentToZero_of_eq_principalCycle C p
    (by rwa [sub_add_cancel]) hf _ hcycle

end PrincipalPrimeCycle

end Stacks.Chow

end
