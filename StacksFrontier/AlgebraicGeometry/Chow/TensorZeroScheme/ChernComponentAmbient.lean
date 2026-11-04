module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ContainedComponentComparison

/-!
# Reading `c₁(L) ∩ [W]` at a component inside a closed subscheme

Let `j : Z ⟶ X` be a closed immersion over the base situation of chapter 42, let `L` be an
invertible `𝒪_X`-module and let `W` be an integral closed subscheme of `X` of δ-dimension `k+1`
which happens to lie inside `Z`. Then `c₁(L) ∩ [W]` can be computed in two places: on `X`, from
the component rule of `L` at `W`, and on `Z`, from the component rule of `j^*L` at the restriction
of `W` to `Z`. The two answers agree in `A_k(Z)` — and this file produces that agreement *with a
carrier*, as an `Stacks.Chow.IsRationallyEquivalentToZeroWithin` confined to `W`.

That is the shape a dévissage over integral components needs, and it is the one the identity of
[Stacks, Tag 0F98] needs twice over. In the case `W ⊆ D` of that tag the Gysin map `i₁^*` is
evaluated at the branch `W₁ ⊆ D₁` through the component rule of `p^*ℒ₁` **on `L`**, since that is
the ambient scheme the cycle `[p^{-1}W] = [W₁] + [W₂]` lives on, whereas the localized form of
Stacks 02SS compares it against the cap product of `p₁^*(ℒ₁|_D)` **on `D₁`**. Likewise `i^*` is
evaluated at `W ⊆ D` through the component rule of `ℒ₁ ⊗ ℒ₂` on `Y`, while 02SS wants the rule of
its restriction to `D`. Both are this file's statement at a different `j`.

## Main results

* `Stacks.Chow.firstChernComponentCycle_sub_isRationallyEquivalentToZeroWithin_of_iso` — the
  component cycle does not see an isomorphism of the module, up to rational equivalence within
  the component.
* `Stacks.Chow.firstChernComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin`
  — **the comparison above**: the component cycle of `j^*L` at a component `V` of `Z` differs from
  the pushforward to `Z` of the value of the rule of `L` at the scheme-theoretic image of `V` by a
  cycle rationally equivalent to zero within `V`.

## Implementation notes

### Why the image is a parameter with an equation

The scheme-theoretic image `V.map j` is the ideal sheaf `Stacks.Chow.pullbackComponentRule` is
defined at, but a consumer holds the component in a different spelling — in the case `W ⊆ D` of
[Stacks, Tag 0F98] as the join `D₁ ⊔ p^{-1}(W)`, the two being identified by
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_subschemeι`. Rewriting an ideal sheaf under the
morphism whose type it determines would put a cycle group under a transport along a concrete
equality, so the image is taken as a *parameter* `U` satisfying `V.map j = U`, together with the
immersion `g : U.subscheme ⟶ Z` it comes with. The equation is then discharged by `subst`, where
`U` is still a variable, and the two immersions are identified by cancelling the mono `j` rather
than by transport. This is the discipline of
`Stacks.Chow.TensorZeroScheme.Decomposition.schemeDeltaDimension_D₁_of_zeroIdeal_le`.

### Why this module sits under `TensorZeroScheme`

Nothing here mentions a divisor, a branch or a line bundle: `j` is an arbitrary closed immersion.
It lives beside its two consumers, as
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.SupComapSubscheme` does for the ideal-sheaf
facts the same dévissage needs.

## References

* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### The component cycle does not see an isomorphism of the module -/

/-- Rationally equivalent cycles on an integral component push forward to cycles whose difference
is rationally equivalent to zero within the component's support. -/
private theorem properPushforward_sub_isRationallyEquivalentToZeroWithin_support
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (k : ℤ)
    (W : Y.IdealSheafData) [LocallyOfFiniteType (W.subschemeι ≫ sY)]
    {a b : CycleGroup C (W.subschemeι ≫ sY) k}
    (hab : RationallyEquivalent C (W.subschemeι ≫ sY) k a b) :
    IsRationallyEquivalentToZeroWithin C sY k
      (properPushforward C (W.subschemeι ≫ sY) sY W.subschemeι rfl k a -
        properPushforward C (W.subschemeι ≫ sY) sY W.subschemeι rfl k b)
      (W.support : Set Y) :=
  (properPushforward_sub_isRationallyEquivalentToZeroWithin C (W.subschemeι ≫ sY) sY
    W.subschemeι rfl k hab).mono (by rw [Scheme.IdealSheafData.range_subschemeι])

/-- **The first Chern component cycle of an invertible module, up to an isomorphism of that
module, with a carrier.** For isomorphic invertible modules `L ≅ N` and an integral closed
subscheme `W ⊆ X` of δ-dimension `k+1`, the two component cycles differ by a cycle rationally
equivalent to zero on `X` witnessed inside `W`.

The two rules are rationally equivalent on `W` by
`Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_of_iso`, and the component cycle is
by definition the pushforward of the rule's value along the closed immersion of `W`, which
confines the witnesses to the image of that immersion. -/
theorem firstChernComponentCycle_sub_isRationallyEquivalentToZeroWithin_of_iso
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (k : ℤ)
    (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (e : L ≅ N) (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt)) :
    IsRationallyEquivalentToZeroWithin C sX k
      (firstChernComponentCycle C sX k (firstChernComponentCycleRule C sX k L) W hW hDim -
        firstChernComponentCycle C sX k (firstChernComponentCycleRule C sX k N) W hW hDim)
      (W.support : Set X) := by
  exact properPushforward_sub_isRationallyEquivalentToZeroWithin_support C sX k W
    (rationallyEquivalent_firstChernComponentCycleRule_of_iso C sX k L N e W hW hDim)

/-! ### Reading the component rule inside a closed subscheme -/

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (j : Z ⟶ X) [IsClosedImmersion j]
  (hj : j ≫ sX = sZ) (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

include hj in
/-- **The component cycle of `j^*L` at a component of `Z`, against the rule of `L` on `X`, with a
carrier.** Let `j : Z ⟶ X` be a closed immersion over the base, `L` an invertible `𝒪_X`-module and
`V ⊆ Z` an integral closed subscheme of δ-dimension `k+1`. Let `U ⊆ X` be the scheme-theoretic
image of `V`, presented by an immersion `g : U.subscheme ⟶ Z` over `j`. Then the component cycle
of `j^*L` at `V` differs from the pushforward to `Z` along `g` of the value at `U` of the
component rule of `L` by a cycle rationally equivalent to zero on `Z`, witnessed inside `V`.

The rule of `j^*L` at `V` and the rule of `L` transported along `j`,
`Stacks.Chow.pullbackComponentRule`, are rationally equivalent on `V` by
`Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule`; pushing
that equivalence forward along the closed immersion of `V` confines its witnesses to `V`. The
transported rule's component cycle is the pushforward of the value at the image by
`Stacks.Chow.firstChernComponentCycle_pullbackComponentRule`, and the immersion that pushforward
uses agrees with `g` because the two agree after the mono `j`. -/
theorem firstChernComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin
    (V : Z.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ sZ) = ((k + 1 : ℤ) : EInt))
    (U : X.IdealSheafData) (hU : V.map j = U) (g : U.subscheme ⟶ Z) [IsClosedImmersion g]
    (hg : g ≫ j = U.subschemeι) (hUint : IsIntegral U.subscheme)
    (hUdim : schemeDeltaDimension C (U.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt)) :
    IsRationallyEquivalentToZeroWithin C sZ k
      (firstChernComponentCycle C sZ k
          (firstChernComponentCycleRule C sZ k ((Scheme.Modules.pullback j).obj L)) V hV hDim -
        properPushforward C (U.subschemeι ≫ sX) sZ g
          (by rw [← hg, Category.assoc, hj]) k
          (firstChernComponentCycleRule C sX k L U hUint hUdim))
      (V.support : Set Z) := by
  subst hU
  have hgeq : g = (imageIsoOfIsClosedImmersion j V).inv ≫ V.subschemeι := by
    refine (cancel_mono j).1 ?_
    rw [hg, Category.assoc, ← imageIsoOfIsClosedImmersion_hom_subschemeι j V,
      Iso.inv_hom_id_assoc]
  subst hgeq
  rw [← firstChernComponentCycle_pullbackComponentRule C sZ sX j hj k
    (firstChernComponentCycleRule C sX k L) V hV hDim]
  exact properPushforward_sub_isRationallyEquivalentToZeroWithin_support C sZ k V
    (rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule C sZ sX j hj k L
      V hV hDim)

end Stacks.Chow

end
