module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTensorExact
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTwistNoEmbedded
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.NowhereDenseSubobjectDimension
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian

/-!
# The twist of a coherent module in a dimension layer

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project, let
`ℒ` be an invertible `𝒪_X`-module and let `ℱ` be coherent with `dim_δ(Supp ℱ) ≤ k + 1`. This file
proves the **membership clause of [Stacks, Tag 02SX]**:

`[ℱ ⊗ ℒ] - [ℱ] ∈ Bₖ(X) ⊆ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`.

`StacksFrontier/AlgebraicGeometry/Chow/Degrees/DimensionLayerTwistNoEmbedded.lean` proves this when
`ℱ` has no embedded associated points. The reduction to that case is the source's first
paragraph, in the one-step form: [Stacks, Tag 02OL] produces the greatest coherent subsheaf
`𝒦 ⊆ ℱ` whose support is nowhere dense in `Supp ℱ`, the quotient `ℱ' = ℱ/𝒦` has no embedded
associated points and the same support as `ℱ`, and `dim_δ(Supp 𝒦) ≤ k`. Tensoring by `ℒ` is an
autoequivalence, hence exact, so

`[ℱ ⊗ ℒ] - [ℱ] = ([𝒦 ⊗ ℒ] - [𝒦]) + ([ℱ' ⊗ ℒ] - [ℱ'])`

in `K₀(Coh_{≤k+1}/Coh_{≤k-1})`; the first bracket lies in `Bₖ(X)` because both of its terms do,
the supports of `𝒦` and of `𝒦 ⊗ ℒ` having delta-dimension at most `k`, and the second is the case
already proved.

The source applies Tag 02OL twice, because its second clause — the cap-product identity — needs
the decomposition of the cycle `[ℱ]_{k+1}`. For the membership one application is enough.

## Main results

* `Stacks.Chow.coherentDimensionKZeroMk_layerMkTensor_sub_mem` — the membership above.

## Implementation notes

**No `@[stacks 02SX]` attribute.** Tag 02SX is a conjunction: the membership in `Bₖ(X)` *and* the
identity `c₁(ℒ) ∩ [ℱ]_{k+1}` for the image of that element under `Bₖ(X) → CH_k(X)`. Only the
membership is proved here; the second clause is
`Stacks.Chow.coherentDimensionLayerImageChowHom_eq_firstChernClassCap` of
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTwistCap`, and the attribute sits on
`Stacks.Chow.exists_mem_coherentDimensionLayerImage_layerMkTensor_sub` there, which states both.

**The quotient's support bound is read off the equality of supports** that Tag 02OL part (1)
gives, not from a general statement about quotients: `Stacks.Chow.relativeDimension_le_of_mem_supp`
turns the hypothesis on `Supp ℱ` into a pointwise bound, which
`Stacks.Chow.schemeDeltaDimension_reducedSupport_le` turns back into a bound for `ℱ'`.

## References

* [Stacks Project, Tag 02SX](https://stacks.math.columbia.edu/tag/02SX)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.CoherentSubquotients

universe u

namespace Stacks.Chow

/-- **[Stacks, Tag 02SX], the membership clause.** Let `X` be locally of finite type over the
base scheme of a Chow situation, let `ℒ` be an invertible `𝒪_X`-module and let `ℱ` be coherent
with `dim_δ(Supp ℱ) ≤ k + 1`. Then the element `[ℱ ⊗ ℒ] - [ℱ]` of
`K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` lies in the subgroup `Bₖ(X)` of [Stacks, Tag 02SC].

Only the membership is proved, not the cap-product identity that Tag 02SX also asserts; see the
module docstring. -/
theorem coherentDimensionKZeroMk_layerMkTensor_sub_mem (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt)) :
    coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMkTensor C f (k + 1) F L hL hdim) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) ∈
      coherentDimensionLayerImage C f k := by
  have hXN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  -- the greatest nowhere dense coherent subsheaf of Tag 02OL, and the quotient by it
  obtain ⟨K, hK, hmax⟩ := exists_greatest_isNowhereDenseCoherentSubobject F
  have hKcoh : (K : X.Modules).IsCoherent := hK.1
  have hQcoh : (cokernel K.arrow).IsCoherent := isCoherent_cokernel K.arrow
  have hQemb : HasNoEmbeddedAssociatedPoints (cokernel K.arrow) :=
    cokernel_hasNoEmbeddedAssociatedPoints F K hK hmax
  have hKTcoh : (tensorModules (K : X.Modules) L).IsCoherent :=
    isCoherent_tensorModules_of_isInvertible (K : X.Modules) L hL
  -- the two support bounds
  have hKdimk : schemeDeltaDimension C ((reducedSupport (K : X.Modules)).subschemeι ≫ f) ≤
      (k : EInt) :=
    schemeDeltaDimension_isNowhereDenseCoherentSubobject_le C f F K hK hdim
  have hKdim : schemeDeltaDimension C ((reducedSupport (K : X.Modules)).subschemeι ≫ f) ≤
      ((k + 1 : ℤ) : EInt) :=
    hKdimk.trans (WithBotTop.coe_le_coe.mpr (by omega))
  have hsuppQ : SheafOfModules.supp (cokernel K.arrow) = SheafOfModules.supp F :=
    supp_cokernel_eq F K hK
  have hQdim : schemeDeltaDimension C ((reducedSupport (cokernel K.arrow)).subschemeι ≫ f) ≤
      ((k + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_reducedSupport_le C f (cokernel K.arrow) fun x hx =>
      relativeDimension_le_of_mem_supp C f F hdim (hsuppQ ▸ hx)
  -- the short exact sequence `0 ⟶ 𝒦 ⟶ ℱ ⟶ ℱ' ⟶ 0` and its twist
  have hSES : (ShortComplex.mk K.arrow (cokernel.π K.arrow)
      (cokernel.condition K.arrow)).ShortExact :=
    ShortComplex.shortExact_mk_cokernel_π K.arrow
  have hadd : coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1)
          (layerMk C f (k + 1) (K : X.Modules) hKdim) +
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          (layerMk C f (k + 1) (cokernel K.arrow) hQdim) :=
    coherentDimensionKZeroMk_add_of_modules C f (k - 1) (k + 1)
      (A := layerMk C f (k + 1) (K : X.Modules) hKdim) (B := layerMk C f (k + 1) F hdim)
      (D := layerMk C f (k + 1) (cokernel K.arrow) hQdim)
      K.arrow (cokernel.π K.arrow) (cokernel.condition K.arrow) hSES
  have haddT := coherentDimensionKZeroMk_layerMkTensor_add_of_modules C f (k - 1) (k + 1)
    K.arrow (cokernel.π K.arrow) (cokernel.condition K.arrow) hSES L hL hKdim hdim hQdim
  -- the three memberships
  have hmemK := coherentDimensionKZeroMk_mem_coherentDimensionLayerImage C f k
    (layerMk C f (k + 1) (K : X.Modules) hKdim) hKdimk
  have hmemKT := coherentDimensionKZeroMk_mem_coherentDimensionLayerImage C f k
    (layerMkTensor C f (k + 1) (K : X.Modules) L hL hKdim)
    (schemeDeltaDimension_reducedSupport_tensorModules_le C f (K : X.Modules) L hKdimk)
  have hmemQ := coherentDimensionKZeroMk_layerMkTensor_sub_mem_of_hasNoEmbeddedAssociatedPoints
    C f (cokernel K.arrow) hQemb L hL hQdim
  -- split the difference along the sequence
  have hkey : coherentDimensionKZeroMk C f (k - 1) (k + 1)
        (layerMkTensor C f (k + 1) F L hL hdim) -
      coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) =
      (coherentDimensionKZeroMk C f (k - 1) (k + 1)
            (layerMkTensor C f (k + 1) (K : X.Modules) L hL hKdim) -
          coherentDimensionKZeroMk C f (k - 1) (k + 1)
            (layerMk C f (k + 1) (K : X.Modules) hKdim)) +
        (coherentDimensionKZeroMk C f (k - 1) (k + 1)
            (layerMkTensor C f (k + 1) (cokernel K.arrow) L hL hQdim) -
          coherentDimensionKZeroMk C f (k - 1) (k + 1)
            (layerMk C f (k + 1) (cokernel K.arrow) hQdim)) := by
    rw [hadd, haddT]
    abel
  rw [hkey]
  exact add_mem (sub_mem hmemKT hmemK) hmemQ

end Stacks.Chow

end
