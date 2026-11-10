module

public import StacksCore.CategoryTheory.Abelian.Subcategory
public import StacksCore.CategoryTheory.GrothendieckGroup.SerreClass
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Additivity
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerKGroup

/-!
# The cycle class homomorphism on the K-group of a dimension layer

Let `(S, δ)` be a base situation with a dimension function and let `X` be a scheme locally of
finite type over `S`. Writing `Coh_{≤k}(X)` for the coherent `𝒪_X`-modules whose support has
delta-dimension at most `k`, the assignment `F ↦ [F]_k` sending a coherent module to its
associated `k`-cycle is additive along short exact sequences and kills `Coh_{≤k-1}(X)`. It
therefore factors through the Grothendieck group of the dimension layer
`Coh_{≤k}(X)/Coh_{≤k-1}(X)` and defines a homomorphism

`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ Z_k(X)`

onto the group of `k`-cycles. This is the second of the two maps of Tag 02S9.

## Main definitions

* `Stacks.Chow.dimensionLayerCycle` — the cycle `[F]_k` of an object of `Coh_{≤k}(X)`.
* `Stacks.Chow.dimensionLayerCycleHom` — the homomorphism
  `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X)`.

## Main results

* `Stacks.Chow.dimensionLayerCycle_add` — the cycle class is additive along a short exact
  sequence of `Coh_{≤k}(X)`.
* `Stacks.Chow.dimensionLayerCycle_eq_zero_of_dimensionLayerClass` — the cycle class vanishes on
  `Coh_{≤k-1}(X)`.
* `Stacks.Chow.dimensionLayerCycleHom_of` — the homomorphism sends the class of the image of a
  coherent module `F` under the localization functor to `[F]_k`.

## Implementation notes

The factorization is the universal property of the Grothendieck group of a Serre quotient: the
map `K₀(Coh_{≤k}(X)) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` identifies its target with the quotient of
its source by the image of `K₀(Coh_{≤k-1}(X))`, so a homomorphism out of `K₀(Coh_{≤k}(X))` that
kills that image descends. The descent is written as the explicit composite of the quotient map
with the inverse of that identification, rather than extracted from the uniqueness statement.

Additivity is the additivity of `F ↦ [F]_k` on coherent modules, transported along the two
inclusions `Coh_{≤k}(X) ⟶ Coh(X) ⟶ Mod(𝒪_X)`, both of which are exact, being inclusions of weak
Serre subcategories.

The vanishing on `Coh_{≤k-1}(X)` is pointwise: a point of the support of a module of support
dimension at most `k - 1` has relative dimension at most `k - 1`, hence never the value `k` at
which the coefficients of `[F]_k` are read off.

## What is not proved

Tag 02S9 asserts that the homomorphism built here and the map `Z_k(X) → K₀(Coh_{≤k}(X)/
Coh_{≤k-1}(X))`, `∑ n_Z[Z] ↦ [⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]`, are mutually
inverse isomorphisms. That second map exists in this development in two constructions, built
independently and over different hypotheses. One is
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerClassOfCycle`, for a `k`-cycle of
finite
support and hence for `X` quasi-compact, which also proves that it is a section of the
homomorphism built here. The other is `Stacks.Chow.cycleDimensionLayerHom`, in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleFromCycles`, together with the
coherence of the locally finite direct sums it is built from
(`Stacks.Chow.isCoherent_cycleStructureSheaf`) and the bound on the delta-dimension of their
supports.

Of the two inverse identities, the one asserting that the composite `Z_k(X) →
K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X)` is the identity is proved there, as
`Stacks.Chow.dimensionLayerCycleHom_comp_cycleDimensionLayerHom`; it gives the injectivity of
that first map and the surjectivity of the homomorphism built here. The other identity, that the
composite `K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})` is the identity, is proved
for a **Noetherian** `X` in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass`, as
`Stacks.Chow.cycleDimensionLayerHom_comp_dimensionLayerCycleHom`, together with the bijectivity
of the two maps that follows, `Stacks.Chow.cycleDimensionLayerEquiv`. It rests on the equality of
the class of a coherent module of support dimension at most `k` with the class of the locally
finite direct sum of the structure sheaves of the integral closed subschemes of `[F]_k`, taken
with their multiplicities — `Stacks.Chow.DimensionLayerClassIsStructureSheafSum` — which the
dévissage filtration of Stacks 01YF supplies on a Noetherian scheme. Over a scheme that is merely
locally of finite type over the base that filtration is unavailable and the identity is not
formalized; the source argues there with the locally finite direct sum of the terms of a
filtration spread out from the stalks at the generic points of the support.

The assertion `Stacks.Chow.DimensionLayerIsStructureSheafSum`, that the module and the direct sum
become *isomorphic* in the dimension layer, is strictly stronger and is false, a module of length
two over a discrete valuation ring not being the square of its residue field; only the equality
of classes is available, and it is all the two homomorphisms see.

Not formalized in either construction: the second map for a general, non-quasi-compact `X`, which
would require a locally finite direct sum of structure sheaves of integral closed subschemes to be
a coherent module over a scheme merely locally of finite type over the base.

## References

* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02QZ](https://stacks.math.columbia.edu/tag/02QZ)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 02MX](https://stacks.math.columbia.edu/tag/02MX)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-! ### The cycle class on a dimension layer -/

/-- The `k`-cycle `[F]_k` of a coherent `𝒪_X`-module whose support has delta-dimension at most
`k`, read as a function on the objects of `Coh_{≤k}(X)`. -/
def dimensionLayerCycle (F : CoherentModulesDimLE C f k) : CycleGroup C f k :=
  haveI : _root_.SheafOfModules.IsCoherent F.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.obj.property
  cycleAssociatedToCoherentSheaf C f F.obj.obj k F.property

/-- **Stacks 02QZ** on a dimension layer. The cycle class is additive along a short exact
sequence of coherent `𝒪_X`-modules of support dimension at most `k`. -/
theorem dimensionLayerCycle_add ⦃S : ShortComplex (CoherentModulesDimLE C f k)⦄
    (hS : S.ShortExact) :
    dimensionLayerCycle C f k S.X₂ =
      dimensionLayerCycle C f k S.X₁ + dimensionLayerCycle C f k S.X₃ := by
  have h₁ : (S.map (coherentModulesDimLE C f k).ι).ShortExact :=
    (coherentModulesDimLE C f k).shortExact_map_ι hS
  have h₂ : ((S.map (coherentModulesDimLE C f k).ι).map
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι).ShortExact :=
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).shortExact_map_ι h₁
  have i₁ : _root_.SheafOfModules.IsCoherent ((S.map (coherentModulesDimLE C f k).ι).map
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι).X₁ :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₁.obj.property
  have i₂ : _root_.SheafOfModules.IsCoherent ((S.map (coherentModulesDimLE C f k).ι).map
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι).X₂ :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₂.obj.property
  have i₃ : _root_.SheafOfModules.IsCoherent ((S.map (coherentModulesDimLE C f k).ι).map
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι).X₃ :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₃.obj.property
  exact cycleAssociatedToCoherentSheaf_add C f _ h₂ k S.X₁.property S.X₂.property S.X₃.property

/-- The cycle class of a coherent `𝒪_X`-module whose support has delta-dimension at most `k - 1`
is zero: a point of the support has relative dimension at most `k - 1`, so it is not one of the
points of relative dimension `k` carrying the coefficients of a `k`-cycle. -/
private theorem cycleAssociatedToCoherentSheaf_eq_zero_of_le_pred (M : X.Modules) [M.IsCoherent]
    (hk : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ (k : EInt))
    (hk' : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ ((k - 1 : ℤ) : EInt)) :
    cycleAssociatedToCoherentSheaf C f M k hk = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  change (cycleAssociatedToCoherentSheaf C f M k hk).1 x = 0
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f M k hk hx]
    refine sheafMultiplicity_eq_zero_of_notMem_supp M fun hmem => ?_
    have hle := relativeDimension_le_of_mem_supp C f M hk' hmem
    omega
  · exact cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f M k hk hx

/-- The cycle class vanishes on the Serre class `Coh_{≤k-1}(X)` of `Coh_{≤k}(X)`. -/
theorem dimensionLayerCycle_eq_zero_of_dimensionLayerClass
    (F : (lowerDimensionClass C f (k - 1) k).FullSubcategory) :
    dimensionLayerCycle C f k F.obj = 0 := by
  have : _root_.SheafOfModules.IsCoherent F.obj.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.obj.obj.property
  exact cycleAssociatedToCoherentSheaf_eq_zero_of_le_pred C f k F.obj.obj.obj F.obj.property
    F.property

/-! ### The descent to the Grothendieck group of the layer -/

/-- The inclusion of the Serre class `Coh_{≤k-1}(X)` into `Coh_{≤k}(X)` carries short exact
sequences to short exact sequences. -/
theorem shortExact_map_ι_lowerDimensionClass
    ⦃S : ShortComplex (lowerDimensionClass C f (k - 1) k).FullSubcategory⦄ (hS : S.ShortExact) :
    (S.map (lowerDimensionClass C f (k - 1) k).ι).ShortExact :=
  (lowerDimensionClass C f (k - 1) k).shortExact_map_ι hS

/-- The localization functor onto the dimension layer carries short exact sequences to short
exact sequences. -/
theorem shortExact_map_q_lowerDimensionClass
    ⦃S : ShortComplex (CoherentModulesDimLE C f k)⦄ (hS : S.ShortExact) :
    (S.map (lowerDimensionClass C f (k - 1) k).isoModSerre.Q).ShortExact :=
  hS.map_of_exact _

/-- The cycle class as a homomorphism out of the Grothendieck group of `Coh_{≤k}(X)`. -/
def dimensionLayerCycleHomAux :
    GrothendieckGroup (CoherentModulesDimLE C f k) →+ CycleGroup C f k :=
  GrothendieckGroup.lift (dimensionLayerCycle C f k) (dimensionLayerCycle_add C f k)

/-- The cycle class homomorphism out of `K₀(Coh_{≤k}(X))` kills the image of
`K₀(Coh_{≤k-1}(X))`. -/
theorem dimensionLayerCycleHomAux_comp_map_ι :
    (dimensionLayerCycleHomAux C f k).comp
        (GrothendieckGroup.map (lowerDimensionClass C f (k - 1) k).ι
          (shortExact_map_ι_lowerDimensionClass C f k)) = 0 := by
  refine GrothendieckGroup.hom_ext fun F => ?_
  rw [AddMonoidHom.comp_apply, GrothendieckGroup.map_of, dimensionLayerCycleHomAux,
    GrothendieckGroup.lift_of, AddMonoidHom.zero_apply]
  exact dimensionLayerCycle_eq_zero_of_dimensionLayerClass C f k F

/-- **Stacks 02MX (1)** for the dimension layer: the Grothendieck group of the layer is the
Grothendieck group of `Coh_{≤k}(X)` modulo the image of that of `Coh_{≤k-1}(X)`. -/
def dimensionLayerGrothendieckGroupEquiv :
    GrothendieckGroup (CoherentModulesDimLE C f k) ⧸
        (GrothendieckGroup.map (lowerDimensionClass C f (k - 1) k).ι
          (shortExact_map_ι_lowerDimensionClass C f k)).range ≃+
      GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) :=
  ObjectProperty.SerreClassLocalization.grothendieckGroupEquiv
    (lowerDimensionClass C f (k - 1) k).isoModSerre.Q (lowerDimensionClass C f (k - 1) k)
    (shortExact_map_ι_lowerDimensionClass C f k) (shortExact_map_q_lowerDimensionClass C f k)

/-- **Stacks 02S9**, the map `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X)`, `F ↦ [F]_k`. The cycle
class of a coherent `𝒪_X`-module of support dimension at most `k` is additive along short exact
sequences and vanishes on support dimension at most `k - 1`, so it descends to the Grothendieck
group of the dimension layer. -/
@[stacks 02S9 "the map `K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X)`, `F ↦ [F]_k`"]
def dimensionLayerCycleHom :
    GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) →+ CycleGroup C f k :=
  (QuotientAddGroup.lift _ (dimensionLayerCycleHomAux C f k)
        ((AddMonoidHom.range_le_ker_iff _ _).2
          (dimensionLayerCycleHomAux_comp_map_ι C f k))).comp
    (dimensionLayerGrothendieckGroupEquiv C f k).symm.toAddMonoidHom

/-- **Stacks 02S9.** The homomorphism `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X)` sends the class of
the image of a coherent `𝒪_X`-module `F` of support dimension at most `k` to the cycle
`[F]_k`. -/
@[stacks 02S9 "the formula `F ↦ [F]_k` for the map out of `K₀(Coh_{≤k}/Coh_{≤k-1})`"]
theorem dimensionLayerCycleHom_of (F : CoherentModulesDimLE C f k) :
    dimensionLayerCycleHom C f k
        (GrothendieckGroup.of
          ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F)) =
      dimensionLayerCycle C f k F := by
  have h : (dimensionLayerGrothendieckGroupEquiv C f k).symm
      (GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F)) =
      QuotientAddGroup.mk (GrothendieckGroup.of F) :=
    ObjectProperty.SerreClassLocalization.grothendieckGroupEquiv_symm_of_obj _ _ _ _ F
  rw [dimensionLayerCycleHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h,
    QuotientAddGroup.lift_mk, dimensionLayerCycleHomAux, GrothendieckGroup.lift_of]

end Stacks.Chow

end
