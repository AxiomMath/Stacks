module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentKZeroDimensionFiltration
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ChowToWideLayer
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentQuotientKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerClassOfCycle
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.KTheory.SerreQuotient

/-!
# The canonical maps `CH_k(X) ⟶ gr_k K'₀(X)`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a
quasi-compact scheme locally of finite type over `S`. Section 42.57 (Stacks 0FEV) observes that
the graded piece `gr_k K'₀(X) = F_k K'₀(X) / F_{k-1} K'₀(X)` of the filtration of `K'₀(X)` by
dimension of supports sits inside `K'₀(X)/F_{k-1} K'₀(X) = K₀(Coh(X)/Coh_{≤k-1}(X))`, and that
Remark 42.23.5 (Stacks 02SD) therefore gives canonical maps

  `CH_k(X) ⟶ gr_k K'₀(X)`,  `[Z] ↦ [𝒪_Z]`.

This file constructs these maps and proves that they are surjective when `X` is Noetherian.

## Main definitions

* `Stacks.Chow.dimLEToGradedCoherentKZero` — the homomorphism `K₀(Coh_{≤k}(X)) ⟶ gr_k K'₀(X)`,
  `[F] ↦ [F]`.
* `Stacks.Chow.layerToGradedCoherentKZero` — its descent along `K₀(Coh_{≤k}(X)) ⟶
  K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`, which is onto with kernel the image of `K₀(Coh_{≤k-1}(X))` by
  Stacks 02MX.
* `Stacks.Chow.gradedToCoherentQuotientKZero` — the inclusion
  `gr_k K'₀(X) ⟶ K₀(Coh(X)/Coh_{≤k-1}(X))`.
* `Stacks.Chow.cycleToGradedCoherentKZero` — the composite `Z_k(X) ⟶ gr_k K'₀(X)` of the map of
  Stacks 02S9 with `Stacks.Chow.layerToGradedCoherentKZero`.
* `Stacks.Chow.chowToGradedCoherentKZero` — the canonical map `CH_k(X) ⟶ gr_k K'₀(X)`, for `X`
  quasi-compact.

## Main results

* `Stacks.Chow.gradedToCoherentQuotientKZero_injective` — `gr_k K'₀(X) ⟶ K₀(Coh(X)/Coh_{≤k-1}(X))`
  is injective, by Stacks 02MX (1) for the Serre subcategory `Coh_{≤k-1}(X)` of `Coh(X)`.
* `Stacks.Chow.cycleToGradedCoherentKZero_eq_zero_of_mem_rationalEquivalences` — on a
  quasi-compact `X` the composite kills cycles rationally equivalent to zero.
* `Stacks.Chow.chowToGradedCoherentKZero_mk_integralComponent` — the canonical map sends the
  class of the integral closed subscheme `Z` attached to a point of relative dimension `k` to the
  class of `𝒪_Z`.
* `Stacks.Chow.cycleToGradedCoherentKZero_dimensionLayerCycle` — on a Noetherian `X`, the class
  in `gr_k K'₀(X)` of a coherent module of support dimension at most `k` is the image of its
  cycle `[F]_k`.
* `Stacks.Chow.chowToGradedCoherentKZero_surjective` — on a Noetherian `X` the canonical map is
  surjective.

## Implementation notes

The map is assembled from the dimension layer rather than from the Chow group directly. The
composite `Z_k(X) ⟶ K₀(Coh_{≤k}/Coh_{≤k-1}) ⟶ gr_k K'₀(X)` is followed by the injection into
`K₀(Coh(X)/Coh_{≤k-1}(X))`, and there it agrees with the composite through the wider layer
`K₀(Coh_{≤k+1}/Coh_{≤k-1})`, which kills rational equivalences by Stacks 0FDS
(`Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences_of_compactSpace`).
This is the source's construction: Remark 02SD composes the map of Stacks 0FDS with the map
`K₀(Coh_{≤k+1}/Coh_{≤k-1}) ⟶ K₀(Coh/Coh_{≤k-1})`, and Section 0FEV reads the result in
`gr_k K'₀(X) ⊆ K₀(Coh/Coh_{≤k-1})`.

Quasi-compactness of `X` enters only through Stacks 0FDS as formalized, and is a hypothesis of
the proposition Stacks 0FEW which consumes these maps.

## References

* [Stacks Project, Tag 0FEV](https://stacks.math.columbia.edu/tag/0FEV)
* [Stacks Project, Tag 02SD](https://stacks.math.columbia.edu/tag/02SD)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02MX](https://stacks.math.columbia.edu/tag/02MX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] ObjectProperty.preservesFiniteLimits_ι
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass


/-- A shortcut for instance search: the lower dimension bound is closed under finite products
inside the category cut out by the upper bound, which with the import closure of this file is
otherwise found only past the default size limit of instance synthesis. -/
instance lowerDimensionClass_isClosedUnderFiniteProducts (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (a b : ℤ) :
    (lowerDimensionClass C f a b).IsClosedUnderFiniteProducts :=
  inferInstance

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  [IsLocallyNoetherian X]

/-! ### From the dimension layer to the graded piece -/

/-- The homomorphism `K₀(Coh_{≤k}(X)) ⟶ gr_k K'₀(X)` sending the class of a coherent module of
support dimension at most `k` to its class in the graded piece. -/
def dimLEToGradedCoherentKZero (k : ℤ) :
    KZero (CoherentModulesDimLE C f k) →+ gradedCoherentKZero C f k :=
  KZero.lift
    (fun F => toGradedCoherentKZero C f k
      ⟨KZero.mk _ F.obj, mk_mem_coherentKZeroFiltration C f k F⟩)
    fun S hS => by
      rw [← map_add]
      congr 1
      exact Subtype.ext
        (KZero.mk_of_shortExact _ (hS.map_of_exact (coherentModulesDimLE C f k).ι))

/-- The homomorphism `K₀(Coh_{≤k}(X)) ⟶ gr_k K'₀(X)` sends the class of `F` to its class in the
graded piece. -/
@[simp]
theorem dimLEToGradedCoherentKZero_mk (k : ℤ) (F : CoherentModulesDimLE C f k) :
    dimLEToGradedCoherentKZero C f k (KZero.mk _ F) =
      toGradedCoherentKZero C f k ⟨KZero.mk _ F.obj, mk_mem_coherentKZeroFiltration C f k F⟩ :=
  KZero.lift_mk _ _ F

omit [IsLocallyNoetherian X] in
/-- An element of `F_k K'₀(X)` which lies in `F_{k-1} K'₀(X)` has zero class in `gr_k K'₀(X)`. -/
theorem toGradedCoherentKZero_eq_zero_iff (k : ℤ) (x : coherentKZeroFiltration C f k) :
    toGradedCoherentKZero C f k x = 0 ↔
      (x : CoherentKZero X) ∈ coherentKZeroFiltration C f (k - 1) := by
  rw [toGradedCoherentKZero, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf]

/-- The homomorphism `K₀(Coh_{≤k}(X)) ⟶ gr_k K'₀(X)` kills the image of `K₀(Coh_{≤k-1}(X))`. -/
theorem dimLEToGradedCoherentKZero_comp_map_ι (k : ℤ) :
    (dimLEToGradedCoherentKZero C f k).comp
        (KZero.map (lowerDimensionClass C f (k - 1) k).ι) = 0 :=
  KZero.hom_ext fun B => by
    rw [AddMonoidHom.comp_apply, KZero.map_mk, dimLEToGradedCoherentKZero_mk,
      AddMonoidHom.zero_apply, toGradedCoherentKZero_eq_zero_iff]
    exact mk_mem_coherentKZeroFiltration C f (k - 1) ⟨B.obj.obj, B.property⟩

/-- The localization `K₀(Coh_{≤k}(X)) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`. -/
abbrev dimLEToLayer (k : ℤ) :
    KZero (CoherentModulesDimLE C f k) →+ coherentDimensionKZero C f (k - 1) k :=
  KZero.map (lowerDimensionClass C f (k - 1) k).isoModSerre.Q

omit [IsLocallyNoetherian X] in
/-- The localization `K₀(Coh_{≤k}(X)) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is surjective. -/
theorem dimLEToLayer_surjective (k : ℤ) : Function.Surjective (dimLEToLayer C f k) :=
  KZero.surjective_map_localization (lowerDimensionClass C f (k - 1) k) _

/-- The homomorphism `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ gr_k K'₀(X)` sending the class of a coherent
module of support dimension at most `k` to its class in the graded piece. It exists because
`K₀(Coh_{≤k}(X)) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is onto with kernel the image of
`K₀(Coh_{≤k-1}(X))`, Stacks 02MX (1). -/
def layerToGradedCoherentKZero (k : ℤ) :
    coherentDimensionKZero C f (k - 1) k →+ gradedCoherentKZero C f k :=
  AddMonoidHom.liftOfRightInverse (dimLEToLayer C f k)
    (Function.surjInv (dimLEToLayer_surjective C f k))
    (Function.rightInverse_surjInv _)
    ⟨dimLEToGradedCoherentKZero C f k, fun x hx => by
      obtain ⟨y, rfl⟩ := (KZero.exact_map_ι_map_localization (lowerDimensionClass C f (k - 1) k)
        (lowerDimensionClass C f (k - 1) k).isoModSerre.Q x).1 hx
      exact DFunLike.congr_fun (dimLEToGradedCoherentKZero_comp_map_ι C f k) y⟩

/-- The localization sends the class of a coherent module to its class in the layer. -/
private theorem dimLEToLayer_mk {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (F : CoherentModulesDimLE C f k) :
    dimLEToLayer C f k (KZero.mk _ F) = coherentDimensionKZeroMk C f (k - 1) k F :=
  KZero.map_mk _ F

/-- The homomorphism `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ gr_k K'₀(X)` composed with the localization
`K₀(Coh_{≤k}(X)) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is `Stacks.Chow.dimLEToGradedCoherentKZero`. -/
theorem layerToGradedCoherentKZero_dimLEToLayer (k : ℤ)
    (x : KZero (CoherentModulesDimLE C f k)) :
    layerToGradedCoherentKZero C f k (dimLEToLayer C f k x) = dimLEToGradedCoherentKZero C f k x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- The homomorphism out of the dimension layer sends the class of a coherent module of support
dimension at most `k` to its class in `gr_k K'₀(X)`. -/
@[simp]
theorem layerToGradedCoherentKZero_mk (k : ℤ) (F : CoherentModulesDimLE C f k) :
    layerToGradedCoherentKZero C f k (coherentDimensionKZeroMk C f (k - 1) k F) =
      toGradedCoherentKZero C f k ⟨KZero.mk _ F.obj, mk_mem_coherentKZeroFiltration C f k F⟩ := by
  rw [← dimLEToLayer_mk, layerToGradedCoherentKZero_dimLEToLayer,
    dimLEToGradedCoherentKZero_mk]

/-- Every element of `gr_k K'₀(X)` comes from the dimension layer. -/
theorem layerToGradedCoherentKZero_surjective (k : ℤ) :
    Function.Surjective (layerToGradedCoherentKZero C f k) := by
  have hle : coherentKZeroFiltration C f k ≤
      ((layerToGradedCoherentKZero C f k).range.comap
        (toGradedCoherentKZero C f k)).map (coherentKZeroFiltration C f k).subtype := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨F, rfl⟩
    exact ⟨⟨_, mk_mem_coherentKZeroFiltration C f k F⟩,
      ⟨coherentDimensionKZeroMk C f (k - 1) k F, layerToGradedCoherentKZero_mk C f k F⟩, rfl⟩
  intro z
  obtain ⟨x, rfl⟩ := toGradedCoherentKZero_surjective C f k z
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rw [show x = y from Subtype.ext hyx.symm]
  exact hy

/-! ### The graded piece inside `K₀(Coh(X)/Coh_{≤k-1}(X))` -/

/-- The localization `K'₀(X) ⟶ K₀(Coh(X)/Coh_{≤a}(X))`. -/
abbrev coherentKZeroToQuotient (a : ℤ) : CoherentKZero X →+ coherentQuotientKZero C f a :=
  KZero.map (coherentModulesDimLE C f a).isoModSerre.Q

/-- The localization `K'₀(X) ⟶ K₀(Coh(X)/Coh_{≤a}(X))` kills `F_a K'₀(X)`. -/
theorem coherentKZeroFiltration_le_ker_coherentKZeroToQuotient (a : ℤ) :
    coherentKZeroFiltration C f a ≤ (coherentKZeroToQuotient C f a).ker :=
  coherentKZeroFiltration_le_ker C f _ a fun F => by
    rw [KZero.map_mk]
    exact KZero.mk_eq_zero_of_isZero ((ObjectProperty.SerreClassLocalization.isZero_obj_iff
      (coherentModulesDimLE C f a).isoModSerre.Q (coherentModulesDimLE C f a) F.obj).2 F.property)

/-- The kernel of `K'₀(X) ⟶ K₀(Coh(X)/Coh_{≤a}(X))` is contained in `F_a K'₀(X)`: by Stacks 02MX
(1) it is the image of `K₀(Coh_{≤a}(X))`. -/
theorem ker_coherentKZeroToQuotient_le (a : ℤ) :
    (coherentKZeroToQuotient C f a).ker ≤ coherentKZeroFiltration C f a := by
  intro x hx
  obtain ⟨y, rfl⟩ := (KZero.exact_map_ι_map_localization (coherentModulesDimLE C f a)
    (coherentModulesDimLE C f a).isoModSerre.Q x).1 hx
  have h : (QuotientAddGroup.mk' (coherentKZeroFiltration C f a)).comp
      (KZero.map (coherentModulesDimLE C f a).ι) = 0 :=
    KZero.hom_ext fun F => by
      rw [AddMonoidHom.comp_apply, KZero.map_mk, AddMonoidHom.zero_apply,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact mk_mem_coherentKZeroFiltration C f a F
  exact (QuotientAddGroup.eq_zero_iff _).1 (DFunLike.congr_fun h y)

/-- The homomorphism `gr_k K'₀(X) ⟶ K₀(Coh(X)/Coh_{≤k-1}(X))` induced by the localization. -/
def gradedToCoherentQuotientKZero (k : ℤ) :
    gradedCoherentKZero C f k →+ coherentQuotientKZero C f (k - 1) :=
  gradedCoherentKZeroLift C f k
    ((coherentKZeroToQuotient C f (k - 1)).comp (coherentKZeroFiltration C f k).subtype)
    fun _ hx => coherentKZeroFiltration_le_ker_coherentKZeroToQuotient C f (k - 1) hx

/-- The homomorphism `gr_k K'₀(X) ⟶ K₀(Coh(X)/Coh_{≤k-1}(X))` sends the class of `x ∈ F_k K'₀(X)`
to the image of `x` under the localization `K'₀(X) ⟶ K₀(Coh(X)/Coh_{≤k-1}(X))`. -/
@[simp]
theorem gradedToCoherentQuotientKZero_toGradedCoherentKZero (k : ℤ)
    (x : coherentKZeroFiltration C f k) :
    gradedToCoherentQuotientKZero C f k (toGradedCoherentKZero C f k x) =
      coherentKZeroToQuotient C f (k - 1) x :=
  rfl

/-- **Stacks 0FEV**, `gr_k K'₀(X) ⊆ K₀(Coh(X)/Coh_{≤k-1}(X))`: the homomorphism induced by the
localization is injective, by Stacks 02MX (1). -/
theorem gradedToCoherentQuotientKZero_injective (k : ℤ) :
    Function.Injective (gradedToCoherentQuotientKZero C f k) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨x, rfl⟩ := toGradedCoherentKZero_surjective C f k z
  rw [gradedToCoherentQuotientKZero_toGradedCoherentKZero] at hz
  exact (toGradedCoherentKZero_eq_zero_iff C f k x).2
    (ker_coherentKZeroToQuotient_le C f (k - 1) hz)

/-- Following the map out of the dimension layer by the inclusion of the graded piece is the
canonical map `K₀(Coh_{≤k}/Coh_{≤k-1}) ⟶ K₀(Coh/Coh_{≤k-1})` of Stacks 02SD. -/
theorem gradedToCoherentQuotientKZero_comp_layerToGradedCoherentKZero (k : ℤ) :
    (gradedToCoherentQuotientKZero C f k).comp (layerToGradedCoherentKZero C f k) =
      coherentDimensionToQuotientHom C f (k - 1) k := by
  refine (AddMonoidHom.cancel_right (dimLEToLayer_surjective C f k)).1
    (KZero.hom_ext fun F => ?_)
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    layerToGradedCoherentKZero_dimLEToLayer, dimLEToGradedCoherentKZero_mk,
    gradedToCoherentQuotientKZero_toGradedCoherentKZero, KZero.map_mk,
    dimLEToLayer_mk, coherentDimensionToQuotientHom_apply_mk]
  rfl

omit [IsLocallyNoetherian X] in
/-- Widening the layer and then dropping the upper bound is dropping the upper bound. -/
theorem coherentDimensionToQuotientHom_comp_coherentDimensionLayerHom (k : ℤ) :
    (coherentDimensionToQuotientHom C f (k - 1) (k + 1)).comp (coherentDimensionLayerHom C f k) =
      coherentDimensionToQuotientHom C f (k - 1) k := by
  refine (AddMonoidHom.cancel_right (dimLEToLayer_surjective C f k)).1
    (KZero.hom_ext fun F => ?_)
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    dimLEToLayer_mk, coherentDimensionLayerHom_apply_mk,
    coherentDimensionToQuotientHom_apply_mk, coherentDimensionToQuotientHom_apply_mk]
  rfl

/-! ### From cycles and from the Chow group -/

/-- The homomorphism `Z_k(X) ⟶ gr_k K'₀(X)`: the map `Z_k(X) ⟶ K₀(Coh_{≤k}/Coh_{≤k-1})` of
Stacks 02S9, `∑ n_Z[Z] ↦ [⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]`, followed by
`Stacks.Chow.layerToGradedCoherentKZero`. -/
def cycleToGradedCoherentKZero (k : ℤ) : CycleGroup C f k →+ gradedCoherentKZero C f k :=
  (layerToGradedCoherentKZero C f k).comp
    ((KZero.ofGrothendieckGroup).comp (cycleDimensionLayerHom C f k))

/-- Followed by the inclusion of the graded piece, the homomorphism out of cycles is the map of
Tag 0FDS read in `K₀(Coh(X)/Coh_{≤k-1}(X))`. -/
theorem gradedToCoherentQuotientKZero_cycleToGradedCoherentKZero (k : ℤ) (c : CycleGroup C f k) :
    gradedToCoherentQuotientKZero C f k (cycleToGradedCoherentKZero C f k c) =
      coherentDimensionToQuotientHom C f (k - 1) (k + 1) (cycleDimensionLayerWideHom C f k c) := by
  rw [cycleToGradedCoherentKZero, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_assoc,
    gradedToCoherentQuotientKZero_comp_layerToGradedCoherentKZero,
    ← coherentDimensionToQuotientHom_comp_coherentDimensionLayerHom, cycleDimensionLayerWideHom]
  rfl

/-- On a quasi-compact `X` the homomorphism `Z_k(X) ⟶ gr_k K'₀(X)` kills every cycle rationally
equivalent to zero: after the injection into `K₀(Coh(X)/Coh_{≤k-1}(X))` it factors through the
map of Tag 0FDS. -/
theorem cycleToGradedCoherentKZero_eq_zero_of_mem_rationalEquivalences [CompactSpace X] (k : ℤ)
    (c : CycleGroup C f k) (hc : c ∈ rationalEquivalences C f k) :
    cycleToGradedCoherentKZero C f k c = 0 := by
  refine gradedToCoherentQuotientKZero_injective C f k ?_
  rw [gradedToCoherentQuotientKZero_cycleToGradedCoherentKZero,
    cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences_of_compactSpace C f k c hc,
    map_zero, map_zero]

/-- **The canonical map `CH_k(X) ⟶ gr_k K'₀(X)` of Section 0FEV**, for `X` quasi-compact: the class
of the integral closed subscheme `Z ⊆ X` of delta-dimension `k` goes to the class of `𝒪_Z`
(`Stacks.Chow.chowToGradedCoherentKZero_mk_integralComponent`). It is the descent of
`Stacks.Chow.cycleToGradedCoherentKZero` to the Chow group. -/
def chowToGradedCoherentKZero [CompactSpace X] (k : ℤ) :
    chowGroup C f k →+ gradedCoherentKZero C f k :=
  QuotientAddGroup.lift _ (cycleToGradedCoherentKZero C f k)
    (cycleToGradedCoherentKZero_eq_zero_of_mem_rationalEquivalences C f k)

/-- The canonical map `CH_k(X) ⟶ gr_k K'₀(X)` sends the class of a cycle `c` to the image of `c`
under `Stacks.Chow.cycleToGradedCoherentKZero`. -/
@[simp]
theorem chowToGradedCoherentKZero_mk [CompactSpace X] (k : ℤ) (c : CycleGroup C f k) :
    chowToGradedCoherentKZero C f k (QuotientAddGroup.mk' (rationalEquivalences C f k) c) =
      cycleToGradedCoherentKZero C f k c :=
  rfl

/-! ### The cycle group of a quasi-compact scheme is generated by prime cycles -/

omit [IsLocallyNoetherian X] in
/-- On a quasi-compact `X`, two homomorphisms out of `Z_k(X)` agree as soon as they agree on the
cycle `[Z]` of every integral closed subscheme `Z` of delta-dimension `k`: a `k`-cycle has finite
support, so it is the finite sum `∑ n_Z [Z]`. -/
theorem cycleGroup_hom_ext [CompactSpace X] (k : ℤ) {A : Type*} [AddCommGroup A]
    {φ ψ : CycleGroup C f k →+ A}
    (h : ∀ (x : X) (_ : relativeDimension C.dimensionFunction f x = k),
      φ (cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι k) =
        ψ (cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι k)) :
    φ = ψ := by
  refine AddMonoidHom.ext fun α => ?_
  have hfin : (Function.support fun x : X => α.1 x • integralComponentLayerClass C f k x).Finite :=
    (finite_support_cycleGroup C f k α).subset fun x hx => by
      by_contra hx'
      rw [Function.notMem_support] at hx'
      exact hx (by simp only; rw [hx', zero_smul])
  have key : ∀ x : X, φ (dimensionLayerCycleHom C f k (integralComponentLayerClass C f k x)) =
      ψ (dimensionLayerCycleHom C f k (integralComponentLayerClass C f k x)) := by
    intro x
    by_cases hx : relativeDimension C.dimensionFunction f x = k
    · rw [dimensionLayerCycleHom_integralComponentLayerClass C f k x hx]
      exact h x hx
    · rw [integralComponentLayerClass_eq_zero C f k hx, map_zero, map_zero, map_zero]
  rw [← dimensionLayerCycleHom_finsum_integralComponentLayerClass C f k α
      (finite_support_cycleGroup C f k α), ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
    AddMonoidHom.map_finsum _ hfin, AddMonoidHom.map_finsum _ hfin]
  exact finsum_congr fun x => by
    rw [map_zsmul, map_zsmul, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, key x]

/-! ### Values, on a Noetherian scheme -/

/-- **Stacks 02S9 in `gr_k K'₀(X)`**, for `X` Noetherian: the class in the graded piece of a
coherent module of support dimension at most `k` is the image of its cycle `[F]_k`. -/
theorem cycleToGradedCoherentKZero_dimensionLayerCycle [IsNoetherian X] (k : ℤ)
    (F : CoherentModulesDimLE C f k) :
    cycleToGradedCoherentKZero C f k (dimensionLayerCycle C f k F) =
      toGradedCoherentKZero C f k ⟨KZero.mk _ F.obj, mk_mem_coherentKZeroFiltration C f k F⟩ := by
  rw [cycleToGradedCoherentKZero, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    cycleDimensionLayerHom_dimensionLayerCycle, KZero.ofGrothendieckGroup_of]
  exact layerToGradedCoherentKZero_mk C f k F

/-- For `X` Noetherian, the image in `gr_k K'₀(X)` of the cycle `[Z]` of the integral closed
subscheme `Z` attached to a point of relative dimension `k` is the class of `𝒪_Z`. -/
theorem cycleToGradedCoherentKZero_integralComponent [IsNoetherian X] (k : ℤ) (x : X)
    (hx : relativeDimension C.dimensionFunction f x = k) :
    cycleToGradedCoherentKZero C f k
        (cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι k) =
      toGradedCoherentKZero C f k ⟨KZero.mk _ (integralComponentDimLE C f k x hx).obj,
        mk_mem_coherentKZeroFiltration C f k _⟩ := by
  rw [← dimensionLayerCycle_integralComponentDimLE C f k x hx,
    cycleToGradedCoherentKZero_dimensionLayerCycle]

/-- **The canonical map `CH_k(X) ⟶ gr_k K'₀(X)` on generators**, for `X` Noetherian: the class of
the integral closed subscheme `Z` attached to a point of relative dimension `k` is sent to the
class of `𝒪_Z`. -/
theorem chowToGradedCoherentKZero_mk_integralComponent [IsNoetherian X] (k : ℤ) (x : X)
    (hx : relativeDimension C.dimensionFunction f x = k) :
    chowToGradedCoherentKZero C f k (QuotientAddGroup.mk' (rationalEquivalences C f k)
        (cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι k)) =
      toGradedCoherentKZero C f k ⟨KZero.mk _ (integralComponentDimLE C f k x hx).obj,
        mk_mem_coherentKZeroFiltration C f k _⟩ :=
  cycleToGradedCoherentKZero_integralComponent C f k x hx

/-- On a Noetherian `X` the homomorphism `Z_k(X) ⟶ gr_k K'₀(X)` is surjective: the map of
Stacks 02S9 is, and so is the homomorphism out of the dimension layer. -/
theorem cycleToGradedCoherentKZero_surjective [IsNoetherian X] (k : ℤ) :
    Function.Surjective (cycleToGradedCoherentKZero C f k) := by
  intro z
  obtain ⟨y, rfl⟩ := layerToGradedCoherentKZero_surjective C f k z
  obtain ⟨c, hc⟩ := surjective_cycleDimensionLayerHom C f k (KZero.toGrothendieckGroup y)
  refine ⟨c, ?_⟩
  rw [cycleToGradedCoherentKZero, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hc,
    KZero.ofGrothendieckGroup_toGrothendieckGroup]

/-- On a Noetherian `X` the canonical map `CH_k(X) ⟶ gr_k K'₀(X)` is surjective. -/
theorem chowToGradedCoherentKZero_surjective [IsNoetherian X] (k : ℤ) :
    Function.Surjective (chowToGradedCoherentKZero C f k) := by
  intro z
  obtain ⟨c, rfl⟩ := cycleToGradedCoherentKZero_surjective C f k z
  exact ⟨_, chowToGradedCoherentKZero_mk C f k c⟩

end Stacks.Chow

end
