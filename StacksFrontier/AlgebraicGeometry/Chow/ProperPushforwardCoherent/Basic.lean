module

public import Mathlib.Data.ENat.BigOperators
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.StalkProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper pushforward of the cycle of a coherent sheaf

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
locally of finite type over `S` and let `f : X ⟶ Y` be proper over `S`. For a coherent
`𝒪_X`-module `F` whose support has delta-dimension at most `k`, proper pushforward of `k`-cycles
carries `[F]_k` to the cycle of the direct image: `f_* [F]_k = [f_* F]_k`. For a closed
subscheme `i : Z ⟶ X` with `dim_δ(Z) ≤ k` the same statement reads `f_* [Z]_k = [f_* 𝒪_Z]_k`.

## Main results

* `Stacks.Chow.schemeDeltaDimension_reducedSupport_pushforward_le`: the support of the direct
  image has delta-dimension at most that of the support of `F`.
* `Stacks.Chow.sheafMultiplicity_pushforward_eq_finsum`: the multiplicity of `f_* F` at a point
  of delta-dimension `k` is the weighted sum of the multiplicities of `F` along the fibre.
* `Stacks.Chow.properPushforward_cycleAssociatedToCoherentSheaf`: `f_* [F]_k = [f_* F]_k`, for
  `f_* F` coherent.
* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme`: `f_* [Z]_k = [f_* 𝒪_Z]_k`,
  for `f_* 𝒪_Z` coherent.

## References

* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}}

/-! ### The fibre of the support over a point of maximal delta-dimension -/

/-- Relative dimension does not increase when passing to the image under a morphism. -/
private theorem relativeDimension_image_le {C : ChowSituation.{u}} {sX : X ⟶ C.S}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) (x : X) :
    relativeDimension C.dimensionFunction sY (f x) ≤
      relativeDimension C.dimensionFunction sX x := by
  have := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f x
  rw [hf] at this
  omega

/-- A point of the support of `F` lying over a point of `Y` of delta-dimension `k` has
delta-dimension `k` as well, when the support of `F` has delta-dimension at most `k`. -/
theorem relativeDimension_eq_of_mem_supp_of_mem_fibre (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (F : X.Modules) [F.IsCoherent] {k : ℤ}
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sX) ≤ (k : EInt)) {y : Y}
    (hy : relativeDimension C.dimensionFunction sY y = k) {x : X} (hxy : f x = y)
    (hx : x ∈ SheafOfModules.supp F) :
    relativeDimension C.dimensionFunction sX x = k := by
  have hle := relativeDimension_le_of_mem_supp C sX F hFk hx
  have := relativeDimension_image_le sY hf x
  rw [hxy, hy] at this
  omega

/-- The fibre over `y` of the support of `F` is finite when `f` is proper, `y` has
delta-dimension `k` and the support of `F` has delta-dimension at most `k`. -/
theorem finite_supportFibre (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX)
    (F : X.Modules) [F.IsCoherent] {k : ℤ}
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sX) ≤ (k : EInt)) (y : Y)
    (hy : relativeDimension C.dimensionFunction sY y = k) :
    {x : X | f x = y ∧ x ∈ SheafOfModules.supp F}.Finite := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let componentSet : irreducibleComponents (SheafOfModules.supp F : Set X) → Set X :=
    fun Z => (Subtype.val '' Z.1 : Set X)
  have hrelevant : {Z | (componentSet Z ∩ f.base ⁻¹' {y}).Nonempty}.Finite :=
    LocallyFinite.finite_nonempty_inter_compact (locallyFinite_irreducibleComponents_supp F)
      (f.isProperMap.isCompact_preimage isCompact_singleton)
  have : Finite {Z | (componentSet Z ∩ f.base ⁻¹' {y}).Nonempty} := hrelevant.to_subtype
  have hchoose (x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F}) :
      ∃ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
        IsGenericPoint x.1 (componentSet Z) :=
    isGenericPoint_component_supp_of_relativeDimension_eq C sX F k x.1 hFk x.2.2
      (relativeDimension_eq_of_mem_supp_of_mem_fibre C sX sY f hf F hFk hy x.2.1 x.2.2)
  have hinj : Function.Injective
      (fun x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F} =>
        (⟨Classical.choose (hchoose x),
          ⟨x.1, (Classical.choose_spec (hchoose x)).mem, x.2.1⟩⟩ :
            {Z | (componentSet Z ∩ f.base ⁻¹' {y}).Nonempty})) := by
    intro x x' hxx'
    refine Subtype.ext ((Classical.choose_spec (hchoose x)).eq ?_)
    simpa [show Classical.choose (hchoose x) = Classical.choose (hchoose x') from
      congrArg Subtype.val hxx'] using Classical.choose_spec (hchoose x')
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

/-! ### The multiplicity of the direct image -/

/-- The support of a proper direct image has delta-dimension at most that of the support of
`F`. -/
theorem schemeDeltaDimension_reducedSupport_pushforward_le (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (F : X.Modules) [F.IsCoherent]
    [((Scheme.Modules.pushforward f).obj F).IsCoherent] {k : ℤ}
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sX) ≤ (k : EInt)) :
    schemeDeltaDimension C
        ((reducedSupport ((Scheme.Modules.pushforward f).obj F)).subschemeι ≫ sY)
      ≤ (k : EInt) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  refine schemeDeltaDimension_reducedSupport_le C sY _ fun y hy => ?_
  obtain ⟨x, hx, hfx⟩ :=
    supp_pushforward_subset_image f F (SheafOfModules.isClosed_supp F) hy
  rw [← hfx]
  exact (relativeDimension_image_le sY hf x).trans
    (relativeDimension_le_of_mem_supp C sX F hFk hx)

/-- The multiplicity of a proper direct image at a point of delta-dimension `k` is the sum over
the fibre of the support of the multiplicities of `F`, each weighted by the degree of the
residue-field extension of `f` at the point. -/
theorem sheafMultiplicity_pushforward_eq_finsum (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (F : X.Modules) [F.IsCoherent]
    [((Scheme.Modules.pushforward f).obj F).IsCoherent] {k : ℤ}
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sX) ≤ (k : EInt)) (y : Y)
    (hy : relativeDimension C.dimensionFunction sY y = k) :
    sheafMultiplicity ((Scheme.Modules.pushforward f).obj F) y =
      ∑ᶠ x ∈ {x : X | f x = y ∧ x ∈ SheafOfModules.supp F},
        sheafMultiplicity F x * (f.residueDegree x : ℤ) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  have hgen (x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F}) :
      ∃ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
        IsGenericPoint x.1 (Subtype.val '' Z.1 : Set X) :=
    isGenericPoint_component_supp_of_relativeDimension_eq C sX F k x.1 hFk x.2.2
      (relativeDimension_eq_of_mem_supp_of_mem_fibre C sX sY f hf F hFk hy x.2.1 x.2.2)
  have : Fintype ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F} :=
    (finite_supportFibre C sX sY f hf F hFk y hy).fintype
  let : ∀ x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F},
      Module (Y.presheaf.stalk y) (F.presheaf.stalk x.1) :=
    supportFibreStalkModule f F y
  have hlen : Module.length (Y.presheaf.stalk y)
        (((Scheme.Modules.pushforward f).obj F).presheaf.stalk y) =
      ∑ x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F},
        Module.length (Y.presheaf.stalk y) (F.presheaf.stalk x.1) := by
    rw [(pushforwardStalkLinearEquivPi f F (SheafOfModules.isClosed_supp F) y
      (locallyFinite_irreducibleComponents_supp F) hgen).length_eq,
      Module.length_pi_of_fintype]
  have hfinite : Module.length (Y.presheaf.stalk y)
      (((Scheme.Modules.pushforward f).obj F).presheaf.stalk y) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_stalk_of_relativeDimension_eq C sY _
        (schemeDeltaDimension_reducedSupport_pushforward_le C sX sY f hf F hFk) hy)
  have hterm (x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F}) :
      Module.length (Y.presheaf.stalk y) (F.presheaf.stalk x.1) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfinite ?_
    rw [hlen]
    exact Finset.single_le_sum
      (f := fun x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F} =>
        Module.length (Y.presheaf.stalk y) (F.presheaf.stalk x.1))
      (fun _ _ => zero_le) (Finset.mem_univ x)
  have hsum : sheafMultiplicity ((Scheme.Modules.pushforward f).obj F) y =
      ∑ x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F},
        sheafMultiplicity F x.1 * (f.residueDegree x.1 : ℤ) := by
    have hn := congrArg ENat.toNat hlen
    rw [ENat.toNat_sum (fun x _ => hterm x)] at hn
    change ((Module.length (Y.presheaf.stalk y)
      (((Scheme.Modules.pushforward f).obj F).presheaf.stalk y)).toNat : ℤ) = _
    rw [hn, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have he : (Module.length (Y.presheaf.stalk y) (F.presheaf.stalk x.1)).toNat =
        (Module.length (X.presheaf.stalk x.1) (F.presheaf.stalk x.1)).toNat *
          f.residueDegree x.1 := by
      obtain ⟨x, hxy, hxF⟩ := x
      subst hxy
      exact length_stalk_restrictScalars_toNat f F x
    rw [he, Nat.cast_mul]
    rfl
  rw [hsum, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]

/-! ### Stacks 02R6 -/

/-- Let `f : X ⟶ Y` be a proper morphism of schemes locally of finite type over the base `S` of
chapter 42, and let `F` be a coherent `𝒪_X`-module whose support has delta-dimension at most
`k`, with `f_* F` coherent. Then proper pushforward of `k`-cycles carries the cycle of `F` to the
cycle of the direct image: `f_* [F]_k = [f_* F]_k`. -/
@[stacks 02R6 "part (2)"]
theorem properPushforward_cycleAssociatedToCoherentSheaf (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (F : X.Modules) [F.IsCoherent]
    [((Scheme.Modules.pushforward f).obj F).IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sX) ≤ (k : EInt)) :
    properPushforward C sX sY f hf k (cycleAssociatedToCoherentSheaf C sX F k hFk) =
      cycleAssociatedToCoherentSheaf C sY ((Scheme.Modules.pushforward f).obj F) k
        (schemeDeltaDimension_reducedSupport_pushforward_le C sX sY f hf F hFk) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  rw [properPushforward_apply]
  by_cases hδ : relativeDimension C.dimensionFunction sY y = k
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C sY _ k _ hδ,
      sheafMultiplicity_pushforward_eq_finsum C sX sY f hf F hFk y hδ]
    trans ∑ᶠ x ∈ f.base ⁻¹' {y}, sheafMultiplicity F x * (f.residueDegree x : ℤ)
    · refine finsum_mem_congr rfl fun x hx => ?_
      have hxy : f x = y := hx
      by_cases hxF : x ∈ SheafOfModules.supp F
      · have hxδ := relativeDimension_eq_of_mem_supp_of_mem_fibre C sX sY f hf F hFk hδ hxy hxF
        rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C sX F k hFk hxδ]
        simp [hxδ, hxy, hδ]
      · rw [cycleAssociatedToCoherentSheaf_apply,
          sheafMultiplicity_eq_zero_of_notMem_supp F hxF]
        simp [hxF]
    · refine finsum_mem_inter_support_eq'
        (fun x : X => sheafMultiplicity F x * (f.residueDegree x : ℤ)) (f.base ⁻¹' {y})
        {x : X | f x = y ∧ x ∈ SheafOfModules.supp F} fun x hx => ?_
      have hxF : x ∈ SheafOfModules.supp F := by
        by_contra hn
        simp [Function.mem_support,
          sheafMultiplicity_eq_zero_of_notMem_supp F hn] at hx
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hxy => ⟨hxy, hxF⟩, fun h => h.1⟩
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C sY _ k _ hδ]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    by_cases hc : (cycleAssociatedToCoherentSheaf C sX F k hFk).1 x = 0
    · rw [hc, zero_mul]
    · have hxδ : relativeDimension C.dimensionFunction sX x = k := by
        by_contra hn
        exact hc (cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C sX F k hFk hn)
      have hxy : f.base x = y := hx
      have hcond : ¬ relativeDimension C.dimensionFunction sX x =
          relativeDimension C.dimensionFunction sY (f.base x) := by
        rw [hxδ, hxy]
        exact fun h => hδ h.symm
      simp [hcond]

/-- Let `f : X ⟶ Y` be a proper morphism of schemes locally of finite type over the base `S` of
chapter 42, and let `i : Z ⟶ X` be a closed subscheme with `dim_δ(Z) ≤ k`, with `f_* (i_* 𝒪_Z)`
coherent. Then proper pushforward of `k`-cycles carries the cycle of `Z` to the cycle of the
direct image of its structure sheaf: `f_* [Z]_k = [f_* 𝒪_Z]_k`, where `𝒪_Z` is read as the
coherent `𝒪_X`-module `i_* 𝒪_Z`. -/
@[stacks 02R6 "part (1)"]
theorem properPushforward_cycleAssociatedToClosedSubscheme (C : ChowSituation.{u})
    {Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (i : Z ⟶ X)
    [IsClosedImmersion i] (k : ℤ) (hZ : schemeDeltaDimension C (i ≫ sX) ≤ (k : EInt)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    ∀ [((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))).IsCoherent],
    properPushforward C sX sY f hf k (cycleAssociatedToClosedSubscheme C sX i k) =
      cycleAssociatedToCoherentSheaf C sY
        ((Scheme.Modules.pushforward f).obj
          ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))) k
        (schemeDeltaDimension_reducedSupport_pushforward_le C sX sY f hf
          ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
          (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C sX i hZ)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  intro _
  rw [cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C sX i k hZ]
  exact properPushforward_cycleAssociatedToCoherentSheaf C sX sY f hf
    ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) k
    (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C sX i hZ)

end Stacks.Chow

end
