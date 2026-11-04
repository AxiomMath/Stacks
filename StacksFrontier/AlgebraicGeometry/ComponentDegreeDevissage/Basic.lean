module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealFiltration
public import StacksFrontier.AlgebraicGeometry.CoherentDevissageGlue.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.FiniteFamily
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Formula
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Irreducible
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.FiniteRank
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a locally free module as a sum over the components

Let `k` be a field, let `f : X ⟶ Spec k` be proper with `topologicalKrullDim X ≤ 1` and let `ℰ`
be a finite locally free `𝒪_X`-module of constant rank `n`. Then

`deg(ℰ) = ∑ᶠ ξ, m(ξ) · deg(ℰ|_{C(ξ)})`,

the sum running over the generic points of the one-dimensional irreducible components of `X`,
with `C(ξ)` the component carrying its reduced induced structure and `m(ξ)` its multiplicity,
the length of the local ring of `X` at `ξ`. More generally, for every coherent `𝒫` the quantity
`χ(𝒫 ⊗ ℰ) − n·χ(𝒫)` is the sum over the same components of the stalk length of `𝒫` at `ξ` times
`deg(ℰ|_{C(ξ)})`.

## Main definitions

* `Stacks.AlgebraicGeometry.ComponentDegreeDevissage.stalkLengthNat`: the length of the stalk of
  a module at a point, as a natural number.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.ComponentDegreeDevissage`.

* `stalkLengthNat_add_of_shortExact`: the stalk length at a generic point is additive along a
  short exact sequence of coherent modules.
* `eulerCharacteristicTensorSheafSub_unit`: the quantity of [Stacks, Tag 0AYU] at the structure
  sheaf is the degree.
* `eulerCharacteristicTensorSheafSub_pushforward_eq_zero`: a layer of dimension at most zero
  contributes nothing.
* `eulerCharacteristicTensorSheafSub_pushforward_eq_fiberRank_mul`: a one-dimensional integral
  layer contributes the fibre rank at its generic point times the degree on its component.
* `curveDegree_pullback_eq_componentDegree`: the degree on an integral closed subscheme of
  dimension one is the degree on the reduced component it is isomorphic to.
* `eulerCharacteristicTensorSheafSub_eq_sum_stalkLengthNat`: the quantity of [Stacks, Tag 0AYU]
  at any coherent module is the sum over the one-dimensional components of its stalk length
  there times the degree on the component.
* `curveDegree_eq_finsum_componentDegree` and `exists_curveDegree_eq_finsum`: the degree of `ℰ`
  is the multiplicity-weighted sum of its degrees on the reduced one-dimensional components.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ComponentDegreeDevissage

open _root_.AlgebraicGeometry
open Stacks.AlgebraicGeometry.ComponentDegrees

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The length of the stalk of a module at a point, as a natural number. -/
def stalkLengthNat (F : X.Modules) (x : X) : ℕ :=
  (Module.length (X.presheaf.stalk x) (F.presheaf.stalk x)).toNat

/-- At a generic point of a scheme proper over a field the stalk of a coherent module has finite
length. -/
theorem length_stalk_ne_top_of_isCoherent [IsProper f] (ξ : genericPointsOne X)
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) :
    Module.length (X.presheaf.stalk ξ.1) (F.presheaf.stalk ξ.1) ≠ ⊤ := by
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k f
  have := hF
  have : F.IsFiniteType := hF.isFiniteType
  have hdim : ringKrullDim (X.presheaf.stalk ξ.1) = 0 := by
    rw [_root_.AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
    have hcoheight : Order.coheight ξ.1 = 0 :=
      Order.coheight_eq_zero.mpr
        (isMax_of_mem_genericPoints ξ.1 (mem_genericPointsOne_iff.mp ξ.2).1)
    simpa only [WithBot.coe_zero] using congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) hcoheight
  have : Ring.KrullDimLE 0 (X.presheaf.stalk ξ.1) :=
    Ring.krullDimLE_iff.mpr (by rw [hdim]; exact le_rfl)
  have : IsArtinianRing (X.presheaf.stalk ξ.1) :=
    isArtinianRing_iff_krullDimLE_zero.mpr inferInstance
  have : Module.Finite (X.presheaf.stalk ξ.1) (F.presheaf.stalk ξ.1) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F ξ.1
  have hart : IsArtinian (X.presheaf.stalk ξ.1) (F.presheaf.stalk ξ.1) := inferInstance
  have hnoe : IsNoetherian (X.presheaf.stalk ξ.1) (F.presheaf.stalk ξ.1) := inferInstance
  exact Module.length_ne_top

/-- The stalk length is additive along a short exact sequence of coherent modules at a generic
point. -/
theorem stalkLengthNat_add_of_shortExact [IsProper f] (ξ : genericPointsOne X)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : _root_.SheafOfModules.IsCoherent S.X₁) (h₃ : _root_.SheafOfModules.IsCoherent S.X₃) :
    stalkLengthNat S.X₂ ξ.1 = stalkLengthNat S.X₁ ξ.1 + stalkLengthNat S.X₃ ξ.1 := by
  have h := _root_.AlgebraicGeometry.length_stalk_add_of_shortExact hS ξ.1
  unfold stalkLengthNat
  rw [h, ENat.toNat_add (length_stalk_ne_top_of_isCoherent k f ξ S.X₁ h₁)
    (length_stalk_ne_top_of_isCoherent k f ξ S.X₃ h₃)]

/-- The stalk length of a zero coherent module vanishes at a generic point. -/
theorem stalkLengthNat_eq_zero_of_isZero [IsProper f] (ξ : genericPointsOne X)
    {F : X.Modules} (hF : _root_.SheafOfModules.IsCoherent F) (hz : IsZero F) :
    stalkLengthNat F ξ.1 = 0 := by
  have hse : (ShortComplex.mk (𝟙 F) (𝟙 F) (hz.eq_of_src (𝟙 F ≫ 𝟙 F) 0)).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ hz }
  have h := stalkLengthNat_add_of_shortExact k f ξ hse hF hF
  change stalkLengthNat F ξ.1 = stalkLengthNat F ξ.1 + stalkLengthNat F ξ.1 at h
  omega

/-- The quantity of [Stacks, Tag 0AYU] at the structure sheaf is the degree. -/
theorem eulerCharacteristicTensorSheafSub_unit [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (E : X.Modules)
    (hE : _root_.SheafOfModules.IsCoherent E) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (hOX : _root_.SheafOfModules.IsCoherent (_root_.SheafOfModules.unit X.ringCatSheaf)) :
    eulerCharacteristicTensorSheafSub k f E hE rank
        (_root_.SheafOfModules.unit X.ringCatSheaf) hOX =
      curveDegree k f hX E rank := by
  simp only [eulerCharacteristicTensorSheafSub]
  rw [eulerCharacteristic_unit_tensorSheaf k f E hE hOX,
    @curveDegree_eq_eulerCharacteristic_sub k _ X f _ hX E rank _ hE hOX]

/-! ### The two kinds of layer -/

/-- The degree does not depend on which of two equal structure morphisms is used. -/
theorem curveDegree_congr_structureMap {W : Scheme.{u}} {p q : W ⟶ Spec (.of k)} (hpq : p = q)
    [IsProper p] [IsProper q] (hW : topologicalKrullDim W ≤ 1) (G : W.Modules) (r : ℕ)
    (hG : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G r) :
    @curveDegree k _ W p _ hW G r hG = @curveDegree k _ W q _ hW G r hG := by
  subst hpq
  rfl

/-- Outside the image of a closed immersion the stalk length of a direct image is zero. -/
theorem stalkLengthNat_pushforward_eq_zero_of_notMemRange {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (M : Z.Modules) (x : X)
    (hx : x ∉ Set.range (ConcreteCategory.hom i.base)) :
    stalkLengthNat ((Scheme.Modules.pushforward i).obj M) x = 0 := by
  have hsub : Subsingleton
      (((Scheme.Modules.pushforward i).obj M).presheaf.stalk x) :=
    _root_.AlgebraicGeometry.subsingleton_stalk_pushforward_of_notMemRange' i M x hx
  unfold stalkLengthNat
  rw [Module.length_eq_zero_iff.mpr hsub]
  rfl

/-- **A layer of dimension at most zero contributes nothing.** The quantity of
[Stacks, Tag 0AYU] vanishes at the direct image of a coherent module from a closed subscheme of
dimension at most zero. -/
theorem eulerCharacteristicTensorSheafSub_pushforward_eq_zero [IsProper f]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : topologicalKrullDim Z ≤ 0)
    (E : X.Modules) (hE : _root_.SheafOfModules.IsCoherent E) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (M : Z.Modules)
    (hpush : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj M)) :
    eulerCharacteristicTensorSheafSub k f E hE rank
      ((Scheme.Modules.pushforward i).obj M) hpush = 0 := by
  have hdim : topologicalKrullDim (_root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj M)) ≤ 0 := by
    rw [_root_.AlgebraicGeometry.topologicalKrullDim_supp_pushforward_of_isClosedImmersion i M]
    exact Topology.IsInducing.subtypeVal.topologicalKrullDim_le.trans hZ
  have := hpush
  obtain ⟨h, hχ⟩ := _root_.AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_rank_mul
    k f ((Scheme.Modules.pushforward i).obj M) hdim E rank
  simp only [eulerCharacteristicTensorSheafSub]
  rw [hχ]
  ring

/-- An integral closed subscheme of dimension one of a scheme proper over a field is a proper
curve over that field. -/
theorem isCurve_comp_of_dim_eq_one [IsProper f] {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (hZ : topologicalKrullDim Z = 1) :
    _root_.AlgebraicGeometry.IsCurve k (i ≫ f) := by
  have : IsProper (i ≫ f) := inferInstance
  refine (_root_.AlgebraicGeometry.isCurve_iff k (i ≫ f)).2 ⟨?_, hZ⟩
  exact { toIsIntegral := inferInstance
          toIsSeparated := inferInstance
          toLocallyOfFiniteType := inferInstance
          toQuasiCompact := inferInstance }

/-- **The degree on an integral closed subscheme of dimension one is the degree on the reduced
component it is isomorphic to.** -/
theorem curveDegree_pullback_eq_componentDegree [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (hZ : topologicalKrullDim Z = 1)
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    @curveDegree k _ Z (i ≫ f) inferInstance (le_of_eq hZ)
        ((Scheme.Modules.pullback i).obj E) rank
        (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank) =
      componentDegree k f hX E rank
        ⟨i (genericPoint (Z : Type u)), genericPoint_mem_genericPointsOne i hX hZ⟩ := by
  set ξ : genericPointsOne X :=
    ⟨i (genericPoint (Z : Type u)), genericPoint_mem_genericPointsOne i hX hZ⟩ with hξdef
  obtain ⟨ψ, hψ, hfac⟩ := exists_isIso_hom_to_reducedComponent i ξ rfl
  have := hψ
  have : IsProper (reducedComponentι X ξ ≫ f) := isProper_reducedComponentι_comp k f ξ
  have hcomp : ψ ≫ (reducedComponentι X ξ ≫ f) = i ≫ f := by
    rw [← Category.assoc, hfac]
  have : IsProper (ψ ≫ (reducedComponentι X ξ ≫ f)) := by rw [hcomp]; infer_instance
  have : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank :=
    isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ E rank
  have : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback ψ).obj
        ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E)) rank :=
    _root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback ψ _ rank
  have : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i).obj E) rank :=
    _root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank
  have hstep := _root_.AlgebraicGeometry.curveDegree_pullback k ψ
    (reducedComponentι X ξ ≫ f) (le_of_eq hZ)
    (topologicalKrullDim_reducedComponent_le X hX ξ)
    ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank
  have hiso : (Scheme.Modules.pullback ψ).obj
        ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) ≅
      (Scheme.Modules.pullback i).obj E :=
    (Scheme.Modules.pullbackComp ψ (reducedComponentι X ξ)).app E ≪≫
      eqToIso (congrArg (fun j => (Scheme.Modules.pullback j).obj E) hfac)
  have htrans := @_root_.AlgebraicGeometry.curveDegree_eq_of_iso k _ Z (i ≫ f) inferInstance
    (le_of_eq hZ) _ _ rank inferInstance inferInstance hiso
  have hcong := curveDegree_congr_structureMap k hcomp (le_of_eq hZ)
    ((Scheme.Modules.pullback ψ).obj
      ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E)) rank inferInstance
  rw [← htrans, ← hcong, hstep]
  rfl

/-- **A one-dimensional integral layer contributes the fibre rank at its generic point times the
degree on the component it lies on.** -/
theorem eulerCharacteristicTensorSheafSub_pushforward_eq_fiberRank_mul [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (hZ : topologicalKrullDim Z = 1)
    (E : X.Modules) (hE : _root_.SheafOfModules.IsCoherent E) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (M : Z.Modules) (hM : _root_.SheafOfModules.IsCoherent M)
    (hpush : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj M)) :
    eulerCharacteristicTensorSheafSub k f E hE rank
        ((Scheme.Modules.pushforward i).obj M) hpush =
      (Scheme.Modules.fiberRank M (genericPoint (Z : Type u)) : ℤ) *
        componentDegree k f hX E rank
          ⟨i (genericPoint (Z : Type u)), genericPoint_mem_genericPointsOne i hX hZ⟩ := by
  have : _root_.AlgebraicGeometry.IsCurve k (i ≫ f) := isCurve_comp_of_dim_eq_one k f i hZ
  have : IsLocallyNoetherian X :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k f
  have : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i).obj E) rank :=
    _root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank
  have hEZ : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k (i ≫ f)
      ((Scheme.Modules.pullback i).obj E) rank
  have := hM
  have ht :=
    _root_.AlgebraicGeometry.eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion
      k i f M E hM hE hpush hEZ
  have hb := _root_.AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion
    k i f M hM hpush
  have hcomm := @_root_.AlgebraicGeometry.eulerCharacteristic_tensorSheaf_comm k _ Z (i ≫ f) _
    M ((Scheme.Modules.pullback i).obj E) hM hEZ
  have h0AYV :=
    @_root_.AlgebraicGeometry.eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add
      k _ Z (i ≫ f) _ _
      ((Scheme.Modules.pullback i).obj E) rank _ M hM
      (@_root_.AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace
        ((Scheme.Modules.pullback i).obj E) M hEZ hM)
  have hdegeq : @curveDegree k _ Z (i ≫ f) _
        (le_of_eq (_root_.AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := i ≫ f)))
        ((Scheme.Modules.pullback i).obj E) rank inferInstance =
      componentDegree k f hX E rank
        ⟨i (genericPoint (Z : Type u)), genericPoint_mem_genericPointsOne i hX hZ⟩ :=
    curveDegree_pullback_eq_componentDegree k f hX i hZ E rank
  simp only [eulerCharacteristicTensorSheafSub]
  rw [ht, hb, hcomm, h0AYV, hdegeq]
  ring

/-- **If a generic point of a one-dimensional component lies in the image of a closed immersion
with integral source, that source has dimension one.** -/
theorem topologicalKrullDim_eq_one_of_mem_range {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (ξ : genericPointsOne X)
    (hmem : (ξ.1 : X) ∈ Set.range (ConcreteCategory.hom i.base)) :
    topologicalKrullDim (Z : Type u) = 1 := by
  have hg := genericPoint_eq_of_mem_range i ξ.1 (mem_genericPointsOne_iff.mp ξ.2).1 hmem
  have hr : Set.range (ConcreteCategory.hom i.base) = closure ({(ξ.1 : X)} : Set X) := by
    rw [← hg, ← support_ker_eq_closure_genericPoint i, Scheme.Hom.support_ker,
      i.isClosedEmbedding.isClosed_range.closure_eq]
  calc topologicalKrullDim (Z : Type u)
      = topologicalKrullDim (Set.range (ConcreteCategory.hom i.base)) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (i.isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph
    _ = topologicalKrullDim (closure ({(ξ.1 : X)} : Set X)) :=
        IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.setCongr hr).isHomeomorph
    _ = 1 := (mem_genericPointsOne_iff.mp ξ.2).2

/-- The stalk length at the generic point of the direct image of a module of finite type from an
integral closed subscheme is the fibre rank of that module at the generic point. -/
theorem stalkLengthNat_pushforward_genericPoint {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (M : Z.Modules) (hM : M.IsFiniteType) :
    stalkLengthNat ((Scheme.Modules.pushforward i).obj M) (i (genericPoint (Z : Type u))) =
      Scheme.Modules.fiberRank M (genericPoint (Z : Type u)) := by
  have := hM
  unfold stalkLengthNat
  rw [_root_.AlgebraicGeometry.length_stalk_pushforward_of_isClosedImmersion i M
    (genericPoint (Z : Type u))]
  exact _root_.AlgebraicGeometry.length_stalk_eq_fiberRank_of_isField M _
    (isField_stalk_genericPoint Z)

/-- The stalk length of the structure sheaf at the generic point of a one-dimensional component
is the multiplicity of that component. -/
theorem stalkLengthNat_unit (ξ : genericPointsOne X) :
    stalkLengthNat (_root_.SheafOfModules.unit X.ringCatSheaf) ξ.1 =
      componentMultiplicity X ξ := by
  unfold stalkLengthNat componentMultiplicity
  rw [(Stacks.UnitStalk.unitStalkLinearEquiv X ξ.1).length_eq]

/-! ### The dévissage of [Stacks, Tag 01YF] applied to the quantity of [Stacks, Tag 0AYU] -/

/-- **The quantity of [Stacks, Tag 0AYU] at a coherent module is the sum over the
one-dimensional components of its stalk length there times the degree on the component.** -/
theorem eulerCharacteristicTensorSheafSub_eq_sum_stalkLengthNat [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (E : X.Modules)
    (hE : _root_.SheafOfModules.IsCoherent E) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    [Fintype (genericPointsOne X)]
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) :
    eulerCharacteristicTensorSheafSub k f E hE rank F hF =
      ∑ ξ : genericPointsOne X,
        (stalkLengthNat F ξ.1 : ℤ) * componentDegree k f hX E rank ξ := by
  classical
  have : _root_.AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProper_over_field k f
  have h02O6 :=
    _root_.AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper k f
  set P : X.Modules → Prop := fun G => ∀ hG : _root_.SheafOfModules.IsCoherent G,
    eulerCharacteristicTensorSheafSub k f E hE rank G hG =
      ∑ ξ : genericPointsOne X,
        (stalkLengthNat G ξ.1 : ℤ) * componentDegree k f hX E rank ξ with hPdef
  refine (CoherentDevissage.property_of_forall_hasIdealFiltration P
    (fun G hG => @CoherentDevissage.hasIdealFiltration X _ G hG) ?_ ?_ ?_ F hF) hF
  · intro hG
    rw [eulerCharacteristicTensorSheafSub_eq_zero_of_isZero k f E hE rank _ hG
      CoherentDevissage.isZero_terminal h02O6]
    refine (Finset.sum_eq_zero fun ξ _ => ?_).symm
    rw [stalkLengthNat_eq_zero_of_isZero k f ξ hG CoherentDevissage.isZero_terminal]
    simp
  · intro S hS h₁ h₂ h₃ hP₁ hP₃ hG
    have hadd := eulerCharacteristicTensorSheafSub_add_of_shortExact k f E hE rank hS h₁ hG h₃
      h02O6
    rw [hadd, hP₁ h₁, hP₃ h₃, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [stalkLengthNat_add_of_shortExact k f ξ hS h₁ h₃]
    push_cast
    ring
  · intro Z i hi hZi I hI hG
    have : IsProper (i ≫ f) := inferInstance
    have : IsLocallyNoetherian Z :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k
        (i ≫ f)
    have hIcoh : _root_.SheafOfModules.IsCoherent I.toSheafOfModules :=
      CoherentDevissageGlue.isCoherent_of_isQuasicoherent_submodule_unit I
    rcases topologicalKrullDim_le_zero_or_eq_one i hX with hd | hd
    · have hout : ∀ ξ : genericPointsOne X,
          (ξ.1 : X) ∉ Set.range (ConcreteCategory.hom i.base) := by
        intro ξ hmem
        rw [topologicalKrullDim_eq_one_of_mem_range i ξ hmem] at hd
        exact absurd hd (by norm_num)
      rw [eulerCharacteristicTensorSheafSub_pushforward_eq_zero k f i hd E hE rank _ hG]
      refine (Finset.sum_eq_zero fun ξ _ => ?_).symm
      rw [stalkLengthNat_pushforward_eq_zero_of_notMemRange i I.toSheafOfModules ξ.1 (hout ξ)]
      simp
    · rw [eulerCharacteristicTensorSheafSub_pushforward_eq_fiberRank_mul k f hX i hd E hE rank
        I.toSheafOfModules hIcoh hG]
      refine Eq.trans ?_ (Finset.sum_eq_single_of_mem
        (⟨i (genericPoint (Z : Type u)), genericPoint_mem_genericPointsOne i hX hd⟩ :
          genericPointsOne X) (Finset.mem_univ _) ?_).symm
      · rw [stalkLengthNat_pushforward_genericPoint i I.toSheafOfModules hIcoh.isFiniteType]
      · intro η _ hη
        have hout : (η.1 : X) ∉ Set.range (ConcreteCategory.hom i.base) := by
          intro hmem
          exact hη (Subtype.ext
            (genericPoint_eq_of_mem_range i η.1 (mem_genericPointsOne_iff.mp η.2).1 hmem).symm)
        rw [stalkLengthNat_pushforward_eq_zero_of_notMemRange i I.toSheafOfModules η.1 hout]
        simp

/-! ### [Stacks, Tag 0AYW] -/

/-- The degree of a finite locally free module of constant rank on a scheme proper over a field
and of dimension at most one is the multiplicity-weighted sum of its degrees on the reduced
one-dimensional components:

`deg(ℰ) = ∑ᶠ ξ, m(ξ) · deg(ℰ|_{C(ξ)})`. -/
@[stacks 0AYW]
theorem curveDegree_eq_finsum_componentDegree [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X,
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ := by
  classical
  have hfin : Finite (genericPointsOne X) :=
    (finite_genericPointsOne_of_isProper k f).to_subtype
  let : Fintype (genericPointsOne X) := Fintype.ofFinite _
  have hE := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
    k f E rank
  have hOX := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  rw [finsum_eq_sum_of_fintype,
    ← eulerCharacteristicTensorSheafSub_unit k f hX E hE rank hOX,
    eulerCharacteristicTensorSheafSub_eq_sum_stalkLengthNat k f hX E hE rank _ hOX]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [stalkLengthNat_unit ξ]

/-- The component formula for the degree in existential form: each reduced one-dimensional
component is proper over the base, has dimension at most one and carries a restriction of `ℰ`
that is again finite locally free of the same rank, and the component formula holds with respect
to those three proofs. -/
@[stacks 0AYW]
theorem exists_curveDegree_eq_finsum [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    ∃ (hproper : ∀ ξ : genericPointsOne X, IsProper (reducedComponentι X ξ ≫ f))
      (hdimC : ∀ ξ : genericPointsOne X, topologicalKrullDim (reducedComponent X ξ) ≤ 1)
      (hrank : ∀ ξ : genericPointsOne X,
        _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank),
      curveDegree k f hX E rank =
        ∑ᶠ ξ : genericPointsOne X,
          (componentMultiplicity X ξ : ℤ) *
            @curveDegree k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
              (hproper ξ) (hdimC ξ)
              ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank (hrank ξ) :=
  (exists_curveDegree_eq_finsum_iff k f hX E rank).2
    (curveDegree_eq_finsum_componentDegree k f hX E rank)

end Stacks.AlgebraicGeometry.ComponentDegreeDevissage

end
