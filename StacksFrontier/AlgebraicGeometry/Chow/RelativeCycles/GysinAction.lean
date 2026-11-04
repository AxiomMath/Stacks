module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionLocal
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionPushPull
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictionAction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassFacet
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.EnvelopeCycleLift
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Compatibilities
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeRelative
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.SectionGysin
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassProperCover

/-!
# The action of a relative cycle commutes with the Gysin maps on cycles

Let `(S, δ)` be as in Section 0H65, let `p : X ⟶ Y` be a morphism of schemes locally of finite
type over `S`, let `α ∈ z(X/Y, r)`, and let `(L, s, i : D ⟶ Y)` be as in Chow Homology,
Definition 02T8, with `L|_D ≅ 𝒪_D`. Stacks, Lemma 0H6E, asserts `i^*α ∩ i^*β = j^*(α ∩ β)`
for `β ∈ Z_{e+1}(Y)`, where `j : E = X ×_Y D ⟶ X`.

## Main results

* `Stacks.Chow.isRelativeCycle_restrictedFamily` — Tag 0H51 for restriction to open subschemes of
  the source and of the base.
* `Stacks.Chow.cap_gysin_familyAssociatedToClosedSubscheme` — the identity, pushed forward to
  `X`, for `α = [Z/X/Y]_r` with `Z` flat over `Y` and `β = [W]` integral (Stacks 0H6A twice).
* `Stacks.Chow.capCommutesWithGysin_of_envelope` — the reduction along an envelope (Stacks 0H6B
  and 0H6D, each twice).
* `Stacks.Chow.capCommutesWithGysin_of_isRelativeCycle` — the identity read in `X`, by
  localization and Tag 0H59.
* `Stacks.Chow.cap_baseChangeFamily_gysinCycleMap` — **Stacks 0H6E**.

## Implementation notes

The identity is first proved after pushing both sides forward to `X`, in the form
`α ∩ i_* i^* β = j_* j^*(α ∩ β)` (`Stacks.Chow.CapCommutesWithGysin`), where it is an equality of
cycles on `X`. That form is stable under the two reductions of the source's proof — along an
envelope `Y' ⟶ Y` and to affine opens — without comparing the base change of `i^*α` with a
base change of `α'`, and it gives back the statement on `E` because pushforward along the closed
immersion `j` is injective and Stacks 0H6B identifies `j_*(i^*α ∩ i^*β)` with `α ∩ i_* i^*β`.

The cartesian square of Remark 0B6Y is taken literally, with `E = X ×_Y D` and `j` the first
projection, and `j^*` is the Gysin map of Remark 0B6Z read along the presentation `j` of the zero
scheme of `p^* s` (`Stacks.Chow.gysinCycleMapAlong`), which by
`Stacks.Chow.properPushforward_gysinCycleMapAlong` is the canonical Gysin map transported along
the identification of `E` with that zero scheme. Both sides of the identity are then cycles on
the same scheme `E`, and no transport appears in the statement.

## References

* [Stacks Project, Tag 0H6E](https://stacks.math.columbia.edu/tag/0H6E)
* [Stacks Project, Tag 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Tag 0H6A](https://stacks.math.columbia.edu/tag/0H6A)
* [Stacks Project, Tag 0H6B](https://stacks.math.columbia.edu/tag/0H6B)
* [Stacks Project, Tag 0H6D](https://stacks.math.columbia.edu/tag/0H6D)
* [Stacks Project, Tag 0H67](https://stacks.math.columbia.edu/tag/0H67)
* [Stacks Project, Tag 0H51](https://stacks.math.columbia.edu/tag/0H51)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Bookkeeping -/

/-- Reindexing the cycle of a closed subscheme along an equality of degrees. -/
theorem cycleGroupCongr_cycleAssociatedToClosedSubscheme (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i]
    {j k : ℤ} (h : j = k) :
    cycleGroupCongr C f h (cycleAssociatedToClosedSubscheme C f i j) =
      cycleAssociatedToClosedSubscheme C f i k := by
  subst h
  rfl

/-- Reindexing along an equality of degrees commutes with proper pushforward. -/
theorem properPushforward_cycleGroupCongr (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) {j k : ℤ} (h : j = k) (c : CycleGroup C sX j) :
    properPushforward C sX sY f hf k (cycleGroupCongr C sX h c) =
      cycleGroupCongr C sY h (properPushforward C sX sY f hf j c) := by
  subst h
  rfl

/-- **The two presentations of `Z ×_Y (W ∩ D)`.** For `g : Z ⟶ Y` and closed subschemes
`D, W ⊆ Y`, the inverse image along `g` of `W ∩ D` (presented as the closed subscheme `W ∩ D` of
`D`) and the intersection of the inverse images `g⁻¹ W ∩ g⁻¹ D` (presented inside `g⁻¹ D`) have the
same fundamental cycles on `Z`: the second is a fibre product for the cospan of the first, by
pasting the cartesian squares of the two inverse images. -/
theorem cycleAssociatedToClosedSubscheme_pullbackFst_comap (C : ChowSituation.{u})
    {Z Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (g : Z ⟶ Y)
    (D W : Y.IdealSheafData) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C sZ
        (pullback.fst g ((W.comap D.subschemeι).subschemeι ≫ D.subschemeι)) k =
      cycleAssociatedToClosedSubscheme C sZ
        (((W.comap g).comap (D.comap g).subschemeι).subschemeι ≫ (D.comap g).subschemeι) k := by
  set qd := Scheme.IdealSheafData.subschemeMap (D.comap g) D g (D.le_map_comap g) with hqd_def
  have hqd : qd ≫ D.subschemeι = (D.comap g).subschemeι ≫ g :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  set A := (W.comap g).comap (D.comap g).subschemeι with hA_def
  have hA : (W.comap D.subschemeι).comap qd = A := by
    rw [hA_def, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hqd]
  set qa := Scheme.IdealSheafData.subschemeMap A (W.comap D.subschemeι) qd
    (Scheme.IdealSheafData.le_map_iff_comap_le.2 hA.le) with hqa_def
  have hqa : qa ≫ (W.comap D.subschemeι).subschemeι = A.subschemeι ≫ qd :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have sq1 : IsPullback (D.comap g).subschemeι qd g D.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ hqd.symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])
  have sq2 : IsPullback A.subschemeι qa qd (W.comap D.subschemeι).subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ hqa.symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, hA])
  have sq := sq2.paste_horiz sq1
  exact (cycleAssociatedToClosedSubscheme_eq_of_iso C sZ _ _ sq.isoPullback
    sq.isoPullback_hom_fst k).symm

/-- **The fibre product `Z ×_Y W` has delta-dimension at most `r + e`** when the fibres of the
closed subscheme `Z ⊆ X` over `Y` have dimension at most `r` and `W ⊆ Y` has delta-dimension at
most `e`. This is the dimension count of the first paragraph of the proof of Stacks 0H69, for the
structure sheaves of `Z` and `W`. -/
theorem schemeDeltaDimension_pullbackFst_comp_le (C : ChowSituation.{u}) {X Y Z W : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (r : ℕ) (e : ℤ)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : ∀ y : Y, topologicalKrullDim (pullback i (f.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞))
    (j : W ⟶ Y) [IsClosedImmersion j]
    (hWe : schemeDeltaDimension C (j ≫ sY) ≤ (e : EInt)) :
    schemeDeltaDimension C ((pullback.fst (i ≫ f) j ≫ i) ≫ (f ≫ sY)) ≤
      (((r : ℤ) + e : ℤ) : EInt) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let F : X.Modules := (Scheme.Modules.pushforward i).obj (Ample.unitModule Z)
  let G : Y.Modules := (Scheme.Modules.pushforward j).obj (Ample.unitModule W)
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let m : pullback (i ≫ f) j ⟶ X := pullback.fst (i ≫ f) j ≫ i
  have hTdim := schemeDeltaDimension_tensorPullback_le C sY f r e F
    (topologicalKrullDim_supp_pullback_fiberι_le i f hZ) G
    (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C sY j hWe)
  have hsupp : SheafOfModules.supp (tensorPullback f F G) =
      Set.range (ConcreteCategory.hom m.base) := by
    rw [SheafOfModules.supp_eq_of_iso (tensorPullbackStructureSheavesIso i f j)]
    exact supp_pushforwardStructureSheaf m
  exact schemeDeltaDimension_le_of_forall_relativeDimension_le C (f ≫ sY) m fun q =>
    relativeDimension_le_of_mem_supp C (f ≫ sY) (tensorPullback f F G) hTdim (hsupp ▸ ⟨q, rfl⟩)

/-- **Stacks Project, Lemma 0H51, restriction to open subschemes of the source and of the base.**
For open immersions `j : U ⟶ X` and `i : V ⟶ S` with `j ≫ f = fU ≫ i`, the restriction to
`U/V` of a relative `r`-cycle on `X/S` is a relative `r`-cycle.

The restriction is the base change along `i`, restricted along the open immersion
`U ⟶ X ×_S V` over `V`: the base change along an open immersion changes no coefficient, the
residue fields being equal, and the fibre maps factor through the fibres of `X ×_S V`
(`Stacks.Chow.fiberRestrict_pullbackLift_comp_restrictedFiberMap`). Both operations preserve
relative cycles. -/
@[stacks 0H51 "restriction to open subschemes of the source and of the base"]
theorem isRelativeCycle_restrictedFamily {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (fU : U ⟶ V) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i)
    (r : ℕ) {α : FamilyOfCycles f r} (hα : IsRelativeCycle f r α) :
    letI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion i
    IsRelativeCycle fU r (restrictedFamily f fU j i h r α).1 := by
  let : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion i
  have hres : ∀ t : V, IsIso (i.residueFieldMap t) := fun t => by
    let : IsIso (i.stalkMap t) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion i)).2 t
    exact (IsLocalRing.ResidueField.mapEquiv
      (asIso (i.stalkMap t)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  have heq : (restrictedFamily f fU j i h r α).1 = fun t =>
      fiberCycleRestrict (pullback.snd f i) fU (pullback.lift j fU h) (pullback.lift_snd _ _ _) t r
        (baseChangeFamily f i r α t) := by
    funext t
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    rw [(restrictedFamily f fU j i h r α).2 t x, fiberCycleRestrict_apply,
      baseChangeFamily_eq_baseChangeFamilyOfResidueIso f i hres r α,
      baseChangeFamilyOfResidueIso_apply, ← Scheme.Hom.comp_apply,
      fiberRestrict_pullbackLift_comp_restrictedFiberMap]
  rw [heq]
  exact isRelativeCycle_fiberCycleRestrict (pullback.snd f i) fU (pullback.lift j fU h)
    (pullback.lift_snd _ _ _) r (isRelativeCycle_baseChangeFamily f i r hα)

/-- If the zero scheme of `s'` is the inverse image of that of `s` under `p`, the same holds after
pulling back along a commutative square `a ≫ p = p' ≫ b`. -/
private theorem zeroScheme_pullback_eq_comap_of_comp {X Y X' Y' : Scheme.{u}} (p : X ⟶ Y)
    (a : X' ⟶ X) (b : Y' ⟶ Y) (p' : X' ⟶ Y') (h : a ≫ p = p' ≫ b) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (L' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
    (s' : Γ(L', ⊤))
    (hzero : Stacks.Divisors.zeroScheme X L' s' = (Stacks.Divisors.zeroScheme Y L s).comap p) :
    Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback a).obj L')
        (pullbackGlobalSections a L' s') =
      (Stacks.Divisors.zeroScheme Y' ((Scheme.Modules.pullback b).obj L)
        (pullbackGlobalSections b L s)).comap p' := by
  rw [Stacks.Divisors.zeroScheme_pullback, hzero, Stacks.Divisors.zeroScheme_pullback,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, h]

/-! ### The identity to be proved, read in `X` -/

section Action

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ) (e : ℤ)
  (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme Y L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme Y L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y L s).subschemeι).obj L))
  (L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  (s' : Γ(L', ⊤))
  (htriv' : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme X L' s').subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme X L' s').subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L' s').subschemeι).obj L'))

/-- The identity `α ∩ i_* i^* β = j_* j^*(α ∩ β)` of `(r + e)`-cycles on `X`, for every
`β ∈ Z_{e+1}(Y)`, where `i : D ⟶ Y` is the zero scheme of `s` and `j : E ⟶ X` that of `s'`.
When `E` is the inverse image of `D` this is Stacks 0H6E pushed forward to `X`. -/
def CapCommutesWithGysin (α : FamilyOfCycles p r) : Prop :=
  ∀ β : CycleGroup C sY (e + 1),
    cap C sY p α (gysinCycleMapPushforward C sY e L s htriv β) =
      gysinCycleMapPushforward C (p ≫ sY) ((r : ℤ) + e) L' s' htriv'
        (cycleGroupCongr C (p ≫ sY) (by ring) (cap C sY p α β))

variable (hzero : Stacks.Divisors.zeroScheme X L' s' = (Stacks.Divisors.zeroScheme Y L s).comap p)

include hzero in
/-- Both sides of the identity vanish on a cycle supported in the divisor `D`: the left by
`Stacks.Chow.gysinCycleMapPushforward_eq_zero_of_support_subset`, the right because `α ∩ β` is
then supported in `E = p⁻¹ D`. -/
theorem cap_gysin_of_support_subset (α : FamilyOfCycles p r) (β : CycleGroup C sY (e + 1))
    (hβ : Function.support β.1 ⊆ ((Stacks.Divisors.zeroScheme Y L s).support : Set Y)) :
    cap C sY p α (gysinCycleMapPushforward C sY e L s htriv β) =
      gysinCycleMapPushforward C (p ≫ sY) ((r : ℤ) + e) L' s' htriv'
        (cycleGroupCongr C (p ≫ sY) (by ring) (cap C sY p α β)) := by
  rw [gysinCycleMapPushforward_eq_zero_of_support_subset C sY e L s htriv β hβ,
    cap_zero_right, gysinCycleMapPushforward_eq_zero_of_support_subset]
  intro x hx
  have hx' : β.1 (p x) * (α (p x) : AlgebraicCycle (p.fiber (p x)) ℤ) (p.asFiber x) ≠ 0 := hx
  rw [hzero, Scheme.IdealSheafData.support_comap]
  exact hβ (left_ne_zero_of_mul hx')

include hzero in
/-- **The case of a flat closed subscheme and an integral cycle.** Let `α = [Z/X/Y]_r` for a closed
subscheme `Z ⊆ X` flat over `Y` with fibres of dimension at most `r`, and let `β = [W]` for an
integral closed subscheme `W ⊆ Y` of delta-dimension `e + 1`. Then `α ∩ i_* i^*β = j_* j^*(α ∩ β)`.

If `W ⊆ D` both sides vanish. Otherwise `i^*[W] = [W ∩ D]`, and Stacks 0H6A (used twice) gives
`α ∩ [W ∩ D] = [Z ×_Y (W ∩ D)]` and `α ∩ [W] = [Z ×_Y W]`; the divisor `E ∩ (Z ×_Y W)` is the
pullback of the effective Cartier divisor `D ∩ W` of `W` along the flat projection
`Z ×_Y W ⟶ W`, hence effective Cartier, so `j^*[Z ×_Y W] = [E ∩ (Z ×_Y W)]`, and the two closed
subschemes `Z ×_Y (W ∩ D)` and `E ∩ (Z ×_Y W)` of `Z` agree. -/
theorem cap_gysin_familyAssociatedToClosedSubscheme {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [Flat (i ≫ p)]
    (hZ : ∀ y : Y, topologicalKrullDim (pullback i (p.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞))
    (W : Y.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hWd : schemeDeltaDimension C (W.subschemeι ≫ sY) = ((e + 1 : ℤ) : EInt)) :
    cap C sY p (familyAssociatedToClosedSubscheme p i r)
        (gysinCycleMapPushforward C sY e L s htriv
          (cycleAssociatedToClosedSubscheme C sY W.subschemeι (e + 1))) =
      gysinCycleMapPushforward C (p ≫ sY) ((r : ℤ) + e) L' s' htriv'
        (cycleGroupCongr C (p ≫ sY) (by ring) (cap C sY p (familyAssociatedToClosedSubscheme p i r)
          (cycleAssociatedToClosedSubscheme C sY W.subschemeι (e + 1)))) := by
  set D := Stacks.Divisors.zeroScheme Y L s with hD
  by_cases hle : D ≤ W
  · refine cap_gysin_of_support_subset C sY p r e L s htriv L' s' htriv' hzero _ _ ?_
    intro y hy
    have h := support_cycleAssociatedToClosedSubscheme_subset C sY W.subschemeι (e + 1) hy
    rw [Scheme.IdealSheafData.range_subschemeι] at h
    exact Scheme.IdealSheafData.support_antitone hle h
  set g := i ≫ p with hg
  have hG : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap W.subschemeι) :=
    Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral L s W hW hle
  -- the delta-dimension of `W ∩ D`
  have hWe : schemeDeltaDimension C
      (((W.comap D.subschemeι).subschemeι ≫ D.subschemeι) ≫ sY) ≤ (e : EInt) := by
    have : IsIntegral W.subscheme := hW
    have h := schemeDeltaDimension_isEffectiveCartierDivisor_le C (W.subschemeι ≫ sY)
      (D.comap W.subschemeι) hG
    have hr : Set.range ((W.comap D.subschemeι).subschemeι ≫ D.subschemeι) =
        Set.range ((D.comap W.subschemeι).subschemeι ≫ W.subschemeι) := by
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
        Closeds.coe_preimage, Set.image_preimage_eq_inter_range]
      exact Set.inter_comm _ _
    rw [schemeDeltaDimension_eq_of_equal_ranges C sY _ _ hr]
    simp only [Category.assoc]
    refine h.trans (le_of_eq ?_)
    rw [hWd, ← coe_add_coe_eq_coe_add]
    congr 1
    ring
  -- the left side
  rw [gysinCycleMapPushforward_apply, gysinCycleMap_of_not_le C sY e L s htriv W hW hWd hle,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C _ sY
      D.subschemeι rfl _ e,
    cap_familyAssociatedToClosedSubscheme C sY p r e i hZ _ hWe,
    ← properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (i ≫ p ≫ sY) (p ≫ sY) i rfl]
  -- the right side
  rw [cap_familyAssociatedToClosedSubscheme C sY p r (e + 1) i hZ W.subschemeι hWd.le,
    cycleGroupCongr_cycleAssociatedToClosedSubscheme]
  have h1 : cycleAssociatedToClosedSubscheme C (p ≫ sY) (pullback.fst (i ≫ p) W.subschemeι ≫ i)
        ((r : ℤ) + e + 1) =
      properPushforward C (i ≫ p ≫ sY) (p ≫ sY) i rfl ((r : ℤ) + e + 1)
        (cycleAssociatedToClosedSubscheme C (i ≫ p ≫ sY) (W.comap g).subschemeι
          ((r : ℤ) + e + 1)) := by
    rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
    exact cycleAssociatedToClosedSubscheme_eq_of_iso C (p ≫ sY) _ _ (W.comapIso g).symm
      (by simp [g]) _
  rw [h1, gysinCycleMapPushforward_properPushforward C (p ≫ sY) ((r : ℤ) + e) L' s' htriv'
    (i ≫ p ≫ sY) i rfl]
  have hEZ : Stacks.Divisors.zeroScheme Z ((Scheme.Modules.pullback i).obj L')
      (pullbackGlobalSections i L' s') = D.comap g := by
    rw [Stacks.Divisors.zeroScheme_pullback i L' s', hzero, hg,
      Scheme.IdealSheafData.comap_comp]
  have hTdim : schemeDeltaDimension C ((W.comap g).subschemeι ≫ i ≫ p ≫ sY) ≤
      (((r : ℤ) + e + 1 : ℤ) : EInt) := by
    have h := schemeDeltaDimension_pullbackFst_comp_le C sY p r (e + 1) i hZ W.subschemeι hWd.le
    have hr : Set.range ((W.comap g).subschemeι ≫ i) =
        Set.range (pullback.fst (i ≫ p) W.subschemeι ≫ i) := by
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      rw [range_comap_subschemeι_eq_range_pullbackFst g W]
    have h' := schemeDeltaDimension_eq_of_equal_ranges C (p ≫ sY) _ _ hr
    simp only [Category.assoc] at h h' ⊢
    rw [h']
    refine h.trans (le_of_eq ?_)
    congr 1
    ring
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Divisors.zeroScheme Z ((Scheme.Modules.pullback i).obj L')
        (pullbackGlobalSections i L' s')).comap (W.comap g).subschemeι) := by
    rw [hEZ]
    set qw := (W.comapIso g).hom ≫ pullback.snd g W.subschemeι with hqw
    have hcomm : (W.comap g).subschemeι ≫ g = qw ≫ W.subschemeι := by
      rw [hqw, Category.assoc, ← pullback.condition,
        Scheme.IdealSheafData.comapIso_hom_fst_assoc]
    rw [← Scheme.IdealSheafData.comap_comp D (W.comap g).subschemeι g, hcomm,
      Scheme.IdealSheafData.comap_comp D qw W.subschemeι]
    exact Stacks.Divisors.isPullbackDefined_of_flat qw _ hG
  rw [gysinCycleMapPushforward_cycleAssociatedToClosedSubscheme C (i ≫ p ≫ sY) ((r : ℤ) + e)
    _ _ _ (W.comap g) hTdim hcart]
  congr 1
  rw [hEZ]
  exact cycleAssociatedToClosedSubscheme_pullbackFst_comap C (i ≫ p ≫ sY) g D W _

include hzero in
/-- **The case of a cycle in the image of the cycle class map over a quasi-compact base.** If `Y`
is quasi-compact and `α` is the image of `∑ nᵢ [Zᵢ]` under the cycle class map of Tag 0H6V, then
`α ∩ i_* i^* β = j_* j^*(α ∩ β)` for every `β ∈ Z_{e+1}(Y)`.

Both sides are additive in `α` and in `β`. The members of `Hilb(X/Y, r)` are flat closed
subschemes with fibres of dimension at most `r`, and on a quasi-compact scheme every cycle is a
finite sum of fundamental cycles of integral closed subschemes, so this is
`Stacks.Chow.cap_gysin_familyAssociatedToClosedSubscheme`. -/
theorem capCommutesWithGysin_cycleClassMap [CompactSpace Y] [LocallyOfFinitePresentation p]
    (c : FreeAbelianGroup (HilbertCycleDatum p r)) :
    CapCommutesWithGysin C sY p r e L s htriv L' s' htriv' (cycleClassMap p r c) := by
  let R := (gysinCycleMapPushforward C (p ≫ sY) ((r : ℤ) + e) L' s' htriv').comp
    (cycleGroupCongr C (p ≫ sY) (show (r : ℤ) + (e + 1) = (r : ℤ) + e + 1 by ring)).toAddMonoidHom
  have hprime : ∀ (W : Y.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hWd : schemeDeltaDimension C (W.subschemeι ≫ sY) = ((e + 1 : ℤ) : EInt)),
      cap C sY p (cycleClassMap p r c) (gysinCycleMapPushforward C sY e L s htriv
          (cycleAssociatedToClosedSubscheme C sY W.subschemeι (e + 1))) =
        gysinCycleMapPushforward C (p ≫ sY) ((r : ℤ) + e) L' s' htriv'
          (cycleGroupCongr C (p ≫ sY) (by ring) (cap C sY p (cycleClassMap p r c)
            (cycleAssociatedToClosedSubscheme C sY W.subschemeι (e + 1)))) := by
    intro W hW hWd
    let capL (k : ℤ) (γ : CycleGroup C sY k) :
        FamilyOfCycles p r →+ CycleGroup C (p ≫ sY) ((r : ℤ) + k) :=
      AddMonoidHom.mk' (fun α ↦ cap C sY p α γ) (fun a b ↦ cap_add_left C sY p a b γ)
    let F₁ := (capL e (gysinCycleMapPushforward C sY e L s htriv
      (cycleAssociatedToClosedSubscheme C sY W.subschemeι (e + 1)))).comp (cycleClassMap p r)
    let F₂ := R.comp
      ((capL (e + 1) (cycleAssociatedToClosedSubscheme C sY W.subschemeι (e + 1))).comp
        (cycleClassMap p r))
    have hF : F₁ = F₂ := by
      refine FreeAbelianGroup.lift_ext F₁ F₂ fun Z ↦ ?_
      change cap C sY p (cycleClassMap p r (FreeAbelianGroup.of Z)) _ =
        gysinCycleMapPushforward C (p ≫ sY) ((r : ℤ) + e) L' s' htriv'
          (cycleGroupCongr C (p ≫ sY) (by ring)
            (cap C sY p (cycleClassMap p r (FreeAbelianGroup.of Z)) _))
      rw [cycleClassMap_of, Z.cycleFamily_eq_familyAssociatedToClosedSubscheme p]
      have : Flat (Z.ideal.subschemeι ≫ p) := Z.flat
      exact cap_gysin_familyAssociatedToClosedSubscheme C sY p r e L s htriv L' s' htriv' hzero
        Z.ideal.subschemeι (Z.topologicalKrullDim_pullback_fiberι_le p) W hW hWd
    exact DFunLike.congr_fun hF c
  intro β
  let G₁ := (capHom C sY p r e (cycleClassMap p r c)).comp
    (gysinCycleMapPushforward C sY e L s htriv)
  let G₂ := R.comp (capHom C sY p r (e + 1) (cycleClassMap p r c))
  change G₁ β = G₂ β
  have hfin := finite_support_of_compactSpace C sY (e + 1) β
  rw [eq_finsetSum_cycleAssociatedToIntegralComponentAt C sY (e + 1) β hfin, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  exact hprime _ (isIntegral_integralComponentAt x)
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sY x
      ((mem_cyclesOfDimension_iff_forall_point C sY (e + 1) β.1).mp β.2 x
        (hfin.mem_toFinset.mp hx)))

omit hzero in
/-- **The reduction along an envelope** (the first paragraph of the proof of Stacks 0H6E). Let
`g : Y' ⟶ Y` be proper and completely decomposed. If the identity holds for the base change
`g^*α` over `Y'`, with the pulled-back sections, then it holds for `α` over `Y`.

Every cycle on `Y` is `g_* β'` because `g` is completely decomposed, and the identity is carried
from `Y'` to `Y` by Stacks 0H6B (twice) and Stacks 0H6D (twice), in the form
`Stacks.Chow.gysinCycleMapPushforward_properPushforward`. -/
theorem capCommutesWithGysin_of_envelope {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsProper g]
    (hcd : IsCompletelyDecomposed g) (α : FamilyOfCycles p r)
    (h' : CapCommutesWithGysin C (g ≫ sY) (pullback.snd p g) r e
      ((Scheme.Modules.pullback g).obj L) (pullbackGlobalSections g L s)
      (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections g L s htriv)
      ((Scheme.Modules.pullback (pullback.fst p g)).obj L')
      (pullbackGlobalSections (pullback.fst p g) L' s')
      (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
        (pullback.fst p g) L' s' htriv')
      (baseChangeFamily p g r α)) :
    CapCommutesWithGysin C sY p r e L s htriv L' s' htriv' α := by
  intro β
  rw [← envelopeCycleLift_pushforward C sY g hcd (e + 1) β]
  set β' := envelopeCycleLift C sY g hcd (e + 1) β
  have hpush (k : ℤ) (γ : CycleGroup C (g ≫ sY) k) :
      properPushforward C (pullback.snd p g ≫ g ≫ sY) (p ≫ sY) (pullback.fst p g)
          (pullbackFst_comp_eq_of_base g rfl rfl) ((r : ℤ) + k)
          (cap C (g ≫ sY) (pullback.snd p g) (baseChangeFamily p g r α) γ) =
        cap C sY p α (properPushforward C (g ≫ sY) sY g rfl k γ) :=
    properPushforward_cap_baseChangeFamily C (p ≫ sY) sY (g ≫ sY) p g rfl rfl r k α γ
  rw [gysinCycleMapPushforward_properPushforward C sY e L s htriv (g ≫ sY) g rfl β',
    ← hpush, h' β', ← hpush, ← properPushforward_cycleGroupCongr,
    gysinCycleMapPushforward_properPushforward C (p ≫ sY) ((r : ℤ) + e) L' s' htriv'
      (pullback.snd p g ≫ g ≫ sY) (pullback.fst p g) (pullbackFst_comp_eq_of_base g rfl rfl)]

include hzero in
/-- **The case of a Noetherian base and a quasi-compact morphism**, given the conclusion of
Tag 0H59 for `α`: a proper, completely decomposed `g : Y' ⟶ Y` with `g^*α` in the image of the
cycle class map. The identity over `Y'` is
`Stacks.Chow.capCommutesWithGysin_cycleClassMap`, `Y'` being quasi-compact, and it descends to `Y`
by `Stacks.Chow.capCommutesWithGysin_of_envelope`. -/
theorem capCommutesWithGysin_of_exists_envelope [CompactSpace Y]
    [LocallyOfFinitePresentation p] [QuasiCompact p] (α : FamilyOfCycles p r)
    (h59 : ∃ (Y' : Scheme.{u}) (g : Y' ⟶ Y), IsProper g ∧ PullbackInCycleClassImage p r α g ∧
      IsCompletelyDecomposed g) :
    CapCommutesWithGysin C sY p r e L s htriv L' s' htriv' α := by
  obtain ⟨Y', g, hprop, ⟨c, hc⟩, hcd⟩ := h59
  have := hprop
  have : CompactSpace Y' :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := g) Set.univ isOpen_univ isCompact_univ⟩
  refine capCommutesWithGysin_of_envelope C sY p r e L s htriv L' s' htriv' g hcd α ?_
  rw [← hc]
  refine capCommutesWithGysin_cycleClassMap C (g ≫ sY) (pullback.snd p g) r e _ _ _ _ _ _ ?_ c
  exact zeroScheme_pullback_eq_comap_of_comp p _ _ _ pullback.condition L s L' s' hzero

include hzero in
/-- **Stacks 0H6E read in `X`.** For a relative `r`-cycle `α` the identity
`α ∩ i_* i^* β = j_* j^*(α ∩ β)` holds for every `β ∈ Z_{e+1}(Y)`.

The question is local on `X` (the second paragraph of the proof of the lemma): every operation
commutes with restriction to open subschemes — the action by Stacks 0H67, relative cycles by
`Stacks.Chow.isRelativeCycle_restrictedFamily`, and `i_* ∘ i^*` by
`Stacks.Chow.cycleGroupRestrict_gysinCycleMapPushforward` — and over an affine open of `Y` with an
affine open of `X` above it the base is Noetherian and the morphism quasi-compact. There Tag 0H59
supplies an envelope after which the relative cycle is in the image of the cycle class map, and
`Stacks.Chow.capCommutesWithGysin_of_exists_envelope` applies. -/
theorem capCommutesWithGysin_of_isRelativeCycle (α : FamilyOfCycles p r)
    (hα : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      IsRelativeCycle p r α) :
    CapCommutesWithGysin C sY p r e L s htriv L' s' htriv' α := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  intro β
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := p x)
    (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x)
    (U := p ⁻¹ᵁ V) hxV
  set fU := p.resLE V U hUV with hfU
  have hsq : U.ι ≫ p = fU ≫ V.ι := (p.resLE_comp_ι hUV).symm
  let : LocallyOfFiniteType fU := by
    have : LocallyOfFiniteType (fU ≫ V.ι) := hsq ▸ inferInstance
    exact locallyOfFiniteType_of_comp fU V.ι
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  let : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  let : IsNoetherian V.toScheme := ⟨⟩
  let : QuasiCompact fU := inferInstance
  set αU := (restrictedFamily p fU U.ι V.ι hsq r α).1 with hαU_def
  have hαU : IsRelativeCycle fU r αU := isRelativeCycle_restrictedFamily p fU U.ι V.ι hsq r hα
  have hzloc : Stacks.Divisors.zeroScheme U ((Scheme.Modules.pullback U.ι).obj L')
      (pullbackGlobalSections U.ι L' s') =
      (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback V.ι).obj L)
        (pullbackGlobalSections V.ι L s)).comap fU := by
    exact zeroScheme_pullback_eq_comap_of_comp p _ _ _ hsq L s L' s' hzero
  have hloc := capCommutesWithGysin_of_exists_envelope C (V.ι ≫ sY) fU r e _ _
    (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections V.ι L s htriv) _ _
    (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections U.ι L' s' htriv')
    hzloc αU
    (exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage_of_isRelativeCycle fU r hαU)
    (cycleGroupRestrict C sY (V.ι ≫ sY) V.ι rfl (e + 1) β)
  have hcap (k : ℤ) (γ : CycleGroup C sY k) :
      (cycleGroupRestrict C (p ≫ sY) (fU ≫ V.ι ≫ sY) U.ι
          (by rw [← Category.assoc, hsq, Category.assoc]) ((r : ℤ) + k) (cap C sY p α γ)) =
        cap C (V.ι ≫ sY) fU αU (cycleGroupRestrict C sY (V.ι ≫ sY) V.ι rfl k γ) :=
    cycleGroupRestrict_cap C sY (V.ι ≫ sY) p fU U.ι V.ι rfl hsq r k α γ
  let x' : U.toScheme := ⟨x, hxU⟩
  have hx' : U.ι.base x' = x := rfl
  -- the left side, restricted to `U`
  have hL := congrArg (fun c : CycleGroup C (fU ≫ V.ι ≫ sY) ((r : ℤ) + e) ↦ c.1 x')
    (hcap e (gysinCycleMapPushforward C sY e L s htriv β))
  simp only [cycleGroupRestrict_apply, hx'] at hL
  rw [hL, cycleGroupRestrict_gysinCycleMapPushforward C sY e L s htriv V.ι
    (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections V.ι L s htriv), hloc]
  -- the right side, restricted to `U`
  have hR := congrArg (fun c : CycleGroup C (U.ι ≫ p ≫ sY) ((r : ℤ) + e) ↦ c.1 x')
    (cycleGroupRestrict_gysinCycleMapPushforward C (p ≫ sY) ((r : ℤ) + e) L' s' htriv' U.ι
      (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections U.ι L' s' htriv')
      (cycleGroupCongr C (p ≫ sY) (by ring) (cap C sY p α β)))
  simp only [cycleGroupRestrict_apply, hx'] at hR
  rw [hR]
  refine congrArg (fun c : AlgebraicCycle U.toScheme ℤ ↦ c x') ?_
  refine (gysinCycleMapPushforward_congr C _ _ _ _ _ _ (by rw [← Category.assoc, hsq,
    Category.assoc]) _ _ ?_).symm
  apply Function.locallyFinsuppWithin.ext
  intro z
  have hz := congrArg (fun c : CycleGroup C (fU ≫ V.ι ≫ sY) ((r : ℤ) + (e + 1)) ↦ c.1 z)
    (hcap (e + 1) β)
  simp only [cycleGroupRestrict_apply] at hz
  simp only [cycleGroupCongr_apply_coe, cycleGroupRestrict_apply]
  exact hz

end Action

/-! ### Stacks 0H6E -/

/-- A closed immersion `m` cutting out a closed subscheme `Z` identifies its source with `Z`,
over the ambient scheme. -/
theorem exists_iso_subscheme_of_ker_eq {P V : Scheme.{u}} (m : P ⟶ V) [IsClosedImmersion m]
    (Z : V.IdealSheafData) (h : m.ker = Z) :
    ∃ e : P ≅ Z.subscheme, e.hom ≫ Z.subschemeι = m := by
  subst h
  exact ⟨asIso m.toImage, m.toImage_imageι⟩

/-- **Stacks Project, Tag 0H6E.** Let `(S, δ)` be as in Section 0H65, let `p : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`, let `r ≥ 0` and let `α ∈ z(X/Y, r)` be a
relative `r`-cycle on `X/Y`. Let `(L, s, i : D ⟶ Y)` be as in Chow Homology, Definition 02T8:
`L` an invertible module on `Y`, `s` a global section and `i` the closed immersion of its zero
scheme `D`. Form the cartesian square of Chow Homology, Remark 0B6Y,
```
E = X ×_Y D --j--> X
     |             |
     v             v
     D    --i-->   Y
```
so that `j` presents `E` as the zero scheme of the pulled-back section `p^* s` of `p^* L`. If
`L|_D ≅ 𝒪_D`, then for every `e ∈ ℤ` and every `β ∈ Z_{e+1}(Y)`
`i^*α ∩ i^*β = j^*(α ∩ β)` in `Z_{r+e}(E)`,
where `∩` is the action of Section 0H65, `i^*α` the base change of `α` along `i`, and
`i^* : Z_{e+1}(Y) ⟶ Z_e(D)` and `j^* : Z_{r+e+1}(X) ⟶ Z_{r+e}(E)` the Gysin maps on cycles of
Chow Homology, Remark 0B6Z, the latter read along the presentation `j` of the zero scheme of
`p^* s` (`Stacks.Chow.gysinCycleMapAlong`). The triviality of `(p^* L)|_E` that `j^*` needs is
not a hypothesis: it follows from that of `L|_D`. -/
@[stacks 0H6E]
theorem cap_baseChangeFamily_gysinCycleMap (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ) (e : ℤ)
    (α : FamilyOfCycles p r)
    (hα : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      IsRelativeCycle p r α)
    (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme Y L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme Y L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y L s).subschemeι).obj L))
    (β : CycleGroup C sY (e + 1)) :
    cap C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
        (pullback.snd p (Stacks.Divisors.zeroScheme Y L s).subschemeι)
        (baseChangeFamily p (Stacks.Divisors.zeroScheme Y L s).subschemeι r α)
        (gysinCycleMap C sY e L s htriv β) =
      gysinCycleMapAlong C (p ≫ sY)
        (pullback.snd p (Stacks.Divisors.zeroScheme Y L s).subschemeι ≫
          (Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) ((r : ℤ) + e)
        ((Scheme.Modules.pullback p).obj L) (pullbackGlobalSections p L s)
        (pullback.fst p (Stacks.Divisors.zeroScheme Y L s).subschemeι)
        (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections p L s htriv)
        (by rw [← Category.assoc, pullback.condition, Category.assoc])
        (Stacks.Divisors.zeroScheme_pullback p L s).symm
        (cycleGroupCongr C (p ≫ sY) (by ring) (cap C sY p α β)) := by
  set D := Stacks.Divisors.zeroScheme Y L s with hD
  set E := Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback p).obj L)
    (pullbackGlobalSections p L s) with hE
  have htriv' := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections p L s htriv
  have hq : pullback.fst p D.subschemeι ≫ p ≫ sY =
      pullback.snd p D.subschemeι ≫ D.subschemeι ≫ sY := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have hM := capCommutesWithGysin_of_isRelativeCycle C sY p r e L s htriv
    ((Scheme.Modules.pullback p).obj L) (pullbackGlobalSections p L s) htriv'
    (Stacks.Divisors.zeroScheme_pullback p L s) α hα β
  apply properPushforward_injective_of_isClosedImmersion C _ (p ≫ sY)
    (pullback.fst p D.subschemeι) hq ((r : ℤ) + e)
  rw [properPushforward_cap_baseChangeFamily C (p ≫ sY) sY (D.subschemeι ≫ sY) p D.subschemeι
    rfl rfl r e α (gysinCycleMap C sY e L s htriv β)]
  change cap C sY p α (gysinCycleMapPushforward C sY e L s htriv β) = _
  rw [hM, gysinCycleMapPushforward_apply]
  obtain ⟨eiso, he⟩ := exists_iso_subscheme_of_ker_eq (pullback.fst p D.subschemeι) E
    (Stacks.Divisors.zeroScheme_pullback p L s).symm
  rw [← properPushforward_gysinCycleMapAlong C (p ≫ sY) ((r : ℤ) + e) _ _ htriv'
    (pullback.snd p D.subschemeι ≫ D.subschemeι ≫ sY) (pullback.fst p D.subschemeι) hq
    (Stacks.Divisors.zeroScheme_pullback p L s).symm eiso he]
  have h1 := congrFun (properPushforward_comp C _ _ (p ≫ sY) eiso.hom E.subschemeι
    (by rw [← Category.assoc, he, hq]) rfl ((r : ℤ) + e))
    (gysinCycleMapAlong C (p ≫ sY) (pullback.snd p D.subschemeι ≫ D.subschemeι ≫ sY)
      ((r : ℤ) + e) ((Scheme.Modules.pullback p).obj L) (pullbackGlobalSections p L s)
      (pullback.fst p D.subschemeι) htriv' hq (Stacks.Divisors.zeroScheme_pullback p L s).symm
      (cycleGroupCongr C (p ≫ sY) (by ring) (cap C sY p α β)))
  simp only [Function.comp_apply] at h1
  rw [h1]
  congr 1

end Stacks.Chow

end
