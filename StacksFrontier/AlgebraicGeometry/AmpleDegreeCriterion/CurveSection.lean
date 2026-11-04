module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Vanishing
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Extension
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Consumers
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.FiniteRank
public import StacksFrontier.AlgebraicGeometry.AmplePredicateBridge.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.CoherentColimit
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Devissage
public import StacksFrontier.Topology.Dimension.Krull

/-!
# A section of a large power vanishing off an affine open

This is the second paragraph of the proof of [Stacks, Tag 0B5X]. Let `X` be a proper curve over a
field `k` and `𝓛` an invertible `𝒪_X`-module of positive degree. Then some positive tensor power
of `𝓛` has a global section whose nonvanishing open is nonempty and affine.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `isCoherent_pushforward_unit`: the direct image of the structure sheaf along a closed immersion
  into a locally Noetherian scheme is coherent.
* `topologicalKrullDim_supp_pushforward_le`: a direct image along a closed immersion is supported
  inside the image, so its support has at most the dimension of that image.
* `pushforwardPullbackIsoTensorPushforwardUnit`: **the projection formula at `𝒪_Z`**,
  `(i_*𝒪_Z) ⊗ 𝒫 ≅ i_*i^*𝒫`.
* `isCoherent_pushforward_pullback`: `i_*i^*𝒫` is coherent for `𝒫` invertible.
* `finrank_cohomologyOverField_zero_pushforward_pullback_eq`: **`dim_k Γ(X, i_*i^*𝒫)` does not
  depend on `𝒫`**, as long as the image of `i` has dimension at most zero.
* `hasAffinePowerOfDegreePos_of_isCurve`: **the paragraph**, inhabiting
  `AlgebraicGeometry.HasAffinePowerOfDegreePos` of `./Vanishing.lean` with nothing assumed.

## The argument

Fix an affine open `U` around any point and let `i : Z ⟶ X` be the reduced closed subscheme on
the complement `X ∖ U`, a proper closed subset of an irreducible curve and hence of dimension at
most zero ([Stacks, Tag 0AYT] is applied to modules supported there).

The source produces a nonzero section of `𝓛^{⊗ n}` vanishing on `X ∖ U` by a dimension count.
Here the count is run against the unit `𝓛^{⊗ n} ⟶ i_*i^*𝓛^{⊗ n}` of `i^* ⊣ i_*`, whose kernel on
global sections is exactly the sections vanishing on `Z`:

* `dim_k Γ(X, 𝓛^{⊗ n})` is at least `n · deg(𝓛) + χ(X, 𝒪_X)` and so grows without bound, by
  `AlgebraicGeometry.le_finrank_cohomologyOverField_zero_tensorPower`.
* `dim_k Γ(X, i_*i^*𝓛^{⊗ n})` is the *same number for every* `n`: the projection formula
  identifies `i_*i^*𝓛^{⊗ n}` with `(i_*𝒪_Z) ⊗ 𝓛^{⊗ n}`, whose Euler characteristic is that of
  `i_*𝒪_Z` because `i_*𝒪_Z` is coherent with zero-dimensional support and `𝓛^{⊗ n}` is finite
  locally free of rank one ([Stacks, Tag 0AYT], "tensor_rank"); and on a module with
  zero-dimensional support the Euler characteristic *is* `dim_k Γ` ([Stacks, Tag 0AYT] (4)).

So for `n` large the unit is not injective on global sections, and the difference of two sections
with the same image is a nonzero `c` killed by the unit.
`Stacks.AmpleReducedDimensionOne.notMem_nonvanishingLocus_of_unit_app_top_eq_zero` then says that
`c` vanishes at every point of `Z`, that is `X_c ⊆ U`; so `X_c` is affine by [Stacks, Tag 01PV]
and nonempty because `c ≠ 0` on an integral scheme.

## Implementation notes

**Why the unit and not the ideal sheaf.** The source phrases the count with the sequence
`0 ⟶ ℐ ⊗ 𝓛^{⊗ n} ⟶ 𝓛^{⊗ n} ⟶ (i_*𝒪_Z) ⊗ 𝓛^{⊗ n} ⟶ 0`. Reading it at the unit instead costs the
projection formula — which is available for closed immersions, as
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` — and saves the step from
"`c` lies in the image of `Γ(ℐ ⊗ 𝓛^{⊗ n})`" to "`c` vanishes on `Z`", which is a statement about
germs that the library does not have. At the unit that step is the lemma quoted above.

**No non-affineness of `X` is needed.** The source observes that `X` is not affine; that is used
only to know `X ∖ U` is nonempty, which is not needed here: the count is run against a closed
subscheme that may be empty, and `X_c ⊆ U` is then vacuous but still true.

**The nonvanishing open has three spellings in play.** `Stacks.SheafOfModules.nonvanishingOpen`
is the one `AlgebraicGeometry.HasAffinePowerOfDegreePos` and the vanishing lemma use;
`Stacks.NonvanishingOpen.nonvanishingOpen` is the one [Stacks, Tag 01PV] is stated at; and
`Stacks.Ample.nonvanishingLocus` is the underlying set both coerce to, by
`Stacks.AmplePredicateBridge.coe_nonvanishingOpen_sectionsOfTop` and
`Stacks.NonvanishingOpen.coe_nonvanishingOpen`. The two opens are therefore equal, not merely
isomorphic, and the affineness transports by rewriting.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (nonvanishingLocus nonvanishingOpen sectionsOfTop)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The direct image of the structure sheaf of a closed subscheme -/

/-- **The direct image of `𝒪_Z` along a closed immersion into a locally Noetherian scheme is
coherent.** The source of a closed immersion is locally Noetherian, so its structure sheaf is
coherent, and a closed immersion is finite. -/
public theorem isCoherent_pushforward_unit [IsLocallyNoetherian X] {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) :=
  have _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have _ : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z
  Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite i _

/-- **A direct image along a closed immersion is supported inside the image of the immersion**,
so the dimension of its support is at most that of the image. -/
public theorem topologicalKrullDim_supp_pushforward_le {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (G : Z.Modules) :
    topologicalKrullDim
        (_root_.SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G)) ≤
      topologicalKrullDim (Set.range i.base) := by
  refine _root_.topologicalKrullDim_le_of_subset ?_
  rw [supp_pushforward_of_isClosedImmersion]
  exact Set.image_subset_range _ _

/-! ### The projection formula at the structure sheaf -/

/-- **The projection formula for a closed immersion, at the structure sheaf of the source**:
`(i_*𝒪_Z) ⊗ 𝒫 ≅ i_*i^*𝒫`.

This is `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` with its first
argument the structure sheaf, followed by the left unit constraint of the tensor product on the
source. -/
public def pushforwardPullbackIsoTensorPushforwardUnit {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (P : X.Modules) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
      (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))).obj (P)) ≅
      (Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj P :=
  Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i
      (SheafOfModules.unit Z.ringCatSheaf) P ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor Z.presheaf Z.ringCatSheaf.2
        ((Scheme.Modules.pullback i).obj P))

/-- **`i_*i^*𝒫` is coherent for an invertible `𝒫`.** It is isomorphic to `(i_*𝒪_Z) ⊗ 𝒫`, and the
tensor product of a coherent module with an invertible one is coherent. -/
public theorem isCoherent_pushforward_pullback [IsLocallyNoetherian X] {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (P : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P] :
    _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj P) :=
  have _ := isCoherent_pushforward_unit i
  GroupoidScheme.isCoherent_of_iso (pushforwardPullbackIsoTensorPushforwardUnit i P)
    (SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X _ P)

/-! ### The global sections of `i_*i^*𝒫` do not grow -/

/-- **`dim_k Γ(X, i_*i^*𝒫)` is `dim_k Γ(X, i_*𝒪_Z)` for every invertible `𝒫`**, as soon as the
image of the closed immersion has dimension at most zero.

The projection formula turns `i_*i^*𝒫` into `(i_*𝒪_Z) ⊗ 𝒫`; on a coherent module with
zero-dimensional support the Euler characteristic is the dimension of the global sections
([Stacks, Tag 0AYT] (4)), and tensoring such a module by a finite locally free module of rank one
multiplies its Euler characteristic by one ([Stacks, Tag 0AYT], "tensor_rank"). -/
public theorem finrank_cohomologyOverField_zero_pushforward_pullback_eq [IsProper f]
    [IsLocallyNoetherian X] {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hdim0 : topologicalKrullDim (Set.range i.base) ≤ 0) (P : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P] :
    Module.finrank k (cohomologyOverField k f
        ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj P) 0) =
      Module.finrank k (cohomologyOverField k f
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) 0) := by
  have _ := isCoherent_pushforward_unit i
  have hsuppW := le_trans (topologicalKrullDim_supp_pushforward_le i
    (SheafOfModules.unit Z.ringCatSheaf)) hdim0
  have _ := Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X P
  obtain ⟨hWP, hchi⟩ := exists_eulerCharacteristic_tensorSheaf_eq_rank_mul k f
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) hsuppW P 1
  have hsuppWP := le_of_eq_of_le
    (congrArg (fun S : Set X => topologicalKrullDim S)
      (_root_.SheafOfModules.supp_eq_of_iso (pushforwardPullbackIsoTensorPushforwardUnit i P)))
    (le_trans (topologicalKrullDim_supp_pushforward_le i
      ((Scheme.Modules.pullback i).obj P)) hdim0)
  refine (finrank_cohomologyOverField_eq_of_iso k f
    (pushforwardPullbackIsoTensorPushforwardUnit i P) 0).symm.trans
    (Nat.cast_injective (R := ℤ) ?_)
  rw [← @eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero k _ X f _ _ hWP
      hsuppWP,
    hchi, Nat.cast_one, one_mul,
    @eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero k _ X f _ _
      (isCoherent_pushforward_unit i) hsuppW]

/-! ### The paragraph -/

/-- **The reduced closed subscheme on the complement of an open has that complement as image.** -/
public theorem range_subschemeι_vanishingIdeal_compl (U : X.Opens) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal
      (⟨(↑U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)).subschemeι.base =
      (↑U : Set X)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- **If `Γ(X, i_*i^*𝒫)` is smaller than `Γ(X, 𝒫)`, the unit `𝒫 ⟶ i_*i^*𝒫` kills a nonzero
global section.** -/
public theorem exists_ne_zero_unit_app_top_eq_zero [IsProper f] [IsLocallyNoetherian X]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (P : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P]
    (hlt : Module.finrank k (cohomologyOverField k f
        ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj P) 0) <
      Module.finrank k (cohomologyOverField k f P 0)) :
    ∃ c : Γ(P, ⊤), c ≠ 0 ∧ (ConcreteCategory.hom (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app P) ⊤)) c = 0 := by
  have _ : FiniteDimensional k (cohomologyOverField k f
      ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj P) 0) :=
    forall_finiteDimensional_cohomologyOverField_of_isProper k f _
      (isCoherent_pushforward_pullback i P) 0
  set u := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app P
  have hninj : ¬ Function.Injective (ModuleCat.Hom.hom (cohomologyOverFieldMap k f u 0)) :=
    fun hinj => absurd hlt (not_lt.mpr (LinearMap.finrank_le_finrank_of_injective hinj))
  obtain ⟨a₁, a₂, hA, hane⟩ := Function.not_injective_iff.mp hninj
  set c₁ := cohomologyOverFieldZeroEquivSections k f ((𝟭 X.Modules).obj P) a₁
  set c₂ := cohomologyOverFieldZeroEquivSections k f ((𝟭 X.Modules).obj P) a₂
  have happ : (ConcreteCategory.hom (Scheme.Modules.Hom.app u ⊤)) c₁ =
      (ConcreteCategory.hom (Scheme.Modules.Hom.app u ⊤)) c₂ :=
    (cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f u a₁).symm.trans
      ((congrArg (cohomologyOverFieldZeroEquivSections k f
        ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj P)) hA).trans
        (cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f u a₂))
  refine ⟨c₁ - c₂, sub_ne_zero.mpr fun h =>
    hane ((cohomologyOverFieldZeroEquivSections k f ((𝟭 X.Modules).obj P)).injective h), ?_⟩
  rw [map_sub, happ, sub_self]

/-- **A nonzero global section of an invertible module on an integral scheme whose nonvanishing
open lies in an affine open has nonempty nonvanishing locus and affine nonvanishing open.** -/
public theorem nonempty_and_isAffineOpen_nonvanishingOpen_of_le [IsIntegral X] (P : X.Modules)
    [hP : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P] {U : X.Opens}
    (hU : IsAffineOpen U) (c : Γ(P, ⊤)) (hc : c ≠ 0)
    (hsub : nonvanishingOpen (X := X.toRingedSpace) P (sectionsOfTop P c) ≤ U) :
    (∃ x : X, x ∈ nonvanishingLocus (X := X.toRingedSpace) P (sectionsOfTop P c)) ∧
      IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) P (sectionsOfTop P c)) := by
  refine ⟨@nonempty_nonvanishingLocus_of_eval_top_ne_zero X _ P hP _ fun hz =>
    hc ((Stacks.SheafOfModules.sectionsOfTop_eval_top (X := X.toRingedSpace) P c).symm.trans hz),
    ?_⟩
  have hbridge : nonvanishingOpen (X := X.toRingedSpace) P (sectionsOfTop P c) =
      Stacks.NonvanishingOpen.nonvanishingOpen X P c :=
    Opens.ext ((Stacks.AmplePredicateBridge.coe_nonvanishingOpen_sectionsOfTop X P c).trans
      (Stacks.NonvanishingOpen.coe_nonvanishingOpen X P c).symm)
  rw [hbridge] at hsub ⊢
  exact Stacks.NonvanishingAffineIntersection.isAffineOpen_of_le_affineOpen P c hU hsub

/-- **The second paragraph of the proof of [Stacks, Tag 0B5X].** On a proper curve over a field,
an invertible module of positive degree has a positive tensor power with a global section whose
nonvanishing locus is nonempty and whose nonvanishing open is affine.

Nothing is assumed: this inhabits `AlgebraicGeometry.HasAffinePowerOfDegreePos` outright. -/
public theorem hasAffinePowerOfDegreePos_of_isCurve [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    HasAffinePowerOfDegreePos k f hdim L := by
  intro hdeg
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hUaff, hxU, -⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Opens.mem_top x)
  have hrange := range_subschemeι_vanishingIdeal_compl U
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(↑U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds X)
  have hdim0 : topologicalKrullDim (Set.range I.subschemeι.base) ≤ 0 := by
    rw [hrange]
    exact topologicalKrullDim_le_zero_of_isClosed_of_ne_univ hdim _ U.isOpen.isClosed_compl
      (Set.compl_ne_univ.mpr ⟨x, hxU⟩)
  set c₀ := Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward I.subschemeι).obj
    (SheafOfModules.unit (I.subscheme).ringCatSheaf)) 0)
  set a := Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0)
  set b := Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1)
  refine ⟨((c₀ : ℤ) - (a : ℤ) + (b : ℤ)).toNat + 1, Nat.le_add_left 1 _, ?_⟩
  set N := ((c₀ : ℤ) - (a : ℤ) + (b : ℤ)).toNat + 1 with hN
  set P := tensorPower X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L (N : ℤ)
  have _ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P :=
    tensorPower_isInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (N : ℤ)
  have hgrow := le_finrank_cohomologyOverField_zero_tensorPower k f hdim L (N : ℤ)
  have hlt : c₀ < Module.finrank k (cohomologyOverField k f P 0) := by
    have hd : (1 : ℤ) ≤ invertibleCurveDegree k f hdim L := by omega
    have hNge : ((c₀ : ℤ) - (a : ℤ) + (b : ℤ)) + 1 ≤ (N : ℤ) := by
      rw [hN]
      push_cast
      omega
    have hmul : (N : ℤ) ≤ (N : ℤ) * invertibleCurveDegree k f hdim L :=
      le_mul_of_one_le_right (Int.natCast_nonneg N) hd
    exact_mod_cast (by linarith : (c₀ : ℤ) < Module.finrank k (cohomologyOverField k f P 0))
  obtain ⟨c, hc, hzero⟩ := exists_ne_zero_unit_app_top_eq_zero k f I.subschemeι P
    ((finrank_cohomologyOverField_zero_pushforward_pullback_eq k f I.subschemeι hdim0 P).trans_lt
      hlt)
  refine ⟨_, nonempty_and_isAffineOpen_nonvanishingOpen_of_le P hUaff c hc fun y hy => ?_⟩
  by_contra hyU
  obtain ⟨z, rfl⟩ : ∃ z, I.subschemeι.base z = y := by
    rw [← Set.mem_range, hrange]
    exact hyU
  exact Stacks.AmpleReducedDimensionOne.notMem_nonvanishingLocus_of_unit_app_top_eq_zero
    I.subschemeι P c hzero z hy

end AlgebraicGeometry

end
