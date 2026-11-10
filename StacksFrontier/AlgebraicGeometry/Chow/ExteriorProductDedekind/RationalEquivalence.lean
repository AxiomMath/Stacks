module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.BaseGeometry
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.ChowGroups
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.GysinTrivial
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.CartesianSquare

/-!
# Stacks 0FC4: the exterior product over a Dedekind base is well defined

Let `(S, δ)` be as in Stacks section 42.63 and let `X`, `Y` be locally of finite type over `S`.
This file proves that the exterior product of cycles
`× : Z_n(X) ⟶ Z_m(Y) ⟶ Z_{n+m-1}(X ×_S Y)` of
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.Cycles` carries a cycle rationally
equivalent to zero, in either variable, to a cycle rationally equivalent to zero, and hence that

  `× : CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`

is well defined.

## Main results

* `Stacks.Chow.properPushforward_flatPullback_of_dominates`,
  `Stacks.Chow.properPushforward_flatPullback_gysin_of_not_dominates` — the summands of `α × β`
  at a point of the support of `α`, for an arbitrary cycle `β`.
* `Stacks.Chow.exteriorProductDedekindCycles_apply_eq_finsum` — `α × β` is the locally finite sum
  of the pushforwards of its summands.
* `Stacks.Chow.exteriorProductDedekindCycles_mem_rationalEquivalences_right`,
  `Stacks.Chow.exteriorProductDedekindCycles_mem_rationalEquivalences_left` — `α × β` is
  rationally equivalent to zero when `β`, respectively `α`, is.
* `Stacks.Chow.exteriorProductFactorsThroughRationalEquivalence_of_isDedekindChowBase` — the
  exterior product of cycles is compatible with rational equivalence in each variable.
* `Stacks.Chow.exteriorProductDedekindChowTensor` — the map
  `CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`.
* `Stacks.Chow.existsUnique_exteriorProductDedekindChowTensor` — there is exactly one additive map
  `CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)` sending `[α] ⊗ [β]` to the class of `α × β`.

## References

* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0B2I](https://stacks.math.columbia.edu/tag/0B2I)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Chow

/-! ### Closed subschemes of a closed subscheme -/

/-- The ideal sheaf on `X ×_S Y` cutting out `Z ×_S Y` for a closed subset `Z ⊆ X`: the inverse
image under the first projection of the vanishing ideal of `Z`, the reduced structure on `Z`. -/
abbrev closedSubsetFibre {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (Z : Closeds X) :
    (pullback f g : Scheme.{u}).IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal Z).comap (pullback.fst f g)

/-- The ideal sheaf on `X ×_S Y` cutting out `closure {x} ×_S Y`. -/
abbrev dedekindPointFibre {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) :
    (pullback f g : Scheme.{u}).IdealSheafData :=
  closedSubsetFibre f g (Closeds.closure ({x} : Set X))

/-- A morphism `i : Z ⟶ Q` whose kernel contains that of a closed immersion `j : W ⟶ Q` factors
through `j`, so the projection `W ×_Q Z ⟶ Z` is an isomorphism. -/
theorem isIso_pullback_snd_of_ker_le {Q W Z : Scheme.{u}} (j : W ⟶ Q) [IsClosedImmersion j]
    (i : Z ⟶ Q) (h : j.ker ≤ i.ker) : IsIso (pullback.snd j i) := by
  have hl : IsClosedImmersion.lift j i h ≫ j = i := IsClosedImmersion.lift_fac j i h
  refine ⟨pullback.lift (IsClosedImmersion.lift j i h) (𝟙 Z) (by simp [hl]), ?_, ?_⟩
  · refine pullback.hom_ext ?_ (by simp)
    refine (cancel_mono j).1 ?_
    simp [hl, ← pullback.condition]
  · simp

/-- The square exhibiting `closure {x} ×_S Y` as a fibre product over the base. -/
theorem isPullback_dedekindPointFibre {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) :
    IsPullback ((pointClosureFibreIso f g x).hom ≫
        pullback.fst ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g)
      ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pointClosureFibreIso f g x) rfl
    (pointClosureFibreIso_hom_snd f g x)
  rw [← pointClosureFibreIso_hom_snd f g x, Category.assoc, Category.assoc, pullback.condition]

/-- Inside `closure {x} ×_S Y`, the product `closure {x} ×_S closure {y}` is the inverse image of
`closure {y}` under the projection to `Y`. -/
theorem comap_exteriorProductIdeal_dedekindPointFibre {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (x : X) (y : Y) :
    (exteriorProductIdeal f g x y).comap (dedekindPointFibre f g x).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).comap
        ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g) := by
  set K : (pullback f g : Scheme.{u}).IdealSheafData := dedekindPointFibre f g x with hK
  have hkill : K.comap K.subschemeι = ⊥ := by
    have h := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion K.subschemeι K.subschemeι
    rw [K.ker_subschemeι] at h
    rw [← h, Scheme.Hom.ker_eq_bot_of_isIso]
  rw [exteriorProductIdeal, Scheme.IdealSheafData.comap_sup, hkill, bot_sup_eq,
    ← Scheme.IdealSheafData.comap_comp]

/-- The kernel of `ι_x` is contained in the ideal of `closure {x} ×_S closure {y}`. -/
theorem ker_dedekindPointFibre_le {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) :
    (dedekindPointFibre f g x).subschemeι.ker ≤ exteriorProductIdeal f g x y := by
  rw [Scheme.IdealSheafData.ker_subschemeι, exteriorProductIdeal]
  exact le_sup_left

/-- A point lies over `closure {x}` exactly when it lies in `closure {x} ×_S Y`. -/
private theorem mem_support_dedekindPointFibre_iff {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x : X) (w : (pullback f g : Scheme.{u})) :
    w ∈ ((dedekindPointFibre f g x).support : Set (pullback f g : Scheme.{u})) ↔
      (pullback.fst f g).base w ∈ closure ({x} : Set X) := by
  simp [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The inverse images of the closures of the points of the support of a cycle under the first
projection form a locally finite family. -/
theorem locallyFinite_dedekindPointFibre {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (c : AlgebraicCycle X ℤ) :
    LocallyFinite fun x : c.support ↦
      ((dedekindPointFibre f g x.1).support : Set (pullback f g : Scheme.{u})) := by
  classical
  intro z
  obtain ⟨t, ht, hfin⟩ := c.supportLocallyFiniteWithinDomain' ((pullback.fst f g).base z) trivial
  obtain ⟨U, hUt, hU, hzU⟩ := mem_nhds_iff.1 ht
  refine ⟨(pullback.fst f g).base ⁻¹' U,
    ((hU.preimage (pullback.fst f g).continuous).mem_nhds hzU), ?_⟩
  have hpre : ((fun x : c.support ↦ (x : X)) ⁻¹' (t ∩ c.support)).Finite :=
    hfin.preimage (fun a _ b _ hab ↦ Subtype.ext hab)
  have hfinU : {x : c.support | (x : X) ∈ U}.Finite := hpre.subset fun x hx ↦ ⟨hUt hx, x.2⟩
  refine hfinU.subset ?_
  rintro x ⟨w, hw, hwU⟩
  exact (isGenericPoint_closure (x := (x : X))).mem_open_set_iff hU |>.2
    ⟨(pullback.fst f g).base w, (mem_support_dedekindPointFibre_iff f g _ w).1 hw, hwU⟩

/-- A continuous map sends the closure of `{x}` to a point if `{f x}` is closed. -/
private theorem map_eq_of_mem_closure_of_isClosed_singleton {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Continuous f) {x p : α} (hp : p ∈ closure ({x} : Set α))
    (hs : IsClosed ({f x} : Set β)) : f p = f x := by
  have := map_mem_closure hf hp (t := ({f x} : Set β)) (Set.mapsTo_singleton.2 rfl)
  rwa [hs.closure_eq] at this

/-! ### Multiplicities along a flat morphism in the wrong degree -/

/-- Along a flat morphism `v : Q ⟶ Y` of relative dimension `r`, the inverse image of the closure
of a point `y` of relative dimension `m` has all its irreducible components of relative dimension
`m + r` (Stacks 02R8), so its cycle in any other degree vanishes. -/
theorem closedSubschemeCycleCoeff_comap_integralComponentAt_eq_zero (C : ChowSituation.{u})
    {Q Y : Scheme.{u}} (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (v : Q ⟶ Y) [LocallyOfFiniteType v] [Flat v] (hbase : v ≫ g = sQ)
    (r : ℕ) (hv : AlgebraicGeometry.RelativeDimension v r) (y : Y) {m k : ℤ}
    (hy : relativeDimension C.dimensionFunction g y = m) (hk : k ≠ m + r) (w : Q) :
    closedSubschemeCycleCoeff C sQ ((integralComponentAt y).comap v).subschemeι k w = 0 := by
  classical
  set I := integralComponentAt y with hI
  have hint : IsIntegral I.subscheme := isIntegral_integralComponentAt y
  unfold closedSubschemeCycleCoeff
  refine dite_eq_right fun ⟨ξ, hξw, hdim⟩ ↦ absurd ?_ hk
  rw [← hdim]
  set e := I.comapIso v with he
  set ξ' : genericPoints (pullback v I.subschemeι : Scheme.{u}) := genericPointsIso e ξ with hξ'
  set W' : irreducibleComponents (pullback v I.subschemeι : Scheme.{u}) :=
    genericPoints.component ξ' with hW'
  have hgen : W'.2.1.genericPoint = ξ'.1 :=
    (W'.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ W'.2)).eq
      (genericPoints.isGenericPoint ξ')
  have hδ := deltaDimension_irreducibleComponent_pullback_snd_comp C g v r hv I.subschemeι W'
  rw [deltaDimension_eq_of_isGenericPoint C _ _ ξ'.1 (genericPoints.isGenericPoint ξ'),
    deltaDimension_eq_of_isGenericPoint C _ _ (genericPoint I.subscheme) (genericPoint_spec _),
    relativeDimension_comp_closedImmersion _ I.subschemeι g,
    show I.subschemeι (genericPoint I.subscheme) = y from
      Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure y, hy] at hδ
  have hcond : pullback.snd v I.subschemeι ≫ I.subschemeι ≫ g =
      pullback.fst v I.subschemeι ≫ sQ := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, hbase]
  rw [hcond, relativeDimension_comp_closedImmersion _ (pullback.fst v I.subschemeι) sQ] at hδ
  have hpt : (pullback.fst v I.subschemeι).base ξ'.1 = w := by
    rw [← hξw, hξ']
    change (pullback.fst v I.subschemeι).base (e.hom.base ξ.1) = _
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.comapIso_hom_fst]
  rwa [hpt] at hδ

/-! ### The summands of the exterior product -/

section Summands

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)

/-- The terms of the exterior product attached to a point `x` vanish off `closure {x} ×_S Y`. -/
theorem exteriorProductDedekindTerm_eq_zero_of_notMem_range (α : CycleGroup C f n)
    (β : CycleGroup C g m) (x : X) (y : Y) {z : (pullback f g : Scheme.{u})}
    (hz : z ∉ Set.range (dedekindPointFibre f g x).subschemeι.base) :
    exteriorProductDedekindTerm C f g n m α β z (x, y) = 0 := by
  by_contra hne
  refine hz ?_
  rw [(dedekindPointFibre f g x).range_subschemeι]
  exact (mem_support_dedekindPointFibre_iff f g x z).2
    (mem_closure_of_exteriorProductDedekindTerm_ne_zero C f g n m α β z (x, y) hne).1

/-- The sum over `y` of the terms attached to `x` vanishes off `closure {x} ×_S Y`. -/
private theorem finsum_exteriorProductDedekindTerm_eq_zero_of_notMem_range (α : CycleGroup C f n)
    (β : CycleGroup C g m) (x : X) {z : (pullback f g : Scheme.{u})}
    (hz : z ∉ Set.range (dedekindPointFibre f g x).subschemeι.base) :
    ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y) = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun y ↦
    exteriorProductDedekindTerm_eq_zero_of_notMem_range C f g n m α β x y hz

/-- The term of the exterior product at `(x, y)` read inside `closure {x} ×_S Y`: when one of the
two points dominates a component of the base it is `α(x) β(y)` times the multiplicity of the
inverse image of `closure {y}` under the projection `v_x : closure {x} ×_S Y ⟶ Y`. -/
theorem exteriorProductDedekindTerm_dedekindPointFibre (α : CycleGroup C f n)
    (β : CycleGroup C g m) (x : X) (y : Y) (w : (dedekindPointFibre f g x).subscheme) :
    exteriorProductDedekindTerm C f g n m α β
        ((dedekindPointFibre f g x).subschemeι.base w) (x, y) =
      open Classical in
      if DominatesBaseComponent C f x ∨ DominatesBaseComponent C g y then
        α.1 x * β.1 y * closedSubschemeCycleCoeff C
          ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
          ((integralComponentAt y).comap
            ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)).subschemeι
          (n + m - 1) w
      else 0 := by
  classical
  unfold exteriorProductDedekindTerm
  split_ifs
  · have hI : (dedekindPointFibre f g x).subschemeι.ker ≤
        (exteriorProductIdeal f g x y).subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι (exteriorProductIdeal f g x y)]
      exact ker_dedekindPointFibre_le f g x y
    have := isIso_pullback_snd_of_ker_le (dedekindPointFibre f g x).subschemeι
      (exteriorProductIdeal f g x y).subschemeι hI
    have hcomp : (((exteriorProductIdeal f g x y).comapIso
          (dedekindPointFibre f g x).subschemeι).trans
          (asIso (pullback.snd (dedekindPointFibre f g x).subschemeι
            (exteriorProductIdeal f g x y).subschemeι))).hom ≫
        (exteriorProductIdeal f g x y).subschemeι =
        ((exteriorProductIdeal f g x y).comap (dedekindPointFibre f g x).subschemeι).subschemeι ≫
          (dedekindPointFibre f g x).subschemeι := by
      change (((exteriorProductIdeal f g x y).comapIso (dedekindPointFibre f g x).subschemeι).hom ≫
        pullback.snd _ _) ≫ _ = _
      rw [Category.assoc, ← pullback.condition, ← Category.assoc,
        Scheme.IdealSheafData.comapIso_hom_fst]
    rw [← closedSubschemeCycleCoeff_eq_of_iso C (pullback.fst f g ≫ f) _ _ _ hcomp,
      closedSubschemeCycleCoeff_comp_isClosedImmersion C _ (pullback.fst f g ≫ f)
        (dedekindPointFibre f g x).subschemeι rfl,
      comap_exteriorProductIdeal_dedekindPointFibre]
    rfl
  · rfl

/-- On a dominating point the sum over `y` of the terms of the exterior product is the flat
pullback of `α(x) β` along the flat projection `v_x`, read in degree `m + r`, provided that
degree is `n + m - 1`; in any other degree it vanishes. -/
theorem finsum_exteriorProductDedekindTerm_of_flat (α : CycleGroup C f n)
    (β : CycleGroup C g m) (x : X) (hdom : DominatesBaseComponent C f x)
    [LocallyOfFiniteType ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)]
    [Flat ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension
      ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g) r)
    (w : (dedekindPointFibre f g x).subscheme) :
    ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β
        ((dedekindPointFibre f g x).subschemeι.base w) (x, y) =
      open Classical in
      if m + (r : ℤ) = n + m - 1 then
        α.1 x * β.1 (((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g).base w) *
          flatPullbackWeight C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
            ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g) (n + m - 1) w
      else 0 := by
  classical
  set v := (dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g with hv
  have hbase : v ≫ g = (dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f) := by
    rw [hv, Category.assoc, ← pullback.condition]
  simp_rw [exteriorProductDedekindTerm_dedekindPointFibre, ite_eq_left (Or.inl hdom)]
  split_ifs with hdeg
  · have key : ∀ y, β.1 y ≠ 0 →
        closedSubschemeCycleCoeff C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
          ((integralComponentAt y).comap v).subschemeι (n + m - 1) w =
        closedSubschemeCycleCoeff C g (integralComponentAt y).subschemeι m (v.base w) *
          flatPullbackWeight C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f)) v
            (n + m - 1) w := fun y hβ ↦ by
      have hy := (mem_cyclesOfDimension_iff_forall_point C g m β.1).1 β.2 y hβ
      rw [← hdeg, closedSubschemeCycleCoeff_comap C _ g v hbase r hr (integralComponentAt _) m
        (le_of_eq (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C g _ hy))]
    rw [finsum_eq_single _ (v.base w)]
    · by_cases hβ : β.1 (v.base w) = 0
      · rw [hβ, mul_zero, zero_mul, zero_mul]
      have hy := (mem_cyclesOfDimension_iff_forall_point C g m β.1).1 β.2 (v.base w) hβ
      rw [key _ hβ]
      have h1 := cycleAssociatedToClosedSubscheme_integralComponentAt_self C g (v.base w)
        (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C g _ hy)
      change closedSubschemeCycleCoeff C g (integralComponentAt (v.base w)).subschemeι m
        (v.base w) = 1 at h1
      rw [h1, one_mul]
    · intro y hy
      by_cases hβ : β.1 y = 0
      · rw [hβ, mul_zero, zero_mul]
      rw [key _ hβ]
      have h0 := cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C g m y
        (Ne.symm hy)
      change closedSubschemeCycleCoeff C g (integralComponentAt y).subschemeι m (v.base w) = 0
        at h0
      rw [h0, zero_mul, mul_zero]
  · refine finsum_eq_zero_of_forall_eq_zero fun y ↦ ?_
    by_cases hβ : β.1 y = 0
    · rw [hβ, mul_zero, zero_mul]
    have hyd := (mem_cyclesOfDimension_iff_forall_point C g m β.1).1 β.2 y hβ
    rw [closedSubschemeCycleCoeff_comap_integralComponentAt_eq_zero C _ g v hbase r hr y hyd
      (Ne.symm hdeg), mul_zero]

omit [LocallyOfFiniteType g] in
/-- The flat projection `closure {x} ×_S Y ⟶ Y` attached to a dominating point, with its
relative dimension and the identity `n = δ(f x) + r`. -/
theorem exists_relativeDimension_dedekindPointFibre (hC : IsDedekindChowBase C)
    (x : X) (hdom : DominatesBaseComponent C f x) :
    ∃ (_ : Flat ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)) (r : ℕ),
      AlgebraicGeometry.RelativeDimension
        ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g) r ∧
      relativeDimension C.dimensionFunction f x = C.dimensionFunction (f.base x) + r := by
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hint : IsIntegral I.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  have hη : I.subschemeι.base (genericPoint I.subscheme) = x :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x
  have hqη : (I.subschemeι ≫ f).base (genericPoint I.subscheme) = f.base x := by
    rw [Scheme.Hom.comp_apply, hη]
  have hflat : Flat (I.subschemeι ≫ f) :=
    hC.flat_of_mem_irreducibleComponents (I.subschemeι ≫ f) (by rw [hqη]; exact hdom)
  have hrel := relativeDimension_of_irreducibleSpace (I.subschemeι ≫ f)
    (fun _ ↦ ⟨inferInstance, hC.ringKrullDim_stalk_le_one _⟩)
  have hsq := isPullback_dedekindPointFibre f g x
  refine ⟨Flat.isStableUnderBaseChange.of_isPullback hsq hflat, _,
    RelativeDimension.of_isPullback hsq hrel, ?_⟩
  have h1 : relativeDimension C.dimensionFunction (I.subschemeι ≫ f) (genericPoint I.subscheme) =
      relativeDimension C.dimensionFunction f x := by
    rw [relativeDimension_comp_closedImmersion, hη]
  rw [← h1, ← hqη]
  rfl

/-- **The summand of a dominating point, for an arbitrary cycle.** If `closure {x}` dominates an
irreducible component of the base, the terms of `α × β` attached to `x` are the pushforward along
`ι_x : closure {x} ×_S Y ⟶ X ×_S Y` of the flat pullback of `α(x) β` along the flat projection
`v_x : closure {x} ×_S Y ⟶ Y`, read in degree `n + m - 1`. -/
theorem properPushforward_flatPullback_of_dominates (α : CycleGroup C f n)
    (β : CycleGroup C g m) (x : X) (hdom : DominatesBaseComponent C f x)
    [LocallyOfFiniteType ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)]
    [Flat ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension
      ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g) r)
    (hdeg : m + (r : ℤ) = n + m - 1)
    (a : CycleGroup C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
      (n + m - 1))
    (ha : a.1 = (flatPullback C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
      g ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)
      (by rw [Category.assoc, ← pullback.condition]) r hr m (α.1 x • β)).1)
    (z : (pullback f g : Scheme.{u})) :
    (properPushforward C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
        (pullback.fst f g ≫ f) (dedekindPointFibre f g x).subschemeι rfl (n + m - 1) a).1 z =
      ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y) := by
  classical
  set K := dedekindPointFibre f g x with hK
  set v := K.subschemeι ≫ pullback.snd f g with hv
  by_cases hz : z ∈ Set.range K.subschemeι.base
  · obtain ⟨w, rfl⟩ := hz
    rw [properPushforward_apply_image_of_isClosedImmersion, ha,
      flatPullback_apply, finsum_exteriorProductDedekindTerm_of_flat C f g n m α β x hdom r
        hr w, ite_eq_left hdeg, hdeg]
    have hsmul : (α.1 x • β : CycleGroup C g m).1 (v.base w) = α.1 x * β.1 (v.base w) := by
      simp
    rw [hsmul]
  · rw [properPushforward_apply_of_notMem_range C _ _ _ rfl _ _ hz]
    exact (finsum_exteriorProductDedekindTerm_eq_zero_of_notMem_range C f g n m α β x hz).symm

/-- **The summand of a dominating point.** If `closure {x}` dominates an irreducible component
of the base and `β` is rationally equivalent to zero, the terms of `α × β` attached to `x` are
the pushforward along `closure {x} ×_S Y ⟶ X ×_S Y` of a cycle rationally equivalent to zero. -/
theorem exists_dedekindSummand_of_dominates (hC : IsDedekindChowBase C) (α : CycleGroup C f n)
    {β : CycleGroup C g m} (hβ : β ∈ rationalEquivalences C g m) (x : X) (_hx : α.1 x ≠ 0)
    (hdom : DominatesBaseComponent C f x) :
    ∃ a : CycleGroup C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
        (n + m - 1),
      a ∈ rationalEquivalences C
          ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m - 1) ∧
        ∀ z : (pullback f g : Scheme.{u}),
          (properPushforward C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
            (pullback.fst f g ≫ f) (dedekindPointFibre f g x).subschemeι rfl (n + m - 1) a).1 z =
            ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y) := by
  classical
  obtain ⟨hflat, r, hrv, -⟩ := exists_relativeDimension_dedekindPointFibre C f g hC x hdom
  set K := dedekindPointFibre f g x with hK
  set v := K.subschemeι ≫ pullback.snd f g with hv
  have hbase : v ≫ g = K.subschemeι ≫ (pullback.fst f g ≫ f) := by
    rw [hv, Category.assoc, ← pullback.condition]
  by_cases hdeg : m + (r : ℤ) = n + m - 1
  · refine ⟨hdeg ▸ flatPullback C (K.subschemeι ≫ (pullback.fst f g ≫ f)) g v hbase r hrv m
      (α.1 x • β), ?_, properPushforward_flatPullback_of_dominates C f g n m α β x hdom r hrv
        hdeg _ (val_cycleGroup_cast C _ hdeg _)⟩
    exact mem_rationalEquivalences_cast C _ hdeg
      (flatPullbackFactorsThroughRationalEquivalence_general C _ g v hbase r hrv m _
        ((rationalEquivalences C g m).zsmul_mem hβ (α.1 x)))
  · refine ⟨0, (rationalEquivalences C _ _).zero_mem, fun z ↦ ?_⟩
    rw [properPushforward_zero]
    by_cases hz : z ∈ Set.range K.subschemeι.base
    · obtain ⟨w, rfl⟩ := hz
      rw [finsum_exteriorProductDedekindTerm_of_flat C f g n m α β x hdom r hrv w,
        ite_eq_right hdeg]
      rfl
    · rw [finsum_exteriorProductDedekindTerm_eq_zero_of_notMem_range C f g n m α β x hz]
      rfl

/-- The local rings of the reduced closed subscheme on a closed point are fields. -/
theorem isField_stalk_of_eq_vanishingIdeal_singleton {T : Scheme.{u}} {s : T}
    (hs : IsClosed ({s} : Set T)) (I : T.IdealSheafData)
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (⟨{s}, hs⟩ : Closeds T)) (t : I.subscheme) :
    IsField (I.subscheme.presheaf.stalk t) := by
  subst hI
  have hsub : Subsingleton (Scheme.IdealSheafData.vanishingIdeal
      (⟨{s}, hs⟩ : Closeds T)).subscheme := subsingleton_subscheme_vanishingIdeal hs
  have hne : Nonempty (Scheme.IdealSheafData.vanishingIdeal
      (⟨{s}, hs⟩ : Closeds T)).subscheme := nonempty_subscheme_vanishingIdeal hs
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal
      (⟨{s}, hs⟩ : Closeds T)).subscheme :=
    { isPreirreducible_univ := Set.subsingleton_of_subsingleton.isPreirreducible
      toNonempty := hne }
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal (⟨{s}, hs⟩ : Closeds T)).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (⟨{s}, hs⟩ : Closeds T)).subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  obtain rfl : t = genericPoint _ := Subsingleton.elim _ _
  exact (inferInstance : Field (Scheme.IdealSheafData.vanishingIdeal
    (⟨{s}, hs⟩ : Closeds T)).subscheme.functionField).toIsField

/-- A coefficient of the inverse image of `closure {y}` inside `closure {x} ×_S Y` is nonzero only
at points lying over `closure {x}` and over `closure {y}`. -/
theorem mem_closure_of_closedSubschemeCycleCoeff_ne_zero (x : X) (y : Y) (k : ℤ)
    (w : (dedekindPointFibre f g x).subscheme)
    (hw : closedSubschemeCycleCoeff C
      ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
      ((integralComponentAt y).comap
        ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)).subschemeι k w ≠ 0) :
    (pullback.fst f g).base ((dedekindPointFibre f g x).subschemeι.base w) ∈
        closure ({x} : Set X) ∧
      (pullback.snd f g).base ((dedekindPointFibre f g x).subschemeι.base w) ∈
        closure ({y} : Set Y) := by
  classical
  have hrange : w ∈ Set.range ((integralComponentAt y).comap
      ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)).subschemeι.base := by
    unfold closedSubschemeCycleCoeff at hw
    split_ifs at hw with h
    · obtain ⟨ξ, hξ⟩ := h
      exact ⟨ξ.1, hξ.1⟩
    · exact absurd rfl hw
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap] at hrange
  have h2 : ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g).base w ∈
      closure ({y} : Set Y) := by
    simpa [coe_support_integralComponentAt] using hrange
  refine ⟨?_, by simpa using h2⟩
  refine (mem_support_dedekindPointFibre_iff f g x _).1 ?_
  rw [← (dedekindPointFibre f g x).range_subschemeι]
  exact Set.mem_range_self w

/-- The inverse image `DY` of a closed subscheme `DS` of the base is the fibre product of `DS`
with `Y`. -/
theorem isPullback_subschemeMap_of_eq_comap {S : Scheme.{u}} (g : Y ⟶ S)
    (DS : S.IdealSheafData) (DY : Y.IdealSheafData) (hDY : DY = DS.comap g) :
    IsPullback DY.subschemeι (Scheme.IdealSheafData.subschemeMap DY DS g
      (Scheme.IdealSheafData.le_map_iff_comap_le.2 (le_of_eq hDY.symm))) g DS.subschemeι :=
  AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ g
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, hDY])

omit [LocallyOfFiniteType g] in
/-- **The projection to the fibre over a closed point.** If `closure {x}` lies over a closed point
`s` of the base which is not the generic point of a component, and `DY ⊆ Y` is the inverse image
of `s`, the projection `closure {x} ×_S Y ⟶ Y` factors through a flat morphism
`closure {x} ×_S Y ⟶ DY` of relative dimension `n`, the base change of `closure {x} ⟶ s`. -/
theorem exists_flat_dedekindPointFibre_fibre (hC : IsDedekindChowBase C)
    (x : X) (hnd : ¬ DominatesBaseComponent C f x) (L : C.S.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible C.S.sheaf.obj C.S.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) (hσ : Stacks.Divisors.zeroScheme C.S L σ =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨{f.base x}, hC.isClosed_singleton hnd⟩ : Closeds C.S))
    (α : CycleGroup C f n) (hx : α.1 x ≠ 0) (DY : Y.IdealSheafData)
    (hDY : DY = (Stacks.Divisors.zeroScheme C.S L σ).comap g) :
    ∃ (w : (dedekindPointFibre f g x).subscheme ⟶ DY.subscheme) (_ : LocallyOfFiniteType w)
      (_ : Flat w) (r : ℕ),
      w ≫ DY.subschemeι = (dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g ∧
        AlgebraicGeometry.RelativeDimension w r ∧ (r : ℤ) = n := by
  classical
  have hs : closure ({f.base x} : Set C.S) ∉ irreducibleComponents C.S := hnd
  have hscl := hC.isClosed_singleton hs
  set DS := Stacks.Divisors.zeroScheme C.S L σ with hDS
  have tsq := isPullback_subschemeMap_of_eq_comap g DS DY hDY
  set πD := Scheme.IdealSheafData.subschemeMap DY DS g
    (Scheme.IdealSheafData.le_map_iff_comap_le.2 (le_of_eq hDY.symm)) with hπD
  have hDSsupp : (DS.support : Set C.S) = {f.base x} := by
    rw [hσ, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hint : IsIntegral I.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  have hη : I.subschemeι.base (genericPoint I.subscheme) = x :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x
  have hker : DS.subschemeι.ker ≤ (I.subschemeι ≫ f).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hσ,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    change closure (Set.range (I.subschemeι ≫ f).base) ⊆ {f.base x}
    refine closure_minimal ?_ hscl
    rintro _ ⟨t, rfl⟩
    have ht : I.subschemeι.base t ∈ closure ({x} : Set X) := by
      have := Set.mem_range_self (f := I.subschemeι.base) t
      rwa [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    exact map_eq_of_mem_closure_of_isClosed_singleton f.continuous ht hscl
  set a := IsClosedImmersion.lift DS.subschemeι (I.subschemeι ≫ f) hker with hadef
  have ha : a ≫ DS.subschemeι = I.subschemeι ≫ f := IsClosedImmersion.lift_fac _ _ _
  have hDSfield : ∀ t : DS.subscheme, IsField (DS.subscheme.presheaf.stalk t) :=
    isField_stalk_of_eq_vanishingIdeal_singleton hscl DS hσ
  have haflat : Flat a := flat_of_isField_stalk a hDSfield
  have halft : LocallyOfFiniteType a := by
    have : LocallyOfFiniteType (a ≫ DS.subschemeι) := by rw [ha]; infer_instance
    exact locallyOfFiniteType_of_comp a DS.subschemeι
  have harel := relativeDimension_of_irreducibleSpace a fun t ↦ by
    let _ := (hDSfield (a.base t)).toField
    refine ⟨inferInstance, ?_⟩
    rw [ringKrullDim_eq_zero_of_field]
    exact zero_le_one
  set r := Cardinal.toNat (residueTrdeg a (genericPoint I.subscheme)) with hr
  have hn := (mem_cyclesOfDimension_iff_forall_point C f n α.1).1 α.2 x hx
  have hrn : (r : ℤ) = n := by
    have h1 : relativeDimension C.dimensionFunction (a ≫ DS.subschemeι ≫ 𝟙 C.S)
        (genericPoint I.subscheme) = relativeDimension C.dimensionFunction f x := by
      rw [Category.comp_id, ha, relativeDimension_comp_closedImmersion, hη]
    rw [relativeDimension_comp_eq_add_trdeg, relativeDimension_comp_closedImmersion,
      relativeDimension_id] at h1
    have hpt : DS.subschemeι.base (a.base (genericPoint I.subscheme)) = f.base x := by
      have := Set.mem_range_self (f := DS.subschemeι.base) (a.base (genericPoint I.subscheme))
      rwa [DS.range_subschemeι, hDSsupp, Set.mem_singleton_iff] at this
    rwa [hpt, hC.2.1 _ hscl, zero_add, hn] at h1
  set K := dedekindPointFibre f g x with hK
  have hsq := isPullback_dedekindPointFibre f g x
  set e := (pointClosureFibreIso f g x).hom ≫ pullback.fst (I.subschemeι ≫ f) g with he
  set w := tsq.lift (K.subschemeι ≫ pullback.snd f g) (e ≫ a)
    (by simp only [Category.assoc, ha]; simpa using hsq.w.symm) with hwdef
  have hw1 : w ≫ DY.subschemeι = K.subschemeι ≫ pullback.snd f g := tsq.lift_fst _ _ _
  have hw2 : w ≫ πD = e ≫ a := tsq.lift_snd _ _ _
  have hleft : IsPullback w e (πD) a :=
    IsPullback.of_right (by rw [hw1, ha]; exact hsq.flip) hw2 tsq
  have hwflat : Flat w := Flat.isStableUnderBaseChange.of_isPullback hleft.flip haflat
  have hwrel := RelativeDimension.of_isPullback hleft.flip harel
  have hwlft : LocallyOfFiniteType w := MorphismProperty.of_isPullback hleft.flip inferInstance
  exact ⟨w, hwlft, hwflat, r, hw1, hwrel, hrn⟩

/-- **The summand of a point over a closed point, for an arbitrary cycle.** If `closure {x}` lies
over a closed point `s` of the base which is not the generic point of a component, the terms of
`α × β` attached to `x` are the pushforward along `closure {x} ×_S Y ⟶ X ×_S Y` of the flat
pullback, along a flat projection `w : closure {x} ×_S Y ⟶ Y_s`, of the Gysin image in the fibre
`Y_s` of `α(x) β` (Stacks 0B6Z). The fibre is presented as the zero scheme of a section of an
invertible module on `Y` restricting trivially to it, whose ideal is the inverse image of `s`. -/
theorem properPushforward_flatPullback_gysin_of_not_dominates (hC : IsDedekindChowBase C)
    (x : X) (hnd : ¬ DominatesBaseComponent C f x) (L : C.S.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible C.S.sheaf.obj C.S.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) (hσ : Stacks.Divisors.zeroScheme C.S L σ =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨{f.base x}, hC.isClosed_singleton hnd⟩ : Closeds C.S))
    (α : CycleGroup C f n) (β : CycleGroup C g m) (LY : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property LY]
    (σY : Γ(LY, ⊤))
    (htrivY : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme Y LY σY).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme Y LY σY).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y LY σY).subschemeι).obj LY))
    (hDY : Stacks.Divisors.zeroScheme Y LY σY = (Stacks.Divisors.zeroScheme C.S L σ).comap g)
    (w : (dedekindPointFibre f g x).subscheme ⟶ (Stacks.Divisors.zeroScheme Y LY σY).subscheme)
    [LocallyOfFiniteType w] [Flat w]
    (hw : w ≫ (Stacks.Divisors.zeroScheme Y LY σY).subschemeι =
      (dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)
    (r : ℕ) (hwrel : AlgebraicGeometry.RelativeDimension w r)
    (hdeg : m - 1 + (r : ℤ) = n + m - 1) (β' : CycleGroup C g (m - 1 + 1)) (hβ' : β'.1 = β.1)
    (a : CycleGroup C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
      (n + m - 1))
    (ha : a.1 = (flatPullback C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
      ((Stacks.Divisors.zeroScheme Y LY σY).subschemeι ≫ g) w
      (by rw [← Category.assoc, hw, Category.assoc, ← pullback.condition]) r hwrel (m - 1)
      (α.1 x • gysinCycleMap C g (m - 1) LY σY htrivY β')).1)
    (z : (pullback f g : Scheme.{u})) :
    (properPushforward C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
        (pullback.fst f g ≫ f) (dedekindPointFibre f g x).subschemeι rfl (n + m - 1) a).1 z =
      ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y) := by
  classical
  have hs : closure ({f.base x} : Set C.S) ∉ irreducibleComponents C.S := hnd
  have hscl := hC.isClosed_singleton hs
  set DS := Stacks.Divisors.zeroScheme C.S L σ with hDS
  have hDSsupp : (DS.support : Set C.S) = {f.base x} := by
    rw [hσ, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hDYsupp : ∀ y : Y, y ∈ ((Stacks.Divisors.zeroScheme Y LY σY).support : Set Y) ↔ g.base y =
      f.base x := by
    intro y
    rw [hDY, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      hDSsupp, Set.mem_singleton_iff]
  have hbase : w ≫ ((Stacks.Divisors.zeroScheme Y LY σY).subschemeι ≫ g) = (dedekindPointFibre f g
      x).subschemeι ≫ (pullback.fst f g ≫ f) := by
    rw [← Category.assoc, hw, Category.assoc, ← pullback.condition]
  have hβ'pt : ∀ y : Y, β'.1 y = β.1 y := fun y ↦ by rw [hβ']
  set Φ := gysinCycleMap C g (m - 1) LY σY htrivY β' with hΦ
  by_cases hz : z ∈ Set.range (dedekindPointFibre f g x).subschemeι.base
  swap
  · rw [properPushforward_apply_of_notMem_range C _ _ _ rfl _ _ hz,
      finsum_exteriorProductDedekindTerm_eq_zero_of_notMem_range C f g n m α β x hz]
  obtain ⟨v', rfl⟩ := hz
  rw [properPushforward_apply_image_of_isClosedImmersion, ha, flatPullback_apply]
  have hpres := isGysinCycleMap_gysinCycleMap C g (m - 1) LY σY htrivY
    (fun y : cycleSupportIndex β' ↦ integralComponentAt y.1)
    (fun y ↦ isIntegral_integralComponentAt y.1) (schemeDeltaDimension_cycleSupportIndex β')
    (locallyFinite_support_integralComponentAt β') (fun y ↦ β'.1 y.1) β'
    (cycle_eq_finsum_primeCycles β') (w.base v')
  have hsmul : (α.1 x • Φ : CycleGroup C ((Stacks.Divisors.zeroScheme Y LY σY).subschemeι ≫ g) (m -
      1)).1 (w.base v') =
      α.1 x * Φ.1 (w.base v') := by simp
  rw [hsmul, hpres, mul_finsum, finsum_mul]
  have hsupp : ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β
        ((dedekindPointFibre f g x).subschemeι.base v') (x, y) =
      ∑ᶠ y : cycleSupportIndex β', exteriorProductDedekindTerm C f g n m α β
        ((dedekindPointFibre f g x).subschemeι.base v') (x, y.1) := by
    refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond (fun y : Y ↦ β'.1 y ≠ 0)
      (f := fun y ↦ exteriorProductDedekindTerm C f g n m α β ((dedekindPointFibre f g
          x).subschemeι.base v') (x, y))).symm
    refine finsum_congr fun y ↦ ?_
    by_cases hy : β'.1 y = 0
    · rw [finsum_eq_if, ite_eq_right (not_not.2 hy)]
      have hy' : β.1 y = 0 := by rwa [hβ'pt] at hy
      unfold exteriorProductDedekindTerm
      split_ifs <;> simp [hy']
    · rw [finsum_eq_if, ite_eq_left hy]
  rw [hsupp]
  refine finsum_congr fun y ↦ ?_
  have hy : β.1 y.1 ≠ 0 := by rw [← hβ'pt]; exact y.2
  have hyd : relativeDimension C.dimensionFunction g y.1 = m :=
    (mem_cyclesOfDimension_iff_forall_point C g m β.1).1 β.2 y.1 hy
  rw [exteriorProductDedekindTerm_dedekindPointFibre, hβ'pt y.1]
  by_cases hle : (Stacks.Divisors.zeroScheme Y LY σY) ≤ integralComponentAt y.1
  · rw [gysinCycleMapComponent_of_le C g (m - 1) _ _ _ _ _ hle]
    have hgy : g.base y.1 = f.base x :=
      (hDYsupp y.1).1 ((le_integralComponentAt_iff_mem_support (Stacks.Divisors.zeroScheme Y LY σY)
          y.1).1 hle)
    have hndy : ¬ DominatesBaseComponent C g y.1 := by
      unfold DominatesBaseComponent; rw [hgy]; exact hs
    rw [ite_eq_right (by tauto)]
    simp
  · rw [gysinCycleMapComponent_of_not_le C g (m - 1) _ _ _ _ _ hle]
    obtain ⟨dY, hdY⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
      C.dimensionFunction g
    have hdimJ : schemeDeltaDimension C (((integralComponentAt y.1).comap
        (Stacks.Divisors.zeroScheme Y LY σY).subschemeι).subschemeι ≫ (Stacks.Divisors.zeroScheme Y
            LY σY).subschemeι ≫ g) ≤ ((m - 1 : ℤ) : EInt) := by
      refine schemeDeltaDimension_le_of_forall_relativeDimension_le C ((Stacks.Divisors.zeroScheme
          Y LY σY).subschemeι ≫ g) _
        fun t ↦ ?_
      set t' := ((integralComponentAt y.1).comap (Stacks.Divisors.zeroScheme Y LY
          σY).subschemeι).subschemeι.base t
      have ht'1 : (Stacks.Divisors.zeroScheme Y LY σY).subschemeι.base t' ∈ closure ({y.1} : Set Y)
          := by
        have := Set.mem_range_self (f := ((integralComponentAt y.1).comap
          (Stacks.Divisors.zeroScheme Y LY σY).subschemeι).subschemeι.base) t
        rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
          Closeds.coe_preimage, coe_support_integralComponentAt] at this
      have ht'2 : (Stacks.Divisors.zeroScheme Y LY σY).subschemeι.base t' ∈
          ((Stacks.Divisors.zeroScheme Y LY σY).support : Set Y) := by
        rw [← (Stacks.Divisors.zeroScheme Y LY σY).range_subschemeι]; exact Set.mem_range_self _
      have hyne : (Stacks.Divisors.zeroScheme Y LY σY).subschemeι.base t' ≠ y.1 := by
        intro h
        refine hle ((le_integralComponentAt_iff_mem_support (Stacks.Divisors.zeroScheme Y LY σY)
            y.1).2 ?_)
        rw [← h]; exact ht'2
      have hlt := dY.strictAnti_specializes (specializes_iff_mem_closure.mpr ht'1) hyne.symm
      rw [hdY, hdY, hyd] at hlt
      rw [relativeDimension_comp_closedImmersion]
      omega
    have hcoeff := closedSubschemeCycleCoeff_comap C ((dedekindPointFibre f g x).subschemeι ≫
        (pullback.fst f g ≫ f))
      ((Stacks.Divisors.zeroScheme Y LY σY).subschemeι ≫ g) w hbase r hwrel ((integralComponentAt
          y.1).comap (Stacks.Divisors.zeroScheme Y LY σY).subschemeι)
      (m - 1) hdimJ v'
    rw [← Scheme.IdealSheafData.comap_comp, hw, hdeg] at hcoeff
    change α.1 x * (β.1 y.1 * closedSubschemeCycleCoeff C ((Stacks.Divisors.zeroScheme Y LY
        σY).subschemeι ≫ g)
      ((integralComponentAt y.1).comap (Stacks.Divisors.zeroScheme Y LY σY).subschemeι).subschemeι
          (m - 1) (w.base v')) *
        flatPullbackWeight C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f)) w (m
            - 1 + r) v' = _
    rw [hdeg, mul_assoc, mul_assoc, ← hcoeff, ← mul_assoc]
    split_ifs with hguard
    · rfl
    · by_contra hne
      have hne' := right_ne_zero_of_mul hne
      obtain ⟨h1, h2⟩ := mem_closure_of_closedSubschemeCycleCoeff_ne_zero C f g x y.1
        (n + m - 1) v' hne'
      have hndy : ¬ DominatesBaseComponent C g y.1 := fun h ↦ hguard (Or.inr h)
      have hgycl := hC.isClosed_singleton hndy
      have hfx := map_eq_of_mem_closure_of_isClosed_singleton f.continuous h1 hscl
      have hgy := map_eq_of_mem_closure_of_isClosed_singleton g.continuous h2 hgycl
      have hcomm : f.base ((pullback.fst f g).base ((dedekindPointFibre f g x).subschemeι.base v'))
          =
          g.base ((pullback.snd f g).base ((dedekindPointFibre f g x).subschemeι.base v')) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
        rfl
      refine hle ((le_integralComponentAt_iff_mem_support (Stacks.Divisors.zeroScheme Y LY σY)
          y.1).2 ((hDYsupp y.1).2 ?_))
      rw [← hgy, ← hcomm, hfx]

/-- **The summand of a point over a closed point.** If `closure {x}` lies over a closed point `s`
of the base which is not the generic point of a component and `β` is rationally equivalent to
zero, the terms of `α × β` attached to `x` are the pushforward along
`closure {x} ×_S Y ⟶ X ×_S Y` of a cycle rationally equivalent to zero. -/
theorem exists_dedekindSummand_of_not_dominates (hC : IsDedekindChowBase C)
    (α : CycleGroup C f n) {β : CycleGroup C g m} (hβ : β ∈ rationalEquivalences C g m) (x : X)
    (hx : α.1 x ≠ 0) (hnd : ¬ DominatesBaseComponent C f x) :
    ∃ a : CycleGroup C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
        (n + m - 1),
      a ∈ rationalEquivalences C
          ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m - 1) ∧
        ∀ z : (pullback f g : Scheme.{u}),
          (properPushforward C ((dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
            (pullback.fst f g ≫ f) (dedekindPointFibre f g x).subschemeι rfl (n + m - 1) a).1 z =
            ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y) := by
  classical
  have hs : closure ({f.base x} : Set C.S) ∉ irreducibleComponents C.S := hnd
  obtain ⟨L, hLinv, σ, hσ, htriv⟩ := hC.exists_section_zeroScheme_eq hs
  have htrivY := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections g L σ htriv
  have hDY := Stacks.Divisors.zeroScheme_pullback g L σ
  obtain ⟨w, hwlft, hwflat, r, hw, hwrel, hrn⟩ := exists_flat_dedekindPointFibre_fibre C f g n hC
    x hnd L σ hσ α hx _ hDY
  have hdeg : m - 1 + (r : ℤ) = n + m - 1 := by rw [hrn]; ring
  have hm : m - 1 + 1 = m := Int.sub_add_cancel m 1
  have hbase : w ≫ ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback g).obj L)
      (AlgebraicGeometry.pullbackGlobalSections g L σ)).subschemeι ≫ g) =
      (dedekindPointFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f) := by
    rw [← Category.assoc, hw, Category.assoc, ← pullback.condition]
  have hΦmem := gysinCycleMap_mem_rationalEquivalences C g (m - 1) _ _ htrivY
    (mem_rationalEquivalences_cast C g hm.symm hβ)
  refine ⟨_, ?_, properPushforward_flatPullback_gysin_of_not_dominates C f g n m hC x hnd L σ hσ
    α β _ _ htrivY hDY w hw r hwrel hdeg _ (val_cycleGroup_cast C g hm.symm β) _
    (val_cycleGroup_cast C _ hdeg _)⟩
  exact mem_rationalEquivalences_cast C _ hdeg
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ w hbase r hwrel (m - 1) _
      ((rationalEquivalences C _ _).zsmul_mem hΦmem (α.1 x)))

end Summands

/-! ### Descent in each variable -/

section Descent

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)

/-- **The exterior product as a locally finite sum of summands.** If, for every point `x` of the
support of `α`, the terms of `α × β` attached to `x` are the pushforward along
`closure {x} ×_S Y ⟶ X ×_S Y` of a cycle `a x`, then `α × β` is the locally finite sum of these
pushforwards. -/
theorem exteriorProductDedekindCycles_apply_eq_finsum (α : CycleGroup C f n)
    (β : CycleGroup C g m) (a : ∀ x : α.1.support, CycleGroup C
      ((dedekindPointFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m - 1))
    (ha : ∀ (x : α.1.support) (z : (pullback f g : Scheme.{u})),
      (properPushforward C ((dedekindPointFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f))
        (pullback.fst f g ≫ f) (dedekindPointFibre f g x.1).subschemeι rfl (n + m - 1)
          (a x)).1 z =
        ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x.1, y))
    (z : (pullback f g : Scheme.{u})) :
    (exteriorProductDedekindCycles C f g n m α β).1 z =
      ∑ᶠ x : α.1.support, (properPushforward C
        ((dedekindPointFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f))
        (pullback.fst f g ≫ f) (dedekindPointFibre f g x.1).subschemeι rfl (n + m - 1)
          (a x)).1 z := by
  classical
  simp_rw [ha]
  rw [exteriorProductDedekindCycles_apply,
    finsum_curry _ (exteriorProductDedekindTerm_support_finite C f g n m α β z)]
  refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond (fun x : X ↦ x ∈ α.1.support)
    (f := fun x ↦ ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x, y))).symm
  refine finsum_congr fun x ↦ ?_
  by_cases hx : x ∈ α.1.support
  · rw [finsum_eq_if, ite_eq_left hx]
  · rw [finsum_eq_if, ite_eq_right hx]
    refine finsum_eq_zero_of_forall_eq_zero fun y ↦ ?_
    have hx0 : α.1 x = 0 := by simpa using hx
    unfold exteriorProductDedekindTerm
    split_ifs <;> simp [hx0]

/-- **Stacks 0FC4, the second variable.** Over a base as in Stacks section 42.63, the exterior
product of an `n`-cycle on `X` with an `m`-cycle on `Y` rationally equivalent to zero is
rationally equivalent to zero. -/
theorem exteriorProductDedekindCycles_mem_rationalEquivalences_right
    (hC : IsDedekindChowBase C) (α : CycleGroup C f n) {β : CycleGroup C g m}
    (hβ : β ∈ rationalEquivalences C g m) :
    exteriorProductDedekindCycles C f g n m α β ∈
      rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1) := by
  classical
  have ha : ∀ x : α.1.support, ∃ a : CycleGroup C
      ((dedekindPointFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m - 1),
      a ∈ rationalEquivalences C
          ((dedekindPointFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m - 1) ∧
        ∀ z : (pullback f g : Scheme.{u}),
          (properPushforward C ((dedekindPointFibre f g x.1).subschemeι ≫
            (pullback.fst f g ≫ f)) (pullback.fst f g ≫ f) (dedekindPointFibre f g x.1).subschemeι
            rfl (n + m - 1) a).1 z =
            ∑ᶠ y : Y, exteriorProductDedekindTerm C f g n m α β z (x.1, y) := fun x ↦ by
    by_cases hdom : DominatesBaseComponent C f x.1
    · exact exists_dedekindSummand_of_dominates C f g n m hC α hβ x.1 x.2 hdom
    · exact exists_dedekindSummand_of_not_dominates C f g n m hC α hβ x.1 x.2 hdom
  choose a hamem hapush using ha
  exact rationallyEquivalentToZero_finsum_of_closedSupports C (pullback.fst f g ≫ f)
    (n + m - 1) (fun x : α.1.support ↦ dedekindPointFibre f g x.1)
    (locallyFinite_dedekindPointFibre f g α.1) a (fun x ↦ hamem x)
    (exteriorProductDedekindCycles_apply_eq_finsum C f g n m α β a hapush)

/-- The coefficient of a closed subscheme is unchanged by an isomorphism of the ambient scheme
over the base. -/
private alias closedSubschemeCycleCoeff_comap_of_isIso' :=
  closedSubschemeCycleCoeff_comap_of_isIso

/-- **Symmetry of the exterior product over a Dedekind base.** The coefficient of `α × β` at a
point of `X ×_S Y` is the coefficient of `β × α` at the corresponding point of `Y ×_S X`. -/
theorem exteriorProductDedekindCycles_pullbackSymmetry (α : CycleGroup C f n)
    (β : CycleGroup C g m) (w : (pullback g f : Scheme.{u})) :
    (exteriorProductDedekindCycles C f g n m α β).1 ((pullbackSymmetry f g).inv.base w) =
      (exteriorProductDedekindCycles C g f m n β α).1 w := by
  classical
  set e : (pullback f g : Scheme.{u}) ≅ (pullback g f : Scheme.{u}) := pullbackSymmetry f g
    with he
  have hbase : e.inv ≫ (pullback.fst f g ≫ f) = pullback.fst g f ≫ g := by
    rw [← Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.condition]
  rw [exteriorProductDedekindCycles_apply, exteriorProductDedekindCycles_apply,
    ← finsum_comp_equiv (Equiv.prodComm Y X)]
  refine finsum_congr fun q ↦ ?_
  obtain ⟨y, x⟩ := q
  change exteriorProductDedekindTerm C f g n m α β (e.inv.base w) (x, y) =
    exteriorProductDedekindTerm C g f m n β α w (y, x)
  have hideal : exteriorProductIdeal g f y x = (exteriorProductIdeal f g x y).comap e.inv := by
    rw [exteriorProductIdeal, exteriorProductIdeal, Scheme.IdealSheafData.comap_sup,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, he,
      pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd]
    exact sup_comm _ _
  unfold exteriorProductDedekindTerm
  have hcoeff := closedSubschemeCycleCoeff_comap_of_isIso' C (pullback.fst g f ≫ g)
    (pullback.fst f g ≫ f) e.inv hbase (exteriorProductIdeal f g x y)
    (exteriorProductIdeal g f y x) hideal (n + m - 1) w
  have hdeg : m + n - 1 = n + m - 1 := by ring
  simp only [hdeg]
  rw [← hcoeff]
  by_cases h : DominatesBaseComponent C f x ∨ DominatesBaseComponent C g y
  · rw [ite_eq_left h, ite_eq_left h.symm]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h h'.symm)]

/-- **Stacks 0FC4, the first variable.** Over a base as in Stacks section 42.63, the exterior
product of an `n`-cycle on `X` rationally equivalent to zero with an `m`-cycle on `Y` is
rationally equivalent to zero. -/
theorem exteriorProductDedekindCycles_mem_rationalEquivalences_left (hC : IsDedekindChowBase C)
    {α : CycleGroup C f n} (hα : α ∈ rationalEquivalences C f n) (β : CycleGroup C g m) :
    exteriorProductDedekindCycles C f g n m α β ∈
      rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1) := by
  set e : (pullback f g : Scheme.{u}) ≅ (pullback g f : Scheme.{u}) := pullbackSymmetry f g
    with he
  have hbase : e.inv ≫ (pullback.fst f g ≫ f) = pullback.fst g f ≫ g := by
    rw [← Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.condition]
  have hdeg : m + n - 1 = n + m - 1 := by ring
  have hswap := exteriorProductDedekindCycles_mem_rationalEquivalences_right C g f m n hC β hα
  have hcast := mem_rationalEquivalences_cast C (pullback.fst g f ≫ g) hdeg hswap
  have hpf := properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion e.inv C
    (pullback.fst g f ≫ g) (pullback.fst f g ≫ f) hbase (n + m - 1) _ hcast
  have hval : properPushforward C (pullback.fst g f ≫ g) (pullback.fst f g ≫ f) e.inv hbase
        (n + m - 1) (hdeg ▸ exteriorProductDedekindCycles C g f m n β α) =
      exteriorProductDedekindCycles C f g n m α β := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    obtain ⟨w, rfl⟩ := (Scheme.homeoOfIso e.symm).surjective z
    rw [show (Scheme.homeoOfIso e.symm) w = e.inv.base w from rfl,
      properPushforward_apply_image_of_isClosedImmersion C (pullback.fst g f ≫ g)
        (pullback.fst f g ≫ f) e.inv hbase (n + m - 1) _ w,
      val_cycleGroup_cast C (pullback.fst g f ≫ g) hdeg]
    exact (exteriorProductDedekindCycles_pullbackSymmetry C f g n m α β w).symm
  rwa [hval] at hpf

/-- **Stacks 0FC4.** Over a base as in Stacks section 42.63 the exterior product of cycles is
compatible with rational equivalence in each variable. -/
theorem exteriorProductFactorsThroughRationalEquivalence_of_isDedekindChowBase
    (hC : IsDedekindChowBase C) :
    ExteriorProductFactorsThroughRationalEquivalence C f g n m :=
  ⟨fun α _ hβ ↦ exteriorProductDedekindCycles_mem_rationalEquivalences_right C f g n m hC α hβ,
    fun β _ hα ↦ exteriorProductDedekindCycles_mem_rationalEquivalences_left C f g n m hC hα β⟩

/-- **The exterior product over a Dedekind base**, Stacks 0FC4:
`× : CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`, determined by
`[X'] ⊗ [Y'] ↦ [X' ×_S Y']_{n+m-1}` when one of `X'`, `Y'` dominates an irreducible component of
the base and by `[X'] ⊗ [Y'] ↦ 0` when neither does. -/
def exteriorProductDedekindChowTensor (hC : IsDedekindChowBase C) :
    TensorProduct ℤ (chowGroup C f n) (chowGroup C g m) →+
      chowGroup C (pullback.fst f g ≫ f) (n + m - 1) :=
  exteriorProductDedekindTensor C f g n m
    (exteriorProductFactorsThroughRationalEquivalence_of_isDedekindChowBase C f g n m hC)

/-- On the pure tensor of the classes of two cycles the exterior product over a Dedekind base is
the class of their exterior product. -/
@[simp]
theorem exteriorProductDedekindChowTensor_tmul_mk (hC : IsDedekindChowBase C)
    (α : CycleGroup C f n) (β : CycleGroup C g m) :
    exteriorProductDedekindChowTensor C f g n m hC
        (TensorProduct.tmul ℤ (QuotientAddGroup.mk' (rationalEquivalences C f n) α)
          (QuotientAddGroup.mk' (rationalEquivalences C g m) β)) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1))
        (exteriorProductDedekindCycles C f g n m α β) :=
  rfl

/-- Let `(S, δ)` be as in Stacks section 42.63 — locally the spectrum of a Dedekind domain, with
`δ = 0` at closed points and `δ = 1` elsewhere — and let `X`, `Y` be locally of finite type over
`S`. The map `× : CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)` is well defined: there is exactly
one additive map out of the tensor product sending `[α] ⊗ [β]` to the class of the exterior
product `α × β` of the two cycles. -/
@[stacks 0FC4]
theorem existsUnique_exteriorProductDedekindChowTensor (hC : IsDedekindChowBase C) :
    ∃! F : TensorProduct ℤ (chowGroup C f n) (chowGroup C g m) →+
        chowGroup C (pullback.fst f g ≫ f) (n + m - 1),
      ∀ (α : CycleGroup C f n) (β : CycleGroup C g m),
        F (TensorProduct.tmul ℤ (QuotientAddGroup.mk' (rationalEquivalences C f n) α)
            (QuotientAddGroup.mk' (rationalEquivalences C g m) β)) =
          QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1))
            (exteriorProductDedekindCycles C f g n m α β) := by
  refine ⟨exteriorProductDedekindChowTensor C f g n m hC,
    exteriorProductDedekindChowTensor_tmul_mk C f g n m hC, fun F hF ↦ ?_⟩
  refine AddMonoidHom.ext fun t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    induction a using QuotientAddGroup.induction_on with
    | H α =>
      induction b using QuotientAddGroup.induction_on with
      | H β =>
        exact (hF α β).trans (exteriorProductDedekindChowTensor_tmul_mk C f g n m hC α β).symm
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

end Descent

end Stacks.Chow
