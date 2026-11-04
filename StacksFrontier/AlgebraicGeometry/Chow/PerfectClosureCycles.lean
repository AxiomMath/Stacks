module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.AlgebraicGeometry.Chow.BaseFieldExtension
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.BaseChangeComponentDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparableField
public import StacksFrontier.FieldTheory.PerfectClosure
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support

/-!
# Cycles after passing to the perfect closure of the base field

Let `k` be a field of characteristic `p > 0` with perfect closure `k^perf`, and let `X` be an
algebraic scheme over `k`. The projection `X_{k^perf} ⟶ X` is a homeomorphism, so the integral
closed subschemes of `X_{k^perf}` correspond bijectively to those of `X`; the base-change map
`Z_r(X) ⟶ Z_r(X_{k^perf})` sends the generator attached to such a subscheme to the
corresponding generator times the multiplicity of the component, which by Stacks 0H4F is a
power of `p`. Hence the map is injective and its cokernel is `p`-power torsion.

## Main definitions

* `Stacks.Chow.fieldExtensionBaseChangeSituation` — the flat base change of Chow situations
  attached to a field extension.
* `Stacks.Chow.perfectClosureBaseChangeSituation` — that base change for the perfect closure.

## Main results

* `Stacks.Chow.baseChangeCyclePullback_perfectClosure_injective` and
  `Stacks.Chow.isElementPowerTorsion_cokernel_baseChangeCyclePullback_perfectClosure` —
  **Stacks 0H4G**: the base-change map on `r`-cycles to the perfect closure is injective and its
  cokernel is a `p`-power torsion module.

## Implementation notes

An algebraic scheme over `k` is a scheme whose structure morphism to `Spec k` is quasi-compact
and locally of finite type, and `k^perf` is `perfectClosure k (AlgebraicClosure k)`, the largest
purely inseparable subextension of an algebraic closure. The group `Z_r(X)` is the cycle group
of the Chow situation `Stacks.Chow.fieldChowSituation k`, whose dimension function vanishes, so
that the delta-dimension of an integral closed subscheme is its dimension over `k`.

Both statements are proved from a general form, valid for any flat base change of Chow
situations with vanishing dimension shift whose projections are homeomorphisms and whose
component multiplicities are powers of a fixed integer. Quasi-compactness enters only through
the finiteness of the support of a cycle, which bounds the exponents occurring in a single
cycle and so produces one power of `p` annihilating a given cokernel class.

## References

* [Stacks Project, Tag 0H4G](https://stacks.math.columbia.edu/tag/0H4G)
* [Stacks Project, Tag 0H4F](https://stacks.math.columbia.edu/tag/0H4F)
* [Stacks Project, Tag 05E6](https://stacks.math.columbia.edu/tag/05E6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The flat base change attached to a field extension -/

/-- The flat base change of Chow situations attached to a field extension `K/k`: the two bases
are the spectra of `k` and of `K` with their vanishing dimension functions, and the dimension
shift is zero. -/
abbrev fieldExtensionBaseChangeSituation (k K : Type u) [Field k] [Field K] [Algebra k K] :
    FlatBaseChangeSituation.{u} where
  base := fieldChowSituation k
  baseChange := fieldChowSituation K
  g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  flat := Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k K))
  c := 0
  dimensionFunction_eq_add := fun _ _ ↦ by
    simp [fieldDimensionFunction, AlgebraicGeometry.fieldBaseDimensionFunction]

/-- The dimension shift of a base change along a field extension vanishes. -/
@[simp]
theorem fieldExtensionBaseChangeSituation_c (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (fieldExtensionBaseChangeSituation k K).c = 0 :=
  rfl

/-- The flat base change of Chow situations from a field `k` to its perfect closure `k^perf`,
realized as the largest purely inseparable subextension of an algebraic closure of `k`. -/
abbrev perfectClosureBaseChangeSituation (k : Type u) [Field k] : FlatBaseChangeSituation.{u} :=
  fieldExtensionBaseChangeSituation k ↥(perfectClosure k (AlgebraicClosure k))

/-! ### The reduced closure of a point -/

/-- The multiplicity of a component of a closed subscheme does not depend on the ambient
scheme. -/
private theorem componentMultiplicity_eq_id {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (ξ : genericPoints Z) :
    componentMultiplicity i ξ = componentMultiplicity (𝟙 Z) ξ := by
  rw [componentMultiplicity_eq_length_stalk i ξ, componentMultiplicity_eq_length_stalk (𝟙 Z) ξ]

/-- A cycle on a scheme with a quasi-compact morphism to a compact scheme has finite support. -/
private theorem finite_support_of_quasiCompact {W S : Scheme.{u}} [CompactSpace S] (w : W ⟶ S)
    [QuasiCompact w] (c : AlgebraicCycle W ℤ) : Set.Finite (Function.support c) := by
  have hcompact : IsCompact (Set.univ : Set W) := by
    simpa using QuasiCompact.isCompact_preimage (f := w) (Set.univ : Set S) isOpen_univ
      isCompact_univ
  simpa using
    (Function.locallyFinsupp.locallyFiniteSupport c).finite_inter_support_of_isCompact hcompact

/-! ### A flat base change whose projections are homeomorphisms -/

section Homeomorph

variable (B : FlatBaseChangeSituation.{u}) (p : ℕ) (hc : B.c = 0)
  (hhom : ∀ {W : Scheme.{u}} (w : W ⟶ B.base.S), IsHomeomorph (pullback.fst w B.g).base)
  (hmul : ∀ {W : Scheme.{u}} (w : W ⟶ B.base.S), IsIntegral W → LocallyOfFiniteType w →
    ∀ ζ : genericPoints (pullback w B.g : Scheme.{u}),
      componentMultiplicity (𝟙 (pullback w B.g : Scheme.{u})) ζ ≠ 0 ∧
        ∃ n : ℕ, componentMultiplicity (𝟙 (pullback w B.g : Scheme.{u})) ζ = (p : ℤ) ^ n)

include hc hhom hmul

/-- In a flat base change of Chow situations with vanishing dimension shift whose projections
are homeomorphisms, every point of the base change has the same relative dimension as its
image, and the weight with which it enters a base-changed cycle is the nonzero multiplicity of
the single component above the reduced closure of that image, concentrated in that relative
dimension. -/
private theorem exists_flatPullbackWeight_eq {X : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] (y : (pullback f B.g : Scheme.{u})) :
    relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) y =
        relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g).base y) ∧
      ∃ m : ℤ, m ≠ 0 ∧ (∃ n : ℕ, m = (p : ℤ) ^ n) ∧
        ∀ r : ℤ, flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g) r y =
          if relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g).base y) = r
            then m else 0 := by
  classical
  set q : (pullback f B.g : Scheme.{u}) ⟶ X := pullback.fst f B.g with hq
  set x : X := q.base y with hx
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hXint : IsIntegral I.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  set Z : Scheme.{u} := pullback (I.subschemeι ≫ f) B.g with hZ
  set e : (I.comap q).subscheme ≅ Z := I.comapIso q ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso f B.g I.subschemeι with he
  set j : Z ⟶ (pullback f B.g : Scheme.{u}) := e.inv ≫ (I.comap q).subschemeι with hj
  have hZirr : IrreducibleSpace Z :=
    ((hhom (I.subschemeι ≫ f)).homeomorph).irreducibleSpace_iff.mpr inferInstance
  have hjsnd : j ≫ pullback.snd f B.g = pullback.snd (I.subschemeι ≫ f) B.g := by
    simp only [hj, he, Iso.trans_inv, Category.assoc,
      Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc, pullbackSymmetry_inv_comp_fst_assoc]
    exact pullbackRightPullbackFstIso_inv_snd_snd f B.g I.subschemeι
  have hrangeI : Set.range I.subschemeι.base = closure ({x} : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hrangeJ : Set.range (I.comap q).subschemeι.base =
      closure ({y} : Set (pullback f B.g : Scheme.{u})) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
      Closeds.coe_preimage, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    show q.base ⁻¹' closure ({x} : Set X) = _
    rw [hx, ← Set.image_singleton, ← (hhom f).image_closure,
      Set.preimage_image_eq _ (hhom f).injective]
  have hrangej : Set.range j.base = closure ({y} : Set (pullback f B.g : Scheme.{u})) := by
    have hcomp : ⇑j.base = ⇑(I.comap q).subschemeι.base ∘ ⇑e.inv.base := rfl
    have hsurj : Function.Surjective ⇑e.inv.base := fun t ↦ ⟨e.hom.base t, by simp⟩
    rw [hcomp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ, hrangeJ]
  have hiy : j.base (genericPoint Z) = y := image_genericPoint_eq_of_range_eq_closure j y hrangej
  have hix : I.subschemeι.base (genericPoint I.subscheme) = x :=
    image_genericPoint_eq_of_range_eq_closure I.subschemeι x hrangeI
  set ξ : genericPoints Z := ⟨genericPoint Z, by
    simp [genericPoints, genericPoint_closure, irreducibleComponents_eq_singleton]⟩ with hξ
  set η : genericPoints (I.comap q).subscheme := genericPointsIso e.symm ξ with hη
  have hηy : (I.comap q).subschemeι.base η.1 = y := hiy
  set d : ℤ := relativeDimension B.base.dimensionFunction f x with hd
  have hdX : schemeDeltaDimension B.base (I.subschemeι ≫ f) = (d : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion, hix, hd]
  have hdZ := deltaDimension_component_baseChange B (I.subschemeι ≫ f) d hdX
    (genericPoints.component ξ)
  rw [deltaDimension_eq_of_isGenericPoint _ _ _ ξ.1 (genericPoints.isGenericPoint ξ)] at hdZ
  have hdim : relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) y = d := by
    rw [← hiy, ← relativeDimension_comp_closedImmersion, hjsnd,
      show genericPoint Z = (ξ : Z) from rfl, hdZ, hc, add_zero]
  obtain ⟨hne, hpow⟩ := hmul (I.subschemeι ≫ f) hXint inferInstance ξ
  refine ⟨hdim, componentMultiplicity (𝟙 Z) ξ, hne, hpow, fun r ↦ ?_⟩
  have hiff : (∃ ζ : genericPoints (I.comap q).subscheme,
      (I.comap q).subschemeι.base ζ.1 = y ∧
      relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) y = r) ↔ d = r :=
    ⟨fun h ↦ hdim.symm.trans h.choose_spec.2, fun hr ↦ ⟨η, hηy, hdim.trans hr⟩⟩
  rw [flatPullbackWeight, closedSubschemeCycleCoeff]
  by_cases h : d = r
  · rw [dite_eq_left (hiff.2 h), ite_eq_left h]
    have hchoose : Classical.choose (hiff.2 h) = η := by
      apply Subtype.ext
      apply (I.comap q).subschemeι.isClosedEmbedding.injective
      exact (Classical.choose_spec (hiff.2 h)).1.trans hηy.symm
    rw [hchoose, ← componentMultiplicity_eq_of_iso (I.comap q).subschemeι e.symm ξ]
    exact componentMultiplicity_eq_id j ξ
  · rw [dite_eq_right fun hex ↦ h (hiff.1 hex), ite_eq_right h]

/-- In a flat base change of Chow situations with vanishing dimension shift whose projections
are homeomorphisms, the base-change map on cycle groups is injective. -/
private theorem injective_baseChangeCyclePullback {X : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] (r : ℤ) :
    Function.Injective (baseChangeCyclePullback B f r) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦
    Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  show z.1 x = 0
  by_contra hx
  obtain ⟨y, hy⟩ := (hhom f).surjective x
  obtain ⟨-, m, hm, -, hweight⟩ := exists_flatPullbackWeight_eq B p hc hhom hmul f y
  have hdy : relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g).base y) =
      r + B.c := by
    rw [hy, hc, add_zero]
    exact (mem_cyclesOfDimension_iff_forall_point B.base f r z.1).mp z.2 x hx
  have heval := congrArg (fun w ↦ w.1 y) hz
  rw [baseChangeCyclePullback_apply, hweight (r + B.c), ite_eq_left hdy, hy] at heval
  exact mul_ne_zero hx hm (by simpa using heval)

/-- In a flat base change of Chow situations with vanishing dimension shift whose projections
are homeomorphisms and whose component multiplicities are powers of `p`, every cycle on the base
change becomes a base-changed cycle after multiplication by a positive power of `p`. -/
private theorem exists_pow_smul_mem_range [CompactSpace B.baseChange.S] {X : Scheme.{u}}
    (f : X ⟶ B.base.S) [LocallyOfFiniteType f] [QuasiCompact f] (r : ℤ)
    (z : CycleGroup B.baseChange (pullback.snd f B.g) (r + B.c)) :
    ∃ N : ℕ, 0 < N ∧ ∃ a : CycleGroup B.base f r,
      baseChangeCyclePullback B f r a = (p : ℤ) ^ N • z := by
  classical
  set eh : (pullback f B.g : Scheme.{u}) ≃ₜ X := (hhom f).homeomorph with heh
  have hdim (y : (pullback f B.g : Scheme.{u})) :
      relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) y =
        relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g).base y) :=
    (exists_flatPullbackWeight_eq B p hc hhom hmul f y).1
  have hweight : ∀ y : (pullback f B.g : Scheme.{u}), ∃ n : ℕ,
      flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g) (r + B.c) y =
        if relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g).base y) = r + B.c
          then (p : ℤ) ^ n else 0 := by
    intro y
    obtain ⟨-, m, -, ⟨n, hn⟩, hm⟩ := exists_flatPullbackWeight_eq B p hc hhom hmul f y
    exact ⟨n, by rw [hm (r + B.c), hn]⟩
  choose n hn using hweight
  have hzfin : Set.Finite (Function.support z.1) :=
    finite_support_of_quasiCompact (pullback.snd f B.g) z.1
  obtain ⟨N, hN⟩ := (hzfin.image n).bddAbove
  set aFun : X → ℤ := fun w ↦ z.1 (eh.symm w) * (p : ℤ) ^ (N + 1 - n (eh.symm w)) with haFun
  have haz (w : X) (hw : aFun w ≠ 0) : z.1 (eh.symm w) ≠ 0 := left_ne_zero_of_mul hw
  have hzdim (y : (pullback f B.g : Scheme.{u})) (hy : z.1 y ≠ 0) :
      relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g).base y) = r := by
    have := (mem_cyclesOfDimension_iff_forall_point B.baseChange (pullback.snd f B.g)
      (r + B.c) z.1).mp z.2 y hy
    rwa [hdim y, hc, add_zero] at this
  have haFinite : Set.Finite (Function.support aFun) := (hzfin.image eh).subset
    fun w hw ↦ ⟨eh.symm w, haz w hw, eh.apply_symm_apply w⟩
  set aCycle : AlgebraicCycle X ℤ :=
    { toFun := aFun
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ ↦
        ⟨Set.univ, Filter.univ_mem, by simpa using haFinite⟩ } with haCycle
  refine ⟨N + 1, Nat.succ_pos N, ⟨aCycle, (mem_cyclesOfDimension_iff_forall_point ..).mpr
    fun w hw ↦ by
      have := hzdim _ (haz w hw)
      rwa [show (pullback.fst f B.g).base (eh.symm w) = w from eh.apply_symm_apply w] at this⟩,
    Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)⟩
  have hey : eh.symm ((pullback.fst f B.g).base y) = y := eh.symm_apply_apply y
  rw [baseChangeCyclePullback_apply, hn y]
  change aFun _ * _ = (p : ℤ) ^ (N + 1) * z.1 y
  simp only [haFun, hey]
  by_cases hy : z.1 y = 0
  · simp [hy]
  · rw [ite_eq_left (by rw [hc, add_zero]; exact hzdim y hy), mul_assoc, ← pow_add,
      Nat.sub_add_cancel (le_trans (hN ⟨y, hy, rfl⟩) (Nat.le_succ N)), mul_comm]

end Homeomorph

/-! ### The perfect closure -/

/-- Along the base change to the perfect closure of `k`, the multiplicity of the single
component above an integral scheme locally of finite type over `k` is a nonzero power of the
characteristic of `k`; this is Stacks 0H4F. -/
private theorem componentMultiplicity_perfectClosure (k : Type u) [Field k] {W : Scheme.{u}}
    (w : W ⟶ (perfectClosureBaseChangeSituation k).base.S) (hW : IsIntegral W)
    (hwft : LocallyOfFiniteType w)
    (ζ : genericPoints (pullback w (perfectClosureBaseChangeSituation k).g : Scheme.{u})) :
    componentMultiplicity
        (𝟙 (pullback w (perfectClosureBaseChangeSituation k).g : Scheme.{u})) ζ ≠ 0 ∧
      ∃ n : ℕ, componentMultiplicity
        (𝟙 (pullback w (perfectClosureBaseChangeSituation k).g : Scheme.{u})) ζ =
          (ringChar k : ℤ) ^ n := by
  have := hW
  have := hwft
  have hm := componentMultiplicity_baseChange_eq_one_or_char_pow
    (k := k) (K := ↥(perfectClosure k (AlgebraicClosure k))) w ζ
  dsimp only at hm
  rcases hm with h | ⟨hchar, n, h⟩
  · exact ⟨by rw [h]; norm_num, 0, by rw [h]; norm_num⟩
  · exact ⟨by rw [h]; exact pow_ne_zero _ (by exact_mod_cast hchar), n, h⟩

/-- Base change to the perfect closure of `k` is a homeomorphism on underlying spaces. -/
private theorem isHomeomorph_pullbackFst_perfectClosure (k : Type u) [Field k] {W : Scheme.{u}}
    (w : W ⟶ (perfectClosureBaseChangeSituation k).base.S) :
    IsHomeomorph (pullback.fst w (perfectClosureBaseChangeSituation k).g).base :=
  isHomeomorph_pullbackFst_specMap_algebraMap k ↥(perfectClosure k (AlgebraicClosure k)) w

/-- For an algebraic scheme `X` over a field `k`, the base-change homomorphism
`Z_r(X) ⟶ Z_r(X_{k^perf})` to the perfect closure of `k` is injective. -/
@[stacks 0H4G "injectivity"]
theorem baseChangeCyclePullback_perfectClosure_injective (k : Type u) [Field k] (r : ℕ)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] :
    Function.Injective
      (baseChangeCyclePullback (perfectClosureBaseChangeSituation k) f (r : ℤ)) :=
  injective_baseChangeCyclePullback (perfectClosureBaseChangeSituation k) (ringChar k) rfl
    (fun w ↦ isHomeomorph_pullbackFst_perfectClosure k w)
    (fun w ↦ componentMultiplicity_perfectClosure k w) f (r : ℤ)

/-- For an algebraic scheme `X` over a field `k` of characteristic `p > 0`, the cokernel of the
base-change homomorphism `Z_r(X) ⟶ Z_r(X_{k^perf})` to the perfect closure of `k` is a `p`-power
torsion module. -/
@[stacks 0H4G "p-power torsion cokernel"]
theorem isElementPowerTorsion_cokernel_baseChangeCyclePullback_perfectClosure (k : Type u)
    [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (r : ℕ) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsElementPowerTorsion ℤ
      (CycleGroup (perfectClosureBaseChangeSituation k).baseChange
          (pullback.snd f (perfectClosureBaseChangeSituation k).g)
          ((r : ℤ) + (perfectClosureBaseChangeSituation k).c) ⧸
        (baseChangeCyclePullback (perfectClosureBaseChangeSituation k) f (r : ℤ)).range)
      (p : ℤ) := by
  obtain rfl := ringChar.eq k p
  intro w
  induction w using QuotientAddGroup.induction_on with
  | H z =>
    obtain ⟨N, hN, a, ha⟩ := exists_pow_smul_mem_range (perfectClosureBaseChangeSituation k)
      (ringChar k) rfl (fun w ↦ isHomeomorph_pullbackFst_perfectClosure k w)
      (fun w ↦ componentMultiplicity_perfectClosure k w) f (r : ℤ) z
    exact ⟨N, hN, (map_zsmul (QuotientAddGroup.mk' _) ((ringChar k : ℤ) ^ N) z).symm.trans
      ((QuotientAddGroup.eq_zero_iff _).mpr ⟨a, ha⟩)⟩

end Stacks.Chow

end
