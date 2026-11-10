module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Stages

/-!
# Divided powers on a set-indexed divided power polynomial algebra

Let `(A, I, γ)` be a divided power ring and `W` an arbitrary type of variables. The finite stages
`A⟨x_e : e ∈ E⟩`, for `E ⊆ W` finite, each carry the canonical divided power structure of the
finite-variable theory, and the transition maps between them are divided power morphisms. Since
every element of `A⟨x_w : w ∈ W⟩` lies in the image of some finite stage, and the finite-stage
inclusions are injective, these structures glue: the distinguished ideal
`dividedPowerPolynomialIdeal I W` carries a unique divided power structure making every
finite-stage inclusion a divided power morphism.

This file constructs that structure, records the two properties that identify it — the divided
power of a variable is the corresponding divided power monomial, and the coefficient map is a
divided power morphism — and proves the uniqueness statement.

## Main definitions

* `DividedPowers.setIndexedDividedPowerPolynomialDividedPowers` — the divided power structure
  induced on the distinguished ideal of `A⟨x_w : w ∈ W⟩`.
* `DividedPowers.setIndexedDividedPowerPolynomialDividedPowerRing` — the resulting divided power
  ring.
* `DividedPowers.setIndexedDividedPowerPolynomialCoefficientDPMorphism` — the coefficient
  morphism out of `A`.

## Main results

* `DividedPowers.finiteStageInclusion_injective` and `DividedPowers.finiteStageMap_injective` —
  the finite-stage maps are injective.
* `DividedPowers.exists_finiteStage_lift` and
  `DividedPowers.exists_finiteStage_lift_mem_polynomialIdeal` — every element, respectively every
  element of the distinguished ideal, comes from a finite stage.
* `DividedPowers.finiteStageMap_isDPMorphism` — the transition maps between finite stages
  preserve the canonical divided powers.
* `DividedPowers.finiteStageInclusion_isDPMorphism` — the finite-stage inclusions preserve the
  induced divided powers.
* `DividedPowers.setIndexedDividedPowerPolynomialDividedPowers_dpow_variable` — the induced
  divided powers of a variable are its divided power monomials.
* `DividedPowers.setIndexedDividedPowerPolynomialCoefficient_isDPMorphism` — the coefficient map
  preserves divided powers.
* `DividedPowers.setIndexedDividedPowerPolynomialDividedPowers_unique` — compatibility with every
  finite stage determines the structure.

## Implementation notes

The distinguished ideal is `dividedPowerPolynomialIdeal I W`, which is already defined for an
arbitrary index type by the finite-variable theory, so no new ideal is introduced here.

The divided powers are defined by choosing, for an element `x` of the ideal, a finite stage `E`
and a lift `y` of `x` lying in the ideal of that stage, and taking the image of `γ_n y`. The
choice is immaterial: two lifts become equal after mapping to the union of the two stages, by
injectivity of the finite-stage inclusions, and the transition maps are divided power morphisms.
That independence is
`DividedPowers.setIndexedDividedPowerPolynomialDividedPowers_dpow_eq_of_lift`, and every axiom of
the structure is then checked by pushing the finitely many elements involved into one common
finite stage.

Producing a lift *inside the ideal* requires more than producing a lift, because the ideal is a
sum of an extension of `I` and the augmentation ideal; the two summands are handled separately,
the first by a span induction over the generators of the extension and the second by the
compatibility of the augmentations with the finite-stage inclusions.

## References

* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
-/

@[expose] public section

noncomputable section

namespace DividedPowers

universe u w

/-- Restriction to a finite stage, as a linear map defined on all finitely supported families. -/
private noncomputable def finiteStageRestriction {A : Type u} [CommRing A] {W : Type w}
    (E : Finset W) : (W →₀ A) →ₗ[A] (E →₀ A) where
  toFun x := x.comapDomain Subtype.val fun _ _ _ _ hab => Subtype.ext hab
  map_add' x y := by ext e; rfl
  map_smul' r x := by ext e; rfl

/-- Restriction to a finite stage is a retraction of the stage embedding. -/
private theorem finiteStageRestriction_comp_lmapDomain {A : Type u} [CommRing A]
    {W : Type w} (E : Finset W) :
    (finiteStageRestriction E).comp (Finsupp.lmapDomain A A (fun e : E => e.1)) =
      LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  change (Finsupp.lmapDomain A A (fun e : E => e.1) x).comapDomain Subtype.val
    (fun _ _ _ _ hab => Subtype.ext hab) = x
  exact Finsupp.comapDomain_mapDomain (f := Subtype.val) Subtype.val_injective x

/-- A finite-stage inclusion is injective: restriction of variables provides a retraction. -/
public theorem finiteStageInclusion_injective (A : Type u) [CommRing A] {W : Type w}
    (E : Finset W) : Function.Injective (finiteStageInclusion A E) := by
  intro x y h
  have h' := congrArg (DividedPowerAlgebra.map A (finiteStageRestriction E)) h
  change (DividedPowerAlgebra.map A (finiteStageRestriction E)).comp
      (finiteStageInclusion A E) x =
    (DividedPowerAlgebra.map A (finiteStageRestriction E)).comp
      (finiteStageInclusion A E) y at h'
  rwa [finiteStageInclusion, ← DividedPowerAlgebra.map_comp,
    finiteStageRestriction_comp_lmapDomain, DividedPowerAlgebra.map_id,
    AlgHom.id_apply] at h'

/-- A transition map between finite stages is injective. -/
public theorem finiteStageMap_injective (A : Type u) [CommRing A] {W : Type w}
    {E F : Finset W} (h : E ⊆ F) :
    Function.Injective (finiteStageMap A h) := fun x y hxy =>
  finiteStageInclusion_injective A E <| by
    rw [← finiteStageInclusion_comp A h, AlgHom.comp_apply, AlgHom.comp_apply, hxy]

/-- A transition map followed by the inclusion of the larger stage is the inclusion of the smaller
stage. -/
private theorem finiteStageInclusion_finiteStageMap (A : Type u) [CommRing A] {W : Type w}
    {E F : Finset W} (h : E ⊆ F) (y : DividedPowerAlgebra A (E →₀ A)) :
    finiteStageInclusion A F (finiteStageMap A h y) = finiteStageInclusion A E y :=
  DFunLike.congr_fun (finiteStageInclusion_comp A h) y

/-- An algebra map sends the extension of an ideal of the base ring into the extension of that
ideal in the target. -/
private theorem algHom_mem_map_algebraMap {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (f : B →ₐ[A] C) (I : Ideal A) {x : B}
    (hx : x ∈ Ideal.map (algebraMap A B) I) : f x ∈ Ideal.map (algebraMap A C) I := by
  have := Ideal.mem_map_of_mem f.toRingHom hx
  rwa [Ideal.map_map, f.toRingHom_eq_coe, f.comp_algebraMap] at this

/-- Every element of the set-indexed divided power polynomial algebra comes from a finite
stage. -/
public theorem exists_finiteStage_lift (A : Type u) [CommRing A] (W : Type w)
    (x : setIndexedDividedPowerPolynomialAlgebra A W) :
    ∃ E : Finset W, ∃ y : DividedPowerAlgebra A (E →₀ A),
      finiteStageInclusion A E y = x := by
  classical
  induction x using DividedPowerAlgebra.induction_on with
  | C a =>
      refine ⟨∅, algebraMap A _ a, ?_⟩
      simp [finiteStageInclusion]
  | add x y hx hy =>
      obtain ⟨E, xE, hxE⟩ := hx
      obtain ⟨F, yF, hyF⟩ := hy
      let G := E ∪ F
      refine ⟨G, finiteStageMap A (Finset.subset_union_left : E ⊆ G) xE +
        finiteStageMap A (Finset.subset_union_right : F ⊆ G) yF, ?_⟩
      rw [map_add, finiteStageInclusion_finiteStageMap, finiteStageInclusion_finiteStageMap,
        hxE, hyF]
  | dp x n m hx =>
      obtain ⟨E, xE, hxE⟩ := hx
      let G := E ∪ m.support
      have hmg : m.support ⊆ G := Finset.subset_union_right
      let mG := restrictToStage G m hmg
      refine ⟨G, finiteStageMap A (Finset.subset_union_left : E ⊆ G) xE *
        DividedPowerAlgebra.dp A n mG, ?_⟩
      rw [map_mul, finiteStageInclusion_finiteStageMap, hxE,
        finiteStageInclusion, DividedPowerAlgebra.map_apply_dp]
      congr 1
      exact congrArg (DividedPowerAlgebra.dp A n)
        (stageEmbedding_restrict G m hmg)

/-- The augmentations of the finite stages are compatible with the finite-stage inclusions. -/
public theorem dividedPowerPolynomialAugmentation_comp_finiteStageInclusion
    (A : Type u) [CommRing A] {W : Type w} (E : Finset W) :
    (dividedPowerPolynomialAugmentation A W).comp (finiteStageInclusion A E) =
      dividedPowerPolynomialAugmentation A E := by
  apply DividedPowerAlgebra.algHom_ext
  intro n m
  simp [finiteStageInclusion, dividedPowerPolynomialAugmentation,
    DividedPowerAlgebra.map_apply_dp, DividedPowerAlgebra.lift_apply_dp]

/-- A first divided power `x^[1]` lies in the divided power ideal. -/
private theorem dp_one_mem_polynomialIdeal (A : DividedPowerRing.{u})
    (ι : Type w) (m : ι →₀ A) :
    DividedPowerAlgebra.dp A 1 m ∈ dividedPowerPolynomialIdeal A.ideal ι := by
  apply Ideal.mem_sup_right
  change dividedPowerPolynomialAugmentation A ι (DividedPowerAlgebra.dp A 1 m) = 0
  simp [dividedPowerPolynomialAugmentation, DividedPowerAlgebra.lift_apply_dp,
    dividedPowersBot]

/-- On a finite stage, the `n`-th divided power of `x^[1]` is `x^[n]`. -/
private theorem dividedPowerPolynomialDividedPowers_dpow_dp_one (A : DividedPowerRing.{u})
    (ι : Type w) [Finite ι] (n : ℕ) (m : ι →₀ A) :
    (dividedPowerPolynomialDividedPowers A ι).dpow n
      (DividedPowerAlgebra.dp A 1 m) = DividedPowerAlgebra.dp A n m := by
  classical
  let hI := dividedPowerPolynomialDividedPowers A ι
  let v : ι → DividedPowerAlgebra A (ι →₀ A) :=
    fun i => dividedPowerPolynomialVariable A i
  have hv : ∀ i ∈ m.support, v i ∈ dividedPowerPolynomialIdeal A.ideal ι :=
    fun i _ => variable_mem_polynomialIdeal A i
  have hm : m.support.sum (fun i => m i • Finsupp.single i 1) = m := by
    simpa [Finsupp.sum, Finsupp.smul_single] using Finsupp.sum_single m
  have hcount (i x : ι) :
      Multiset.count i (↑(x ::ₛ (∅ : Sym ι 0)) : Multiset ι) =
        if i = x then 1 else 0 := by
    change Multiset.count i (x ::ₘ (0 : Multiset ι)) = _
    rw [Multiset.count_cons]
    simp
  have hsym : m.support.sym 1 =
      m.support.image (fun x => x ::ₛ (∅ : Sym ι 0)) := by
    simp [Finset.sym_succ, Finset.sym_zero, Finset.sup_singleton_apply]
  have hsym_inj : Set.InjOn (fun x : ι => x ::ₛ (∅ : Sym ι 0)) m.support := by
    intro x hx y hy hxy
    exact (Sym.cons_inj_left _ _ _).mp hxy
  have hrepr' : DividedPowerAlgebra.dp A 1 m =
      m.support.sum fun i => m i • v i := by
    have hdp := congrArg (DividedPowerAlgebra.dp A 1) hm.symm
    rw [hdp, DividedPowerAlgebra.dp_sum_smul (s := m.support) (q := 1)
      (a := fun i => m i) (x := fun i => Finsupp.single i 1)]
    rw [hsym, Finset.sum_image hsym_inj]
    simp only [hcount]
    apply Finset.sum_congr rfl
    intro x hx
    have hcoeff : ∏ i ∈ m.support, m i ^ (if i = x then 1 else 0) = m x := by
      rw [Finset.prod_eq_single_of_mem x hx]
      · simp
      · intro i hi hix
        simp [hix]
    have hprod : ∏ i ∈ m.support,
        DividedPowerAlgebra.dp A (if i = x then 1 else 0) (Finsupp.single i 1) =
          dividedPowerPolynomialVariable A x := by
      rw [Finset.prod_eq_single_of_mem x hx]
      · simp [dividedPowerPolynomialVariable]
      · intro i hi hix
        simp [hix, DividedPowerAlgebra.dp_zero]
    rw [hcoeff, hprod]
  have hrepr : DividedPowerAlgebra.dp A 1 m =
      m.sum fun i a => a • v i := by
    simpa [Finsupp.sum] using hrepr'
  rw [hrepr, hI.dpow_linearCombination hv]
  have hdp := congrArg (DividedPowerAlgebra.dp A n) hm.symm
  rw [hdp, DividedPowerAlgebra.dp_sum_smul (s := m.support) (q := n)
    (a := fun i => m i) (x := fun i => Finsupp.single i 1)]
  simp only [Finsupp.prod, v, hI, dividedPowerPolynomialDividedPowers_dpow_variable]
  exact Finset.sum_congr rfl fun _ _ => Finset.prod_smul _ _ _

/-- A first divided power `x^[1]` is the corresponding linear combination of variables. -/
private theorem dp_one_eq_finsuppSum {A : Type u} [CommRing A] {ι : Type w}
    (m : ι →₀ A) :
    DividedPowerAlgebra.dp A 1 m = m.sum fun i a => a •
      DividedPowerAlgebra.dp A 1 (Finsupp.single i 1) := by
  rw [← DividedPowerAlgebra.embed_def]
  conv_lhs => rw [← Finsupp.sum_single m]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  have hs : (Finsupp.single i (m i) : ι →₀ A) = m i • Finsupp.single i 1 := by
    ext j
    by_cases h : j = i <;> simp [h]
  rw [hs, map_smul, DividedPowerAlgebra.embed_def]

/-- An element of the extension of the coefficient ideal lifts to the extension of the
coefficient ideal in a finite stage. -/
private theorem exists_finiteStage_lift_mem_coefficientIdeal (A : Type u) [CommRing A]
    (I : Ideal A)
    (W : Type w) {x : setIndexedDividedPowerPolynomialAlgebra A W}
    (hx : x ∈ Ideal.map (algebraMap A _) (I : Ideal A)) :
    ∃ E : Finset W, ∃ y : DividedPowerAlgebra A (E →₀ A),
      finiteStageInclusion A E y = x ∧
        y ∈ Ideal.map (algebraMap A _) (I : Ideal A) := by
  classical
  change x ∈ Ideal.span ((algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W)) '' I) at hx
  refine Submodule.span_induction
    (p := fun z _ => ∃ E : Finset W, ∃ y : DividedPowerAlgebra A (E →₀ A),
      finiteStageInclusion A E y = z ∧ y ∈ Ideal.map (algebraMap A _) I)
    ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with ⟨c, hc, rfl⟩
    refine ⟨∅, algebraMap A _ c, ?_, ?_⟩
    · simp [finiteStageInclusion]
    · exact Ideal.mem_map_of_mem (algebraMap A _) hc
  · refine ⟨∅, 0, ?_, Ideal.zero_mem _⟩
    simp [finiteStageInclusion]
  · intro x y _ _ hx hy
    obtain ⟨E, xE, hincE, hmemE⟩ := hx
    obtain ⟨F, yF, hincF, hmemF⟩ := hy
    let G := E ∪ F
    refine ⟨G, finiteStageMap A (Finset.subset_union_left : E ⊆ G) xE +
      finiteStageMap A (Finset.subset_union_right : F ⊆ G) yF, ?_, ?_⟩
    · rw [map_add, finiteStageInclusion_finiteStageMap, finiteStageInclusion_finiteStageMap,
        hincE, hincF]
    · exact Ideal.add_mem _ (algHom_mem_map_algebraMap _ I hmemE)
        (algHom_mem_map_algebraMap _ I hmemF)
  · intro r x _ hx
    obtain ⟨E, xE, hincE, hmemE⟩ := hx
    obtain ⟨F, rF, hincF⟩ := exists_finiteStage_lift A W r
    let G := E ∪ F
    let z := finiteStageMap A (Finset.subset_union_left : E ⊆ G) xE
    let rG := finiteStageMap A (Finset.subset_union_right : F ⊆ G) rF
    refine ⟨G, rG * z, ?_, ?_⟩
    · rw [map_mul, finiteStageInclusion_finiteStageMap, hincF,
        finiteStageInclusion_finiteStageMap, hincE]
      rfl
    · exact Ideal.mul_mem_left _ _ (algHom_mem_map_algebraMap _ I hmemE)

/-- Every element of the divided power ideal of the set-indexed algebra lifts to an element of
the divided power ideal of some finite stage. -/
public theorem exists_finiteStage_lift_mem_polynomialIdeal (A : DividedPowerRing.{u})
    (W : Type w) {x : setIndexedDividedPowerPolynomialAlgebra A W}
    (hx : x ∈ dividedPowerPolynomialIdeal A.ideal W) :
    ∃ E : Finset W, ∃ y : DividedPowerAlgebra A (E →₀ A),
      finiteStageInclusion A E y = x ∧ y ∈ dividedPowerPolynomialIdeal A.ideal E := by
  classical
  change x ∈ Ideal.map (algebraMap A _) A.ideal +
    RingHom.ker (dividedPowerPolynomialAugmentation A W).toRingHom at hx
  rw [Submodule.add_eq_sup, Submodule.mem_sup] at hx
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  obtain ⟨E, aE, hincA, hmemA⟩ :=
    exists_finiteStage_lift_mem_coefficientIdeal A A.ideal W ha
  obtain ⟨F, bF, hincB⟩ := exists_finiteStage_lift A W b
  let G := E ∪ F
  let aG := finiteStageMap A (Finset.subset_union_left : E ⊆ G) aE
  let bG := finiteStageMap A (Finset.subset_union_right : F ⊆ G) bF
  refine ⟨G, aG + bG, ?_, ?_⟩
  · rw [map_add, finiteStageInclusion_finiteStageMap, finiteStageInclusion_finiteStageMap,
      hincA, hincB]
  · change aG + bG ∈ Ideal.map (algebraMap A _) A.ideal +
      RingHom.ker (dividedPowerPolynomialAugmentation A G).toRingHom
    apply Submodule.add_mem_sup
    · exact algHom_mem_map_algebraMap _ A.ideal hmemA
    · change dividedPowerPolynomialAugmentation A G bG = 0
      change dividedPowerPolynomialAugmentation A W b = 0 at hb
      have hincBG : finiteStageInclusion A G bG = b :=
        (finiteStageInclusion_finiteStageMap A _ bF).trans hincB
      have haugG := congrArg (fun f : _ →ₐ[A] A => f bG)
        (dividedPowerPolynomialAugmentation_comp_finiteStageInclusion A G)
      rw [AlgHom.comp_apply, hincBG, hb] at haugG
      exact haugG.symm

/-- Transition maps between finite stages preserve the canonical divided powers. -/
@[stacks 07H6 "compatible_divided_powers"]
public theorem finiteStageMap_isDPMorphism (A : DividedPowerRing.{u})
    {W : Type w} {E F : Finset W} (h : E ⊆ F) :
    _root_.DividedPowers.IsDPMorphism
      (dividedPowerPolynomialDividedPowers A E)
      (dividedPowerPolynomialDividedPowers A F)
      (finiteStageMap A h).toRingHom := by
  classical
  let B := dividedPowerPolynomialDividedPowerRing A F
  let k : E → B.ideal := fun e =>
    ⟨dividedPowerPolynomialVariable A ⟨e.1, h e.2⟩,
      variable_mem_polynomialIdeal (ι := (F : Type w)) A ⟨e.1, h e.2⟩⟩
  obtain ⟨φ, hφ, -⟩ :=
    existsUnique_dPMorphism_from_dividedPowerPolynomial A E B
      (dividedPowerPolynomialCoefficientDPMorphism A F) k
  let φA : DividedPowerAlgebra A (E →₀ A) →ₐ[A] DividedPowerAlgebra A (F →₀ A) :=
    { toRingHom := φ.toRingHom
      commutes' a := congrArg
        (fun g : _root_.DividedPowers.DPMorphism A.dividedPowers B.dividedPowers => g a) hφ.1 }
  have hvar (e : E) : φA (dividedPowerPolynomialVariable A e) =
      finiteStageMap A h (dividedPowerPolynomialVariable A e) := by
    calc
      φA (dividedPowerPolynomialVariable A e) =
          dividedPowerPolynomialVariable A ⟨e.1, h e.2⟩ := by
            change φ (dividedPowerPolynomialVariable A e) = _
            exact hφ.2 e
      _ = finiteStageMap A h (dividedPowerPolynomialVariable A e) := by
            simpa [dividedPowerPolynomialVariable, dividedPowerPolynomialVariableMonomial]
              using (finiteStageMap_dp A h e 1).symm
  have hembed (m : E →₀ A) :
      φA (DividedPowerAlgebra.dp A 1 m) =
        finiteStageMap A h (DividedPowerAlgebra.dp A 1 m) := by
    rw [dp_one_eq_finsuppSum]
    change φA.toLinearMap (m.sum fun i a => a • DividedPowerAlgebra.dp A 1
        (Finsupp.single i 1)) =
      (finiteStageMap A h).toLinearMap (m.sum fun i a => a •
        DividedPowerAlgebra.dp A 1 (Finsupp.single i 1))
    simp only [map_finsuppSum, map_smul]
    exact Finsupp.sum_congr fun e _ => congrArg (fun z => m e • z) (hvar e)
  have hdp (n : ℕ) (m : E →₀ A) :
      φA (DividedPowerAlgebra.dp A n m) =
        finiteStageMap A h (DividedPowerAlgebra.dp A n m) := by
    have hx := dp_one_mem_polynomialIdeal A E m
    have hφdp := φ.isDPMorphism.dpow_comp (n := n)
      (a := DividedPowerAlgebra.dp A 1 m) hx
    let mF := Finsupp.lmapDomain A A (fun e : E => (⟨e.1, h e.2⟩ : F)) m
    have h1 : φA (DividedPowerAlgebra.dp A n m) =
        φ ((dividedPowerPolynomialDividedPowers A E).dpow n
          (DividedPowerAlgebra.dp A 1 m)) := by
      change φ (DividedPowerAlgebra.dp A n m) = _
      rw [← dividedPowerPolynomialDividedPowers_dpow_dp_one A E n m]
    have h2 : φ ((dividedPowerPolynomialDividedPowers A E).dpow n
          (DividedPowerAlgebra.dp A 1 m)) =
        B.dividedPowers.dpow n (φA (DividedPowerAlgebra.dp A 1 m)) := by
      change φ.toRingHom ((dividedPowerPolynomialDividedPowers A E).dpow n
          (DividedPowerAlgebra.dp A 1 m)) =
        B.dividedPowers.dpow n (φA.toRingHom (DividedPowerAlgebra.dp A 1 m))
      exact hφdp.symm
    have h3 : B.dividedPowers.dpow n (φA (DividedPowerAlgebra.dp A 1 m)) =
        B.dividedPowers.dpow n
          (finiteStageMap A h (DividedPowerAlgebra.dp A 1 m)) := by
      change (dividedPowerPolynomialDividedPowers A F).dpow n
          (φA (DividedPowerAlgebra.dp A 1 m)) =
        (dividedPowerPolynomialDividedPowers A F).dpow n
          (finiteStageMap A h (DividedPowerAlgebra.dp A 1 m))
      rw [hembed]
    have hmap (k : ℕ) : finiteStageMap A h (DividedPowerAlgebra.dp A k m) =
        DividedPowerAlgebra.dp A k mF := by
      simp [mF, finiteStageMap, DividedPowerAlgebra.map_apply_dp]
    have h4 : B.dividedPowers.dpow n
          (finiteStageMap A h (DividedPowerAlgebra.dp A 1 m)) =
        DividedPowerAlgebra.dp A n mF := by
      rw [hmap]
      simpa [B, dividedPowerPolynomialDividedPowerRing] using
        (dividedPowerPolynomialDividedPowers_dpow_dp_one A F n mF)
    have h5 : DividedPowerAlgebra.dp A n mF =
        finiteStageMap A h (DividedPowerAlgebra.dp A n m) := (hmap n).symm
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hφA : φA = finiteStageMap A h := DividedPowerAlgebra.algHom_ext hdp
  rw [← hφA]
  exact φ.isDPMorphism

/-- A finite-stage inclusion maps the divided power ideal of the stage into the divided power
ideal of the set-indexed algebra. -/
public theorem finiteStageInclusion_mem_polynomialIdeal (A : DividedPowerRing.{u})
    (W : Type w) (E : Finset W) {x : DividedPowerAlgebra A (E →₀ A)}
    (hx : x ∈ dividedPowerPolynomialIdeal A.ideal E) :
    finiteStageInclusion A E x ∈ dividedPowerPolynomialIdeal A.ideal W := by
  change x ∈ Ideal.map (algebraMap A _) A.ideal +
      RingHom.ker (dividedPowerPolynomialAugmentation A E).toRingHom at hx
  rw [Submodule.add_eq_sup, Submodule.mem_sup] at hx
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  change finiteStageInclusion A E (a + b) ∈
      Ideal.map (algebraMap A _) A.ideal +
        RingHom.ker (dividedPowerPolynomialAugmentation A W).toRingHom
  rw [map_add]
  apply Submodule.add_mem_sup
  · exact algHom_mem_map_algebraMap _ _ ha
  · change dividedPowerPolynomialAugmentation A W (finiteStageInclusion A E b) = 0
    change dividedPowerPolynomialAugmentation A E b = 0 at hb
    rw [← AlgHom.comp_apply, dividedPowerPolynomialAugmentation_comp_finiteStageInclusion, hb]

/-- The divided power operations induced on the distinguished ideal of the set-indexed divided
power polynomial algebra, computed through an arbitrary finite-stage lift. -/
public noncomputable def setIndexedDividedPowerPolynomialDpow
    (A : DividedPowerRing.{u}) (W : Type w) :
    ℕ → setIndexedDividedPowerPolynomialAlgebra A W →
      setIndexedDividedPowerPolynomialAlgebra A W := by
  classical
  intro n x
  by_cases hx : x ∈ dividedPowerPolynomialIdeal A.ideal W
  · let h := exists_finiteStage_lift_mem_polynomialIdeal A W hx
    let E := Classical.choose h
    let hE := Classical.choose_spec h
    let y := Classical.choose hE
    exact finiteStageInclusion A E
      ((dividedPowerPolynomialDividedPowers A E).dpow n y)
  · exact 0

/-- The induced operations do not depend on the chosen finite-stage lift. -/
public theorem setIndexedDividedPowerPolynomialDpow_eq_of_lift
    (A : DividedPowerRing.{u}) (W : Type w)
    (n : ℕ) {x : setIndexedDividedPowerPolynomialAlgebra A W}
    (hx : x ∈ dividedPowerPolynomialIdeal A.ideal W)
    {E : Finset W} (y : DividedPowerAlgebra A (E →₀ A))
    (hy : finiteStageInclusion A E y = x)
    (hyI : y ∈ dividedPowerPolynomialIdeal A.ideal E) :
    setIndexedDividedPowerPolynomialDpow A W n x = finiteStageInclusion A E
      ((dividedPowerPolynomialDividedPowers A E).dpow n y) := by
  classical
  let h := exists_finiteStage_lift_mem_polynomialIdeal A W hx
  let E₀ := Classical.choose h
  let hE₀ := Classical.choose_spec h
  let y₀ := Classical.choose hE₀
  have hy₀ := Classical.choose_spec hE₀
  let G := E₀ ∪ E
  have h₀G : E₀ ⊆ G := Finset.subset_union_left
  have hEG : E ⊆ G := Finset.subset_union_right
  let z₀ := finiteStageMap A h₀G y₀
  let z := finiteStageMap A hEG y
  have hz₀ : finiteStageInclusion A G z₀ = x :=
    (finiteStageInclusion_finiteStageMap A h₀G y₀).trans hy₀.1
  have hz : finiteStageInclusion A G z = x :=
    (finiteStageInclusion_finiteStageMap A hEG y).trans hy
  have hzeq : z₀ = z := finiteStageInclusion_injective A G (hz₀.trans hz.symm)
  have hmap₀ := (finiteStageMap_isDPMorphism A h₀G).map_dpow
    (n := n) hy₀.2
  have hmap := (finiteStageMap_isDPMorphism A hEG).map_dpow (n := n) hyI
  unfold setIndexedDividedPowerPolynomialDpow
  rw [dite_eq_left hx]
  change finiteStageInclusion A E₀
      ((dividedPowerPolynomialDividedPowers A E₀).dpow n y₀) = _
  calc
    finiteStageInclusion A E₀
        ((dividedPowerPolynomialDividedPowers A E₀).dpow n y₀) =
      finiteStageInclusion A G
        (finiteStageMap A h₀G ((dividedPowerPolynomialDividedPowers A E₀).dpow n y₀)) :=
          (finiteStageInclusion_finiteStageMap A h₀G _).symm
    _ = finiteStageInclusion A G
        ((dividedPowerPolynomialDividedPowers A G).dpow n z₀) := by
          simpa [z₀] using congrArg (finiteStageInclusion A G) hmap₀
    _ = finiteStageInclusion A G
        ((dividedPowerPolynomialDividedPowers A G).dpow n z) := by rw [hzeq]
    _ = finiteStageInclusion A G
        (finiteStageMap A hEG ((dividedPowerPolynomialDividedPowers A E).dpow n y)) := by
          simpa [z] using congrArg (finiteStageInclusion A G) hmap.symm
    _ = finiteStageInclusion A E
        ((dividedPowerPolynomialDividedPowers A E).dpow n y) :=
          finiteStageInclusion_finiteStageMap A hEG _

/-- The divided powers on the distinguished ideal of the divided power polynomial algebra
on an arbitrary type of variables, induced from all finite-variable subalgebras. -/
@[stacks 07H6 "compatible_divided_powers"]
public noncomputable def setIndexedDividedPowerPolynomialDividedPowers
    (A : DividedPowerRing.{u}) (W : Type w) :
    _root_.DividedPowers (dividedPowerPolynomialIdeal A.ideal W) where
  dpow := setIndexedDividedPowerPolynomialDpow A W
  dpow_null {n x} hx := by
    simp [setIndexedDividedPowerPolynomialDpow, hx]
  dpow_zero {x} hx := by
    obtain ⟨E, y, rfl, hyI⟩ := exists_finiteStage_lift_mem_polynomialIdeal A W hx
    rw [setIndexedDividedPowerPolynomialDpow_eq_of_lift A W 0 hx y rfl hyI]
    rw [(dividedPowerPolynomialDividedPowers A E).dpow_zero hyI]
    simp
  dpow_one {x} hx := by
    obtain ⟨E, y, rfl, hyI⟩ := exists_finiteStage_lift_mem_polynomialIdeal A W hx
    rw [setIndexedDividedPowerPolynomialDpow_eq_of_lift A W 1 hx y rfl hyI]
    rw [(dividedPowerPolynomialDividedPowers A E).dpow_one hyI]
  dpow_mem {n x} hn hx := by
    obtain ⟨E, y, rfl, hyI⟩ := exists_finiteStage_lift_mem_polynomialIdeal A W hx
    rw [setIndexedDividedPowerPolynomialDpow_eq_of_lift A W n hx y rfl hyI]
    exact finiteStageInclusion_mem_polynomialIdeal A W E
      ((dividedPowerPolynomialDividedPowers A E).dpow_mem hn hyI)
  dpow_add {n x y} hx hy := by
    classical
    obtain ⟨E, xE, hxE, hxEI⟩ := exists_finiteStage_lift_mem_polynomialIdeal A W hx
    obtain ⟨F, yF, hyF, hyFI⟩ := exists_finiteStage_lift_mem_polynomialIdeal A W hy
    let G := E ∪ F
    let xG := finiteStageMap A (Finset.subset_union_left : E ⊆ G) xE
    let yG := finiteStageMap A (Finset.subset_union_right : F ⊆ G) yF
    have hxG : finiteStageInclusion A G xG = x :=
      (DFunLike.congr_fun
        (finiteStageInclusion_comp A (Finset.subset_union_left : E ⊆ G)) xE).trans hxE
    have hyG : finiteStageInclusion A G yG = y :=
      (DFunLike.congr_fun
        (finiteStageInclusion_comp A (Finset.subset_union_right : F ⊆ G)) yF).trans hyF
    have hxGI : xG ∈ dividedPowerPolynomialIdeal A.ideal G :=
      (finiteStageMap_isDPMorphism A Finset.subset_union_left).ideal_comp
        (Ideal.mem_map_of_mem (finiteStageMap A Finset.subset_union_left).toRingHom hxEI)
    have hyGI : yG ∈ dividedPowerPolynomialIdeal A.ideal G :=
      (finiteStageMap_isDPMorphism A Finset.subset_union_right).ideal_comp
        (Ideal.mem_map_of_mem (finiteStageMap A Finset.subset_union_right).toRingHom hyFI)
    have hsumG : finiteStageInclusion A G (xG + yG) = x + y := by
      rw [map_add, hxG, hyG]
    have hpowx (k : ℕ) : setIndexedDividedPowerPolynomialDpow A W k x = finiteStageInclusion A G
        ((dividedPowerPolynomialDividedPowers A G).dpow k xG) :=
      setIndexedDividedPowerPolynomialDpow_eq_of_lift A W k hx xG hxG hxGI
    have hpowy (k : ℕ) : setIndexedDividedPowerPolynomialDpow A W k y = finiteStageInclusion A G
        ((dividedPowerPolynomialDividedPowers A G).dpow k yG) :=
      setIndexedDividedPowerPolynomialDpow_eq_of_lift A W k hy yG hyG hyGI
    calc
      setIndexedDividedPowerPolynomialDpow A W n (x + y) = finiteStageInclusion A G
          ((dividedPowerPolynomialDividedPowers A G).dpow n (xG + yG)) :=
        setIndexedDividedPowerPolynomialDpow_eq_of_lift A W n
          ((dividedPowerPolynomialIdeal A.ideal W).add_mem hx hy) (xG + yG) hsumG
          ((dividedPowerPolynomialIdeal A.ideal G).add_mem hxGI hyGI)
      _ = (Finset.antidiagonal n).sum fun k =>
          (finiteStageInclusion A G
            ((dividedPowerPolynomialDividedPowers A G).dpow k.1 xG)) *
          (finiteStageInclusion A G
            ((dividedPowerPolynomialDividedPowers A G).dpow k.2 yG)) := by
          rw [(dividedPowerPolynomialDividedPowers A G).dpow_add hxGI hyGI,
            map_sum]
          simp only [map_mul]
      _ = (Finset.antidiagonal n).sum fun k =>
          setIndexedDividedPowerPolynomialDpow A W k.1 x *
            setIndexedDividedPowerPolynomialDpow A W k.2 y := by
          exact Finset.sum_congr rfl fun k _ => by rw [← hpowx k.1, ← hpowy k.2]
  dpow_mul {n a x} hx := by
    classical
    obtain ⟨E, xE, hxE, hxEI⟩ := exists_finiteStage_lift_mem_polynomialIdeal A W hx
    obtain ⟨F, aF, haF⟩ := exists_finiteStage_lift A W a
    let G := E ∪ F
    let xG := finiteStageMap A (Finset.subset_union_left : E ⊆ G) xE
    let aG := finiteStageMap A (Finset.subset_union_right : F ⊆ G) aF
    have hxG : finiteStageInclusion A G xG = x :=
      (DFunLike.congr_fun
        (finiteStageInclusion_comp A (Finset.subset_union_left : E ⊆ G)) xE).trans hxE
    have haG : finiteStageInclusion A G aG = a :=
      (DFunLike.congr_fun
        (finiteStageInclusion_comp A (Finset.subset_union_right : F ⊆ G)) aF).trans haF
    have hxGI : xG ∈ dividedPowerPolynomialIdeal A.ideal G :=
      (finiteStageMap_isDPMorphism A Finset.subset_union_left).ideal_comp
        (Ideal.mem_map_of_mem (finiteStageMap A Finset.subset_union_left).toRingHom hxEI)
    have haxG : finiteStageInclusion A G (aG * xG) = a * x := by
      rw [map_mul, haG, hxG]
    calc
      setIndexedDividedPowerPolynomialDpow A W n (a * x) = finiteStageInclusion A G
          ((dividedPowerPolynomialDividedPowers A G).dpow n (aG * xG)) :=
        setIndexedDividedPowerPolynomialDpow_eq_of_lift A W n
          ((dividedPowerPolynomialIdeal A.ideal W).mul_mem_left a hx) (aG * xG) haxG
          ((dividedPowerPolynomialIdeal A.ideal G).mul_mem_left aG hxGI)
      _ = finiteStageInclusion A G
          (aG ^ n * (dividedPowerPolynomialDividedPowers A G).dpow n xG) := by
          rw [(dividedPowerPolynomialDividedPowers A G).dpow_mul hxGI]
      _ = a ^ n * setIndexedDividedPowerPolynomialDpow A W n x := by
          rw [map_mul, map_pow, haG,
            setIndexedDividedPowerPolynomialDpow_eq_of_lift A W n hx xG hxG hxGI]
  mul_dpow {m n x} hx := by
    classical
    obtain ⟨E, xE, hxE, hxEI⟩ := exists_finiteStage_lift_mem_polynomialIdeal A W hx
    have hpow (k : ℕ) : setIndexedDividedPowerPolynomialDpow A W k x = finiteStageInclusion A E
        ((dividedPowerPolynomialDividedPowers A E).dpow k xE) :=
      setIndexedDividedPowerPolynomialDpow_eq_of_lift A W k hx xE hxE hxEI
    calc
      setIndexedDividedPowerPolynomialDpow A W m x *
            setIndexedDividedPowerPolynomialDpow A W n x =
          finiteStageInclusion A E
            (((dividedPowerPolynomialDividedPowers A E).dpow m xE) *
              ((dividedPowerPolynomialDividedPowers A E).dpow n xE)) := by
          rw [hpow m, hpow n, map_mul]
      _ = finiteStageInclusion A E
          ((Nat.choose (m + n) m : DividedPowerAlgebra A (E →₀ A)) *
            (dividedPowerPolynomialDividedPowers A E).dpow (m + n) xE) :=
          congrArg (finiteStageInclusion A E)
            ((dividedPowerPolynomialDividedPowers A E).mul_dpow hxEI)
      _ = (Nat.choose (m + n) m : setIndexedDividedPowerPolynomialAlgebra A W) *
          setIndexedDividedPowerPolynomialDpow A W (m + n) x := by
          rw [map_mul, map_natCast, hpow (m + n)]
  dpow_comp {m n x} hn hx := by
    classical
    obtain ⟨E, xE, hxE, hxEI⟩ := exists_finiteStage_lift_mem_polynomialIdeal A W hx
    have hpow (k : ℕ) : setIndexedDividedPowerPolynomialDpow A W k x = finiteStageInclusion A E
        ((dividedPowerPolynomialDividedPowers A E).dpow k xE) :=
      setIndexedDividedPowerPolynomialDpow_eq_of_lift A W k hx xE hxE hxEI
    have hinnerMem : (dividedPowerPolynomialDividedPowers A E).dpow n xE ∈
        dividedPowerPolynomialIdeal A.ideal E :=
      (dividedPowerPolynomialDividedPowers A E).dpow_mem hn hxEI
    have hmem : setIndexedDividedPowerPolynomialDpow A W n x ∈
        dividedPowerPolynomialIdeal A.ideal W := by
      rw [hpow n]
      exact finiteStageInclusion_mem_polynomialIdeal A W E hinnerMem
    calc
      setIndexedDividedPowerPolynomialDpow A W m
            (setIndexedDividedPowerPolynomialDpow A W n x) =
          finiteStageInclusion A E
            ((dividedPowerPolynomialDividedPowers A E).dpow m
              ((dividedPowerPolynomialDividedPowers A E).dpow n xE)) :=
        setIndexedDividedPowerPolynomialDpow_eq_of_lift A W m hmem
          ((dividedPowerPolynomialDividedPowers A E).dpow n xE)
          (hpow n).symm hinnerMem
      _ = finiteStageInclusion A E
          ((Nat.uniformBell m n : DividedPowerAlgebra A (E →₀ A)) *
            (dividedPowerPolynomialDividedPowers A E).dpow (m * n) xE) :=
          congrArg (finiteStageInclusion A E)
            ((dividedPowerPolynomialDividedPowers A E).dpow_comp hn hxEI)
      _ = (Nat.uniformBell m n : setIndexedDividedPowerPolynomialAlgebra A W) *
          setIndexedDividedPowerPolynomialDpow A W (m * n) x := by
          rw [map_mul, map_natCast, hpow (m * n)]

/-- The induced divided powers of an element of the ideal are computed through any finite-stage
lift of it lying in the ideal of that stage. -/
public theorem setIndexedDividedPowerPolynomialDividedPowers_dpow_eq_of_lift
    (A : DividedPowerRing.{u}) (W : Type w)
    (n : ℕ) {x : setIndexedDividedPowerPolynomialAlgebra A W}
    (hx : x ∈ dividedPowerPolynomialIdeal A.ideal W)
    {E : Finset W} (y : DividedPowerAlgebra A (E →₀ A))
    (hy : finiteStageInclusion A E y = x)
    (hyI : y ∈ dividedPowerPolynomialIdeal A.ideal E) :
    (setIndexedDividedPowerPolynomialDividedPowers A W).dpow n x =
      finiteStageInclusion A E
        ((dividedPowerPolynomialDividedPowers A E).dpow n y) :=
  setIndexedDividedPowerPolynomialDpow_eq_of_lift A W n hx y hy hyI

/-- The divided power polynomial algebra on an arbitrary set of variables, as a divided
power ring. -/
public noncomputable def setIndexedDividedPowerPolynomialDividedPowerRing
    (A : DividedPowerRing.{u}) (W : Type w) : DividedPowerRing.{max u w} :=
  .of (setIndexedDividedPowerPolynomialAlgebra A W)
    (dividedPowerPolynomialIdeal A.ideal W)
    (setIndexedDividedPowerPolynomialDividedPowers A W)

/-- Every finite-stage inclusion preserves divided powers induced on the colimit. -/
@[stacks 07H6 "compatible_divided_powers"]
public theorem finiteStageInclusion_isDPMorphism (A : DividedPowerRing.{u})
    {W : Type w} (E : Finset W) :
    _root_.DividedPowers.IsDPMorphism
      (dividedPowerPolynomialDividedPowers A E)
      (setIndexedDividedPowerPolynomialDividedPowers A W)
      (finiteStageInclusion A E).toRingHom := by
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun x hx =>
    finiteStageInclusion_mem_polynomialIdeal A W E hx, fun {n} x hx => ?_⟩
  change setIndexedDividedPowerPolynomialDpow A W n (finiteStageInclusion A E x) = _
  exact setIndexedDividedPowerPolynomialDpow_eq_of_lift A W n
    (finiteStageInclusion_mem_polynomialIdeal A W E hx) x rfl hx

/-- The induced divided powers send a variable to its divided power monomial. -/
@[stacks 07H6 "compatible_divided_powers"]
public theorem setIndexedDividedPowerPolynomialDividedPowers_dpow_variable
    (A : DividedPowerRing.{u}) {W : Type w} (i : W) (n : ℕ) :
    (setIndexedDividedPowerPolynomialDividedPowers A W).dpow n
        (dividedPowerPolynomialVariable A i) =
      dividedPowerPolynomialVariableMonomial A i n := by
  classical
  let E : Finset W := {i}
  let e : E := ⟨i, Finset.mem_singleton_self i⟩
  let y := dividedPowerPolynomialVariable A e
  have hy : finiteStageInclusion A E y = dividedPowerPolynomialVariable A i := by
    change finiteStageInclusion A E (dividedPowerPolynomialVariable A e) = _
    simpa [E, e, dividedPowerPolynomialVariable,
      dividedPowerPolynomialVariableMonomial] using
      (finiteStageInclusion_dp A E e 1)
  have hyI : y ∈ dividedPowerPolynomialIdeal A.ideal E := variable_mem_polynomialIdeal A e
  have hxI : dividedPowerPolynomialVariable A i ∈ dividedPowerPolynomialIdeal A.ideal W :=
    variable_mem_polynomialIdeal A i
  change setIndexedDividedPowerPolynomialDpow A W n (dividedPowerPolynomialVariable A i) = _
  rw [setIndexedDividedPowerPolynomialDpow_eq_of_lift A W n hxI y hy hyI]
  rw [dividedPowerPolynomialDividedPowers_dpow_variable A E e n]
  simpa [E, e, dividedPowerPolynomialVariable, dividedPowerPolynomialVariableMonomial]
    using (finiteStageInclusion_dp A E e n)

/-- The coefficient map is a morphism of divided power rings. -/
@[stacks 07H6 "compatible_divided_powers"]
public theorem setIndexedDividedPowerPolynomialCoefficient_isDPMorphism
    (A : DividedPowerRing.{u}) (W : Type w) :
    _root_.DividedPowers.IsDPMorphism A.dividedPowers
      (setIndexedDividedPowerPolynomialDividedPowers A W)
      (algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W)) := by
  let f := algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W)
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f a ∈ dividedPowerPolynomialIdeal A.ideal W
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem f ha)
  · intro n a ha
    let fE := algebraMap A (DividedPowerAlgebra A ((∅ : Finset W) →₀ A))
    have hfE : finiteStageInclusion A (∅ : Finset W) (fE a) = f a := by
      simp [fE, f, finiteStageInclusion]
    have haE : fE a ∈ dividedPowerPolynomialIdeal A.ideal (∅ : Finset W) :=
      (dividedPowerPolynomialCoefficient_isDPMorphism A (∅ : Finset W)).ideal_comp
        (Ideal.mem_map_of_mem fE ha)
    have hfa : f a ∈ dividedPowerPolynomialIdeal A.ideal W :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem f ha)
    change setIndexedDividedPowerPolynomialDpow A W n (f a) = f (A.dividedPowers.dpow n a)
    calc
      setIndexedDividedPowerPolynomialDpow A W n (f a) = finiteStageInclusion A (∅ : Finset W)
          ((dividedPowerPolynomialDividedPowers A (∅ : Finset W)).dpow n (fE a)) :=
        setIndexedDividedPowerPolynomialDpow_eq_of_lift A W n hfa (fE a) hfE haE
      _ = finiteStageInclusion A (∅ : Finset W)
          (algebraMap A (DividedPowerAlgebra A ((∅ : Finset W) →₀ A))
            (A.dividedPowers.dpow n a)) :=
          congrArg (finiteStageInclusion A (∅ : Finset W))
            ((dividedPowerPolynomialCoefficient_isDPMorphism A (∅ : Finset W)).map_dpow ha).symm
      _ = f (A.dividedPowers.dpow n a) := by
          simp [f, finiteStageInclusion]

/-- The canonical divided power morphism from the coefficient ring. -/
public def setIndexedDividedPowerPolynomialCoefficientDPMorphism
    (A : DividedPowerRing.{u}) (W : Type w) :
    _root_.DividedPowers.DPMorphism A.dividedPowers
      (setIndexedDividedPowerPolynomialDividedPowers A W) :=
  _root_.DividedPowers.DPMorphism.mk'
    (setIndexedDividedPowerPolynomialCoefficient_isDPMorphism A W)

/-- Compatibility with every finite stage uniquely determines the induced divided powers. -/
@[stacks 07H6 "compatible_divided_powers"]
public theorem setIndexedDividedPowerPolynomialDividedPowers_unique
    (A : DividedPowerRing.{u}) (W : Type w)
    (δ : _root_.DividedPowers (dividedPowerPolynomialIdeal A.ideal W))
    (hδ : ∀ E : Finset W,
      _root_.DividedPowers.IsDPMorphism (dividedPowerPolynomialDividedPowers A E) δ
        (finiteStageInclusion A E).toRingHom) :
    δ = setIndexedDividedPowerPolynomialDividedPowers A W := by
  apply _root_.DividedPowers.ext
  intro n x hx
  obtain ⟨E, y, rfl, hyI⟩ := exists_finiteStage_lift_mem_polynomialIdeal A W hx
  change δ.dpow n _ = setIndexedDividedPowerPolynomialDpow A W n _
  exact ((hδ E).map_dpow (n := n) hyI).symm.trans
    (setIndexedDividedPowerPolynomialDpow_eq_of_lift A W n hx y rfl hyI).symm

end DividedPowers

end
