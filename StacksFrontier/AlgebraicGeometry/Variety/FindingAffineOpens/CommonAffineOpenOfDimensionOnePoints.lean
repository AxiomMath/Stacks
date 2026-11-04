module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.GlueFinite
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.TensorProductCriterion
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfStalks

/-!
# A finite family of one-dimensional points lies in a common affine open

Let `X` be an integral separated scheme and let `x₁, …, x_r` be finitely many points of `X`
whose local rings are Noetherian of Krull dimension at most one. Then a single affine open
subscheme of `X` contains all of them.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_containing_of_stalk_krullDimLE_one`: the common affine
  open.

## Implementation notes

The finite family is given as a function from an arbitrary finite type, so repetitions are
allowed; they do not affect the conclusion. The bound on the local rings is expressed by
`Ring.KrullDimLE 1`.

## References

* [Stacks Project, Tag 09NJ](https://stacks.math.columbia.edu/tag/09NJ)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- On an integral scheme the local ring at a point other than the generic point is not a
field. -/
private lemma stalk_not_isField_of_ne_genericPoint (X : Scheme.{u}) [IsIntegral X]
    {x : X} (hx : x ≠ genericPoint X) :
    ¬ IsField (X.presheaf.stalk x) := by
  intro hfield
  let := hfield.toField
  have hsub : Subsingleton (PrimeSpectrum (X.presheaf.stalk x)) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.2 hfield
  have hgen : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  obtain ⟨y, hy⟩ := hgen
  have hy' : y = IsLocalRing.closedPoint (X.presheaf.stalk x) := hsub.elim _ _
  apply hx
  simpa [hy'] using hy

/-- On an integral scheme the local ring at a point other than the generic point, if of Krull
dimension at most one, has Krull dimension exactly one. -/
private lemma stalk_ringKrullDim_eq_one_of_not_genericPoint (X : Scheme.{u}) [IsIntegral X]
    {x : X} (hx : x ≠ genericPoint X)
    (h_dimension : Ring.KrullDimLE 1 (X.presheaf.stalk x)) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  let R := X.presheaf.stalk x
  have hnot : ¬ ringKrullDim R ≤ 0 := by
    intro h0
    apply stalk_not_isField_of_ne_genericPoint X hx
    let : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr h0
    exact Ring.KrullDimLE.isField_of_isDomain
  exact le_antisymm (Ring.krullDimLE_iff.mp h_dimension) (Order.succ_le_of_lt (lt_of_not_ge hnot))

/-- For local subrings `A ≤ O` of a field `K` with `K` the fraction field of `A` and `A` of
Krull dimension at most one, the inclusion is a local homomorphism as soon as `O` is not a
field. -/
private lemma subring_inclusion_isLocalHom_of_fractionRing_dimLE_one
    {K : Type u} [Field K] {A O : Subring K} [IsFractionRing A K]
    [IsLocalRing A] [IsLocalRing O] (h_dim : Ring.KrullDimLE 1 A)
    (hO : ¬ IsField O)
    (hAO : A ≤ O) : IsLocalHom (Subring.inclusion hAO) := by
  let f := Subring.inclusion hAO
  have hPne : (IsLocalRing.maximalIdeal O).comap f ≠ ⊥ := by
    intro hPbot
    have hunit (b : A) (hb : b ≠ 0) : IsUnit (f b) :=
      IsLocalRing.notMem_maximalIdeal.mp fun hmem => hb <| by
        simpa [hPbot] using show b ∈ (IsLocalRing.maximalIdeal O).comap f from hmem
    have hsubtype_surj : Function.Surjective (O.subtype : O →+* K) := by
      intro z
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A z
      let u : Units O := (hunit b (nonZeroDivisors.ne_zero hb)).unit
      refine ⟨f a * ↑u⁻¹, ?_⟩
      have hbK : ((u : O) : K) = (b : K) :=
        congrArg Subtype.val (hunit b (nonZeroDivisors.ne_zero hb)).unit_spec
      have hmul : (((u⁻¹ : Units O) : O) : K) * (b : K) = 1 := by
        rw [← hbK]
        exact congrArg Subtype.val (Units.inv_mul u)
      show (a : K) * (↑(u⁻¹) : K) = z
      rw [eq_inv_of_mul_eq_one_left hmul, ← div_eq_mul_inv]
      exact hab
    let e : O ≃+* K := RingEquiv.ofBijective O.subtype
      ⟨Subring.subtype_injective O, hsubtype_surj⟩
    exact hO (e.toMulEquiv.isField (Field.toIsField K))
  have hPprime : ((IsLocalRing.maximalIdeal O).comap f).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal O).isPrime.comap f
  let : Ring.KrullDimLE 1 A := h_dim
  have hPmax : ((IsLocalRing.maximalIdeal O).comap f).IsMaximal :=
    hPprime.isMaximal_of_ne_bot hPne
  have hP : (IsLocalRing.maximalIdeal O).comap f = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hPmax
  refine ⟨fun a hfa => IsLocalRing.notMem_maximalIdeal.1 fun ha =>
    IsLocalRing.notMem_maximalIdeal.2 hfa ?_⟩
  show a ∈ (IsLocalRing.maximalIdeal O).comap f
  rwa [hP]

/-- A local ring has finitely many maximal ideals, namely exactly one. -/
private lemma finite_maximalSpectrum_of_isLocalRing {R : Type*} [CommRing R]
    [IsLocalRing R] : Finite (MaximalSpectrum R) := by
  let : Subsingleton (MaximalSpectrum R) := ⟨fun x y => MaximalSpectrum.ext <|
    (IsLocalRing.eq_maximalIdeal x.isMaximal).trans (IsLocalRing.eq_maximalIdeal y.isMaximal).symm⟩
  infer_instance

/-- The image of a ring in its field of fractions has that field as its own field of
fractions. -/
private lemma isFractionRing_range_algebraMap {R K : Type*} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    IsFractionRing (algebraMap R K).range K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, hdiv⟩ := IsFractionRing.div_surjective R z
  exact ⟨⟨algebraMap R K a, ⟨a, rfl⟩⟩, ⟨algebraMap R K b, ⟨b, rfl⟩⟩, hdiv.symm⟩

/-- A subring of a field containing a subring with that field as fraction field again has it
as fraction field. -/
private lemma isFractionRing_of_subring_le {K : Type*} [Field K] {A O : Subring K}
    [IsFractionRing A K] (hAO : A ≤ O) : IsFractionRing O K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A z
  exact ⟨⟨a.1, hAO a.2⟩, ⟨b.1, hAO b.2⟩, hab.symm⟩

/-- A ring isomorphism is a local homomorphism. -/
private lemma ringEquiv_toRingHom_isLocalHom {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : IsLocalHom e.toRingHom :=
  ⟨fun _ ha => by simpa using ha.map e.symm.toRingHom⟩

/-- The local ring at a point of an integral scheme, identified with its image in the function
field. -/
private noncomputable def stalkRangeEquiv (X : Scheme.{u}) [IsIntegral X] (x : X) :
    X.presheaf.stalk x ≃+* (algebraMap (X.presheaf.stalk x) X.functionField).range :=
  RingEquiv.ofBijective (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨(fun _ _ hab => IsFractionRing.injective _ _ (congrArg Subtype.val hab)),
      RingHom.rangeRestrict_surjective (algebraMap (X.presheaf.stalk x) X.functionField)⟩

/-- A composite of morphisms of schemes induces an isomorphism on the stalk at a point whenever
both factors do. -/
private lemma isIso_stalkMap_comp_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hg : IsIso (g.stalkMap (f x))) (hf : IsIso (f.stalkMap x)) :
    IsIso ((f ≫ g).stalkMap x) := by
  rw [Scheme.Hom.stalkMap_comp]
  exact IsIso.comp_isIso' hg hf

/-- If a composite of morphisms of schemes induces an isomorphism on the stalk at a point, then
so does the composite of the stalk maps of its factors. -/
private lemma isIso_stalkMap_comp_stalkMap {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (h : IsIso ((f ≫ g).stalkMap x)) :
    IsIso (g.stalkMap (f x) ≫ f.stalkMap x) := by
  rwa [← Scheme.Hom.stalkMap_comp]

/-- **[Stacks, Tag 09NJ]** A finite family of points on an integral separated scheme,
whose local rings are Noetherian of Krull dimension at most one, lies in a common affine open.
-/
@[stacks 09NJ]
theorem exists_isAffineOpen_containing_of_stalk_krullDimLE_one
    (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
    {ι : Type v} [Finite ι] (x : ι → X)
    (h_noetherian : ∀ i, IsNoetherianRing (X.presheaf.stalk (x i)))
    (h_dimension : ∀ i, Ring.KrullDimLE 1 (X.presheaf.stalk (x i))) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  classical
  let := Fintype.ofFinite ι
  by_cases hgeneric : ∀ i, x i = genericPoint X
  · obtain ⟨U, hU, hηU, _⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint X) (by simp)
    exact ⟨U, hU, fun i => by simpa [hgeneric i] using hηU⟩
  · let J : Type u := {y : X // y ∈ Set.range x ∧ y ≠ genericPoint X}
    have hrange : (Set.range x).Finite := Set.finite_range x
    let : Fintype (Set.range x) := hrange.fintype
    let : Finite J := Finite.of_injective
      (fun y : J => (⟨y.1, y.2.1⟩ : Set.range x))
      fun _ _ hyz => Subtype.ext (congrArg (fun q : Set.range x => (q : X)) hyz)
    let x' : J → X := fun y => y.1
    have hJne : Nonempty J := by
      obtain ⟨i, hi⟩ := not_forall.mp hgeneric
      exact ⟨⟨x i, ⟨⟨i, rfl⟩, hi⟩⟩⟩
    let K := X.functionField
    let B : J → Subring K := fun j => (algebraMap (X.presheaf.stalk (x' j)) K).range
    have hstalkN (j : J) : IsNoetherianRing (X.presheaf.stalk (x' j)) := by
      obtain ⟨i, hi⟩ := j.2.1
      show IsNoetherianRing (X.presheaf.stalk j.1)
      rw [← hi]
      exact h_noetherian i
    have hstalkDim (j : J) : Ring.KrullDimLE 1 (X.presheaf.stalk (x' j)) := by
      obtain ⟨i, hi⟩ := j.2.1
      show Ring.KrullDimLE 1 (X.presheaf.stalk j.1)
      rw [← hi]
      exact h_dimension i
    have (j : J) : IsFractionRing (B j) K := isFractionRing_range_algebraMap
    have (j : J) : IsNoetherianRing (B j) := by
      let : IsNoetherianRing (X.presheaf.stalk (x' j)) := hstalkN j
      exact isNoetherianRing_of_ringEquiv _ (stalkRangeEquiv X (x' j))
    have (j : J) : IsLocalRing (B j) := (stalkRangeEquiv X (x' j)).isLocalRing
    have (j : J) : Finite (MaximalSpectrum (B j)) :=
      finite_maximalSpectrum_of_isLocalRing
    have hdimB (j : J) : ringKrullDim (B j) = 1 := by
      calc
        ringKrullDim (B j) = ringKrullDim (X.presheaf.stalk (x' j)) :=
          (ringKrullDim_eq_of_ringEquiv (stalkRangeEquiv X (x' j))).symm
        _ = 1 := stalk_ringKrullDim_eq_one_of_not_genericPoint X j.2.2 (hstalkDim j)
    have hsurj : ∀ j k : J, j ≠ k → Function.Surjective
        (Algebra.TensorProduct.lift (B := B k) (B j).subtype.toIntAlgHom
          (B k).subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
      intro j k hjk
      by_contra h
      obtain ⟨O, hO, hj, hk⟩ :=
        (Subring.not_surjective_tensorProduct_iff_exists_isDiscreteValuationRing
          (B j) (B k) (hdimB j)).mp h
      let : IsFractionRing O K := isFractionRing_of_subring_le hj
      let v := (IsDiscreteValuationRing.maximalIdeal O).valuation K
      let V := v.valuationSubring
      let e : O ≃+* V := IsDiscreteValuationRing.equivValuationSubring (A := O) (K := K)
      have heval (z : O) : ((e z : V) : K) = (z : K) := rfl
      have : IsLocalHom e.toRingHom := ringEquiv_toRingHom_isLocalHom e
      have key (m : J) (hm : B m ≤ O) : ∃ l : Spec (.of V) ⟶ X,
          Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l = X.fromSpecStalk (genericPoint X) ∧
            l (IsLocalRing.closedPoint (CommRingCat.of V)) = x' m := by
        have : IsLocalHom (stalkRangeEquiv X (x' m)).toRingHom :=
          ringEquiv_toRingHom_isLocalHom _
        have : IsLocalHom (Subring.inclusion hm) :=
          subring_inclusion_isLocalHom_of_fractionRing_dimLE_one
            (Ring.krullDimLE_iff.mpr (by simp [hdimB m]))
            (IsDiscreteValuationRing.not_isField O) hm
        let ψ : X.presheaf.stalk (x' m) →+* V :=
          e.toRingHom.comp ((Subring.inclusion hm).comp (stalkRangeEquiv X (x' m)).toRingHom)
        have : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
        have hmap : (algebraMap V K).comp ψ = algebraMap (X.presheaf.stalk (x' m)) K := by
          ext a
          show ((e ((Subring.inclusion hm) ((stalkRangeEquiv X (x' m)) a)) : V) : K) = _
          rw [heval]
          show ((algebraMap (X.presheaf.stalk (x' m)) K).rangeRestrict a : K) = _
          rfl
        refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk (x' m), ?_, ?_⟩
        · rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hmap]
          exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
            ((genericPoint_spec X).specializes trivial)
        · show X.fromSpecStalk (x' m)
            ((Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint (CommRingCat.of V))) = _
          rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
      obtain ⟨lj, hjgeneric, hjclosed⟩ := key j hj
      obtain ⟨lk, hkgeneric, hkclosed⟩ := key k hk
      let f : X ⟶ ⊤_ Scheme := CategoryTheory.Limits.terminal.from X
      let S : ValuativeCommSq f := {
        R := V
        K := K
        i₁ := X.fromSpecStalk (genericPoint X)
        i₂ := CategoryTheory.Limits.terminal.from (Spec (.of V))
        commSq := ⟨Subsingleton.elim _ _⟩
      }
      let hjlift : S.commSq.LiftStruct := ⟨lj, hjgeneric, Subsingleton.elim _ _⟩
      let hklift : S.commSq.LiftStruct := ⟨lk, hkgeneric, Subsingleton.elim _ _⟩
      have hlift : lj = lk := by
        have hsep : Subsingleton S.commSq.LiftStruct :=
          IsSeparated.valuativeCriterion f S
        simpa [hjlift, hklift] using
          congrArg CommSq.LiftStruct.l (Subsingleton.elim hjlift hklift)
      have h := congrArg (fun g : Spec (.of V) ⟶ X =>
        g (IsLocalRing.closedPoint (CommRingCat.of V))) hlift
      rw [hjclosed, hkclosed] at h
      exact hjk (Subtype.ext h)
    let R : Subring K := Subring.gluedSubring B
    let T := Spec (.of R)
    have : IsAffine T := isAffine_Spec _
    let g (j : J) : Spec (.of (B j)) ⟶ T :=
      Spec.map (CommRingCat.ofHom (Subring.gluedSubringInclusion B j))
    have (j : J) : IsOpenImmersion (g j) :=
      Subring.isOpenImmersion_specMap_gluedSubringInclusion B hdimB hsurj j
    let U (j : J) : T.Opens := (g j).opensRange
    have hsets : (⋃ j, Set.range (g j)) = Set.univ := by
      have hs := Subring.iUnion_range_comap_gluedSubringInclusion B hdimB hsurj
      refine Set.eq_univ_of_forall fun x => ?_
      let p : PrimeSpectrum R :=
        (AlgebraicGeometry.primeSpectrumOrderIsoSpec R).symm (OrderDual.toDual x)
      have hp : p ∈ Set.univ := Set.mem_univ _
      rw [← hs] at hp
      obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
      obtain ⟨q, hq⟩ := Set.mem_range.mp hpj
      refine Set.mem_iUnion.mpr ⟨j, OrderDual.ofDual
        (AlgebraicGeometry.primeSpectrumOrderIsoSpec (B j) q), ?_⟩
      apply (AlgebraicGeometry.primeSpectrumOrderIsoSpec R).symm.injective
      exact hq
    have hU : TopologicalSpace.IsOpenCover U := by
      rw [TopologicalSpace.IsOpenCover]
      apply TopologicalSpace.Opens.ext
      simpa [U, Scheme.Hom.coe_opensRange] using hsets
    let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover U hU
    let e (j : J) : Spec (.of (B j)) ≅ U j :=
      IsOpenImmersion.isoOfRangeEq (g j) ((U j).ι) (by simp [U])
    let l (j : J) : (U j).toScheme ⟶ X :=
      (e j).inv ≫ Spec.map (CommRingCat.ofHom (stalkRangeEquiv X (x' j)).toRingHom) ≫
        X.fromSpecStalk (x' j)
    let qT : Spec (.of K) ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap R K))
    have hqη : qT (genericPoint (Spec (.of K))) = genericPoint T := by
      show PrimeSpectrum.comap (algebraMap R K) (genericPoint (Spec (.of K))) =
        genericPoint T
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R K) ⊥ = ⊥
      exact Ideal.comap_bot_of_injective _ fun _ _ => Subtype.ext
    have hηrange : genericPoint T ∈ Set.range qT := ⟨genericPoint (Spec (.of K)), hqη⟩
    have hTdom : IsDominant qT := by
      rw [AlgebraicGeometry.isDominant_iff, denseRange_iff_closure_range]
      exact Set.eq_univ_of_univ_subset ((genericPoint_spec T).def.symm.le.trans
        (closure_mono (Set.singleton_subset_iff.mpr hηrange)))
    have hmap (j : J) :
        (algebraMap (B j) K).comp (stalkRangeEquiv X (x' j)).toRingHom =
          algebraMap (X.presheaf.stalk (x' j)) K := by
      ext a
      show ((algebraMap (X.presheaf.stalk (x' j)) K).rangeRestrict a : K) = _
      rfl
    let q (j : J) : Spec (.of K) ⟶ (U j).toScheme :=
      Spec.map (CommRingCat.ofHom (algebraMap (B j) K)) ≫ (e j).hom
    have hqT (j : J) : q j ≫ (U j).ι = qT := by
      calc
        q j ≫ (U j).ι = Spec.map (CommRingCat.ofHom (algebraMap (B j) K)) ≫ g j := by
          dsimp [q, e]
          simp only [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
        _ = qT := by
          dsimp [qT, g]
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 1
    have hqX (j : J) : q j ≫ l j = X.fromSpecStalk (genericPoint X) := by
      calc
        q j ≫ l j = Spec.map (CommRingCat.ofHom (algebraMap (B j) K)) ≫
            Spec.map (CommRingCat.ofHom (stalkRangeEquiv X (x' j)).toRingHom) ≫
            X.fromSpecStalk (x' j) := by
          dsimp [q, l, e]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
        _ = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (x' j)) K)) ≫
            X.fromSpecStalk (x' j) := by
          rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hmap j]
        _ = X.fromSpecStalk (genericPoint X) :=
          Scheme.SpecMap_stalkSpecializes_fromSpecStalk
            ((genericPoint_spec X).specializes trivial)
    let : IsIntegral T := by
      dsimp [T]
      infer_instance
    have hcompat (j k : J) :
        pullback.fst ((U j).ι) ((U k).ι) ≫ l j =
          pullback.snd ((U j).ι) ((U k).ι) ≫ l k := by
      let p := pullback ((U j).ι) ((U k).ι)
      let q' : Spec (.of K) ⟶ p := pullback.lift (q j) (q k) (by
        rw [hqT j, hqT k])
      have : IsReduced p := AlgebraicGeometry.isReduced_of_isOpenImmersion
        (pullback.fst ((U j).ι) ((U k).ι) ≫ (U j).ι)
      have hq'dom : IsDominant q' := by
        have : IsDominant (q' ≫ pullback.fst ((U j).ι) ((U k).ι) ≫ (U j).ι) := by
          rw [pullback.lift_fst_assoc, hqT]
          exact hTdom
        exact IsDominant.of_comp_of_isOpenImmersion q'
          (pullback.fst ((U j).ι) ((U k).ι) ≫ (U j).ι)
      apply AlgebraicGeometry.ext_of_isDominant q'
      calc
        q' ≫ pullback.fst ((U j).ι) ((U k).ι) ≫ l j = q j ≫ l j := by
          simp only [q', pullback.lift_fst_assoc]
        _ = X.fromSpecStalk (genericPoint X) := hqX j
        _ = q k ≫ l k := (hqX k).symm
        _ = q' ≫ pullback.snd ((U j).ι) ((U k).ι) ≫ l k := by
          simp only [q', pullback.lift_snd_assoc]
    let f : T ⟶ X := 𝒰.glueMorphisms l hcompat
    have hf (j : J) : (U j).ι ≫ f = l j := 𝒰.ι_glueMorphisms l hcompat j
    have hqf : qT ≫ f = X.fromSpecStalk (genericPoint X) := by
      obtain ⟨j⟩ := hJne
      calc
        qT ≫ f = q j ≫ (U j).ι ≫ f := by
          rw [← hqT j]
          simp [Category.assoc]
        _ = q j ≫ l j := by rw [hf]
        _ = X.fromSpecStalk (genericPoint X) := hqX j
    have hKpt : genericPoint (Spec (.of K)) = IsLocalRing.closedPoint (↑K) := by
      apply PrimeSpectrum.ext
      rw [genericPoint_eq_bot_of_affine]
      show (⊥ : Ideal (↑K)) = IsLocalRing.maximalIdeal (↑K)
      rw [IsLocalRing.maximalIdeal_eq_bot]
    have hgeneric : Set.MapsTo f (genericPoints T) (genericPoints X) := by
      rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
      intro y hy
      rw [Set.mem_singleton_iff] at hy ⊢
      subst y
      have h := congrArg (fun g : Spec (.of K) ⟶ X => g (genericPoint (Spec (.of K)))) hqf
      rw [Scheme.Hom.comp_apply, hqη, hKpt] at h
      change f (genericPoint T) =
        (X.fromSpecStalk (genericPoint X))
          (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))) at h
      rw [Scheme.fromSpecStalk_closedPoint] at h
      exact h
    have hinj : Set.InjOn f (genericPoints T) := by
      intro a ha b hb _
      rw [genericPoints_eq_singleton] at ha hb
      exact ha.trans hb.symm
    let t : J → T := fun j => g j (IsLocalRing.closedPoint (B j))
    have hgf (j : J) : g j ≫ f =
        Spec.map (CommRingCat.ofHom (stalkRangeEquiv X (x' j)).toRingHom) ≫
          X.fromSpecStalk (x' j) := by
      calc
        g j ≫ f = (e j).hom ≫ (U j).ι ≫ f := by simp [g, e]
        _ = (e j).hom ≫ l j := by rw [hf j]
        _ = Spec.map (CommRingCat.ofHom (stalkRangeEquiv X (x' j)).toRingHom) ≫
              X.fromSpecStalk (x' j) := by simp [l]
    let s (j : J) := Spec.map (CommRingCat.ofHom (stalkRangeEquiv X (x' j)).toRingHom)
    have hspt (j : J) : s j (IsLocalRing.closedPoint (B j)) =
        IsLocalRing.closedPoint (X.presheaf.stalk (x' j)) := by
      dsimp [s]
      let : IsLocalHom (stalkRangeEquiv X (x' j)).toRingHom :=
        ringEquiv_toRingHom_isLocalHom _
      exact IsLocalRing.comap_closedPoint (stalkRangeEquiv X (x' j)).toRingHom
    have hpoint (j : J) : f (t j) = x' j := by
      have h := congrArg (fun h : Spec (.of (B j)) ⟶ X => h (IsLocalRing.closedPoint (B j)))
        (hgf j)
      change f (t j) = (s j ≫ X.fromSpecStalk (x' j))
        (IsLocalRing.closedPoint (B j)) at h
      change f (t j) = X.fromSpecStalk (x' j)
        (s j (IsLocalRing.closedPoint (B j))) at h
      rw [hspt j] at h
      exact h.trans (Scheme.fromSpecStalk_closedPoint)
    have hstalk (j : J) : IsIso (f.stalkMap (t j)) := by
      have hfrom : IsIso ((X.fromSpecStalk (x' j)).stalkMap
          (IsLocalRing.closedPoint (X.presheaf.stalk (x' j)))) := by
        have hcomp : IsIso ((X.fromSpecStalk (x' j)).stalkMap
            (IsLocalRing.closedPoint (X.presheaf.stalk (x' j))) ≫
              (stalkClosedPointIso (X.presheaf.stalk (x' j))).hom) := by
          show IsIso (Scheme.stalkClosedPointTo (X.fromSpecStalk (x' j)))
          rw [Scheme.stalkClosedPointTo_fromSpecStalk]
          infer_instance
        exact IsIso.of_isIso_comp_right
          ((X.fromSpecStalk (x' j)).stalkMap
            (IsLocalRing.closedPoint (X.presheaf.stalk (x' j))))
          ((stalkClosedPointIso (X.presheaf.stalk (x' j))).hom)
      have : IsIso (CommRingCat.ofHom (stalkRangeEquiv X (x' j)).toRingHom) :=
        (stalkRangeEquiv X (x' j)).toCommRingCatIso.isIso_hom
      have : IsIso (s j) := by
        dsimp [s]
        exact (Scheme.Spec.mapIso (stalkRangeEquiv X (x' j)).toCommRingCatIso.op).isIso_hom
      have : IsIso ((s j).stalkMap (IsLocalRing.closedPoint (B j))) :=
        ((isIso_iff_isIso_stalkMap (s j)).mp inferInstance).2 _
      have hfrom' : IsIso ((X.fromSpecStalk (x' j)).stalkMap
          (s j (IsLocalRing.closedPoint (B j)))) := by
        rw [hspt j]
        exact hfrom
      have hscomp : IsIso ((s j ≫ X.fromSpecStalk (x' j)).stalkMap
          (IsLocalRing.closedPoint (B j))) :=
        isIso_stalkMap_comp_of_isIso (s j) (X.fromSpecStalk (x' j))
          (IsLocalRing.closedPoint (B j)) hfrom' inferInstance
      have : IsIso ((g j).stalkMap (IsLocalRing.closedPoint (B j))) :=
        (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion (g j))).2 _
      have hcomp : IsIso ((g j ≫ f).stalkMap (IsLocalRing.closedPoint (B j))) := by
        rw [hgf]
        infer_instance
      have : IsIso (f.stalkMap (g j (IsLocalRing.closedPoint (B j)))) := by
        have hcomp' : IsIso (f.stalkMap (g j (IsLocalRing.closedPoint (B j))) ≫
            (g j).stalkMap (IsLocalRing.closedPoint (B j))) :=
          isIso_stalkMap_comp_stalkMap (g j) f (IsLocalRing.closedPoint (B j)) hcomp
        exact IsIso.of_isIso_comp_right
          (f.stalkMap (g j (IsLocalRing.closedPoint (B j))))
          ((g j).stalkMap (IsLocalRing.closedPoint (B j)))
      simpa [t] using (inferInstance : IsIso
        (f.stalkMap (g j (IsLocalRing.closedPoint (B j)))))
    have hfinite : (genericPoints X).Finite := by
      rw [genericPoints_eq_singleton]
      exact Set.finite_singleton _
    obtain ⟨U, hUaff, hUt⟩ := exists_isAffineOpen_containing_image_of_genericPoints_injOn
      f hfinite hgeneric hinj t hstalk
    have hηU : genericPoint X ∈ U := by
      obtain ⟨j⟩ := hJne
      have hx : x' j ∈ U := hpoint j ▸ hUt j
      exact ((genericPoint_spec X).specializes trivial).mem_open U.2 hx
    refine ⟨U, hUaff, fun i => ?_⟩
    by_cases hi : x i = genericPoint X
    · simpa [hi] using hηU
    · let j : J := ⟨x i, ⟨⟨i, rfl⟩, hi⟩⟩
      have hiU : f (t j) ∈ U := hUt j
      simpa [j, hpoint j] using hiU

end AlgebraicGeometry
