module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.ProperPushforward

/-!
# The bivariant class of a Chow class over a Dedekind base

Let `(S, δ)` be as in Stacks section 42.63 and let `X` be locally of finite type over `S`. For
`α ∈ CH_{1-p}(X)` the proof of Stacks 0FC5 defines `c_α ∈ A^p(X ⟶ S)` by

  `c_α ∩ α' = α × α'`   in   `CH_{k-p}(X ×_S T)`

for every `T ⟶ S` locally of finite type and `α' ∈ CH_k(T)`, where `×` is the exterior product
of Stacks 0FC4. This file proves that this rule is a bivariant class (Stacks 0B76).

## Main definitions

* `Stacks.Chow.dedekindExteriorCap`: the rule `α' ↦ α × α'` at a test scheme.
* `Stacks.Chow.dedekindExteriorClass`: the bivariant class `c_α ∈ A^p(X ⟶ S)`.

## Main results

* `Stacks.Chow.dedekindExteriorCap_properPushforward`: the rule `α' ↦ α × α'` commutes with
  proper pushforward.
* `Stacks.Chow.exteriorProductDedekindChowTensor_flatPullbackChow`: the exterior product commutes
  with flat pullback in the second variable.
* `Stacks.Chow.exteriorProductDedekindChowTensor_gysinChowOfInvertible`: the exterior product
  commutes with Gysin maps in the second variable.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Tag 0FC7](https://stacks.math.columbia.edu/tag/0FC7)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Heterogeneous equality of exterior products -/

section Bookkeeping

variable {C : ChowSituation.{u}}

variable (hC : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The exterior product over a Dedekind base respects equalities of the structure morphism of
the second factor, of the degree and of the second argument. -/
theorem exteriorProductDedekindChowTensor_heq {T : Scheme.{u}} {g g' : T ⟶ C.S}
    [LocallyOfFiniteType g] [LocallyOfFiniteType g'] (hg : g = g') (n : ℤ) {m m' : ℤ}
    (hm : m = m') (α : chowGroup C sX n) (β : chowGroup C g m) (β' : chowGroup C g' m')
    (hβ : β ≍ β') :
    exteriorProductDedekindChowTensor C sX g n m hC (α ⊗ₜ[ℤ] β) ≍
      exteriorProductDedekindChowTensor C sX g' n m' hC (α ⊗ₜ[ℤ] β') := by
  subst hg hm
  obtain rfl := eq_of_heq hβ
  rfl

end Bookkeeping

/-! ### The rule `α' ↦ α × α'` -/

section Cap

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ) (α : chowGroup C sX (1 - p))

/-- The cap operation of `c_α` at a test scheme `g : T ⟶ S`: the exterior product
`α' ↦ α × α'`, read in degree `k - p`. -/
def dedekindExteriorCap {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ 𝟙 C.S) k →+ chowGroup C (pullback.fst sX g ≫ sX) (k - p) :=
  (chowGroupDegreeEquiv C (pullback.fst sX g ≫ sX)
      (by ring : 1 - p + k - 1 = k - p)).toAddMonoidHom.comp
    ((exteriorProductDedekindChowTensor C sX g (1 - p) k hC).comp
      ((TensorProduct.mk ℤ (chowGroup C sX (1 - p)) (chowGroup C g k) α).toAddMonoidHom.comp
        (chowGroupCongr C (Category.comp_id g) k).toAddMonoidHom))

/-- The value of `Stacks.Chow.dedekindExteriorCap` at `β` is the exterior product `α × β`,
re-indexed to degree `k - p`. -/
theorem dedekindExteriorCap_apply {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (g ≫ 𝟙 C.S) k) :
    dedekindExteriorCap hC sX p α g k β =
      chowGroupDegreeEquiv C (pullback.fst sX g ≫ sX) (by ring : 1 - p + k - 1 = k - p)
        (exteriorProductDedekindChowTensor C sX g (1 - p) k hC
          (α ⊗ₜ[ℤ] chowGroupCongr C (Category.comp_id g) k β)) :=
  rfl

/-- The cap operation of `c_α` is heterogeneously the exterior product with `α`. -/
theorem dedekindExteriorCap_heq {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (g ≫ 𝟙 C.S) k) :
    dedekindExteriorCap hC sX p α g k β ≍
      exteriorProductDedekindChowTensor C sX g (1 - p) k hC
        (α ⊗ₜ[ℤ] chowGroupCongr C (Category.comp_id g) k β) :=
  chowGroupDegreeEquiv_heq C _ _ _

/-- **Condition (1) of Stacks 0B76 for `c_α`.** The rule `α' ↦ α × α'` commutes with proper
pushforward along a morphism of test schemes. -/
theorem dedekindExteriorCap_properPushforward {T T' : Scheme.{u}} (g : T ⟶ C.S)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (k : ℤ)
    (β : chowGroup C ((h ≫ g) ≫ 𝟙 C.S) k) :
    dedekindExteriorCap hC sX p α g k (properChowPushforward C ((h ≫ g) ≫ 𝟙 C.S) (g ≫ 𝟙 C.S) h
        (Category.assoc _ _ _).symm k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C ((h ≫ g) ≫ 𝟙 C.S)
          (g ≫ 𝟙 C.S) h (Category.assoc _ _ _).symm k) β) =
      properChowPushforward C (pullback.fst sX (h ≫ g) ≫ sX) (pullback.fst sX g ≫ sX)
        (bivariantBaseChangeMap sX g h)
        (bivariantBaseChangeMap_comp_structureMorphism sX sX g h) (k - p)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
          (pullback.fst sX (h ≫ g) ≫ sX) (pullback.fst sX g ≫ sX) (bivariantBaseChangeMap sX g h)
          (bivariantBaseChangeMap_comp_structureMorphism sX sX g h) (k - p))
        (dedekindExteriorCap hC sX p α (h ≫ g) k β) := by
  rw [dedekindExteriorCap_apply, dedekindExteriorCap_apply,
    properChowPushforward_chowGroupCongr C (Category.comp_id (h ≫ g)) (Category.comp_id g) h _ rfl
      k _ (properPushforwardDescends C _ _ _ _ _),
    exteriorProductDedekindChowTensor_properChowPushforward hC sX g h (1 - p) k]
  exact chowGroupDegreeEquiv_properChowPushforward_comp C _ _ _ _ _ _ _ _

end Cap

/-! ### Stacks 0FC7 at a presentation of the test morphisms -/

section CapComm

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z)
  [LocallyOfFiniteType w]

/-- The canonical morphism `X ×_S (Y ×_Z T) ⟶ Y ×_Z (X ×_S T)` of
`Stacks.Chow.mixedCommuteHom`, with the structure morphism `qT` of the test scheme and the test
morphism `t'` of `X ×_S T` given as morphisms equal to `t ≫ sZ` and `pullback.snd sX qT ≫ t`. -/
def mixedCommuteHomOfEq {T : Scheme.{u}} (t : T ⟶ Z) (qT : T ⟶ C.S) (hqT : t ≫ sZ = qT)
    (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    pullback sX (pullback.fst w t ≫ (w ≫ sZ)) ⟶ pullback w t' :=
  pullback.lift (pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ pullback.fst w t)
    (pullback.lift (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)))
      (pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ pullback.snd w t)
      (by
        rw [pullback.condition (f := sX) (g := pullback.fst w t ≫ (w ≫ sZ)), ← hqT]
        simp only [Category.assoc]
        rw [← Category.assoc (pullback.fst w t) w sZ, pullback.condition (f := w) (g := t),
          Category.assoc]))
    (by
      rw [← ht', pullback.lift_snd_assoc]
      simp only [Category.assoc, pullback.condition])

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- At `qT = t ≫ sZ` and `t' = pullback.snd sX (t ≫ sZ) ≫ t`, `Stacks.Chow.mixedCommuteHomOfEq` is
`Stacks.Chow.mixedCommuteHom`. -/
theorem mixedCommuteHomOfEq_eq {T : Scheme.{u}} (t : T ⟶ Z) :
    mixedCommuteHomOfEq sX sZ w t (t ≫ sZ) rfl (pullback.snd sX (t ≫ sZ) ≫ t) rfl =
      mixedCommuteHom sX sZ w t := by
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;>
    simp [mixedCommuteHomOfEq, mixedCommuteHom, mixedCommuteSnd]

/-- `Stacks.Chow.mixedCommuteHomOfEq` is an isomorphism. -/
instance isIso_mixedCommuteHomOfEq {T : Scheme.{u}} (t : T ⟶ Z) (qT : T ⟶ C.S)
    (hqT : t ≫ sZ = qT) (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    IsIso (mixedCommuteHomOfEq sX sZ w t qT hqT t' ht') := by
  subst hqT ht'
  rw [mixedCommuteHomOfEq_eq]
  infer_instance

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- The composite of `Stacks.Chow.mixedCommuteHomOfEq` with the projection to `Y`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteHomOfEq_fst {T : Scheme.{u}} (t : T ⟶ Z) (qT : T ⟶ C.S)
    (hqT : t ≫ sZ = qT) (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    mixedCommuteHomOfEq sX sZ w t qT hqT t' ht' ≫ pullback.fst w t' =
      pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ pullback.fst w t :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- The composite of `Stacks.Chow.mixedCommuteHomOfEq` with the projection to `X`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteHomOfEq_snd_fst {T : Scheme.{u}} (t : T ⟶ Z) (qT : T ⟶ C.S)
    (hqT : t ≫ sZ = qT) (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    mixedCommuteHomOfEq sX sZ w t qT hqT t' ht' ≫ pullback.snd w t' ≫ pullback.fst sX qT =
      pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) := by
  rw [mixedCommuteHomOfEq, pullback.lift_snd_assoc, pullback.lift_fst]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- The composite of `Stacks.Chow.mixedCommuteHomOfEq` with the projection to `T`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteHomOfEq_snd_snd {T : Scheme.{u}} (t : T ⟶ Z) (qT : T ⟶ C.S)
    (hqT : t ≫ sZ = qT) (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    mixedCommuteHomOfEq sX sZ w t qT hqT t' ht' ≫ pullback.snd w t' ≫ pullback.snd sX qT =
      pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ pullback.snd w t := by
  rw [mixedCommuteHomOfEq, pullback.lift_snd_assoc, pullback.lift_snd]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- `Stacks.Chow.mixedCommuteHomOfEq` commutes with the structure morphisms to `S`. -/
theorem mixedCommuteHomOfEq_comp_structureMorphism {T : Scheme.{u}} (t : T ⟶ Z)
    (qT : T ⟶ C.S) (hqT : t ≫ sZ = qT) (t' : pullback sX qT ⟶ Z)
    (ht' : pullback.snd sX qT ≫ t = t') :
    mixedCommuteHomOfEq sX sZ w t qT hqT t' ht' ≫ (pullback.fst w t' ≫ (w ≫ sZ)) =
      pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX := by
  rw [mixedCommuteHomOfEq_fst_assoc]
  exact (pullback.condition (f := sX) (g := pullback.fst w t ≫ (w ≫ sZ))).symm

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] in
/-- The structure morphism `X ×_S T ⟶ X ⟶ S` equals `t' ≫ sZ`. -/
theorem pullbackFst_comp_structureMorphism_of_eq {T : Scheme.{u}} (t : T ⟶ Z) (qT : T ⟶ C.S)
    (hqT : t ≫ sZ = qT) (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    pullback.fst sX qT ≫ sX = t' ≫ sZ := by
  rw [← ht', Category.assoc, hqT, pullback.condition]

variable (n m q : ℤ) (c' : CanonicalBivariantClass C (w ≫ sZ) sZ w rfl q)

include hC in
/-- **Stacks 0FC7, at a presentation of the test morphisms.** The identity
`α × (c' ∩ β) = c' ∩ (α × β)` of `Stacks.Chow.exteriorProductDedekindChowTensor_cap_comm`, with
the structure morphism `qT` of the test scheme and the test morphism `t'` of `X ×_S T` given as
morphisms equal to `t ≫ sZ` and `pr ≫ t`. -/
theorem exteriorProductDedekindChowTensor_cap_comm_of_eq {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (qT : T ⟶ C.S) [LocallyOfFiniteType qT] (hqT : t ≫ sZ = qT)
    (t' : pullback sX qT ⟶ Z) [LocallyOfFiniteType t'] (ht' : pullback.snd sX qT ≫ t = t')
    (α : chowGroup C sX n) (β : chowGroup C (t ≫ sZ) m) :
    chowPushforwardOfIso C (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)
        (pullback.fst w t' ≫ (w ≫ sZ)) (mixedCommuteHomOfEq sX sZ w t qT hqT t' ht')
        (mixedCommuteHomOfEq_comp_structureMorphism sX sZ w t qT hqT t' ht') (n + (m - q) - 1)
        (exteriorProductDedekindChowTensor C sX (pullback.fst w t ≫ (w ≫ sZ)) n (m - q) hC
          (α ⊗ₜ[ℤ] c'.cap t m β)) =
      chowGroupDegreeEquiv C (pullback.fst w t' ≫ (w ≫ sZ))
        (by ring : (n + m - 1) - q = n + (m - q) - 1)
        (c'.cap t' (n + m - 1)
          (chowGroupCongr C (pullbackFst_comp_structureMorphism_of_eq sX sZ t qT hqT t' ht')
            (n + m - 1)
            (exteriorProductDedekindChowTensor C sX qT n m hC
              (α ⊗ₜ[ℤ] chowGroupCongr C hqT m β)))) := by
  subst hqT ht'
  rw [chowPushforwardOfIso_congr_apply C _ _ _ _ (mixedCommuteHomOfEq_eq sX sZ w t) _
    (mixedCommuteHom_comp_structureMorphism sX sZ w t)]
  exact exteriorProductDedekindChowTensor_cap_comm hC sX sZ w n m q c' t α β

end CapComm

/-- The two base change maps `X ×_S (Y ×_Z Z) ⟶ X ×_S Y ⟶ X ×_S Z` factor through
`Stacks.Chow.mixedCommuteHomOfEq` at the identity test scheme. -/
private theorem bivariantBaseChangeMap_comp_eq_mixedCommuteHomOfEq_comp_snd
    {C : ChowSituation.{u}} {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) (sZ : Z ⟶ C.S) (w : Y ⟶ Z) :
    bivariantBaseChangeMap sX (w ≫ sZ) (pullback.fst w (𝟙 Z)) ≫ bivariantBaseChangeMap sX sZ w =
      mixedCommuteHomOfEq sX sZ w (𝟙 Z) sZ (Category.id_comp sZ) (pullback.snd sX sZ)
        (Category.comp_id _) ≫ pullback.snd w (pullback.snd sX sZ) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, bivariantBaseChangeMap_fst, bivariantBaseChangeMap_fst,
      Category.assoc, mixedCommuteHomOfEq_snd_fst]
  · rw [Category.assoc, Category.assoc, mixedCommuteHomOfEq_snd_snd]
    simp only [bivariantBaseChangeMap, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.assoc]
    congr 1
    exact (pullback.condition (f := w) (g := 𝟙 Z)).trans (Category.comp_id _)

/-! ### Flat pullback -/

section Flat

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX]

include hC in
/-- **The exterior product over a Dedekind base commutes with flat pullback in the second
variable.** For `h : T' ⟶ T` flat of relative dimension `r`, `α ∈ CH_n(X)` and `β ∈ CH_k(T)`,
`α × h^* β = (1 × h)^* (α × β)`. -/
theorem exteriorProductDedekindChowTensor_flatPullbackChow {T T' : Scheme.{u}} (g : T ⟶ C.S)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (n k : ℤ) (α : chowGroup C sX n)
    (β : chowGroup C g k) :
    letI : LocallyOfFiniteType (bivariantBaseChangeMap sX g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap sX g h)
        (P := @LocallyOfFiniteType) inferInstance
    letI : Flat (bivariantBaseChangeMap sX g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap sX g h) (P := @Flat)
        inferInstance
    exteriorProductDedekindChowTensor C sX (h ≫ g) n (k + r) hC
        (α ⊗ₜ[ℤ] flatPullbackChow C (h ≫ g) g h rfl r hr k
          (flatPullbackDescends C _ _ _ _ _ _ _) β) ≍
      flatPullbackChow C (pullback.fst sX (h ≫ g) ≫ sX) (pullback.fst sX g ≫ sX)
        (bivariantBaseChangeMap sX g h) (bivariantBaseChangeMap_comp_structureMorphism sX sX g h) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_bivariantBaseChangeMap sX g h) hr) (n + k - 1)
        (flatPullbackDescends C _ _ _ _ _ _ _)
        (exteriorProductDedekindChowTensor C sX g n k hC (α ⊗ₜ[ℤ] β)) := by
  have : LocallyOfFiniteType (bivariantBaseChangeMap sX g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap sX g h)
      (P := @LocallyOfFiniteType) inferInstance
  have : Flat (bivariantBaseChangeMap sX g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap sX g h) (P := @Flat)
      inferInstance
  set c' := flatPullbackBivariantClassOfInvertible C (h ≫ g) g h rfl r hr with hc'
  set e := pullback.fst h (𝟙 T) with he
  set d := pullback.snd h (𝟙 T) with hd
  have hde : d = e ≫ h := by
    rw [hd, he, pullback.condition, Category.comp_id]
  have hdr : AlgebraicGeometry.RelativeDimension d r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback h (𝟙 T)) hr
  set β₀ : chowGroup C (𝟙 T ≫ g) k := chowGroupCongr C (Category.id_comp g).symm k β with hβ₀
  have hd' : d ≫ (𝟙 T ≫ g) = e ≫ (h ≫ g) := by
    rw [hde, Category.id_comp, Category.assoc]
  have h1 : flatPullbackChow C (h ≫ g) g h rfl r hr k (flatPullbackDescends C _ _ _ _ _ _ _) β =
      properChowPushforward C (e ≫ (h ≫ g)) (h ≫ g) e rfl (k + r)
        (properPushforwardDescends C _ _ _ _ _)
        (flatPullbackChow C (e ≫ (h ≫ g)) (𝟙 T ≫ g) d hd' r hdr k
          (flatPullbackDescends C _ _ _ _ _ _ _) β₀) := by
    have H := flatPullbackChow_chowPushforwardOfIso C (𝟙 T ≫ g) (e ≫ (h ≫ g)) g (h ≫ g) (𝟙 T)
      rfl e rfl d hd' h rfl (by rw [Category.comp_id, hde]) r hdr hr k
      (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) β₀
    refine Eq.trans ?_ H
    rw [chowPushforwardOfIso_id_eq_chowGroupCongr]
    congr 1
  have h2 := exteriorProductDedekindChowTensor_properChowPushforward hC sX (h ≫ g) e n (k + r) α
    (flatPullbackChow C (e ≫ (h ≫ g)) (𝟙 T ≫ g) d hd' r hdr k
      (flatPullbackDescends C _ _ _ _ _ _ _) β₀)
  set t' := pullback.snd sX g with ht'
  have H := exteriorProductDedekindChowTensor_cap_comm_of_eq hC sX g h n k (-(r : ℤ)) c' (𝟙 T) g
    (Category.id_comp g) t' (Category.comp_id t') α β₀
  set M := mixedCommuteHomOfEq sX g h (𝟙 T) g (Category.id_comp g) t' (Category.comp_id t')
    with hM
  set d'' := pullback.snd h t' with hd''
  have hd''r : AlgebraicGeometry.RelativeDimension d'' r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback h t') hr
  have hd''base : d'' ≫ (pullback.fst sX g ≫ sX) = pullback.fst h t' ≫ (h ≫ g) := by
    rw [pullback.condition (f := sX) (g := g), ← Category.assoc, hd'', ← ht',
      ← pullback.condition, Category.assoc]
  have hM' : inv M ≫ (pullback.fst sX (pullback.fst h (𝟙 T) ≫ (h ≫ g)) ≫ sX) =
      pullback.fst h t' ≫ (h ≫ g) := by
    rw [IsIso.inv_comp_eq, hM, mixedCommuteHomOfEq_comp_structureMorphism]
  set Φ := inv M ≫ bivariantBaseChangeMap sX (h ≫ g) e with hΦ
  have hΦbase : Φ ≫ (pullback.fst sX (h ≫ g) ≫ sX) = pullback.fst h t' ≫ (h ≫ g) := by
    rw [hΦ, Category.assoc, bivariantBaseChangeMap_comp_structureMorphism, hM']
  have hsq : d'' ≫ 𝟙 _ = Φ ≫ bivariantBaseChangeMap sX g h := by
    rw [Category.comp_id, hΦ, Category.assoc, IsIso.eq_inv_comp]
    exact (bivariantBaseChangeMap_comp_eq_mixedCommuteHomOfEq_comp_snd sX g h).symm
  have h4 := flatPullbackChow_chowPushforwardOfIso C (pullback.fst sX g ≫ sX)
    (pullback.fst h t' ≫ (h ≫ g)) (pullback.fst sX g ≫ sX) (pullback.fst sX (h ≫ g) ≫ sX)
    (𝟙 _) (Category.id_comp _) Φ hΦbase d'' hd''base (bivariantBaseChangeMap sX g h)
    (bivariantBaseChangeMap_comp_structureMorphism sX sX g h) hsq r hd''r
    (AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_bivariantBaseChangeMap sX g h)
      hr) (n + k - 1) (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (exteriorProductDedekindChowTensor C sX g n k hC (α ⊗ₜ[ℤ] β))
  rw [chowPushforwardOfIso_id] at h4
  rw [h4, h1, h2]
  have hcomp := chowPushforwardOfIso_comp_apply C (pullback.fst h t' ≫ (h ≫ g))
    (pullback.fst sX (pullback.fst h (𝟙 T) ≫ (h ≫ g)) ≫ sX) (pullback.fst sX (h ≫ g) ≫ sX)
    (inv M) (bivariantBaseChangeMap sX (h ≫ g) e) hM'
    (bivariantBaseChangeMap_comp_structureMorphism sX sX (h ≫ g) e) (n + k - 1 + r)
  rw [← hcomp]
  refine properChowPushforward_heq_congr C _ _ _ _ (by ring) _ _ _ _ ?_
  set y := exteriorProductDedekindChowTensor C sX (pullback.fst h (𝟙 T) ≫ (h ≫ g)) n
    (k - -(r : ℤ)) hC (α ⊗ₜ[ℤ] c'.cap (𝟙 T) k β₀) with hy
  have hyinv : y = chowPushforwardOfIso C _ _ (inv M) hM' (n + (k - -(r : ℤ)) - 1)
      (chowPushforwardOfIso C _ _ M (mixedCommuteHomOfEq_comp_structureMorphism sX g h (𝟙 T) g
        (Category.id_comp g) t' (Category.comp_id t')) (n + (k - -(r : ℤ)) - 1) y) := by
    rw [chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_of_eq_id _ _ _ _ (IsIso.hom_inv_id M)]
    rfl
  have hβ₀β : chowGroupCongr C (Category.id_comp g) k β₀ ≍ β :=
    (chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _)
  refine HEq.trans (exteriorProductDedekindChowTensor_heq hC sX rfl n (by ring) α _ _
    (flatPullbackBivariantCap_heq C (h ≫ g) g h rfl r hr (flatPullbackDescends C) (𝟙 T) k β₀).symm)
    ?_
  change y ≍ _
  rw [hyinv, H]
  refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ ?_
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine (flatPullbackBivariantCap_heq C (h ≫ g) g h rfl r hr (flatPullbackDescends C) t'
    (n + k - 1) _).trans ?_
  refine flatPullbackChow_heq_congr_base C rfl (pullbackFst_comp_structureMorphism_of_eq sX g (𝟙 T)
    g (Category.id_comp g) t' (Category.comp_id t')).symm rfl _ _ rfl _ _ rfl _ _ _ _ ?_
  exact (chowGroupCongr_heq C _ _ _).trans
    (exteriorProductDedekindChowTensor_heq hC sX rfl n rfl α _ _ hβ₀β)

end Flat

/-! ### Gysin maps -/

section Gysin

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- The Gysin map of Stacks 02TO respects equalities of the structure morphism, of the degree and
of the argument. -/
theorem gysinChowOfInvertible_heq_congr {A : Scheme.{u}} {q q' : A ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') (L : A.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) {k k' : ℤ} (hk : k = k') {x : chowGroup C q (k + 1)}
    {y : chowGroup C q' (k' + 1)} (hxy : x ≍ y) :
    gysinChowOfInvertible C q k L σ x ≍ gysinChowOfInvertible C q' k' L σ y := by
  subst hq hk
  rw [eq_of_heq hxy]

include hC in
/-- **The exterior product over a Dedekind base commutes with Gysin maps in the second
variable.** For an invertible module `L` with a section `s` on `T`, zero scheme `D`, and the
pulled-back data on `X ×_S T`, `α × i_D^* β = i_E^* (α × β)`, the base change `X ×_S D` being
identified with the zero scheme `E` of the pulled-back section by Remark 0B6Y. -/
theorem exteriorProductDedekindChowTensor_gysinChowOfInvertible {T : Scheme.{u}} (g : T ⟶ C.S)
    [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (n k : ℤ) (α : chowGroup C sX n) (β : chowGroup C g (k + 1)) :
    properChowPushforward C
        (pullback.fst sX ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
        ((Stacks.Divisors.zeroScheme (pullback sX g)
          ((Scheme.Modules.pullback (pullback.snd sX g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd sX g) L s)).subschemeι ≫
          pullback.fst sX g ≫ sX)
        (bivariantDivisorBaseChangeIso sX g L s).hom
        (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism sX sX g L s) (n + k - 1)
        (properPushforwardDescends C _ _ _ _ _)
        (exteriorProductDedekindChowTensor C sX ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
          n k hC (α ⊗ₜ[ℤ] gysinChowOfInvertible C g k L s β)) ≍
      gysinChowOfInvertible C (pullback.fst sX g ≫ sX) (n + k - 1)
        ((Scheme.Modules.pullback (pullback.snd sX g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd sX g) L s)
        (chowGroupDegreeEquiv C _ (by ring : n + (k + 1) - 1 = n + k - 1 + 1)
          (exteriorProductDedekindChowTensor C sX g n (k + 1) hC (α ⊗ₜ[ℤ] β))) := by
  let c' := (gysinBivariantClass C g L s).1
  let t' := pullback.snd sX g
  let β₀ : chowGroup C (𝟙 T ≫ g) (k + 1) := chowGroupCongr C (Category.id_comp g).symm (k + 1) β
  let ε := pullback.fst (Stacks.Divisors.zeroScheme T L s).subschemeι (𝟙 T)
  let j := (gysinDivisorBaseChangeIso L s (𝟙 T)).hom ≫ ε
  have hjι : j ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι =
      (gysinTripleDivisor L s (𝟙 T)).subschemeι ≫ 𝟙 T := by
    change ((gysinDivisorBaseChangeIso L s (𝟙 T)).hom ≫ ε) ≫ _ = _
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      gysinDivisorBaseChangeIso_hom_snd]
  have hjb : j ≫ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) =
      (gysinTripleDivisor L s (𝟙 T)).subschemeι ≫ (𝟙 T ≫ g) := by
    rw [← Category.assoc, hjι, Category.assoc]
  have h02TA := gysinSystemOfInvertible_onChow_properChowPushforward C (𝟙 T ≫ g) g (𝟙 T) rfl L s
    ((Scheme.Modules.pullback (𝟙 T)).obj L) (AlgebraicGeometry.pullbackGlobalSections (𝟙 T) L s)
    (Iso.refl _) rfl j hjι hjb k (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) β₀
  have hβ : properChowPushforward C (𝟙 T ≫ g) g (𝟙 T) rfl (k + 1)
      (properPushforwardDescends C _ _ _ _ _) β₀ = β := by
    change chowPushforwardOfIso C (𝟙 T ≫ g) g (𝟙 T) rfl (k + 1) β₀ = β
    rw [chowPushforwardOfIso_id_eq_chowGroupCongr]
    exact eq_of_heq ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _))
  rw [hβ] at h02TA
  change gysinChowOfInvertible C g k L s β = _ at h02TA
  rw [h02TA]
  rw [properChowPushforward_comp_apply C _
      (pullback.fst (Stacks.Divisors.zeroScheme T L s).subschemeι (𝟙 T) ≫
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) _
    (gysinDivisorBaseChangeIso L s (𝟙 T)).hom ε j rfl
    (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C g (𝟙 T)) rfl hjb k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _),
    exteriorProductDedekindChowTensor_properChowPushforward hC sX _ ε n k α]
  let M := mixedCommuteHomOfEq sX g (Stacks.Divisors.zeroScheme T L s).subschemeι (𝟙 T) g
    (Category.id_comp g) t' (Category.comp_id t')
  have hinvι : (gysinDivisorBaseChangeIso L s t').inv ≫ (gysinTripleDivisor L s t').subschemeι =
      pullback.snd (Stacks.Divisors.zeroScheme T L s).subschemeι t' := by
    rw [Iso.inv_comp_eq, gysinDivisorBaseChangeIso_hom_snd]
  have hiso : bivariantBaseChangeMap sX ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ε ≫
      (bivariantDivisorBaseChangeIso sX g L s).hom =
        M ≫ (gysinDivisorBaseChangeIso L s t').inv := by
    refine (cancel_mono (gysinTripleDivisor L s t').subschemeι).1 ?_
    rw [Category.assoc, Category.assoc, hinvι]
    change _ ≫ (bivariantDivisorBaseChangeIso sX g L s).hom ≫ (Stacks.Divisors.zeroScheme
      (pullback sX g) ((Scheme.Modules.pullback (pullback.snd sX g)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd sX g) L s)).subschemeι = _
    rw [bivariantDivisorBaseChangeIso_hom_subschemeι]
    exact bivariantBaseChangeMap_comp_eq_mixedCommuteHomOfEq_comp_snd sX g
      (Stacks.Divisors.zeroScheme T L s).subschemeι
  have hMbase := mixedCommuteHomOfEq_comp_structureMorphism sX g
    (Stacks.Divisors.zeroScheme T L s).subschemeι (𝟙 T) g (Category.id_comp g) t'
    (Category.comp_id t')
  have hinvbase : (gysinDivisorBaseChangeIso L s t').inv ≫
      ((Stacks.Divisors.zeroScheme (pullback sX g)
        ((Scheme.Modules.pullback (pullback.snd sX g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd sX g) L s)).subschemeι ≫
          pullback.fst sX g ≫ sX) =
      pullback.fst (Stacks.Divisors.zeroScheme T L s).subschemeι t' ≫
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) := by
    rw [Iso.inv_comp_eq, gysinDivisorBaseChangeIso_hom_comp_structureMorphism,
      pullback.condition]
  have hw : (M ≫ (gysinDivisorBaseChangeIso L s t').inv) ≫
      ((Stacks.Divisors.zeroScheme (pullback sX g)
        ((Scheme.Modules.pullback (pullback.snd sX g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd sX g) L s)).subschemeι ≫
          pullback.fst sX g ≫ sX) =
      pullback.fst sX (ε ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX := by
    rw [Category.assoc, hinvbase, hMbase]
  refine (heq_of_eq (properChowPushforward_comp_apply C
    (pullback.fst sX (ε ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    (pullback.fst sX ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    ((Stacks.Divisors.zeroScheme (pullback sX g)
        ((Scheme.Modules.pullback (pullback.snd sX g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd sX g) L s)).subschemeι ≫
          pullback.fst sX g ≫ sX)
    (bivariantBaseChangeMap sX ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ε)
    (bivariantDivisorBaseChangeIso sX g L s).hom (M ≫ (gysinDivisorBaseChangeIso L s t').inv) hiso
    (bivariantBaseChangeMap_comp_structureMorphism sX sX _ ε)
    (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism sX sX g L s) hw (n + k - 1)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _).symm).trans ?_
  refine (heq_of_eq (properChowPushforward_comp_apply C
    (pullback.fst sX (ε ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX)
    (pullback.fst (Stacks.Divisors.zeroScheme T L s).subschemeι t' ≫
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
    ((Stacks.Divisors.zeroScheme (pullback sX g)
        ((Scheme.Modules.pullback (pullback.snd sX g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd sX g) L s)).subschemeι ≫
          pullback.fst sX g ≫ sX)
    M (gysinDivisorBaseChangeIso L s t').inv _ rfl hMbase hinvbase hw (n + k - 1)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _)).trans ?_
  have H := exteriorProductDedekindChowTensor_cap_comm_of_eq hC sX g
    (Stacks.Divisors.zeroScheme T L s).subschemeι n (k + 1) 1 c' (𝟙 T) g (Category.id_comp g) t'
    (Category.comp_id t') α β₀
  have hz : properChowPushforward C ((gysinTripleDivisor L s (𝟙 T)).subschemeι ≫ 𝟙 T ≫ g)
      (pullback.fst (Stacks.Divisors.zeroScheme T L s).subschemeι (𝟙 T) ≫
        (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
      (gysinDivisorBaseChangeIso L s (𝟙 T)).hom
      (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C g (𝟙 T)) k
      (properPushforwardDescends C _ _ _ _ _)
      (gysinChowOfInvertible C (𝟙 T ≫ g) k ((Scheme.Modules.pullback (𝟙 T)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (𝟙 T) L s) β₀) ≍ c'.cap (𝟙 T) (k + 1) β₀ :=
    properChowPushforward_heq_congr C _ _ _ _ (by ring) _
      (properPushforwardDescends C _ _ _ _ _) _ _
      (gysinChowOfInvertible_heq _ _ _ (by ring) (chowGroupDegreeEquiv_heq C _ _ _).symm)
  refine (properChowPushforward_heq_congr C _ _ _ hinvbase
    (by ring : n + k - 1 = n + (k + 1) - 1 - 1) _ (properPushforwardDescends C _ _ _ _ _) _ _
    ((properChowPushforward_heq_congr C _ _ M hMbase (by ring) _
      (properPushforwardDescends C _ _ _ _ _) _ _
      (exteriorProductDedekindChowTensor_heq hC sX rfl n (by ring) α _ _ hz)).trans
      ((heq_of_eq H).trans (chowGroupDegreeEquiv_heq C _ _ _)))).trans ?_
  have hhom : (gysinDivisorBaseChangeIso L s t').hom ≫
      (pullback.fst (Stacks.Divisors.zeroScheme T L s).subschemeι t' ≫
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) =
      (gysinTripleDivisor L s t').subschemeι ≫ (t' ≫ g) :=
    gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C g t'
  have hw' : ((gysinDivisorBaseChangeIso L s t').hom ≫ (gysinDivisorBaseChangeIso L s t').inv) ≫
      ((Stacks.Divisors.zeroScheme (pullback sX g)
        ((Scheme.Modules.pullback (pullback.snd sX g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd sX g) L s)).subschemeι ≫
          pullback.fst sX g ≫ sX) = (gysinTripleDivisor L s t').subschemeι ≫ (t' ≫ g) := by
    rw [Category.assoc, hinvbase, hhom]
  refine (heq_of_eq (properChowPushforward_comp_apply C _ _ _ (gysinDivisorBaseChangeIso L s t').hom
    (gysinDivisorBaseChangeIso L s t').inv _ rfl hhom hinvbase hw' _
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _).symm).trans ?_
  refine (heq_of_eq (chowPushforwardOfIso_of_eq_id _ _ _ hw' (Iso.hom_inv_id _) _ _)).trans ?_
  refine (chowGroupCongr_heq C _ _ _).trans ?_
  refine gysinChowOfInvertible_heq_congr (pullbackFst_comp_structureMorphism_of_eq sX g (𝟙 T) g
    (Category.id_comp g) t' (Category.comp_id t')).symm _ _ (by ring) ?_
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans
    (HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm)
  exact (chowGroupCongr_heq C _ _ _).trans
    (exteriorProductDedekindChowTensor_heq hC sX rfl n rfl α _ _
      ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _)))

end Gysin

/-! ### The bivariant class `c_α` -/

section Class

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ) (α : chowGroup C sX (1 - p))

/-- **The bivariant class `c_α` of the proof of Stacks 0FC5.** For `α ∈ CH_{1-p}(X)` the rule
`α' ↦ α × α'` on the Chow groups of the schemes locally of finite type over the base is a
bivariant class `c_α ∈ A^p(X ⟶ S)` (Stacks 0B76): it commutes with proper pushforward, flat
pullback and Gysin maps. -/
def dedekindExteriorClass : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p where
  cap g _ k := dedekindExteriorCap hC sX p α g k
  cap_properPushforward g _ h _ k β := dedekindExteriorCap_properPushforward hC sX p α g h k β
  cap_flatPullback g _ h _ _ r hr k := by
    have : LocallyOfFiniteType (bivariantBaseChangeMap sX g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap sX g h)
        (P := @LocallyOfFiniteType) inferInstance
    have : Flat (bivariantBaseChangeMap sX g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap sX g h) (P := @Flat)
        inferInstance
    intro β
    refine (dedekindExteriorCap_heq hC sX p α _ _ _).trans ?_
    refine (exteriorProductDedekindChowTensor_heq hC sX rfl (1 - p) rfl α _
      (flatPullbackChow C (h ≫ g) g h rfl r hr k (flatPullbackDescends C _ _ _ _ _ _ _)
        (chowGroupCongr C (Category.comp_id g) k β))
      ((chowGroupCongr_heq C _ _ _).trans (flatPullbackChow_heq_congr_base C
        (Category.comp_id (h ≫ g)) (Category.comp_id g) rfl _ rfl rfl _ hr rfl _ _ _ _
        (chowGroupCongr_heq C _ _ _).symm))).trans ?_
    refine (exteriorProductDedekindChowTensor_flatPullbackChow hC sX g h r hr (1 - p) k α
      (chowGroupCongr C (Category.comp_id g) k β)).trans ?_
    exact flatPullbackChow_heq_of_degree_eq _ _ _ _ r _ (by ring) _ _
      (chowGroupDegreeEquiv_heq C _ _ _).symm
  cap_gysin g _ L _ s k β := by
    refine eq_of_heq ((properChowPushforward_heq_congr C _ _ _ _ (by ring : k - p = 1 - p + k - 1)
      _ (properPushforwardDescends C _ _ _ _ _) _ _
      ((dedekindExteriorCap_heq hC sX p α _ _ _).trans
        (exteriorProductDedekindChowTensor_heq hC sX rfl (1 - p) rfl α _
          (gysinChowOfInvertible C g k L s (chowGroupCongr C (Category.comp_id g) (k + 1) β))
          ((chowGroupCongr_heq C _ _ _).trans (gysinChowOfInvertible_heq_congr
            (Category.comp_id g) L s rfl (chowGroupCongr_heq C _ _ _).symm))))).trans ?_)
    refine (exteriorProductDedekindChowTensor_gysinChowOfInvertible hC sX g L s (1 - p) k α
      (chowGroupCongr C (Category.comp_id g) (k + 1) β)).trans ?_
    refine gysinChowOfInvertible_heq_congr rfl _ _ (by ring) ?_
    exact (chowGroupDegreeEquiv_heq C _ _ _).trans (HEq.trans
      (chowGroupDegreeEquiv_heq C _ _ _).symm (eqMp_heq_self _ _).symm)

/-- The cap operation of `Stacks.Chow.dedekindExteriorClass` is
`Stacks.Chow.dedekindExteriorCap`. -/
@[simp]
theorem dedekindExteriorClass_cap {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g]
    (k : ℤ) (β : chowGroup C (g ≫ 𝟙 C.S) k) :
    (dedekindExteriorClass hC sX p α).cap g k β = dedekindExteriorCap hC sX p α g k β :=
  rfl

end Class

end Stacks.Chow

end
