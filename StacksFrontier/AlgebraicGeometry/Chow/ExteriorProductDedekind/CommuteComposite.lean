module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.ChowCohomology

/-!
# Bivariant classes towards a Dedekind base commute with all bivariant classes

Let `(S, δ)` be as in Stacks section 42.63, every irreducible component of `S` being of dimension
one, let `X` be locally of finite type over `S`, `c ∈ A^p(X ⟶ S)`, `Y ⟶ Z` a morphism of
schemes locally of finite type over `S` and `c' ∈ A^q(Y ⟶ Z)`. Then ([Stacks, Tag 0FC6])

  `c ∘ c' = c' ∘ c`   in   `A^{p+q}(X ×_S Y ⟶ Z)`.

As in Stacks 0FA2, `c ∘ c' = res(c) ∘ c'` with `res(c) ∈ A^p(X ×_S Y ⟶ Y)` the restriction of `c`
along `Y ⟶ S`, and `c' ∘ c = res(c') ∘ res(c)` with `res(c) ∈ A^p(X ×_S Z ⟶ Z)` and
`res(c') ∈ A^q(Y ×_Z (X ×_S Z) ⟶ X ×_S Z)`, read on `X ×_S Y` through the canonical isomorphism
`Y ×_Z (X ×_S Z) ≅ X ×_S Y`.

## Main results

* `Stacks.Chow.bivariantCommute_bivariantToBase_dedekind` — the base change of `c` to `Z` commutes
  with `c'` in the sense of Stacks 0FA2.
* `Stacks.Chow.BivariantChowClass.comp_comm_of_dedekind` — `c ∘ c' = c' ∘ c` when the irreducible
  components of `S` are curves.

## References

* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FC7](https://stacks.math.columbia.edu/tag/0FC7)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Exterior products and cap products, with presented structure morphisms -/

section CapCommGen

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z)
  [LocallyOfFiniteType w]

/-- The canonical morphism `X ×_S (Y ×_Z T) ⟶ Y ×_Z (X ×_S T)` of
`Stacks.Chow.mixedCommuteHom`, with the structure morphism of `Y ×_Z T`, the structure morphism of
the test scheme and the test morphism of `X ×_S T` all given as morphisms equal to the canonical
ones. -/
def mixedCommuteHomGen {T : Scheme.{u}} (t : T ⟶ Z) (qY : pullback w t ⟶ C.S)
    (hqY : pullback.fst w t ≫ (w ≫ sZ) = qY) (qT : T ⟶ C.S) (hqT : t ≫ sZ = qT)
    (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    pullback sX qY ⟶ pullback w t' :=
  pullback.lift (pullback.snd sX qY ≫ pullback.fst w t)
    (pullback.lift (pullback.fst sX qY) (pullback.snd sX qY ≫ pullback.snd w t)
      (by
        rw [pullback.condition (f := sX) (g := qY), ← hqY, ← hqT]
        simp only [Category.assoc]
        rw [← Category.assoc (pullback.fst w t) w sZ, pullback.condition (f := w) (g := t),
          Category.assoc]))
    (by
      rw [← ht', pullback.lift_snd_assoc]
      simp only [Category.assoc, pullback.condition])

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- With the canonical structure morphism of `Y ×_Z T`, `mixedCommuteHomGen` is
`mixedCommuteHomOfEq`. -/
theorem mixedCommuteHomGen_eq {T : Scheme.{u}} (t : T ⟶ Z) (qT : T ⟶ C.S) (hqT : t ≫ sZ = qT)
    (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    mixedCommuteHomGen sX sZ w t (pullback.fst w t ≫ (w ≫ sZ)) rfl qT hqT t' ht' =
      mixedCommuteHomOfEq sX sZ w t qT hqT t' ht' :=
  rfl

/-- `mixedCommuteHomGen` is an isomorphism. -/
instance isIso_mixedCommuteHomGen {T : Scheme.{u}} (t : T ⟶ Z) (qY : pullback w t ⟶ C.S)
    (hqY : pullback.fst w t ≫ (w ≫ sZ) = qY) (qT : T ⟶ C.S) (hqT : t ≫ sZ = qT)
    (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    IsIso (mixedCommuteHomGen sX sZ w t qY hqY qT hqT t' ht') := by
  subst hqY
  rw [mixedCommuteHomGen_eq]
  infer_instance

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- The composite of `mixedCommuteHomGen` with the projection to `Y` is the projection
`X ×_S (Y ×_Z T) ⟶ Y ×_Z T ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteHomGen_fst {T : Scheme.{u}} (t : T ⟶ Z) (qY : pullback w t ⟶ C.S)
    (hqY : pullback.fst w t ≫ (w ≫ sZ) = qY) (qT : T ⟶ C.S) (hqT : t ≫ sZ = qT)
    (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    mixedCommuteHomGen sX sZ w t qY hqY qT hqT t' ht' ≫ pullback.fst w t' =
      pullback.snd sX qY ≫ pullback.fst w t :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- The composite of `mixedCommuteHomGen` with the projection to `X` is the first projection of
`X ×_S (Y ×_Z T)`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteHomGen_snd_fst {T : Scheme.{u}} (t : T ⟶ Z) (qY : pullback w t ⟶ C.S)
    (hqY : pullback.fst w t ≫ (w ≫ sZ) = qY) (qT : T ⟶ C.S) (hqT : t ≫ sZ = qT)
    (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    mixedCommuteHomGen sX sZ w t qY hqY qT hqT t' ht' ≫ pullback.snd w t' ≫ pullback.fst sX qT =
      pullback.fst sX qY := by
  rw [mixedCommuteHomGen, pullback.lift_snd_assoc, pullback.lift_fst]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- The composite of `mixedCommuteHomGen` with the projection to `T` is the projection
`X ×_S (Y ×_Z T) ⟶ Y ×_Z T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteHomGen_snd_snd {T : Scheme.{u}} (t : T ⟶ Z) (qY : pullback w t ⟶ C.S)
    (hqY : pullback.fst w t ≫ (w ≫ sZ) = qY) (qT : T ⟶ C.S) (hqT : t ≫ sZ = qT)
    (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    mixedCommuteHomGen sX sZ w t qY hqY qT hqT t' ht' ≫ pullback.snd w t' ≫ pullback.snd sX qT =
      pullback.snd sX qY ≫ pullback.snd w t := by
  rw [mixedCommuteHomGen, pullback.lift_snd_assoc, pullback.lift_snd]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] [LocallyOfFiniteType w] in
/-- `mixedCommuteHomGen` commutes with the structure morphisms to `S`. -/
theorem mixedCommuteHomGen_comp_structureMorphism {T : Scheme.{u}} (t : T ⟶ Z)
    (qY : pullback w t ⟶ C.S) (hqY : pullback.fst w t ≫ (w ≫ sZ) = qY) (qT : T ⟶ C.S)
    (hqT : t ≫ sZ = qT) (t' : pullback sX qT ⟶ Z) (ht' : pullback.snd sX qT ≫ t = t') :
    mixedCommuteHomGen sX sZ w t qY hqY qT hqT t' ht' ≫ (pullback.fst w t' ≫ (w ≫ sZ)) =
      pullback.fst sX qY ≫ sX := by
  rw [mixedCommuteHomGen_fst_assoc, hqY]
  exact (pullback.condition (f := sX) (g := qY)).symm

variable (n m q : ℤ) (c' : CanonicalBivariantClass C (w ≫ sZ) sZ w rfl q)

include hC in
/-- **Exterior products commute with cap products, at a presentation of the structure morphisms.**
The identity `α × (c' ∩ β) = c' ∩ (α × β)` of
`Stacks.Chow.exteriorProductDedekindChowTensor_cap_comm`, with the structure morphism `qY` of
`Y ×_Z T`, the structure morphism `qT` of the test scheme and the test morphism `t'` of `X ×_S T`
given as morphisms equal to the canonical ones. -/
theorem exteriorProductDedekindChowTensor_cap_comm_gen {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (qY : pullback w t ⟶ C.S) [LocallyOfFiniteType qY]
    (hqY : pullback.fst w t ≫ (w ≫ sZ) = qY) (qT : T ⟶ C.S) [LocallyOfFiniteType qT]
    (hqT : t ≫ sZ = qT) (t' : pullback sX qT ⟶ Z) [LocallyOfFiniteType t']
    (ht' : pullback.snd sX qT ≫ t = t') (α : chowGroup C sX n) (β : chowGroup C (t ≫ sZ) m) :
    chowPushforwardOfIso C (pullback.fst sX qY ≫ sX) (pullback.fst w t' ≫ (w ≫ sZ))
        (mixedCommuteHomGen sX sZ w t qY hqY qT hqT t' ht')
        (mixedCommuteHomGen_comp_structureMorphism sX sZ w t qY hqY qT hqT t' ht')
        (n + (m - q) - 1)
        (exteriorProductDedekindChowTensor C sX qY n (m - q) hC
          (α ⊗ₜ[ℤ] chowGroupCongr C hqY (m - q) (c'.cap t m β))) =
      chowGroupDegreeEquiv C (pullback.fst w t' ≫ (w ≫ sZ))
        (by ring : (n + m - 1) - q = n + (m - q) - 1)
        (c'.cap t' (n + m - 1)
          (chowGroupCongr C (pullbackFst_comp_structureMorphism_of_eq sX sZ t qT hqT t' ht')
            (n + m - 1)
            (exteriorProductDedekindChowTensor C sX qT n m hC
              (α ⊗ₜ[ℤ] chowGroupCongr C hqT m β)))) := by
  subst hqY
  exact exteriorProductDedekindChowTensor_cap_comm_of_eq hC sX sZ w n m q c' t qT hqT t' ht' α β

end CapCommGen

/-! ### The base change of `c_α` commutes with every class over the base -/

section Commute

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : Y ⟶ Z)
  [LocallyOfFiniteType f] (p q : ℤ)

include hC in
/-- The base change to `Z` of the class `c_α ∈ A^p(X ⟶ S)` of Stacks 0FC5 commutes, in the sense of
Stacks 0FA2, with every `c' ∈ A^q(Y ⟶ Z)`. -/
theorem bivariantCommute_dedekindExteriorClass (α : chowGroup C sX (1 - p))
    (c' : BivariantChowClass C (f ≫ sZ) sZ f rfl q) :
    BivariantCommute C (gysinSystemOfInvertible C) sZ (pullback.snd sX sZ) f p q
      (bivariantToBaseRestrictionHom C (gysinSystemOfInvertible C) sX sZ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (BivariantChowClass.equivBivariantClass (dedekindExteriorClass hC sX p α)))
      (BivariantChowClass.equivBivariantClass c') := by
  intro T t _ k β
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply]
  let c := dedekindExteriorClass hC sX p α
  let R := bivariantToBaseRestrictionHom C (gysinSystemOfInvertible C) sX sZ p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (BivariantChowClass.equivBivariantClass c)
  have hR : ∀ {T' : Scheme.{u}} (g : T' ⟶ Z) [LocallyOfFiniteType g] (m : ℤ)
      (x : chowGroup C (g ≫ sZ) m) (x' : chowGroup C ((g ≫ sZ) ≫ 𝟙 C.S) m), x' ≍ x →
      R.cap g m x ≍ chowPushforwardOfIso C (pullback.fst sX (g ≫ sZ) ≫ sX)
        (pullback.fst (pullback.snd sX sZ) g ≫ (pullback.fst sX sZ ≫ sX))
        (pullbackLeftPullbackSndIso sX sZ g).inv (by simp) (m - p) (c.cap (g ≫ sZ) m x') := by
    intro T' g _ m x x' hx
    have hT : g ≫ sZ = g ≫ (sZ ≫ 𝟙 C.S) := by rw [Category.comp_id]
    refine (bivariantClassCongrBase_cap C (gysinSystemOfInvertible C) (pullback.snd sX sZ)
      (pullback.condition (f := sX) (g := sZ)) (Category.comp_id sZ) p
      (bivariantRestriction C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) sZ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (BivariantChowClass.equivBivariantClass c)) g m (chowGroupCongr C hT m x) x
      (chowGroupCongr_heq C hT m x) (hv' := rfl)).trans ?_
    rw [bivariantRestriction_cap, bivariantRestrictionCap_apply]
    refine chowPushforwardOfIso_heq_congr C _ _ _ _ rfl _ _ ?_
    exact c.heq_cap _ rfl (((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _)).trans
      hx.symm)
  let c'' := BivariantChowClass.equivBivariantClass c'
  let g₁ := pullback.fst f t ≫ f
  let g₂ := pullback.fst (pullback.snd sX sZ) t ≫ pullback.snd sX sZ
  let ι₁ := (pullbackLeftPullbackSndIso sX sZ g₁).inv
  let ιt := (pullbackLeftPullbackSndIso sX sZ t).inv
  let t' := ιt ≫ g₂
  have ht' : pullback.snd sX (t ≫ sZ) ≫ t = t' := by
    change _ = (pullbackLeftPullbackSndIso sX sZ t).inv ≫
      pullback.fst (pullback.snd sX sZ) t ≫ pullback.snd sX sZ
    rw [pullbackLeftPullbackSndIso_inv_fst_snd]
  have hqY : pullback.fst f t ≫ (f ≫ sZ) = g₁ ≫ sZ := (Category.assoc _ _ _).symm
  let N := mixedCommuteHomGen sX sZ f t (g₁ ≫ sZ) hqY (t ≫ sZ) rfl t' ht'
  have H := exteriorProductDedekindChowTensor_cap_comm_gen hC sX sZ f (1 - p) k q c'' t (g₁ ≫ sZ)
    hqY (t ≫ sZ) rfl t' ht' α β
  have hiso : ι₁ ≫ commuteComparisonHom (pullback.snd sX sZ) f t =
      N ≫ bivariantBaseChangeMap f g₂ ιt := by
    refine pullback.hom_ext ?_ (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_) <;>
      simp [ι₁, N, g₁, g₂, ιt, t', bivariantBaseChangeMap, pullback.condition]
  have hA : ∀ {T' : Scheme.{u}} (g : T' ⟶ Z),
      pullback.fst (pullback.snd sX sZ) g ≫ (pullback.snd sX sZ ≫ sZ) =
      pullback.fst (pullback.snd sX sZ) g ≫ (pullback.fst sX sZ ≫ sX) := fun g => by
    rw [pullback.condition (f := sX) (g := sZ)]
  have hu' : commuteComparisonHom (pullback.snd sX sZ) f t ≫
      (pullback.fst f g₂ ≫ (f ≫ sZ)) =
      pullback.fst (pullback.snd sX sZ) g₁ ≫ (pullback.fst sX sZ ≫ sX) := by
    rw [commuteComparisonHom_comp_structureMorphism C sZ (pullback.snd sX sZ) f t, hA]
  have hx'eq : pullback.fst f t ≫ (f ≫ sZ) = (g₁ ≫ sZ) ≫ 𝟙 C.S :=
    hqY.trans (Category.comp_id _).symm
  refine eq_of_heq ((chowPushforwardOfIso_heq_congr_base C _ _ rfl _ hu' (hA _) rfl rfl _ _
    (hR g₁ (k - q) _ (chowGroupCongr C hx'eq (k - q) (c''.cap t k β))
      ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _).symm))).trans ?_)
  rw [chowPushforwardOfIso_comp_apply]
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring : k - q - p = 1 - p + (k - q) - 1) _ _
    (dedekindExteriorCap_heq hC sX p α _ _ _)).trans ?_
  have hNbase := mixedCommuteHomGen_comp_structureMorphism sX sZ f t (g₁ ≫ sZ) hqY (t ≫ sZ) rfl t'
    ht'
  have hBbase : bivariantBaseChangeMap f g₂ ιt ≫ (pullback.fst f g₂ ≫ (f ≫ sZ)) =
      pullback.fst f t' ≫ (f ≫ sZ) :=
    bivariantBaseChangeMap_comp_structureMorphism (f ≫ sZ) f g₂ ιt
  refine (heq_of_eq ((chowPushforwardOfIso_congr_apply C _ _ _ _ hiso _
      (by rw [Category.assoc N, hBbase, hNbase]) _ _).trans
    (chowPushforwardOfIso_comp_apply C _ _ _ N (bivariantBaseChangeMap f g₂ ιt) hNbase hBbase _
      _).symm)).trans ?_
  have hNx : chowGroupCongr C (Category.comp_id (g₁ ≫ sZ)) (k - q)
      (chowGroupCongr C hx'eq (k - q) (c''.cap t k β)) =
      chowGroupCongr C hqY (k - q) (c''.cap t k β) := by
    congr 1
  rw [hNx, H]
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
  have hβ' : t ≫ sZ = (t ≫ sZ) ≫ 𝟙 C.S := (Category.comp_id _).symm
  have hAt : pullback.fst sX (t ≫ sZ) ≫ sX = (ιt ≫ g₂) ≫ sZ := by
    rw [Category.assoc, Category.assoc, ← pullback.condition (f := sX) (g := sZ)]
    change _ = (pullbackLeftPullbackSndIso sX sZ t).inv ≫ pullback.fst (pullback.snd sX sZ) t ≫
      pullback.fst sX sZ ≫ sX
    rw [pullbackLeftPullbackSndIso_inv_fst_assoc]
  have hBt : pullback.fst (pullback.snd sX sZ) t ≫ (pullback.fst sX sZ ≫ sX) = g₂ ≫ sZ :=
    (hA t).symm.trans (Category.assoc _ _ _).symm
  let x'' := chowGroupCongr C hAt (k - p) (c.cap (t ≫ sZ) k (chowGroupCongr C hβ' k β))
  have hw : chowGroupCongr C (Category.assoc (pullback.fst (pullback.snd sX sZ) t)
      (pullback.snd sX sZ) sZ).symm (k - p) (R.cap t k β) =
      properChowPushforward C ((ιt ≫ g₂) ≫ sZ) (g₂ ≫ sZ) ιt (Category.assoc _ _ _).symm (k - p)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C ((ιt ≫ g₂) ≫ sZ)
          (g₂ ≫ sZ) ιt (Category.assoc _ _ _).symm (k - p)) x'' := by
    refine eq_of_heq ((chowGroupCongr_heq C _ _ _).trans ((hR t k β
      (chowGroupCongr C hβ' k β) (chowGroupCongr_heq C hβ' k β)).trans ?_))
    exact chowPushforwardOfIso_heq_congr_base C _ _ rfl _ (Category.assoc _ _ _).symm hAt hBt rfl
      _ _ (chowGroupCongr_heq C _ _ _).symm
  refine HEq.trans ?_ (heq_of_eq (congrArg (c'.cap g₂ (k - p)) hw).symm)
  refine HEq.trans ?_ (heq_of_eq (c'.cap_properPushforward g₂ ιt (k - p) x'').symm)
  refine properChowPushforward_heq_congr C _ _ _ _ (by ring) _ _ _ _ ?_
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans (c'.heq_cap _ (by ring) ?_)
  refine (chowGroupCongr_heq C _ _ _).trans (HEq.trans ?_ (chowGroupCongr_heq C _ _ _).symm)
  refine HEq.trans ?_ (dedekindExteriorCap_heq hC sX p α _ _ _).symm
  exact exteriorProductDedekindChowTensor_heq hC sX rfl (1 - p) rfl α _ _
    ((chowGroupCongr_heq C _ _ _).trans (((chowGroupCongr_heq C _ _ _).trans
      (chowGroupCongr_heq C _ _ _)).symm))

include hC in
/-- Over a Dedekind base whose irreducible components are curves, the base change
`res(c) ∈ A^p(X ×_S Z ⟶ Z)` of any `c ∈ A^p(X ⟶ S)` commutes, in the sense of Stacks 0FA2, with
every `c' ∈ A^q(Y ⟶ Z)`. -/
theorem bivariantCommute_bivariantToBase_dedekind
    (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1)
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (c' : BivariantChowClass C (f ≫ sZ) sZ f rfl q) :
    BivariantCommute C (gysinSystemOfInvertible C) sZ (pullback.snd sX sZ) f p q
      (bivariantToBaseRestrictionHom C (gysinSystemOfInvertible C) sX sZ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (BivariantChowClass.equivBivariantClass c))
      (BivariantChowClass.equivBivariantClass c') := by
  rw [eq_dedekindExteriorClass hC hdim c]
  exact bivariantCommute_dedekindExteriorClass hC sX sZ f p q _ c'

end Commute

/-! ### Commutation of composites -/

section Composite

variable {C : ChowSituation.{u}} {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : Y ⟶ Z)
  (hf : f ≫ sZ = sY) (p q : ℤ)

/-- Let `(S, δ)` be as in Stacks section 42.63 — locally the spectrum of a Dedekind domain, with
`δ = 0` at the closed points and `δ = 1` elsewhere — every irreducible component of `S` being of
dimension one. Let `X` be a scheme locally of finite type over `S` and `c ∈ A^p(X ⟶ S)`. Let
`f : Y ⟶ Z` be a morphism of schemes locally of finite type over `S` and `c' ∈ A^q(Y ⟶ Z)`. Then
`c ∘ c' = c' ∘ c` in `A^{p+q}(X ×_S Y ⟶ Z)`.

Here `c ∘ c' = res(c) ∘ c'` with `res(c) ∈ A^p(X ×_S Y ⟶ Y)` the restriction of `c` along
`Y ⟶ S`, and `c' ∘ c = res(c') ∘ res(c)` with `res(c) ∈ A^p(X ×_S Z ⟶ Z)` the restriction of `c`
along `Z ⟶ S` and `res(c') ∈ A^q(Y ×_Z (X ×_S Z) ⟶ X ×_S Z)` the restriction of `c'` along
`X ×_S Z ⟶ Z` (Stacks 0F9Z, 0FA2). The second composite lives on `Y ×_Z (X ×_S Z)` and in degree
`q + p`; it is read on `X ×_S Y` through the canonical isomorphism and in degree `p + q`. -/
theorem BivariantChowClass.comp_comm_of_dedekind (hC : IsDedekindChowBase C)
    (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1)
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (c' : BivariantChowClass C sY sZ f hf q) :
    (c.restrict sY (Category.comp_id sY)).comp c' =
      (((c'.restrict (pullback.snd sX sZ)
          (BivariantChowClass.restrict_structure_eq (Category.comp_id sX) sZ
            (Category.comp_id sZ))).comp
        (c.restrict sZ (Category.comp_id sZ))).degreeCongr (add_comm q p)).transport
        (comp_comp_structureMorphism_eq
          (BivariantChowClass.restrict_structure_eq (Category.comp_id sX) sY
            (Category.comp_id sY)) hf)
        (pointClassCompositeIso C sX sZ f hf) (pointClassCompositeIso_hom_comp C sX sZ f hf) := by
  subst hf
  have := BivariantChowClass.locallyOfFiniteType_of_structure sZ f rfl
  exact BivariantChowClass.comp_comm_of_bivariantCommute C sX sZ f p q c c'
    (bivariantCommute_bivariantToBase_dedekind hC sX sZ f p q hdim c c')

end Composite

end Stacks.Chow

end
