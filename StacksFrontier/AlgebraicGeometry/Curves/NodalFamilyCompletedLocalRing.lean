module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Smooth.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.IsSplitNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodalSingularitiesCharacterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import StacksFrontier.AlgebraicGeometry.Variety.RationalMap.LocalRingDimension
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace
public import StacksFrontier.RingTheory.MvPowerSeries.Noetherian
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The formal local structure of a family of nodal curves

Let `f : T ⟶ S` be a morphism of schemes, locally of finite type and flat at a point `t` of
`T`, whose base has a Noetherian local ring at `s = f t`.  Write `A` for the completion of
`𝒪_{S, s}` and `B` for the completion of `𝒪_{T, t}`.  If `t` is a split node of the fibre
`T_s` over the residue field `κ(s)`, then there is an element `h` of the maximal ideal of `A`
and an isomorphism of `A`-algebras `A⟦x, y⟧/(x y - h) ≅ B`.

## Main results

* `Stacks.Curves.exists_algEquiv_adicCompletion_quotient_mvPowerSeries_of_isSplitNode` — the
  relative nodal presentation of the completed local ring at a split node of a family
  (Tag 0CBX).

## Implementation notes

The fibre and the point above `t` are the canonical `AlgebraicGeometry.Scheme.Hom.fiber` and
`AlgebraicGeometry.Scheme.Hom.asFiber` of the morphism, viewed over `Spec κ(s)`.  The algebra
structure on `B` over `A` is the one induced by the map of completions of the stalk
homomorphism, so the equivalence is one of algebras over the completed base local ring.

The proof follows the source: the split node gives `k⟦x, y⟧/(x y)` for the completed local ring
of the fibre, the hypersurface relation is lifted step by step through the powers of the
maximal ideal of `A`, and flatness forces the lifted relation to generate the whole kernel.

## References

* [Stacks Project, Tag 0CBX](https://stacks.math.columbia.edu/tag/0CBX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.Curves

/-- The two-branch multicross ring `multicross k 2` over a field has Krull dimension
at most `1`. -/
private theorem ringKrullDim_multicross_two_le_one (k : Type*) [Field k] :
    ringKrullDim (multicross k 2) ≤ 1 := by
  let C := multicross k 2
  let D := PowerSeries k × PowerSeries k
  let f : C →+* D :=
    { toFun := fun c => (c.1 0, c.1 1)
      map_zero' := rfl
      map_one' := rfl
      map_add' := by intros; rfl
      map_mul' := by intros; rfl }
  let : Algebra C D := f.toAlgebra
  have : Module.Finite C D := by
    let L : (C × C) →ₗ[C] D :=
      { toFun := fun z => ((f z.1).1, (f z.2).2)
        map_add' := by intros; apply Prod.ext <;> rfl
        map_smul' := by intros; apply Prod.ext <;> rfl }
    apply Module.Finite.of_surjective L
    intro d
    let a : C := ⟨fun _ => d.1, by intro i j; rfl⟩
    let b : C := ⟨fun _ => d.2, by intro i j; rfl⟩
    refine ⟨(a,b), ?_⟩
    simp [L, a, b, f]
  have : Algebra.IsIntegral C D := Algebra.IsIntegral.of_finite C D
  have : FaithfulSMul C D := (faithfulSMul_iff_algebraMap_injective C D).mpr (by
    show Function.Injective f
    intro a b hab
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg Prod.fst hab
    · exact congrArg Prod.snd hab)
  rw [Algebra.IsIntegral.ringKrullDim_eq C D]
  exact Ring.krullDimLE_iff.mp (show Ring.KrullDimLE 1 D by infer_instance)

/-- The two-branch multicross ring `multicross k 2` over a field has Krull dimension
exactly `1`. -/
private theorem ringKrullDim_multicross_two_eq_one (k : Type*) [Field k] :
    ringKrullDim (multicross k 2) = 1 := by
  let proj : multicross k 2 →+* PowerSeries k :=
    (Pi.evalRingHom (fun _ : Fin 2 => PowerSeries k) (0 : Fin 2)).comp
      (multicross k 2).subtype
  have hsurj : Function.Surjective proj := by
    intro p
    refine ⟨⟨fun _ => p, ?_⟩, ?_⟩
    · rw [mem_multicross]
      intro i j
      rfl
    · rfl
  apply le_antisymm (ringKrullDim_multicross_two_le_one k)
  have hdim : ringKrullDim (PowerSeries k) = 1 :=
    IsDiscreteValuationRing.ringKrullDim_eq_one (PowerSeries k)
  rw [← hdim]
  exact ringKrullDim_le_of_surjective proj hsurj


/-- A node of a scheme locally of finite type over a field has local topological Krull
dimension `1`. -/
private theorem topologicalKrullDimAt_eq_one_of_isNode
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (x : X)
    (hx : IsNode k X x) :
    topologicalKrullDimAt X x = 1 := by
  let K := AlgebraicClosure k
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y : Scheme.{u} := pullback (X ↘ Spec (.of k)) g
  let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
  let q : Y ⟶ Spec (.of K) := pullback.snd (X ↘ Spec (.of k)) g
  let : Y.Over (Spec (.of K)) := ⟨q⟩
  change IsClosed ({x} : Set X) ∧
    ∃ y : Y, p.base y = x ∧ IsOrdinaryDoublePoint K Y y at hx
  obtain ⟨_, y, hy, hnode⟩ := hx
  have : LocallyOfFiniteType q := by
    dsimp [q]
    infer_instance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  let R := Y.presheaf.stalk y
  have : IsNoetherianRing R := inferInstance
  let kToStalk : K →+* R :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫
      Y.presheaf.germ ⊤ y (by simp)).hom
  let : Algebra K R := kToStalk.toAlgebra
  let : Algebra K (AdicCompletion (maximalIdeal R) R) := inferInstance
  let : Algebra K (multicross K 2) := multicrossAlgebra K 2
  obtain ⟨e⟩ := hnode.2
  have hdim : ringKrullDim R = 1 := by
    rw [← IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal
      (A := R), ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    exact ringKrullDim_multicross_two_eq_one K
  have hY : topologicalKrullDimAt Y y = 1 :=
    (AlgebraicGeometry.topologicalKrullDimAt_eq_krullDimOfRing_stalk
      K Y q y hnode.1).trans hdim
  calc
    topologicalKrullDimAt X x = topologicalKrullDimAt Y y := by
      rw [topologicalKrullDimAt_baseChange_eq k K X (X ↘ Spec (.of k)) y, hy]
    _ = 1 := hY

/-- A point whose local Krull dimension is `1` has an open neighbourhood of Krull dimension `1`. -/
private theorem exists_open_with_dimension_eq_one
    {X : Type*} [TopologicalSpace X] (x : X)
    (h : topologicalKrullDimAt X x = (1 : WithBot ℕ∞)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ topologicalKrullDim (↥U) = (1 : WithBot ℕ∞) := by
  obtain ⟨⟨U, hxU, hU, hdimU⟩, _⟩ := topologicalKrullDimAt_isLeast X x
  exact ⟨U, hU, hxU, by rw [← hdimU, h]⟩


/-- If `f : T ⟶ S` is flat at `t`, the induced map of maximal-adic completions of the stalks
`𝒪_{S, f t}` and `𝒪_{T, t}` is flat. -/
private theorem adicCompletionMap_flat_of_isFlatAt
    {T S : Scheme.{u}} (f : T ⟶ S) (t : T)
    (hflat : AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom t)
    [IsNoetherianRing (S.presheaf.stalk (f t))] [LocallyOfFiniteType f] :
    let R := S.presheaf.stalk (f t)
    let Q := T.presheaf.stalk t
    let φ : AdicCompletion (maximalIdeal R) R →+*
        AdicCompletion (maximalIdeal Q) Q :=
      adicCompletionMap (f.stalkMap t).hom (maximalIdeal R) (maximalIdeal Q)
        (map_maximalIdeal_le (f.stalkMap t).hom)
    φ.Flat := by
  let R := S.presheaf.stalk (f t)
  let Q := T.presheaf.stalk t
  let : Algebra R Q := (f.stalkMap t).hom.toAlgebra
  have : Algebra.EssFiniteType R Q := LocallyOfFiniteType.stalkMap f t
  have : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing R Q
  have : IsLocalHom ((f.stalkMap t).hom) := inferInstance
  show (adicCompletionMap (f.stalkMap t).hom (maximalIdeal R) (maximalIdeal Q)
    (map_maximalIdeal_le (f.stalkMap t).hom)).Flat
  exact (adicCompletionMap_flat_iff (f.stalkMap t).hom).2 hflat

/-- The maximal ideal of the completion of `R`, mapped to the completion of `Q`, is generated by the
image of `(maximalIdeal R).map f`. -/
private theorem map_maximalIdeal_adicCompletionMap {R Q : Type*} [CommRing R] [CommRing Q]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing Q] (f : R →+* Q)
    (hf : (maximalIdeal R).map f ≤ maximalIdeal Q) :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).map
        (adicCompletionMap f (maximalIdeal R) (maximalIdeal Q) hf) =
      ((maximalIdeal R).map f).map (algebraMap Q (AdicCompletion (maximalIdeal Q) Q)) := by
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map,
    adicCompletionMap_comp_algebraMap, ← Ideal.map_map]

/-- The map of maximal-adic completions induced by a local homomorphism of Noetherian local
rings is again a local homomorphism. -/
private theorem adicCompletionMap_isLocalHom_of_isLocalHom
    {R Q : Type*} [CommRing R] [CommRing Q]
    [IsNoetherianRing R] [IsNoetherianRing Q]
    [IsLocalRing R] [IsLocalRing Q]
    (f : R →+* Q) [IsLocalHom f] :
    IsLocalHom (adicCompletionMap f (maximalIdeal R) (maximalIdeal Q)
      (map_maximalIdeal_le f)) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 3 1).mp
  rw [map_maximalIdeal_adicCompletionMap, AdicCompletion.maximalIdeal_eq_map (R := Q)]
  exact Ideal.map_mono (map_maximalIdeal_le f)

/-- A flat local homomorphism of Noetherian local rings makes the completion of the target a
faithfully flat module over the completion of the source. -/
private theorem adicCompletionMap_faithfullyFlat
    {R Q : Type*} [CommRing R] [CommRing Q]
    [IsNoetherianRing R] [IsNoetherianRing Q]
    [IsLocalRing R] [IsLocalRing Q]
    (f : R →+* Q) [IsLocalHom f] (hf : f.Flat) :
    let A := AdicCompletion (maximalIdeal R) R
    let B := AdicCompletion (maximalIdeal Q) Q
    let φ := adicCompletionMap f (maximalIdeal R) (maximalIdeal Q)
      (map_maximalIdeal_le f)
    letI : Algebra A B := φ.toAlgebra
    Module.FaithfullyFlat A B := by
  let A := AdicCompletion (maximalIdeal R) R
  let B := AdicCompletion (maximalIdeal Q) Q
  let φ := adicCompletionMap f (maximalIdeal R) (maximalIdeal Q)
    (map_maximalIdeal_le f)
  let : Algebra A B := φ.toAlgebra
  have : IsLocalHom (algebraMap A B) := by
    show IsLocalHom φ
    exact adicCompletionMap_isLocalHom_of_isLocalHom f
  have : Module.Flat A B :=
    RingHom.flat_algebraMap_iff.mpr ((adicCompletionMap_flat_iff f).2 hf)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- For a surjection `g : C →ₐ[A] B` onto a flat `A`-algebra, an ideal `I ≤ ker g` with
`ker g ≤ I ⊔ 𝔪_A C` is already the whole kernel. -/
private theorem ker_eq_of_flat_closed_fiber
    {A C B : Type*} [CommRing A] [CommRing C] [CommRing B]
    [Algebra A C] [Algebra A B] [Module.Flat A B] [IsLocalRing A]
    [IsNoetherianRing C]
    (g : C →ₐ[A] B) (hg : Function.Surjective g) (I : Ideal C)
    (hI : I ≤ RingHom.ker g.toRingHom)
    (hm : (maximalIdeal A).map (algebraMap A C) ≤ (⊥ : Ideal C).jacobson)
    (hclosed : RingHom.ker g.toRingHom ≤
      I ⊔ (maximalIdeal A).map (algebraMap A C)) :
    RingHom.ker g.toRingHom = I := by
  let K := RingHom.ker g.toRingHom
  let m := (maximalIdeal A).map (algebraMap A C)
  have hker : LinearMap.ker g.toLinearMap = K.restrictScalars A := by
    ext x
    simp [K, RingHom.mem_ker]
  have hInt : K ⊓ m = m • K := by
    apply Submodule.restrictScalars_injective A
    rw [Ideal.smul_restrictScalars, ← hker,
      ← LinearMap.ker_inf_smul_top_eq_smul_of_flat
        (maximalIdeal A) g.toLinearMap hg, hker, Ideal.smul_top_eq_map]
    rfl
  have hKfg : K.FG := IsNoetherian.noetherian K
  have hle : K ≤ I ⊔ ((maximalIdeal A).map (algebraMap A C) • K) := by
    intro x hx
    obtain ⟨y, hy, z, hz, hxyz⟩ := Submodule.mem_sup.mp (hclosed hx)
    have hzK : z ∈ K := by
      have hzEq : z = x - y := by rw [← hxyz]; ring
      rw [hzEq]
      exact K.sub_mem hx (hI hy)
    have hz' : z ∈ (maximalIdeal A).map (algebraMap A C) • K := by
      rw [← hInt]
      exact ⟨hzK, hz⟩
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz', hxyz⟩
  exact le_antisymm
    (Submodule.le_of_le_smul_of_le_jacobson_bot hKfg hm hle) hI

/-- A relation `u * v - f h = ∑ f (r i) * b i` with coefficients `r i ∈ I ^ n` is corrected to
`u', v', h'` congruent to `u, v, h` modulo `I ^ n` with `u' * v' - f h' ∈ (I B) ^ (n + 1)`. -/
private theorem improve_relation_mod_pow
    {A B ι : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (u v : B) (h : A) (n : ℕ) (hn : 1 ≤ n)
    (s : Finset ι) (r : ι → A) (b b₁ b₂ e : ι → B) (a : ι → A)
    (hr : ∀ i ∈ s, r i ∈ I ^ n)
    (hb : ∀ i ∈ s, b i = f (a i) + u * b₁ i + v * b₂ i + e i)
    (hrel : u * v - f h = ∑ i ∈ s, f (r i) * b i)
    (he : ∀ i ∈ s, e i ∈ (I.map f)) :
    ∃ u' v' : B, ∃ h' : A,
      u - u' ∈ (I.map f) ^ n ∧ v - v' ∈ (I.map f) ^ n ∧
        h' - h ∈ I ^ n ∧ u' * v' - f h' ∈ (I.map f) ^ (n + 1) := by
  classical
  let J := I.map f
  let α : B := ∑ i ∈ s, b₂ i * f (r i)
  let β : B := ∑ i ∈ s, b₁ i * f (r i)
  let γ : A := ∑ i ∈ s, a i * r i
  have hmul : ∀ c : ι → B, ∑ i ∈ s, c i * f (r i) ∈ J ^ n := fun c =>
    Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _
      (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem f (hr i hi))
  have hα : α ∈ J ^ n := hmul b₂
  have hβ : β ∈ J ^ n := hmul b₁
  have hγ : γ ∈ I ^ n := Ideal.sum_mem _ fun i hi => (I ^ n).mul_mem_left _ (hr i hi)
  refine ⟨u - α, v - β, h + γ, ?_, ?_, ?_, ?_⟩
  · simpa [α] using hα
  · simpa [β] using hβ
  · simpa [γ] using hγ
  · show (u - α) * (v - β) - f (h + γ) ∈ J ^ (n + 1)
    have hsplit : (∑ i ∈ s, f (r i) * b i) =
        f γ + u * β + v * α + ∑ i ∈ s, f (r i) * e i := by
      have hrewrite : (∑ i ∈ s, f (r i) * b i) =
          ∑ i ∈ s, f (r i) *
            (f (a i) + u * b₁ i + v * b₂ i + e i) :=
        Finset.sum_congr rfl fun i hi => by rw [hb i hi]
      have hfirst : (∑ i ∈ s, f (r i) * f (a i)) = f γ := by
        simp [γ, map_sum, map_mul, mul_comm]
      have hsecond : (∑ i ∈ s, f (r i) * (u * b₁ i)) = u * β := by
        calc
          (∑ i ∈ s, f (r i) * (u * b₁ i)) =
              ∑ i ∈ s, u * (b₁ i * f (r i)) :=
            Finset.sum_congr rfl fun _ _ => by ring
          _ = u * β := by
            simpa [β] using (Finset.mul_sum s (fun i => b₁ i * f (r i)) u).symm
      have hthird : (∑ i ∈ s, f (r i) * (v * b₂ i)) = v * α := by
        calc
          (∑ i ∈ s, f (r i) * (v * b₂ i)) =
              ∑ i ∈ s, v * (b₂ i * f (r i)) :=
            Finset.sum_congr rfl fun _ _ => by ring
          _ = v * α := by
            simpa [α] using (Finset.mul_sum s (fun i => b₂ i * f (r i)) v).symm
      rw [hrewrite]
      simp only [Finset.sum_add_distrib, mul_add]
      rw [hfirst, hsecond, hthird]
    have hsplit' : u * v - f h =
        f γ + u * β + v * α + ∑ i ∈ s, f (r i) * e i := hrel.trans hsplit
    have hid : (u - α) * (v - β) - f (h + γ) =
        α * β + ∑ i ∈ s, f (r i) * e i := by
      rw [map_add]
      calc
        (u - α) * (v - β) - (f h + f γ) =
            (u * v - f h) - u * β - v * α + α * β - f γ := by ring
        _ = α * β + ∑ i ∈ s, f (r i) * e i := by linear_combination hsplit'
    rw [hid]
    have heSum : (∑ i ∈ s, f (r i) * e i) ∈ J ^ (n + 1) := by
      apply Ideal.sum_mem _
      intro i hi
      have hri : f (r i) ∈ J ^ n := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem f (hr i hi)
      have hei : e i ∈ J := he i hi
      have hmul : f (r i) * e i ∈ J ^ n * J := Ideal.mul_mem_mul hri hei
      simpa [pow_succ] using hmul
    have hab : α * β ∈ J ^ (n + n) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul hα hβ
    have hab' : α * β ∈ J ^ (n + 1) :=
      Ideal.pow_le_pow_right (by omega) hab
    exact (J ^ (n + 1)).add_mem hab' heSum

/-- A sequence `x` in an `I`-adically complete ring with `x n - x (n + 1) ∈ I ^ n` has a limit `L`
with `L - x n ∈ I ^ n` for all `n`. -/
private theorem exists_limit_of_sub_mem_pow {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (x : ℕ → R) (hx : ∀ n, x n - x (n + 1) ∈ I ^ n) :
    ∃ L : R, ∀ n, L - x n ∈ I ^ n := by
  have hC : ∀ {p q : ℕ}, p ≤ q → x p ≡ x q [SMOD (I ^ p • (⊤ : Submodule R R))] := by
    intro p q hpq
    induction q, hpq using Nat.le_induction with
    | base => simp [SModEq]
    | succ q hpq ih =>
        simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at ih ⊢
        have hadd : x p - x (q + 1) = (x p - x q) + (x q - x (q + 1)) := by ring
        rw [hadd]
        exact (I ^ p).add_mem ih ((Ideal.pow_le_pow_right hpq) (hx q))
  obtain ⟨L, hL⟩ := IsAdicComplete.toIsPrecomplete.prec hC
  refine ⟨L, fun n => ?_⟩
  have hn := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hn
  exact (I ^ n).neg_mem_iff.mp (by simpa [sub_eq_add_neg, add_comm] using hn)

/-- Cauchy sequences `u n, v n` in `B` and `h n` in `A` with `u n * v n - f (h n) ∈ J ^ n` have
limits in the adically complete rings satisfying `uLim * vLim = f hLim` exactly. -/
private theorem limits_of_relation_mod_pow
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J mB : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete mB B]
    (hJm : J ≤ mB) (hIleJ : Ideal.map f I ≤ J) (hJfg : J.FG)
    (u v : ℕ → B) (h : ℕ → A)
    (hu : ∀ n, u n - u (n + 1) ∈ J ^ n)
    (hv : ∀ n, v n - v (n + 1) ∈ J ^ n)
    (hh : ∀ n, h n - h (n + 1) ∈ I ^ n)
    (hrel : ∀ n, u n * v n - f (h n) ∈ J ^ n) :
    ∃ uLim vLim : B, ∃ hLim : A,
      (∀ n, uLim - u n ∈ J ^ n) ∧
      (∀ n, vLim - v n ∈ J ^ n) ∧
      (∀ n, hLim - h n ∈ I ^ n) ∧
      uLim * vLim = f hLim := by
  have hJcomplete : IsAdicComplete J B :=
    isAdicComplete_of_le_of_fg_of_isAdicComplete hJm inferInstance hJfg
  obtain ⟨uLim, hu'⟩ := exists_limit_of_sub_mem_pow J u hu
  obtain ⟨vLim, hv'⟩ := exists_limit_of_sub_mem_pow J v hv
  obtain ⟨hLim, hh'⟩ := exists_limit_of_sub_mem_pow I h hh
  have herror : ∀ n, uLim * vLim - f hLim ∈ J ^ n := by
    intro n
    have hprod : uLim * vLim - u n * v n ∈ J ^ n := by
      rw [show uLim * vLim - u n * v n = (uLim - u n) * vLim + u n * (vLim - v n) by ring]
      exact (J ^ n).add_mem (Ideal.mul_mem_right _ (J ^ n) (hu' n))
        ((J ^ n).mul_mem_left _ (hv' n))
    have hbase : f hLim - f (h n) ∈ J ^ n := by
      rw [← map_sub]
      refine Ideal.pow_right_mono hIleJ n ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem f (hh' n)
    have hsum : uLim * vLim - f hLim =
        (uLim * vLim - u n * v n) + (u n * v n - f (h n)) - (f hLim - f (h n)) := by ring
    rw [hsum]
    exact (J ^ n).sub_mem ((J ^ n).add_mem hprod (hrel n)) hbase
  have hz : uLim * vLim - f hLim = 0 := by
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := mB))
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_right_mono hJm n (herror n)
  exact ⟨uLim, vLim, hLim, hu', hv', hh', sub_eq_zero.mp hz⟩

/-- An approximate hypersurface relation at level `n`: elements `x, y : B` and `a : A` with
`x * y - f a` lying in `J ^ (n + 1)`. -/
private structure RelationApprox {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal B) (n : ℕ) where
  xval : B
  yval : B
  base : A
  error : B
  error_mem : error ∈ J ^ (n + 1)
  relation : xval * yval = f base + error

/-- When `A` surjects onto the residue field of `B` and `𝔪_B ≤ J + (u, v)`, every `b : B` has the
form `f a + u * b₁ + v * b₂ + e` with `a : A` and `e ∈ J`. -/
private theorem exists_decomposition_mod_ideal
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (J : Ideal B) (u v b : B)
    (hres : Function.Surjective (fun a : A => residue B (f a)))
    (hmax : maximalIdeal B ≤ J + Ideal.span {u, v}) :
    ∃ a : A, ∃ b₁ b₂ e : B,
      b = f a + u * b₁ + v * b₂ + e ∧ e ∈ J := by
  obtain ⟨a, ha⟩ := hres (residue B b)
  have hzero : residue B (b - f a) = 0 := by
    rw [map_sub, ← ha]
    exact sub_self _
  have hmem : b - f a ∈ maximalIdeal B :=
    (residue_eq_zero_iff (b - f a)).mp hzero
  have hsum : b - f a ∈ J + Ideal.span {u, v} := hmax hmem
  rw [add_eq_sup, Submodule.mem_sup] at hsum
  obtain ⟨e, he, z, hz, hEq⟩ := hsum
  obtain ⟨b₁, b₂, hz⟩ := Ideal.mem_span_pair.mp hz
  refine ⟨a, b₁, b₂, e, ?_, he⟩
  rw [← hz] at hEq
  calc
    b = f a + (b - f a) := by ring
    _ = f a + (e + (b₁ * u + b₂ * v)) := congrArg (fun z => f a + z) hEq.symm
    _ = f a + u * b₁ + v * b₂ + e := by ring

/-- If the images of `u` and `v` generate the maximal ideal of `B ⧸ J`, then `𝔪_B ≤ J + (u, v)`. -/
private theorem maximalIdeal_le_sup_of_quotient_generators
    {B : Type*} [CommRing B] [IsLocalRing B]
    (J : Ideal B) (u v : B)
    [IsLocalRing (B ⧸ J)]
    (hgen : maximalIdeal (B ⧸ J) ≤
      Ideal.span {Ideal.Quotient.mk J u, Ideal.Quotient.mk J v}) :
    maximalIdeal B ≤ J + Ideal.span {u, v} := by
  intro b hb
  have hmap : (Ideal.Quotient.mk J) b ∈ maximalIdeal (B ⧸ J) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem _ hb
  have hspan : Ideal.span {Ideal.Quotient.mk J u, Ideal.Quotient.mk J v} =
      (Ideal.span {u, v}).map (Ideal.Quotient.mk J) := by
    rw [Ideal.map_span]
    simp
  have hmem : b ∈ Ideal.span {u, v} ⊔ J := by
    apply (Ideal.mem_quotient_iff_mem_sup (I := J)
      (J := Ideal.span {u, v})).mp
    exact hspan ▸ hgen hmap
  rw [Ideal.add_eq_sup, sup_comm]
  exact hmem

/-- An element of `(I B) ^ (n + 1)` is a finitely supported `B`-linear combination of the images
`f r` of elements `r ∈ I ^ (n + 1)`. -/
private theorem exists_finsupp_relation_sum
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (n : ℕ) {z : B}
    (hz : z ∈ (Ideal.map f I) ^ (n + 1)) :
    ∃ c : (↥(I ^ (n + 1))) →₀ B,
      Finsupp.linearCombination B (fun r : ↥(I ^ (n + 1)) => f r.1) c = z := by
  rw [← Ideal.map_pow] at hz
  rw [Ideal.map] at hz
  have hrange : Set.range (fun r : ↥(I ^ (n + 1)) => f r.1) =
      f '' (↑(I ^ (n + 1)) : Set A) := by
    ext y
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, r.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange] at hz
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  refine ⟨c, ?_⟩
  simpa [Finsupp.linearCombination_apply] using hc

/-- An element of `(I B) ^ (n + 1)` is a finite sum `∑ f r * b r` with `r` ranging over elements
of `I ^ (n + 1)`. -/
private theorem exists_finite_relation_sum
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (n : ℕ) {z : B}
    (hz : z ∈ (Ideal.map f I) ^ (n + 1)) :
    ∃ s : Finset (↥(I ^ (n + 1))), ∃ b : ↥(I ^ (n + 1)) → B,
      z = ∑ r ∈ s, f r.1 * b r := by
  obtain ⟨c, hc⟩ := exists_finsupp_relation_sum f I n hz
  refine ⟨c.support, c, ?_⟩
  rw [← hc]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- An approximate relation at level `n` whose error expands in coefficients from `I ^ (n + 1)`
refines to one at level `n + 1` congruent to it modulo `J ^ (n + 1)` and `I ^ (n + 1)`. -/
private theorem relationApprox_step
    {A B ι : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = Ideal.map f I) (n : ℕ) (a : RelationApprox f J n)
    (s : Finset ι) (r : ι → A) (b b₁ b₂ e : ι → B) (a₀ : ι → A)
    (hr : ∀ i ∈ s, r i ∈ I ^ (n + 1))
    (hb : ∀ i ∈ s,
      b i = f (a₀ i) + a.xval * b₁ i + a.yval * b₂ i + e i)
    (hrel : a.xval * a.yval - f a.base = ∑ i ∈ s, f (r i) * b i)
    (he : ∀ i ∈ s, e i ∈ J) :
    ∃ a' : RelationApprox f J (n + 1),
      a.xval - a'.xval ∈ J ^ (n + 1) ∧ a.yval - a'.yval ∈ J ^ (n + 1) ∧
        a'.base - a.base ∈ I ^ (n + 1) := by
  obtain ⟨u', v', h', hu, hv, hh, herror⟩ :=
    have he' : ∀ i ∈ s, e i ∈ Ideal.map f I := by
      simpa [hJ] using he
    improve_relation_mod_pow f I a.xval a.yval a.base (n + 1) (by omega)
      s r b b₁ b₂ e a₀ hr hb hrel he'
  let e' := u' * v' - f h'
  have he' : e' ∈ J ^ (n + 2) := by
    rw [hJ]
    simpa [e'] using herror
  let a' : RelationApprox f J (n + 1) :=
    ⟨u', v', h', e', he', by dsimp [e']; ring⟩
  refine ⟨a', ?_, ?_, hh⟩
  · simpa [hJ] using hu
  · simpa [hJ] using hv

/-- Iterating refinements that stay congruent to `u₀, v₀` modulo `J` yields `u, v : B` and `h ∈ I`
with `u * v = f h` and `u - u₀, v - v₀ ∈ J`. -/
private theorem iterate_relation_mod_pow_with_close
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J mB : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete mB B]
    (hJm : J ≤ mB) (hIleJ : Ideal.map f I ≤ J) (hJfg : J.FG)
    (initial : RelationApprox f J 0) (hInitial : initial.base = 0)
    (u₀ v₀ : B) (hclose : initial.xval - u₀ ∈ J ∧ initial.yval - v₀ ∈ J)
    (step : ∀ n (a : RelationApprox f J n),
      a.xval - u₀ ∈ J → a.yval - v₀ ∈ J →
      ∃ b : RelationApprox f J (n + 1),
        a.xval - b.xval ∈ J ^ (n + 1) ∧ a.yval - b.yval ∈ J ^ (n + 1) ∧
          b.base - a.base ∈ I ^ (n + 1) ∧ b.xval - u₀ ∈ J ∧ b.yval - v₀ ∈ J) :
    ∃ uLim vLim : B, ∃ hLim : A,
      hLim ∈ I ∧ uLim * vLim = f hLim ∧
        uLim - u₀ ∈ J ∧ vLim - v₀ ∈ J := by
  classical
  let State (n : ℕ) :=
    {a : RelationApprox f J n // a.xval - u₀ ∈ J ∧ a.yval - v₀ ∈ J}
  let next : ∀ n, State n → State (n + 1) := fun n s =>
    let b := Classical.choose (step n s.1 s.2.1 s.2.2)
    ⟨b, (Classical.choose_spec (step n s.1 s.2.1 s.2.2)).2.2.2.1,
      (Classical.choose_spec (step n s.1 s.2.1 s.2.2)).2.2.2.2⟩
  let seq : ∀ n, State n := fun n => Nat.rec ⟨initial, hclose.1, hclose.2⟩
    (fun n s => next n s) n
  have hnext (n : ℕ) : seq (n + 1) = next n (seq n) := by
    simp [seq]
  have hu : ∀ n, (seq n).1.xval - (seq (n + 1)).1.xval ∈ J ^ n := by
    intro n
    have h := (Classical.choose_spec (step n (seq n).1 (seq n).2.1 (seq n).2.2)).1
    rw [hnext]
    exact Ideal.pow_le_pow_right n.le_succ h
  have hv : ∀ n, (seq n).1.yval - (seq (n + 1)).1.yval ∈ J ^ n := by
    intro n
    have h := (Classical.choose_spec (step n (seq n).1 (seq n).2.1 (seq n).2.2)).2.1
    rw [hnext]
    exact Ideal.pow_le_pow_right n.le_succ h
  have hh : ∀ n, (seq n).1.base - (seq (n + 1)).1.base ∈ I ^ n := by
    intro n
    have h := (Classical.choose_spec (step n (seq n).1 (seq n).2.1 (seq n).2.2)).2.2.1
    rw [hnext]
    exact Ideal.pow_le_pow_right n.le_succ (sub_mem_comm_iff.mp h)
  have hrel : ∀ n,
      (seq n).1.xval * (seq n).1.yval - f (seq n).1.base ∈ J ^ n := by
    intro n
    have heq : (seq n).1.xval * (seq n).1.yval - f (seq n).1.base =
        (seq n).1.error := by
      rw [(seq n).1.relation]
      ring
    rw [heq]
    exact Ideal.pow_le_pow_right n.le_succ (seq n).1.error_mem
  obtain ⟨uLim, vLim, hLim, huLim, hvLim, hhLim, hEq⟩ :=
    limits_of_relation_mod_pow f I J mB hJm hIleJ hJfg
      (fun n => (seq n).1.xval) (fun n => (seq n).1.yval) (fun n => (seq n).1.base)
      hu hv hh hrel
  have hlim1 : hLim - (seq 1).1.base ∈ I := by
    simpa [pow_one] using hhLim 1
  have hstep0 : (seq 1).1.base - (seq 0).1.base ∈ I := by
    show (seq (0 + 1)).1.base - (seq 0).1.base ∈ I
    rw [hnext 0]
    have hs :=
      (Classical.choose_spec (step 0 (seq 0).1 (seq 0).2.1 (seq 0).2.2)).2.2.1
    simpa [pow_one, next, State] using hs
  have hseq0 : (seq 0).1.base = 0 := by
    simpa [seq] using hInitial
  have hlim : hLim ∈ I := by
    simpa [hseq0] using I.add_mem hlim1 hstep0
  have huClose : uLim - u₀ ∈ J := by
    rw [← sub_add_sub_cancel uLim (seq 1).1.xval u₀]
    exact J.add_mem (by simpa [pow_one] using huLim 1) (seq 1).2.1
  have hvClose : vLim - v₀ ∈ J := by
    rw [← sub_add_sub_cancel vLim (seq 1).1.yval v₀]
    exact J.add_mem (by simpa [pow_one] using hvLim 1) (seq 1).2.2
  exact ⟨uLim, vLim, hLim, hlim, hEq, huClose, hvClose⟩

/-- If `u' ≡ u` and `v' ≡ v` modulo `J` and `𝔪_B ≤ J + (u, v)`, then `𝔪_B ≤ J + (u', v')`. -/
private theorem maximalIdeal_le_sup_span_of_sub_mem
    {B : Type*} [CommRing B] [IsLocalRing B] {J : Ideal B} {u v u' v' : B}
    (hu : u' - u ∈ J) (hv : v' - v ∈ J) (hmax : maximalIdeal B ≤ J + Ideal.span {u, v}) :
    maximalIdeal B ≤ J + Ideal.span {u', v'} := by
  refine hmax.trans (sup_le le_sup_left (Ideal.span_le.mpr ?_))
  rintro b (rfl | rfl)
  · simpa using (J ⊔ Ideal.span {u', v'}).add_mem
      (Ideal.mem_sup_left (J.neg_mem hu))
      (Ideal.mem_sup_right (Ideal.subset_span (by simp) : u' ∈ Ideal.span {u', v'}))
  · simpa using (J ⊔ Ideal.span {u', v'}).add_mem
      (Ideal.mem_sup_left (J.neg_mem hv))
      (Ideal.mem_sup_right (Ideal.subset_span (by simp) : v' ∈ Ideal.span {u', v'}))

/-- If `u * v ∈ J = I B` and `u, v` generate `𝔪_B` modulo `J`, they can be corrected modulo `J` to
a pair with `u' * v' = f h` for some `h ∈ I`. -/
private theorem exists_exact_relation_of_relation_mod_ideal
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (I : Ideal A) (J mB : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete mB B]
    (hJ : J = Ideal.map f I) (hJm : J ≤ mB) (hJfg : J.FG)
    (hres : Function.Surjective (fun a : A => residue B (f a)))
    (u v : B) (hmax : maximalIdeal B ≤ J + Ideal.span {u, v})
    (huv : u * v ∈ J) :
    ∃ uLim vLim : B, ∃ hLim : A,
      hLim ∈ I ∧ uLim * vLim = f hLim ∧
        uLim - u ∈ J ∧ vLim - v ∈ J := by
  have hIleJ : Ideal.map f I ≤ J := le_of_eq hJ.symm
  let initial : RelationApprox f J 0 :=
    ⟨u, v, 0, u * v, by simpa using huv, by simp⟩
  exact iterate_relation_mod_pow_with_close f I J mB hJm hIleJ hJfg
    initial (by rfl) u v ⟨by dsimp [initial]; simp, by dsimp [initial]; simp⟩ (by
      classical
      intro n a hcloseu hclosev
      -- The error coefficients can be decomposed using the current pair: it still
      -- generates the maximal ideal modulo `J` because it is congruent to `(u, v)`.
      have hmaxa : maximalIdeal B ≤ J + Ideal.span {a.xval, a.yval} :=
        maximalIdeal_le_sup_span_of_sub_mem hcloseu hclosev hmax
      have herror' : a.error ∈ (Ideal.map f I) ^ (n + 1) := by
        simpa [hJ] using a.error_mem
      obtain ⟨s, coeff, herror⟩ := exists_finite_relation_sum f I n herror'
      let r : ↥(I ^ (n + 1)) → A := fun i => i.1
      choose a₀ b₁ b₂ e hdecomp he using fun i : ↥(I ^ (n + 1)) =>
        exists_decomposition_mod_ideal f J a.xval a.yval (coeff i) hres hmaxa
      have hrel : a.xval * a.yval - f a.base =
          ∑ i ∈ s, f (r i) * coeff i := by
        rw [show a.xval * a.yval - f a.base = a.error by
          rw [a.relation]
          ring, herror]
      have hb : ∀ i ∈ s,
          coeff i = f (a₀ i) + a.xval * b₁ i + a.yval * b₂ i + e i := by
        intro i hi
        exact hdecomp i
      have he' : ∀ i ∈ s, e i ∈ J := by
        intro i hi
        exact he i
      obtain ⟨b, hb₁, hb₂, hb₃⟩ :=
        relationApprox_step f I J hJ n a s r coeff b₁ b₂ e a₀
          (fun i hi => i.2) hb hrel he'
      have hcorrU : a.xval - b.xval ∈ J :=
        (Ideal.pow_le_self (by omega)) hb₁
      have hcorrV : a.yval - b.yval ∈ J :=
        (Ideal.pow_le_self (by omega)) hb₂
      have hcloseU' : b.xval - u ∈ J := by
        rw [← sub_add_sub_cancel b.xval a.xval u]
        exact J.add_mem (sub_mem_comm_iff.mp hcorrU) hcloseu
      have hcloseV' : b.yval - v ∈ J := by
        rw [← sub_add_sub_cancel b.yval a.yval v]
        exact J.add_mem (sub_mem_comm_iff.mp hcorrV) hclosev
      exact ⟨b, hb₁, hb₂, hb₃, hcloseU', hcloseV'⟩)

/-- The quotient of a local ring by an ideal inside its maximal ideal is local. -/
private theorem isLocalRing_quotient_of_le_maximalIdeal {B : Type*} [CommRing B] [IsLocalRing B]
    {J : Ideal B} (hJ : J ≤ maximalIdeal B) : IsLocalRing (B ⧸ J) :=
  have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hJ)
  .of_surjective' _ Ideal.Quotient.mk_surjective

/-- For a local map from a complete local ring that is surjective on residue fields, with
`𝔪_B ≤ 𝔪_A B ⊔ K`, the composite `A → B ⧸ K` is surjective. -/
private theorem surjective_quotient_of_residue_surjective
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing B] [IsAdicComplete (maximalIdeal A) A]
    (f : A →+* B) [IsLocalHom f] (K : Ideal B) (hK : K ≤ maximalIdeal B)
    (hres : Function.Surjective ((residue B).comp f))
    (hm : maximalIdeal B ≤ (maximalIdeal A).map f ⊔ K) :
    Function.Surjective ((Ideal.Quotient.mk K).comp f) := by
  let q := Ideal.Quotient.mk K
  let g := q.comp f
  have : IsLocalRing (B ⧸ K) := isLocalRing_quotient_of_le_maximalIdeal hK
  have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have : IsLocalHom g := RingHom.isLocalHom_comp q f
  have hmap : (maximalIdeal A).map g = maximalIdeal (B ⧸ K) := by
    apply le_antisymm (map_maximalIdeal_le g)
    rw [← map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective]
    calc
      (maximalIdeal B).map q ≤ ((maximalIdeal A).map f ⊔ K).map q := Ideal.map_mono hm
      _ = (maximalIdeal A).map g := by
        simp [g, Ideal.map_sup, Ideal.map_map, q]
  have : IsHausdorff ((maximalIdeal A).map g) (B ⧸ K) := by
    rw [hmap]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := maximalIdeal A) g
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨a, ha⟩ := hres (residue B b)
  refine ⟨a, ?_⟩
  apply Ideal.Quotient.eq.mpr
  rw [hmap]
  show q (f a) - q b ∈ maximalIdeal (B ⧸ K)
  rw [← map_sub]
  refine map_maximalIdeal_le q <| Ideal.mem_map_of_mem q <| (residue_eq_zero_iff _).mp ?_
  simpa only [map_sub, RingHom.comp_apply] using sub_eq_zero.mpr ha

/-- Elements `x i ∈ 𝔪_B` generating `𝔪_B` modulo `𝔪_A B` give a surjective `A`-algebra map from
the power series ring in `n` variables onto `B` sending `X i` to `x i`. -/
private theorem exists_surjective_powerSeries_hom
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing B] [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    {n : ℕ} (x : Fin n → B) (hx : ∀ i, x i ∈ maximalIdeal B)
    (hres : Function.Surjective ((residue B).comp (algebraMap A B)))
    (hm : maximalIdeal B ≤ (maximalIdeal A).map (algebraMap A B) ⊔
      Ideal.span (Set.range x)) :
    ∃ F : MvPowerSeries (Fin n) A →ₐ[A] B,
      Function.Surjective F ∧ ∀ i, F (MvPowerSeries.X i) = x i := by
  let K := Ideal.span (Set.range x)
  have hK : K ≤ maximalIdeal B := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hx i)
  have hf := surjective_quotient_of_residue_surjective (algebraMap A B) K hK hres hm
  let : WithIdeal A := ⟨⊥⟩
  have : DiscreteTopology A := is_bot_adic_iff.mp rfl
  let : WithIdeal B := ⟨maximalIdeal B⟩
  obtain ⟨hcomplete, hT2⟩ := (IsAdic.isAdicComplete_iff (I := maximalIdeal B) rfl).mp
    (inferInstance : IsAdicComplete (maximalIdeal B) B)
  let := hcomplete
  let := hT2
  let ha : MvPowerSeries.HasEval x :=
    { hpow := fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hx i)
      tendsto_zero := by simp [Filter.cofinite_eq_bot] }
  let F : MvPowerSeries (Fin n) A →ₐ[A] B :=
    { __ := MvPowerSeries.eval₂Hom (φ := algebraMap A B) continuous_of_discreteTopology ha
      commutes' := fun a => by
        show MvPowerSeries.eval₂Hom (φ := algebraMap A B)
          continuous_of_discreteTopology ha (MvPowerSeries.C a) = _
        rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C] }
  have hFX : ∀ i, F (MvPowerSeries.X i) = x i :=
    fun i => by
      show MvPowerSeries.eval₂Hom (φ := algebraMap A B)
        continuous_of_discreteTopology ha (MvPowerSeries.X i) = _
      rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
  let L : Ideal (MvPowerSeries (Fin n) A) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : L.map F.toRingHom = K := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext hFX))
  have : IsHausdorff (L.map F.toRingHom) B := by
    rw [hmap]
    exact IsHausdorff.of_isLocalRing K B
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hK)
  refine ⟨F, ?_, hFX⟩
  apply surjective_of_mk_map_comp_surjective (I := L) F.toRingHom
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk K b)
  refine ⟨MvPowerSeries.C a, ?_⟩
  apply Ideal.Quotient.eq.mpr
  rw [hmap]
  show F (algebraMap A _ a) - b ∈ K
  rw [F.commutes]
  exact Ideal.Quotient.eq.mp ha

/-- The range of a function on `Fin 2` is the pair `{x 0, x 1}`. -/
private theorem range_fin_two {α : Type*} (x : Fin 2 → α) :
    Set.range x = {x 0, x 1} := by
  ext a
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- A power series in two variables is its constant term plus `X 0 * a + X 1 * b`. -/
private theorem exists_eq_constant_add_variables
    {A : Type*} [CommRing A] (p : MvPowerSeries (Fin 2) A) :
    ∃ a b : MvPowerSeries (Fin 2) A,
      p = MvPowerSeries.C (MvPowerSeries.constantCoeff p) +
        MvPowerSeries.X 0 * a + MvPowerSeries.X 1 * b := by
  classical
  have hmem : p - MvPowerSeries.C (MvPowerSeries.constantCoeff p) ∈
      Ideal.span ({MvPowerSeries.X 0, MvPowerSeries.X 1} :
        Set (MvPowerSeries (Fin 2) A)) := by
    have h := Stacks.MvPowerSeries.RegularParameters.QuotInitVars.mem_span_X_image_of_coeff_eq_zero
      (Finset.univ : Finset (Fin 2))
      (p - MvPowerSeries.C (MvPowerSeries.constantCoeff p)) (by
        intro d hd
        have hd0 : d = 0 := Finsupp.ext (fun i => hd i (Finset.mem_univ _))
        simp [hd0])
    simpa only [Finset.coe_univ, Set.image_univ, range_fin_two] using h
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
  exact ⟨a, b, by linear_combination -hab⟩

/-- Two ring maps out of `A⟦x, y⟧` agreeing on constants and on the variables are equal, provided
the images of the variables lie in an ideal `I` for which the target is `I`-adically Hausdorff. -/
private theorem powerSeries_hom_ext
    {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal B) [IsHausdorff I B]
    (f g : MvPowerSeries (Fin 2) A →+* B)
    (hC : ∀ a, f (MvPowerSeries.C a) = g (MvPowerSeries.C a))
    (hX : ∀ i, f (MvPowerSeries.X i) = g (MvPowerSeries.X i))
    (hfX : ∀ i, f (MvPowerSeries.X i) ∈ I) : f = g := by
  have hpow : ∀ n (p : MvPowerSeries (Fin 2) A), f p - g p ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro p
      obtain ⟨a, b, hp⟩ := exists_eq_constant_add_variables p
      have heq : f p - g p =
          f (MvPowerSeries.X 0) * (f a - g a) +
          f (MvPowerSeries.X 1) * (f b - g b) := by
        rw [hp]
        simp only [map_add, map_mul, ← hC, ← hX]
        ring
      rw [heq, pow_succ']
      exact (I * I ^ n).add_mem (Ideal.mul_mem_mul (hfX 0) (ih a))
        (Ideal.mul_mem_mul (hfX 1) (ih b))
  ext p
  apply sub_eq_zero.mp
  apply IsHausdorff.haus (inferInstance : IsHausdorff I B)
  intro n
  simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hpow n p

/-- Given `u, v ∈ 𝔪_B` lifting the node coordinates of the closed fibre `B ⧸ 𝔪_A B`, there is an
element `h ∈ 𝔪_A` and an `A`-algebra isomorphism `A⟦x, y⟧/(x y - h) ≃ B`. -/
private theorem exists_nodal_presentation_of_closed_fiber
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (u v : B) (hu : u ∈ maximalIdeal B) (hv : v ∈ maximalIdeal B)
    (hres : Function.Surjective ((residue B).comp (algebraMap A B)))
    (hmax : maximalIdeal B ≤ (maximalIdeal A).map (algebraMap A B) ⊔ Ideal.span {u, v})
    (huv : u * v ∈ (maximalIdeal A).map (algebraMap A B))
    (g : MvPowerSeries (Fin 2) A →ₐ[A]
      B ⧸ (maximalIdeal A).map (algebraMap A B))
    (hgX : g (MvPowerSeries.X 0) = Ideal.Quotient.mk _ u ∧
      g (MvPowerSeries.X 1) = Ideal.Quotient.mk _ v)
    (hgker : RingHom.ker g.toRingHom =
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} ⊔
        (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A))) :
    ∃ h : A, h ∈ maximalIdeal A ∧
      Nonempty ((MvPowerSeries (Fin 2) A ⧸
        Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) ≃ₐ[A] B) := by
  let J := (maximalIdeal A).map (algebraMap A B)
  have hJ : J ≤ maximalIdeal B := map_maximalIdeal_le _
  have : IsLocalRing (B ⧸ J) := isLocalRing_quotient_of_le_maximalIdeal hJ
  obtain ⟨u', v', h, hh, hrel, hcloseu, hclosev⟩ :=
    exists_exact_relation_of_relation_mod_ideal (algebraMap A B) (maximalIdeal A) J
      (maximalIdeal B) rfl hJ (IsNoetherian.noetherian J) hres u v hmax huv
  have hu' : u' ∈ maximalIdeal B := by simpa using (maximalIdeal B).add_mem (hJ hcloseu) hu
  have hv' : v' ∈ maximalIdeal B := by simpa using (maximalIdeal B).add_mem (hJ hclosev) hv
  have hmax' : maximalIdeal B ≤ J ⊔ Ideal.span {u', v'} :=
    maximalIdeal_le_sup_span_of_sub_mem hcloseu hclosev hmax
  obtain ⟨F, hF, hFX⟩ := exists_surjective_powerSeries_hom ![u', v']
    (by intro i; fin_cases i <;> simp [hu', hv']) hres (by
      simpa only [range_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using hmax')
  let q : B →ₐ[A] B ⧸ J := Ideal.Quotient.mkₐ A J
  have : IsLocalHom q.toRingHom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmod : q.comp F = g := by
    apply AlgHom.coe_ringHom_injective
    apply powerSeries_hom_ext (maximalIdeal (B ⧸ J))
    · intro a
      exact (q.comp F).commutes a |>.trans (g.commutes a).symm
    · intro i
      fin_cases i
      · show q (F (MvPowerSeries.X 0)) = g (MvPowerSeries.X 0)
        rw [hFX, hgX.1]
        exact Ideal.Quotient.eq.mpr hcloseu
      · show q (F (MvPowerSeries.X 1)) = g (MvPowerSeries.X 1)
        rw [hFX, hgX.2]
        exact Ideal.Quotient.eq.mpr hclosev
    · intro i
      show q (F (MvPowerSeries.X i)) ∈ _
      rw [hFX]
      apply map_maximalIdeal_le q.toRingHom
      apply Ideal.mem_map_of_mem
      fin_cases i
      · exact hu'
      · exact hv'
  let P := MvPowerSeries (Fin 2) A
  let r : P := MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h
  let I := Ideal.span {r}
  let m := (maximalIdeal A).map (algebraMap A P)
  have hr : F r = 0 := by
    show F (MvPowerSeries.X 0 * MvPowerSeries.X 1 - algebraMap A P h) = 0
    rw [map_sub, map_mul, hFX, hFX, F.commutes]
    exact sub_eq_zero.mpr hrel
  have hI : I ≤ RingHom.ker F.toRingHom := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hr)
  have hclosed : RingHom.ker F.toRingHom ≤ I ⊔ m := by
    have hle : RingHom.ker F.toRingHom ≤ RingHom.ker g.toRingHom := by
      intro b hb
      rw [← hmod]
      show q (F b) = 0
      rw [show F b = 0 from hb, map_zero]
    apply hle.trans
    rw [hgker]
    refine sup_le (Ideal.span_le.mpr ?_) le_sup_right
    rintro _ rfl
    have h₁ : r ∈ I := Ideal.subset_span (Set.mem_singleton _)
    have h₂ : MvPowerSeries.C h ∈ m := Ideal.mem_map_of_mem _ hh
    simpa [r] using (I ⊔ m).add_mem (Ideal.mem_sup_left h₁) (Ideal.mem_sup_right h₂)
  have : IsNoetherianRing P := mvPowerSeries_fin_isNoetherianRing A 2
  have hm : m ≤ (⊥ : Ideal P).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    show ¬IsUnit (MvPowerSeries.C a)
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C]
    exact ha
  have hker : RingHom.ker F.toRingHom = I := ker_eq_of_flat_closed_fiber F hF I hI hm hclosed
  exact ⟨h, hh, ⟨(Ideal.quotientEquivAlgOfEq A hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hF)⟩⟩

/-- A surjection `A⟦x, y⟧ → B ⧸ 𝔪_A B` with kernel `(x y) + 𝔪_A A⟦x, y⟧` gives `h ∈ 𝔪_A` and an
`A`-algebra isomorphism `A⟦x, y⟧/(x y - h) ≃ B`. -/
private theorem exists_nodal_presentation_of_surjective_closed_fiber
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (g : MvPowerSeries (Fin 2) A →ₐ[A]
      B ⧸ (maximalIdeal A).map (algebraMap A B)) (hg : Function.Surjective g)
    (hgker : RingHom.ker g.toRingHom =
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} ⊔
        (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A))) :
    ∃ h : A, h ∈ maximalIdeal A ∧
      Nonempty ((MvPowerSeries (Fin 2) A ⧸
        Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) ≃ₐ[A] B) := by
  let J := (maximalIdeal A).map (algebraMap A B)
  have hJ : J ≤ maximalIdeal B := map_maximalIdeal_le _
  have : IsLocalRing (B ⧸ J) := isLocalRing_quotient_of_le_maximalIdeal hJ
  let q : B →ₐ[A] B ⧸ J := Ideal.Quotient.mkₐ A J
  have : IsLocalHom q.toRingHom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom g.toRingHom := IsLocalHom.of_surjective _ hg
  have hq (b : B) : q b ∈ maximalIdeal (B ⧸ J) ↔ b ∈ maximalIdeal B := by
    show ¬IsUnit (q b) ↔ ¬IsUnit b
    exact not_congr ⟨isUnit_of_map_unit q.toRingHom b, IsUnit.map q.toRingHom⟩
  have hgX (i : Fin 2) : g (MvPowerSeries.X i) ∈ maximalIdeal (B ⧸ J) := by
    apply map_maximalIdeal_le g.toRingHom
    apply Ideal.mem_map_of_mem
    show ¬IsUnit (MvPowerSeries.X i : MvPowerSeries (Fin 2) A)
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  obtain ⟨u, huq⟩ := Ideal.Quotient.mk_surjective (g (MvPowerSeries.X 0))
  obtain ⟨v, hvq⟩ := Ideal.Quotient.mk_surjective (g (MvPowerSeries.X 1))
  have hu : u ∈ maximalIdeal B := (hq u).mp (huq ▸ hgX 0)
  have hv : v ∈ maximalIdeal B := (hq v).mp (hvq ▸ hgX 1)
  have hdecomp (b : B) : ∃ a : A, ∃ c d e : B,
      b = algebraMap A B a + u * c + v * d + e ∧ e ∈ J ∧
        (b ∈ maximalIdeal B → a ∈ maximalIdeal A) := by
    obtain ⟨p, hp⟩ := hg (q b)
    obtain ⟨c, d, hcd⟩ := exists_eq_constant_add_variables p
    obtain ⟨c', hc⟩ := Ideal.Quotient.mk_surjective (g c)
    obtain ⟨d', hd⟩ := Ideal.Quotient.mk_surjective (g d)
    let a := MvPowerSeries.constantCoeff p
    let w := algebraMap A B a + u * c' + v * d'
    have hw : q w = q b := by
      have hp' := congrArg g hcd
      rw [map_add, map_add, map_mul, map_mul, hp, ← huq, ← hvq, ← hc, ← hd] at hp'
      have hgc : g (MvPowerSeries.C (MvPowerSeries.constantCoeff p)) =
          q (algebraMap A B a) := (g.commutes a).trans (q.commutes a).symm
      rw [hgc] at hp'
      simpa [q, w] using hp'.symm
    refine ⟨a, c', d', b - w, ?_, Ideal.Quotient.eq.mp hw.symm, ?_⟩
    · dsimp [w]
      ring
    · intro hb
      have hgp : ¬IsUnit (g p) := by
        show g p ∈ maximalIdeal (B ⧸ J)
        rw [hp]
        exact (hq b).mpr hb
      have hpu : ¬IsUnit p := fun h => hgp (h.map g.toRingHom)
      show ¬IsUnit a
      exact fun h => hpu (MvPowerSeries.isUnit_iff_constantCoeff.mpr h)
  have hres : Function.Surjective ((residue B).comp (algebraMap A B)) := by
    intro b
    obtain ⟨b, rfl⟩ := residue_surjective b
    obtain ⟨a, c, d, e, hb, he, _⟩ := hdecomp b
    refine ⟨a, ?_⟩
    show residue B (algebraMap A B a) = residue B b
    rw [hb, map_add, map_add, map_add, map_mul, map_mul,
      (residue_eq_zero_iff u).mpr hu, (residue_eq_zero_iff v).mpr hv,
      (residue_eq_zero_iff e).mpr (hJ he)]
    simp
  have hmax : maximalIdeal B ≤ J ⊔ Ideal.span {u, v} := by
    intro b hb
    obtain ⟨a, c, d, e, rfl, he, ha⟩ := hdecomp b
    have ham : algebraMap A B a ∈ J := Ideal.mem_map_of_mem _ (ha hb)
    have huc : u * c ∈ Ideal.span ({u, v} : Set B) :=
      Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have hvd : v * d ∈ Ideal.span ({u, v} : Set B) :=
      Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    apply Submodule.mem_sup.mpr
    exact ⟨algebraMap A B a + e, J.add_mem ham he, u * c + v * d,
      Ideal.add_mem _ huc hvd, by ring⟩
  have huv : u * v ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hxy : MvPowerSeries.X 0 * MvPowerSeries.X 1 ∈ RingHom.ker g.toRingHom := by
      rw [hgker]
      exact (show Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} ≤
        Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} ⊔
          (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A)) from le_sup_left)
          (Ideal.subset_span (Set.mem_singleton _))
    change g (MvPowerSeries.X 0 * MvPowerSeries.X 1) = 0 at hxy
    rw [map_mul, ← huq, ← hvq] at hxy
    simpa only [map_mul] using hxy
  exact exists_nodal_presentation_of_closed_fiber u v hu hv hres hmax huv g
    ⟨huq.symm, hvq.symm⟩ hgker

/-- An `A`-algebra isomorphism `A⟦x, y⟧/((x y) + 𝔪_A) ≃ B ⧸ 𝔪_A B` gives `h ∈ 𝔪_A` and an
isomorphism `A⟦x, y⟧/(x y - h) ≃ₐ[A] B`. -/
private theorem exists_nodal_presentation_of_closed_fiber_algEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (e : (MvPowerSeries (Fin 2) A ⧸
      (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} ⊔
        (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A)))) ≃ₐ[A]
        B ⧸ (maximalIdeal A).map (algebraMap A B)) :
    ∃ h : A, h ∈ maximalIdeal A ∧
      Nonempty ((MvPowerSeries (Fin 2) A ⧸
        Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) ≃ₐ[A] B) := by
  let K : Ideal (MvPowerSeries (Fin 2) A) :=
    Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} ⊔
      (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A))
  let g := e.toAlgHom.comp (Ideal.Quotient.mkₐ A K)
  apply exists_nodal_presentation_of_surjective_closed_fiber g
    (e.surjective.comp Ideal.Quotient.mk_surjective)
  ext p
  show e (Ideal.Quotient.mk K p) = 0 ↔ p ∈ K
  rw [map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- For a Noetherian local ring `A` with residue field `κ`, there is an `A`-algebra isomorphism
`A⟦x, y⟧/((x y) + 𝔪_A) ≃ κ⟦x, y⟧/(x y)`. -/
private theorem quotient_powerSeries_algEquiv_residueField
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Nonempty ((MvPowerSeries (Fin 2) A ⧸
      (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} ⊔
        (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A)))) ≃ₐ[A]
      (MvPowerSeries (Fin 2) (ResidueField A) ⧸
        Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} :
          Set (MvPowerSeries (Fin 2) (ResidueField A))))) := by
  classical
  let f : MvPowerSeries (Fin 2) A →ₐ[A] MvPowerSeries (Fin 2) (ResidueField A) :=
    MvPowerSeries.mapAlgHom (Algebra.ofId A (ResidueField A))
  have hf : Function.Surjective f := by
    intro p
    choose c hc using fun d : Fin 2 →₀ ℕ => residue_surjective (MvPowerSeries.coeff d p)
    refine ⟨(fun d => c d), ?_⟩
    ext d
    exact hc d
  let I : Ideal (MvPowerSeries (Fin 2) A) :=
    Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}
  let K : Ideal (MvPowerSeries (Fin 2) (ResidueField A)) :=
    Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}
  have hfI : I.map f.toRingHom = K := by
    simp [I, K, Ideal.map_span, f, MvPowerSeries.mapAlgHom_apply]
  have hfker : RingHom.ker f.toRingHom =
      (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A)) := by
    show RingHom.ker (MvPowerSeries.map (residue A)) = _
    rw [MvPowerSeries.ker_map_of_fg (residue A)
      (IsNoetherian.noetherian _), ker_residue]
    rfl
  let g := (Ideal.Quotient.mkₐ A K).comp f
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hf
  have hgker : RingHom.ker g.toRingHom =
      I ⊔ (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A)) := by
    show RingHom.ker ((Ideal.Quotient.mk K).comp f.toRingHom) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← hfI,
      Ideal.comap_map_of_surjective f.toRingHom hf, ← RingHom.ker_eq_comap_bot, hfker]
  exact ⟨(Ideal.quotientEquivAlgOfEq A hgker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg)⟩

/-- A ring isomorphism `K ≃+* L` induces an isomorphism `K⟦x, y⟧/(x y) ≃+* L⟦x, y⟧/(x y)`. -/
private noncomputable def nodalPowerSeriesQuotientRingEquiv
    {K L : Type*} [CommRing K] [CommRing L] (e : K ≃+* L) :
    (MvPowerSeries (Fin 2) K ⧸
      Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} :
        Set (MvPowerSeries (Fin 2) K))) ≃+*
    (MvPowerSeries (Fin 2) L ⧸
      Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} :
        Set (MvPowerSeries (Fin 2) L))) := by
  let E : MvPowerSeries (Fin 2) K ≃+* MvPowerSeries (Fin 2) L :=
    RingEquiv.ofRingHom (MvPowerSeries.map e.toRingHom)
      (MvPowerSeries.map e.symm.toRingHom)
      (by rw [← MvPowerSeries.map_comp]; simp only [RingEquiv.toRingHom_eq_coe,
        e.comp_symm, MvPowerSeries.map_id])
      (by rw [← MvPowerSeries.map_comp]; simp only [RingEquiv.toRingHom_eq_coe,
        e.symm_comp, MvPowerSeries.map_id])
  let IK : Ideal (MvPowerSeries (Fin 2) K) :=
    Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}
  let IL : Ideal (MvPowerSeries (Fin 2) L) :=
    Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}
  have hI : IL = IK.map E := by
    simp [IK, IL, Ideal.map_span, E, MvPowerSeries.map_X]
  exact Ideal.quotientEquiv IK IL E hI

/-- The isomorphism induced by `e : K ≃+* L` carries the class of the constant `c` to the class
of the constant `e c`. -/
private lemma nodalPowerSeriesQuotientRingEquiv_algebraMap
    {K L : Type*} [CommRing K] [CommRing L] (e : K ≃+* L) (c : K) :
    nodalPowerSeriesQuotientRingEquiv e (algebraMap K _ c) =
      algebraMap L _ (e c) := by
  show Ideal.Quotient.mk _ (MvPowerSeries.map e.toRingHom (MvPowerSeries.C c)) = _
  rw [MvPowerSeries.map_C]
  rfl

/-- The kernel of the `n`-th evaluation of the `𝔪`-adic completion of `R` onto `R ⧸ 𝔪 ^ n` is the
`n`-th power of the maximal ideal of the completion. -/
private lemma ker_eval_pow (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) n).toRingHom =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  ext x
  rw [RingHom.mem_ker]
  show AdicCompletion.evalₐ (maximalIdeal R) n x = 0 ↔ _
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing]
  have heq : maximalIdeal R ^ n * ⊤ = maximalIdeal R ^ n := by simp
  have hinj : Function.Injective (Ideal.Quotient.factor (le_of_eq heq)) := by
    simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker] using
      Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
  simpa [← AdicCompletion.factor_eval_eq_evalₐ] using map_eq_zero_iff _ hinj

/-- Every element of the `𝔪`-adic completion of `R` agrees with the image of some `r : R` modulo
the `n`-th power of the maximal ideal of the completion. -/
private lemma completion_approx (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (x : AdicCompletion (maximalIdeal R) R) (n : ℕ) :
    ∃ r : R, x - algebraMap R _ r ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) n x)
  refine ⟨r, ?_⟩
  rw [← ker_eval_pow R n, RingHom.mem_ker, map_sub]
  simpa using sub_eq_zero.mpr hr.symm

/-- Two ring maps out of the completion of `R` that agree on `R` and carry its maximal ideal into
an ideal `J` for which the target is `J`-adically Hausdorff are equal. -/
private lemma completion_hom_ext {R D : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing D] (J : Ideal D) [IsHausdorff J D]
    (f g : AdicCompletion (maximalIdeal R) R →+* D)
    (hf : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).map f ≤ J)
    (hg : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).map g ≤ J)
    (h : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g := by
  ext x
  apply sub_eq_zero.mp
  apply IsHausdorff.haus (inferInstance : IsHausdorff J D)
  intro n
  obtain ⟨r, hr⟩ := completion_approx R x n
  have hp (φ : AdicCompletion (maximalIdeal R) R →+* D)
      (hφ : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).map φ ≤ J) :
      φ (x - algebraMap R _ r) ∈ J ^ n := by
    apply (Ideal.pow_right_mono hφ n)
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem φ hr
  have heq : f x - g x = f (x - algebraMap R _ r) - g (x - algebraMap R _ r) := by
    have hh := RingHom.congr_fun h r
    dsimp only [RingHom.comp_apply] at hh
    simp only [map_sub, hh]
    ring
  simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top, heq] using
    (J ^ n).sub_mem (hp f hf) (hp g hg)

/-- The composite of `R → R^` with the residue map onto the residue field of the completion is
surjective. -/
private lemma completion_residue_surjective (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    Function.Surjective ((residue (AdicCompletion (maximalIdeal R) R)).comp
      (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  intro z
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨r, hr⟩ := completion_approx R x 1
  refine ⟨r, ?_⟩
  apply eq_of_sub_eq_zero
  rw [RingHom.comp_apply, ← map_sub, residue_eq_zero_iff]
  convert (maximalIdeal (AdicCompletion (maximalIdeal R) R)).neg_mem
    (by simpa only [pow_one] using hr) using 1
  ring

/-- The residue field of a Noetherian local ring is isomorphic to the residue field of its
maximal-adic completion. -/
private noncomputable def completionResidueFieldEquiv (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    ResidueField R ≃+* ResidueField (AdicCompletion (maximalIdeal R) R) :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap R _))
    (AdicCompletion.residueField_map_bijective R)

/-- For `A` the completion of `R` and `D` an `A`-algebra killed by `𝔪_A`, a ring isomorphism
`κ(R)⟦x, y⟧/(x y) ≃+* D` compatible with `R` upgrades to an `A`-algebra isomorphism
`κ(A)⟦x, y⟧/(x y) ≃ₐ[A] D`. -/
private theorem nodalPowerSeriesQuotientAlgEquiv_of_completion
    (R D : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing D]
    [Algebra (AdicCompletion (maximalIdeal R) R) D]
    (e : (MvPowerSeries (Fin 2) (ResidueField R) ⧸
      Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} :
        Set (MvPowerSeries (Fin 2) (ResidueField R)))) ≃+* D)
    (hm : ∀ a ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R),
      algebraMap (AdicCompletion (maximalIdeal R) R) D a = 0)
    (he : ∀ r : R, e (algebraMap (ResidueField R) _ (residue R r)) =
      algebraMap (AdicCompletion (maximalIdeal R) R) D
        (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) :
    Nonempty ((MvPowerSeries (Fin 2) (ResidueField (AdicCompletion (maximalIdeal R) R)) ⧸
      Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} :
        Set (MvPowerSeries (Fin 2) (ResidueField (AdicCompletion (maximalIdeal R) R)))))
        ≃ₐ[AdicCompletion (maximalIdeal R) R] D) := by
  let A := AdicCompletion (maximalIdeal R) R
  let eκ := completionResidueFieldEquiv R
  let eN := nodalPowerSeriesQuotientRingEquiv eκ.symm
  let E := eN.trans e
  refine ⟨{ __ := E, commutes' := ?_ }⟩
  intro a
  show E (algebraMap A _ a) = algebraMap A D a
  obtain ⟨r, hr⟩ := completion_approx R a 1
  have hres : residue A a = residue A (algebraMap R A r) := by
    apply sub_eq_zero.mp
    rw [← map_sub, residue_eq_zero_iff]
    simpa only [pow_one] using hr
  have hκ : eκ.symm (residue A (algebraMap R A r)) = residue R r := by
    rw [← ResidueField.map_residue (algebraMap R A)]
    simpa only [eκ, completionResidueFieldEquiv, RingEquiv.ofBijective_apply] using
      eκ.symm_apply_apply (residue R r)
  have ha : algebraMap A D a = algebraMap A D (algebraMap R A r) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact hm _ (by simpa only [pow_one] using hr)
  rw [ha]
  show e (eN (algebraMap A _ a)) = _
  rw [IsScalarTower.algebraMap_apply A (ResidueField A)]
  show e (eN (algebraMap (ResidueField A) _ (residue A a))) = _
  rw [hres, nodalPowerSeriesQuotientRingEquiv_algebraMap, hκ]
  exact he r

/-- The completion of `R ⧸ I` is `R`-isomorphic to `R^ ⧸ I R^`, the quotient of the completion of
`R` by the ideal generated by `I`. -/
private theorem completion_quotient_equiv (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    Nonempty (AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I) ≃ₐ[R]
      (AdicCompletion (maximalIdeal R) R ⧸
        I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))) := by
  let H := AdicCompletion (maximalIdeal R) R
  let J := I.map (algebraMap R H)
  let D := H ⧸ J
  let Q := R ⧸ I
  let qR : R →+* Q := Ideal.Quotient.mk I
  let qH : H →+* D := Ideal.Quotient.mk J
  let g : Q →+* D := Ideal.quotientMap J (algebraMap R H) Ideal.le_comap_map
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hJ : J ≠ ⊤ := by
    apply ne_top_of_le_ne_top (maximalIdeal.isMaximal H).ne_top
    show I.map (algebraMap R H) ≤ maximalIdeal H
    exact (Ideal.map_mono (le_maximalIdeal hI)).trans (map_maximalIdeal_le _)
  have : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing D := IsLocalRing.of_surjective' qH Ideal.Quotient.mk_surjective
  have : IsLocalHom qH := IsLocalHom.of_surjective qH Ideal.Quotient.mk_surjective
  have hg : g.comp qR = qH.comp (algebraMap R H) := by ext; rfl
  have hmax : (maximalIdeal Q).map g = maximalIdeal D := by
    rw [← map_maximalIdeal_of_surjective qR Ideal.Quotient.mk_surjective,
      Ideal.map_map, hg, ← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map]
    exact map_maximalIdeal_of_surjective qH Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap Q D) :=
    ((IsLocalRing.local_hom_TFAE g).out 3 1).mp hmax.le
  have : Module.Flat Q D := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor H I).toLinearEquiv
  have hres : Function.Bijective (ResidueField.map g) := by
    refine ⟨RingHom.injective _, fun z => ?_⟩
    obtain ⟨d, rfl⟩ := residue_surjective z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨r, hr⟩ := completion_approx R x 1
    refine ⟨residue Q (qR r), ?_⟩
    rw [ResidueField.map_residue]
    apply eq_of_sub_eq_zero
    rw [← map_sub, residue_eq_zero_iff]
    show qH (algebraMap R H r) - qH x ∈ maximalIdeal D
    rw [← map_sub]
    apply (map_maximalIdeal_le qH)
    apply Ideal.mem_map_of_mem
    convert (maximalIdeal H).neg_mem (by simpa only [pow_one] using hr) using 1
    ring
  obtain ⟨e, he⟩ := exists_adicCompletion_ringEquiv_of_flat
    (A := Q) (B := D) (IsNoetherian.noetherian _) hmax hres
  have : IsAdicComplete (maximalIdeal D) D :=
    (quotient_isNoetherianCompleteLocalRing
      (show IsNoetherianCompleteLocalRing H from ⟨inferInstance, inferInstance, inferInstance⟩)
      J hJ).isComplete
  let E := e.trans (AdicCompletion.ofAlgEquiv (maximalIdeal D)).symm.toRingEquiv
  refine ⟨{ __ := E, commutes' := ?_ }⟩
  intro r
  show (AdicCompletion.ofAlgEquiv (maximalIdeal D)).symm
    (e (algebraMap Q (AdicCompletion (maximalIdeal Q) Q) (qR r))) = _
  rw [he]
  show (AdicCompletion.ofAlgEquiv (maximalIdeal D)).symm
    ((AdicCompletion.ofAlgEquiv (maximalIdeal D)) (g (qR r))) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- Evaluating at level `n` the completion map induced by `g : C →+* D` gives the map
`C ⧸ J ^ n → D ⧸ I ^ n` induced by `g`. -/
private lemma eval_adicCompletionMap {C D : Type*} [CommRing C] [CommRing D]
    (g : C →+* D) (J : Ideal C) (I : Ideal D) (hg : J.map g ≤ I)
    (n : ℕ) (a : AdicCompletion J C) :
    AdicCompletion.evalₐ I n (adicCompletionMap g J I hg a) =
      Ideal.quotientMap (I ^ n) g
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]; exact Ideal.pow_right_mono hg n))
        (AdicCompletion.evalₐ J n a) := by
  unfold adicCompletionMap
  rw [AdicCompletion.evalₐ_liftRingHom]
  rfl

/-- Maps of adic completions compose: the completion map of `j` after that of `g` is the
completion map of `j.comp g`. -/
private lemma adicCompletionMap_comp {C D E : Type*}
    [CommRing C] [CommRing D] [CommRing E]
    (g : C →+* D) (j : D →+* E) (I : Ideal C) (J : Ideal D) (K : Ideal E)
    (hg : I.map g ≤ J) (hj : J.map j ≤ K) :
    (adicCompletionMap j J K hj).comp (adicCompletionMap g I J hg) =
      adicCompletionMap (j.comp g) I K
        (by rw [← Ideal.map_map]; exact (Ideal.map_mono hg).trans hj) := by
  refine RingHom.ext fun a => AdicCompletion.ext_evalₐ fun n => ?_
  simp only [RingHom.comp_apply, eval_adicCompletionMap]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  rw [← hc]
  rfl

/-- The map of `I`-adic completions induced by the identity of `C` is the identity. -/
private lemma adicCompletionMap_id {C : Type*} [CommRing C] (I : Ideal C)
    (h : I.map (RingHom.id C) ≤ I) :
    adicCompletionMap (RingHom.id C) I I h = RingHom.id _ := by
  refine RingHom.ext fun a => AdicCompletion.ext_evalₐ fun n => ?_
  simp only [RingHom.id_apply, eval_adicCompletionMap]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  rw [← hc]
  rfl

/-- A ring isomorphism of local rings induces an isomorphism of their maximal-adic completions. -/
private noncomputable def completionRingEquiv {C D : Type*}
    [CommRing C] [CommRing D] [IsLocalRing C] [IsLocalRing D] (e : C ≃+* D) :
    AdicCompletion (maximalIdeal C) C ≃+* AdicCompletion (maximalIdeal D) D := by
  letI : IsLocalHom e.toRingHom := isLocalHom_of_leftInverse e.symm e.left_inv
  letI : IsLocalHom e.symm.toRingHom := isLocalHom_of_leftInverse e e.right_inv
  exact RingEquiv.ofRingHom
    (adicCompletionMap e.toRingHom _ _ (map_maximalIdeal_le e.toRingHom))
    (adicCompletionMap e.symm.toRingHom _ _
      (map_maximalIdeal_le e.symm.toRingHom))
    (by rw [adicCompletionMap_comp]; simpa using adicCompletionMap_id (maximalIdeal D) _)
    (by rw [adicCompletionMap_comp]; simpa using adicCompletionMap_id (maximalIdeal C) _)

/-- The induced isomorphism of completions carries the image of `c : C` to the image of `e c`. -/
private lemma completionRingEquiv_algebraMap {C D : Type*}
    [CommRing C] [CommRing D] [IsLocalRing C] [IsLocalRing D]
    (e : C ≃+* D) (c : C) :
    completionRingEquiv e (algebraMap C _ c) = algebraMap D _ (e c) := by
  let : IsLocalHom e.toRingHom := isLocalHom_of_leftInverse e.symm e.left_inv
  exact RingHom.congr_fun (adicCompletionMap_comp_algebraMap e.toRingHom _ _
    (map_maximalIdeal_le e.toRingHom)) c

/-- A `k`-algebra isomorphism of local `k`-algebras induces a `k`-algebra isomorphism of their
maximal-adic completions. -/
private noncomputable def completionAlgEquiv {k C D : Type*}
    [CommRing k] [CommRing C] [CommRing D]
    [IsLocalRing C] [IsLocalRing D] [Algebra k C] [Algebra k D]
    (e : C ≃ₐ[k] D) :
    AdicCompletion (maximalIdeal C) C ≃ₐ[k]
      AdicCompletion (maximalIdeal D) D := by
  refine { __ := completionRingEquiv e.toRingEquiv, commutes' := ?_ }
  intro c
  change completionRingEquiv e.toRingEquiv
    (algebraMap C _ (algebraMap k C c)) =
      algebraMap D _ (algebraMap k D c)
  rw [completionRingEquiv_algebraMap]
  congr 1
  exact e.commutes c

/-- For an open subscheme `U` of a `k`-scheme `X`, the stalk of `X` at a point of `U` is
`k`-isomorphic to the stalk of `U` there. -/
private noncomputable def openStalkAlgEquiv
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (U : X.Opens) (x : U) :
    let kToStalkX : k →+* X.presheaf.stalk x.1 :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x.1 trivial).hom
    let kToStalkU : k →+* U.toScheme.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop ≫
        U.toScheme.presheaf.germ ⊤ x trivial).hom
    letI : Algebra k (X.presheaf.stalk x.1) := kToStalkX.toAlgebra
    letI : Algebra k (U.toScheme.presheaf.stalk x) := kToStalkU.toAlgebra
    X.presheaf.stalk x.1 ≃ₐ[k] U.toScheme.presheaf.stalk x := by
  let kToStalkX : k →+* X.presheaf.stalk x.1 :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x.1 trivial).hom
  let kToStalkU : k →+* U.toScheme.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop ≫
      U.toScheme.presheaf.germ ⊤ x trivial).hom
  letI : Algebra k (X.presheaf.stalk x.1) := kToStalkX.toAlgebra
  letI : Algebra k (U.toScheme.presheaf.stalk x) := kToStalkU.toAlgebra
  let e := (U.stalkIso x).symm.commRingCatIsoToRingEquiv
  refine { __ := e, commutes' := ?_ }
  intro c
  have h2 : X.presheaf.germ ⊤ x.1 trivial ≫ U.ι.stalkMap x =
      U.ι.appTop ≫ U.toScheme.presheaf.germ ⊤ x trivial :=
    Scheme.Hom.germ_stalkMap U.ι ⊤ x trivial
  have h : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x.1 trivial) ≫ U.ι.stalkMap x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop ≫
        U.toScheme.presheaf.germ ⊤ x trivial :=
    calc ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
            X.presheaf.germ ⊤ x.1 trivial) ≫ U.ι.stalkMap x
        = (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
            (X.presheaf.germ ⊤ x.1 trivial ≫ U.ι.stalkMap x) :=
          (Category.assoc _ _ _).trans
            (congrArg ((Scheme.ΓSpecIso (.of k)).inv ≫ ·) (Category.assoc _ _ _))
      _ = (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
            (U.ι.appTop ≫ U.toScheme.presheaf.germ ⊤ x trivial) := by rw [h2]
      _ = (Scheme.ΓSpecIso (.of k)).inv ≫ (f.appTop ≫ U.ι.appTop) ≫
            U.toScheme.presheaf.germ ⊤ x trivial :=
          congrArg ((Scheme.ΓSpecIso (.of k)).inv ≫ ·) (Category.assoc _ _ _).symm
      _ = (Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop ≫
            U.toScheme.presheaf.germ ⊤ x trivial := by
          rw [Scheme.Hom.comp_appTop]
  change (U.stalkIso x).inv.hom (kToStalkX c) = kToStalkU c
  rw [U.stalkIso_inv]
  exact ConcreteCategory.congr_hom h c

/-- A point of a subtype whose image is a closed point of the ambient space is a closed point. -/
private theorem isClosed_singleton_of_val {X : Type*} [TopologicalSpace X] {p : X → Prop}
    {x : Subtype p} (h : IsClosed ({x.1} : Set X)) : IsClosed ({x} : Set (Subtype p)) := by
  have := h.preimage (continuous_subtype_val (p := p))
  rwa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] at this

/-- A point of an open subscheme `U ⊆ X` that is an ordinary double point of `X` is an ordinary
double point of `U`. -/
private theorem ordinaryNode_of_open
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (U : X.Opens) (x : U) (hx : IsOrdinaryDoublePoint k X x.1) :
    letI : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ (X ↘ Spec (.of k))⟩
    IsOrdinaryDoublePoint k U.toScheme x := by
  let f := X ↘ Spec (.of k)
  let : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ f⟩
  have hclosed : IsClosed ({x} : Set U) := isClosed_singleton_of_val hx.1
  let kToStalkX : k →+* X.presheaf.stalk x.1 :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x.1 trivial).hom
  let kToStalkU : k →+* U.toScheme.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop ≫
      U.toScheme.presheaf.germ ⊤ x trivial).hom
  let : Algebra k (X.presheaf.stalk x.1) := kToStalkX.toAlgebra
  let : Algebra k (U.toScheme.presheaf.stalk x) := kToStalkU.toAlgebra
  let e := openStalkAlgEquiv k X f U x
  have : IsLocalRing (U.toScheme.presheaf.stalk x) := e.toRingEquiv.isLocalRing
  let : Algebra k (multicross k 2) := multicrossAlgebra k 2
  have hcompletion : Nonempty
      (AdicCompletion (maximalIdeal (X.presheaf.stalk x.1))
        (X.presheaf.stalk x.1) ≃ₐ[k] multicross k 2) := hx.2
  obtain ⟨a⟩ := hcompletion
  exact ⟨hclosed, ⟨(completionAlgEquiv e).symm.trans a⟩⟩

/-- Being an ordinary double point is transported along an isomorphism of schemes over `Spec k`. -/
private theorem ordinaryNode_of_iso
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (e : X ≅ Y)
    (he : e.hom ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k)) (x : X) :
    IsOrdinaryDoublePoint k X x ↔ IsOrdinaryDoublePoint k Y (e.hom x) := by
  let : Algebra k (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
  let : Algebra k (Y.presheaf.stalk (e.hom x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop ≫
      Y.presheaf.germ ⊤ (e.hom x) (by simp)).hom.toAlgebra
  let E : Y.presheaf.stalk (e.hom x) ≃ₐ[k] X.presheaf.stalk x :=
    { (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv with
      commutes' := by
        intro a
        show (e.hom.stalkMap x).hom
          (((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop ≫
            Y.presheaf.germ ⊤ (e.hom x) (by simp)).hom a) =
          (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
            X.presheaf.germ ⊤ x (by simp)).hom a)
        have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop ≫
            Y.presheaf.germ ⊤ (e.hom x) (by simp) ≫ e.hom.stalkMap x =
            (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
            X.presheaf.germ ⊤ x (by simp) := by
          rw [Scheme.Hom.germ_stalkMap]
          rw [← he]
          simp only [Scheme.Hom.appTop, TopologicalSpace.Opens.map_top,
            Scheme.Hom.comp_app, Iso.cancel_iso_inv_left]
          exact (Category.assoc _ _ _).symm
        exact ConcreteCategory.congr_hom h a }
  let : Algebra k (multicross k 2) := multicrossAlgebra k 2
  have hc : IsClosed ({x} : Set X) ↔ IsClosed ({e.hom x} : Set Y) := by
    simpa using (e.hom.homeomorph.isClosed_image (s := {x})).symm
  rw [isOrdinaryDoublePoint_iff, isOrdinaryDoublePoint_iff, hc]
  apply and_congr_right
  intro _
  let Ehat := completionAlgEquiv E
  show Nonempty (_ ≃ₐ[k] _) ↔ Nonempty (_ ≃ₐ[k] _)
  exact ⟨fun ⟨a⟩ => ⟨Ehat.trans a⟩, fun ⟨a⟩ => ⟨Ehat.symm.trans a⟩⟩

/-- A point of an open subscheme `U ⊆ X` that is a node of `X` is a node of `U`. -/
private theorem node_of_open
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (U : X.Opens) (x : U) (hx : IsNode k X x.1) :
    letI : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ (X ↘ Spec (.of k))⟩
    IsNode k U.toScheme x := by
  let f := X ↘ Spec (.of k)
  let K := AlgebraicClosure k
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y : Scheme.{u} := pullback f g
  let Z : Scheme.{u} := pullback (U.ι ≫ f) g
  let p : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ Spec (.of K) := pullback.snd f g
  let pZ : Z ⟶ U := pullback.fst (U.ι ≫ f) g
  let qZ : Z ⟶ Spec (.of K) := pullback.snd (U.ι ≫ f) g
  let W : Y.Opens := p ⁻¹ᵁ U
  let e : Z ≅ W.toScheme :=
    (pullbackRightPullbackFstIso f g U.ι).symm ≪≫
      pullbackSymmetry U.ι p ≪≫ pullbackRestrictIsoRestrict p U
  have heY : e.hom ≫ W.ι = pullback.lift (pZ ≫ U.ι) qZ (by
      rw [Category.assoc, pullback.condition]) := by
    apply pullback.hom_ext
    · simp only [W, e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        pullback.lift_fst,
        pullbackRestrictIsoRestrict_hom_ι_assoc,
        pullbackSymmetry_hom_comp_fst_assoc]
      rw [← pullback.condition (f := U.ι) (g := p)]
      exact congrArg (fun h => h ≫ U.ι)
        (pullbackRightPullbackFstIso_inv_fst f g U.ι)
    · simp only [W, e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        pullback.lift_snd,
        pullbackRestrictIsoRestrict_hom_ι_assoc,
        pullbackSymmetry_hom_comp_fst_assoc]
      exact pullbackRightPullbackFstIso_inv_snd_snd f g U.ι
  have heK : e.hom ≫ W.ι ≫ q = qZ := by
    rw [← Category.assoc, heY, pullback.lift_snd]
  let : Y.Over (Spec (.of K)) := ⟨q⟩
  let : W.toScheme.Over (Spec (.of K)) := ⟨W.ι ≫ q⟩
  let : Z.Over (Spec (.of K)) := ⟨qZ⟩
  show IsClosed ({x} : Set U) ∧
    ∃ z : Z, pZ.base z = x ∧ IsOrdinaryDoublePoint K Z z
  obtain ⟨hclosed, y, hy, hnode⟩ := hx
  have hclosedU : IsClosed ({x} : Set U) := isClosed_singleton_of_val hclosed
  have hyW : y ∈ W := by
    show p y ∈ U
    rw [hy]
    exact x.2
  let yw : W := ⟨y, hyW⟩
  have hnodeW : IsOrdinaryDoublePoint K W.toScheme yw :=
    ordinaryNode_of_open K Y W yw hnode
  let z : Z := e.inv yw
  have hez : e.hom z = yw :=
    congrArg (fun (g : W.toScheme ⟶ W.toScheme) => g yw) e.inv_hom_id
  refine ⟨hclosedU, z, ?_, ?_⟩
  · apply U.ι.isEmbedding.injective
    calc
      U.ι (pZ z) = p ((e.hom ≫ W.ι) z) := by
        rw [congrArg (fun (h : Z ⟶ Y) => h z) heY]
        show (pZ ≫ U.ι) z =
          (pullback.lift (pZ ≫ U.ι) qZ (by rw [Category.assoc, pullback.condition]) ≫ p) z
        rw [pullback.lift_fst]
      _ = p y := by rw [Scheme.Hom.comp_apply, hez]; rfl
      _ = U.ι x := hy
  · exact (ordinaryNode_of_iso K e heK z).mpr (by rw [hez]; exact hnodeW)

/-- A ring isomorphism `R ≃+* S` induces an isomorphism of the integral closures of `R` and `S`
in their respective fraction rings. -/
private noncomputable def integralClosureRingEquiv
    (R S : Type*) [CommRing R] [CommRing S] (e : R ≃+* S) :
    integralClosure R (FractionRing R) ≃+*
      integralClosure S (FractionRing S) := by
  let eK : FractionRing R ≃+* FractionRing S :=
    IsFractionRing.ringEquivOfRingEquiv e
  letI : Algebra R (FractionRing S) :=
    ((algebraMap S (FractionRing S)).comp e.toRingHom).toAlgebra
  letI : Algebra S (FractionRing R) :=
    ((algebraMap R (FractionRing R)).comp e.symm.toRingHom).toAlgebra
  let eKR : FractionRing R ≃ₐ[R] FractionRing S :=
    { eK with
      commutes' := IsFractionRing.ringEquivOfRingEquiv_algebraMap e }
  let eKS : FractionRing S ≃ₐ[S] FractionRing R :=
    { eK.symm with
      commutes' := IsFractionRing.ringEquivOfRingEquiv_algebraMap e.symm }
  have hRS : (algebraMap S (FractionRing S)).comp e.toRingHom =
      algebraMap R (FractionRing S) := rfl
  have hSR : (algebraMap R (FractionRing R)).comp e.symm.toRingHom =
      algebraMap S (FractionRing R) := rfl
  let f : integralClosure R (FractionRing R) →+*
      integralClosure S (FractionRing S) :=
    { toFun := fun x => ⟨eK x.1, by
        have hx : IsIntegral R x.1 := x.2
        exact (e.isIntegral_iff hRS (eK x.1)).mp
          ((isIntegral_algEquiv eKR).mpr hx)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact eK.injective (congrArg Subtype.val h)
  · intro y
    let x : integralClosure R (FractionRing R) := ⟨eK.symm y.1, by
      have hy : IsIntegral S y.1 := y.2
      exact (e.symm.isIntegral_iff hSR (eK.symm y.1)).mp
        ((isIntegral_algEquiv eKS).mpr hy)⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact eK.apply_symm_apply y.1

/-- The induced isomorphism of integral closures carries the image of `r : R` to the image
of `e r`. -/
private theorem integralClosureRingEquiv_commutes
    (R S : Type*) [CommRing R] [CommRing S]
    (e : R ≃+* S) (r : R) :
    integralClosureRingEquiv R S e
      (algebraMap R (integralClosure R (FractionRing R)) r) =
    algebraMap S (integralClosure S (FractionRing S)) (e r) := by
  apply Subtype.ext
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap e r

/-- A ring isomorphism of local rings induces an isomorphism of their quadratic algebras, the
closed fibres of the normalizations. -/
private noncomputable def quadraticAlgebraRingEquiv
    (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    quadraticAlgebra R ≃+*
      quadraticAlgebra S := by
  let CR := integralClosure R (FractionRing R)
  let CS := integralClosure S (FractionRing S)
  let eC : CR ≃+* CS := integralClosureRingEquiv R S e
  let IR : Ideal CR := (maximalIdeal R).map (algebraMap R CR)
  let IS : Ideal CS := (maximalIdeal S).map (algebraMap S CS)
  have hI : IS = IR.map eC := by
    calc
      IS = ((maximalIdeal R).map e.toRingHom).map (algebraMap S CS) := by
        change (maximalIdeal S).map (algebraMap S CS) =
          ((maximalIdeal R).map (e : R →+* S)).map (algebraMap S CS)
        rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
        congr 1
      _ = (maximalIdeal R).map ((algebraMap S CS).comp e.toRingHom) :=
        Ideal.map_map e.toRingHom (algebraMap S CS)
      _ = (maximalIdeal R).map (eC.toRingHom.comp (algebraMap R CR)) := by
        congr 1
        exact RingHom.ext fun r => (integralClosureRingEquiv_commutes R S e r).symm
      _ = IR.map eC := by
        change (maximalIdeal R).map (eC.toRingHom.comp (algebraMap R CR)) =
          ((maximalIdeal R).map (algebraMap R CR)).map eC.toRingHom
        rw [Ideal.map_map]
  exact Ideal.quotientEquiv IR IS eC hI

/-- The induced isomorphism of quadratic algebras is compatible with the isomorphism of residue
fields: the class of `c` goes to the class of `ResidueField.mapEquiv e c`. -/
private theorem quadraticAlgebraRingEquiv_residue
    (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
    (c : ResidueField R) :
    quadraticAlgebraRingEquiv R S e
      (algebraMap (ResidueField R)
        (quadraticAlgebra R) c) =
    algebraMap (ResidueField S)
      (quadraticAlgebra S)
      (ResidueField.mapEquiv e c) := by
  obtain ⟨r, rfl⟩ := residue_surjective c
  rw [ResidueField.mapEquiv_apply, ResidueField.map_residue]
  show Ideal.Quotient.mk _
      (integralClosureRingEquiv R S e (algebraMap R _ r)) =
    Ideal.Quotient.mk _ (algebraMap S _ (e r))
  rw [integralClosureRingEquiv_commutes]

/-- If the quadratic algebra of `R` splits as `κ(R) × κ(R)`, then so does the quadratic algebra
of an isomorphic local ring `S`. -/
theorem quadraticAlgebra_split_of_ringEquiv
    (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
    (h : Nonempty
      (quadraticAlgebra R
        ≃ₐ[ResidueField R] (ResidueField R × ResidueField R))) :
    Nonempty
      (quadraticAlgebra S
        ≃ₐ[ResidueField S] (ResidueField S × ResidueField S)) := by
  obtain ⟨a⟩ := h
  let eκ := ResidueField.mapEquiv e
  let eQ := quadraticAlgebraRingEquiv R S e
  let b : quadraticAlgebra S ≃+*
      (ResidueField S × ResidueField S) :=
    eQ.symm.trans a.toRingEquiv |>.trans (RingEquiv.prodCongr eκ eκ)
  refine ⟨AlgEquiv.ofRingEquiv (f := b) ?_⟩
  intro c
  let d := eκ.symm c
  have hQ := quadraticAlgebraRingEquiv_residue R S e d
  have hc : eκ d = c := eκ.apply_symm_apply c
  rw [hc] at hQ
  have he : eQ.symm (algebraMap (ResidueField S)
      (quadraticAlgebra S) c) =
      algebraMap (ResidueField R)
        (quadraticAlgebra R) d := by
    rw [← hQ]
    exact eQ.symm_apply_apply _
  show (eκ (a (eQ.symm (algebraMap (ResidueField S) _ c))).1,
      eκ (a (eQ.symm (algebraMap (ResidueField S) _ c))).2) = (c, c)
  rw [he, a.commutes d]
  exact Prod.ext (by simp [d]) (by simp [d])

/-- A point of an open subscheme `U ⊆ X` that is a split node of `X` is a split node of `U`. -/
private theorem splitNode_of_open
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (U : X.Opens) (x : U) (hx : IsSplitNode k X x.1) :
    letI : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ (X ↘ Spec (.of k))⟩
    IsSplitNode k U.toScheme x := by
  let f := X ↘ Spec (.of k)
  let : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ f⟩
  let kToStalkX : k →+* X.presheaf.stalk x.1 :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x.1 trivial).hom
  let kToStalkU : k →+* U.toScheme.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop ≫
      U.toScheme.presheaf.germ ⊤ x trivial).hom
  let : Algebra k (X.presheaf.stalk x.1) := kToStalkX.toAlgebra
  let : Algebra k (U.toScheme.presheaf.stalk x) := kToStalkU.toAlgebra
  let e := openStalkAlgEquiv k X f U x
  have : IsLocalRing (U.toScheme.presheaf.stalk x) := e.toRingEquiv.isLocalRing
  let eκ := ResidueField.mapEquiv e.toRingEquiv
  have : IsLocalHom e.toRingEquiv.toRingHom :=
    isLocalHom_of_leftInverse e.symm e.left_inv
  have hres (c : k) :
      eκ ((X.residue x.1).hom (kToStalkX c)) =
        (U.toScheme.residue x).hom (kToStalkU c) := by
    show ResidueField.map e.toRingEquiv.toRingHom
      (residue (X.presheaf.stalk x.1) (kToStalkX c)) =
      residue (U.toScheme.presheaf.stalk x) (kToStalkU c)
    rw [ResidueField.map_residue]
    exact congrArg (residue (U.toScheme.presheaf.stalk x)) (e.commutes c)
  have hbij : Function.Bijective
      ((U.toScheme.residue x).hom.comp kToStalkU) := by
    have hcomp : (U.toScheme.residue x).hom.comp kToStalkU =
        eκ.toRingHom.comp ((X.residue x.1).hom.comp kToStalkX) := by
      ext c
      exact (hres c).symm
    rw [hcomp]
    exact eκ.bijective.comp hx.2.1
  exact ⟨node_of_open k X U x hx.1, hbij,
    quadraticAlgebra_split_of_ringEquiv _ _ e.toRingEquiv hx.2.2⟩

/-- The map from the stalk of `T` at `t` to the stalk of the fibre `T_{f t}` at the corresponding
point is surjective. -/
private lemma fiber_stalk_surjective {T S : Scheme.{u}} (f : T ⟶ S) (t : T) :
    let Q := T.presheaf.stalk t
    let j : Q ⟶ (f.fiber (f t)).presheaf.stalk (f.asFiber t) :=
      (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
        (f.fiberι (f t)).stalkMap (f.asFiber t)
    Function.Surjective j.hom := by
  let c := (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom
  have hc : Function.Surjective c.hom :=
    ((ConcreteCategory.isIso_iff_bijective c).mp inferInstance).2
  exact ((f.fiberι (f t)).stalkMap_surjective (f.asFiber t)).comp hc

/-- The map from the stalk of `T` at `t` to the stalk of the fibre is compatible with the canonical
maps from the spectra of the stalks. -/
private lemma spec_map_fiber_stalk_comp {T S : Scheme.{u}} (f : T ⟶ S) (t : T) :
    Spec.map ((T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
        (f.fiberι (f t)).stalkMap (f.asFiber t)) ≫ T.fromSpecStalk t =
      (f.fiber (f t)).fromSpecStalk (f.asFiber t) ≫ f.fiberι (f t) := by
  have hcongr : (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom =
      T.presheaf.stalkSpecializes
        (Inseparable.of_eq (f.fiberι_asFiber t).symm).specializes' := rfl
  rw [hcongr, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk (f.fiberι (f t))

/-- The stalk map of `f` at `t`, followed by the map to the stalk of the fibre, factors through the
residue field of `S` at `f t`. -/
private lemma fiber_stalk_map_comp {T S : Scheme.{u}} (f : T ⟶ S) (t : T) :
    let j : T.presheaf.stalk t ⟶ (f.fiber (f t)).presheaf.stalk (f.asFiber t) :=
      (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
        (f.fiberι (f t)).stalkMap (f.asFiber t)
    f.stalkMap t ≫ j = S.residue (f t) ≫ Spec.preimage
      ((f.fiber (f t)).fromSpecStalk (f.asFiber t) ≫ f.fiberToSpecResidueField (f t)) := by
  intro j
  have hj : Spec.map j ≫ T.fromSpecStalk t =
      (f.fiber (f t)).fromSpecStalk (f.asFiber t) ≫ f.fiberι (f t) :=
    spec_map_fiber_stalk_comp f t
  apply Spec.map_inj.mp
  apply (cancel_mono (S.fromSpecStalk (f t))).mp
  calc
    _ = (Spec.map j ≫ T.fromSpecStalk t) ≫ f := by
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
        Category.assoc]
    _ = (f.fiber (f t)).fromSpecStalk (f.asFiber t) ≫ f.fiberToSpecResidueField (f t) ≫
        S.fromSpecResidueField (f t) := by rw [hj, Category.assoc, f.fiber_fac]
    _ = _ := by
      rw [Spec.map_comp, Spec.map_preimage, Category.assoc]
      rfl

/-- The kernel of the stalk map to the fibre is the ideal of `𝒪_{T, t}` generated by the maximal
ideal of `𝒪_{S, f t}`. -/
private lemma fiber_stalk_quotient {T S : Scheme.{u}} (f : T ⟶ S) (t : T) :
    let R := S.presheaf.stalk (f t)
    let Q := T.presheaf.stalk t
    let j : Q ⟶ (f.fiber (f t)).presheaf.stalk (f.asFiber t) :=
      (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
        (f.fiberι (f t)).stalkMap (f.asFiber t)
    RingHom.ker j.hom = (maximalIdeal R).map (f.stalkMap t).hom := by
  let R := S.presheaf.stalk (f t)
  let Q := T.presheaf.stalk t
  let F := f.fiber (f t)
  let z := f.asFiber t
  let p := f.fiberι (f t)
  let j : Q ⟶ F.presheaf.stalk z :=
    (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫ p.stalkMap z
  let I := (maximalIdeal R).map (f.stalkMap t).hom
  let D := Q ⧸ I
  have : IsLocalRing D := isLocalRing_quotient_of_le_maximalIdeal (map_maximalIdeal_le _)
  let q : Q ⟶ CommRingCat.of D := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have : IsLocalHom q.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let b : S.residueField (f t) ⟶ CommRingCat.of D := CommRingCat.ofHom
    (Ideal.Quotient.lift (maximalIdeal R) (q.hom.comp (f.stalkMap t).hom) fun _ hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr))
  have hb : S.residue (f t) ≫ b = f.stalkMap t ≫ q := by ext; rfl
  let a : AlgebraicGeometry.Spec (.of D) ⟶ T := Spec.map q ≫ T.fromSpecStalk t
  have hab : a ≫ f = Spec.map b ≫ S.fromSpecResidueField (f t) := by
    dsimp [a, Scheme.fromSpecResidueField]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hb]
  let l : AlgebraicGeometry.Spec (.of D) ⟶ F := pullback.lift a (Spec.map b) hab
  have hl : l ≫ p = a := pullback.lift_fst _ _ _
  have hlz : l (closedPoint D) = z := by
    have h1 : p (l (closedPoint D)) =
        (Spec.map q ≫ T.fromSpecStalk t) (closedPoint D) :=
      congrArg (fun (g : AlgebraicGeometry.Spec (.of D) ⟶ T) => g (closedPoint D)) hl
    have h2 : (Spec.map q ≫ T.fromSpecStalk t) (closedPoint D) = t :=
      (Scheme.Hom.comp_apply (Spec.map q) (T.fromSpecStalk t) (closedPoint D)).trans
        ((congrArg (fun y => (T.fromSpecStalk t) y) (Spec_closedPoint (f := q))).trans
          Scheme.fromSpecStalk_closedPoint)
    exact p.isEmbedding.injective (h1.trans (h2.trans (f.fiberι_asFiber t).symm))
  let k : F.presheaf.stalk z ⟶ CommRingCat.of D :=
    (F.presheaf.stalkCongr (Inseparable.of_eq hlz.symm)).hom ≫ Scheme.stalkClosedPointTo l
  have hcongrF : (F.presheaf.stalkCongr (Inseparable.of_eq hlz.symm)).hom =
      F.presheaf.stalkSpecializes (Inseparable.of_eq hlz.symm).specializes' := rfl
  have hj : Spec.map j ≫ T.fromSpecStalk t = F.fromSpecStalk z ≫ p :=
    spec_map_fiber_stalk_comp f t
  have hk : Spec.map k ≫ F.fromSpecStalk z = l := by
    dsimp [k]
    rw [hcongrF, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  have hjk : j ≫ k = q := by
    apply Spec.map_inj.mp
    apply (cancel_mono (T.fromSpecStalk t)).mp
    rw [Spec.map_comp, Category.assoc, hj, ← Category.assoc, hk, hl]
  apply le_antisymm
  · intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    show q.hom r = 0
    rw [← hjk]
    show k.hom (j.hom r) = 0
    rw [show j.hom r = 0 from hr, map_zero]
  · let β := Spec.preimage (F.fromSpecStalk z ≫ f.fiberToSpecResidueField (f t))
    have hβ : f.stalkMap t ≫ j = S.residue (f t) ≫ β := fiber_stalk_map_comp f t
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    show (f.stalkMap t ≫ j).hom r = 0
    rw [hβ]
    show β.hom ((residue R) r) = 0
    rw [(residue_eq_zero_iff r).mpr hr]
    exact map_zero β.hom

/-- The local ring of the fibre at `t` is isomorphic to `𝒪_{T, t} ⧸ 𝔪_{S, f t} 𝒪_{T, t}`. -/
private lemma fiber_stalk_quotient_ringEquiv {T S : Scheme.{u}}
    (f : T ⟶ S) (t : T) :
    let R := S.presheaf.stalk (f t)
    let Q := T.presheaf.stalk t
    let F := (f.fiber (f t)).presheaf.stalk (f.asFiber t)
    Nonempty ((Q ⧸ (maximalIdeal R).map (f.stalkMap t).hom) ≃+* F) := by
  let j : T.presheaf.stalk t ⟶
      (f.fiber (f t)).presheaf.stalk (f.asFiber t) :=
    (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
      (f.fiberι (f t)).stalkMap (f.asFiber t)
  have hker := fiber_stalk_quotient f t
  have hsurj := fiber_stalk_surjective f t
  show Nonempty ((T.presheaf.stalk t ⧸
    (maximalIdeal (S.presheaf.stalk (f t))).map (f.stalkMap t).hom) ≃+*
      (f.fiber (f t)).presheaf.stalk (f.asFiber t))
  rw [← hker]
  exact ⟨RingHom.quotientKerEquivOfSurjective (f := j.hom) hsurj⟩

/-- As an `𝒪_{S, f t}`-algebra, the local ring of the fibre at `t` is isomorphic to
`𝒪_{T, t} ⧸ 𝔪_{S, f t} 𝒪_{T, t}`. -/
private lemma fiber_stalk_quotient_algEquiv {T S : Scheme.{u}}
    (f : T ⟶ S) (t : T) :
    let R := S.presheaf.stalk (f t)
    let Q := T.presheaf.stalk t
    let F := (f.fiber (f t)).presheaf.stalk (f.asFiber t)
    let j : Q ⟶ F :=
      (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
        (f.fiberι (f t)).stalkMap (f.asFiber t)
    letI : Algebra R Q := (f.stalkMap t).hom.toAlgebra
    letI : Algebra R F := (j.hom.comp (f.stalkMap t).hom).toAlgebra
    Nonempty ((Q ⧸ (maximalIdeal R).map (f.stalkMap t).hom) ≃ₐ[R] F) := by
  let R := S.presheaf.stalk (f t)
  let Q := T.presheaf.stalk t
  let F := (f.fiber (f t)).presheaf.stalk (f.asFiber t)
  let j : Q ⟶ F :=
    (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
      (f.fiberι (f t)).stalkMap (f.asFiber t)
  let : Algebra R Q := (f.stalkMap t).hom.toAlgebra
  let : Algebra R F := (j.hom.comp (f.stalkMap t).hom).toAlgebra
  let g : Q →ₐ[R] F := ⟨j.hom, fun _ => rfl⟩
  have hker := fiber_stalk_quotient f t
  have hsurj := fiber_stalk_surjective f t
  show Nonempty ((Q ⧸ (maximalIdeal R).map (f.stalkMap t).hom) ≃ₐ[R] F)
  rw [← hker]
  exact ⟨Ideal.quotientKerAlgEquivOfSurjective (f := g) hsurj⟩

/-- The closed fibre `B ⧸ 𝔪_A B` of the completed stalk map is isomorphic to the completion of
the local ring of the fibre at `t`. -/
private lemma completed_fiber_stalk_ringEquiv {T S : Scheme.{u}}
    (f : T ⟶ S) (t : T)
    [IsNoetherianRing (S.presheaf.stalk (f t))] [LocallyOfFiniteType f] :
    let R := S.presheaf.stalk (f t)
    let Q := T.presheaf.stalk t
    let A := AdicCompletion (maximalIdeal R) R
    let B := AdicCompletion (maximalIdeal Q) Q
    let F := (f.fiber (f t)).presheaf.stalk (f.asFiber t)
    let φ := adicCompletionMap (f.stalkMap t).hom
      (maximalIdeal R) (maximalIdeal Q)
      (map_maximalIdeal_le (f.stalkMap t).hom)
    Nonempty ((B ⧸ (maximalIdeal A).map φ) ≃+*
      AdicCompletion (maximalIdeal F) F) := by
  let R := S.presheaf.stalk (f t)
  let Q := T.presheaf.stalk t
  let : Algebra R Q := (f.stalkMap t).hom.toAlgebra
  have : Algebra.EssFiniteType R Q := LocallyOfFiniteType.stalkMap f t
  have : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing R Q
  let A := AdicCompletion (maximalIdeal R) R
  let B := AdicCompletion (maximalIdeal Q) Q
  let F := (f.fiber (f t)).presheaf.stalk (f.asFiber t)
  let φ := adicCompletionMap (f.stalkMap t).hom
    (maximalIdeal R) (maximalIdeal Q)
    (map_maximalIdeal_le (f.stalkMap t).hom)
  let I : Ideal Q := (maximalIdeal R).map (f.stalkMap t).hom
  have hI : (maximalIdeal A).map φ = I.map (algebraMap Q B) :=
    map_maximalIdeal_adicCompletionMap _ _
  have : IsLocalRing (Q ⧸ I) := isLocalRing_quotient_of_le_maximalIdeal (map_maximalIdeal_le _)
  obtain ⟨e₁⟩ := completion_quotient_equiv Q I
  obtain ⟨e₂⟩ := fiber_stalk_quotient_ringEquiv f t
  show Nonempty ((B ⧸ (maximalIdeal A).map φ) ≃+*
    AdicCompletion (maximalIdeal F) F)
  rw [hI]
  exact ⟨e₁.symm.toRingEquiv.trans (completionRingEquiv e₂)⟩

/-- As an `𝒪_{S, f t}`-algebra, the closed fibre `B ⧸ 𝔪_A B` of the completed stalk map is
isomorphic to the completion of the local ring of the fibre at `t`. -/
private lemma completed_fiber_stalk_algEquiv {T S : Scheme.{u}}
    (f : T ⟶ S) (t : T)
    [IsNoetherianRing (S.presheaf.stalk (f t))] [LocallyOfFiniteType f] :
    let R := S.presheaf.stalk (f t)
    let Q := T.presheaf.stalk t
    let A := AdicCompletion (maximalIdeal R) R
    let B := AdicCompletion (maximalIdeal Q) Q
    let F := (f.fiber (f t)).presheaf.stalk (f.asFiber t)
    let φ := adicCompletionMap (f.stalkMap t).hom
      (maximalIdeal R) (maximalIdeal Q)
      (map_maximalIdeal_le (f.stalkMap t).hom)
    let j : Q ⟶ F :=
      (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
        (f.fiberι (f t)).stalkMap (f.asFiber t)
    letI : Algebra R B := ((algebraMap Q B).comp (f.stalkMap t).hom).toAlgebra
    letI : Algebra R F := (j.hom.comp (f.stalkMap t).hom).toAlgebra
    Nonempty ((B ⧸ (maximalIdeal A).map φ) ≃ₐ[R]
      AdicCompletion (maximalIdeal F) F) := by
  let R := S.presheaf.stalk (f t)
  let Q := T.presheaf.stalk t
  let : Algebra R Q := (f.stalkMap t).hom.toAlgebra
  have : Algebra.EssFiniteType R Q := LocallyOfFiniteType.stalkMap f t
  have : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing R Q
  let A := AdicCompletion (maximalIdeal R) R
  let B := AdicCompletion (maximalIdeal Q) Q
  let F := (f.fiber (f t)).presheaf.stalk (f.asFiber t)
  let φ := adicCompletionMap (f.stalkMap t).hom
    (maximalIdeal R) (maximalIdeal Q)
    (map_maximalIdeal_le (f.stalkMap t).hom)
  let j : Q ⟶ F :=
    (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
      (f.fiberι (f t)).stalkMap (f.asFiber t)
  let : Algebra R B := ((algebraMap Q B).comp (f.stalkMap t).hom).toAlgebra
  let : Algebra R F := (j.hom.comp (f.stalkMap t).hom).toAlgebra
  let I : Ideal Q := (maximalIdeal R).map (f.stalkMap t).hom
  have hI : (maximalIdeal A).map φ = I.map (algebraMap Q B) :=
    map_maximalIdeal_adicCompletionMap _ _
  have : IsLocalRing (Q ⧸ I) := isLocalRing_quotient_of_le_maximalIdeal (map_maximalIdeal_le _)
  let : Algebra R (Q ⧸ I) :=
    ((Ideal.Quotient.mk I).comp (f.stalkMap t).hom).toAlgebra
  obtain ⟨e₁⟩ := completion_quotient_equiv Q I
  obtain ⟨e₂⟩ := fiber_stalk_quotient_algEquiv f t
  let e₁R : AdicCompletion (maximalIdeal (Q ⧸ I)) (Q ⧸ I) ≃ₐ[R]
      (B ⧸ I.map (algebraMap Q B)) :=
    { __ := e₁.toRingEquiv, commutes' := by
        intro r
        exact e₁.commutes ((f.stalkMap t).hom r) }
  show Nonempty ((B ⧸ (maximalIdeal A).map φ) ≃ₐ[R]
    AdicCompletion (maximalIdeal F) F)
  rw [hI]
  exact ⟨e₁R.symm.trans (completionAlgEquiv e₂)⟩


/-- The completion at a split node of a flat, locally finite-type family over a Noetherian
local base is a nodal smoothing `A⟦x,y⟧/(xy-h)` over the completed base ring `A`. -/
@[stacks 0CBX]
theorem exists_algEquiv_adicCompletion_quotient_mvPowerSeries_of_isSplitNode
    {T S : Scheme.{u}} (f : T ⟶ S) (t : T)
    (hflat : AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom t)
    [IsNoetherianRing (S.presheaf.stalk (f t))]
    [LocallyOfFiniteType f]
    (hnode : letI := f.fiberOverSpecResidueField (f t)
      IsSplitNode (S.residueField (f t)) (f.fiber (f t)) (f.asFiber t)) :
    let R := S.presheaf.stalk (f t)
    let Q := T.presheaf.stalk t
    let A := AdicCompletion (maximalIdeal R) R
    let B := AdicCompletion (maximalIdeal Q) Q
    let φ : A →+* B := adicCompletionMap (f.stalkMap t).hom
      (maximalIdeal R) (maximalIdeal Q)
      (map_maximalIdeal_le (f.stalkMap t).hom)
    letI : Algebra A B := φ.toAlgebra
    ∃ h : A, h ∈ maximalIdeal A ∧
      Nonempty ((MvPowerSeries (Fin 2) A ⧸
        Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) ≃ₐ[A] B) := by
  let R := S.presheaf.stalk (f t)
  let Q := T.presheaf.stalk t
  let : Algebra R Q := (f.stalkMap t).hom.toAlgebra
  have : Algebra.EssFiniteType R Q := LocallyOfFiniteType.stalkMap f t
  have : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing R Q
  let A := AdicCompletion (maximalIdeal R) R
  let B := AdicCompletion (maximalIdeal Q) Q
  let φ : A →+* B := adicCompletionMap (f.stalkMap t).hom
    (maximalIdeal R) (maximalIdeal Q) (map_maximalIdeal_le (f.stalkMap t).hom)
  let : Algebra A B := φ.toAlgebra
  have : IsLocalHom (algebraMap A B) :=
    adicCompletionMap_isLocalHom_of_isLocalHom (f.stalkMap t).hom
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mpr
    (adicCompletionMap_flat_of_isFlatAt f t hflat)
  show ∃ h : A, h ∈ maximalIdeal A ∧
    Nonempty ((MvPowerSeries (Fin 2) A ⧸
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) ≃ₐ[A] B)
  suffices hclosed : Nonempty ((MvPowerSeries (Fin 2) A ⧸
      (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} ⊔
        (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A)))) ≃ₐ[A]
          B ⧸ (maximalIdeal A).map (algebraMap A B)) by
    obtain ⟨e⟩ := hclosed
    exact exists_nodal_presentation_of_closed_fiber_algEquiv e
  obtain ⟨e⟩ := quotient_powerSeries_algEquiv_residueField A
  suffices hfiber : Nonempty ((MvPowerSeries (Fin 2) (ResidueField A) ⧸
      Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} :
        Set (MvPowerSeries (Fin 2) (ResidueField A)))) ≃ₐ[A]
        B ⧸ (maximalIdeal A).map (algebraMap A B)) by
    obtain ⟨e'⟩ := hfiber
    exact ⟨e.trans e'⟩
  let F := f.fiber (f t)
  let z := f.asFiber t
  let : F.Over (Spec (.of (S.residueField (f t)))) :=
    f.fiberOverSpecResidueField (f t)
  let : LocallyOfFiniteType (F ↘ Spec (.of (S.residueField (f t)))) := by
    show LocallyOfFiniteType (f.fiberToSpecResidueField (f t))
    let : MorphismProperty.IsStableUnderBaseChangeAlong
        (@LocallyOfFiniteType) (S.fromSpecResidueField (f t)) :=
      ⟨fun pb hg => locallyOfFiniteType_isStableUnderBaseChange.of_isPullback pb hg⟩
    exact MorphismProperty.pullback_snd _ _ (show LocallyOfFiniteType f from inferInstance)
  have hdimAt : topologicalKrullDimAt F z = 1 :=
    topologicalKrullDimAt_eq_one_of_isNode _ F z hnode.1
  obtain ⟨U, hUopen, hzU, hdimU⟩ :=
    exists_open_with_dimension_eq_one z hdimAt
  let V : F.Opens := ⟨U, hUopen⟩
  let : V.toScheme.Over (Spec (.of (S.residueField (f t)))) :=
    ⟨V.ι ≫ (F ↘ Spec (.of (S.residueField (f t))))⟩
  let w : V := ⟨z, hzU⟩
  have hclosedV : IsClosed ({w} : Set V) := isClosed_singleton_of_val hnode.1.1
  have hdimV : topologicalKrullDim V.toScheme = 1 := hdimU
  let : LocallyOfFiniteType (V.toScheme ↘ Spec (.of (S.residueField (f t)))) := by
    show LocallyOfFiniteType (V.ι ≫ (F ↘ Spec (.of (S.residueField (f t)))))
    infer_instance
  have hnodeV : IsSplitNode (S.residueField (f t)) V.toScheme w := by
    exact splitNode_of_open (S.residueField (f t)) F V w hnode
  obtain ⟨eV⟩ := nonempty_algEquiv_adicCompletion_quotient_X_mul_X_of_isSplitNode
    (S.residueField (f t)) V.toScheme hdimV w hnodeV
  let kToStalkF : S.residueField (f t) →+* F.presheaf.stalk z :=
    ((Scheme.ΓSpecIso (.of (S.residueField (f t)))).inv ≫
      (F ↘ Spec (.of (S.residueField (f t)))).appTop ≫
      F.presheaf.germ ⊤ z (by simp)).hom
  let : Algebra (S.residueField (f t)) (F.presheaf.stalk z) := kToStalkF.toAlgebra
  let kToStalkV : S.residueField (f t) →+* V.toScheme.presheaf.stalk w :=
    ((Scheme.ΓSpecIso (.of (S.residueField (f t)))).inv ≫
      (V.ι ≫ (F ↘ Spec (.of (S.residueField (f t))))).appTop ≫
      V.toScheme.presheaf.germ ⊤ w trivial).hom
  let : Algebra (S.residueField (f t)) (V.toScheme.presheaf.stalk w) :=
    kToStalkV.toAlgebra
  let eOpen : F.presheaf.stalk z ≃ₐ[S.residueField (f t)]
      V.toScheme.presheaf.stalk w :=
    openStalkAlgEquiv (S.residueField (f t)) F
      (F ↘ Spec (.of (S.residueField (f t)))) V w
  let : IsLocalRing (V.toScheme.presheaf.stalk w) :=
    eOpen.toRingEquiv.isLocalRing
  let eF : AdicCompletion (maximalIdeal (F.presheaf.stalk z)) (F.presheaf.stalk z)
      ≃ₐ[S.residueField (f t)] (MvPowerSeries (Fin 2) (S.residueField (f t)) ⧸
        Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} :
          Set (MvPowerSeries (Fin 2) (S.residueField (f t))))) :=
    (completionAlgEquiv eOpen).trans eV
  let βcat : S.residueField (f t) ⟶ F.presheaf.stalk z :=
    Spec.preimage (F.fromSpecStalk z ≫ (F ↘ Spec (.of (S.residueField (f t)))))
  let beta : S.residueField (f t) →+* F.presheaf.stalk z := βcat.hom
  have hmap : Spec.map (CommRingCat.ofHom kToStalkF) =
      F.fromSpecStalk z ≫ (F ↘ Spec (.of (S.residueField (f t)))) := by
    calc
      Spec.map (CommRingCat.ofHom kToStalkF) =
          Spec.map (F.presheaf.germ ⊤ z trivial) ≫
            Spec.map (F ↘ Spec (.of (S.residueField (f t)))).appTop ≫
            Spec.map (Scheme.ΓSpecIso (.of (S.residueField (f t)))).inv := by
              simp [kToStalkF, Spec.map_comp]
      _ = F.fromSpecStalk z ≫ F.toSpecΓ ≫
            Spec.map (F ↘ Spec (.of (S.residueField (f t)))).appTop ≫
            Spec.map (Scheme.ΓSpecIso (.of (S.residueField (f t)))).inv := by
              simp only [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ]
      _ = F.fromSpecStalk z ≫ (F ↘ Spec (.of (S.residueField (f t)))) := by
        calc
          _ = F.fromSpecStalk z ≫
              (F.toSpecΓ ≫ Spec.map (F ↘ Spec (.of (S.residueField (f t)))).appTop) ≫
              Spec.map (Scheme.ΓSpecIso (.of (S.residueField (f t)))).inv := by
                simp only [Category.assoc]
          _ = F.fromSpecStalk z ≫
              ((F ↘ Spec (.of (S.residueField (f t)))) ≫
                (Spec (.of (S.residueField (f t)))).toSpecΓ) ≫
              Spec.map (Scheme.ΓSpecIso (.of (S.residueField (f t)))).inv := by
                rw [← Scheme.toSpecΓ_naturality]
          _ = F.fromSpecStalk z ≫ (F ↘ Spec (.of (S.residueField (f t)))) := by
            simp only [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hbeta : beta = kToStalkF := by
    have hcat : Spec.preimage (F.fromSpecStalk z ≫
        (F ↘ Spec (.of (S.residueField (f t))))) =
        CommRingCat.ofHom kToStalkF := by
      apply Spec.map_inj.mp
      simpa only [Spec.map_preimage] using hmap.symm
    exact congrArg CommRingCat.Hom.hom hcat
  let j : Q ⟶ F.presheaf.stalk z :=
    (T.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber t).symm)).hom ≫
      (f.fiberι (f t)).stalkMap z
  have hβ : f.stalkMap t ≫ j = S.residue (f t) ≫ βcat := fiber_stalk_map_comp f t
  have hjR (r : R) : j.hom ((f.stalkMap t).hom r) =
      kToStalkF (residue R r) := by
    have hh := congrArg (fun g => (CommRingCat.Hom.hom g) r) hβ
    change j.hom ((f.stalkMap t).hom r) = beta (residue R r) at hh
    simpa only [hbeta] using hh
  let : Algebra R B := ((algebraMap Q B).comp (f.stalkMap t).hom).toAlgebra
  let : Algebra R (F.presheaf.stalk z) :=
    (j.hom.comp (f.stalkMap t).hom).toAlgebra
  obtain ⟨eC⟩ : Nonempty ((B ⧸ (maximalIdeal A).map (algebraMap A B)) ≃ₐ[R]
      AdicCompletion (maximalIdeal (F.presheaf.stalk z)) (F.presheaf.stalk z)) :=
    completed_fiber_stalk_algEquiv f t
  let E := eF.symm.toRingEquiv.trans eC.symm.toRingEquiv
  apply nodalPowerSeriesQuotientAlgEquiv_of_completion R _ E
  · intro a ha
    show Ideal.Quotient.mk _ (φ a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ ha)
  · intro r
    have hφ : φ (algebraMap R A r) =
        algebraMap Q B ((f.stalkMap t).hom r) :=
      RingHom.congr_fun (adicCompletionMap_comp_algebraMap (f.stalkMap t).hom _ _
        (map_maximalIdeal_le _)) r
    have hn : eF.symm (algebraMap (S.residueField (f t)) _ (residue R r)) =
        algebraMap R (AdicCompletion (maximalIdeal (F.presheaf.stalk z))
          (F.presheaf.stalk z)) r := by
      apply (eF.symm.commutes (residue R r)).trans
      show algebraMap (F.presheaf.stalk z) _ (kToStalkF (residue R r)) =
        algebraMap (F.presheaf.stalk z) _ (j.hom ((f.stalkMap t).hom r))
      exact congrArg (algebraMap (F.presheaf.stalk z) _) (hjR r).symm
    calc
      E (algebraMap (S.residueField (f t)) _ (residue R r)) =
          eC.symm (algebraMap R _ r) := congrArg eC.symm hn
      _ = algebraMap R _ r := eC.symm.commutes r
      _ = algebraMap A _ (algebraMap R A r) := by
        show Ideal.Quotient.mk _ (algebraMap Q B ((f.stalkMap t).hom r)) =
          Ideal.Quotient.mk _ (φ (algebraMap R A r))
        exact congrArg (Ideal.Quotient.mk _) hφ.symm

end Stacks.Curves

end
