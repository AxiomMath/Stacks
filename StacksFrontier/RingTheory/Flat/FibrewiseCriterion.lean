module

public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.LocalCriterionVariant
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Flat.TowerLTensor

/-!
# Critère de platitude par fibres

Two cases of the fibrewise criterion for flatness.

*The nilpotent case.* Let `R → S` be a map of commutative rings, let `I ⊆ R` be a nilpotent ideal
and let `M` be an `S`-module, regarded as an `R`-module through `R → S`. If `M/IM` is flat over
`S/IS` and `M` is flat over `R`, then `M` is flat over `S`, and the localization `S_𝔮` is flat
over `R` at every prime `𝔮 ⊆ S` whose fibre `M ⊗_S κ(𝔮)` is nonzero.

Tensoring `0 → K → R → R/K → 0` with the `R`-flat module `M` shows that `K ⊗_R M → M` is
injective for every ideal `K ⊆ R`, and the comparison `K ⊗_R M → KS ⊗_S M` is surjective, so
`KS ⊗_S M → M` is injective as well, that is `Tor_1^S(S/KS, M) = 0`. Feeding this into the
square-zero local criterion along the filtration by the powers of `IS` gives, by induction on
`k`, flatness of `M/(IS)^k M` over `S/(IS)^k`, and at `k` one less than the nilpotency degree of
`I` the criterion applies to `(IS)^k` itself. At a prime `𝔮` with `M ⊗_S κ(𝔮) ≠ 0` the module
`S_𝔮 ⊗_S M` is faithfully flat over `S_𝔮` and flat over `R`, whence `S_𝔮` is flat over `R`.

*The Noetherian local case.* Let `R → S → S'` be local homomorphisms of Noetherian local rings,
let `𝔪 ⊆ R` be the maximal ideal of `R` and let `M` be a finite nonzero `S'`-module, regarded as
an `S`-module and an `R`-module through the two ring maps. If `M` is flat over `R` and `M/𝔪M` is
flat over `S/𝔪S`, then `S` is flat over `R` and `M` is flat over `S`.

Put `I = 𝔪S`. Both conclusions come from the variant local criterion, whose `Tor` hypothesis is
the injectivity of `J ⊗ N → N`. Contracting `M ⊗_S (S ⊗_R 𝔪)` along the multiplication
`S ⊗_R 𝔪 → S` is, across `TensorProduct.AlgebraTensorModule.cancelBaseChange`, the map
`M ⊗_R 𝔪 → M`, which is injective because `M` is flat over `R`. As `S ⊗_R 𝔪 → S` factors as
`S ⊗_R 𝔪 ↠ I ↪ S`, this is the `Tor` hypothesis for `I ⊆ S`, and `M` is flat over `S`.
Nakayama's lemma for the finite nonzero `S'`-module `M` then makes `M` faithfully flat over `S`,
so the kernel `K` of `S ⊗_R 𝔪 → S`, which satisfies `M ⊗_S K = 0`, vanishes; this is the `Tor`
hypothesis for `𝔪 ⊆ R` and the module `S`, and `S` is flat over `R`.

## Main results

* `Module.flat_and_flat_localization_of_flat_quotient_of_isNilpotent`: the nilpotent case.
* `Module.flat_and_flat_of_flat_quotient_maximalIdeal_of_flat`: the Noetherian local case.
* `Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat`: if an `S`-module is
  flat over `R` and faithfully flat over `S`, then `S` is flat over `R`.

## Implementation notes

In both cases `IM` is written as `IS • ⊤` inside `M` viewed as an `S`-module, so that the
quotient carries the `S/IS`-module structure the hypothesis is about; this is the same submodule
as `I • ⊤` computed over `R` (`restrictScalars_smul_top_map`), since `(IS) · M = I · M`.

In the nilpotent case `M` is an `S`-module with `IsScalarTower R S M`, rather than a module over
a third ring `S'` under `S`, which plays no part in the statement. The localization is left
abstract: `S_𝔮` is any `S`-algebra `Sq` with `IsLocalization.AtPrime Sq 𝔮` and
`IsScalarTower R S Sq`, the fibre is `Ideal.ResidueField 𝔮` and "nonzero" is `Nontrivial`. The
filtration is indexed by `Ideal.map (algebraMap R S) (I ^ n)` rather than by the powers of
`Ideal.map (algebraMap R S) I`, so that the ideals appearing in the types of the relative
injectivity statements are literally extensions of ideals of `R`.

In the Noetherian local case `S'` carries the finiteness hypothesis on `M`; no `Algebra R S'` is
assumed, the two scalar towers on `M` already pinning its `R`-action. The auxiliary module
`S ⊗_R 𝔪` is written with `S` on the left, as `TensorProduct R S 𝔪`, because that is the side
carrying the `S`-module structure (`TensorProduct.leftModule`), which the kernel of the
multiplication map needs for faithful flatness of `M` over `S` to apply to it.

## References

* [Stacks, Tag 06A5](https://stacks.math.columbia.edu/tag/06A5)
* [Stacks, Tag 00MP](https://stacks.math.columbia.edu/tag/00MP)
* [Stacks, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
* [Stacks, Tag 00ML](https://stacks.math.columbia.edu/tag/00ML)
* [Stacks, Tag 00HP](https://stacks.math.columbia.edu/tag/00HP)
* [Stacks, Tag 039V](https://stacks.math.columbia.edu/tag/039V)
* [Stacks, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public section

@[expose] public section

open TensorProduct

namespace Stacks.Flatness.NilpotentFibreCriterion

/-- Injectivity of the right-hand vertical of a commuting square of additive maps out of a tensor
product, whose top is surjective and whose left-hand vertical and bottom are injective; the
commutativity is only checked on pure tensors. -/
private theorem injective_of_comm_square {R X M β γ δ Fr Ft Fl Fb : Type*} [CommSemiring R]
    [AddCommMonoid X] [Module R X] [AddCommMonoid M] [Module R M]
    [AddZeroClass β] [AddZeroClass γ] [AddZeroClass δ]
    [FunLike Fr β δ] [AddMonoidHomClass Fr β δ] [FunLike Ft (X ⊗[R] M) β]
    [AddMonoidHomClass Ft (X ⊗[R] M) β] [FunLike Fl (X ⊗[R] M) γ]
    [AddMonoidHomClass Fl (X ⊗[R] M) γ] [FunLike Fb γ δ] [AddMonoidHomClass Fb γ δ]
    (r : Fr) (t : Ft) (l : Fl) (b : Fb)
    (hcomm : ∀ (x : X) (m : M), r (t (x ⊗ₜ m)) = b (l (x ⊗ₜ m)))
    (ht : Function.Surjective t) (hl : Function.Injective l) (hb : Function.Injective b) :
    Function.Injective r := by
  have h : ∀ z, r (t z) = b (l z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => exact hcomm x m
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  intro u v huv
  obtain ⟨u', rfl⟩ := ht u
  obtain ⟨v', rfl⟩ := ht v
  rw [h, h] at huv
  rw [hl (hb huv)]

section Comparison

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- `IM`, computed over `R`, is `(IS)M`, computed over `S`. -/
private theorem restrictScalars_smul_top_map (I : Ideal R) :
    ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M)).restrictScalars R
      = I • (⊤ : Submodule R M) := by
  have hstab : ∀ (a : S) {z : M}, z ∈ I • (⊤ : Submodule R M) →
      a • z ∈ I • (⊤ : Submodule R M) := by
    intro a z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro r hr n _
      rw [smul_comm]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x y hx hy
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
  have hgen : ∀ s : S, s ∈ Ideal.map (algebraMap R S) I → ∀ m : M,
      s • m ∈ I • (⊤ : Submodule R M) := by
    intro s hs m
    refine Submodule.span_induction (p := fun s _ => s • m ∈ I • (⊤ : Submodule R M))
      ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨r, hr, rfl⟩
      rw [algebraMap_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · simp
    · intro a b _ _ ha hb
      rw [add_smul]
      exact Submodule.add_mem _ ha hb
    · intro a b _ hb
      rw [smul_assoc]
      exact hstab a hb
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    exact Submodule.smul_induction_on hx (fun s hs m _ => hgen s hs m)
      (fun a b ha hb => Submodule.add_mem _ ha hb)
  · rw [Submodule.smul_le]
    intro r hr m _
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul S r m]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top

/-- The additive comparison map `X ⊗[R] M → Y ⊗[S] M` induced by an `algebraMap`-semilinear
additive map `ψ : X →+ Y` of the left factors. -/
private def tmulComp {X : Type*} [AddCommGroup X] [Module R X]
    {Y : Type*} [AddCommGroup Y] [Module S Y] (ψ : X →+ Y)
    (hψ : ∀ (r : R) (x : X), ψ (r • x) = (algebraMap R S r) • ψ x) :
    (X ⊗[R] M) →+ (Y ⊗[S] M) :=
  TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun m => (ψ x) ⊗ₜ[S] m
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun m m' => TensorProduct.tmul_add _ _ _ }
      map_zero' := by ext m; simp
      map_add' := fun x x' => by ext m; simp [TensorProduct.add_tmul] }
    (fun r x m => by
      change ψ (r • x) ⊗ₜ[S] m = ψ x ⊗ₜ[S] (r • m)
      rw [hψ, TensorProduct.smul_tmul, algebraMap_smul])

private theorem tmulComp_tmul {X : Type*} [AddCommGroup X] [Module R X]
    {Y : Type*} [AddCommGroup Y] [Module S Y] (ψ : X →+ Y)
    (hψ : ∀ (r : R) (x : X), ψ (r • x) = (algebraMap R S r) • ψ x) (x : X) (m : M) :
    tmulComp (M := M) ψ hψ (x ⊗ₜ[R] m) = (ψ x) ⊗ₜ[S] m := rfl

attribute [local simp] tmulComp_tmul

/-- The range of `tmulComp`, as an `S`-submodule: `S` acts through the right factor. -/
private def tmulCompRange {X : Type*} [AddCommGroup X] [Module R X]
    {Y : Type*} [AddCommGroup Y] [Module S Y] (ψ : X →+ Y)
    (hψ : ∀ (r : R) (x : X), ψ (r • x) = (algebraMap R S r) • ψ x) :
    Submodule S (Y ⊗[S] M) where
  carrier := Set.range (tmulComp (M := M) ψ hψ)
  add_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u + v, by rw [map_add]⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro a _ ⟨u, rfl⟩
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x m => exact ⟨x ⊗ₜ[R] (a • m), by rw [tmulComp_tmul, tmulComp_tmul, tmul_smul]⟩
    | add p q hp hq =>
        obtain ⟨u, hu⟩ := hp
        obtain ⟨v, hv⟩ := hq
        exact ⟨u + v, by rw [map_add, hu, hv, map_add, smul_add]⟩

/-- `tmulComp ψ` is surjective as soon as the image of `ψ` spans the target of `ψ` over `S`. -/
private theorem tmulComp_surjective {X : Type*} [AddCommGroup X] [Module R X]
    {Y : Type*} [AddCommGroup Y] [Module S Y] (ψ : X →+ Y)
    (hψ : ∀ (r : R) (x : X), ψ (r • x) = (algebraMap R S r) • ψ x)
    (hspan : Submodule.span S (Set.range ψ) = ⊤) :
    Function.Surjective (tmulComp (M := M) ψ hψ) := by
  set T : Submodule S Y :=
    { carrier := {y | ∀ m : M, y ⊗ₜ[S] m ∈ tmulCompRange (M := M) ψ hψ}
      add_mem' := fun hx hy m => by
        rw [TensorProduct.add_tmul]
        exact Submodule.add_mem _ (hx m) (hy m)
      zero_mem' := fun m => by
        rw [TensorProduct.zero_tmul]
        exact Submodule.zero_mem _
      smul_mem' := fun a x hx m => by
        rw [TensorProduct.smul_tmul]
        exact hx (a • m) } with hT
  have h : T = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩ m
    exact ⟨x ⊗ₜ[R] m, rfl⟩
  have hTtop : ∀ y : Y, ∀ m : M, y ⊗ₜ[S] m ∈ tmulCompRange (M := M) ψ hψ :=
    fun y => (h ▸ Submodule.mem_top : y ∈ T)
  intro z
  have hz : z ∈ tmulCompRange (M := M) ψ hψ := by
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul y m => exact hTtop y m
    | add p q hp hq => exact Submodule.add_mem _ hp hq
  exact hz

/-- The restriction of a ring map `f : A →+* T` to an ideal `B ⊆ A`, as an additive map into
`B.map f`. -/
private def idealMapHom {A T : Type*} [CommRing A] [CommRing T] (f : A →+* T) (B : Ideal A) :
    ↥B →+ ↥(Ideal.map f B) where
  toFun b := ⟨f (b : A), Ideal.mem_map_of_mem f b.2⟩
  map_zero' := by ext; simp
  map_add' b b' := by ext; simp

private theorem idealMapHom_val {A T : Type*} [CommRing A] [CommRing T] (f : A →+* T)
    (B : Ideal A) (b : ↥B) : ((idealMapHom f B b : ↥(Ideal.map f B)) : T) = f (b : A) := rfl

attribute [local simp] idealMapHom_val

/-- The image of an ideal `B ⊆ A` under `f : A →+* T` spans `B.map f` already over a ring `S`
mapping onto `T`. -/
private theorem span_range_eq_top_of_val_eq {T A : Type*} [CommRing T] [CommRing A] [Algebra S T]
    (hsurj : Function.Surjective (algebraMap S T)) (f : A →+* T) (B : Ideal A) :
    Submodule.span S (Set.range (idealMapHom f B)) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨y, hy⟩ := y
  refine Submodule.span_induction
    (p := fun t ht => (⟨t, ht⟩ : ↥(Ideal.map f B))
      ∈ Submodule.span S (Set.range (idealMapHom f B))) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, hb, rfl⟩
    exact Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  · show (0 : ↥(Ideal.map f B)) ∈ _
    exact Submodule.zero_mem _
  · intro a b ha hb ha' hb'
    have h : (⟨a + b, Ideal.add_mem _ ha hb⟩ : ↥(Ideal.map f B)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [h]
    exact Submodule.add_mem _ ha' hb'
  · intro a x hx hx'
    obtain ⟨s, rfl⟩ := hsurj a
    have h : (⟨algebraMap S T s • x, Submodule.smul_mem _ _ hx⟩ : ↥(Ideal.map f B))
        = s • (⟨x, hx⟩ : ↥(Ideal.map f B)) := Subtype.ext (algebraMap_smul T s x)
    rw [h]
    exact Submodule.smul_mem _ _ hx'

/-- The multiplication map `KS ⊗_S M → M` is injective for every ideal `K ⊆ R`, when `M` is flat
over `R`: it receives `K ⊗_R M → M` surjectively, and that map is injective by flatness. -/
private theorem injective_lift_lsmul_map [Module.Flat R M] (Bs : Ideal S) (B : Ideal R)
    (hBs : Bs = Ideal.map (algebraMap R S) B) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul S M).comp Bs.subtype)) := by
  subst hBs
  have hψ : ∀ (r : R) (b : ↥B), idealMapHom (algebraMap R S) B (r • b)
      = (algebraMap R S r) • idealMapHom (algebraMap R S) B b :=
    fun r b => Subtype.ext (by simp [Algebra.smul_def])
  refine injective_of_comm_square _
    (tmulComp (M := M) (idealMapHom (algebraMap R S) B) hψ)
    (TensorProduct.lift ((LinearMap.lsmul R M).comp B.subtype)) (AddMonoidHom.id _)
    (fun b m => by simp [algebraMap_smul])
    (tmulComp_surjective _ hψ (span_range_eq_top_of_val_eq (fun x => ⟨x, rfl⟩) _ B)) ?_
    Function.injective_id
  have h1 : Function.Injective (LinearMap.rTensor M B.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ B.subtype_injective
  have h2 : TensorProduct.lift ((LinearMap.lsmul R M).comp B.subtype)
      = (TensorProduct.lid R M).toLinearMap ∘ₗ LinearMap.rTensor M B.subtype := by
    ext b m; simp
  rw [h2]
  exact (TensorProduct.lid R M).injective.comp h1

/-- The `algebraMap`-semilinear comparison `R ⧸ C → S ⧸ CS` of the quotients. -/
private def quotComp (C : Ideal R) : (R ⧸ C) →+ (S ⧸ Ideal.map (algebraMap R S) C) :=
  (algebraMap (R ⧸ C) (S ⧸ Ideal.map (algebraMap R S) C)).toAddMonoidHom

private theorem quotComp_mk (C : Ideal R) (r : R) :
    quotComp (S := S) C (Ideal.Quotient.mk C r)
      = Ideal.Quotient.mk _ (algebraMap R S r) := rfl

attribute [local simp] quotComp_mk

private theorem quotComp_semilinear (C : Ideal R) (r : R) (x : R ⧸ C) :
    quotComp (S := S) C (r • x) = (algebraMap R S r) • quotComp C x := by
  obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : r • (Ideal.Quotient.mk C r') = Ideal.Quotient.mk C (r * r') := rfl
  rw [h1, quotComp_mk, quotComp_mk, map_mul]
  rfl

/-- The comparison `(R/C) ⊗_R M → (S/CS) ⊗_S M` is injective: both sides are `M/CM`. -/
private theorem tmulComp_quotComp_injective (C : Ideal R) :
    Function.Injective
      (tmulComp (M := M) (quotComp (S := S) C) (quotComp_semilinear C)) := by
  have key : ∀ z : (R ⧸ C) ⊗[R] M, ∃ x : M,
      TensorProduct.quotTensorEquivQuotSMul M (Ideal.map (algebraMap R S) C)
          (tmulComp (M := M) (quotComp (S := S) C)
            (quotComp_semilinear C) z)
        = Submodule.Quotient.mk x
      ∧ TensorProduct.quotTensorEquivQuotSMul M C z = Submodule.Quotient.mk x := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul x m =>
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        refine ⟨r • m, ?_, ?_⟩
        · rw [tmulComp_tmul, quotComp_mk, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
            algebraMap_smul]
        · rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    | add p q hp hq =>
        obtain ⟨x, hx1, hx2⟩ := hp
        obtain ⟨y, hy1, hy2⟩ := hq
        exact ⟨x + y, by rw [map_add, map_add, hx1, hy1]; rfl,
          by rw [map_add, hx2, hy2]; rfl⟩
  intro u v huv
  rw [← sub_eq_zero] at huv ⊢
  rw [← map_sub] at huv
  obtain ⟨x, h1, h2⟩ := key (u - v)
  rw [huv, map_zero] at h1
  have hx : x ∈ C • (⊤ : Submodule R M) := by
    rw [← restrictScalars_smul_top_map (S := S) (M := M) C, Submodule.restrictScalars_mem]
    exact (Submodule.Quotient.mk_eq_zero _).mp h1.symm
  have h3 : TensorProduct.quotTensorEquivQuotSMul M C (u - v) = 0 := by
    rw [h2]; exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  exact (TensorProduct.quotTensorEquivQuotSMul M C).injective (by rw [h3, map_zero])

/-- The relative form: `(BS/CS) ⊗_S M → (S/CS) ⊗_S M` is injective when `M` is flat over `R`. -/
private theorem rTensor_subtype_map_mk_injective [Module.Flat R M] (C B : Ideal R)
    (Lb : Ideal (S ⧸ Ideal.map (algebraMap R S) C))
    (hLb : Lb = Ideal.map (algebraMap (R ⧸ C) (S ⧸ Ideal.map (algebraMap R S) C))
      (Ideal.map (Ideal.Quotient.mk C) B)) :
    Function.Injective (LinearMap.rTensor M (Lb.subtype.restrictScalars S)) := by
  subst hLb
  have hψ : ∀ (r : R) (x : ↥(Ideal.map (Ideal.Quotient.mk C) B)),
      idealMapHom (algebraMap (R ⧸ C) (S ⧸ Ideal.map (algebraMap R S) C))
          (Ideal.map (Ideal.Quotient.mk C) B) (r • x)
        = (algebraMap R S r) • idealMapHom
            (algebraMap (R ⧸ C) (S ⧸ Ideal.map (algebraMap R S) C))
            (Ideal.map (Ideal.Quotient.mk C) B) x :=
    fun r x => Subtype.ext (quotComp_semilinear (S := S) C r (x : R ⧸ C))
  have hsurj : Function.Surjective
      (algebraMap S (S ⧸ Ideal.map (algebraMap R S) C)) := Ideal.Quotient.mk_surjective
  exact injective_of_comm_square _
    (tmulComp (M := M) (idealMapHom (algebraMap (R ⧸ C)
      (S ⧸ Ideal.map (algebraMap R S) C)) (Ideal.map (Ideal.Quotient.mk C) B)) hψ)
    (LinearMap.rTensor M
      ((Ideal.map (Ideal.Quotient.mk C) B).subtype.restrictScalars R))
    (tmulComp (M := M) (quotComp (S := S) C) (quotComp_semilinear C)) (fun _ _ => rfl)
    (tmulComp_surjective _ hψ (span_range_eq_top_of_val_eq hsurj _ _))
    (rTensor_subtype_baseChange_inj (Ideal.map (Ideal.Quotient.mk C) B) inferInstance)
    (tmulComp_quotComp_injective C)

/-- The square of the extension of `I ^ a` vanishes in a ring where the extension of `I ^ b` does,
for every `b ≤ 2 a`: that square is the extension of `I ^ (2 a) ⊆ I ^ b`. -/
private theorem sq_map_pow_eq_bot {T : Type*} [CommRing T] (ψ : R →+* T) (I : Ideal R) {a b : ℕ}
    (hab : b ≤ a * 2) (hb : Ideal.map ψ (I ^ b) = ⊥) :
    Ideal.map ψ (I ^ a) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, ← pow_mul]
  exact le_bot_iff.mp ((Ideal.map_mono (Ideal.pow_le_pow_right hab)).trans hb.le)

/-- If `M` is flat over `R` and `M/IM` is flat over `S/IS`, then `M / (I ^ (k + 1))M` is flat
over `S / (I ^ (k + 1))S` for every `k`. -/
@[sga "3 VIB 12.7" "more general"]
private theorem flat_quotient_map_pow [Module.Flat R M] (I : Ideal R)
    [Module.Flat (S ⧸ I.map (algebraMap R S))
      (M ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S M)))] (k : ℕ) :
    Module.Flat (S ⧸ Ideal.map (algebraMap R S) (I ^ (k + 1)))
      (M ⧸ (Ideal.map (algebraMap R S) (I ^ (k + 1)) • (⊤ : Submodule S M))) := by
  induction k with
  | zero =>
      rw [zero_add, pow_one]
      infer_instance
  | succ k ih =>
      refine flat_of_sq_zero_local_criterion
        (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (I ^ (k + 1 + 1))))
          (Ideal.map (algebraMap R S) (I ^ (k + 1))))
        (by
          rw [Ideal.map_map]
          exact sq_map_pow_eq_bot _ I (show k + 1 + 1 ≤ (k + 1) * 2 by omega)
            (by rw [← Ideal.map_map]; exact Ideal.map_quotient_self _))
        (flat_quotient_map_quotient (Ideal.map (algebraMap R S) (I ^ (k + 1)))
          (Ideal.map (algebraMap R S) (I ^ (k + 1 + 1))) ih)
        (injective_lift_lsmul_of_rTensor_injective _ _
          (rTensor_subtype_map_mk_injective (I ^ (k + 1 + 1)) (I ^ (k + 1)) _ (by
            rw [Ideal.map_map, Ideal.map_map]
            congr 1)))

end Comparison

section Permanence

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Flat permanence**. If an `S`-module `M` is flat over `R` and faithfully flat over `S`,
then `S` is flat over `R`. -/
@[stacks 039V, ega "0 6.6.4" "sufficiency, flat case"]
theorem flat_of_flat_of_faithfullyFlat
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R M] [Module.FaithfullyFlat S M] : Module.Flat R S :=
  have : Module.Flat R (M ⊗[S] S) :=
    Module.Flat.of_linearEquiv ((TensorProduct.rid S M).restrictScalars R)
  Module.Flat.of_tensorProduct_of_faithfullyFlat (A := R) (C := S) (D := M) (P := S)

/-- A flat `S`-module `M` with nonzero fibre `M ⊗_S κ(𝔮)` at a prime `𝔮` becomes faithfully flat
over `S_𝔮` after localizing: `S_𝔮` is local, and its only fibre `(S_𝔮 ⊗_S M)/𝔪(S_𝔮 ⊗_S M)` is
`M ⊗_S κ(𝔮)`. -/
private theorem faithfullyFlat_baseChange_localizationAtPrime
    (M : Type*) [AddCommGroup M] [Module S M] [Module.Flat S M] (q : Ideal S) [q.IsPrime]
    (hne : Nontrivial (M ⊗[S] q.ResidueField)) :
    Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime q ⊗[S] M) := by
  have e : ((Localization.AtPrime q ⊗[S] M) ⧸
      (IsLocalRing.maximalIdeal (Localization.AtPrime q) •
        (⊤ : Submodule (Localization.AtPrime q) (Localization.AtPrime q ⊗[S] M))))
      ≃ (M ⊗[S] q.ResidueField) :=
    (TensorProduct.quotTensorEquivQuotSMul (Localization.AtPrime q ⊗[S] M)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q))).symm.toEquiv.trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange S (Localization.AtPrime q)
          (Localization.AtPrime q)
          (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q))
          M).toEquiv.trans
        (TensorProduct.comm S _ M).toEquiv)
  have hnt := e.nontrivial
  rw [Module.faithfullyFlat_iff]
  refine ⟨inferInstance, fun {m} hm => ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hm]
  intro htop
  exact not_subsingleton _ (Submodule.Quotient.subsingleton_iff.mpr htop)

/-- If `M` is flat over `R` and over `S`, then at a prime `𝔮 ⊆ S` whose fibre `M ⊗_S κ(𝔮)` is
nonzero, the localization `S_𝔮` is flat over `R`. -/
private theorem flat_localization_of_nontrivial_fiber {M : Type*} [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.Flat R M] [Module.Flat S M] (q : Ideal S)
    [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    [Algebra R Sq] [IsScalarTower R S Sq]
    (hne : Nontrivial (M ⊗[S] q.ResidueField)) : Module.Flat R Sq :=
  have := faithfullyFlat_baseChange_localizationAtPrime M q hne
  have : Module.Flat R (Localization.AtPrime q ⊗[S] M) :=
    Module.Flat.tensorProduct_of_flat_left (A := R) (C := S) (D := Localization.AtPrime q)
      (P := M)
  have : Module.Flat R (Localization.AtPrime q) :=
    flat_of_flat_of_faithfullyFlat (Localization.AtPrime q ⊗[S] M)
  Module.Flat.of_linearEquiv
    (AlgEquiv.restrictScalars R
      (IsLocalization.algEquiv q.primeCompl Sq (Localization.AtPrime q))).toLinearEquiv

end Permanence

/-- Let `I ⊆ R` be a nilpotent ideal and `M` an `S`-module which is flat over `R` and such that
`M/IM` is flat over `S/IS`. Then `M` is flat over `S`, and `S_𝔮` is flat over `R` for every prime
`𝔮 ⊆ S` with `M ⊗_S κ(𝔮)` nonzero. -/
public theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R) (hI : IsNilpotent I)
    [Module.Flat (S ⧸ I.map (algebraMap R S))
      (M ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S M)))]
    [Module.Flat R M] :
    Module.Flat S M ∧
      ∀ (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq]
        [IsLocalization.AtPrime Sq q] [Algebra R Sq] [IsScalarTower R S Sq],
        Nontrivial (M ⊗[S] q.ResidueField) → Module.Flat R Sq := by
  obtain ⟨n, hn⟩ := hI
  have hn' : I ^ n = ⊥ := by simpa using hn
  have hflat : Module.Flat S M :=
    flat_of_sq_zero_local_criterion (Ideal.map (algebraMap R S) (I ^ (n + 1)))
      (sq_map_pow_eq_bot _ I (show n ≤ (n + 1) * 2 by omega) (by rw [hn', Ideal.map_bot]))
      (flat_quotient_map_pow I n) (injective_lift_lsmul_map _ (I ^ (n + 1)) rfl)
  exact ⟨hflat, fun q _ Sq _ _ _ _ _ hne => flat_localization_of_nontrivial_fiber q Sq hne⟩

end Stacks.Flatness.NilpotentFibreCriterion

open TensorProduct

@[expose] public section

/-- **Critère de platitude par fibres, nilpotent case**. Let `R → S` be a map of commutative rings,
let `M` be an `S`-module whose `R`-module structure comes from `R → S`, and let `I ⊆ R` be a
nilpotent ideal. If `M/IM` is flat over `S/IS` and `M` is flat over `R`, then `M` is flat over `S`,
and `S_q` is flat over `R` for every prime `q ⊆ S` with `M ⊗_S κ(q)` nonzero. -/
@[stacks 06A5 "The auxiliary ring `S'` of the source's triangle is dropped: `M` is taken to be an
`S`-module over `R → S`, which is equivalent and does not mention `S'`. `IM` is written as
`IS • ⊤` over `S`, and `S_q` is an abstract localization at `q`; see the module docstring.",
  ega "IV 11.3.11" "(a) ⇒ (b), special case",
  sga "1 IV 5.9" "(ii) ⇒ (i), special case",
  sga "3 VIB 1.3.0" "special case",
  sga "3 VIB 12.7" "more general",
  sga "3 VIB 2.5" "flatness clause"]
public theorem Module.flat_and_flat_localization_of_flat_quotient_of_isNilpotent
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R) (hI : IsNilpotent I)
    [Module.Flat (S ⧸ I.map (algebraMap R S))
      (M ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S M)))]
    [Module.Flat R M] :
    Module.Flat S M ∧
      ∀ (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq]
        [IsLocalization.AtPrime Sq q] [Algebra R Sq] [IsScalarTower R S Sq],
        Nontrivial (M ⊗[S] q.ResidueField) → Module.Flat R Sq :=
  Stacks.Flatness.NilpotentFibreCriterion.solution I hI

end

namespace Stacks.Flatness.NoetherianFibreCriterion

open TensorProduct

universe u v w x

section SMulMap

variable (R : Type u) (N : Type v) [CommRing R] [AddCommGroup N] [Module R N]
  {P : Type w} [AddCommGroup P] [Module R P] {Q : Type x} [AddCommGroup Q] [Module R Q]

/-- Contraction of a tensor product along a linear form: the map `N ⊗[R] P → N`,
`n ⊗ p ↦ f p • n`, attached to `f : P →ₗ[R] R`. -/
noncomputable def smulMap (f : P →ₗ[R] R) : N ⊗[R] P →ₗ[R] N :=
  (TensorProduct.rid R N).toLinearMap ∘ₗ LinearMap.lTensor N f

/-- `smulMap R N f` is `TensorProduct.rid R N` after `LinearMap.lTensor N f`. -/
lemma coe_smulMap (f : P →ₗ[R] R) :
    (smulMap R N f : N ⊗[R] P → N) = TensorProduct.rid R N ∘ LinearMap.lTensor N f := rfl

/-- `smulMap R N f` sends `n ⊗ p` to `f p • n`. -/
lemma smulMap_tmul (f : P →ₗ[R] R) (n : N) (p : P) :
    smulMap R N f (n ⊗ₜ p) = f p • n := by simp [smulMap]

attribute [local simp] smulMap_tmul

/-- Contracting along `f ∘ₗ g` is contracting along `f` after tensoring `g` with `N`. -/
lemma smulMap_comp (f : P →ₗ[R] R) (g : Q →ₗ[R] P) :
    smulMap R N (f ∘ₗ g) = smulMap R N f ∘ₗ LinearMap.lTensor N g := by
  ext n q; simp

/-- Contracting `N ⊗[R] J` along the inclusion of an ideal is injective as soon as `N` is flat
over `R`: it is the base change of `J ↪ R` followed by an isomorphism. -/
lemma injective_smulMap_subtype [Module.Flat R N] (J : Ideal R) :
    Function.Injective (smulMap R N J.subtype) := by
  rw [coe_smulMap]
  exact (TensorProduct.rid R N).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype)

/-- If the contraction `N ⊗[R] J → N`, `n ⊗ x ↦ x • n`, along the inclusion of an ideal `J` is
injective, then so is `J ⊗[R] N → R ⊗[R] N`. -/
lemma injective_rTensor_subtype_of_injective_smulMap (J : Ideal R)
    (h : Function.Injective (smulMap R N J.subtype)) :
    Function.Injective (J.subtype.rTensor N) := by
  rw [coe_smulMap] at h
  exact (LinearMap.lTensor_inj_iff_rTensor_inj N J.subtype).mp h.of_comp

end SMulMap

section MulMap

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (J : Ideal R)

/-- The `S`-linear multiplication map `S ⊗[R] J → S`, `s ⊗ x ↦ algebraMap R S x * s`, attached to
an ideal `J` of `R`; its range is the ideal `J S` of `S`. -/
noncomputable def mulMap : S ⊗[R] J →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ J.subtype.baseChange S

/-- `mulMap R S J` sends `s ⊗ x` to `algebraMap R S x * s`. -/
lemma mulMap_tmul (s : S) (x : J) : mulMap R S J (s ⊗ₜ x) = algebraMap R S x * s := by
  simp [mulMap, Algebra.smul_def]

attribute [local simp] mulMap_tmul smulMap_tmul

/-- `mulMap` is the contraction of `S ⊗[R] J` along `J ↪ R`, forgetting its `S`-linearity. -/
lemma coe_mulMap : (mulMap R S J : S ⊗[R] J → S) = smulMap R S J.subtype := by
  refine funext fun z => ?_
  induction z with
  | zero => simp
  | tmul s x => simp [Algebra.smul_def]
  | add a b ha hb => simp [ha, hb]

/-- The range of `mulMap R S J` is the ideal `J S` of `S`. -/
lemma range_mulMap : LinearMap.range (mulMap R S J) = J.map (algebraMap R S) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨z, rfl⟩
    induction z with
    | zero => simp
    | tmul s x => simpa using Ideal.mul_mem_right s _ (Ideal.mem_map_of_mem _ x.2)
    | add a b ha hb => simpa using add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    exact fun x hx => ⟨(1 : S) ⊗ₜ ⟨x, hx⟩, by simp⟩

/-- `mulMap` with its target cut down to its range, the ideal `J S` of `S`. -/
noncomputable def mulMap' : S ⊗[R] J →ₗ[S] (J.map (algebraMap R S)) :=
  (mulMap R S J).codRestrict _ fun z => (range_mulMap R S J).le (LinearMap.mem_range_self _ z)

/-- `mulMap' R S J` followed by the inclusion of `J S` into `S` is `mulMap R S J`. -/
lemma subtype_comp_mulMap' :
    (J.map (algebraMap R S)).subtype ∘ₗ mulMap' R S J = mulMap R S J :=
  LinearMap.subtype_comp_codRestrict _ _ _

/-- `mulMap' R S J` is surjective onto the ideal `J S`. -/
lemma surjective_mulMap' : Function.Surjective (mulMap' R S J) := fun y => by
  obtain ⟨z, hz⟩ : (y : S) ∈ LinearMap.range (mulMap R S J) := (range_mulMap R S J).ge y.2
  exact ⟨z, Subtype.ext hz⟩

end MulMap

section Core

attribute [local simp] smulMap_tmul mulMap_tmul

variable (R : Type u) (S : Type v) (M : Type x) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (J : Ideal R)

/-- The two routes from `M ⊗[S] (S ⊗[R] J)` to `M` agree: both send `m ⊗ (s ⊗ x)` to
`(algebraMap R S x * s) • m`. -/
lemma smulMap_mulMap_apply (w : M ⊗[S] (S ⊗[R] J)) :
    smulMap S M (mulMap R S J) w =
      smulMap R M J.subtype (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M J w) := by
  induction w with
  | zero => simp
  | tmul m z =>
      induction z with
      | zero => simp
      | tmul s x =>
          simp only [smulMap_tmul, mulMap_tmul, Submodule.coe_subtype,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
          rw [mul_smul, algebraMap_smul]
      | add z₁ z₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- Contracting `M ⊗[S] (S ⊗[R] J)` along the multiplication `S ⊗[R] J → S` is injective when
`M` is flat over `R`. -/
lemma injective_smulMap_mulMap [Module.Flat R M] :
    Function.Injective (smulMap S M (mulMap R S J)) := by
  rw [show (smulMap S M (mulMap R S J) : M ⊗[S] (S ⊗[R] J) → M) =
      smulMap R M J.subtype ∘ TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M J from
    funext (smulMap_mulMap_apply R S M J)]
  exact (injective_smulMap_subtype R M J).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M J).injective

/-- If `M` is flat over `R`, then `J S ⊗[S] M → S ⊗[S] M` is injective for the ideal `J S` of
`S`. -/
lemma injective_rTensor_subtype_map [Module.Flat R M] :
    Function.Injective ((J.map (algebraMap R S)).subtype.rTensor M) := by
  refine injective_rTensor_subtype_of_injective_smulMap S M _ ?_
  refine Function.Injective.of_comp_right (g := LinearMap.lTensor M (mulMap' R S J)) ?_
    (LinearMap.lTensor_surjective M (surjective_mulMap' R S J))
  rw [← LinearMap.coe_comp, ← smulMap_comp, subtype_comp_mulMap']
  exact injective_smulMap_mulMap R S M J

/-- If `M` is flat over `R` and faithfully flat over `S`, then the multiplication map
`S ⊗[R] J → S` is injective. -/
private lemma injective_mulMap [Module.Flat R M] [Module.FaithfullyFlat S M] :
    Function.Injective (mulMap R S J) := by
  rw [← LinearMap.ker_eq_bot]
  have hzero : ∀ t : M ⊗[S] LinearMap.ker (mulMap R S J),
      smulMap S M (mulMap R S J)
        (LinearMap.lTensor M (LinearMap.ker (mulMap R S J)).subtype t) = 0 := by
    intro t
    induction t with
    | zero => simp
    | tmul m k =>
        have hk : mulMap R S J (k : S ⊗[R] J) = 0 := k.2
        simp [hk]
    | add t₁ t₂ h₁ h₂ => simp [h₁, h₂]
  have hinj := (injective_smulMap_mulMap R S M J).comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := M) _
      (LinearMap.ker (mulMap R S J)).injective_subtype)
  have : Subsingleton (M ⊗[S] LinearMap.ker (mulMap R S J)) :=
    ⟨fun a b => hinj ((hzero a).trans (hzero b).symm)⟩
  have : Subsingleton (LinearMap.ker (mulMap R S J)) :=
    Module.FaithfullyFlat.lTensor_reflects_triviality S M _
  exact Submodule.eq_bot_of_subsingleton

end Core

/-- A module that is flat over a local ring `S` and finite and nonzero over a local ring `S'`
above `S` is faithfully flat over `S`: Nakayama's lemma over `S'` gives `𝔪_{S'} M ≠ M`, and
`𝔪_S M` is contained in `𝔪_{S'} M`. -/
@[ega "IV 2.5.5.4" "sufficiency"]
lemma faithfullyFlat_of_flat (S : Type v) (S' : Type w) (M : Type x)
    [CommRing S] [CommRing S'] [IsLocalRing S] [IsLocalRing S'] [Algebra S S']
    [IsLocalHom (algebraMap S S')] [AddCommGroup M] [Module S M] [Module S' M]
    [IsScalarTower S S' M] [Module.Finite S' M] [Nontrivial M] [Module.Flat S M] :
    Module.FaithfullyFlat S M := by
  rw [Module.faithfullyFlat_iff]
  refine ⟨‹_›, fun {m} hm hm' => Module.maximalIdeal_smul_top_ne_top (R := S') M (top_le_iff.mp ?_)⟩
  rw [IsLocalRing.eq_maximalIdeal hm] at hm'
  refine le_trans (le_of_eq ?_)
    (Submodule.smul_mono_left (IsLocalRing.map_maximalIdeal_le (algebraMap S S')))
  refine ((Submodule.restrictScalars_eq_top_iff S S' _).mp ?_).symm
  rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top, hm']

/-- Let `R → S → S'` be local homomorphisms of Noetherian local rings and `M` a finite nonzero
`S'`-module which is flat over `R` and such that `M/𝔪M` is flat over `S/𝔪S`, for `𝔪` the maximal
ideal of `R`. Then `S` is flat over `R` and `M` is flat over `S`. -/
public theorem solution
    {R S S' M : Type*} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing S']
    [Algebra R S] [Algebra S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M]
    [Module.Finite S' M] [Nontrivial M]
    [Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M)))]
    [Module.Flat R M] :
    Module.Flat R S ∧ Module.Flat S M := by
  have hMS : Module.Flat S M :=
    Module.Flat.of_rTensor_subtype_injective_of_flat_quotient S' M _
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
      (injective_rTensor_subtype_map R S M (IsLocalRing.maximalIdeal R)) inferInstance
  have hff : Module.FaithfullyFlat S M := faithfullyFlat_of_flat S S' M
  have hinj : Function.Injective (smulMap R S (IsLocalRing.maximalIdeal R).subtype) := by
    rw [← coe_mulMap]
    exact injective_mulMap R S M (IsLocalRing.maximalIdeal R)
  refine ⟨Module.Flat.of_rTensor_subtype_injective_of_flat_quotient S S _
    (Ideal.IsMaximal.ne_top inferInstance)
    (injective_rTensor_subtype_of_injective_smulMap R S _ hinj) ?_, hMS⟩
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  exact Module.Flat.of_free

end Stacks.Flatness.NoetherianFibreCriterion

universe u v w

@[expose] public section

/-- **Critère de platitude par fibres, Noetherian local case**. Let `R → S → S'` be local
homomorphisms of Noetherian local rings, let `𝔪 ⊆ R` be the maximal ideal of `R`, and let `M` be an
`S'`-module whose `S`- and `R`-module structures come from the two ring maps. If `M` is finite over
`S'`, nonzero, `M/𝔪M` is flat over `S/𝔪S` and `M` is flat over `R`, then `S` is flat over `R` and
`M` is flat over `S`. -/
@[stacks 00MP "The composite `R → S'` is not assumed: the two scalar towers on `M` already pin
the `R`-action to the restriction along `R → S → S'`. `𝔪M` is written as `𝔪S • ⊤` over `S`, so
that the quotient carries the `S/𝔪S`-structure; see the module docstring.",
  ega "IV 11.3.10" "special case",
  ega "IV 11.3.10.1" "(a) ⇒ (b)",
  sga "1 I 5.9" "partial",
  sga "1 IV 5.9" "(ii) ⇒ (i)",
  sga "3 VIB 1.3.0" "special case",
  sga "3 VIB 12.7" "special case",
  sga "3 VIB 2.5" "flatness clause",
  sga "3 X 3.5" "Flat case"]
public theorem Module.flat_and_flat_of_flat_quotient_maximalIdeal_of_flat
    {R S S' M : Type*} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing S']
    [Algebra R S] [Algebra S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M]
    [Module.Finite S' M] [Nontrivial M]
    [Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M)))]
    [Module.Flat R M] :
    Module.Flat R S ∧ Module.Flat S M :=
  Stacks.Flatness.NoetherianFibreCriterion.solution (S' := S')

end
