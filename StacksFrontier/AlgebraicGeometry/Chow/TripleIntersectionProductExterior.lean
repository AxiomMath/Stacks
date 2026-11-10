module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommutingEveryClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CommutingAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommutingEveryCap
public import StacksFrontier.AlgebraicGeometry.Chow.TripleIntersectionProductChainCommute
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionPart

/-!
# The two exterior-product steps of the associativity of the intersection product

Let `k` be a field, `X` locally of finite type over `k` and `Δ^! ∈ A^d(X ⟶ X ×_k X)` a
bivariant class of the diagonal. The proof of Stacks 0FC1 runs through the chain

`(α · β) · γ = Δ^!(Δ₁₂^!((α × β) × γ)) = Δ^!(Δ₂₃^!((α × β) × γ))`
`           = Δ^!(Δ₂₃^!(α × (β × γ))) = Δ^!(α × Δ^!(β × γ)) = α · (β · γ)`,

and the source justifies the first and the penultimate equality by Remark 0FBY:

`Δ₂₃^!(α × η) = α × Δ^!(η)`   and   `Δ₁₂^!(ξ × γ) = Δ^!(ξ) × γ`.

Here `Δ₂₃^!` is the restriction (Stacks 0F9Z) of `Δ^!` along the projection of the triple product
to its last two factors, so that for `η` on `Z ×_k W` the class `Δ₂₃^!(α × η)` is the cap of
`Δ^!` itself against the test morphism `Y ×_k (Z ×_k W) ⟶ Z ×_k W ⟶ X ×_k X`. On the other hand
`Δ^!` restricts along `Z ×_k W ⟶ X ×_k X` to a class `c ∈ A^d(Z ×_X W ⟶ Z ×_k W)`, and the
equation is Stacks 0FBY for `c`, which over a field holds for every bivariant class.

In general, for a bivariant class `c` of a morphism
`u : Y ⟶ Z` and a morphism `h : T ⟶ Z`, the restriction of `c` along `h`, read on any scheme
`V` identified with `Y ×_Z T` over `T`, is a bivariant class for `V ⟶ T`; its cap product against
a class on `T` is `c ∩ -` at the test morphism `h`, and Stacks 0FBY for it is an identity between
the exterior product and `c ∩ -` at the test morphisms `X ×_k T ⟶ T ⟶ Z` and
`T ×_k X ⟶ T ⟶ Z`. Applied to the diagonal and the two factorwise diagonals this gives the two
instances of Stacks 0FBY in the proof of Stacks 0FC1.

## Main definitions

* `Stacks.Chow.bivariantRestrictionTransport` — the restriction of a bivariant class along
  `h : T ⟶ Z` (Stacks 0F9Z), transported to a scheme `V` isomorphic to `Y ×_Z T` over `T`.
* `Stacks.Chow.dimPartOverIntersectionProduct` — the intersection product of Stacks 0FC0 for `X`
  smooth of arbitrary dimension, formed over the open and closed parts `X_d` of `X` of constant
  dimension, as the source prescribes.
* `Stacks.Chow.pullbackPullbackSwap` — the exchange `Y ×_P (Y ×_P T) ⟶ Y ×_P (Y ×_P T)` of the
  two points of `Y`, for the pullbacks of `Y ⟶ P` along two test morphisms `T ⟶ P`.

## Main results

* `Stacks.Chow.bivariantRestrictionTransport_capTarget` — the restricted class caps a class on
  `T` as the original class at the test morphism `h`.
* `Stacks.Chow.chowExteriorProduct_tmul_cap_of_field`,
  `Stacks.Chow.chowExteriorProduct_cap_tmul_of_field` — Stacks 0FBY for a restricted class over
  a field, in the second and in the first variable of the exterior product.
* `Stacks.Chow.commutesDiagonalCapExteriorSecond_of_field`,
  `Stacks.Chow.commutesDiagonalCapExteriorFirst_of_field` — the penultimate and the first step of
  the chain of Stacks 0FC1, for every bivariant class of the diagonal.
* `Stacks.Chow.isAssociativeIntersectionProduct_of_field` — Stacks 0FC1 over a field from
  Stacks 0FBP for the class of the diagonal on the triple product.
* `Stacks.Chow.chowPushforwardOfIso_cap_cap_eq_of_bivariantCommute` — if the restrictions of a
  class `c` along two test morphisms `t₁, t₂ : T ⟶ P` commute (Stacks 0FA2), then
  `c ∩_{t₁} c ∩_{t₂} = c ∩_{t₂} c ∩_{t₁}` on `CH_*(T)`.
* `Stacks.Chow.diagonalGysinCommuteOnTripleProduct_of_commutesWithEveryClass` —
  `Stacks.Chow.DiagonalGysinCommuteOnTripleProductOverBase` holds as soon as the restriction of
  `Δ^!` along `Δ₁₂` commutes with every bivariant class over the triple product.
* `Stacks.Chow.isAssociativeIntersectionProduct_of_field_of_commutesWithEveryClass`,
  `Stacks.Chow.isAssociativeIntersectionProduct_diagonalGysinClass_of_commutesWithEveryClass` —
  Stacks 0FC1 over a field, for any class of the diagonal and for the Gysin class of Stacks 0FBR,
  from that commutation.
* `Stacks.Chow.diagonalGysinClass_bivariantRestriction_commutesWithEveryClass` — the restriction
  of the Gysin class `Δ^!` of the diagonal of a smooth morphism along any morphism commutes with
  every bivariant class.
* `Stacks.Chow.isAssociativeIntersectionProduct_canonical_of_relativeDimension` — Stacks 0FC1
  for `X` smooth over a field `k` of constant dimension: the intersection product formed with the
  Gysin class of the diagonal is associative.
* `Stacks.Chow.isAssociativeIntersectionProduct_canonical` — **Stacks 0FC1**: for `X` smooth over
  a field `k` of arbitrary dimension, the intersection product formed part by part over the open
  and closed parts of `X` of constant dimension (`Stacks.Chow.dimPartOverIntersectionProduct`) is
  associative.

## Implementation notes

The bivariant classes are those of the Gysin system of invertible modules,
`Stacks.Chow.gysinSystemOfInvertible`, the system at which Stacks 0FBY is proved over a field
and at which restriction and transport of bivariant classes need no hypothesis, by
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso`.

The exterior product of Stacks 0FBV is presented on a structure morphism `sT` of `T` that is only
propositionally equal to `h ≫ sZ`. The results are stated for an arbitrary such `sT`; this is
what lets the class `α × η` on `Y ×_k (Z ×_k W)` be capped against `Δ₂₃` without a transport of
the exterior product along an isomorphism of its second factor.

The step `Δ^!(Δ₁₂^!(x)) = Δ^!(Δ₂₃^!(x))` of the chain is the commutation of the two
restrictions `Δ₁₂^!` and `Δ₂₃^!` of `Δ^!` to the triple product, two classes over the triple
product and not over `X ×_k X`. The results for an arbitrary class of the diagonal take as
hypothesis that `Δ₁₂^!` commutes with every bivariant class over the triple product; for the Gysin
class of the diagonal of a smooth morphism this is
`Stacks.Chow.diagonalGysinClass_bivariantRestriction_commutesWithEveryClass`.

## References

* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FC1](https://stacks.math.columbia.edu/tag/0FC1)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Restriction of a bivariant class, read on an isomorphic scheme -/

/-- An isomorphism `θ : Y ×_Z T ≅ V` over `T`, for `u : Y ⟶ Z` and `h : T ⟶ Z` over a base `S`,
is a morphism over `S`. -/
theorem pullbackIso_hom_comp_structureMorphism {S Y Z T V : Scheme.{u}} (sY : Y ⟶ S)
    (sZ : Z ⟶ S) (u : Y ⟶ Z) (hu : u ≫ sZ = sY) (h : T ⟶ Z) (sT : T ⟶ S) (hT : h ≫ sZ = sT)
    (sV : V ⟶ S) (v : V ⟶ T) (hV : v ≫ sT = sV) (θ : (pullback u h : Scheme.{u}) ≅ V)
    (hθ : θ.hom ≫ v = pullback.snd u h) : θ.hom ≫ sV = pullback.fst u h ≫ sY := by
  rw [← hV, ← Category.assoc, hθ, ← hT, ← Category.assoc, ← pullback.condition, Category.assoc,
    hu]

section TransportRestriction

variable (C : ChowSituation.{u}) (G : GysinSystem C) (hgys : G.IsNaturalUnderBaseChangeIso)
  {Y Z T V : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (u : Y ⟶ Z) [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)
  (c : BivariantClass C G sY sZ u hu p) (h : T ⟶ Z) [LocallyOfFiniteType h]
  (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (v : V ⟶ T) [LocallyOfFiniteType v]
  (hV : v ≫ (h ≫ sZ) = sV) (θ : (pullback u h : Scheme.{u}) ≅ V)
  (hθ : θ.hom ≫ v = pullback.snd u h)

/-- **Stacks 0F9Z, read on an isomorphic scheme.** The restriction of a bivariant class
`c ∈ A^p(Y ⟶ Z)` along `h : T ⟶ Z`, a class in `A^p(Y ×_Z T ⟶ T)`, transported along an
isomorphism `θ : Y ×_Z T ≅ V` over `T` to a class in `A^p(V ⟶ T)`. -/
abbrev bivariantRestrictionTransport : BivariantClass C G sV (h ≫ sZ) v hV p :=
  bivariantTransport C G (pullback.fst u h ≫ sY) sV (h ≫ sZ) (pullback.snd u h)
    (pullbackSnd_comp_structureMorphism_eq C sY sZ u hu h) v hV θ hθ p hgys
    (bivariantRestriction C G sY sZ u hu h p hgys c)

/-- The cap operation of the restriction of `c` along `h` at a test morphism `r : W ⟶ T` is the
cap operation of `c` at `r ≫ h`, carried to `V ×_T W` by the canonical identification. -/
theorem bivariantRestrictionTransport_cap {W : Scheme.{u}} (r : W ⟶ T) [LocallyOfFiniteType r]
    (k : ℤ) (y : chowGroup C (r ≫ (h ≫ sZ)) k) :
    (bivariantRestrictionTransport C G hgys sY sZ u hu p c h sV v hV θ hθ).cap r k y =
      chowPushforwardOfIso C (pullback.fst u (r ≫ h) ≫ sY) (pullback.fst v r ≫ sV)
        ((pullbackLeftPullbackSndIso u h r).inv ≫ (transportPullbackIso _ v θ hθ r).hom)
        (by simp [pullbackIso_hom_comp_structureMorphism sY sZ u hu h (h ≫ sZ) rfl sV v hV θ hθ])
        (k - p)
        (c.cap (r ≫ h) k (chowGroupCongr C (Category.assoc r h sZ).symm k y)) := by
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestriction_cap,
    bivariantRestrictionCap_apply, chowPushforwardOfIso_comp_apply]

/-- **The restricted class caps as the original class at the test morphism.** The cap product
of the restriction of `c` along `h` against a class `y` on `T` itself is `c ∩ y` at the test
morphism `h`, read on `V` through `θ`. -/
theorem bivariantRestrictionTransport_capTarget (k : ℤ) (y : chowGroup C (h ≫ sZ) k) :
    (bivariantRestrictionTransport C G hgys sY sZ u hu p c h sV v hV θ hθ).capTarget C G sV
        (h ≫ sZ) v hV p k y =
      chowPushforwardOfIso C (pullback.fst u h ≫ sY) sV θ.hom
        (pullbackIso_hom_comp_structureMorphism sY sZ u hu h (h ≫ sZ) rfl sV v hV θ hθ) (k - p)
        (c.cap h k y) := by
  have hcap : chowPushforwardOfIso C (pullback.fst u (𝟙 T ≫ h) ≫ sY) (pullback.fst u h ≫ sY)
      (pullback.congrHom rfl (Category.id_comp h)).hom (by simp) (k - p)
      (c.cap (𝟙 T ≫ h) k (chowGroupCongr C (by simp) k y)) = c.cap h k y :=
    chowPushforwardOfIso_congrHom_cap C G sY sZ u hu p c (Category.id_comp h) (by simp) k y
      (by simp) rfl
  rw [BivariantClass.capTarget, bivariantRestrictionTransport_cap,
    chowPushforwardOfIso_comp_apply, ← hcap, chowPushforwardOfIso_comp_apply,
    chowGroupCongr_chowGroupCongr]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  rw [pullbackIdIso_inv_eq_fst, Category.assoc, transportPullbackIso_hom_fst, ← Category.assoc]
  congr 1
  ext <;> simp

end TransportRestriction

/-! ### Stacks 0FBY for a restricted class over a field -/

section AtTest

variable (k : Type u) [Field k] {X Y Z T V : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z)
  [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)
  (c : BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
    sY sZ u hu p)
  (h : T ⟶ Z) [LocallyOfFiniteType h] (sT : T ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sT] (hT : h ≫ sZ = sT) (sV : V ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sV] (v : V ⟶ T) [LocallyOfFiniteType v] (hV : v ≫ sT = sV)
  (θ : (pullback u h : Scheme.{u}) ≅ V) (hθ : θ.hom ≫ v = pullback.snd u h)

/-- **Stacks 0FBY for a restricted class, in the second variable.** Let `c ∈ A^p(Y ⟶ Z)` be a
bivariant class over a field, `h : T ⟶ Z`, and `V ≅ Y ×_Z T` over `T`. Then for `α ∈ CH_n(X)` and
`η ∈ CH_m(T)`

  `α × (c ∩ η) = c ∩ (α × η)`   in   `CH_{n + (m - p)}(X ×_k V)`,

where on the left `c ∩ η` is the cap at the test morphism `h`, read on `V`, and on the right the
cap is taken at the test morphism `X ×_k T ⟶ T ⟶ Z` and read on `X ×_k V`. -/
theorem chowExteriorProduct_tmul_cap_of_field (n m : ℤ)
    (α : chowGroup (fieldChowSituation k) sX n) (η : chowGroup (fieldChowSituation k) sT m) :
    chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) sX sV n (m - p)
        (α ⊗ₜ[ℤ] chowPushforwardOfIso (fieldChowSituation k) (pullback.fst u h ≫ sY) sV θ.hom
          (pullbackIso_hom_comp_structureMorphism sY sZ u hu h sT hT sV v hV θ hθ) (m - p)
          (c.cap h m (chowGroupCongr (fieldChowSituation k) hT.symm m η))) =
      chowPushforwardOfIso (fieldChowSituation k)
        (pullback.fst u (pullback.snd sX sT ≫ h) ≫ sY) (pullback.fst sX sV ≫ sX)
        ((pullbackLeftPullbackSndIso u h (pullback.snd sX sT)).inv ≫
          (transportPullbackIso (pullback.snd u h) v θ hθ (pullback.snd sX sT)).hom ≫
            (exteriorCapIso sX sT v hV).hom)
        (by rw [Category.assoc, Category.assoc, exteriorCapIso_hom_comp_structureMorphism]
            simp [pullbackIso_hom_comp_structureMorphism sY sZ u hu h sT hT sV v hV θ hθ])
        (n + (m - p))
        (chowGroupDegreeEquiv (fieldChowSituation k)
          (pullback.fst u (pullback.snd sX sT ≫ h) ≫ sY) (by omega : n + m - p = n + (m - p))
          (c.cap (pullback.snd sX sT ≫ h) (n + m)
            (chowGroupCongr (fieldChowSituation k)
              (by rw [Category.assoc, hT, pullback.condition]) (n + m)
              (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) sX sT n m
                (α ⊗ₜ[ℤ] η))))) := by
  subst hT
  have key := commutesExteriorProductCapAt_of_field k sX sV (h ≫ sZ) v hV p
    (bivariantRestrictionTransport (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k))
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso (fieldChowSituation k)) sY sZ u hu p
      c h sV v hV θ hθ) n m α η
  unfold exteriorProductCap capExteriorProduct exteriorProductOnTarget at key
  rw [bivariantRestrictionTransport_capTarget, bivariantRestrictionTransport_cap,
    chowGroupDegreeEquiv_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply,
    chowGroupCongr_chowGroupCongr] at key
  refine key.trans ?_
  exact chowPushforwardOfIso_congr_apply _ _ _ _ _ (Category.assoc _ _ _) _ _ _ _

/-- **Stacks 0FBY for a restricted class, in the first variable.** With the notation of
`Stacks.Chow.chowExteriorProduct_tmul_cap_of_field`, for `ξ ∈ CH_m(T)` and `γ ∈ CH_n(X)`

  `(c ∩ ξ) × γ = c ∩ (ξ × γ)`   in   `CH_{(m - p) + n}(V ×_k X)`,

the cap on the right being taken at the test morphism `T ×_k X ⟶ T ⟶ Z`. -/
theorem chowExteriorProduct_cap_tmul_of_field (m n : ℤ)
    (ξ : chowGroup (fieldChowSituation k) sT m) (γ : chowGroup (fieldChowSituation k) sX n) :
    chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) sV sX (m - p) n
        (chowPushforwardOfIso (fieldChowSituation k) (pullback.fst u h ≫ sY) sV θ.hom
          (pullbackIso_hom_comp_structureMorphism sY sZ u hu h sT hT sV v hV θ hθ) (m - p)
          (c.cap h m (chowGroupCongr (fieldChowSituation k) hT.symm m ξ)) ⊗ₜ[ℤ] γ) =
      chowPushforwardOfIso (fieldChowSituation k)
        (pullback.fst u (pullback.fst sT sX ≫ h) ≫ sY) (pullback.fst sV sX ≫ sV)
        ((pullbackLeftPullbackSndIso u h (pullback.fst sT sX)).inv ≫
          (transportPullbackIso (pullback.snd u h) v θ hθ (pullback.fst sT sX)).hom ≫
            (exteriorCapFstIso sX sT v hV).hom)
        (by rw [Category.assoc, Category.assoc, exteriorCapFstIso_hom_comp_structureMorphism]
            simp [pullbackIso_hom_comp_structureMorphism sY sZ u hu h sT hT sV v hV θ hθ])
        ((m - p) + n)
        (chowGroupDegreeEquiv (fieldChowSituation k)
          (pullback.fst u (pullback.fst sT sX ≫ h) ≫ sY) (by omega : m + n - p = (m - p) + n)
          (c.cap (pullback.fst sT sX ≫ h) (m + n)
            (chowGroupCongr (fieldChowSituation k) (by rw [Category.assoc, hT]) (m + n)
              (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) sT sX m n
                (ξ ⊗ₜ[ℤ] γ))))) := by
  subst hT
  have key := chowExteriorProduct_capTarget_eq_capExteriorProductFst_of_field k sX sV (h ≫ sZ) v
    hV p (bivariantRestrictionTransport (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k))
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso (fieldChowSituation k)) sY sZ u hu p
      c h sV v hV θ hθ) m n ξ γ
  unfold capExteriorProductFst at key
  rw [bivariantRestrictionTransport_capTarget, bivariantRestrictionTransport_cap,
    chowGroupDegreeEquiv_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply] at key
  refine key.trans ?_
  exact chowPushforwardOfIso_congr_apply _ _ _ _ _ (Category.assoc _ _ _) _ _ _ _

end AtTest

/-! ### Two caps of a class against two test morphisms -/

section Swap

variable {Y P T : Scheme.{u}} (Δ : Y ⟶ P) (t₁ t₂ : T ⟶ P)

/-- The canonical morphism exchanging the two points of `Y` in an iterated pullback of
`Δ : Y ⟶ P`: a point `(y₂, (y₁, x))` of `Y ×_P (Y ×_P T)` with `Δ y₁ = t₂ x` and `Δ y₂ = t₁ x`
is sent to `(y₁, (y₂, x))`. -/
def pullbackPullbackSwap :
    (pullback Δ (pullback.snd Δ t₂ ≫ t₁) : Scheme.{u}) ⟶
      (pullback Δ (pullback.snd Δ t₁ ≫ t₂) : Scheme.{u}) :=
  pullback.lift (pullback.snd Δ (pullback.snd Δ t₂ ≫ t₁) ≫ pullback.fst Δ t₂)
    (pullback.lift (pullback.fst Δ (pullback.snd Δ t₂ ≫ t₁))
      (pullback.snd Δ (pullback.snd Δ t₂ ≫ t₁) ≫ pullback.snd Δ t₂)
      (by rw [pullback.condition, Category.assoc]))
    (by
      simp only [Category.assoc, pullback.lift_snd_assoc]
      rw [pullback.condition (f := Δ) (g := t₂)])

/-- The exchange sends the outer point of `Y` to the inner one. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackSwap_fst :
    pullbackPullbackSwap Δ t₁ t₂ ≫ pullback.fst Δ (pullback.snd Δ t₁ ≫ t₂) =
      pullback.snd Δ (pullback.snd Δ t₂ ≫ t₁) ≫ pullback.fst Δ t₂ :=
  pullback.lift_fst _ _ _

/-- The exchange sends the inner point of `Y` to the outer one. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackSwap_snd_fst :
    pullbackPullbackSwap Δ t₁ t₂ ≫ pullback.snd Δ (pullback.snd Δ t₁ ≫ t₂) ≫
        pullback.fst Δ t₁ =
      pullback.fst Δ (pullback.snd Δ t₂ ≫ t₁) := by
  rw [pullbackPullbackSwap, pullback.lift_snd_assoc, pullback.lift_fst]

/-- The exchange does not move the point of `T`. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackSwap_snd_snd :
    pullbackPullbackSwap Δ t₁ t₂ ≫ pullback.snd Δ (pullback.snd Δ t₁ ≫ t₂) ≫
        pullback.snd Δ t₁ =
      pullback.snd Δ (pullback.snd Δ t₂ ≫ t₁) ≫ pullback.snd Δ t₂ := by
  rw [pullbackPullbackSwap, pullback.lift_snd_assoc, pullback.lift_snd]

end Swap

section RestrictionCap

variable {C : ChowSituation.{u}} {G : GysinSystem C} (hgys : G.IsNaturalUnderBaseChangeIso)
  {X Y Y' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
  [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
  (c : BivariantClass C G sX sY f hf p) (h : Y' ⟶ Y) [LocallyOfFiniteType h]

/-- The restriction of `c` along `h` caps a class on `Y'` itself, at the identity test morphism,
as `c` caps it at `h`, read through the identification `X ×_Y Y' ≅ (X ×_Y Y') ×_{Y'} Y'`. -/
theorem bivariantRestriction_cap_id_heq (k : ℤ) (α : chowGroup C (𝟙 Y' ≫ (h ≫ sY)) k)
    (x : chowGroup C (h ≫ sY) k) (hα : α ≍ x) :
    (bivariantRestriction C G sX sY f hf h p hgys c).cap (𝟙 Y') k α ≍
      chowPushforwardOfIso C (pullback.fst f h ≫ sX)
        (pullback.fst (pullback.snd f h) (𝟙 Y') ≫ (pullback.fst f h ≫ sX))
        ((pullback.congrHom (rfl : f = f) (Category.id_comp h).symm).hom ≫
          (pullbackLeftPullbackSndIso f h (𝟙 Y')).inv) (by simp) (k - p) (c.cap h k x) := by
  have e := chowPushforwardOfIso_congrHom_cap C G sX sY f hf p c (Category.id_comp h).symm
    (by simp) k x rfl
    (by simp)
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply,
    ← chowPushforwardOfIso_comp_apply C (pullback.fst f h ≫ sX) (pullback.fst f (𝟙 Y' ≫ h) ≫ sX)
      _ _ _ (by simp) (by simp)]
  refine heq_of_eq (congrArg _ (Eq.trans ?_ e.symm))
  exact congrArg _ (eq_of_heq ((chowGroupCongr_heq C _ k α).trans
    (hα.trans (chowGroupCongr_heq C _ k x).symm)))

/-- The restriction of `c` along `h` caps a class pushed forward along an isomorphism `u` of test
schemes as `c` caps the original class at the composite test morphism `m = u ≫ s ≫ h`, read
through the induced identification of base changes. -/
theorem bivariantRestriction_cap_heq_chowPushforwardOfIso {T T' : Scheme.{u}} (s : T ⟶ Y')
    [LocallyOfFiniteType s] (u : T' ⟶ T) [IsIso u] (m : T' ⟶ Y) [LocallyOfFiniteType m]
    (hm : u ≫ s ≫ h = m) {qm : T' ⟶ C.S} [LocallyOfFiniteType qm] {k k' : ℤ} (hk : k = k')
    (x : chowGroup C qm k) (y : chowGroup C (s ≫ (h ≫ sY)) k')
    (hux : u ≫ (s ≫ (h ≫ sY)) = qm) (hy : y ≍ chowPushforwardOfIso C qm (s ≫ (h ≫ sY)) u hux k x)
    (x' : chowGroup C (m ≫ sY) k) (hx : x' ≍ x) :
    (bivariantRestriction C G sX sY f hf h p hgys c).cap s k' y ≍
      chowPushforwardOfIso C (pullback.fst f m ≫ sX)
        (pullback.fst (pullback.snd f h) s ≫ (pullback.fst f h ≫ sX))
        ((testBaseChangeIso f (s ≫ h) u m hm).hom ≫ (pullbackLeftPullbackSndIso f h s).inv)
        (by simp) (k - p) (c.cap m k x') := by
  have hux' : u ≫ ((s ≫ h) ≫ sY) = qm := by rw [Category.assoc s h sY, hux]
  have key := c.cap_heq_chowPushforwardOfIso (s ≫ h) u m hm hk x
    (chowGroupCongr C (Category.assoc s h sY).symm k' y) hux'
    ((chowGroupCongr_heq C _ k' y).trans (hy.trans (chowPushforwardOfIso_heq u _ _ rfl
      (Category.assoc s h sY).symm rfl HEq.rfl))) x' hx
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply]
  exact chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl (by simp) (by simp) rfl rfl
    (by rw [hk]) _ _ key

end RestrictionCap

section TwoCaps

/-- Two classes whose pushforwards along isomorphisms `Ξ₁`, `Ξ₂` to a common scheme agree have
equal pushforwards along any two isomorphisms `Θ₁`, `Θ₂` with `Ξ₂ ≫ Ξ₁⁻¹ ≫ Θ₁ = Θ₂`. -/
theorem chowPushforwardOfIso_eq_of_heq {C : ChowSituation.{u}} {A₁ A₂ Q V : Scheme.{u}}
    {s₁ : A₁ ⟶ C.S} [LocallyOfFiniteType s₁] {s₂ : A₂ ⟶ C.S} [LocallyOfFiniteType s₂]
    {sQ sQ' : Q ⟶ C.S} [LocallyOfFiniteType sQ] [LocallyOfFiniteType sQ'] {sV : V ⟶ C.S}
    [LocallyOfFiniteType sV] (Ξ₁ : A₁ ⟶ Q) [IsIso Ξ₁] (Ξ₂ : A₂ ⟶ Q) [IsIso Ξ₂] (Θ₁ : A₁ ⟶ V)
    [IsIso Θ₁] (Θ₂ : A₂ ⟶ V) [IsIso Θ₂] (hΞ₁ : Ξ₁ ≫ sQ' = s₁) (hΞ₂ : Ξ₂ ≫ sQ = s₂)
    (hΘ₁ : Θ₁ ≫ sV = s₁) (hΘ₂ : Θ₂ ≫ sV = s₂) (hQ : sQ = sQ') (hΘ : Ξ₂ ≫ inv Ξ₁ ≫ Θ₁ = Θ₂)
    {k k' : ℤ} (hk : k = k') (x₁ : chowGroup C s₁ k') (x₂ : chowGroup C s₂ k)
    (h : chowPushforwardOfIso C s₂ sQ Ξ₂ hΞ₂ k x₂ ≍ chowPushforwardOfIso C s₁ sQ' Ξ₁ hΞ₁ k' x₁) :
    chowPushforwardOfIso C s₂ sV Θ₂ hΘ₂ k x₂ ≍ chowPushforwardOfIso C s₁ sV Θ₁ hΘ₁ k' x₁ := by
  subst hQ hk
  have h' := congrArg (chowPushforwardOfIso C sQ sV (inv Ξ₁ ≫ Θ₁)
    (by rw [Category.assoc, hΘ₁, IsIso.inv_comp_eq, hΞ₁]) k) (eq_of_heq h)
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ Θ₂ hΘ _ hΘ₂,
    chowPushforwardOfIso_congr_apply C _ _ _ Θ₁ (by simp) _ hΘ₁] at h'
  exact heq_of_eq h'

variable {C : ChowSituation.{u}} {G : GysinSystem C} (hgys : G.IsNaturalUnderBaseChangeIso)
  {X P T : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sP : P ⟶ C.S}
  [LocallyOfFiniteType sP] {Δ : X ⟶ P} [LocallyOfFiniteType Δ] {hΔ : Δ ≫ sP = sX} {d : ℤ}
  (Dc : BivariantClass C G sX sP Δ hΔ d) (t₁ t₂ : T ⟶ P) [LocallyOfFiniteType t₁]
  [LocallyOfFiniteType t₂] (h₁₂ : t₂ ≫ sP = t₁ ≫ sP)

/-- **Two caps of one class against two test morphisms commute, if the two restrictions do.**
Let `c ∈ A^d(X ⟶ P)` be a bivariant class and `t₁, t₂ : T ⟶ P` two test morphisms. If the
restrictions (Stacks 0F9Z) of `c` along `t₁` and along `t₂`, both classes over `T`, commute in
the sense of Stacks 0FA2, then for every `x ∈ CH_k(T)`

  `c ∩_{t₁} (c ∩_{t₂} x) = c ∩_{t₂} (c ∩_{t₁} x)`,

the outer caps being taken at the test morphisms `X ×_P T ⟶ T ⟶ P`, and the two sides compared
by pushing them forward along any two isomorphisms `Θ₂`, `Θ₁` that differ by the canonical
exchange `Stacks.Chow.pullbackPullbackSwap` of the two points of `X`. -/
theorem chowPushforwardOfIso_cap_cap_eq_of_bivariantCommute
    (hcomm : BivariantCommute C G (t₁ ≫ sP) (pullback.snd Δ t₁) (pullback.snd Δ t₂) d d
      (bivariantClassCongrBase C G (pullback.snd Δ t₁)
        (pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁) (hv' := rfl) d
        (bivariantRestriction C G sX sP Δ hΔ t₁ d hgys Dc))
      (bivariantClassCongrBase C G (pullback.snd Δ t₂)
        (by rw [← h₁₂, pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₂] :
          pullback.fst Δ t₂ ≫ sX = pullback.snd Δ t₂ ≫ (t₁ ≫ sP)) h₁₂
        (hv := pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₂) (hv' := rfl) d
        (bivariantRestriction C G sX sP Δ hΔ t₂ d hgys Dc)))
    {V : Scheme.{u}} (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
    (Θ₁ : (pullback Δ (pullback.snd Δ t₁ ≫ t₂) : Scheme.{u}) ⟶ V) [IsIso Θ₁]
    (Θ₂ : (pullback Δ (pullback.snd Δ t₂ ≫ t₁) : Scheme.{u}) ⟶ V) [IsIso Θ₂]
    (hΘ₁ : Θ₁ ≫ sV = pullback.fst Δ (pullback.snd Δ t₁ ≫ t₂) ≫ sX)
    (hΘ₂ : Θ₂ ≫ sV = pullback.fst Δ (pullback.snd Δ t₂ ≫ t₁) ≫ sX)
    (hΘ : pullbackPullbackSwap Δ t₁ t₂ ≫ Θ₁ = Θ₂) (k : ℤ) (x : chowGroup C (t₁ ≫ sP) k) :
    chowPushforwardOfIso C (pullback.fst Δ (pullback.snd Δ t₂ ≫ t₁) ≫ sX) sV Θ₂ hΘ₂ (k - d - d)
        (Dc.cap (pullback.snd Δ t₂ ≫ t₁) (k - d)
          (chowGroupCongr C (by rw [Category.assoc, ← h₁₂,
              pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₂]) (k - d)
            (Dc.cap t₂ k (chowGroupCongr C h₁₂.symm k x)))) =
      chowPushforwardOfIso C (pullback.fst Δ (pullback.snd Δ t₁ ≫ t₂) ≫ sX) sV Θ₁ hΘ₁
        (k - d - d)
        (Dc.cap (pullback.snd Δ t₁ ≫ t₂) (k - d)
          (chowGroupCongr C (by rw [Category.assoc, h₁₂,
              pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁]) (k - d)
            (Dc.cap t₁ k x))) := by
  have hsA₂ : pullback.fst Δ t₂ ≫ sX = pullback.snd Δ t₂ ≫ (t₁ ≫ sP) := by
    rw [← h₁₂, pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₂]
  have hBC := hcomm (𝟙 T) k (chowGroupCongr C (Category.id_comp (t₁ ≫ sP)).symm k x)
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply] at hBC
  have h₁ := (bivariantClassCongrBase_cap C G (pullback.snd Δ t₁)
    (pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁).symm rfl (hv' := rfl) d
    (bivariantRestriction C G sX sP Δ hΔ t₁ d hgys Dc) (𝟙 T) k
    (chowGroupCongr C (Category.id_comp (t₁ ≫ sP)).symm k x)
    (chowGroupCongr C (Category.id_comp (t₁ ≫ sP)).symm k x) HEq.rfl).trans
    (bivariantRestriction_cap_id_heq hgys Dc t₁ k _ x (chowGroupCongr_heq C _ k x))
  have h₂ := (bivariantClassCongrBase_cap C G (pullback.snd Δ t₂) hsA₂ h₁₂ (hv' := rfl) d
    (bivariantRestriction C G sX sP Δ hΔ t₂ d hgys Dc) (𝟙 T) k
    (chowGroupCongr C (by rw [h₁₂]) k (chowGroupCongr C (Category.id_comp (t₁ ≫ sP)).symm k x))
    (chowGroupCongr C (Category.id_comp (t₁ ≫ sP)).symm k x)
    (chowGroupCongr_heq C _ k _)).trans
    (bivariantRestriction_cap_id_heq hgys Dc t₂ k _ (chowGroupCongr C h₁₂.symm k x)
      ((chowGroupCongr_heq C _ k _).trans ((chowGroupCongr_heq C _ k x).trans
        (chowGroupCongr_heq C _ k x).symm)))
  have h₃ := (bivariantClassCongrBase_cap C G (pullback.snd Δ t₂) hsA₂ h₁₂ (hv' := rfl) d
    (bivariantRestriction C G sX sP Δ hΔ t₂ d hgys Dc)
    (pullback.fst (pullback.snd Δ t₁) (𝟙 T) ≫ pullback.snd Δ t₁) (k - d)
    (chowGroupCongr C (by rw [h₁₂]) (k - d)
      (chowGroupCongr C (Category.assoc (pullback.fst (pullback.snd Δ t₁) (𝟙 T))
        (pullback.snd Δ t₁) (t₁ ≫ sP)).symm (k - d)
        ((bivariantClassCongrBase C G (pullback.snd Δ t₁)
          (pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁).symm rfl (hv' := rfl) d
          (bivariantRestriction C G sX sP Δ hΔ t₁ d hgys Dc)).cap (𝟙 T) k
          (chowGroupCongr C (Category.id_comp (t₁ ≫ sP)).symm k x))))
    _ (chowGroupCongr_heq C _ _ _)).trans
    (bivariantRestriction_cap_heq_chowPushforwardOfIso hgys Dc t₂
      (pullback.fst (pullback.snd Δ t₁) (𝟙 T) ≫ pullback.snd Δ t₁) _
      (pullback.snd Δ t₁ ≫ t₂) (by simp) rfl (Dc.cap t₁ k x) _
      (by rw [Category.assoc, h₁₂]; simp [pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁])
      ((chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
        (h₁.trans (chowPushforwardOfIso_heq _ _ _ rfl
          (by rw [Category.assoc, h₁₂, pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁])
          rfl HEq.rfl))))
      (chowGroupCongr C (by rw [Category.assoc, h₁₂,
        pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁]) (k - d) (Dc.cap t₁ k x))
      (chowGroupCongr_heq C _ _ _))
  have h₄ := (bivariantClassCongrBase_cap C G (pullback.snd Δ t₁)
    (pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁).symm rfl (hv' := rfl) d
    (bivariantRestriction C G sX sP Δ hΔ t₁ d hgys Dc)
    (pullback.fst (pullback.snd Δ t₂) (𝟙 T) ≫ pullback.snd Δ t₂) (k - d)
    (chowGroupCongr C (Category.assoc (pullback.fst (pullback.snd Δ t₂) (𝟙 T))
        (pullback.snd Δ t₂) (t₁ ≫ sP)).symm (k - d)
      ((bivariantClassCongrBase C G (pullback.snd Δ t₂) hsA₂ h₁₂ (hv' := rfl) d
          (bivariantRestriction C G sX sP Δ hΔ t₂ d hgys Dc)).cap (𝟙 T) k
        (chowGroupCongr C (Category.id_comp (t₁ ≫ sP)).symm k x)))
    _ HEq.rfl).trans
    (bivariantRestriction_cap_heq_chowPushforwardOfIso hgys Dc t₁
      (pullback.fst (pullback.snd Δ t₂) (𝟙 T) ≫ pullback.snd Δ t₂) _
      (pullback.snd Δ t₂ ≫ t₁) (by simp) rfl (Dc.cap t₂ k (chowGroupCongr C h₁₂.symm k x)) _
      (by rw [← h₁₂]; simp [pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₂])
      ((chowGroupCongr_heq C _ _ _).trans
        (h₂.trans (chowPushforwardOfIso_heq _ _ _ rfl
          (by rw [Category.assoc, ← h₁₂, pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₂])
          rfl HEq.rfl)))
      (chowGroupCongr C (by rw [Category.assoc, ← h₁₂,
        pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₂]) (k - d)
          (Dc.cap t₂ k (chowGroupCongr C h₁₂.symm k x)))
      (chowGroupCongr_heq C _ _ _))
  have h₅ := chowPushforwardOfIso_heq_comp_of_comp_eq _ (commuteComparisonHom (pullback.snd Δ t₁)
      (pullback.snd Δ t₂) (𝟙 T)) _ rfl _
    (commuteComparisonHom_comp_structureMorphism C (t₁ ≫ sP) _ _ (𝟙 T))
    (by rw [pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₁])
    (sD' := pullback.fst (pullback.snd Δ t₂)
      (pullback.fst (pullback.snd Δ t₁) (𝟙 T) ≫ pullback.snd Δ t₁) ≫ pullback.fst Δ t₂ ≫ sX)
    (by rw [← h₁₂, pullbackSnd_comp_structureMorphism_eq C sX sP Δ hΔ t₂]) rfl _ _ h₄
  have h₆ := (h₅.symm.trans (heq_of_eq hBC)).trans ((chowGroupDegreeEquiv_heq C _ _ _).trans h₃)
  refine eq_of_heq (chowPushforwardOfIso_eq_of_heq _ _ Θ₁ Θ₂ _ _ hΘ₁ hΘ₂ rfl ?_ rfl _ _ h₆)
  have hsw : ((testBaseChangeIso Δ ((pullback.fst (pullback.snd Δ t₂) (𝟙 T) ≫
        pullback.snd Δ t₂) ≫ t₁)
        ((pullback.congrHom (rfl : Δ = Δ) (Category.id_comp t₂).symm).hom ≫
          (pullbackLeftPullbackSndIso Δ t₂ (𝟙 T)).inv) (pullback.snd Δ t₂ ≫ t₁) (by simp)).hom ≫
      (pullbackLeftPullbackSndIso Δ t₁
        (pullback.fst (pullback.snd Δ t₂) (𝟙 T) ≫ pullback.snd Δ t₂)).inv) ≫
      commuteComparisonHom (pullback.snd Δ t₁) (pullback.snd Δ t₂) (𝟙 T) =
      pullbackPullbackSwap Δ t₁ t₂ ≫
        ((testBaseChangeIso Δ ((pullback.fst (pullback.snd Δ t₁) (𝟙 T) ≫
          pullback.snd Δ t₁) ≫ t₂)
          ((pullback.congrHom (rfl : Δ = Δ) (Category.id_comp t₁).symm).hom ≫
            (pullbackLeftPullbackSndIso Δ t₁ (𝟙 T)).inv) (pullback.snd Δ t₁ ≫ t₂) (by simp)).hom ≫
        (pullbackLeftPullbackSndIso Δ t₂
          (pullback.fst (pullback.snd Δ t₁) (𝟙 T) ≫ pullback.snd Δ t₁)).inv) := by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_)
    all_goals simp [testBaseChangeIso_hom_snd_assoc]
  rw [hsw, Category.assoc, IsIso.hom_inv_id_assoc, hΘ]

end TwoCaps

/-! ### The projections of the two substrate identifications -/

section Projections

variable {S X Y Z W : Scheme.{u}} (sX : X ⟶ S) (a : Y ⟶ X) (b : Z ⟶ X) (g : W ⟶ X)

/-- The point of `Y` of the substrate identification at `Δ₁₂`. -/
@[reassoc]
theorem firstPartialDiagonalPullbackIso_hom_fst_fst :
    (firstPartialDiagonalPullbackIso sX a b g).hom ≫
        pullback.fst ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) ≫ pullback.fst a b =
      pullback.snd (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫
        pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) ≫
          pullback.fst (a ≫ sX) (b ≫ sX) := by
  simpa using firstPartialDiagonalPullbackIso_hom_fst sX a b g =≫
    pullback.fst (a ≫ sX) (b ≫ sX)

/-- The point of `Z` of the substrate identification at `Δ₁₂`. -/
@[reassoc]
theorem firstPartialDiagonalPullbackIso_hom_fst_snd :
    (firstPartialDiagonalPullbackIso sX a b g).hom ≫
        pullback.fst ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) ≫ pullback.snd a b =
      pullback.snd (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫
        pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) ≫
          pullback.snd (a ≫ sX) (b ≫ sX) := by
  simpa using firstPartialDiagonalPullbackIso_hom_fst sX a b g =≫
    pullback.snd (a ≫ sX) (b ≫ sX)

/-- The point of `Z` of the substrate identification at `Δ₂₃`. -/
@[reassoc]
theorem secondPartialDiagonalPullbackIso_hom_snd_fst :
    (secondPartialDiagonalPullbackIso sX a b g).hom ≫
        pullback.snd (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) ≫ pullback.fst b g =
      pullback.snd (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) ≫
        pullback.snd (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫
          pullback.fst (b ≫ sX) (g ≫ sX) := by
  simpa using secondPartialDiagonalPullbackIso_hom_snd sX a b g =≫
    pullback.fst (b ≫ sX) (g ≫ sX)

/-- The point of `W` of the substrate identification at `Δ₂₃`. -/
@[reassoc]
theorem secondPartialDiagonalPullbackIso_hom_snd_snd :
    (secondPartialDiagonalPullbackIso sX a b g).hom ≫
        pullback.snd (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) ≫ pullback.snd b g =
      pullback.snd (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) ≫
        pullback.snd (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫
          pullback.snd (b ≫ sX) (g ≫ sX) := by
  simpa using secondPartialDiagonalPullbackIso_hom_snd sX a b g =≫
    pullback.snd (b ≫ sX) (g ≫ sX)

/-- On the pullback of the diagonal along `Δ₁₂`, the points of `Y` and of `Z` lie over the same
point of `X`. -/
@[reassoc]
theorem pullbackDiagonal_firstPartialDiagonalTest_condition :
    pullback.snd (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫
        pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) ≫
          pullback.fst (a ≫ sX) (b ≫ sX) ≫ a =
      pullback.snd (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫
        pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) ≫
          pullback.snd (a ≫ sX) (b ≫ sX) ≫ b := by
  have h := pullback.condition (f := pullback.diagonal sX) (g := firstPartialDiagonalTest sX a b g)
  have h₁ := h =≫ pullback.fst sX sX
  have h₂ := h =≫ pullback.snd sX sX
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id]
    at h₁ h₂
  simp only [pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  rw [← h₁, h₂]

end Projections

/-! ### The two steps of the chain of Stacks 0FC1 -/

/-- The canonical morphism `Y ×_X Z ⟶ Y ×_S Z` is a monomorphism. -/
instance mono_fibreProductToExteriorProduct {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (a : Y ⟶ X)
    (b : Z ⟶ X) : Mono (fibreProductToExteriorProduct sX a b) :=
  ⟨fun x y hxy ↦ pullback.hom_ext
    (by simpa using hxy =≫ pullback.fst (a ≫ sX) (b ≫ sX))
    (by simpa using hxy =≫ pullback.snd (a ≫ sX) (b ≫ sX))⟩

/-- The canonical morphism `Y ×_X Z ⟶ Y ×_S Z` is locally of finite type. -/
instance locallyOfFiniteType_fibreProductToExteriorProduct {S X Y Z : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X)
    [LocallyOfFiniteType b] : LocallyOfFiniteType (fibreProductToExteriorProduct sX a b) := by
  have : LocallyOfFiniteType (fibreProductToExteriorProduct sX a b ≫
      (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))) := by
    rw [fibreProductToExteriorProduct_comp_structure]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))

/-- The composite `Y ×_X Z ⟶ Y ×_S Z ⟶ Y` followed by the structure morphism of `Y` is the
structure morphism of `Y ×_X Z`. -/
private theorem fibreProductToExteriorProduct_comp_fst_structure {S X Y Z : Scheme.{u}}
    (sX : X ⟶ S) (a : Y ⟶ X) (b : Z ⟶ X) :
    fibreProductToExteriorProduct sX a b ≫ (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) =
      (pullback.fst a b ≫ a) ≫ sX := by
  rw [fibreProductToExteriorProduct_comp_structure, Category.assoc]

/-! ### Stacks 0FBP on the triple product, over an arbitrary base -/

section ChainCommute

variable (C : ChowSituation.{u}) (hpp : ProperPushforwardDescends C)
  {X Y Z W : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]
  (g : W ⟶ X) [LocallyOfFiniteType g] (d : ℤ)
  (Dc : BivariantClass C (gysinSystemOfInvertible C) sX
    (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) d)
  (n m l : ℤ)

set_option maxHeartbeats 1000000 in
-- long proof transporting Chow classes along isomorphisms of iterated pullbacks of the triple
-- fibre product, with many `pullback.hom_ext`, `simp` and `chowGroupCongr` steps
/-- **Stacks 0FBP on the triple product, from Stacks 0FBP for the restricted class.** Let `Δ^!` be
a bivariant class of the diagonal of `X ⟶ S`, over any base `S`. If its restriction `Δ₁₂^!`
(Stacks 0F9Z) along the test morphism `Δ₁₂` of the triple product `(Y ×_S Z) ×_S W` commutes
with every bivariant class over the triple product, then
`Stacks.Chow.DiagonalGysinCommuteOnTripleProductOverBase` holds: `Δ^!` capped against `Δ₁₂` and
then against `Δ₂₃` agrees with `Δ^!` capped against `Δ₂₃` and then against `Δ₁₂`. -/
theorem diagonalGysinCommuteOnTripleProduct_of_commutesWithEveryClass
    (hres : (bivariantRestriction C (gysinSystemOfInvertible C) sX (selfProductStructure C sX)
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX)
      (firstPartialDiagonalTest sX a b g) d
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) Dc).CommutesWithEveryClass) :
    DiagonalGysinCommuteOnTripleProductOverBase C (gysinSystemOfInvertible C) hpp sX a b g d Dc
      n m l := by
  intro x
  have h₁₂ : secondPartialDiagonalTestLeft sX a b g ≫
      selfProductStructure C sX =
        firstPartialDiagonalTest sX a b g ≫ selfProductStructure C sX :=
    (secondPartialDiagonalTestLeft_comp_base sX a b g).trans
      (firstPartialDiagonalTest_comp_base sX a b g).symm
  have hm₁ : pullback.snd (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫
      secondPartialDiagonalTestLeft sX a b g =
        (firstPartialDiagonalPullbackIso sX a b g).hom ≫
          exteriorToSelfProduct C sX (pullback.fst a b ≫ a) g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, exteriorToSelfProduct, pullback.lift_fst,
        firstPartialDiagonalPullbackIso_hom_fst_fst_assoc]
      rw [reassoc_of% (tripleProductAssoc_hom_snd_fst (a ≫ sX) (b ≫ sX) (g ≫ sX)),
        ← pullbackDiagonal_firstPartialDiagonalTest_condition]
    · simp only [Category.assoc, exteriorToSelfProduct, pullback.lift_snd,
        firstPartialDiagonalPullbackIso_hom_snd_assoc]
      rw [reassoc_of% (tripleProductAssoc_hom_snd_snd (a ≫ sX) (b ≫ sX) (g ≫ sX))]
  have hP₁ := pullbackSnd_comp_structureMorphism_eq C sX
    (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX)
    (firstPartialDiagonalTest sX a b g)
  have hq₁ : pullback.fst (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫ sX =
      (pullback.snd (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫
        secondPartialDiagonalTestLeft sX a b g) ≫
          selfProductStructure C sX := by
    rw [Category.assoc, h₁₂, hP₁]
  have hq₁' : pullback.fst (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫ sX =
      ((firstPartialDiagonalPullbackIso sX a b g).hom ≫
        exteriorToSelfProduct C sX (pullback.fst a b ≫ a) g) ≫
          selfProductStructure C sX := by
    rw [← hm₁, hq₁]
  have X₁heq := chowPushforwardOfIso_congrHom_cap C
    (gysinSystemOfInvertible C) sX
    (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) d Dc hm₁ (by simp)
    (n + m + l - d)
    (Dc.cap (firstPartialDiagonalTest sX a b g) (n + m + l)
      (chowGroupCongr C (firstPartialDiagonalTest_comp_base sX a b g).symm
        (n + m + l) x))
    hq₁ hq₁'
  have L₁ := Dc.cap_heq_chowPushforwardOfIso
    (exteriorToSelfProduct C sX (pullback.fst a b ≫ a) g)
    (firstPartialDiagonalPullbackIso sX a b g).hom _ rfl (by ring : n + m + l - d = n + m - d + l)
    (Dc.cap (firstPartialDiagonalTest sX a b g) (n + m + l)
      (chowGroupCongr C (firstPartialDiagonalTest_comp_base sX a b g).symm
        (n + m + l) x))
    ((chowGroupCongr C
        (exteriorToSelfProduct_comp_selfProductStructure C sX
          (pullback.fst a b ≫ a) g).symm (n + m - d + l)).toAddMonoidHom
      ((chowPushforwardOfIso C
          (pullback.fst (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫ sX)
          (pullback.fst ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) ≫ ((pullback.fst a b ≫ a) ≫ sX))
          (firstPartialDiagonalPullbackIso sX a b g).hom
          (firstPartialDiagonalPullbackIso_hom_comp_base sX a b g) (n + m - d + l))
        ((chowGroupDegreeEquiv C
            (pullback.fst (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫ sX)
            (by ring : n + m + l - d = n + m - d + l))
          ((Dc.cap (firstPartialDiagonalTest sX a b g) (n + m + l))
            ((chowGroupCongr C
                (firstPartialDiagonalTest_comp_base sX a b g).symm
                (n + m + l)).toAddMonoidHom x)))))
    (by rw [exteriorToSelfProduct_comp_selfProductStructure]
        exact firstPartialDiagonalPullbackIso_hom_comp_base sX a b g)
    ((chowGroupCongr_heq _ _ _ _).trans (chowPushforwardOfIso_heq _ _ _ rfl
      (exteriorToSelfProduct_comp_selfProductStructure _ _ _ _).symm (by ring)
      (chowGroupDegreeEquiv_heq _ _ _ _)))
    (chowGroupCongr C hq₁' (n + m + l - d)
      (Dc.cap (firstPartialDiagonalTest sX a b g) (n + m + l)
        (chowGroupCongr C (firstPartialDiagonalTest_comp_base sX a b g).symm
          (n + m + l) x)))
    (chowGroupCongr_heq _ _ _ _)
  have L₂ := L₁.trans (heq_of_eq ((congrArg _ X₁heq.symm).trans
    (chowPushforwardOfIso_comp_apply _ _ _ _ _ _ _ _ _ _)))
  have L₃ := chowPushforwardOfIso_heq_comp_of_comp_eq _
    (pullbackDiagonalMapIdIso (pullback.fst a b ≫ a) g sX).hom _ rfl _
    (pullbackDiagonalMapIdIso_hom_comp_structure C sX
      (pullback.fst a b ≫ a) g) rfl rfl (by ring) _ _ L₂
  have L₄ := chowPushforwardOfIso_heq_comp_of_comp_eq _ (tripleProductAssoc a b g).hom _ rfl _
    (tripleProductAssoc_hom_comp_structureMorphism C sX a b g) rfl rfl
    (by ring) _ _ L₃
  rw [properChowPushforward_eq_chowPushforwardOfIso, properChowPushforward_eq_chowPushforwardOfIso,
    properChowPushforward_eq_chowPushforwardOfIso]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (L₄.trans ?_))
  have hP₂ := pullbackSnd_comp_structureMorphism_eq C sX
    (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX)
    (secondPartialDiagonalTestLeft sX a b g)
  have R₁ := Dc.cap_heq_chowPushforwardOfIso (secondPartialDiagonalTest sX a b g)
    (tripleProductAssoc (a ≫ sX) (b ≫ sX) (g ≫ sX)).hom (secondPartialDiagonalTestLeft sX a b g)
    rfl (add_assoc n m l) x
    ((chowGroupCongr C
        (secondPartialDiagonalTest_comp_base sX a b g).symm (n + (m + l))).toAddMonoidHom
      ((chowGroupDegreeEquiv C
          (pullback.fst (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫ (a ≫ sX))
          (add_assoc n m l))
        ((chowPushforwardOfIso C
            (pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))
                (g ≫ sX) ≫ (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)))
            (pullback.fst (a ≫ sX)
              (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫ (a ≫ sX))
            (tripleProductAssoc (a ≫ sX) (b ≫ sX) (g ≫ sX)).hom
            (tripleProductAssoc_hom_comp_base (a ≫ sX) (b ≫ sX) (g ≫ sX))
            (n + m + l))
          x)))
    (by rw [secondPartialDiagonalTest_comp_base]
        exact tripleProductAssoc_hom_comp_base (a ≫ sX) (b ≫ sX) (g ≫ sX))
    ((chowGroupCongr_heq _ _ _ _).trans ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      (chowPushforwardOfIso_heq _ _ _ rfl (secondPartialDiagonalTest_comp_base sX a b g).symm
        rfl HEq.rfl)))
    (chowGroupCongr C h₁₂.symm (n + m + l)
      (chowGroupCongr C (firstPartialDiagonalTest_comp_base sX a b g).symm
        (n + m + l) x))
    ((chowGroupCongr_heq _ _ _ _).trans (chowGroupCongr_heq _ _ _ _))
  have R₂ := chowPushforwardOfIso_heq_comp_of_comp_eq _
    (secondPartialDiagonalPullbackIso sX a b g).hom _ rfl (by simp)
    (secondPartialDiagonalPullbackIso_hom_comp_base sX a b g) rfl rfl
    (by ring : n + m + l - d = n + (m + l - d)) _ _
    ((chowGroupDegreeEquiv_heq _ _ (by ring : n + (m + l) - d = n + (m + l - d)) _).trans R₁)
  have hm₂ : pullback.snd (pullback.diagonal sX) (secondPartialDiagonalTestLeft sX a b g) ≫
      firstPartialDiagonalTest sX a b g =
        ((testBaseChangeIso (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g)
          (tripleProductAssoc (a ≫ sX) (b ≫ sX) (g ≫ sX)).hom
          (secondPartialDiagonalTestLeft sX a b g) rfl).hom ≫
          (secondPartialDiagonalPullbackIso sX a b g).hom) ≫
        exteriorToSelfProduct C sX a (pullback.fst b g ≫ b) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, exteriorToSelfProduct, pullback.lift_fst,
        secondPartialDiagonalPullbackIso_hom_fst_assoc, testBaseChangeIso_hom_snd_assoc]
      rw [reassoc_of% (tripleProductAssoc_hom_fst (a ≫ sX) (b ≫ sX) (g ≫ sX))]
    · simp only [Category.assoc, exteriorToSelfProduct, pullback.lift_snd,
        secondPartialDiagonalPullbackIso_hom_snd_fst_assoc, testBaseChangeIso_hom_snd_assoc]
      rw [reassoc_of% (tripleProductAssoc_hom_snd_fst (a ≫ sX) (b ≫ sX) (g ≫ sX))]
  have hq₂ : pullback.fst (pullback.diagonal sX) (secondPartialDiagonalTestLeft sX a b g) ≫ sX =
      (pullback.snd (pullback.diagonal sX) (secondPartialDiagonalTestLeft sX a b g) ≫
        firstPartialDiagonalTest sX a b g) ≫ selfProductStructure C sX := by
    rw [Category.assoc, ← h₁₂, hP₂]
  have hq₂' : pullback.fst (pullback.diagonal sX) (secondPartialDiagonalTestLeft sX a b g) ≫ sX =
      (((testBaseChangeIso (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g)
          (tripleProductAssoc (a ≫ sX) (b ≫ sX) (g ≫ sX)).hom
          (secondPartialDiagonalTestLeft sX a b g) rfl).hom ≫
          (secondPartialDiagonalPullbackIso sX a b g).hom) ≫
        exteriorToSelfProduct C sX a (pullback.fst b g ≫ b)) ≫
          selfProductStructure C sX := by
    rw [← hm₂, hq₂]
  have X₂heq := chowPushforwardOfIso_congrHom_cap C
    (gysinSystemOfInvertible C) sX
    (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) d Dc hm₂ (by simp)
    (n + m + l - d)
    (Dc.cap (secondPartialDiagonalTestLeft sX a b g) (n + m + l)
      (chowGroupCongr C h₁₂.symm (n + m + l)
        (chowGroupCongr C (firstPartialDiagonalTest_comp_base sX a b g).symm
          (n + m + l) x))) hq₂ hq₂'
  have R₃ := Dc.cap_heq_chowPushforwardOfIso
    (exteriorToSelfProduct C sX a (pullback.fst b g ≫ b))
    ((testBaseChangeIso (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g)
          (tripleProductAssoc (a ≫ sX) (b ≫ sX) (g ≫ sX)).hom
          (secondPartialDiagonalTestLeft sX a b g) rfl).hom ≫
          (secondPartialDiagonalPullbackIso sX a b g).hom) _ rfl
    (by ring : n + m + l - d = n + (m + l - d))
    (Dc.cap (secondPartialDiagonalTestLeft sX a b g) (n + m + l)
      (chowGroupCongr C h₁₂.symm (n + m + l)
        (chowGroupCongr C (firstPartialDiagonalTest_comp_base sX a b g).symm
          (n + m + l) x)))
    ((chowGroupCongr C
        (exteriorToSelfProduct_comp_selfProductStructure C sX a
          (pullback.fst b g ≫ b)).symm (n + (m + l - d))).toAddMonoidHom
      ((chowPushforwardOfIso C
          (pullback.fst (pullback.diagonal sX)
            (secondPartialDiagonalTest sX a b g) ≫ sX)
          (pullback.fst (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) ≫ (a ≫ sX))
          (secondPartialDiagonalPullbackIso sX a b g).hom
          (secondPartialDiagonalPullbackIso_hom_comp_base sX a b g) (n + (m + l - d)))
        ((chowGroupDegreeEquiv C
            (pullback.fst (pullback.diagonal sX)
              (secondPartialDiagonalTest sX a b g) ≫ sX)
            (by ring : n + (m + l) - d = n + (m + l - d)))
          ((Dc.cap (secondPartialDiagonalTest sX a b g) (n + (m + l)))
            ((chowGroupCongr C
                (secondPartialDiagonalTest_comp_base sX a b g).symm
                (n + (m + l))).toAddMonoidHom
              ((chowGroupDegreeEquiv C
                  (pullback.fst (a ≫ sX)
                    (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫ (a ≫ sX))
                  (add_assoc n m l))
                ((chowPushforwardOfIso C
                    (pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))
                        (g ≫ sX) ≫ (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)))
                    (pullback.fst (a ≫ sX)
                      (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫ (a ≫ sX))
                    (tripleProductAssoc (a ≫ sX) (b ≫ sX) (g ≫ sX)).hom
                    (tripleProductAssoc_hom_comp_base (a ≫ sX) (b ≫ sX) (g ≫ sX))
                    (n + m + l))
                  x)))))))
    (by rw [exteriorToSelfProduct_comp_selfProductStructure, Category.assoc,
          secondPartialDiagonalPullbackIso_hom_comp_base]
        simp)
    ((chowGroupCongr_heq _ _ _ _).trans (R₂.trans (chowPushforwardOfIso_heq _ _ _ rfl
      (exteriorToSelfProduct_comp_selfProductStructure _ _ _ _).symm rfl HEq.rfl)))
    (chowGroupCongr C hq₂' (n + m + l - d)
      (Dc.cap (secondPartialDiagonalTestLeft sX a b g) (n + m + l)
        (chowGroupCongr C h₁₂.symm (n + m + l)
          (chowGroupCongr C (firstPartialDiagonalTest_comp_base sX a b g).symm
            (n + m + l) x))))
    (chowGroupCongr_heq _ _ _ _)
  have R₄ := R₃.trans (heq_of_eq ((congrArg _ X₂heq.symm).trans
    (chowPushforwardOfIso_comp_apply _ _ _ _ _ _ _ _ _ _)))
  have R₅ := chowPushforwardOfIso_heq_comp_of_comp_eq _
    (pullbackDiagonalMapIdIso a (pullback.fst b g ≫ b) sX).hom _ rfl _
    (pullbackDiagonalMapIdIso_hom_comp_structure C sX a
      (pullback.fst b g ≫ b)) rfl rfl (by ring) _ _ R₄
  refine (heq_of_eq (chowPushforwardOfIso_cap_cap_eq_of_bivariantCommute
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) Dc _ _ h₁₂
    (hres _ _ _) _ _ _ _ _ ?_ (n + m + l)
    (chowGroupCongr C (firstPartialDiagonalTest_comp_base sX a b g).symm
      (n + m + l) x))).symm.trans R₅.symm
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;>
    simp only [Category.assoc, tripleProductAssoc_hom_fst, tripleProductAssoc_hom_snd_fst,
      tripleProductAssoc_hom_snd_snd, pullbackDiagonalMapIdIso_hom_fst,
      pullbackDiagonalMapIdIso_hom_fst_assoc, pullbackDiagonalMapIdIso_hom_snd,
      testBaseChangeIso_hom_snd_assoc, pullback.congrHom_hom, pullback.lift_snd_assoc,
      Category.comp_id, firstPartialDiagonalPullbackIso_hom_fst_fst,
      firstPartialDiagonalPullbackIso_hom_fst_snd, firstPartialDiagonalPullbackIso_hom_snd,
      pullbackPullbackSwap_snd_snd_assoc, secondPartialDiagonalPullbackIso_hom_fst,
      secondPartialDiagonalPullbackIso_hom_snd_fst, secondPartialDiagonalPullbackIso_hom_snd_snd,
      pullback.map]

end ChainCommute

section Chain

variable (k : Type u) [Field k] (hpp : ProperPushforwardDescends (fieldChowSituation k))
  {X Y Z W : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]
  (g : W ⟶ X) [LocallyOfFiniteType g] (d : ℤ)
  (Dc : BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k)) sX
    (selfProductStructure (fieldChowSituation k) sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) d)
  (n m l : ℤ)

/-- **The penultimate step of Stacks 0FC1, `Δ₂₃^!(α × η) = α × Δ^!(η)`**, for every bivariant
class `Δ^!` of the diagonal of `X` over a field: `Stacks.Chow.CommutesDiagonalCapExteriorSecond`
holds. The class `Δ₂₃^!` is the restriction of `Δ^!` along `Z ×_k W ⟶ X ×_k X` read on
`Z ×_X W`. -/
theorem commutesDiagonalCapExteriorSecond_of_field :
    CommutesDiagonalCapExteriorSecond k (gysinSystemOfInvertible (fieldChowSituation k)) hpp sX
      a b g d Dc n m l := by
  intro alpha eta
  have key := chowExteriorProduct_tmul_cap_of_field k (a ≫ sX) sX
    (selfProductStructure (fieldChowSituation k) sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) d Dc
    (exteriorToSelfProduct (fieldChowSituation k) sX b g)
    (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX))
    (exteriorToSelfProduct_comp_selfProductStructure (fieldChowSituation k) sX b g)
    ((pullback.fst b g ≫ b) ≫ sX) (fibreProductToExteriorProduct sX b g)
    (fibreProductToExteriorProduct_comp_fst_structure sX b g)
    (pullbackDiagonalMapIdIso b g sX)
    (pullbackDiagonalMapIdIso_hom_comp_fibreProductToExteriorProduct sX b g) n (m + l) alpha eta
  rw [properChowPushforward_eq_chowPushforwardOfIso, chowGroupCongr_chowPushforwardOfIso_target]
  refine key.trans ?_
  refine chowPushforwardOfIso_congr_apply _ _ _ _ _ ?_ _ _ _ _
  apply pullback.hom_ext
  · rw [secondPartialDiagonalPullbackIso_hom_fst]
    simp
  · rw [← cancel_mono (fibreProductToExteriorProduct sX b g)]
    simp only [Category.assoc, secondPartialDiagonalPullbackIso_hom_snd,
      exteriorCapIso_hom_snd_assoc]
    rw [pullback.condition (f := fibreProductToExteriorProduct sX b g)
      (g := pullback.snd (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)))]
    simp

/-- **The first step of Stacks 0FC1, `Δ^!(ξ) × γ = Δ₁₂^!(ξ × γ)`**, for every bivariant class
`Δ^!` of the diagonal of `X` over a field: `Stacks.Chow.CommutesDiagonalCapExteriorFirst` holds.
The class `Δ₁₂^!` is the restriction of `Δ^!` along `Y ×_k Z ⟶ X ×_k X`, read on `Y ×_X Z`. -/
theorem commutesDiagonalCapExteriorFirst_of_field :
    CommutesDiagonalCapExteriorFirst k (gysinSystemOfInvertible (fieldChowSituation k)) hpp sX
      a b g d Dc n m l := by
  intro xi gamma
  have key := chowExteriorProduct_cap_tmul_of_field k (g ≫ sX) sX
    (selfProductStructure (fieldChowSituation k) sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) d Dc
    (exteriorToSelfProduct (fieldChowSituation k) sX a b)
    (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))
    (exteriorToSelfProduct_comp_selfProductStructure (fieldChowSituation k) sX a b)
    ((pullback.fst a b ≫ a) ≫ sX) (fibreProductToExteriorProduct sX a b)
    (fibreProductToExteriorProduct_comp_fst_structure sX a b)
    (pullbackDiagonalMapIdIso a b sX)
    (pullbackDiagonalMapIdIso_hom_comp_fibreProductToExteriorProduct sX a b) (n + m) l xi gamma
  rw [properChowPushforward_eq_chowPushforwardOfIso, chowGroupCongr_chowPushforwardOfIso_target]
  refine key.trans ?_
  refine chowPushforwardOfIso_congr_apply _ _ _ _ _ ?_ _ _ _ _
  apply pullback.hom_ext
  · rw [← cancel_mono (fibreProductToExteriorProduct sX a b)]
    simp only [Category.assoc, firstPartialDiagonalPullbackIso_hom_fst,
      exteriorCapFstIso_hom_fst_assoc]
    rw [pullback.condition (f := fibreProductToExteriorProduct sX a b)
      (g := pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX))]
    simp
  · rw [firstPartialDiagonalPullbackIso_hom_snd]
    simp

/-- **Stacks 0FC1 over a field, from Stacks 0FBP.** Let `k` be a field, `X` locally of finite
type over `k` with a bivariant class `Δ^!` of degree `d` of its diagonal, and `Y`, `Z`, `W`
locally of finite type over `X`. If `Δ^!` capped against the two factorwise diagonals of the
triple product commutes with itself,
`Stacks.Chow.DiagonalGysinCommuteOnTripleProductOverBase`, then

`(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`. -/
theorem isAssociativeIntersectionProduct_of_field
    (hcommute : DiagonalGysinCommuteOnTripleProductOverBase (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) hpp sX a b g d Dc n m l) :
    IsAssociativeIntersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX a b g d Dc n m l hpp :=
  isAssociativeIntersectionProduct k (gysinSystemOfInvertible (fieldChowSituation k))
    hpp sX a b g d Dc n m l
    (commutesDiagonalCapExteriorFirst_of_field k hpp sX a b g d Dc n m l)
    (commutesDiagonalCapExteriorSecond_of_field k hpp sX a b g d Dc n m l) hcommute

/-- **Stacks 0FC1 over a field, from Stacks 0FBP for the restricted diagonal class.** Let `k` be
a field, `X` locally of finite type over `k` with a bivariant class `Δ^!` of degree `d` of its
diagonal, and `Y`, `Z`, `W` locally of finite type over `X`. If the restriction of `Δ^!` along
the test morphism `Δ₁₂` of `(Y ×_k Z) ×_k W` commutes with every bivariant class over it, then

`(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`. -/
theorem isAssociativeIntersectionProduct_of_field_of_commutesWithEveryClass
    (hres : (bivariantRestriction (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX
      (selfProductStructure (fieldChowSituation k) sX) (pullback.diagonal sX)
      (diagonal_comp_selfProductStructure (fieldChowSituation k) sX)
      (firstPartialDiagonalTest sX a b g) d
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso (fieldChowSituation k))
      Dc).CommutesWithEveryClass) :
    IsAssociativeIntersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX a b g d Dc n m l hpp :=
  isAssociativeIntersectionProduct_of_field k hpp sX a b g d Dc n m l
    (diagonalGysinCommuteOnTripleProduct_of_commutesWithEveryClass _ hpp sX a b g d Dc n m l hres)

end Chain

/-! ### Restriction of classes commuting with every class -/

section RestrictionCongr

variable {C : ChowSituation.{u}} {G : GysinSystem C} (hgys : G.IsNaturalUnderBaseChangeIso)
  {X Y Y' : Scheme.{u}} (h : Y' ⟶ Y) [LocallyOfFiniteType h]

/-- Whether the restriction (Stacks 0F9Z) of a class commutes with every class does not depend on
the structure morphisms of its source and target. -/
theorem commutesWithEveryClass_bivariantRestriction_bivariantClassCongrBase_iff
    {sX sX' : X ⟶ C.S} [LocallyOfFiniteType sX] [LocallyOfFiniteType sX']
    {sY sY' : Y ⟶ C.S} [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] {f : X ⟶ Y}
    [LocallyOfFiniteType f] (e : sX = sX') (e' : sY = sY') {hf : f ≫ sY = sX}
    {hf' : f ≫ sY' = sX'} {p : ℤ} (c : BivariantClass C G sX sY f hf p) :
    (bivariantRestriction C G sX' sY' f hf' h p hgys
        (bivariantClassCongrBase C G f e e' p c)).CommutesWithEveryClass ↔
      (bivariantRestriction C G sX sY f hf h p hgys c).CommutesWithEveryClass := by
  subst e e'
  rfl

/-- Whether the restriction (Stacks 0F9Z) of a class commutes with every class does not depend on
how its degree is written. -/
theorem commutesWithEveryClass_bivariantRestriction_bivariantClassDegreeCongr_iff
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p p' : ℤ} (e : p = p')
    (c : BivariantClass C G sX sY f hf p) :
    (bivariantRestriction C G sX sY f hf h p' hgys
        (bivariantClassDegreeCongr C G sX sY f hf e c)).CommutesWithEveryClass ↔
      (bivariantRestriction C G sX sY f hf h p hgys c).CommutesWithEveryClass := by
  subst e
  rfl

/-- Whether the restriction (Stacks 0F9Z) of a class commutes with every class does not depend on
the spelling of the morphism the class is read for. -/
theorem commutesWithEveryClass_bivariantRestriction_congrHom_iff
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f'] {hf : f ≫ sY = sX}
    (e : f = f') (hf' : f' ≫ sY = sX) {p : ℤ} (c : BivariantClass C G sX sY f hf p) :
    (bivariantRestriction C G sX sY f' hf' h p hgys (c.congrHom e hf')).CommutesWithEveryClass ↔
      (bivariantRestriction C G sX sY f hf h p hgys c).CommutesWithEveryClass := by
  subst e
  rfl

end RestrictionCongr

/-- **The restriction of `Δ^!` along any morphism commutes with every class.** Let `g : Y ⟶ Z` be
smooth of constant relative dimension `d` and `h : T ⟶ Y ×_Z Y` locally of finite type. The
restriction (Stacks 0F9Z) along `h` of the Gysin class `Δ^! = c(Y ⟶ U, 𝒩) ∘ ι^*` of the diagonal
commutes with every bivariant class over `T`. -/
theorem diagonalGysinClass_bivariantRestriction_commutesWithEveryClass (C : ChowSituation.{u})
    {Y Z T : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : Y ⟶ Z) [Smooth g] {d : ℕ}
    (hd : RelativeDimension g d) (h : T ⟶ pullback g g) [LocallyOfFiniteType h] :
    (bivariantRestriction C (gysinSystemOfInvertible C)
      (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)) (pullback.fst g g ≫ sY)
      (pullback.diagonal g) rfl h d (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (diagonalGysinClass C sY g hd)).CommutesWithEveryClass := by
  rw [diagonalGysinClass_eq_bivariantCompositeOfInvertible,
    commutesWithEveryClass_bivariantRestriction_bivariantClassDegreeCongr_iff,
    commutesWithEveryClass_bivariantRestriction_congrHom_iff,
    commutesWithEveryClass_bivariantRestriction_bivariantClassCongrBase_iff,
    bivariantRestriction_bivariantCompositeOfInvertible]
  refine BivariantClass.CommutesWithEveryClass.bivariantTransport _ _ ?_
  refine BivariantClass.CommutesWithEveryClass.bivariantCompositeOfInvertible ?_ ?_
  · have := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd
    rw [bivariantRestriction_virtualNormalGysinClass]
    exact virtualNormalBundleClass_commutesWithEveryClass _ _ _ _ _ _ _
  · rw [bivariantRestriction_flatPullbackBivariantClass]
    exact commutesWithEveryClass_flatPullbackBivariantClass _ _ _ (flatPullbackDescends _) _
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _)

section Canonical

variable (k : Type u) [Field k] (hpp : ProperPushforwardDescends (fieldChowSituation k))
  {X Y Z W : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
  [Smooth sX] {d : ℕ} (hd : RelativeDimension sX d)
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]
  (g : W ⟶ X) [LocallyOfFiniteType g] (n m l : ℤ)

/-- **Stacks 0FC1 for the Gysin class of the diagonal, from Stacks 0FBP for its restriction.**
Let `k` be a field, `X` smooth over `k` of constant relative dimension `d`, and `Y`, `Z`, `W`
locally of finite type over `X`. Form the intersection product of Stacks 0FC0 with the Gysin class
`Δ^! ∈ A^d(X ⟶ X ×_k X)` of the diagonal of Stacks 0FBR, `Stacks.Chow.diagonalGysinClass`, read
with its source over `k` through `s_X`. If the restriction of `Δ^!` along the test morphism `Δ₁₂`
of `(Y ×_k Z) ×_k W` commutes with every bivariant class over it, then

`(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`. -/
theorem isAssociativeIntersectionProduct_diagonalGysinClass_of_commutesWithEveryClass
    (hres : (bivariantRestriction (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX
      (selfProductStructure (fieldChowSituation k) sX) (pullback.diagonal sX)
      (diagonal_comp_selfProductStructure (fieldChowSituation k) sX)
      (firstPartialDiagonalTest sX a b g) d
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso (fieldChowSituation k))
      (bivariantClassCongrBase (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) (pullback.diagonal sX)
        (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) rfl (d : ℤ)
        (diagonalGysinClass (fieldChowSituation k) sX sX hd))).CommutesWithEveryClass) :
    IsAssociativeIntersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX a b g d
      (bivariantClassCongrBase (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) (pullback.diagonal sX)
        (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) rfl (d : ℤ)
        (diagonalGysinClass (fieldChowSituation k) sX sX hd)) n m l hpp :=
  isAssociativeIntersectionProduct_of_field_of_commutesWithEveryClass k hpp sX a b g d _ n m l
    hres

/-- **Stacks 0FC1 for `X` of constant dimension.** Let `k` be a field, `X` smooth over `k` of
constant relative dimension `d`, and `Y`, `Z`, `W` locally of finite type over `X`. Form the
intersection product of Stacks 0FC0 with the Gysin class `Δ^! ∈ A^d(X ⟶ X ×_k X)` of the diagonal
of Stacks 0FBR, `Stacks.Chow.diagonalGysinClass`, read with its source over `k` through `s_X`.
Then

`(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`,

read through the associator of the triple fibre product over `X` and the matching of the two
degrees. -/
theorem isAssociativeIntersectionProduct_canonical_of_relativeDimension :
    IsAssociativeIntersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX a b g d
      (bivariantClassCongrBase (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) (pullback.diagonal sX)
        (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) rfl (d : ℤ)
        (diagonalGysinClass (fieldChowSituation k) sX sX hd)) n m l
      (properPushforwardDescends (fieldChowSituation k)) :=
  isAssociativeIntersectionProduct_diagonalGysinClass_of_commutesWithEveryClass k
    (properPushforwardDescends (fieldChowSituation k)) sX hd a b g n m l
    ((commutesWithEveryClass_bivariantRestriction_bivariantClassCongrBase_iff _ _ _ _ _).2
      (diagonalGysinClass_bivariantRestriction_commutesWithEveryClass _ sX sX hd _))

end Canonical

/-! ### The intersection product for `X` of arbitrary dimension -/

section DimParts

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase)

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Smooth sX]
  (Δ : ∀ d : ℕ, BivariantClass C G (partBase sX d) (selfProductStructure C (partBase sX d))
    (pullback.diagonal (partBase sX d)) (diagonal_comp_selfProductStructure C (partBase sX d))
    (d : ℤ))

/-- **The intersection product of Stacks 0FC0 for `X` of arbitrary dimension**, on classes given
part by part. Let `X` be smooth over the base, with parts `X_d` of relative dimension `d`
(`Stacks.WeilCohomology.dimPart`), and let `Δ_d^! ∈ A^d(X_d ⟶ X_d ×_S X_d)` be classes of the
diagonals of the parts. For schemes `T_d`, `T'_d` over `X_d` and classes `x_d ∈ CH_{k_d}(T_d)`,
`y_d ∈ CH_{k'_d}(T'_d)`, the product is `(x · y)_d = Δ_d^!(x_d × y_d) ∈ CH_{k_d+k'_d-d}(T_d ×_{X_d}
T'_d)`: "in general we can decompose into the parts lying over the open and closed subschemes of
`X` where `X` has a given dimension". -/
def dimPartOverIntersectionProduct {T T' : ℕ → Scheme.{u}}
    (t : ∀ d, T d ⟶ (dimPart sX d).toScheme) [∀ d, LocallyOfFiniteType (t d)]
    (t' : ∀ d, T' d ⟶ (dimPart sX d).toScheme)
    [∀ d, LocallyOfFiniteType (t' d)] (k k' : ℕ → ℤ)
    (x : ∀ d, chowGroup C (t d ≫ partBase sX d) (k d))
    (y : ∀ d, chowGroup C (t' d ≫ partBase sX d) (k' d)) (d : ℕ) :
    chowGroup C (pullback.fst (t d) (t' d) ≫ (t d ≫ partBase sX d)) (k d + k' d - d) :=
  intersectionProduct C hδ G (partBase sX d) (t d) (t' d) d (Δ d) (k d) (k' d)
    (TensorProduct.tmul ℤ (x d) (y d))

end DimParts

section CanonicalDimParts

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase)

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [Smooth sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]
  (g : W ⟶ X) [LocallyOfFiniteType g] (n m l : ℤ)

/-- The Gysin classes `Δ_d^! ∈ A^d(X_d ⟶ X_d ×_k X_d)` of the diagonals of the parts `X_d` of `X`
of dimension `d` (Stacks 0FBR), read with their sources over `k` through `X_d ⟶ Spec k`. -/
abbrev dimPartDiagonalGysinClass (d : ℕ) :
    BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
      (partBase sX d) (selfProductStructure (fieldChowSituation k) (partBase sX d))
      (pullback.diagonal (partBase sX d))
      (diagonal_comp_selfProductStructure (fieldChowSituation k) (partBase sX d)) (d : ℤ) :=
  bivariantClassCongrBase (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
    (pullback.diagonal (partBase sX d))
    (diagonal_comp_selfProductStructure (fieldChowSituation k) (partBase sX d)) rfl (d : ℤ)
    (diagonalGysinClass (fieldChowSituation k) (partBase sX d) (partBase sX d)
      (relativeDimension_partBase sX d))

/-- The intersection product `α · β` of Stacks 0FC0 over `X` smooth over `k` of arbitrary
dimension, on part families: `Stacks.Chow.dimPartOverIntersectionProduct` with the Gysin classes of
the diagonals of the parts. -/
local notation "μ" => dimPartOverIntersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
  (gysinSystemOfInvertible (fieldChowSituation k)) sX (dimPartDiagonalGysinClass k sX)

/-- A class of `CH_n(Y)` as the family of its restrictions to the parts `Y_d = a⁻¹(X_d)`. -/
local notation "res[" a ", " n ", " α "]" =>
  fun d : ℕ ↦ chowGroupDimPartOver (fieldChowSituation k) sX a d n α

/-- **Stacks 0FC1.** Let `k` be a field, `X` smooth over `k` of arbitrary, not necessarily
constant, dimension, and `Y`, `Z`, `W` locally of finite type over `X`. The intersection product
`α · β = Δ^!(α × β)` of Stacks 0FC0 is formed with the Gysin class of the diagonal of Stacks 0FBR
part by part, over the open and closed parts `X_d` of `X` of dimension `d`
(`Stacks.Chow.dimPartOverIntersectionProduct`): for `α ∈ CH_n(Y)` and `β ∈ CH_m(Z)`, `α · β` has
component `α|_{Y_d} · β|_{Z_d} ∈ CH_{n+m-d}(Y_d ×_{X_d} Z_d)` over `X_d`, where
`Y_d = a⁻¹(X_d)`, `Z_d = b⁻¹(X_d)` are the parts of `Y` and `Z` over `X_d`. Then for
`γ ∈ CH_l(W)`

`(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`,

component by component, read through the associator of the triple fibre product over `X_d` and
the matching of the degrees `(n + m - d) + l - d = n + (m + l - d) - d`. -/
@[stacks 0FC1 "the whole statement: associativity (α·β)·γ = α·(β·γ) in CH_*(Y ×_X Z ×_X W) of \
the Stacks 0FC0 product for X smooth over a field of arbitrary dimension, Y, Z, W locally of \
finite type over X and arbitrary α, β, γ, the product Δ^!(α × β) formed with the Gysin class of \
the diagonal on the open and closed parts of X of constant dimension, as in Section 0FC0"]
theorem isAssociativeIntersectionProduct_canonical
    (α : chowGroup (fieldChowSituation k) (a ≫ sX) n)
    (β : chowGroup (fieldChowSituation k) (b ≫ sX) m)
    (γ : chowGroup (fieldChowSituation k) (g ≫ sX) l) :
    (fun d : ℕ ↦ chowGroupDegreeEquiv (fieldChowSituation k)
        (pullback.fst (dimPartOverHom sX a d)
            (pullback.fst (dimPartOverHom sX b d) (dimPartOverHom sX g d) ≫
              dimPartOverHom sX b d) ≫
          (dimPartOverHom sX a d ≫ partBase sX d))
        (intersectionProductAssocDegree n m l d)
        (properChowPushforward (fieldChowSituation k)
          (pullback.fst (pullback.fst (dimPartOverHom sX a d) (dimPartOverHom sX b d) ≫
              dimPartOverHom sX a d) (dimPartOverHom sX g d) ≫
            ((pullback.fst (dimPartOverHom sX a d) (dimPartOverHom sX b d) ≫
              dimPartOverHom sX a d) ≫ partBase sX d))
          (pullback.fst (dimPartOverHom sX a d)
              (pullback.fst (dimPartOverHom sX b d) (dimPartOverHom sX g d) ≫
                dimPartOverHom sX b d) ≫
            (dimPartOverHom sX a d ≫ partBase sX d))
          (tripleProductAssoc (dimPartOverHom sX a d) (dimPartOverHom sX b d)
            (dimPartOverHom sX g d)).hom
          (tripleProductAssoc_hom_comp_structureMorphism (fieldChowSituation k) (partBase sX d)
            (dimPartOverHom sX a d) (dimPartOverHom sX b d) (dimPartOverHom sX g d))
          ((n + m - d) + l - d) (properPushforwardDescends (fieldChowSituation k) _ _ _ _ _)
          (μ (fun d ↦ pullback.fst (dimPartOverHom sX a d) (dimPartOverHom sX b d) ≫
              dimPartOverHom sX a d) (fun d ↦ dimPartOverHom sX g d)
            (fun d : ℕ ↦ n + m - d) (fun _ ↦ l)
            (fun d ↦ chowGroupCongr (fieldChowSituation k)
              (Category.assoc (pullback.fst (dimPartOverHom sX a d) (dimPartOverHom sX b d))
                (dimPartOverHom sX a d) (partBase sX d)).symm (n + m - d)
              (μ (fun d ↦ dimPartOverHom sX a d) (fun d ↦ dimPartOverHom sX b d) (fun _ ↦ n)
                (fun _ ↦ m) res[a, n, α] res[b, m, β] d))
            res[g, l, γ] d))) =
      μ (fun d ↦ dimPartOverHom sX a d)
        (fun d ↦ pullback.fst (dimPartOverHom sX b d) (dimPartOverHom sX g d) ≫
          dimPartOverHom sX b d) (fun _ ↦ n) (fun d : ℕ ↦ m + l - d) res[a, n, α]
        (fun d ↦ chowGroupCongr (fieldChowSituation k)
          (Category.assoc (pullback.fst (dimPartOverHom sX b d) (dimPartOverHom sX g d))
            (dimPartOverHom sX b d) (partBase sX d)).symm (m + l - d)
          (μ (fun d ↦ dimPartOverHom sX b d) (fun d ↦ dimPartOverHom sX g d) (fun _ ↦ m)
            (fun _ ↦ l) res[b, m, β] res[g, l, γ] d)) := by
  funext d
  exact isAssociativeIntersectionProduct_canonical_of_relativeDimension k (partBase sX d)
    (relativeDimension_partBase sX d) (dimPartOverHom sX a d) (dimPartOverHom sX b d)
    (dimPartOverHom sX g d) n m l _ _ _

end CanonicalDimParts

end Stacks.Chow

end
