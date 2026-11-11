module

public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.RelativeDimension.Defs
public import StacksFrontier.RingTheory.Syntomic.BaseChange
import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
import StacksFrontier.RingTheory.CompleteIntersection.Basic
import StacksFrontier.RingTheory.RelativeDimension.Basic
import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity

/-!
# Relative global complete intersections

A presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)` of an `R`-algebra `S` by `n` variables and `c`
relations is a relative global complete intersection when every nonempty fibre of
`Spec(S) → Spec(R)` has dimension `n - c`. This file proves that the base changed presentation
`R'[x_1, …, x_n]/(f_1, …, f_c)` of `R' ⊗_R S`, the presentation
`R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)` of a principal localization `S_g`, and the
presentation `R_M[x_1, …, x_n]/(f_1, …, f_c)` of `S` over a localization `R_M` through which
`R → S` factors are again relative global complete intersections, and deduces the corresponding
stability of the property of ring maps. It also proves that if the fibres have dimension
`n - c` over `V(I)`, over one prime of `R`, or at one prime of `S`, then some principal
localization `S_g = R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)` is a relative global
complete intersection.

## Main definitions

* `Algebra.Presentation.localizationAwayComp`: for a presentation
  `S = R[x_1, …, x_n]/(f_1, …, f_c)` and `h ∈ R[x_1, …, x_n]` with image `g ∈ S`, the presentation
  `S_g = R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)`.
* `Algebra.Presentation.localizationAwayCompOfMulMem`: the same presentation of `S_g` with the
  relations `f_j` replaced by elements `f'_1, …, f'_c` of the kernel with `h I ⊆ (f'_1, …, f'_c)`.
* `Algebra.Presentation.localizationBase`: for a presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)`
  and a localization `R_M` of `R` through which `R → S` factors, the presentation
  `S = R_M[x_1, …, x_n]/(f_1, …, f_c)` over `R_M`.

## Main results

* `Algebra.Presentation.IsRelativeGlobalCompleteIntersection.baseChange`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection.localizationAwayComp`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection.localizationBase`: if a presentation
  `P` of `S` is a relative global complete intersection, then so are `P.baseChange R'`,
  `P.localizationAwayComp h T` and `P.localizationBase M Rₘ`; together they are
  `baseChange_and_localizationAwayComp_and_localizationBase` in the same namespace.
* `Algebra.Presentation.IsRelativeGlobalCompleteIntersection.baseChange_ofAlgEquiv_isPushoutEquiv`:
  the base changed presentation transported to an arbitrary pushout square.

* `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`: the base change of a relative global
  complete intersection along an arbitrary pushout square is a relative global complete
  intersection.
* `Algebra.IsRelativeGlobalCompleteIntersection.of_isLocalizationAway`: a localization of a
  relative global complete intersection away from one element is one.
* `Algebra.IsRelativeGlobalCompleteIntersection.localization_base`: a relative global complete
  intersection over `R` whose structure map factors through a localization `R_M` of `R` is one over
  `R_M`.
* `baseChange_and_localization_away_and_localization_base`, in the namespace
  `Algebra.IsRelativeGlobalCompleteIntersection`: the three stability properties together.
* `Algebra.Presentation.natCard_le_ringKrullDim_add_natCard`: a nonzero algebra presented over a
  field by `n` variables and `c` relations has dimension at least `n - c`.
* `Algebra.Presentation.exists_sub_one_mem_map_isRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.exists_isUnit_fiber_isRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.exists_notMem_isRelativeGlobalCompleteIntersection`: if the fibres have
  dimension `n - c` over `V(I)`, over a prime `𝔭` of `R`, or at a prime `𝔮` of `S`, then some
  principal localization `S_g`, with `g ↦ 1 ∈ S/IS`, `g` a unit in `S ⊗_R κ(𝔭)`, or `g ∉ 𝔮`
  respectively, is a relative global complete intersection.
* `Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv`: the property is invariant under
  isomorphism of `R`-algebras.

## Implementation notes

The stability results come in two forms. The presentation-level ones, in the namespace
`Algebra.Presentation.IsRelativeGlobalCompleteIntersection`, take a presentation `P` with
`P.IsRelativeGlobalCompleteIntersection` and conclude that the named presentations built from it
are relative global complete intersections, with `n`, `n + 1` or `n` variables and `c`, `c + 1` or
`c` relations; they are the statement of Stacks 00SS. The class-level ones, in the namespace
`Algebra.IsRelativeGlobalCompleteIntersection`, conclude only the property
`Algebra.IsRelativeGlobalCompleteIntersection` of the new ring map. In both, the three parts are
the conjuncts of one statement with the auxiliary rings quantified inside the statement. These
rings live in independent universes, so a projection of the
conjunction leaves the other universes undetermined; the three parts are therefore also stated
separately.

The base change is stated over an arbitrary pushout square `Algebra.IsPushout R S R' S'`, with
nothing assumed about `R → R'`. Its fibre over a prime `p'` of `R'` is the base change of the fibre
of `R → S` over `p = p' ∩ R` along `κ(p) → κ(p')`, so the two have the same dimension. The
localization of `S` is an arbitrary `IsLocalization.Away g S'`; its fibre over `p` is the
localization of the fibre of `S` away from the image of `g`. The localization of the base is at an
arbitrary submonoid `M ⊆ R`, and the factorization `R → R_M → S` is `[Algebra Rₘ S]` with
`[IsScalarTower R Rₘ S]`.

The dimension condition is written additively, as `dim + c = n` in `WithBot ℕ∞`, so that no
truncated subtraction `n - c` appears.

## References

* [Stacks 00SS](https://stacks.math.columbia.edu/tag/00SS), Lemma 10.136.9
* [Stacks 00ST](https://stacks.math.columbia.edu/tag/00ST), Lemma 10.136.10
* [Stacks 00SP](https://stacks.math.columbia.edu/tag/00SP), Definition 10.136.5
* [Stacks 00P3](https://stacks.math.columbia.edu/tag/00P3), Lemma 10.116.5
* [Stacks 00SA](https://stacks.math.columbia.edu/tag/00SA), Lemma 10.135.2
* [Stacks 00QH](https://stacks.math.columbia.edu/tag/00QH), Lemma 10.125.6
-/

@[expose] public section

universe u v u' v' w t

namespace Stacks.CompleteIntersection.Stability

open Syntomic.BaseChange

attribute [local instance] Ideal.residueFieldAlgebra
attribute [local instance] Ideal.isScalarTower_residueField
attribute [local instance] isScalarTower_baseChange_fiber
attribute [local instance] fiberAlgebra
attribute [local instance] isScalarTower_residueField_fiber
attribute [local instance] isPushout_fiber

open scoped TensorProduct

/-! ### The dimension condition -/

/-- If `x + c = n` in `WithBot ℕ∞` with `c` and `n` natural numbers, then `x` is a natural number
`m` with `m + c = n`; in particular `c ≤ n`. -/
private theorem exists_natCast_eq_of_add_natCast_eq {x : WithBot ℕ∞} {c n : ℕ}
    (h : x + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)) :
    ∃ m : ℕ, x = (m : WithBot ℕ∞) ∧ m + c = n := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      rw [show ((⊤ : ℕ∞) : WithBot ℕ∞) + (c : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) from rfl] at h
      exact absurd (WithBot.coe_injective h) (by simp)
    | coe m => exact ⟨m, by norm_cast, by exact_mod_cast h⟩

/-- Adding one variable and one relation preserves the dimension condition: if `x + c = n`, then
`x + (c + 1) = n + 1`. -/
private theorem add_succ_natCast_eq_succ_natCast {x : WithBot ℕ∞} {c n : ℕ}
    (h : x + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)) :
    x + ((c + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
  push_cast
  rw [← add_assoc, h]

/-! ### Principal localizations of global complete intersections -/

/-- The isomorphism of `R`-algebras of `A` onto `R[x_i]/(f_j)` given by a presentation of `A`
over `R`, with the quotient taken by the span of the relations. -/
private noncomputable def presentationQuotientEquiv {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {ι σ : Type*} (P : Algebra.Presentation R A ι σ) :
    A ≃ₐ[R] MvPolynomial ι R ⧸ Ideal.span (Set.range P.relation) :=
  (P.quotientEquiv.restrictScalars R).symm.trans
    (Ideal.quotientEquivAlgOfEq R P.span_range_relation_eq_ker.symm)

/-- A nonzero localization away from one element of a global complete intersection over a field
has the dimension of the ring itself: if `A` is presented over a field by `n` variables and `c`
relations with `dim A + c = n`, then `dim A_g = dim A` whenever `A_g` is nonzero. -/
private theorem ringKrullDim_localizationAway_eq {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    {n c : ℕ} (P : Algebra.Presentation k A (Fin n) (Fin c))
    (hdim : ringKrullDim A + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)) (g : A)
    [Nontrivial (Localization.Away g)] :
    ringKrullDim (Localization.Away g) = ringKrullDim A := by
  have : Algebra.FinitePresentation k A := P.finitePresentation_of_isFinite
  obtain ⟨m, hm, hmc⟩ := exists_natCast_eq_of_add_natCast_eq hdim
  have hnc : n - c = m := by omega
  rw [hm, gci_localization_dim k A g n c P.relation (presentationQuotientEquiv P)
    (by rw [hm, hnc]) (not_subsingleton _), hnc]

/-! ### The fibre of a base change -/

section Fiber

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R R' S S' : Type*) [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S'] [Algebra S S']
  [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']
  (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime] [p'.LiesOver p]

omit [Algebra.IsPushout R R' S S'] in
/-- If the fibre of `Spec(S') → Spec(R')` over `p'` is nonempty, then so is the fibre of
`Spec(S) → Spec(R)` over `p`. -/
private theorem nontrivial_fiber [Nontrivial (p'.Fiber S')] : Nontrivial (p.Fiber S) :=
  (fiberMap R R' S S' p p').toRingHom.domain_nontrivial

/-- The fibres of a base change have the same dimension as the fibres of the original map: the
fibre of `Spec(S') → Spec(R')` over `p'` has the dimension of the fibre of `Spec(S) → Spec(R)`
over `p`. -/
private theorem ringKrullDim_fiber_eq [Algebra.FiniteType p.ResidueField (p.Fiber S)] :
    ringKrullDim (p.Fiber S) = ringKrullDim (p'.Fiber S') :=
  Algebra.IsPushout.ringKrullDim_eq p.ResidueField p'.ResidueField (p.Fiber S) (p'.Fiber S')

end Fiber

/-! ### The fibre of a localization away from one element -/

section FiberLocalization

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (g : S) (S' : Type*) [CommRing S']
  [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [IsLocalization.Away g S']
  (p : Ideal R) [p.IsPrime]

/-- The fibre of a localization is a localization of the fibre: the fibre `κ(p) ⊗_R S_g` of
`R → S_g` at a prime `p` of `R` is the localization of the fibre `κ(p) ⊗_R S` of `R → S` away from
the image of `g`. -/
private noncomputable def fiberLocalizationAwayRingEquiv :
    p.Fiber S' ≃+* Localization.Away (algebraMap S (p.Fiber S) g) :=
  (Algebra.IsPushout.cancelBaseChangeAlg R p.ResidueField S (p.Fiber S) S').symm.toRingEquiv.trans
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap S (p.Fiber S) g))
      (p.Fiber S ⊗[S] S') (Localization.Away (algebraMap S (p.Fiber S) g))).toRingEquiv

/-- If the fibre of `Spec(S_g) → Spec(R)` over `p` is nonempty, then so is the localization of the
fibre of `Spec(S) → Spec(R)` over `p` away from the image of `g`. -/
private theorem nontrivial_localizationAway_fiber [Nontrivial (p.Fiber S')] :
    Nontrivial (Localization.Away (algebraMap S (p.Fiber S) g)) :=
  (fiberLocalizationAwayRingEquiv g S' p).toEquiv.nontrivial_congr.mp ‹_›

include g in
/-- If the fibre of `Spec(S_g) → Spec(R)` over `p` is nonempty, then so is the fibre of
`Spec(S) → Spec(R)` over `p`. -/
private theorem nontrivial_fiber_of_isLocalizationAway [Nontrivial (p.Fiber S')] :
    Nontrivial (p.Fiber S) :=
  have := nontrivial_localizationAway_fiber g S' p
  (algebraMap (p.Fiber S) (Localization.Away (algebraMap S (p.Fiber S) g))).domain_nontrivial

end FiberLocalization

/-! ### Stability under base change and localization -/

/-- The base change of a relative global complete intersection along an
arbitrary ring map `R → R'` is a relative global complete intersection over `R'`, presented by the
base changed presentation, with the same number of variables and of relations. -/
private theorem baseChange_aux (R S R' S' : Type*) [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
    [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R S R' S']
    [Algebra.IsRelativeGlobalCompleteIntersection R S] :
    Algebra.IsRelativeGlobalCompleteIntersection R' S' := by
  have : Algebra.IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  obtain ⟨n, c, P, hP⟩ := ‹Algebra.IsRelativeGlobalCompleteIntersection R S›.out
  refine ⟨n, c, (P.baseChange R').ofAlgEquiv (Algebra.IsPushout.equiv R R' S S'), ⟨?_⟩⟩
  intro q _ hq
  have : Nontrivial ((q.under R).Fiber S) := nontrivial_fiber R R' S S' (q.under R) q
  have : Algebra.FinitePresentation (q.under R).ResidueField ((q.under R).Fiber S) :=
    (P.baseChange (q.under R).ResidueField).finitePresentation_of_isFinite
  rw [← ringKrullDim_fiber_eq R R' S S' (q.under R) q]
  exact hP.ringKrullDim_fiber_add_card_eq_card (q.under R) ‹_›

/-- The equivalence `Fin (n + 1) ≃ Unit ⊕ Fin n` sending `0` to the unit and `i + 1` to `i`. -/
private def finSuccEquivUnitSum (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n :=
  (finCongr (Nat.add_comm n 1)).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl (Fin n))))

/-- A localization `S_g` of a relative global complete intersection away from
one element is a relative global complete intersection over `R`, presented by `n + 1` variables and
`c + 1` relations. -/
private theorem of_isLocalizationAway_aux {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsRelativeGlobalCompleteIntersection R S] (g : S) (S' : Type*) [CommRing S']
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [IsLocalization.Away g S'] :
    Algebra.IsRelativeGlobalCompleteIntersection R S' := by
  obtain ⟨n, c, P, hP⟩ := ‹Algebra.IsRelativeGlobalCompleteIntersection R S›.out
  refine ⟨n + 1, c + 1, (((Algebra.Presentation.localizationAway S' g).comp P).reindex
    (finSuccEquivUnitSum n) (finSuccEquivUnitSum c)), ⟨?_⟩⟩
  intro p _ hp
  have := nontrivial_localizationAway_fiber g S' p
  have := nontrivial_fiber_of_isLocalizationAway g S' p
  have hdim : ringKrullDim (p.Fiber S) + (c : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    simpa using hP.ringKrullDim_fiber_add_card_eq_card p ‹_›
  rw [ringKrullDim_eq_of_ringEquiv (fiberLocalizationAwayRingEquiv g S' p),
    ringKrullDim_localizationAway_eq (P.baseChange p.ResidueField) hdim]
  simpa using add_succ_natCast_eq_succ_natCast hdim

/-- A relative global complete intersection over `R` whose structure map factors through a
localization `Rₘ` of `R` is a relative global complete intersection over `Rₘ`. -/
private theorem localization_base_aux {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*}
    [CommRing S] [Algebra R S] [Algebra.IsRelativeGlobalCompleteIntersection R S] {Rₘ : Type*}
    [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra Rₘ S] [IsScalarTower R Rₘ S] :
    Algebra.IsRelativeGlobalCompleteIntersection Rₘ S := by
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) S := by
    refine IsLocalization.of_le_isUnit ?_
    rintro x ⟨y, hy, rfl⟩
    rw [IsScalarTower.algebraMap_apply R Rₘ S]
    exact (IsLocalization.map_units Rₘ ⟨y, hy⟩).map (algebraMap Rₘ S)
  have : Algebra.IsPushout R S Rₘ S := Algebra.isPushout_of_isLocalization M Rₘ S S
  exact baseChange_aux R S Rₘ S

/-- The three stability properties of a relative global complete intersection `S` over `R`: its
base change along any pushout square, its localization away from any element of `S`, and `S` over
any localization of `R` through which `R → S` factors are relative global complete
intersections. -/
public theorem solution (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsRelativeGlobalCompleteIntersection R S] :
    (∀ (R' : Type u') (S' : Type v') [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R S']
        [Algebra S S'] [Algebra R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
        [Algebra.IsPushout R S R' S'], Algebra.IsRelativeGlobalCompleteIntersection R' S') ∧
      (∀ (g : S) (S' : Type w) [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
        [IsLocalization.Away g S'], Algebra.IsRelativeGlobalCompleteIntersection R S') ∧
      (∀ (M : Submonoid R) (Rₘ : Type t) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ]
        [Algebra Rₘ S] [IsScalarTower R Rₘ S],
          Algebra.IsRelativeGlobalCompleteIntersection Rₘ S) :=
  ⟨fun R' S' _ _ _ _ _ _ _ _ _ => baseChange_aux R S R' S',
    fun g S' _ _ _ _ _ => of_isLocalizationAway_aux g S',
    fun M _Rₘ _ _ _ _ _ => localization_base_aux M⟩

end Stacks.CompleteIntersection.Stability

@[expose] public section



namespace Algebra.IsRelativeGlobalCompleteIntersection

/-- The three stability properties of the class `Algebra.IsRelativeGlobalCompleteIntersection`: if
`S` is a relative global complete intersection over `R`, then

1. for any pushout square `Algebra.IsPushout R S R' S'`, `S'` is one over `R'`;
2. for any `g ∈ S`, any localization `S'` of `S` away from `g` is one over `R`;
3. if `R → S` factors through a localization `Rₘ` of `R`, then `S` is one over `Rₘ`.

These are statements about the existence of some good presentation. The statement of Stacks 00SS
about the specific presentations `R'[x_1, …, x_n]/(f_1, …, f_c)`,
`R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, hx_{n+1} - 1)` and `Rₘ[x_1, …, x_n]/(f_1, …, f_c)` is
`baseChange_and_localizationAwayComp_and_localizationBase` in the namespace
`Algebra.Presentation.IsRelativeGlobalCompleteIntersection`. -/
public theorem baseChange_and_localization_away_and_localization_base (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsRelativeGlobalCompleteIntersection R S] :
    (∀ (R' : Type u') (S' : Type v') [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R S']
        [Algebra S S'] [Algebra R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
        [Algebra.IsPushout R S R' S'], Algebra.IsRelativeGlobalCompleteIntersection R' S') ∧
      (∀ (g : S) (S' : Type w) [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
        [IsLocalization.Away g S'], Algebra.IsRelativeGlobalCompleteIntersection R S') ∧
      (∀ (M : Submonoid R) (Rₘ : Type t) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ]
        [Algebra Rₘ S] [IsScalarTower R Rₘ S],
          Algebra.IsRelativeGlobalCompleteIntersection Rₘ S) :=
  Stacks.CompleteIntersection.Stability.solution R S

/-- The base change of a relative global complete intersection is a relative global complete
intersection: if `S` is one over `R` and `Algebra.IsPushout R S R' S'`, then `S'` is one over `R'`.
Nothing is assumed about `R → R'`. This is the class-level form; that the base changed presentation
is a relative global complete intersection is
`Algebra.Presentation.IsRelativeGlobalCompleteIntersection.baseChange`. -/
public theorem baseChange (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (R' : Type u') (S' : Type v') [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R S']
    [Algebra S S'] [Algebra R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Algebra.IsRelativeGlobalCompleteIntersection R S] :
    Algebra.IsRelativeGlobalCompleteIntersection R' S' :=
  (baseChange_and_localization_away_and_localization_base.{u, v, u', v', v, v} R S).1 R' S'

/-- A localization of a relative global complete intersection away from an element is a relative
global complete intersection: if `S` is one over `R` and `S'` is a localization of `S` away from
`g ∈ S`, then `S'` is one over `R`. This is the class-level form; that the presentation
`R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, hx_{n+1} - 1)` of `S_g` is a relative global complete
intersection is `Algebra.Presentation.IsRelativeGlobalCompleteIntersection.localizationAwayComp`. -/
public theorem of_isLocalizationAway {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsRelativeGlobalCompleteIntersection R S] (g : S) {S' : Type w}
    [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [IsLocalization.Away g S'] :
    Algebra.IsRelativeGlobalCompleteIntersection R S' :=
  (baseChange_and_localization_away_and_localization_base.{u, v, u, v, w, v} R S).2.1 g S'

/-- A relative global complete intersection over `R` whose structure map factors through a
localization `Rₘ` of `R` is a relative global complete intersection over `Rₘ`. This is the
class-level form; that the presentation `Rₘ[x_1, …, x_n]/(f_1, …, f_c)` of `S` is a relative global
complete intersection is
`Algebra.Presentation.IsRelativeGlobalCompleteIntersection.localizationBase`. -/
public theorem localization_base {R : Type u} [CommRing R] (M : Submonoid R) {S : Type v}
    [CommRing S] [Algebra R S] [Algebra.IsRelativeGlobalCompleteIntersection R S] {Rₘ : Type t}
    [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra Rₘ S] [IsScalarTower R Rₘ S] :
    Algebra.IsRelativeGlobalCompleteIntersection Rₘ S :=
  (baseChange_and_localization_away_and_localization_base.{u, v, u, v, v, t} R S).2.2 M Rₘ

end Algebra.IsRelativeGlobalCompleteIntersection

/-! ### Principal localizations whose fibres have the expected dimension -/

namespace Algebra.Presentation

open MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*}

/-- For a presentation `S = R[xᵢ]/(fⱼ)`, the kernel of `R[yₖ, xᵢ] → S[yₖ]`, `yₖ ↦ yₖ`,
`xᵢ ↦ xᵢ mod (fⱼ)`, is generated by the `fⱼ`. -/
theorem ker_aeval_sumElim (P : Algebra.Presentation R S ι σ) (ι' : Type*) :
    RingHom.ker (aeval (R := R) (S₁ := MvPolynomial ι' S) (Sum.elim X (C ∘ P.val))) =
      Ideal.span (Set.range fun j ↦ rename Sum.inr (P.relation j)) := by
  have heq : aeval (R := R) (S₁ := MvPolynomial ι' S) (Sum.elim X (C ∘ P.val)) =
      (mapAlgHom (aeval P.val)).comp (sumAlgEquiv R ι' ι).toAlgHom := by
    ext i : 1
    cases i <;> simp
  have hC : Ideal.map (C : MvPolynomial ι R →+* MvPolynomial ι' (MvPolynomial ι R))
      (RingHom.ker (aeval (R := R) P.val)) =
      Ideal.map ((sumAlgEquiv R ι' ι).toAlgHom.comp (rename Sum.inr))
        (RingHom.ker (aeval (R := R) P.val)) := by
    rw [sumAlgEquiv_comp_rename_inr, ← Ideal.map_coe (IsScalarTower.toAlgHom R (MvPolynomial ι R)
      (MvPolynomial ι' (MvPolynomial ι R))), IsScalarTower.coe_toAlgHom, MvPolynomial.algebraMap_eq]
  rw [heq, ← AlgHom.comap_ker, ker_mapAlgHom, hC, ← Ideal.map_mapₐ, Ideal.comap_map_of_bijective]
  · rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker, Ideal.map_span, ← Set.range_comp]
    rfl
  · simpa using AlgEquiv.bijective (sumAlgEquiv R ι' ι)

variable (P : Algebra.Presentation R S ι σ) (h : P.Ring) (T : Type*) [CommRing T] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T] [IsLocalization.Away (algebraMap P.Ring S h) T]

/-- Given a presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)` and `h ∈ R[x_1, …, x_n]` with image
`g ∈ S`, the presentation `S_g = R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)`, with the
new variable indexed by `Unit`. -/
noncomputable def localizationAwayComp : Algebra.Presentation R T (Unit ⊕ ι) (Unit ⊕ σ) where
  toGenerators := (Generators.localizationAway T (algebraMap P.Ring S h)).comp P.toGenerators
  relation := Sum.elim (fun _ ↦ rename Sum.inr h * X (Sum.inl ()) - 1)
    fun j ↦ rename Sum.inr (P.relation j)
  span_range_relation_eq_ker := by
    refine Eq.trans ?_
      ((Presentation.localizationAway T (algebraMap P.Ring S h)).span_range_relation_eq_ker_comp P)
    rw [Set.Sum.elim_range, Set.Sum.elim_range, Ideal.span_union,
      Ideal.span_union, Set.range_const, Set.range_unique
        (f := (Presentation.localizationAway T (algebraMap P.Ring S h)).compRelationAux P)]
    set a := (Presentation.localizationAway T (algebraMap P.Ring S h)).compRelationAux P default
    have ha : aeval (R := R) (S₁ := MvPolynomial Unit S) (Sum.elim X (C ∘ P.val)) a =
        C (algebraMap P.Ring S h) * X () - 1 := by
      have := comp_aeval_relation_inl (Presentation.localizationAway T (algebraMap P.Ring S h)) P ()
      rwa [Presentation.comp_relation, Sum.elim_inl, localizationAway_relation] at this
    have hdiff : a - (rename Sum.inr h * X (Sum.inl ()) - 1) ∈
        Ideal.span (Set.range fun j ↦ rename Sum.inr (P.relation j)) := by
      have hC : aeval (R := R) (S₁ := MvPolynomial Unit S) (Sum.elim X (C ∘ P.val))
          (rename Sum.inr h) = C (algebraMap P.Ring S h) := by
        rw [aeval_rename, Sum.elim_comp_inr, P.algebraMap_apply, ← MvPolynomial.algebraMap_eq,
          ← IsScalarTower.toAlgHom_apply R S (MvPolynomial Unit S), comp_aeval_apply]
        rfl
      rw [← ker_aeval_sumElim, RingHom.mem_ker, map_sub, ha, map_sub, map_mul, hC, aeval_X, map_one]
      simp
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
    · rw [Ideal.span_singleton_le_iff_mem, show rename Sum.inr h * X (Sum.inl ()) - 1 =
        a - (a - (rename Sum.inr h * X (Sum.inl ()) - 1)) by ring]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_right hdiff)
    · rw [Ideal.span_singleton_le_iff_mem, ← sub_add_cancel a
        (rename Sum.inr h * X (Sum.inl ()) - 1)]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hdiff)
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

end Algebra.Presentation

/-! ### Stability of the presentations of a relative global complete intersection -/

namespace Algebra.Presentation

open Stacks.CompleteIntersection.Stability Syntomic.BaseChange

attribute [local instance] Ideal.residueFieldAlgebra
attribute [local instance] Ideal.isScalarTower_residueField
attribute [local instance] isScalarTower_baseChange_fiber
attribute [local instance] fiberAlgebra
attribute [local instance] isScalarTower_residueField_fiber
attribute [local instance] isPushout_fiber

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*}

/-- If `R → S` factors through a localization `Rₘ` of `R`, then `S` is the base change of `S` along
`R → Rₘ`, that is, `Rₘ ⊗_R S ≅ S`. -/
theorem _root_.Algebra.IsPushout.of_isLocalization_base (M : Submonoid R) (Rₘ : Type*)
    [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra Rₘ S] [IsScalarTower R Rₘ S] :
    Algebra.IsPushout R Rₘ S S := by
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) S := by
    refine IsLocalization.of_le_isUnit ?_
    rintro x ⟨y, hy, rfl⟩
    rw [IsScalarTower.algebraMap_apply R Rₘ S]
    exact (IsLocalization.map_units Rₘ ⟨y, hy⟩).map (algebraMap Rₘ S)
  exact (Algebra.isPushout_of_isLocalization M Rₘ S S).symm

/-- Given a presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)` and a localization `Rₘ` of `R` through
which `R → S` factors, the presentation `S = Rₘ[x_1, …, x_n]/(f_1, …, f_c)` of `S` over `Rₘ`, with
the same variables `x_i` and the images of the same relations `f_j`. It is the base change
`Rₘ ⊗_R S = Rₘ[x_1, …, x_n]/(f_1, …, f_c)` transported along `Rₘ ⊗_R S ≅ S`. -/
noncomputable def localizationBase (P : Algebra.Presentation R S ι σ) (M : Submonoid R)
    (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra Rₘ S]
    [IsScalarTower R Rₘ S] : Algebra.Presentation Rₘ S ι σ :=
  haveI := Algebra.IsPushout.of_isLocalization_base M Rₘ (S := S)
  (P.baseChange Rₘ).ofAlgEquiv (Algebra.IsPushout.equiv R Rₘ S S)

/-- The variables of `Algebra.Presentation.localizationBase` are those of the original
presentation. -/
@[simp]
theorem localizationBase_val (P : Algebra.Presentation R S ι σ) (M : Submonoid R)
    (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra Rₘ S]
    [IsScalarTower R Rₘ S] (i : ι) : (P.localizationBase M Rₘ).val i = P.val i := by
  have := Algebra.IsPushout.of_isLocalization_base M Rₘ (S := S)
  change Algebra.IsPushout.equiv R Rₘ S S (1 ⊗ₜ[R] P.val i) = P.val i
  rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul, Algebra.algebraMap_self, RingHom.id_apply]

/-- The relations of `Algebra.Presentation.localizationBase` are the images in `Rₘ[x_1, …, x_n]`
of those of the original presentation. -/
@[simp]
theorem localizationBase_relation (P : Algebra.Presentation R S ι σ) (M : Submonoid R)
    (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra Rₘ S]
    [IsScalarTower R Rₘ S] (j : σ) :
    (P.localizationBase M Rₘ).relation j = MvPolynomial.map (algebraMap R Rₘ) (P.relation j) :=
  rfl

namespace IsRelativeGlobalCompleteIntersection

variable [Finite ι] [Finite σ] (P : Algebra.Presentation R S ι σ)
  [P.IsRelativeGlobalCompleteIntersection]

/-- Transporting a presentation which is a relative global complete intersection along an
isomorphism of `R`-algebras gives a presentation which is a relative global complete
intersection. -/
theorem ofAlgEquiv {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    (P.ofAlgEquiv e).IsRelativeGlobalCompleteIntersection := by
  refine ⟨fun p _ hnt ↦ ?_⟩
  let eF : p.Fiber S ≃ₐ[p.ResidueField] p.Fiber T := Algebra.TensorProduct.congr AlgEquiv.refl e
  rw [← ringKrullDim_eq_of_ringEquiv eF.toRingEquiv]
  exact ‹P.IsRelativeGlobalCompleteIntersection›.ringKrullDim_fiber_add_card_eq_card p
    (eF.toEquiv.nontrivial_congr.mpr hnt)

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Stacks 00SS (1): if `S = R[x_1, …, x_n]/(f_1, …, f_c)` is a relative global complete
intersection, then for any ring map `R → R'` the base change
`R' ⊗_R S = R'[x_1, …, x_n]/(f_1, …, f_c)`, presented by `P.baseChange R'` with the same `n`
variables and `c` relations, is a relative global complete intersection over `R'`. -/
theorem baseChange (R' : Type*) [CommRing R'] [Algebra R R'] :
    (P.baseChange R').IsRelativeGlobalCompleteIntersection := by
  refine ⟨fun q _ hq ↦ ?_⟩
  have : Nontrivial ((q.under R).Fiber S) :=
    nontrivial_fiber R R' S (TensorProduct R R' S) (q.under R) q
  have : Algebra.FinitePresentation (q.under R).ResidueField ((q.under R).Fiber S) :=
    (P.baseChange (q.under R).ResidueField).finitePresentation_of_isFinite
  rw [← ringKrullDim_fiber_eq R R' S (TensorProduct R R' S) (q.under R)
    q]
  exact ‹P.IsRelativeGlobalCompleteIntersection›.ringKrullDim_fiber_add_card_eq_card (q.under R)
    ‹_›

end BaseChange

/-- Stacks 00SS (1) along an arbitrary pushout square: if `S = R[x_1, …, x_n]/(f_1, …, f_c)` is a
relative global complete intersection and `S'` is a pushout of `R → S` along `R → R'`, then the
presentation `S' ≅ R' ⊗_R S = R'[x_1, …, x_n]/(f_1, …, f_c)` is a relative global complete
intersection over `R'`. -/
theorem baseChange_ofAlgEquiv_isPushoutEquiv (R' S' : Type*) [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'] [IsScalarTower R R' S']
    [IsScalarTower R S S'] [Algebra.IsPushout R R' S S'] :
    ((P.baseChange R').ofAlgEquiv
      (Algebra.IsPushout.equiv R R' S S')).IsRelativeGlobalCompleteIntersection :=
  have := baseChange P R'
  ofAlgEquiv (P.baseChange R') _

/-- Stacks 00SS (2): if `S = R[x_1, …, x_n]/(f_1, …, f_c)` is a relative global complete
intersection and `g ∈ S` is the image of `h ∈ R[x_1, …, x_n]`, then the presentation
`S_g = R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)`, with `n + 1` variables and `c + 1`
relations, is a relative global complete intersection over `R`. Here `S_g` is any localization `T`
of `S` away from `g`. -/
theorem localizationAwayComp (h : P.Ring) (T : Type*) [CommRing T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [IsLocalization.Away (algebraMap P.Ring S h) T] :
    (P.localizationAwayComp h T).IsRelativeGlobalCompleteIntersection := by
  refine ⟨fun p _ hp ↦ ?_⟩
  have := nontrivial_localizationAway_fiber (algebraMap P.Ring S h) T p
  have := nontrivial_fiber_of_isLocalizationAway (algebraMap P.Ring S h) T p
  have hdim : ringKrullDim (p.Fiber S) + ((Nat.card σ : ℕ) : WithBot ℕ∞) =
      ((Nat.card ι : ℕ) : WithBot ℕ∞) :=
    ‹P.IsRelativeGlobalCompleteIntersection›.ringKrullDim_fiber_add_card_eq_card p ‹_›
  rw [ringKrullDim_eq_of_ringEquiv (fiberLocalizationAwayRingEquiv (algebraMap P.Ring S h) T p),
    ringKrullDim_localizationAway_eq ((P.baseChange p.ResidueField).reindex
      (Finite.equivFin ι).symm (Finite.equivFin σ).symm) hdim,
    Nat.card_sum, Nat.card_sum, Nat.card_unique, Nat.add_comm 1, Nat.add_comm 1]
  exact add_succ_natCast_eq_succ_natCast hdim

/-- Stacks 00SS (3): if `S = R[x_1, …, x_n]/(f_1, …, f_c)` is a relative global complete
intersection and `R → S` factors as `R → Rₘ → S` through a localization `Rₘ` of `R`, then the
presentation `S = Rₘ[x_1, …, x_n]/(f_1, …, f_c)` with the same `n` variables and `c` relations is a
relative global complete intersection over `Rₘ`. -/
theorem localizationBase (M : Submonoid R) (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ]
    [IsLocalization M Rₘ] [Algebra Rₘ S] [IsScalarTower R Rₘ S] :
    (P.localizationBase M Rₘ).IsRelativeGlobalCompleteIntersection :=
  have := baseChange P Rₘ
  ofAlgEquiv (P.baseChange Rₘ) _

/-- Let `S = R[x_1, …, x_n]/(f_1, …, f_c)` be a relative global complete intersection, presented
by `P` with `n` variables and `c` relations. Then

1. for any ring map `R → R'` the presentation `R' ⊗_R S = R'[x_1, …, x_n]/(f_1, …, f_c)` with `n`
   variables and `c` relations is a relative global complete intersection over `R'`;
2. for any `g ∈ S` which is the image of `h ∈ R[x_1, …, x_n]`, the presentation
   `S_g = R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)` with `n + 1` variables and `c + 1`
   relations is a relative global complete intersection over `R`;
3. if `R → S` factors as `R → Rₘ → S` through a localization `Rₘ` of `R`, the presentation
   `S = Rₘ[x_1, …, x_n]/(f_1, …, f_c)` with `n` variables and `c` relations is a relative global
   complete intersection over `Rₘ`. -/
@[stacks 00SS "The given relative global complete intersection
`S = R[x_1, …, x_n]/(f_1, …, f_c)` is a presentation `P` with
`P.IsRelativeGlobalCompleteIntersection`, the numbers of variables and relations being
`Nat.card ι` and `Nat.card σ`, and each conclusion is that the named presentation is a relative
global complete intersection. (1) is `P.baseChange R'`, the presentation
`R'[x_1, …, x_n]/(f_1, …, f_c)` of `R' ⊗_R S`; the version along an arbitrary pushout square is
`baseChange_ofAlgEquiv_isPushoutEquiv`. (2) is `P.localizationAwayComp h T`, with variables
`Unit ⊕ ι` and relations `Unit ⊕ σ`, the new relation being `h x_{n+1} - 1`, for any localization
`T` of `S` away from the image `g` of `h`. (3) is `P.localizationBase M Rₘ`, with the same variables
(`localizationBase_val`) and the images of the same relations (`localizationBase_relation`), for a
localization `Rₘ` of `R` at an arbitrary submonoid `M`, not only at the powers of one `f ∈ R`; the
factorization `R → Rₘ → S` is `[Algebra Rₘ S]` with `[IsScalarTower R Rₘ S]`. The auxiliary rings
are quantified inside the statement; each part is also stated separately."]
theorem baseChange_and_localizationAwayComp_and_localizationBase :
    (∀ (R' : Type*) [CommRing R'] [Algebra R R'],
        (P.baseChange R').IsRelativeGlobalCompleteIntersection) ∧
      (∀ (h : P.Ring) (T : Type*) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
        [IsLocalization.Away (algebraMap P.Ring S h) T],
          (P.localizationAwayComp h T).IsRelativeGlobalCompleteIntersection) ∧
      (∀ (M : Submonoid R) (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ]
        [Algebra Rₘ S] [IsScalarTower R Rₘ S],
          (P.localizationBase M Rₘ).IsRelativeGlobalCompleteIntersection) :=
  ⟨fun R' _ _ ↦ baseChange P R', fun h T _ _ _ _ _ ↦ localizationAwayComp P h T,
    fun M Rₘ _ _ _ _ _ ↦ localizationBase P M Rₘ⟩

end IsRelativeGlobalCompleteIntersection

end Algebra.Presentation

/-- A nonzero algebra presented over a field by `n` variables and `c` relations has dimension at
least `n - c`, written additively: `n ≤ dim A + c`. -/
theorem Algebra.Presentation.natCard_le_ringKrullDim_add_natCard {k A : Type*} [Field k]
    [CommRing A] [Algebra k A] [Nontrivial A] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation k A ι σ) :
    ((Nat.card ι : ℕ) : WithBot ℕ∞) ≤ ringKrullDim A + ((Nat.card σ : ℕ) : WithBot ℕ∞) := by
  set P' := P.reindex (Finite.equivFin ι).symm (Finite.equivFin σ).symm
  let e := Stacks.CompleteIntersection.Stability.presentationQuotientEquiv P'
  have hnt : Nontrivial (MvPolynomial (Fin (Nat.card ι)) k ⧸ Ideal.span (Set.range P'.relation)) :=
    e.toEquiv.symm.nontrivial
  have hge := mvpoly_quotient_span_range_ringKrullDim_ge k _ _ P'.relation hnt
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv] at hge
  calc ((Nat.card ι : ℕ) : WithBot ℕ∞)
      ≤ ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞) + ((Nat.card σ : ℕ) : WithBot ℕ∞) := by
        norm_cast
        omega
    _ ≤ ringKrullDim A + ((Nat.card σ : ℕ) : WithBot ℕ∞) := by gcongr

/-- If the Krull dimension `d` of a ring satisfies `d + c = n` for natural numbers `c`, `n`, then
`c ≤ n` and `d = n - c`. -/
alias WithBot.le_and_eq_tsub_of_add_natCast_eq := natCast_le_and_eq_of_add_eq

/-- A principal localization with fibres of dimension at most `n - c` is a relative global
complete intersection: let `S = R[x_1, …, x_n]/(f_1, …, f_c)` with `c ≤ n`, let `h ∈ R[x_i]` have
image `g ∈ S`, and suppose every fibre of `Spec(S_g) → Spec(R)` has dimension at most `n - c`. Then
`S_g = R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)` is a relative global complete
intersection. -/
theorem Algebra.Presentation.isRelativeGlobalCompleteIntersection_localizationAwayComp
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation R S ι σ) (h : P.Ring) (hcn : Nat.card σ ≤ Nat.card ι)
    (hfib : ∀ (p : Ideal R) [p.IsPrime],
      ringKrullDim (p.Fiber (Localization.Away (algebraMap P.Ring S h))) ≤
        ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞)) :
    (P.localizationAwayComp h
      (Localization.Away (algebraMap P.Ring S h))).IsRelativeGlobalCompleteIntersection := by
  refine ⟨fun p _ hnt ↦ ?_⟩
  have hge := ((P.localizationAwayComp h (Localization.Away (algebraMap P.Ring S h))).baseChange
    p.ResidueField).natCard_le_ringKrullDim_add_natCard
  simp only [Nat.card_sum, Nat.card_unique] at hge ⊢
  refine le_antisymm ?_ hge
  calc ringKrullDim (p.Fiber (Localization.Away (algebraMap P.Ring S h))) +
        ((1 + Nat.card σ : ℕ) : WithBot ℕ∞)
      ≤ ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞) + ((1 + Nat.card σ : ℕ) : WithBot ℕ∞) :=
        by gcongr; exact hfib p
    _ = ((1 + Nat.card ι : ℕ) : WithBot ℕ∞) := by
        norm_cast
        omega

/-- If the fibre over `p = q ∩ R` has dimension `d`, then `dim_q(S/R) ≤ d`. -/
private theorem relativeDimensionAt_le_of_ringKrullDim_fiber_eq {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime] (p : Ideal R) [p.IsPrime]
    (hqp : q.under R = p) {d : WithBot ℕ∞} (hd : ringKrullDim (p.Fiber S) = d) :
    Algebra.relativeDimensionAt R q ≤ d := by
  obtain ⟨Q, hQp, hQ⟩ := Ideal.Fiber.exists_comap_includeRight_eq q p hqp
  rw [Algebra.relativeDimensionAt_eq_localKrullDim q p hqp Q hQ, ← hd,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  exact le_iSup (TopologicalSpace.localKrullDim (PrimeSpectrum (p.Fiber S))) ⟨Q, hQp⟩

/-- The contraction of a prime of the fibre `p.Fiber S` to `S`, and then to `R`, is `p`. -/
private theorem under_comap_includeRight {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (m : Ideal (p.Fiber S)) [m.IsPrime] :
    (m.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S)).under R = p := by
  refine Eq.trans ?_ (Ideal.over_def m p).symm
  ext r
  rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
    AlgHom.commutes]

/-- The fibres of a principal localization are bounded by the relative dimension: if
`dim_𝔮(S/R) ≤ N` at every prime `𝔮` of `S` with `g ∉ 𝔮`, then every fibre of
`Spec(S_g) → Spec(R)` has dimension at most `N`. -/
theorem Algebra.ringKrullDim_fiber_away_le_of_relativeDimensionAt_le {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (g : S) {N : WithBot ℕ∞}
    (hN : ∀ (q : Ideal S) [q.IsPrime], g ∉ q → Algebra.relativeDimensionAt R q ≤ N)
    (p : Ideal R) [p.IsPrime] : ringKrullDim (p.Fiber (Localization.Away g)) ≤ N := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x ↦ ?_
  have hloc := Algebra.relativeDimensionAt_comap_eq (R := R) g (Localization.Away g)
    (x.asIdeal.comap (Algebra.TensorProduct.includeRight :
      Localization.Away g →ₐ[R] p.Fiber (Localization.Away g)))
  rw [← Algebra.relativeDimensionAt_eq_localKrullDim _ p (under_comap_includeRight p x.asIdeal)
    x.asIdeal rfl, ← hloc]
  refine hN _ fun hg ↦ ?_
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem x.asIdeal hg
    ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map
      (Algebra.TensorProduct.includeRight :
        Localization.Away g →ₐ[R] p.Fiber (Localization.Away g))))

/-- Let `S = R[x_1, …, x_n]/(f_1, …, f_c)`, presented by `P`, and let `I ⊆ R`
be an ideal such that the fibres of `Spec(S/IS) → Spec(R/I)` have dimension `n - c`, that is, every
nonempty fibre of `Spec(S) → Spec(R)` over a prime `𝔭 ⊇ I` has dimension `n - c`. Then there is an
`h ∈ R[x_1, …, x_n]` whose image `g ∈ S` maps to `1 ∈ S/IS`, such that
`S_g = R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)` is a relative global complete
intersection with this presentation. -/
@[stacks 00ST "(1): the fibre of `Spec(S/IS) → Spec(R/I)` over `𝔭/I` is the fibre
`κ(𝔭) ⊗_R S = 𝔭.Fiber S` of `Spec(S) → Spec(R)` over `𝔭 ⊇ I`, and only nonempty fibres are
constrained, as in Definition 00SP; `g ↦ 1 ∈ S/IS` is `g - 1 ∈ IS`. The presentation of `S_g` is
`Algebra.Presentation.localizationAwayComp`."]
theorem Algebra.Presentation.exists_sub_one_mem_map_isRelativeGlobalCompleteIntersection
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation R S ι σ) (I : Ideal R)
    (hI : ∀ (p : Ideal R) [p.IsPrime], I ≤ p → Nontrivial (p.Fiber S) →
      ringKrullDim (p.Fiber S) + ((Nat.card σ : ℕ) : WithBot ℕ∞) =
        ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    ∃ h : P.Ring, algebraMap P.Ring S h - 1 ∈ I.map (algebraMap R S) ∧
      (P.localizationAwayComp h
        (Localization.Away (algebraMap P.Ring S h))).IsRelativeGlobalCompleteIntersection := by
  have := P.finitePresentation_of_isFinite
  have hV : ∀ (q : Ideal S) [q.IsPrime], I.map (algebraMap R S) ≤ q →
      Nat.card σ ≤ Nat.card ι ∧ Algebra.relativeDimensionAt R q ≤
        ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞) := fun q _ hq ↦ by
    have hnt : Nontrivial ((q.under R).Fiber S) :=
      PrimeSpectrum.nonempty_iff_nontrivial.1
        ⟨PrimeSpectrum.primesOverOrderIsoFiber R S (q.under R) ⟨q, ⟨‹_›, ⟨rfl⟩⟩⟩⟩
    obtain ⟨hcn, hd⟩ := WithBot.le_and_eq_tsub_of_add_natCast_eq
      (hI (q.under R) (Ideal.map_le_iff_le_comap.1 hq) hnt)
    exact ⟨hcn, relativeDimensionAt_le_of_ringKrullDim_fiber_eq q _ rfl hd⟩
  by_cases hcn : Nat.card σ ≤ Nat.card ι
  swap
  · have htop : I.map (algebraMap R S) = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      exact hcn (hV m hle).1
    refine ⟨0, by rw [htop]; trivial, ⟨fun p _ hnt ↦ absurd hnt ?_⟩⟩
    rw [not_nontrivial_iff_subsingleton, map_zero]
    have : Subsingleton (Localization.Away (0 : S)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : S)) (Submonoid.mem_powers 0)
    infer_instance
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1
    (Algebra.isOpen_setOf_relativeDimensionAt_le (R := R) (S := S)
      (Nat.card ι - Nat.card σ)).isClosed_compl
  have htop : J ⊔ I.map (algebraMap R S) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmZ : (⟨m, hm.isPrime⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.zeroLocus J :=
      fun x hx ↦ hle (Ideal.mem_sup_left hx)
    rw [← hJ] at hmZ
    exact hmZ (hV m (le_sup_right.trans hle)).2
  obtain ⟨g, hg, i, hi, hgi⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : S) ∈ _)
  obtain ⟨h, rfl⟩ := P.algebraMap_surjective g
  refine ⟨h, by rw [← hgi, sub_add_cancel_left]; exact neg_mem hi,
    P.isRelativeGlobalCompleteIntersection_localizationAwayComp h hcn
      (Algebra.ringKrullDim_fiber_away_le_of_relativeDimensionAt_le _ fun q _ hq ↦ ?_)⟩
  by_contra hlt
  have hqZ : (⟨q, ‹_›⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.zeroLocus J := hJ ▸ hlt
  exact hq (hqZ hg)

/-- Let `S = R[x_1, …, x_n]/(f_1, …, f_c)`, presented by `P`, and let `𝔭` be a
prime of `R` with `dim(S ⊗_R κ(𝔭)) = n - c`. Then there is an `h ∈ R[x_1, …, x_n]` whose image
`g ∈ S` maps to a unit of `S ⊗_R κ(𝔭)`, such that
`S_g = R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)` is a relative global complete
intersection with this presentation. -/
@[stacks 00ST "(2): the fibre `S ⊗_R κ(𝔭)` is `𝔭.Fiber S = κ(𝔭) ⊗_R S`, in which `g` is
`1 ⊗ g`, and `dim = n - c` is written additively as in Definition 00SP. The presentation of `S_g`
is `Algebra.Presentation.localizationAwayComp`."]
theorem Algebra.Presentation.exists_isUnit_fiber_isRelativeGlobalCompleteIntersection
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation R S ι σ) (p : Ideal R) [p.IsPrime]
    (hp : ringKrullDim (p.Fiber S) + ((Nat.card σ : ℕ) : WithBot ℕ∞) =
      ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    ∃ h : P.Ring, IsUnit (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)
        (algebraMap P.Ring S h)) ∧
      (P.localizationAwayComp h
        (Localization.Away (algebraMap P.Ring S h))).IsRelativeGlobalCompleteIntersection := by
  have := P.finitePresentation_of_isFinite
  obtain ⟨hcn, hd⟩ := WithBot.le_and_eq_tsub_of_add_natCast_eq hp
  have hfib : ∀ (q : Ideal S) [q.IsPrime], q.under R = p →
      Algebra.relativeDimensionAt R q ≤ ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞) :=
    fun q _ hqp ↦ by
      exact relativeDimensionAt_le_of_ringKrullDim_fiber_eq q p hqp hd
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1
    (Algebra.isOpen_setOf_relativeDimensionAt_le (R := R) (S := S)
      (Nat.card ι - Nat.card σ)).isClosed_compl
  have htop : J.map (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmZ : (⟨m.comap (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)),
        inferInstance⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.zeroLocus J :=
      fun x hx ↦ hle (Ideal.mem_map_of_mem _ hx)
    rw [← hJ] at hmZ
    exact hmZ (hfib _ (under_comap_includeRight p m))
  have h1 : (1 : p.Fiber S) ∈ J.map (Algebra.TensorProduct.includeRight (R := R)) := by
    rw [htop]
    trivial
  obtain ⟨g, hgJ, hgu⟩ := Ideal.Fiber.exists_mem_isUnit_includeRight_of_one_mem_map p J h1
  obtain ⟨h, rfl⟩ := P.algebraMap_surjective g
  refine ⟨h, hgu, P.isRelativeGlobalCompleteIntersection_localizationAwayComp h hcn
    (Algebra.ringKrullDim_fiber_away_le_of_relativeDimensionAt_le _ fun q _ hq ↦ ?_)⟩
  by_contra hlt
  have hqZ : (⟨q, ‹_›⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.zeroLocus J := hJ ▸ hlt
  exact hq (hqZ hgJ)

/-- Let `S = R[x_1, …, x_n]/(f_1, …, f_c)`, presented by `P`, and let `𝔮` be a
prime of `S` with `dim_𝔮(S/R) = n - c`. Then there is an `h ∈ R[x_1, …, x_n]` whose image `g ∈ S`
is not in `𝔮`, such that
`S_g = R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)` is a relative global complete
intersection with this presentation. -/
@[stacks 00ST "(3): the presentation of `S_g` is `Algebra.Presentation.localizationAwayComp`, the
source's `R[x_1, …, x_n, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)`, and `dim_𝔮(S/R) = n - c` is
`Algebra.relativeDimensionAt R 𝔮 + c = n` (tag 00QD), written additively as in Definition 00SP.
The numbers of variables and relations are `Nat.card ι` and `Nat.card σ`."]
theorem Algebra.Presentation.exists_notMem_isRelativeGlobalCompleteIntersection
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation R S ι σ) (q : Ideal S) [q.IsPrime]
    (hq : Algebra.relativeDimensionAt R q + ((Nat.card σ : ℕ) : WithBot ℕ∞) =
      ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    ∃ h : P.Ring, algebraMap P.Ring S h ∉ q ∧
      (P.localizationAwayComp h
        (Localization.Away (algebraMap P.Ring S h))).IsRelativeGlobalCompleteIntersection := by
  have := P.finitePresentation_of_isFinite
  obtain ⟨hcn, hd⟩ := WithBot.le_and_eq_tsub_of_add_natCast_eq hq
  obtain ⟨g, hg, hfib⟩ := Algebra.exists_notMem_ringKrullDim_fiber_le q hd.le
  obtain ⟨h, rfl⟩ := P.algebraMap_surjective g
  exact ⟨h, hg, P.isRelativeGlobalCompleteIntersection_localizationAwayComp h hcn
    fun p _ ↦ hfib p⟩

/-! ### Transport and presentations -/

/-- Being a relative global complete intersection is invariant under `R`-algebra
isomorphism. -/
theorem Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv {R A B : Type*} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.IsRelativeGlobalCompleteIntersection R A] (e : A ≃ₐ[R] B) :
    Algebra.IsRelativeGlobalCompleteIntersection R B := by
  obtain ⟨n, c, P, hP⟩ := ‹Algebra.IsRelativeGlobalCompleteIntersection R A›.out
  refine ⟨n, c, P.ofAlgEquiv e, ⟨fun p _ hnt ↦ ?_⟩⟩
  let eF : p.Fiber A ≃ₐ[p.ResidueField] p.Fiber B := Algebra.TensorProduct.congr AlgEquiv.refl e
  rw [← ringKrullDim_eq_of_ringEquiv eF.toRingEquiv]
  exact hP.ringKrullDim_fiber_add_card_eq_card p (eF.toEquiv.nontrivial_congr.mpr hnt)

/-- A presentation with finitely many variables and relations which is a relative global complete
intersection exhibits `S` as one. -/
theorem Algebra.IsRelativeGlobalCompleteIntersection.of_presentation {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation R S ι σ) [hP : P.IsRelativeGlobalCompleteIntersection] :
    Algebra.IsRelativeGlobalCompleteIntersection R S := by
  refine ⟨Nat.card ι, Nat.card σ, P.reindex (Finite.equivFin ι).symm (Finite.equivFin σ).symm,
    ⟨fun p _ hnt ↦ ?_⟩⟩
  simpa using hP.ringKrullDim_fiber_add_card_eq_card p hnt

open MvPolynomial in
/-- Given a presentation `S = R[x_i]/I`, `h ∈ R[x_i]` with image `g ∈ S`, and `f_1, …, f_c ∈ I`
with `h I ⊆ (f_1, …, f_c)`, the presentation
`S_g = R[x_i, x_{n+1}]/(f_1, …, f_c, h x_{n+1} - 1)`: in `S_g` the ideal `I` is generated by the
`f_j`. -/
noncomputable def Algebra.Presentation.localizationAwayCompOfMulMem {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {ι σ : Type*} (P : Algebra.Presentation R S ι σ) (h : P.Ring)
    (T : Type*) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalization.Away (algebraMap P.Ring S h) T] {c : ℕ} (f : Fin c → P.Ring)
    (hf : ∀ j, f j ∈ P.ker) (hh : ∀ i, h * P.relation i ∈ Ideal.span (Set.range f)) :
    Algebra.Presentation R T (Unit ⊕ ι) (Unit ⊕ Fin c) where
  toGenerators := (P.localizationAwayComp h T).toGenerators
  relation := Sum.elim (fun _ ↦ rename Sum.inr h * X (Sum.inl ()) - 1)
    fun j ↦ rename Sum.inr (f j)
  span_range_relation_eq_ker := by
    refine Eq.trans ?_ (P.localizationAwayComp h T).span_range_relation_eq_ker
    have hrel : (P.localizationAwayComp h T).relation =
        Sum.elim (fun _ ↦ rename Sum.inr h * X (Sum.inl ()) - 1)
          fun i ↦ rename Sum.inr (P.relation i) := rfl
    have hmap : ∀ x ∈ Ideal.span (Set.range f),
        rename (R := R) Sum.inr x ∈ Ideal.span (Set.range fun j ↦ rename (R := R) Sum.inr (f j)) :=
      fun x hx ↦ by
        have := Ideal.mem_map_of_mem (rename (R := R) (Sum.inr : ι → Unit ⊕ ι)) hx
        rwa [Ideal.map_span, ← Set.range_comp] at this
    rw [hrel, Set.Sum.elim_range, Set.Sum.elim_range, Ideal.span_union, Ideal.span_union]
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have hj := hf j
      rw [← P.span_range_relation_eq_ker] at hj
      have := Ideal.mem_map_of_mem (rename (R := R) (Sum.inr : ι → Unit ⊕ ι)) hj
      rw [Ideal.map_span, ← Set.range_comp] at this
      exact Ideal.mem_sup_right this
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h2 : rename (R := R) Sum.inr (P.relation i) =
          -rename Sum.inr (P.relation i) * (rename Sum.inr h * X (Sum.inl ()) - 1) +
            X (Sum.inl ()) * rename Sum.inr (h * P.relation i) := by
        rw [map_mul]
        ring
      beta_reduce
      rw [SetLike.mem_coe, h2]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨(), rfl⟩))) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _
          (hmap _ (hh i))))

end
