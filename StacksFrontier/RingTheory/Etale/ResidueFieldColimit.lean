module

import StacksFrontier.RingTheory.AdjoinRoot.LocalRing
public import StacksFrontier.RingTheory.Flat.LocalConstruction
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# A separable algebraic residue field extension as a colimit of finite étale extensions

Proof of `IsLocalRing.exists_finiteEtale_directed_residueField_algEquiv` (Stacks Tag 09E0): for a
local ring `(R, 𝔪, k)` and a separable algebraic extension `K / k` there is a local `R`-algebra
`R'` which is the directed union of its finite étale local `R`-subalgebras and whose residue field
is `k`-isomorphic to `K`.

The extension is built by adjoining the elements of `K` one at a time. If `A` is a local
`R`-algebra which is already the directed union of a family `𝒮` of finite étale local
`R`-subalgebras, with residue field embedded in `K` over `k`, and `α : K`, then the minimal
polynomial of `α` over `κ(A)` is separable, and its finitely many coefficients all lie in the
residue field of a single member `S ∈ 𝒮`. Lifting them to `S` gives a monic `p ∈ S[X]` whose
reduction is separable irreducible, so `S[X] ⧸ (p)` is again finite étale and local over `R`, and
`A[X] ⧸ (p) = A ⊗[S] S[X] ⧸ (p)` is the union of the `S'[X] ⧸ (p)` for `S' ∈ 𝒮` above `S`. Thus the
invariant is preserved by a monogenic step, it is preserved by directed colimits, and a transfinite
assembly of such steps reaches a stage whose residue field is all of `K`.

## Main results

* `Stacks.Etale.ResidueFieldColimit.solution`: the statement of Stacks Tag 09E0.

## Implementation notes

*Why the flat extension of [StacksProject 03C3] is not enough.* The source runs the transfinite
recursion of 03C3 and observes that in the separable algebraic case every transition map is finite
étale. That is a statement about the *construction*, not about the flat local extension 03C3
produces: a flat local extension `R ⊆ R'` with `𝔪 R' = 𝔪'` and residue field `K` need not be
covered by finite étale subalgebras, because an element of `R'` whose residue is algebraic over `k`
need not be integral over `R`. So 09E0 is proved by rerunning the recursion with the stronger
invariant, not by post-processing 03C3.

*Why the recursion cannot be replaced by a single filtered colimit.* One would like to index the
system by the finite subextensions `L / k` of `K / k`, or by the pairs `(p, α)` with `p ∈ R[X]`
monic lifting the minimal polynomial of `α : K`. Neither is a directed system, and not for lack of
a clever index: for `R = ℤ_(5)` the algebras `S₁ = R[X] ⧸ (X ^ 2 - 2)` and
`S₂ = R[X] ⧸ (X ^ 2 - 3)` are both finite étale and local, with residue field `𝔽_25` (both `2` and
`3` are nonsquares mod `5`), yet no finite étale local `R`-algebra `T` receives both. Indeed such a
`T` would have `√2, √3 ∈ T`, hence a fraction field containing `ℚ(√2, √3)`, and `5` would be inert
in it, so its Galois closure would have a cyclic decomposition group at `5` surjecting onto
`Gal(ℚ(√2, √3) / ℚ) = (ℤ/2) ^ 2`, which is impossible. The lift of the minimal polynomial at each
step must therefore be chosen over the *previous stage* — over `S₁` the element `√3` is already in
the residue field, so nothing has to be adjoined — and that is what makes the index a well-ordered
chain of choices rather than a poset defined in advance. The same example shows that a finite étale
algebra over a local ring is *not* in general a finite product of local rings (`S₁ ⊗[R] S₂` is a
domain with two maximal ideals), so locality of the members of `𝒮` is genuine data.

*Monogenic étale algebras.* `etale_adjoinRoot` is the case `g = f'` of Mathlib's standard étale
algebras `R[X][1/g] ⧸ (f)`: when `f'` is already a unit in `R[X] ⧸ (f)` no localization is needed
and the standard étale algebra is `AdjoinRoot f` itself. Over a local ring `A` this applies to
every monic `p` whose reduction `p̄ ∈ κ(A)[X]` is separable *and irreducible*: irreducibility makes
`AdjoinRoot p` local with `𝔪 · AdjoinRoot p` for its maximal ideal, so `p'` is a unit there as soon
as it is nonzero in the residue field `κ(A)[X] ⧸ (p̄)`, which is what separability gives. Both
hypotheses hold at each step of the construction, `p̄` being the minimal polynomial of an element
of `K` over the current residue field.

## References

* [StacksProject 09E0](https://stacks.math.columbia.edu/tag/09E0)
* [StacksProject 03C3](https://stacks.math.columbia.edu/tag/03C3)
-/

@[expose] public section

open Polynomial IsLocalRing

namespace Stacks.Etale.ResidueFieldColimit



/-- **A monogenic algebra with invertible derivative is étale.** If `p : A[X]` is monic and the
derivative of `p` is a unit in `AdjoinRoot p`, then `AdjoinRoot p` is étale over `A`.

This is the standard étale algebra `A[X][1/g] ⧸ (p)` of the pair `(p, derivative p)`, whose
localization is trivial because `derivative p` is already invertible. -/
@[ega "IV 18.4.3" "(F)"]
theorem etale_adjoinRoot {A : Type*} [CommRing A] {p : A[X]} (hp : p.Monic)
    (hu : IsUnit (AdjoinRoot.mk p (derivative p))) : Algebra.Etale A (AdjoinRoot p) :=
  let P : StandardEtalePair A := ⟨p, hp, derivative p, ⟨1, 0, 1, by ring⟩⟩
  Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot p)
      (Localization.Away (AdjoinRoot.mk p (derivative p))) _ hu).restrictScalars A).symm)

section Monogenic

variable {A : Type u} [CommRing A] [IsLocalRing A] {p : A[X]}

/-- **The derivative is invertible in a monogenic algebra with separable irreducible reduction.**
If `AdjoinRoot p` is local and the reduction `p̄` of `p` is irreducible and separable, then
`derivative p` is a unit in `AdjoinRoot p`: otherwise it lies in the maximal ideal
`𝔪 · AdjoinRoot p`, so `p̄ ∣ derivative p̄` in `κ(A)[X]`, and coprimality of `p̄` with
`derivative p̄` would make `p̄` a unit. -/
private theorem isUnit_mk_derivative (hirr : Irreducible (p.map (residue A)))
    (hsep : (p.map (residue A)).Separable) [IsLocalRing (AdjoinRoot p)] :
    IsUnit (AdjoinRoot.mk p (derivative p)) := by
  by_contra hu
  have hmem : AdjoinRoot.mk p (derivative p) ∈ (maximalIdeal A).map (AdjoinRoot.of p) := by
    rw [← AdjoinRoot.maximalIdeal_eq_map_maximalIdeal hirr]
    exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
  have h0 : (Ideal.Quotient.mk ((maximalIdeal A).map (AdjoinRoot.of p)))
      (AdjoinRoot.mk p (derivative p)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have key := AdjoinRoot.quotEquivQuotMap_apply_mk p (derivative p) (maximalIdeal A)
  rw [h0, map_zero] at key
  have hdvd : p.map (residue A) ∣ (derivative p).map (residue A) := by
    rw [← Ideal.mem_span_singleton]
    exact Ideal.Quotient.eq_zero_iff_mem.mp key.symm
  have hc : IsCoprime (p.map (residue A)) (derivative (p.map (residue A))) := hsep
  rw [Polynomial.derivative_map] at hc
  exact hirr.not_isUnit (hc.isUnit_of_dvd' dvd_rfl hdvd)

/-- **A monogenic algebra with separable irreducible reduction over a local ring is étale.** -/
theorem etale_adjoinRoot_of_separable (hp : p.Monic)
    (hirr : Irreducible (p.map (residue A))) (hsep : (p.map (residue A)).Separable)
    [IsLocalRing (AdjoinRoot p)] : Algebra.Etale A (AdjoinRoot p) :=
  etale_adjoinRoot hp (isUnit_mk_derivative hirr hsep)

end Monogenic

/-- **The monogenic step of the construction.** Let `S` be a local ring which is a finite étale
`R`-algebra with `R → S` local, and let `q ∈ S[X]` be monic with irreducible separable
reduction in `κ(S)[X]` — for instance a lift of the minimal polynomial over `κ(S)` of a separable
algebraic element. Then `AdjoinRoot q` is again a local ring, finite étale over `R`, and local
over `R`. -/
@[ega "0 10.3.1.2" "(F), (F), special case",
  sga "1 I 7.5" "special case",
  sga "3 VIIB 1.6" "(F), (F), special case",
  sga "3 XXIV 3.9.1" "partial"]
private theorem finiteEtale_adjoinRoot_of_separable {R : Type*} [CommRing R] {S : Type*}
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [Algebra.Etale R S] {q : S[X]} (hq : q.Monic)
    (hirr : Irreducible (q.map (residue S))) (hsep : (q.map (residue S)).Separable) :
    ∃ _ : IsLocalRing (AdjoinRoot q), Module.Finite R (AdjoinRoot q) ∧
      Algebra.Etale R (AdjoinRoot q) ∧ IsLocalHom (algebraMap R (AdjoinRoot q)) := by
  have hloc : IsLocalRing (AdjoinRoot q) :=
    AdjoinRoot.isLocalRing_of_irreducible_map_residue hq hirr
  have : Module.Finite S (AdjoinRoot q) := hq.finite_adjoinRoot
  have : Algebra.Etale S (AdjoinRoot q) := etale_adjoinRoot_of_separable hq hirr hsep
  have : IsLocalHom (algebraMap S (AdjoinRoot q)) := by
    rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.isLocalHom_of_monic hq
  refine ⟨hloc, Module.Finite.trans S _, Algebra.Etale.comp R S _, ?_⟩
  rw [IsScalarTower.algebraMap_eq R S (AdjoinRoot q)]
  exact RingHom.isLocalHom_comp _ _

/-! ### Rings covered by finite étale local subalgebras -/

/-- **A ring covered by finite étale local subalgebras.** `IsFinEtaleUnion R A` says that every
finite subset of the `R`-algebra `A` lies in an `R`-subalgebra `S` which is finite étale over `R`,
is a local ring, and whose inclusion into `A` is a local ring map (a unit of `A` lying in `S` is a
unit of `S`).

This is the invariant carried through the construction. It is equivalent to `A` being the directed
union of its finite étale local `R`-subalgebras (`IsFinEtaleUnion.exists_directed_family`); the
locality of the inclusions is extra data, needed to compare residue fields at a step, and is
discarded at the end. -/
private def IsFinEtaleUnion (R : Type*) (A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    Prop :=
  ∀ E : Finset A, ∃ S : Subalgebra R A, (↑E : Set A) ⊆ (S : Set A) ∧ Module.Finite R S ∧
    Algebra.Etale R S ∧ IsLocalRing S ∧ ∀ x : S, IsUnit (x : A) → IsUnit x

/-- If `t` spans `S` as a module and `f '' t ⊆ T`, the algebra map `f` sends all of `S` into the
subalgebra `T`. -/
private theorem apply_mem_of_image_subset {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (f : S →ₐ[R] B) {t : Set S} (ht : Submodule.span R t = ⊤)
    {T : Subalgebra R B} (hT : f '' t ⊆ T) (x : S) : f x ∈ T :=
  (Submodule.span_le.mpr hT : Submodule.span R (f '' t) ≤ Subalgebra.toSubmodule T)
    (Submodule.apply_mem_span_image_of_mem_span f.toLinearMap (ht ▸ Submodule.mem_top))

/-- A subalgebra which is finite as a module is contained in every subalgebra containing a suitable
finite subset of it, namely a finite set of module generators. -/
private theorem Subalgebra.exists_finset_le_of_finite {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (S : Subalgebra R A) [Module.Finite R S] :
    ∃ E : Finset A, ∀ T : Subalgebra R A, (↑E : Set A) ⊆ (T : Set A) → S ≤ T := by
  classical
  obtain ⟨t, ht⟩ := (Module.finite_def.mp inferInstance : (⊤ : Submodule R S).FG)
  exact ⟨t.image (Subalgebra.val S), fun T hT x hx =>
    apply_mem_of_image_subset (Subalgebra.val S) ht (by rwa [Finset.coe_image] at hT) ⟨x, hx⟩⟩

/-- **The finite étale local subalgebras of such a ring form a directed family covering it.** The
family is directed because a member is generated as a module by finitely many elements, and those
finitely many elements lie in a common member. -/
private theorem IsFinEtaleUnion.exists_directed_family {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (h : IsFinEtaleUnion R A) :
    ∃ 𝒮 : Set (Subalgebra R A), DirectedOn (· ≤ ·) 𝒮 ∧ (∀ x : A, ∃ S ∈ 𝒮, x ∈ S) ∧
      ∀ S ∈ 𝒮, Module.Finite R S ∧ Algebra.Etale R S ∧ IsLocalRing S := by
  classical
  refine ⟨{S : Subalgebra R A | Module.Finite R S ∧ Algebra.Etale R S ∧ IsLocalRing S},
    ?_, ?_, fun S hS => hS⟩
  · rintro S₁ ⟨f₁, -, -⟩ S₂ ⟨f₂, -, -⟩
    have := f₁; have := f₂
    obtain ⟨E₁, hE₁⟩ := Subalgebra.exists_finset_le_of_finite S₁
    obtain ⟨E₂, hE₂⟩ := Subalgebra.exists_finset_le_of_finite S₂
    obtain ⟨S, hSsub, hfin, het, hloc, -⟩ := h (E₁ ∪ E₂)
    refine ⟨S, ⟨hfin, het, hloc⟩, hE₁ S fun x hx => ?_, hE₂ S fun x hx => ?_⟩
    · exact hSsub (by rw [Finset.coe_union]; exact Or.inl hx)
    · exact hSsub (by rw [Finset.coe_union]; exact Or.inr hx)
  · intro x
    obtain ⟨S, hSsub, hfin, het, hloc, -⟩ := h {x}
    exact ⟨S, ⟨hfin, het, hloc⟩, hSsub (by simp)⟩

/-- **The range of an injective algebra map from a finite étale local ring.** It is a finite étale
local subalgebra of the target whose inclusion is a local ring map, as soon as the map itself is
one: the range is isomorphic to the source by `AlgEquiv.ofInjective`. -/
private theorem exists_subalgebra_range {R T B : Type*} [CommRing R] [CommRing T] [CommRing B]
    [Algebra R T] [Algebra R B] [Module.Finite R T] [Algebra.Etale R T] [IsLocalRing T]
    (f : T →ₐ[R] B) (hf : Function.Injective f) (hloc : ∀ x : T, IsUnit (f x) → IsUnit x) :
    ∃ S : Subalgebra R B, Set.range f ⊆ (S : Set B) ∧ Module.Finite R S ∧ Algebra.Etale R S ∧
      IsLocalRing S ∧ ∀ x : S, IsUnit (x : B) → IsUnit x := by
  set e : T ≃ₐ[R] f.range := AlgEquiv.ofInjective f hf with he
  have : Nontrivial f.range := ⟨⟨e 0, e 1, fun h => zero_ne_one (e.injective h)⟩⟩
  refine ⟨f.range, fun x hx => hx, Module.Finite.equiv e.toLinearEquiv,
    Algebra.Etale.of_equiv e, IsLocalRing.of_surjective' (e : T →+* f.range) e.surjective,
    fun x hx => ?_⟩
  have hval : ((e (e.symm x) : f.range) : B) = f (e.symm x) := rfl
  have h1 : IsUnit (f (e.symm x)) := by rw [← hval, e.apply_symm_apply]; exact hx
  have h2 : IsUnit (e (e.symm x)) := (hloc _ h1).map (e : T →+* f.range)
  rwa [e.apply_symm_apply] at h2

/-- **The cover property is inherited by a monogenic étale extension.** Let `A` be a local
`R`-algebra with `R → A` local which is covered by its finite étale local `R`-subalgebras, and let
`p ∈ A[X]` be monic with irreducible separable reduction in `κ(A)[X]`. Then `AdjoinRoot p` is
covered by its finite étale local `R`-subalgebras as well.

This is the base-change step of the source's induction. The finitely many coefficients of `p` and
of polynomial representatives of a given finite subset of `AdjoinRoot p` all lie in a single member
`S` of the family, so `p` descends to a monic `q ∈ S[X]`; the reduction of `q` stays irreducible
(it is irreducible over the larger field `κ(A)`, and `q` is monic) and separable, so `AdjoinRoot q`
is a finite étale local `R`-algebra, and it maps injectively into `AdjoinRoot p` — a monic division
computation — with the given finite subset inside its image. -/
private theorem isFinEtaleUnion_adjoinRoot {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    (hA : IsFinEtaleUnion R A) {p : A[X]} (hp : p.Monic)
    (hirr : Irreducible (p.map (residue A))) (hsep : (p.map (residue A)).Separable) :
    IsFinEtaleUnion R (AdjoinRoot p) := by
  classical
  have hlocp : IsLocalRing (AdjoinRoot p) :=
    AdjoinRoot.isLocalRing_of_irreducible_map_residue hp hirr
  have hmaxp : maximalIdeal (AdjoinRoot p) = (maximalIdeal A).map (AdjoinRoot.of p) :=
    AdjoinRoot.maximalIdeal_eq_map_maximalIdeal hirr
  intro E
  choose rep hrep using AdjoinRoot.mk_surjective (g := p)
  obtain ⟨S, hSG, hSfin, hSet, hSloc, hSunit⟩ :=
    hA (p.coeffs ∪ E.biUnion fun z => (rep z).coeffs)
  have := hSfin; have := hSet; have := hSloc
  set j : S →+* A := algebraMap S A with hj
  have hjloc : IsLocalHom j := ⟨fun x hx => hSunit x hx⟩
  have hjinj : Function.Injective j := fun _ _ hxy => Subtype.ext hxy
  have hRS : IsLocalHom (algebraMap R S) := by
    refine ⟨fun r hr => ?_⟩
    refine isUnit_of_map_unit (algebraMap R A) r ?_
    rw [IsScalarTower.algebraMap_apply R S A]
    exact hr.map j
  -- polynomials with coefficients in `S` are exactly the ones lifting to `S[X]`
  have hlift : ∀ F : A[X], (↑F.coeffs : Set A) ⊆ (S : Set A) → F ∈ Polynomial.lifts j := by
    intro F hF
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h0 : F.coeff n = 0
    · exact ⟨0, by rw [h0]; exact map_zero j⟩
    · exact ⟨⟨F.coeff n, hF (Polynomial.coeff_mem_coeffs h0)⟩, rfl⟩
  -- descend `p` to a monic `q ∈ S[X]`
  obtain ⟨q, hqmap, -, hqmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (hlift p fun x hx => hSG (by rw [Finset.coe_union]; exact Or.inl hx)) hp
  -- the reduction of `q` over `κ(S)` is irreducible and separable
  have hres : (ResidueField.map j).comp (residue S) = (residue A).comp j :=
    RingHom.ext fun x => ResidueField.map_residue j x
  have hqbar : (q.map (residue S)).map (ResidueField.map j) = p.map (residue A) := by
    rw [Polynomial.map_map, hres, ← Polynomial.map_map, hqmap]
  have hqirr : Irreducible (q.map (residue S)) :=
    Polynomial.Monic.irreducible_of_irreducible_map (ResidueField.map j) _
      (hqmonic.map _) (by rw [hqbar]; exact hirr)
  have hqsep : (q.map (residue S)).Separable :=
    (Polynomial.separable_map (ResidueField.map j)).mp (by rw [hqbar]; exact hsep)
  obtain ⟨hlocq, hfinq, hetq, hlhq⟩ :=
    finiteEtale_adjoinRoot_of_separable (R := R) (S := S) hqmonic hqirr hqsep
  have := hlocq; have := hfinq; have := hetq; have := hlhq
  -- the induced map `AdjoinRoot q → AdjoinRoot p`
  have hroot : Polynomial.eval₂ ((AdjoinRoot.of p).comp j) (AdjoinRoot.root p) q = 0 := by
    rw [← Polynomial.eval₂_map, hqmap]
    exact AdjoinRoot.eval₂_root p
  set ψ : AdjoinRoot q →+* AdjoinRoot p :=
    AdjoinRoot.lift ((AdjoinRoot.of p).comp j) (AdjoinRoot.root p) hroot with hψ
  have hψmk : ∀ F : S[X], ψ (AdjoinRoot.mk q F) = AdjoinRoot.mk p (F.map j) := by
    intro F
    rw [hψ, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
      ← Polynomial.aeval_def]
    exact AdjoinRoot.aeval_eq _
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).mpr fun x hx => ?_
    obtain ⟨F, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [hψmk] at hx
    have h1 : (F %ₘ q).map j = 0 := by
      rw [Polynomial.map_modByMonic j hqmonic, hqmap,
        (Polynomial.modByMonic_eq_zero_iff_dvd hp).mpr (AdjoinRoot.mk_eq_zero.mp hx)]
    exact AdjoinRoot.mk_eq_zero.mpr ((Polynomial.modByMonic_eq_zero_iff_dvd hqmonic).mp
      (Polynomial.map_injective j hjinj (by simpa using h1)))
  have hψof : ψ.comp (AdjoinRoot.of q) = (AdjoinRoot.of p).comp j :=
    RingHom.ext fun a => by rw [RingHom.comp_apply, hψ, AdjoinRoot.lift_of]
  have hψalg : ∀ r : R, ψ (algebraMap R (AdjoinRoot q) r) = algebraMap R (AdjoinRoot p) r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R S (AdjoinRoot q), AdjoinRoot.algebraMap_eq,
      IsScalarTower.algebraMap_apply R A (AdjoinRoot p), AdjoinRoot.algebraMap_eq,
      ← RingHom.comp_apply, hψof, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply R S A]
  have hψloc : IsLocalHom ψ := by
    refine ((IsLocalRing.local_hom_TFAE ψ).out 3 1).mp ?_
    rw [AdjoinRoot.maximalIdeal_eq_map_maximalIdeal hqirr, Ideal.map_map, hψof, hmaxp,
      ← Ideal.map_map]
    exact Ideal.map_mono (((IsLocalRing.local_hom_TFAE j).out 1 3).mp hjloc)
  -- the image of `AdjoinRoot q` is the required subalgebra
  obtain ⟨S', hS'range, hS'fin, hS'et, hS'loc, hS'unit⟩ :=
    exists_subalgebra_range (AlgHom.mk ψ hψalg) hψinj (fun x hx => isUnit_of_map_unit ψ x hx)
  refine ⟨S', fun z hz => ?_, hS'fin, hS'et, hS'loc, hS'unit⟩
  have hzc : (↑(rep z).coeffs : Set A) ⊆ (S : Set A) := fun x hx =>
    hSG (by
      rw [Finset.coe_union]
      exact Or.inr (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
        ⟨z, Finset.mem_coe.mp hz, Finset.mem_coe.mp hx⟩)))
  obtain ⟨G, hG⟩ := (Polynomial.mem_lifts _).mp (hlift _ hzc)
  exact hS'range ⟨AdjoinRoot.mk q G, by rw [show (AlgHom.mk ψ hψalg) (AdjoinRoot.mk q G)
    = ψ (AdjoinRoot.mk q G) from rfl, hψmk, hG, hrep]⟩

/-! ### Injectivity of the transition maps -/

/-- **A local map between étale algebras over a common base is injective.** If `S` and `T` are
étale `R`-algebras which are local rings and `f : S →ₐ[R] T` reflects units, then `f` is injective:
`T` is étale over `S` by `Algebra.Etale.of_restrictScalars`, hence flat, hence faithfully flat
because `f` is a local ring map, and a faithfully flat ring map is injective. -/
private theorem injective_of_etale_of_isLocalHom {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra.Etale R S] [Algebra.Etale R T]
    [IsLocalRing S] [IsLocalRing T] (f : S →ₐ[R] T) (hf : ∀ x : S, IsUnit (f x) → IsUnit x) :
    Function.Injective f := by
  let : Algebra S T := (f : S →+* T).toAlgebra
  have ham : (algebraMap S T) = (f : S →+* T) := RingHom.algebraMap_toAlgebra _
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => by
    rw [ham]; exact (f.commutes r).symm
  have : Algebra.Etale S T := Algebra.Etale.of_restrictScalars R S T
  have : Module.Flat S T := Algebra.WeaklyEtale.flat
  have hlh : IsLocalHom (algebraMap S T) := ⟨fun x hx => hf x (by rwa [ham] at hx)⟩
  have hff : Module.FaithfullyFlat S T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have := ((RingHom.faithfullyFlat_algebraMap_iff (R := S) (S := T)).mpr hff).injective
  rwa [ham] at this

/-- **A unit-reflecting map from a finite étale local algebra into a ring covered by finite étale
local subalgebras is injective.** The images of finitely many module generators of `S` lie in a
single member `T` of the covering family, so the map factors through `T`, where
`injective_of_etale_of_isLocalHom` applies. -/
private theorem injective_of_isFinEtaleUnion {R S B : Type*} [CommRing R] [CommRing S]
    [CommRing B] [Algebra R S] [Algebra R B] [Module.Finite R S] [Algebra.Etale R S]
    [IsLocalRing S] (hB : IsFinEtaleUnion R B) (f : S →ₐ[R] B)
    (hf : ∀ x : S, IsUnit (f x) → IsUnit x) : Function.Injective f := by
  classical
  obtain ⟨t, ht⟩ := (Module.finite_def.mp inferInstance : (⊤ : Submodule R S).FG)
  obtain ⟨T, hTsub, hTfin, hTet, hTloc, hTunit⟩ := hB (t.image f)
  have hrange : ∀ x : S, f x ∈ T :=
    apply_mem_of_image_subset f ht (by rwa [Finset.coe_image] at hTsub)
  have := hTfin; have := hTet; have := hTloc
  have hg : Function.Injective (AlgHom.codRestrict f T hrange) :=
    injective_of_etale_of_isLocalHom _ fun x hx => hf x (hx.map (Subalgebra.val T))
  exact fun x y hxy => hg (Subtype.ext hxy)

/-- The cover property depends on the algebra structure only through its structure map. -/
private theorem isFinEtaleUnion_of_algebraMap_eq {R B : Type*} [CommRing R] [CommRing B]
    (i₁ i₂ : Algebra R B) (h : ∀ r, @algebraMap R B _ _ i₁ r = @algebraMap R B _ _ i₂ r)
    (H : @IsFinEtaleUnion R B _ _ i₁) : @IsFinEtaleUnion R B _ _ i₂ := by
  have : i₁ = i₂ := Algebra.algebra_ext _ _ h
  subst this
  exact H

/-- **A local ring is covered by its finite étale local subalgebras over itself.** -/
private theorem isFinEtaleUnion_self (R : Type*) [CommRing R] [IsLocalRing R] :
    IsFinEtaleUnion R R := by
  intro E
  obtain ⟨S, hr, hfin, het, hloc, hun⟩ :=
    exists_subalgebra_range (R := R) (T := R) (B := R) (AlgHom.id R R) Function.injective_id
      fun x hx => hx
  exact ⟨S, fun x _ => hr ⟨x, rfl⟩, hfin, het, hloc, hun⟩

/-! ### The category of étale lifts, and the transfinite assembly

The transfinite recursion of the source is run as Mathlib's transfinite iteration of a successor
structure (`CategoryTheory.SmallObject.SuccStruct.iterationFunctor`): a hand-rolled well-founded
recursion cannot express it, because the transition maps at a stage have types depending on the
stages below. Étale lifts are therefore organized into a category, in which a directed system is
a functor (so the cocycle is functoriality) and the colimit engine of
[StacksProject 03C3]'s infrastructure provides the colimits of well-ordered shape.
-/

section Assembly

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

/-- An **étale lift of `A` towards `F`**: a good lift of `A` towards `F` — a flat local
`A`-algebra `B` with `𝔪_B = 𝔪_A B` together with a `κ(A)`-embedding `κ(B) → F` — whose carrier
is moreover a directed union of its finite étale local `A`-subalgebras.

This is the bookkeeping object of the assembly: `A` itself is an étale lift
(`etLift_trivial`), the monogenic step `exists_etaleStep` enlarges one, directed colimits of
étale lifts are étale lifts (`hasColimit_of_directed`), and an étale lift whose residue
embedding is onto `F` is the ring the theorem asks for. -/
private structure EtLift (A : Type w) [CommRing A] [IsLocalRing A] (F : Type w) [Field F]
    [Algebra (ResidueField A) F] where
  /-- the underlying good lift of [StacksProject 03C3] -/
  gl : GoodLift A F
  /-- the carrier is covered by its finite étale local `A`-subalgebras -/
  cover : letI : Algebra A gl.carrier := gl.φ.toAlgebra; IsFinEtaleUnion A gl.carrier

variable {A : Type w} [CommRing A] [IsLocalRing A] {F : Type w} [Field F]
  [Algebra (ResidueField A) F]

/-- A morphism of étale lifts: a local ring map of the carriers which extends the maximal ideal,
commutes with the structure maps and is compatible with the embeddings into `F`. Neither
flatness nor injectivity is required of a morphism: both hold automatically
(`ELHom.injective`), and demanding them would obstruct the descent of a colimit cocone. -/
private structure ELHom (g h : EtLift A F) : Type w where
  /-- the underlying ring map of carriers -/
  ψ : g.gl.carrier →+* h.gl.carrier
  /-- the ring map is local -/
  isLocal : IsLocalHom ψ
  /-- the maximal ideal of the target is generated by the image of the maximal ideal -/
  maxeq : maximalIdeal h.gl.carrier = Ideal.map ψ (maximalIdeal g.gl.carrier)
  /-- the ring map commutes with the structure maps from `A` -/
  φcomp : ψ.comp g.gl.φ = h.gl.φ
  /-- the induced map of residue fields is compatible with the embeddings into `F` -/
  ιcomp : h.gl.ι.comp (@ResidueField.map _ _ _ _ _ _ ψ isLocal) = g.gl.ι

/-- Two morphisms of étale lifts with the same underlying ring map are equal. -/
private theorem ELHom.ext' {g h : EtLift A F} {f₁ f₂ : ELHom g h} (H : f₁.ψ = f₂.ψ) :
    f₁ = f₂ := by
  cases f₁; cases f₂; subst H; rfl

/-- Étale lifts of `A` towards `F` form a category, with `ELHom` for its morphisms. -/
@[instance_reducible] private def catEtLift : Category.{w} (EtLift A F) where
  Hom g h := ELHom g h
  id g :=
    { ψ := RingHom.id g.gl.carrier
      isLocal := ⟨fun _ ha => ha⟩
      maxeq := by rw [Ideal.map_id]
      φcomp := RingHom.id_comp _
      ιcomp := by rw [IsLocalRing.ResidueField.map_id, RingHom.comp_id] }
  comp {g h l} f₁ f₂ :=
    { ψ := f₂.ψ.comp f₁.ψ
      isLocal := by
        have := f₁.isLocal; have := f₂.isLocal; exact RingHom.isLocalHom_comp _ _
      maxeq := by rw [f₂.maxeq, f₁.maxeq, Ideal.map_map]
      φcomp := by rw [RingHom.comp_assoc, f₁.φcomp, f₂.φcomp]
      ιcomp := by
        have := f₁.isLocal; have := f₂.isLocal
        rw [IsLocalRing.ResidueField.map_comp f₁.ψ f₂.ψ, ← RingHom.comp_assoc, f₂.ιcomp,
          f₁.ιcomp] }
  id_comp _ := ELHom.ext' (RingHom.comp_id _)
  comp_id _ := ELHom.ext' (RingHom.id_comp _)
  assoc _ _ _ := ELHom.ext' (RingHom.comp_assoc _ _ _).symm

attribute [local instance] catEtLift

/-- **A morphism of étale lifts is injective.** An element of the kernel lies in a finite étale
local `A`-subalgebra `S` of the source, and the composite `S → h` is a unit-reflecting map from a
finite étale local `A`-algebra into a ring covered by its finite étale local `A`-subalgebras,
hence injective by `injective_of_isFinEtaleUnion`. -/
private theorem ELHom.injective {g h : EtLift A F} (f : ELHom g h) : Function.Injective f.ψ := by
  classical
  let : Algebra A g.gl.carrier := g.gl.φ.toAlgebra
  let : Algebra A h.gl.carrier := h.gl.φ.toAlgebra
  have hfl := f.isLocal
  have halg : ∀ r : A, f.ψ (algebraMap A g.gl.carrier r)
      = algebraMap A h.gl.carrier r := fun r => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply, f.φcomp]
  refine (injective_iff_map_eq_zero f.ψ).mpr fun x hx => ?_
  obtain ⟨S, hSsub, hSfin, hSet, hSloc, hSunit⟩ := g.cover {x}
  have hxS : x ∈ S := hSsub (by simp)
  have := hSfin; have := hSet; have := hSloc
  set fS : S →ₐ[A] h.gl.carrier :=
    { toRingHom := f.ψ.comp (Subalgebra.val S).toRingHom
      commutes' := fun r => halg r } with hfS
  have hinj : Function.Injective fS :=
    injective_of_isFinEtaleUnion h.cover fS fun z hz => hSunit z (isUnit_of_map_unit f.ψ _ hz)
  have h0 : fS ⟨x, hxS⟩ = fS 0 := by simpa [hfS] using hx
  exact congrArg Subtype.val (hinj h0)

/-- A morphism of étale lifts enlarges the subfield of `F` cut out by the residue embedding. -/
private theorem range_ι_subset {g h : EtLift A F} (f : ELHom g h) :
    Set.range g.gl.ι ⊆ Set.range h.gl.ι := by
  rintro x ⟨y, rfl⟩
  refine ⟨@ResidueField.map _ _ _ _ _ _ f.ψ f.isLocal y, ?_⟩
  have := congrArg (fun (r : ResidueField g.gl.carrier →+* F) => r y) f.ιcomp
  simpa using this

/-- Isomorphic étale lifts cut out the same subfield of `F`. -/
private theorem range_ι_eq_of_iso {g h : EtLift A F} (e : g ≅ h) :
    Set.range g.gl.ι = Set.range h.gl.ι :=
  Set.Subset.antisymm (range_ι_subset e.hom) (range_ι_subset e.inv)

/-- **The legs of a directed colimit of rings with injective transition maps are injective.** The
colimit is described by its universal property, so it maps to Mathlib's `Ring.DirectLimit` of the
same system compatibly with the legs, and the legs of that direct limit are injective. -/
private theorem injective_of_universal {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]
    (G : I → Type w) [∀ i, CommRing (G i)] (t : ∀ i j, i ≤ j → G i →+* G j)
    (ht_id : ∀ i, t i i (le_refl i) = RingHom.id (G i))
    (ht_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      (t j k hjk).comp (t i j hij) = t i k (le_trans hij hjk))
    (htinj : ∀ i j (hij : i ≤ j), Function.Injective (t i j hij))
    {B : Type w} [CommRing B] (s : ∀ i, G i →+* B)
    (huniv : ∀ (T : Type w) [CommRing T] (τ : ∀ i, G i →+* T),
      (∀ i j (hij : i ≤ j), (τ j).comp (t i j hij) = τ i) →
        ∃ h : B →+* T, ∀ i, h.comp (s i) = τ i) :
    ∀ i, Function.Injective (s i) := by
  have hDS : DirectedSystem G (fun i j hij => (t i j hij : G i → G j)) :=
    ⟨fun a x ↦ DFunLike.congr_fun (ht_id a) x,
      fun _ _ _ hab hbc x ↦ DFunLike.congr_fun (ht_comp _ _ _ hab hbc) x⟩
  obtain ⟨θ, hθ⟩ := huniv (Ring.DirectLimit G (fun i j hij => (t i j hij : G i → G j)))
    (fun i => Ring.DirectLimit.of G (fun i j hij => (t i j hij : G i → G j)) i)
    (fun i j hij => RingHom.ext fun x => Ring.DirectLimit.of_f hij x)
  intro i x y hxy
  have h2 : ∀ z : G i, θ (s i z)
      = Ring.DirectLimit.of G (fun i j hij => (t i j hij : G i → G j)) i z :=
    fun z => DFunLike.congr_fun (hθ i) z
  exact Ring.DirectLimit.of_injective t htinj i (by rw [← h2, ← h2, hxy])

/-- **Colimits of directed systems of étale lifts.** A functor from a directed nonempty preorder
to étale lifts has a colimit: its carrier is the colimit ring of the carriers, by the engine
`goodLift_colimit_chosen_noflat`.

Two facts are added to the good-lift colimit. Its legs are injective: the transition maps are
(`ELHom.injective`), so the legs of Mathlib's `Ring.DirectLimit` are, and the colimit maps to
that direct limit compatibly with the legs by the universal property. And its carrier is covered
by its finite étale local `A`-subalgebras: a finite subset of the colimit comes from a single
stage `M`, hence lies in a finite étale local `A`-subalgebra `S` of that stage, and the image of
`S` in the colimit is such a subalgebra, the leg at `M` being injective and local. -/
private theorem hasColimit_of_directed {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] (D : I ⥤ EtLift A F) : HasColimit D := by
  classical
  have ht_id : ∀ i, (D.map (homOfLE (le_refl i))).ψ = RingHom.id (D.obj i).gl.carrier := by
    intro i; rw [show homOfLE (le_refl i) = 𝟙 i from rfl, D.map_id]; rfl
  have ht_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      ((D.map (homOfLE hjk)).ψ).comp ((D.map (homOfLE hij)).ψ)
        = (D.map (homOfLE (le_trans hij hjk))).ψ := by
    intro i j k hij hjk
    rw [show homOfLE (le_trans hij hjk) = homOfLE hij ≫ homOfLE hjk from rfl, D.map_comp]; rfl
  obtain ⟨ub, s, hsl, hcoc, hmax, hphi, hiota, hexh, huniv⟩ :=
    goodLift_colimit_chosen_noflat (fun i => (D.obj i).gl)
      (fun i j hij => (D.map (homOfLE hij)).ψ) ht_id ht_comp
      (fun i j hij => (D.map (homOfLE hij)).isLocal)
      (fun i j hij => (D.map (homOfLE hij)).φcomp)
      (fun i j hij => (D.map (homOfLE hij)).ιcomp)
  -- the legs of the colimit are injective, the transition maps being so
  have hsinj : ∀ i, Function.Injective (s i) :=
    injective_of_universal (fun i => (D.obj i).gl.carrier)
      (fun i j hij => (D.map (homOfLE hij)).ψ) ht_id ht_comp
      (fun i j hij => ELHom.injective _) s huniv
  -- the colimit is covered by its finite étale local `A`-subalgebras
  have hcover : letI : Algebra A ub.carrier := ub.φ.toAlgebra; IsFinEtaleUnion A ub.carrier := by
    let : Algebra A ub.carrier := ub.φ.toAlgebra
    intro E
    obtain ⟨M, hM⟩ := Finset.exists_le (E.image (fun z => (hexh z).choose))
    let : Algebra A (D.obj M).gl.carrier := (D.obj M).gl.φ.toAlgebra
    have hsM := hsl M
    have hEM : ∀ z ∈ E, s M (Function.invFun (s M) z) = z := by
      intro z hz
      refine Function.invFun_eq ?_
      obtain ⟨x, hx⟩ := (hexh z).choose_spec
      have hle : (hexh z).choose ≤ M := hM _ (Finset.mem_image_of_mem _ hz)
      refine ⟨(D.map (homOfLE hle)).ψ x, ?_⟩
      rw [show s M ((D.map (homOfLE hle)).ψ x)
          = ((s M).comp ((D.map (homOfLE hle)).ψ)) x from rfl, hcoc _ _ hle, hx]
    obtain ⟨S, hSsub, hSfin, hSet, hSloc, hSunit⟩ :=
      (D.obj M).cover (E.image (fun z => Function.invFun (s M) z))
    have := hSfin; have := hSet; have := hSloc
    have halg : ∀ r : A, s M (algebraMap A (D.obj M).gl.carrier r)
        = algebraMap A ub.carrier r := fun r => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply,
        hphi M]
    set f : S →ₐ[A] ub.carrier :=
      { toRingHom := (s M).comp (Subalgebra.val S).toRingHom
        commutes' := fun r => halg r } with hf
    obtain ⟨S', hS'range, hS'fin, hS'et, hS'loc, hS'unit⟩ :=
      exists_subalgebra_range f ((hsinj M).comp Subtype.val_injective)
        (fun x hx => hSunit x (isUnit_of_map_unit (s M) _ hx))
    refine ⟨S', fun z hz => ?_, hS'fin, hS'et, hS'loc, hS'unit⟩
    refine hS'range ⟨⟨Function.invFun (s M) z, ?_⟩, hEM z (Finset.mem_coe.mp hz)⟩
    exact hSsub (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hz)))
  set ubE : EtLift A F := ⟨ub, hcover⟩ with hubE
  let cc : Cocone D :=
    { pt := ubE
      ι :=
        { app := fun i =>
            { ψ := s i, isLocal := hsl i, maxeq := hmax i, φcomp := hphi i, ιcomp := hiota i }
          naturality := by
            intro i j f
            refine ELHom.ext' ?_
            change (s j).comp ((D.map f).ψ) = (RingHom.id ub.carrier).comp (s i)
            rw [RingHom.id_comp]
            exact hcoc i j (leOfHom f) } }
  have hdesc : ∀ sc : Cocone D, ∃ f : ELHom ubE sc.pt, ∀ i, cc.ι.app i ≫ f = sc.ι.app i := by
    intro sc
    have hcompat : ∀ i j (hij : i ≤ j),
        ((sc.ι.app j).ψ).comp ((D.map (homOfLE hij)).ψ) = (sc.ι.app i).ψ := by
      intro i j hij
      have h := congrArg ELHom.ψ (sc.ι.naturality (homOfLE hij))
      change (sc.ι.app j).ψ.comp ((D.map (homOfLE hij)).ψ) = (sc.ι.app i).ψ
      rw [show (sc.ι.app j).ψ.comp ((D.map (homOfLE hij)).ψ)
          = ((D.map (homOfLE hij)) ≫ sc.ι.app j).ψ from rfl, h]
      exact RingHom.id_comp _
    obtain ⟨ψ, hψ⟩ := huniv sc.pt.gl.carrier (fun i => (sc.ι.app i).ψ) hcompat
    obtain ⟨i₀⟩ := ‹Nonempty I›
    have hlocal : IsLocalHom ψ := by
      refine ⟨fun z hz => ?_⟩
      obtain ⟨i, x, rfl⟩ := hexh z
      have hx : ψ (s i x) = (sc.ι.app i).ψ x :=
        congrArg (fun (r : (D.obj i).gl.carrier →+* sc.pt.gl.carrier) => r x) (hψ i)
      rw [hx] at hz
      have := (sc.ι.app i).isLocal
      exact (isUnit_of_map_unit ((sc.ι.app i).ψ) x hz).map (s i)
    refine ⟨{ ψ := ψ, isLocal := hlocal, maxeq := ?_, φcomp := ?_, ιcomp := ?_ }, ?_⟩
    · calc maximalIdeal sc.pt.gl.carrier
          = Ideal.map ((sc.ι.app i₀).ψ) (maximalIdeal (D.obj i₀).gl.carrier) := (sc.ι.app i₀).maxeq
        _ = Ideal.map (ψ.comp (s i₀)) (maximalIdeal (D.obj i₀).gl.carrier) := by rw [hψ i₀]
        _ = Ideal.map ψ (Ideal.map (s i₀) (maximalIdeal (D.obj i₀).gl.carrier)) :=
            (Ideal.map_map _ _).symm
        _ = Ideal.map ψ (maximalIdeal ub.carrier) := by rw [← hmax i₀]
    · rw [← hphi i₀, ← RingHom.comp_assoc, hψ i₀]
      exact (sc.ι.app i₀).φcomp
    · refine RingHom.ext fun x => ?_
      obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective (R := ub.carrier) x
      obtain ⟨i, y, rfl⟩ := hexh z
      have key : ψ (s i y) = (sc.ι.app i).ψ y :=
        congrArg (fun (r : (D.obj i).gl.carrier →+* sc.pt.gl.carrier) => r y) (hψ i)
      have := (sc.ι.app i).isLocal
      have := hsl i
      calc (sc.pt.gl.ι.comp (ResidueField.map ψ)) (residue ub.carrier (s i y))
          = sc.pt.gl.ι (residue sc.pt.gl.carrier (ψ (s i y))) := by
            rw [RingHom.comp_apply, ResidueField.map_residue]
        _ = sc.pt.gl.ι (residue sc.pt.gl.carrier ((sc.ι.app i).ψ y)) := by rw [key]
        _ = (D.obj i).gl.ι (residue (D.obj i).gl.carrier y) := by
          simpa [ResidueField.map_residue] using
            congrArg (fun (r : ResidueField (D.obj i).gl.carrier →+* F) =>
              r (residue (D.obj i).gl.carrier y)) (sc.ι.app i).ιcomp
        _ = ub.ι (residue ub.carrier (s i y)) := by
          simpa [ResidueField.map_residue] using
            (congrArg (fun (r : ResidueField (D.obj i).gl.carrier →+* F) =>
              r (residue (D.obj i).gl.carrier y)) (hiota i)).symm
    · intro i
      refine ELHom.ext' ?_
      change ψ.comp (s i) = (sc.ι.app i).ψ
      exact hψ i
  exact ⟨⟨{ cocone := cc
            isColimit :=
              { desc := fun sc => (hdesc sc).choose
                fac := fun sc i => (hdesc sc).choose_spec i
                uniq := fun sc m hm => by
                  refine ELHom.ext' (RingHom.ext fun z => ?_)
                  obtain ⟨i, x, rfl⟩ := hexh z
                  have e1 : m.ψ.comp (s i) = (sc.ι.app i).ψ := congrArg ELHom.ψ (hm i)
                  have e2 : ((hdesc sc).choose).ψ.comp (s i) = (sc.ι.app i).ψ :=
                    congrArg ELHom.ψ ((hdesc sc).choose_spec i)
                  have := congrArg (fun (r : (D.obj i).gl.carrier →+* sc.pt.gl.carrier) => r x)
                    (e1.trans e2.symm)
                  simpa using this } }⟩⟩

/-- Étale lifts admit the colimits needed to iterate a successor structure over a well-ordered
type: colimits of the shapes `Set.Iio j` for a successor limit `j`, and of the shape `J`. -/
private theorem hasIterationOfShape_etLift (J : Type w) [LinearOrder J] [OrderBot J] :
    HasIterationOfShape J (EtLift A F) := by
  constructor
  · intro j hj
    have : Nonempty (Set.Iio j) := (not_isMin_iff.mp hj.not_isMin).elim fun b hb ↦ ⟨⟨b, hb⟩⟩
    exact ⟨fun D => hasColimit_of_directed D⟩
  · exact ⟨fun D => hasColimit_of_directed D⟩

/-- **The residue field of a monogenic step embeds in `F` and hits the adjoined element.** Let `B`
be a local ring whose residue field is embedded in `F`, let `α : F`, and let `p ∈ B[X]` have
irreducible reduction in `κ(B)[X]` equal to the minimal polynomial of `α`. Then the residue field
of `AdjoinRoot p` embeds in `F` over `κ(B)`, and `α` lies in the range of that embedding.

The embedding is obtained by lifting rather than by identifying the residue field. Since `α` is a
root of the image of `p` under `κ(B) → F`, `AdjoinRoot.lift` gives a ring map
`θ : AdjoinRoot p → F` over `B` carrying `AdjoinRoot.root p` to `α`. Its maximal ideal is
`𝔪ᴮ · AdjoinRoot p` (`AdjoinRoot.maximalIdeal_eq_map_maximalIdeal`, whence the irreducibility
hypothesis), which `θ` kills, so `θ` is local and `ResidueField.lift θ` is the required embedding,
sending the residue of `AdjoinRoot.root p` to `α`. Its image is the simple subextension `κ(B)⟮α⟯`
of `F`, but nothing here needs that description, so neither
`AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot` nor `IntermediateField.adjoinRootEquivAdjoin` is
used; in particular `p` need not be assumed monic. -/
private theorem exists_residueEmbedding_adjoinRoot {B : Type w} [CommRing B] [IsLocalRing B]
    [Algebra (ResidueField B) F] (α : F) {p : B[X]}
    (hirr : Irreducible (p.map (residue B)))
    (hpmap : p.map (residue B) = minpoly (ResidueField B) α)
    [IsLocalRing (AdjoinRoot p)] (hlh : IsLocalHom (AdjoinRoot.of p)) :
    ∃ ι' : ResidueField (AdjoinRoot p) →+* F,
      ι'.comp (@ResidueField.map _ _ _ _ _ _ (AdjoinRoot.of p) hlh)
          = algebraMap (ResidueField B) F ∧ α ∈ Set.range ι' := by
  have hroot : Polynomial.eval₂ ((algebraMap (ResidueField B) F).comp (residue B)) α p = 0 := by
    rw [← Polynomial.eval₂_map, hpmap, ← Polynomial.aeval_def, minpoly.aeval]
  set θ : AdjoinRoot p →+* F :=
    AdjoinRoot.lift ((algebraMap (ResidueField B) F).comp (residue B)) α hroot with hθ
  have hker : ∀ a ∈ maximalIdeal (AdjoinRoot p), θ a = 0 := by
    rw [AdjoinRoot.maximalIdeal_eq_map_maximalIdeal hirr]
    refine fun a ha => (?_ : Ideal.map (AdjoinRoot.of p) (maximalIdeal B) ≤ RingHom.ker θ) ha
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    simp only [Ideal.mem_comap, RingHom.mem_ker, hθ, AdjoinRoot.lift_of, RingHom.comp_apply]
    rw [show residue B b = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
  have hlocθ : IsLocalHom θ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hnu
    rw [hker a ((mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hnu))] at ha
    exact not_isUnit_zero ha
  refine ⟨ResidueField.lift θ, ?_, ⟨residue (AdjoinRoot p) (AdjoinRoot.root p), ?_⟩⟩
  · refine RingHom.ext fun x => ?_
    obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
    rw [RingHom.comp_apply, ResidueField.map_residue, ResidueField.lift_residue_apply, hθ,
      AdjoinRoot.lift_of, RingHom.comp_apply]
  · rw [ResidueField.lift_residue_apply, hθ, AdjoinRoot.lift_root]

/-- **The monogenic étale step.** Any element `α : F` can be adjoined to an étale lift: there is
an étale lift `h`, a morphism `g ⟶ h` and a point of the residue field of `h` mapping to `α`.

Let `κ` be the residue field of the carrier `B` of `g`, embedded in `F` by `g.gl.ι`. Then `α` is
separable algebraic over `κ`, so its minimal polynomial is monic, irreducible and separable; lift
it to a monic `p ∈ B[X]`. The new carrier is `AdjoinRoot p`, which is local
(`AdjoinRoot.isLocalRing_of_irreducible_map_residue`) with `𝔪 = 𝔪_B · AdjoinRoot p`
(`AdjoinRoot.maximalIdeal_eq_map_maximalIdeal`), free hence flat over `B`, covered by its finite
étale local `A`-subalgebras (`isFinEtaleUnion_adjoinRoot`), and whose residue field is
`κ[X] ⧸ (p̄) = κ⟮α⟯ ⊆ F`. -/
private theorem exists_etaleStep [Algebra.IsSeparable (ResidueField A) F] (g : EtLift A F)
    (α : F) : ∃ (h : EtLift A F) (_ : ELHom g h), α ∈ Set.range h.gl.ι := by
  classical
  let : Algebra A g.gl.carrier := g.gl.φ.toAlgebra
  have hamB : algebraMap A g.gl.carrier = g.gl.φ := RingHom.algebraMap_toAlgebra _
  have hlhB : IsLocalHom (algebraMap A g.gl.carrier) := by rw [hamB]; exact g.gl.hφ
  let : Algebra (ResidueField g.gl.carrier) F := g.gl.ι.toAlgebra
  have hamF : algebraMap (ResidueField g.gl.carrier) F = g.gl.ι := RingHom.algebraMap_toAlgebra _
  have htower : IsScalarTower (ResidueField A) (ResidueField g.gl.carrier) F := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    have h := congrArg (fun (r : ResidueField A →+* F) => r x) g.gl.hι
    simp only [RingHom.comp_apply] at h
    rw [hamF, ← h]
    rfl
  have hsepF : Algebra.IsSeparable (ResidueField g.gl.carrier) F :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) _ F
  have hsep : IsSeparable (ResidueField g.gl.carrier) α := Algebra.IsSeparable.isSeparable _ α
  have hint : IsIntegral (ResidueField g.gl.carrier) α := hsep.isIntegral
  have hirr : Irreducible (minpoly (ResidueField g.gl.carrier) α) := minpoly.irreducible hint
  have hmonicbar : (minpoly (ResidueField g.gl.carrier) α).Monic := minpoly.monic hint
  have hsepbar : (minpoly (ResidueField g.gl.carrier) α).Separable := hsep
  have hlifts : minpoly (ResidueField g.gl.carrier) α
      ∈ Polynomial.lifts (residue g.gl.carrier) :=
    (Polynomial.lifts_iff_coeff_lifts _).2 fun _ ↦ IsLocalRing.residue_surjective _
  obtain ⟨p, hpmap, -, hpmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmonicbar
  have hirr' : Irreducible (p.map (residue g.gl.carrier)) := hpmap ▸ hirr
  have hsep' : (p.map (residue g.gl.carrier)).Separable := hpmap ▸ hsepbar
  have hloc' : IsLocalRing (AdjoinRoot p) :=
    AdjoinRoot.isLocalRing_of_irreducible_map_residue hpmonic hirr'
  have hmaxeq : maximalIdeal (AdjoinRoot p) = (maximalIdeal g.gl.carrier).map (AdjoinRoot.of p) :=
    AdjoinRoot.maximalIdeal_eq_map_maximalIdeal hirr'
  have hlh' : IsLocalHom (AdjoinRoot.of p) := AdjoinRoot.isLocalHom_of_monic hpmonic
  have hflatB : letI : Algebra g.gl.carrier (AdjoinRoot p) := (AdjoinRoot.of p).toAlgebra
      Module.Flat g.gl.carrier (AdjoinRoot p) := by
    rw [show ((AdjoinRoot.of p).toAlgebra) = AdjoinRoot.instAlgebra p from by
      apply Algebra.algebra_ext; intro r; rfl]
    have : Module.Free g.gl.carrier (AdjoinRoot p) := hpmonic.free_adjoinRoot
    exact Module.Flat.of_free
  obtain ⟨hflatA, hmaxA⟩ := flat_and_maximalIdeal_eq_map_comp A g.gl.carrier (AdjoinRoot p) g.gl.φ
    (AdjoinRoot.of p) g.gl.flat hflatB g.gl.maxeq hmaxeq
  obtain ⟨ι', hιcomp0, hαrange⟩ :=
    exists_residueEmbedding_adjoinRoot α hirr' hpmap hlh'
  have hιcomp : ι'.comp (@ResidueField.map _ _ _ _ _ _ (AdjoinRoot.of p) hlh') = g.gl.ι := by
    rw [hιcomp0]; exact hamF
  have hφ' : IsLocalHom ((AdjoinRoot.of p).comp g.gl.φ) := RingHom.isLocalHom_comp _ _
  have hιA : ι'.comp (@ResidueField.map _ _ _ _ _ _ ((AdjoinRoot.of p).comp g.gl.φ) hφ')
      = algebraMap (ResidueField A) F := by
    rw [IsLocalRing.ResidueField.map_comp g.gl.φ (AdjoinRoot.of p), ← RingHom.comp_assoc, hιcomp,
      g.gl.hι]
  have hcover' : letI : Algebra A (AdjoinRoot p) := ((AdjoinRoot.of p).comp g.gl.φ).toAlgebra
      IsFinEtaleUnion A (AdjoinRoot p) :=
    isFinEtaleUnion_of_algebraMap_eq (AdjoinRoot.instAlgebra p) _ (fun _ => rfl)
      (isFinEtaleUnion_adjoinRoot (R := A) g.cover hpmonic hirr' hsep')
  exact ⟨⟨{ carrier := AdjoinRoot p
            commRing := inferInstance
            isLocalRing := hloc'
            φ := (AdjoinRoot.of p).comp g.gl.φ
            hφ := hφ'
            flat := hflatA
            maxeq := hmaxA
            ι := ι'
            hι := hιA }, hcover'⟩,
    { ψ := AdjoinRoot.of p
      isLocal := hlh'
      maxeq := hmaxeq
      φcomp := rfl
      ιcomp := hιcomp }, hαrange⟩

/-- **The trivial étale lift**: `A` itself, with the given embedding `k → F` for its residue
embedding, is covered by its finite étale local `A`-subalgebras (`isFinEtaleUnion_self`). -/
private noncomputable def etLift_trivial (A : Type w) [CommRing A] [IsLocalRing A] (F : Type w)
    [Field F] [Algebra (ResidueField A) F] : EtLift A F where
  gl := goodLift_trivial A F
  cover := isFinEtaleUnion_of_algebraMap_eq (Algebra.id A) _ (fun _ => rfl)
    (isFinEtaleUnion_self A)

/-- **One monogenic step, as a successor.** Every étale lift admits a morphism to an étale lift
which, unless its residue embedding was already onto `F`, cuts out a strictly larger subfield of
`F`: adjoin an element of `F` outside the range (`exists_etaleStep`). -/
private theorem exists_step [Algebra.IsSeparable (ResidueField A) F] (g : EtLift A F) :
    ∃ (h : EtLift A F) (_ : ELHom g h),
      ¬ Function.Surjective g.gl.ι → Set.range g.gl.ι ≠ Set.range h.gl.ι := by
  classical
  by_cases hs : Function.Surjective g.gl.ι
  · exact ⟨g, 𝟙 g, fun h => absurd hs h⟩
  · obtain ⟨α, hα⟩ : ∃ α : F, α ∉ Set.range g.gl.ι := by
      rw [Function.Surjective] at hs
      push Not at hs
      obtain ⟨α, hα⟩ := hs
      exact ⟨α, fun hmem => by obtain ⟨y, hy⟩ := hmem; exact hα y hy⟩
    obtain ⟨h', m, hcov⟩ := exists_etaleStep g α
    exact ⟨h', m, fun _ hEq => hα (by rw [hEq]; exact hcov)⟩

/-- The successor structure on étale lifts: adjoin one missing element of `F` at each step,
starting from `A` itself. -/
private noncomputable def succStructEtLift [Algebra.IsSeparable (ResidueField A) F] :
    SuccStruct (EtLift A F) where
  X₀ := etLift_trivial A F
  succ g := (exists_step g).choose
  toSucc g := (exists_step g).choose_spec.choose

/-- **The transfinite assembly.** For a local ring `A` and a separable algebraic extension `F` of
its residue field there is an étale lift of `A` towards `F` whose residue embedding is onto `F`.

Starting from `etLift_trivial` one adjoins the elements of `F` one at a time by `exists_step`,
taking the colimits of `hasColimit_of_directed` at limit stages; the tower is the iteration of
`succStructEtLift` over an index type longer than `Set F`, so some stage's residue embedding is
already onto. -/
private theorem exists_etLift_surjective [Algebra.IsSeparable (ResidueField A) F] :
    ∃ g : EtLift A F, Function.Surjective g.gl.ι := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  set κ : Cardinal.{w} := Order.succ (2 ^ Cardinal.mk F) with hκdef
  have hκpos : (0 : Cardinal.{w}) < κ := lt_of_le_of_lt (zero_le) (Order.lt_succ _)
  have hne : Nonempty κ.ord.ToType := by
    rw [Ordinal.nonempty_toType_iff]
    simpa [Cardinal.ord_eq_zero] using hκpos.ne'
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  have := hasIterationOfShape_etLift (A := A) (F := F) κ.ord.ToType
  set Φ := succStructEtLift (A := A) (F := F) with hΦ
  set f : κ.ord.ToType → Set F :=
    fun j => Set.range ((Φ.iterationFunctor κ.ord.ToType).obj j).gl.ι with hf
  have hmono : StrictMono f := by
    intro j j' hjj'
    have hnm : ¬ IsMax j := not_isMax_iff.mpr ⟨j', hjj'⟩
    have hsub1 : f j ⊆ f (Order.succ j) :=
      range_ι_subset ((Φ.iterationFunctor κ.ord.ToType).map (homOfLE (Order.le_succ j)))
    have hne : f j ≠ f (Order.succ j) := by
      have hiso := range_ι_eq_of_iso (Φ.iterationFunctorObjSuccIso j hnm)
      intro hEq
      exact (exists_step ((Φ.iterationFunctor κ.ord.ToType).obj j)).choose_spec.choose_spec
        (hcon _) (hEq.trans hiso)
    refine lt_of_lt_of_le (lt_of_le_of_ne hsub1 hne) ?_
    exact range_ι_subset
      ((Φ.iterationFunctor κ.ord.ToType).map (homOfLE (Order.succ_le_of_lt hjj')))
  have h1 : Cardinal.mk κ.ord.ToType ≤ Cardinal.mk (Set F) :=
    Cardinal.mk_le_of_injective hmono.injective
  rw [Cardinal.mk_ord_toType, Cardinal.mk_set] at h1
  exact absurd h1 (not_le.mpr (Order.lt_succ _))

end Assembly

/-- The residue field map of a ring isomorphism of local rings inverts that of its inverse. -/
private theorem residueField_map_map_symm {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (e : A ≃+* B) (x : ResidueField B) :
    ResidueField.map (e : A →+* B) (ResidueField.map (e.symm : B →+* A) x) = x := by
  obtain ⟨y, rfl⟩ := residue_surjective (R := B) x
  simp [ResidueField.map_residue]

/-- **The cover property descends along a finite étale base ring.** If `B` is covered by its
finite étale local `S`-subalgebras and `S` is itself finite étale over `R`, then `B` is covered by
its finite étale local `R`-subalgebras: a finite étale local `S`-subalgebra of `B` is one over `R`
by `Module.Finite.trans` and `Algebra.Etale.comp`. -/
private theorem IsFinEtaleUnion.restrictScalars {R S B : Type*} [CommRing R] [CommRing S]
    [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    [Module.Finite R S] [Algebra.Etale R S] (h : IsFinEtaleUnion S B) : IsFinEtaleUnion R B := by
  intro E
  obtain ⟨T, hTsub, hTfin, hTet, hTloc, hTunit⟩ := h E
  have := hTfin; have := hTet; have := hTloc
  have : Module.Finite R T := Module.Finite.trans S T
  have : Algebra.Etale R T := Algebra.Etale.comp R S T
  exact ⟨T.restrictScalars R, hTsub, inferInstanceAs (Module.Finite R ↥T),
    inferInstanceAs (Algebra.Etale R ↥T), inferInstanceAs (IsLocalRing ↥T), hTunit⟩


/-- **The transfinite construction.** For a local ring `R` and a separable algebraic extension `K`
of its residue field there are a local `R`-algebra `R'`, a directed family `𝒮` of finite étale
local `R`-subalgebras of `R'` covering `R'`, and a `k`-embedding `ι` of the residue field of `R'`
into `K` which is onto.

This is the transfinite assembly described in the module docstring: adjoin the elements of `K` one
at a time by the monogenic step `finiteEtale_adjoinRoot_of_separable`, take directed colimits at
limit stages, and stop at a stage whose residue embedding is surjective.

The assembly `exists_etLift_surjective` runs in a single universe, so it is applied to
`ULift.{v} R` and `ULift.{u} K` and the conclusion transported back: separability by
`Algebra.IsSeparable.of_equiv_equiv`, the family of subalgebras by
`IsFinEtaleUnion.restrictScalars` along the finite étale (indeed isomorphic) base change
`R → ULift.{v} R`. -/
@[sga "3 V 4.1.2" "special case"]
private theorem exists_directedUnion_finiteEtale_residueField_surjective (R : Type u) [CommRing R]
    [IsLocalRing R] (K : Type v) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R') (_ : IsLocalRing R')
      (_ : IsLocalHom (algebraMap R R')) (𝒮 : Set (Subalgebra R R'))
      (ι : ResidueField R' →ₐ[ResidueField R] K),
      DirectedOn (· ≤ ·) 𝒮 ∧
      (∀ x : R', ∃ S ∈ 𝒮, x ∈ S) ∧
      (∀ S ∈ 𝒮, Module.Finite R S ∧ Algebra.Etale R S ∧ IsLocalRing S) ∧
      Function.Surjective ι := by
  classical
  let e : ULift.{v} R ≃+* R := ULift.ringEquiv
  let f : ULift.{u} K ≃+* K := ULift.ringEquiv
  have : IsLocalRing (ULift.{v} R) := e.symm.isLocalRing
  let : Algebra (ResidueField (ULift.{v} R)) (ULift.{u} K) :=
    ((f.symm : K →+* ULift.{u} K).comp ((algebraMap (ResidueField R) K).comp
      (ResidueField.map (e : ULift.{v} R →+* R)))).toAlgebra
  have hamF : algebraMap (ResidueField (ULift.{v} R)) (ULift.{u} K)
      = (f.symm : K →+* ULift.{u} K).comp ((algebraMap (ResidueField R) K).comp
        (ResidueField.map (e : ULift.{v} R →+* R))) := RingHom.algebraMap_toAlgebra _
  have : Algebra.IsSeparable (ResidueField (ULift.{v} R)) (ULift.{u} K) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (ResidueField.mapEquiv (e.symm : R ≃+* ULift.{v} R)) (f.symm : K ≃+* ULift.{u} K) ?_
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, hamF]
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom,
      show ResidueField.map (e : ULift.{v} R →+* R)
          (ResidueField.mapEquiv (e.symm : R ≃+* ULift.{v} R) x) = x from
        residueField_map_map_symm e x]
  obtain ⟨g, hgsurj⟩ := exists_etLift_surjective (A := ULift.{v} R) (F := ULift.{u} K)
  have hamA : algebraMap R (ULift.{v} R) = (e.symm : R →+* ULift.{v} R) := rfl
  let : Algebra (ULift.{v} R) g.gl.carrier := g.gl.φ.toAlgebra
  have hamB : algebraMap (ULift.{v} R) g.gl.carrier = g.gl.φ := RingHom.algebraMap_toAlgebra _
  let algR : Algebra R g.gl.carrier := (g.gl.φ.comp (e.symm : R →+* ULift.{v} R)).toAlgebra
  have hAM : algebraMap R g.gl.carrier = g.gl.φ.comp (e.symm : R →+* ULift.{v} R) :=
    RingHom.algebraMap_toAlgebra _
  have hlh : IsLocalHom (algebraMap R g.gl.carrier) := by
    rw [hAM]; exact RingHom.isLocalHom_comp _ _
  have htower : IsScalarTower R (ULift.{v} R) g.gl.carrier :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [hAM, hamA, hamB]; rfl
  -- `R → ULift.{v} R` is an isomorphism, hence finite étale
  let eA : R ≃ₐ[R] ULift.{v} R :=
    AlgEquiv.ofRingEquiv (f := (e.symm : R ≃+* ULift.{v} R)) fun _ => rfl
  have hfinA : Module.Finite R (ULift.{v} R) := Module.Finite.equiv eA.toLinearEquiv
  have hetA : Algebra.Etale R (ULift.{v} R) := Algebra.Etale.of_equiv eA
  have hcover : IsFinEtaleUnion R g.gl.carrier :=
    @IsFinEtaleUnion.restrictScalars R (ULift.{v} R) g.gl.carrier _ _ _ _ _ _ htower hfinA hetA
      g.cover
  obtain ⟨𝒮, hdir, hcov, hprop⟩ := hcover.exists_directed_family
  have hcomm : ((f : ULift.{u} K →+* K).comp g.gl.ι).comp
      (algebraMap (ResidueField R) (ResidueField g.gl.carrier))
      = algebraMap (ResidueField R) K := by
    refine RingHom.ext fun r => ?_
    obtain ⟨x, rfl⟩ := residue_surjective (R := R) r
    have h1 : ResidueField.map (algebraMap R g.gl.carrier) (residue R x)
        = ResidueField.map g.gl.φ (residue (ULift.{v} R) (e.symm x)) := by
      rw [ResidueField.map_residue, ResidueField.map_residue, hAM]; rfl
    have h2 := DFunLike.congr_fun g.gl.hι (residue (ULift.{v} R) (e.symm x))
    simp only [RingHom.coe_comp, Function.comp_apply] at h2
    change f (g.gl.ι (ResidueField.map (algebraMap R g.gl.carrier) (residue R x))) = _
    rw [h1, h2, hamF]
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ResidueField.map_residue,
      RingEquiv.apply_symm_apply]
  let ιK : ResidueField g.gl.carrier →ₐ[ResidueField R] K :=
    { toRingHom := (f : ULift.{u} K →+* K).comp g.gl.ι,
      commutes' := fun r => DFunLike.congr_fun hcomm r }
  refine ⟨g.gl.carrier, g.gl.commRing, algR, g.gl.isLocalRing, hlh, 𝒮, ιK, hdir, hcov, hprop,
    fun y => ?_⟩
  obtain ⟨z, hz⟩ := hgsurj (f.symm y)
  exact ⟨z, by change f (g.gl.ι z) = y; rw [hz, RingEquiv.apply_symm_apply]⟩

/-- For a local ring `R` and a separable algebraic extension `K` of its residue field there is a
local `R`-algebra `R'` which is the directed union of a family `𝒮` of finite étale local
`R`-subalgebras, and whose residue field is isomorphic to `K` over the residue field of `R`. -/
public theorem solution (R : Type u) [CommRing R] [IsLocalRing R] (K : Type v) [Field K]
    [Algebra (ResidueField R) K] [Algebra.IsSeparable (ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R') (_ : IsLocalRing R')
      (_ : IsLocalHom (algebraMap R R')) (𝒮 : Set (Subalgebra R R')),
      DirectedOn (· ≤ ·) 𝒮 ∧
      (∀ x : R', ∃ S ∈ 𝒮, x ∈ S) ∧
      (∀ S ∈ 𝒮, Module.Finite R S ∧ Algebra.Etale R S ∧ IsLocalRing S) ∧
      Nonempty (ResidueField R' ≃ₐ[ResidueField R] K) := by
  obtain ⟨R', hring, halg, hloc, hhom, 𝒮, ι, hdir, hcov, hfe, hsurj⟩ :=
    exists_directedUnion_finiteEtale_residueField_surjective R K
  exact ⟨R', hring, halg, hloc, hhom, 𝒮, hdir, hcov, hfe,
    ⟨AlgEquiv.ofBijective ι ⟨ι.toRingHom.injective, hsurj⟩⟩⟩

end Stacks.Etale.ResidueFieldColimit

end

/-!
# A separable algebraic residue field extension is a colimit of finite étale extensions

Let `(R, 𝔪, k)` be a local ring and let `K / k` be a separable algebraic field extension. Then `K`
is the residue field of a local ring `R'` which is a directed union of finite étale local
extensions of `R`: there is a local ring `R'`, a local ring map `R → R'`, and a directed family
`𝒮` of `R`-subalgebras of `R'` covering `R'`, each of which is a local ring finite étale over `R`,
such that the residue field of `R'` is `K` as an extension of `k`. So a separable algebraic
extension of the residue field is realized not merely by a flat local extension, as in
[StacksProject 03C3], but by a filtered colimit of finite étale ones.

The construction, which is no part of the statement, runs the transfinite recursion of
[StacksProject 03C3] and shows by transfinite induction that each ring produced there is already a
filtered colimit of finite étale extensions of `R`: a successor step `R_α → R_{α + 1}` is finite
étale, hence obtained from a finite étale extension `R_i → R_{i, 1}` of some finite stage by base
change, and a limit stage is a union of earlier ones, in which every finite subset lies in a
finite étale subextension.

## Main results

* `IsLocalRing.exists_finiteEtale_directed_residueField_algEquiv`: for a local ring `R` and a
  separable algebraic extension `K` of its residue field there is a local `R`-algebra `R'` which
  is the directed union of its finite étale local `R`-subalgebras and has residue field
  `k`-isomorphic to `K`.

## Implementation notes

*The colimit is a directed union of subalgebras.* The source's data is a directed set `I` and a
system of finite étale extensions `R ⊂ R_i` with `R' = colim R_i`. Since the transition maps of
such a system are injective, the maps `R_i → R'` are injective too and `R'` is the directed union
of the images; conversely a directed family of subalgebras covering `R'` is a directed system
whose colimit is `R'`. The two descriptions are therefore equivalent, and the statement uses the
second: `𝒮 : Set (Subalgebra R R')`, `DirectedOn (· ≤ ·) 𝒮`, and `∀ x, ∃ S ∈ 𝒮, x ∈ S`. This
avoids naming a diagram in `CommAlgCat` and a colimit cone, and it is the form in which a user
consumes the lemma: an element, or a finite subset, of `R'` lies in a finite étale subextension.
The index set is nonempty, as the source's directed set is, because `R'` is covered.

*`R ⊂ R'` and `R ⊂ R_i` are automatic.* `Algebra.Etale R S` makes `S` flat over `R`, and a nonzero
finite flat algebra over a local ring is faithfully flat, so `algebraMap R S` is injective for
every `S ∈ 𝒮`; since `𝒮` covers `R'`, `algebraMap R R'` is injective as well, and `R'` is flat
over `R` as a directed colimit of flat algebras. The source's inclusion signs are thus consequences
of the stated conjuncts rather than extra ones, and `Module.Flat R R'` is likewise not restated.

*Locality of the members of `𝒮` is stated, not derived.* The source says the `R_i` are local
rings, and the statement says so; that it follows (a finite étale algebra over a local ring is a
finite product of local rings, and a ring with a nontrivial idempotent admits no injection into a
local ring) is a lemma about `𝒮`, not a weakening of it. For the same reason `𝔪_i = 𝔪 R_i` and
`𝔪' = 𝔪 R'`, which hold here as in [StacksProject 03C3], are omitted: the source states neither.

*Separable algebraic is one hypothesis.* `Algebra.IsSeparable k K` says every element of `K` has
separable minimal polynomial over `k`, which for a transcendental element is false; so it already
carries algebraicity (`Algebra.IsSeparable.isAlgebraic`), and no separate `Algebra.IsAlgebraic`
hypothesis is added.

*The universes.* `R : Type u` and `K : Type v` are independent and `R' : Type (max u v)`, which is
where the construction of [StacksProject 03C3] lands. The source states the lemma with `R` and `K`
in one universe, the case `v = u`.

Faithfulness to [StacksProject 09E0], point by point. (1) No hypothesis is dead: `R` local is used
through `maximalIdeal R` and `ResidueField R`, and `[Field K]` with `[Algebra (ResidueField R) K]`
and `[Algebra.IsSeparable (ResidueField R) K]` — precisely "`k ⊂ K` is separable algebraic" — is
used by the last conjunct, and is what makes the finite étale conjunct attainable, the residue
extension of a finite étale local extension being finite separable. (2) The scalars and the base
are the source's: the `S ∈ 𝒮` are subalgebras over `R` itself and are finite étale over `R`, not
over a localization, a quotient or an intermediate stage, and the isomorphism is over
`k = ResidueField R`. (3) The canonical maps are pinned: the ring map is `algebraMap R R'`, the
maps `R_i → R'` are the subalgebra inclusions, and the `k`-algebra structure on the residue field
of `R'` is the one `algebraMap R R'` induces (`IsLocalRing.ResidueField.instAlgebra`), so no
conjunct can be met by an unrelated identification. (4) The instantiation is not degenerate: for
`K = k` it holds with `R' = R` and `𝒮 = {⊤}`, for `K / k` finite separable with a single finite
étale `R'`, and for `R = ℤ_(p)` and `K` a separable algebraic closure of `𝔽_p` the ring `R'` is
the directed union of the unramified extensions of `R`, a local ring with residue field `K` which
is not itself finite over `R`, so the family `𝒮` is genuinely infinite there.

## References

* [StacksProject 09E0](https://stacks.math.columbia.edu/tag/09E0)
* [StacksProject 03C3](https://stacks.math.columbia.edu/tag/03C3), the flat local extension
  realizing an arbitrary residue field extension, which this refines

## Tags

finite étale, local ring, residue field, separable algebraic extension, filtered colimit
-/



@[expose] public section

open IsLocalRing in
/-- **A separable algebraic residue field extension is realized by a colimit of finite étale
extensions** (Stacks 09E0). Let `(R, 𝔪, k)` be a local ring and let `K` be a separable algebraic
extension of `k`. Then there are a local ring `R'`, a local ring map `R → R'`, and a directed
family `𝒮` of `R`-subalgebras of `R'` whose union is `R'`, each a local ring finite étale over
`R`, such that the residue field of `R'` is isomorphic to `K` as an extension of `k`. -/
@[stacks 09E0 "The source's directed set `I` and system of finite étale extensions `R ⊂ R_i` with
`R' = colim R_i` appear as a directed family `𝒮` of finite étale local `R`-subalgebras of `R'`
covering `R'`, which is equivalent since the transition maps of such a system are injective. `K`
is allowed to live in a universe of its own, the source's case being `v = u`. See the module
docstring.", ega "IV 18.8.6" "(18.8.6.2)"]
public theorem IsLocalRing.exists_finiteEtale_directed_residueField_algEquiv (R : Type u)
    [CommRing R] [IsLocalRing R] (K : Type v) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R') (_ : IsLocalRing R')
      (_ : IsLocalHom (algebraMap R R')) (𝒮 : Set (Subalgebra R R')),
      DirectedOn (· ≤ ·) 𝒮 ∧
      (∀ x : R', ∃ S ∈ 𝒮, x ∈ S) ∧
      (∀ S ∈ 𝒮, Module.Finite R S ∧ Algebra.Etale R S ∧ IsLocalRing S) ∧
      Nonempty (ResidueField R' ≃ₐ[ResidueField R] K) :=
  Stacks.Etale.ResidueFieldColimit.solution R K

end
