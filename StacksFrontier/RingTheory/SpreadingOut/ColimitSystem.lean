module

import StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Colimit.Ring
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Algebra.Category.Grp.Colimits

public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# Spreading out a finitely presented module along an essentially finitely presented local map

Proof of Stacks 00QX. Let `R → S` be a local homomorphism of local rings which is
essentially of finite presentation and let `M` be a finitely presented `S`-module. The
source builds a directed system `(R_λ → S_λ, M_λ)` of local homomorphisms of local rings
with finite modules, of finite character over `ℤ`, whose colimit is `(R → S, M)`, and which
is cartesian in the strong sense: `S_μ` is a localization of `S_λ ⊗_{R_λ} R_μ` at a prime
and `M_μ` is `M_λ ⊗_{S_λ} S_μ`.

## Main results

* `Stacks.SpreadingOut.LocalModuleSystem.solution`: Stacks 00QX.

## Implementation notes

The first step of the source's proof is to replace `S` by a localization at a *prime* of a
finitely presented `R`-algebra: `S` is essentially of finite presentation, so it is a
localization `T⁻¹P` of a finitely presented `R`-algebra `P` at some submonoid `T`, and since
`S` is local it is already the localization of `P` at the prime `q = (algebraMap P S)⁻¹(𝔪_S)`.
That is `exists_finitePresentation_isLocalization_atPrime`, whose ring-theoretic content is
`isLocalization_primeCompl_comap_maximalIdeal`: a localization of `P` which happens to be a
local ring is the localization of `P` at the contraction of its maximal ideal, because every
element outside that contraction already maps to a unit. Neither statement is in Mathlib.

The ring-theoretic half of the source's construction — the system `R_λ → S_λ` together with
the four conditions of 00QV — is `descent_core`, which is stated with `Ring.DirectLimit` and
its structure maps rather than with a functor to `CommRingCat` and a colimit cocone. The
translation is `sysFunctor`, `sysCocone` and `sysIsColimit`: a directed system of commutative
rings over a preorder is a functor on that preorder, and an isomorphism of the direct limit
with `R` turns the family of structure maps into a colimit cocone, because the legs of a
direct limit are jointly surjective and identify elements only at a finite stage.

Locality of the structure maps `R_λ → R`, which the statement asserts and which does not
follow from conditions (1)–(6), does follow from locality of the *transition* maps together
with the colimit description of `R`, and that derivation is
`isLocalHom_sysCocone_app`: if `a ∈ R_λ` has invertible image in `R`, an inverse comes from
some stage, the resulting relation `a · y = 1` holds at a common later stage `μ`, so the
image of `a` in `R_μ` is a unit, and `R_λ → R_μ` local gives `a` a unit. So no separate
locality hypothesis on the structure maps is needed from the ring-side input.

Condition (5) of 00QV is stated by `descent_core` for the tensor product `S_λ ⊗_{R_λ} R_μ` and
the map `Algebra.TensorProduct.productMap`, whereas the statement of 00QX spells that ring as a
pushout in `CommRingCat` and the map as `pushout.desc`. The two agree because the tensor product
*is* the pushout (`CommRingCat.isPushout_tensorProduct`) and the two maps out of it restrict to
`S_λ → S_μ` and `R_μ → S_μ` alike, so they are equal; `IsLocalization` then transports along the
resulting isomorphism of the base, which is
`exists_isLocalization_primeCompl_of_ringEquiv`, the prime being the contraction of the given
one. That transport lemma is not in Mathlib in this form; `IsLocalization.of_ringEquiv_left`
is, and does the work.

The presentation matrix of `M` lives at a single stage `l`, so the module system exists only from
`l` on, and the conclusion of 00QX replaces the index by the tail `{λ // l ≤ λ}`. Restricting the
ring-side data to the tail loses nothing: the tail of a directed preorder is a *final*
subcategory (`tailFunctor_final`), so `Functor.Final.isColimitWhiskerEquiv` turns the colimit
cocones over `Λ` into colimit cocones over the tail, and every other condition is the old one
read at the objects of the tail, the restricted functors being `tailFunctor l ⋙ A₀` and the
restricted transformations `Functor.whiskerLeft (tailFunctor l) φ₀`. Neither the finality of a
tail nor its directedness is in Mathlib for a preorder index; `Under.final_forget` is the same
fact for the `Under` category, which is not a preorder.

## References

* [Stacks Project, Tag 00QX](https://stacks.math.columbia.edu/tag/00QX)
-/

namespace Stacks.SpreadingOut.LocalModuleSystem


open CategoryTheory Limits
open scoped TensorProduct

/-- A localization of `P` which is a local ring is the localization of `P` at the
contraction of its maximal ideal: every element of `P` outside that contraction already
maps to a unit, so inverting it changes nothing. -/
public lemma isLocalization_primeCompl_comap_maximalIdeal
    {P S : Type*} [CommRing P] [CommRing S] [Algebra P S] (T : Submonoid P)
    [IsLocalization T S] [IsLocalRing S] :
    IsLocalization ((IsLocalRing.maximalIdeal S).comap (algebraMap P S)).primeCompl S := by
  refine IsLocalization.of_le T _ (fun t ht => ?_) (fun n hn => ?_)
  · simpa [Ideal.primeCompl, IsLocalRing.notMem_maximalIdeal] using
      IsLocalization.map_units S ⟨t, ht⟩
  · exact IsLocalRing.notMem_maximalIdeal.mp hn

/-- A local ring `S` which is essentially of finite presentation over `R` is the
localization at a prime of a finitely presented `R`-algebra. This is the first line of the
source's proof of 00QX, which writes `S = (R[x_1, …, x_n]/I)_𝔮` with `I` finitely
generated. -/
@[ega "IV 1.3.10" "special case"]
private theorem exists_finitePresentation_isLocalization_atPrime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) :
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra.FinitePresentation R P)
      (_ : Algebra P S) (q : Ideal P) (_ : q.IsPrime) (_ : IsLocalization q.primeCompl S),
      ∀ x : R, algebraMap P S (algebraMap R P x) = algebraMap R S x := by
  let _ : Algebra R S := (algebraMap R S).toAlgebra
  obtain ⟨P, hcr, halgRP, halgPS, hst, hfp, T, hT⟩ := hS
  let _ := hcr
  let _ := halgRP
  let _ := halgPS
  let _ := hst
  let _ := hfp
  let _ := hT
  exact ⟨P, hcr, halgRP, hfp, halgPS,
    (IsLocalRing.maximalIdeal S).comap (algebraMap P S), Ideal.IsPrime.comap _,
    isLocalization_primeCompl_comap_maximalIdeal T,
    fun x => (IsScalarTower.algebraMap_apply R P S x).symm⟩

/-!
### From a directed system of rings to a functor with a colimit cocone

`descent_core` delivers the ring-side system as a family `Robj : Λ → Type u` with transition
maps `fR` and an isomorphism of `Ring.DirectLimit Robj fR` with `R`. The statement of 00QX
asks instead for a functor `Λ ⥤ CommRingCat` and an honest colimit cocone. This section is
that translation.
-/

section System

variable {Λ : Type u} [Preorder Λ]
  (Robj : Λ → Type u) [∀ i, CommRing (Robj i)]
  (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
  (hdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))

/-- A directed system of commutative rings over a preorder `Λ`, read as a functor
`Λ ⥤ CommRingCat`. The functoriality is exactly the `DirectedSystem` laws. -/
public abbrev sysFunctor : Λ ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (Robj i)
  map {i j} h := CommRingCat.ofHom (fR i j (leOfHom h))
  map_id i := by ext x; exact hdir.map_self x
  map_comp {i j k} h h' := by ext x; exact (hdir.map_map (leOfHom h) (leOfHom h') x).symm

/-- Compatibility of the legs of a cocone on `sysFunctor` with the transition maps, read
on elements. -/
public lemma sysFunctor_leg_comp (s : Cocone (sysFunctor Robj fR hdir)) (i j : Λ)
    (hij : i ≤ j) (x : Robj i) :
    (s.ι.app j).hom (fR i j hij x) = (s.ι.app i).hom x :=
  congrArg (fun g => CommRingCat.Hom.hom g x) (s.w (homOfLE hij))

/-- The ring homomorphism out of the direct limit induced by a cocone on `sysFunctor`. -/
public noncomputable def sysLift (s : Cocone (sysFunctor Robj fR hdir)) :
    Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) →+* s.pt :=
  Ring.DirectLimit.lift Robj (fun i j h => (fR i j h : Robj i → Robj j)) s.pt
    (fun i => (s.ι.app i).hom) (fun i j hij x => sysFunctor_leg_comp Robj fR hdir s i j hij x)

private lemma sysLift_of (s : Cocone (sysFunctor Robj fR hdir)) (i : Λ) (x : Robj i) :
    sysLift Robj fR hdir s (Ring.DirectLimit.of Robj _ i x) = (s.ι.app i).hom x :=
  Ring.DirectLimit.lift_of _ _ _ i x

variable (R : Type u) [CommRing R]
  (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)

/-- The cocone on `sysFunctor` with apex `R` whose legs are the structure maps of the direct
limit, read through an isomorphism of the direct limit with `R`. -/
@[ega "0 1.4.5" "more general"]
public noncomputable def sysCocone :
    sysFunctor Robj fR hdir ⟶ (Functor.const Λ).obj (CommRingCat.of R) where
  app i := CommRingCat.ofHom (eR.toRingHom.comp (Ring.DirectLimit.of Robj _ i))
  naturality {i j} h := by
    ext x
    exact congrArg eR (Ring.DirectLimit.of_f (i := i) (j := j) (leOfHom h) x)

/-- `R` together with the structure maps of the direct limit is the colimit of `sysFunctor`
in `CommRingCat`: the legs are jointly surjective, and a map out of the direct limit is
determined by its restrictions. -/
@[ega "0 1.4.5" "more general"]
public noncomputable def sysIsColimit [Nonempty Λ] [IsDirected Λ (· ≤ ·)] :
    IsColimit (Cocone.mk (CommRingCat.of R) (sysCocone Robj fR hdir R eR)) where
  desc s := CommRingCat.ofHom ((sysLift Robj fR hdir s).comp eR.symm.toRingHom)
  fac s i := by
    ext x
    change sysLift Robj fR hdir s (eR.symm (eR (Ring.DirectLimit.of Robj _ i x))) = _
    rw [eR.symm_apply_apply]
    exact sysLift_of Robj fR hdir s i x
  uniq s m hm := by
    ext y
    obtain ⟨i, x, hx⟩ := Ring.DirectLimit.exists_of (eR.symm y)
    have hy : eR (Ring.DirectLimit.of Robj _ i x) = y := by
      rw [hx, eR.apply_symm_apply]
    have h1 : m.hom (eR (Ring.DirectLimit.of Robj _ i x)) = (s.ι.app i).hom x :=
      congrArg (fun g => CommRingCat.Hom.hom g x) (hm i)
    rw [← hy, h1]
    change _ = sysLift Robj fR hdir s (eR.symm (eR (Ring.DirectLimit.of Robj _ i x)))
    rw [eR.symm_apply_apply]
    exact (sysLift_of Robj fR hdir s i x).symm

include hdir in
/-- **The structure maps of a colimit of local rings with local transition maps are local.**

If `a ∈ R_λ` becomes a unit in `R = colim R_μ`, an inverse of its image comes from some stage
`R_ν`; at a stage `μ ≥ λ, ν` the relation `a · y = 1` holds up to an element of the kernel of
`R_μ → R`, hence holds outright at some later stage, so the image of `a` in that stage is a
unit and `a` is a unit because the transition map is local.

This is why 00QX needs no separate locality hypothesis on the structure maps of the
ring-side input: locality of the transition maps suffices. -/
private lemma isLocalHom_directLimit_of [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (hloc : ∀ i j (hij : i ≤ j), IsLocalHom (fR i j hij)) (i : Λ) :
    IsLocalHom (eR.toRingHom.comp (Ring.DirectLimit.of Robj _ i)) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb0⟩ := ha.exists_right_inv
  have hb : eR (Ring.DirectLimit.of Robj _ i a) * b = 1 := hb0
  obtain ⟨j, y, hy⟩ := Ring.DirectLimit.exists_of (eR.symm b)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have hb' : eR (Ring.DirectLimit.of Robj _ k (fR i k hik a * fR j k hjk y)) = 1 := by
    rw [map_mul, Ring.DirectLimit.of_f, Ring.DirectLimit.of_f, map_mul, hy,
      eR.apply_symm_apply, hb]
  have hz : Ring.DirectLimit.of Robj (fun i j h => (fR i j h : Robj i → Robj j)) k
      (fR i k hik a * fR j k hjk y - 1) = 0 := by
    rw [map_sub, map_one, sub_eq_zero]
    exact eR.injective (by rw [hb', map_one])
  obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.of.zero_exact hz
  rw [map_sub, map_one, map_mul, sub_eq_zero] at hl
  have hunit : IsUnit (fR i l (hik.trans hkl) a) := by
    refine IsUnit.of_mul_eq_one (fR k l hkl (fR j k hjk y)) ?_
    rwa [← hdir.map_map hik hkl a]
  exact (hloc i l (hik.trans hkl)).1 _ hunit

/-- The legs of the colimit cocone `sysCocone` are local homomorphisms; this is
`isLocalHom_directLimit_of`, read on the legs. -/
public lemma isLocalHom_sysCocone_app [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (hloc : ∀ i j (hij : i ≤ j), IsLocalHom (fR i j hij)) (i : Λ) :
    IsLocalHom ((sysCocone Robj fR hdir R eR).app i).hom :=
  isLocalHom_directLimit_of Robj fR hdir R eR hloc i

end System

section NatTrans

variable {Λ : Type u} [Preorder Λ]
  (Robj Sobj : Λ → Type u) [∀ i, CommRing (Robj i)] [∀ i, CommRing (Sobj i)]
  (fR : ∀ i j, i ≤ j → Robj i →+* Robj j) (fS : ∀ i j, i ≤ j → Sobj i →+* Sobj j)
  (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
  (hSdir : DirectedSystem Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)))
  (ψ : ∀ i, Robj i →+* Sobj i)
  (comm : ∀ i j (hij : i ≤ j), (ψ j).comp (fR i j hij) = (fS i j hij).comp (ψ i))

/-- A morphism of directed systems of rings, read as a natural transformation of the
associated functors: the commuting squares of the system are its naturality. -/
public def sysNatTrans : sysFunctor Robj fR hRdir ⟶ sysFunctor Sobj fS hSdir where
  app i := CommRingCat.ofHom (ψ i)
  naturality {i j} h := by
    ext x
    exact DFunLike.congr_fun (comm i j (leOfHom h)) x

/-- The two colimit cocones intertwine the morphism of systems with the map of colimits:
this is the identity `colim ψ = algebraMap R S` read on the structure maps. -/
public lemma directLimit_of_intertwine {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
    (eS : Ring.DirectLimit Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)) ≃+* S)
    (hcomm : (algebraMap R S).comp eR.toRingHom
      = eS.toRingHom.comp (Ring.DirectLimit.map ψ comm))
    (i : Λ) (x : Robj i) :
    eS (Ring.DirectLimit.of Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)) i (ψ i x))
      = algebraMap R S
        (eR (Ring.DirectLimit.of Robj (fun i j h => (fR i j h : Robj i → Robj j)) i x)) := by
  have h2 := DFunLike.congr_fun hcomm
    (Ring.DirectLimit.of Robj (fun i j h => (fR i j h : Robj i → Robj j)) i x)
  rw [RingHom.comp_apply, RingHom.comp_apply, Ring.DirectLimit.map_apply_of] at h2
  exact h2.symm

end NatTrans

/-- **Transport of "the localization at a prime" along an isomorphism of the base.**

If `Z` is the localization of `Q` at a prime and `e : P ≃+* Q` is compatible with the two
algebra structures on `Z`, then `Z` is the localization of `P` at the contracted prime. -/
public theorem exists_isLocalization_primeCompl_of_ringEquiv
    {P Q Z : Type u} [CommRing P] [CommRing Q] [CommRing Z]
    [Algebra P Z] [Algebra Q Z] (e : P ≃+* Q)
    (he : ∀ x, algebraMap P Z x = algebraMap Q Z (e x))
    (H : ∃ (p : Ideal Q) (_ : p.IsPrime), IsLocalization p.primeCompl Z) :
    ∃ (p : Ideal P) (_ : p.IsPrime), IsLocalization p.primeCompl Z := by
  obtain ⟨p, hp, hloc⟩ := H
  refine ⟨p.comap (e : P →+* Q), hp.comap _, ?_⟩
  have hM : Submonoid.map (e : P →+* Q) (p.comap (e : P →+* Q)).primeCompl = p.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe, Ideal.mem_comap]
    exact ⟨fun ⟨_, hy, hxy⟩ => hxy ▸ hy, fun hx => ⟨e.symm x, by simpa using hx, by simp⟩⟩
  exact IsLocalization.of_ringEquiv_left e hM he

/-- **The pushout in `CommRingCat` is the tensor product, and `pushout.desc` is
`Algebra.TensorProduct.productMap`.**

So the cartesian condition of 00QV, stated for `S_λ ⊗_{R_λ} R_μ` and the product map, is the
cartesian condition of 00QX, stated for the pushout of `φ_λ` along `R_λ → R_μ` and
`pushout.desc`. Both maps out of `S_λ ⊗_{R_λ} R_μ` restrict to `S_λ → S_μ` and `R_μ → S_μ`, so
they agree, and `IsLocalization` transports along the resulting isomorphism. -/
public theorem exists_isLocalization_primeCompl_pushout_of_tensorProduct
    {Ri Si Rj Sj : Type u} [CommRing Ri] [CommRing Si] [CommRing Rj] [CommRing Sj]
    [Algebra Ri Si] [Algebra Ri Rj] [Algebra Si Sj] [Algebra Rj Sj] [Algebra Ri Sj]
    [IsScalarTower Ri Si Sj] [IsScalarTower Ri Rj Sj]
    (sq : CommRingCat.ofHom (algebraMap Ri Si) ≫ CommRingCat.ofHom (algebraMap Si Sj)
      = CommRingCat.ofHom (algebraMap Ri Rj) ≫ CommRingCat.ofHom (algebraMap Rj Sj))
    (H : letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom Ri Si Sj)
          (IsScalarTower.toAlgHom Ri Rj Sj)).toRingHom.toAlgebra
      ∃ (p : Ideal (Si ⊗[Ri] Rj)) (_ : p.IsPrime), IsLocalization p.primeCompl Sj) :
    letI := (pushout.desc (CommRingCat.ofHom (algebraMap Si Sj))
        (CommRingCat.ofHom (algebraMap Rj Sj)) sq).hom.toAlgebra
    ∃ (p : Ideal ↑(pushout (CommRingCat.ofHom (algebraMap Ri Si))
        (CommRingCat.ofHom (algebraMap Ri Rj)))) (_ : p.IsPrime),
      IsLocalization p.primeCompl Sj := by
  have hpo := CommRingCat.isPushout_tensorProduct Ri Si Rj
  set can : (Si ⊗[Ri] Rj) →ₐ[Ri] Sj := Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom Ri Si Sj) (IsScalarTower.toAlgHom Ri Rj Sj) with hcan
  have key : hpo.isoPushout.inv ≫ CommRingCat.ofHom can.toRingHom
      = pushout.desc (CommRingCat.ofHom (algebraMap Si Sj))
          (CommRingCat.ofHom (algebraMap Rj Sj)) sq := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hpo.inl_isoPushout_inv, pushout.inl_desc]
      ext x
      simp [hcan]
    · rw [← Category.assoc, hpo.inr_isoPushout_inv, pushout.inr_desc]
      ext x
      simp [hcan]
  let instT : Algebra (Si ⊗[Ri] Rj) Sj := can.toRingHom.toAlgebra
  let instP := (pushout.desc (CommRingCat.ofHom (algebraMap Si Sj))
        (CommRingCat.ofHom (algebraMap Rj Sj)) sq).hom.toAlgebra
  exact exists_isLocalization_primeCompl_of_ringEquiv
    hpo.isoPushout.symm.commRingCatIsoToRingEquiv
    (fun x => congrArg (fun g => CommRingCat.Hom.hom g x) key.symm) H

/-- **The cartesian condition, in the pushout form the statement of 00QX uses.**

`descent_core` states condition (4) of 00QV as `IsLocalizationAtPrimeOfBaseChange`, i.e. with
`S_i ⊗_{R_i} R_j` spelled as a tensor product and the map to `S_j` as
`Algebra.TensorProduct.productMap`. The statement of 00QX spells the same ring as the pushout
of `φ_i` along `A.map h` in `CommRingCat`, with the map to `S_j` given by `pushout.desc`.
The two agree, by
`exists_isLocalization_primeCompl_pushout_of_tensorProduct`. -/
private theorem isLocalization_primeCompl_pushout_of_isLocalizationAtPrimeOfBaseChange
    {Λ : Type u} [Preorder Λ]
    (Robj Sobj : Λ → Type u) [∀ i, CommRing (Robj i)] [∀ i, CommRing (Sobj i)]
    (fR : ∀ i j, i ≤ j → Robj i →+* Robj j) (fS : ∀ i j, i ≤ j → Sobj i →+* Sobj j)
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (hSdir : DirectedSystem Sobj (fun i j h => (fS i j h : Sobj i → Sobj j)))
    (ψ : ∀ i, Robj i →+* Sobj i)
    (comm : ∀ i j (hij : i ≤ j), (ψ j).comp (fR i j hij) = (fS i j hij).comp (ψ i))
    {i j : Λ} (h : i ⟶ j)
    (hbc : IsLocalizationAtPrimeOfBaseChange fR fS ψ comm i j (leOfHom h)) :
    letI A := sysFunctor Robj fR hRdir
    letI B := sysFunctor Sobj fS hSdir
    letI φ := sysNatTrans Robj Sobj fR fS hRdir hSdir ψ comm
    letI := (pushout.desc (B.map h) (φ.app j) (φ.naturality h).symm).hom.toAlgebra
    ∃ (p : Ideal ↑(pushout (φ.app i) (A.map h))) (_ : p.IsPrime),
      IsLocalization p.primeCompl ↑(B.obj j) := by
  let _ : Algebra (Robj i) (Sobj i) := (ψ i).toAlgebra
  let _ : Algebra (Robj i) (Robj j) := (fR i j (leOfHom h)).toAlgebra
  let _ : Algebra (Robj i) (Sobj j) := ((ψ j).comp (fR i j (leOfHom h))).toAlgebra
  let _ : Algebra (Sobj i) (Sobj j) := (fS i j (leOfHom h)).toAlgebra
  let _ : Algebra (Robj j) (Sobj j) := (ψ j).toAlgebra
  have _ : IsScalarTower (Robj i) (Sobj i) (Sobj j) :=
    IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (comm i j (leOfHom h)) x
  have _ : IsScalarTower (Robj i) (Robj j) (Sobj j) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact exists_isLocalization_primeCompl_pushout_of_tensorProduct _ hbc

/-!
### Passing to a tail of the index

The presentation matrix of `M` lives at a single stage `l`, so the module system is defined
only from `l` on. That is why the conclusion of 00QX is allowed to replace the index: the tail
`{x // l ≤ x}` of a directed preorder is a final subcategory, so restricting a colimit cocone
to it gives a colimit cocone again.
-/

/-- The tail `{x // l ≤ x}` of a preorder, included into it. -/
public def tailFunctor {Λ : Type u} [Preorder Λ] (l : Λ) : {x : Λ // l ≤ x} ⥤ Λ :=
  Monotone.functor (f := (Subtype.val : {x : Λ // l ≤ x} → Λ)) fun _ _ h => h

private lemma tailFunctor_full {Λ : Type u} [Preorder Λ] (l : Λ) : (tailFunctor l).Full where
  map_surjective h := ⟨homOfLE (leOfHom h), rfl⟩

private lemma tailFunctor_faithful {Λ : Type u} [Preorder Λ] (l : Λ) :
    (tailFunctor l).Faithful where
  map_injective _ := Subsingleton.elim _ _

attribute [local instance] tailFunctor_full tailFunctor_faithful

/-- **A tail of a directed preorder is final in it.** Hence a cocone restricted to a tail is a
colimit cocone as soon as the original one is, by
`CategoryTheory.Functor.Final.isColimitWhiskerEquiv`. -/
public lemma tailFunctor_final {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (l : Λ) :
    (tailFunctor l).Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ fun d => by
    obtain ⟨c, hlc, hdc⟩ := directed_of (· ≤ ·) l d
    exact ⟨⟨c, hlc⟩, ⟨homOfLE hdc⟩⟩

attribute [local instance] tailFunctor_final

/-- A tail of a directed preorder is directed. -/
public lemma isDirected_tail {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (l : Λ) :
    IsDirected {x : Λ // l ≤ x} (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
  exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩

/-!
### Descending a presentation of `M` to a stage

`descent_core` says nothing about `M`, so the module system has to be built by hand from a
presentation `S^{⊕s} → S^{⊕n} → M → 0`. Its matrix has finitely many entries, so all of them
come from a single `B_l`, and for `λ ≥ l` one takes `N_λ` to be the cokernel of the lifted
matrix over `B_λ`. The three conditions are then elementary: `N_λ` is a quotient of
`B_λ^{⊕n}`, so it is finite; the colimit of the `N_λ` is `M` because a filtered colimit of
abelian groups is computed on elements; and `N_μ` is the base change of `N_λ` because a
cokernel of a map of finite free modules base-changes to the cokernel of the same matrix.
-/

/-- **A criterion for a cocone of abelian groups over a filtered index to be a colimit:**
its legs are jointly surjective, and an element killed by a leg already dies at a later
stage. Mathlib has the two consequences — `CategoryTheory.Limits.Concrete.colimit_exists_rep`
and `CategoryTheory.Limits.IsColimit.eq_iff` — but not this converse. -/
public noncomputable def isColimitAddCommGrpCatOf {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ AddCommGrpCat.{u}) (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ (j : J) (y : F.obj j), (c.ι.app j) y = x)
    (hzero : ∀ (j : J) (y : F.obj j), (c.ι.app j) y = 0 →
      ∃ (k : J) (f : j ⟶ k), (F.map f) y = 0) :
    IsColimit c := by
  have hc := colimit.isColimit F
  have hfac : ∀ (j : J) (y : F.obj j), (hc.desc c) ((colimit.ι F j) y) = (c.ι.app j) y :=
    fun j y => congrArg (fun g : F.obj j ⟶ c.pt => g y) (hc.fac c j)
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : F.obj j),
      (colimit.ι F k) ((F.map f) y) = (colimit.ι F j) y :=
    fun {j k} f y => congrArg (fun t : F.obj j ⟶ colimit F => t y) (colimit.w F f)
  have hcw : ∀ {j k : J} (f : j ⟶ k) (y : F.obj j),
      (c.ι.app k) ((F.map f) y) = (c.ι.app j) y :=
    fun {j k} f y => congrArg (fun t : F.obj j ⟶ c.pt => t y) (c.w f)
  haveI : IsIso (hc.desc c) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun z z' hzz' => ?_, fun x => ?_⟩
    · obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep F z
      obtain ⟨j', y', rfl⟩ := Concrete.colimit_exists_rep F z'
      rw [hfac, hfac] at hzz'
      have hk : (c.ι.app (IsFiltered.max j j'))
          ((F.map (IsFiltered.leftToMax j j')) y
            - (F.map (IsFiltered.rightToMax j j')) y') = 0 := by
        rw [map_sub, hcw, hcw, hzz', sub_self]
      obtain ⟨m, t, ht⟩ := hzero _ _ hk
      rw [map_sub, sub_eq_zero] at ht
      rw [← hw (IsFiltered.leftToMax j j' ≫ t) y, ← hw (IsFiltered.rightToMax j j' ≫ t) y',
        F.map_comp, F.map_comp]
      exact congrArg _ ht
    · obtain ⟨j, y, rfl⟩ := hsurj x
      exact ⟨(colimit.ι F j) y, hfac j y⟩
  exact hc.ofPointIso

/-- **The same criterion for a cocone of commutative rings over a filtered index:** its legs
are jointly surjective, and an element killed by a leg already dies at a later stage. The proof
is that of `isColimitAddCommGrpCatOf`, which uses of the ambient category only that its
forgetful functor is faithful, reflects isomorphisms and preserves filtered colimits, and that
its morphisms are additive. -/
public noncomputable def isColimitCommRingCatOf {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ (j : J) (y : F.obj j), (c.ι.app j) y = x)
    (hzero : ∀ (j : J) (y : F.obj j), (c.ι.app j) y = 0 →
      ∃ (k : J) (f : j ⟶ k), (F.map f) y = 0) :
    IsColimit c := by
  have hc := colimit.isColimit F
  have hfac : ∀ (j : J) (y : F.obj j), (hc.desc c) ((colimit.ι F j) y) = (c.ι.app j) y :=
    fun j y => congrArg (fun g : F.obj j ⟶ c.pt => g y) (hc.fac c j)
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : F.obj j),
      (colimit.ι F k) ((F.map f) y) = (colimit.ι F j) y :=
    fun {j k} f y => congrArg (fun t : F.obj j ⟶ colimit F => t y) (colimit.w F f)
  have hcw : ∀ {j k : J} (f : j ⟶ k) (y : F.obj j),
      (c.ι.app k) ((F.map f) y) = (c.ι.app j) y :=
    fun {j k} f y => congrArg (fun t : F.obj j ⟶ c.pt => t y) (c.w f)
  haveI : IsIso (hc.desc c) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun z z' hzz' => ?_, fun x => ?_⟩
    · obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep F z
      obtain ⟨j', y', rfl⟩ := Concrete.colimit_exists_rep F z'
      rw [hfac, hfac] at hzz'
      have hk : (c.ι.app (IsFiltered.max j j'))
          ((F.map (IsFiltered.leftToMax j j')) y
            - (F.map (IsFiltered.rightToMax j j')) y') = 0 := by
        rw [show ((c.ι.app (IsFiltered.max j j'))
            ((F.map (IsFiltered.leftToMax j j')) y
              - (F.map (IsFiltered.rightToMax j j')) y') : c.pt)
          = (c.ι.app (IsFiltered.max j j')).hom
              ((F.map (IsFiltered.leftToMax j j')) y
                - (F.map (IsFiltered.rightToMax j j')) y') from rfl, map_sub]
        rw [show ((c.ι.app (IsFiltered.max j j')).hom
            ((F.map (IsFiltered.leftToMax j j')) y) : c.pt)
          = (c.ι.app (IsFiltered.max j j')) ((F.map (IsFiltered.leftToMax j j')) y) from rfl]
        rw [show ((c.ι.app (IsFiltered.max j j')).hom
            ((F.map (IsFiltered.rightToMax j j')) y') : c.pt)
          = (c.ι.app (IsFiltered.max j j')) ((F.map (IsFiltered.rightToMax j j')) y') from rfl]
        rw [hcw, hcw, hzz', sub_self]
      obtain ⟨m, t, ht⟩ := hzero _ _ hk
      rw [show ((F.map t) ((F.map (IsFiltered.leftToMax j j')) y
            - (F.map (IsFiltered.rightToMax j j')) y') : F.obj m)
        = (F.map t).hom ((F.map (IsFiltered.leftToMax j j')) y
            - (F.map (IsFiltered.rightToMax j j')) y') from rfl, map_sub, sub_eq_zero] at ht
      rw [← hw (IsFiltered.leftToMax j j' ≫ t) y, ← hw (IsFiltered.rightToMax j j' ≫ t) y',
        F.map_comp, F.map_comp]
      exact congrArg _ ht
    · obtain ⟨j, y, rfl⟩ := hsurj x
      exact ⟨(colimit.ι F j) y, hfac j y⟩
  exact hc.ofPointIso

/-- The leg `B_i → S` of a cocone of rings, as a ring homomorphism. -/
public def legHom {J : Type u} [Preorder J] {S : Type u} [CommRing S]
    {B : J ⥤ CommRingCat.{u}} (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S)) (i : J) :
    ↑(B.obj i) →+* S :=
  (σ.app i).hom

/-- The legs `legHom σ` are compatible with the transition maps of the system. -/
public lemma legHom_map {J : Type u} [Preorder J] {S : Type u} [CommRing S]
    {B : J ⥤ CommRingCat.{u}} (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S))
    {i j : J} (h : i ⟶ j) (x : ↑(B.obj i)) :
    legHom σ j ((B.map h).hom x) = legHom σ i x :=
  congrArg (fun g => CommRingCat.Hom.hom g x) ((Cocone.mk (CommRingCat.of S) σ).w h)

/-- Finitely many indices of a directed preorder have a common upper bound above any given one. -/
private theorem exists_forall_le_of_finite {J : Type u} [Preorder J] [Nonempty J]
    [IsDirected J (· ≤ ·)] {α : Type*} [Finite α] (k : α → J) (i₀ : J) :
    ∃ p, i₀ ≤ p ∧ ∀ x, k x ≤ p := by
  obtain ⟨M, hM⟩ := Finite.exists_le k
  obtain ⟨p, hp, hMp⟩ := directed_of (· ≤ ·) i₀ M
  exact ⟨p, hp, fun x => (hM x).trans hMp⟩

/-- Finitely many elements of a filtered colimit of rings come from a common stage, which may
moreover be taken above any prescribed one. -/
public lemma exists_stage_lift {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    {S : Type u} [CommRing S] {B : J ⥤ CommRingCat.{u}}
    (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S))
    (hσ : IsColimit (Cocone.mk (CommRingCat.of S) σ))
    {α : Type*} [Finite α] (y : α → S) (i₀ : J) :
    ∃ (j : J) (_ : i₀ ≤ j) (z : α → ↑(B.obj j)), ∀ a, legHom σ j (z a) = y a := by
  choose ix iy hiy using fun a => Concrete.isColimit_exists_rep B hσ (y a)
  obtain ⟨j, hij, key⟩ := exists_forall_le_of_finite ix i₀
  refine ⟨j, hij, fun a => (B.map (homOfLE (key a))).hom (iy a), fun a => ?_⟩
  exact (congrArg (fun g => CommRingCat.Hom.hom g (iy a))
    ((Cocone.mk (CommRingCat.of S) σ).w (homOfLE (key a)))).trans (hiy a)

/-- Finitely many pairs of elements of `B_j` with equal images in the colimit already agree at
a single later stage. -/
public lemma exists_eventually_eq {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    {S : Type u} [CommRing S] {B : J ⥤ CommRingCat.{u}}
    (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S))
    (hσ : IsColimit (Cocone.mk (CommRingCat.of S) σ))
    {α : Type*} [Finite α] {j : J} (a b : α → ↑(B.obj j))
    (hab : ∀ x, legHom σ j (a x) = legHom σ j (b x)) :
    ∃ (p : J) (hjp : j ≤ p),
      ∀ x, (B.map (homOfLE hjp)).hom (a x) = (B.map (homOfLE hjp)).hom (b x) := by
  have key : ∀ x : α, ∃ (k : J) (hjk : j ≤ k),
      (B.map (homOfLE hjk)).hom (a x) = (B.map (homOfLE hjk)).hom (b x) := by
    intro x
    obtain ⟨k, f, g, hfg⟩ := (IsColimit.eq_iff B hσ).1 (hab x)
    exact ⟨k, leOfHom f, hfg⟩
  choose kk hkk hk using key
  obtain ⟨p, hjp, hkp⟩ := exists_forall_le_of_finite kk j
  refine ⟨p, hjp, fun x => ?_⟩
  have e1 : ∀ y : ↑(B.obj j), (B.map (homOfLE hjp)).hom y
      = (B.map (homOfLE (hkp x))).hom ((B.map (homOfLE (hkk x))).hom y) :=
    fun y => congrArg (fun t => CommRingCat.Hom.hom t y)
      (B.map_comp (homOfLE (hkk x)) (homOfLE (hkp x)))
  rw [e1 (a x), e1 (b x), hk x]

/-- A transition ring map of the system, applied to each coordinate of `B_i^{⊕n}`. -/
public def coordMap {J : Type u} [Preorder J] (B : J ⥤ CommRingCat.{u}) (n : ℕ)
    {i j : J} (h : i ⟶ j) :
    (Fin n → ↑(B.obj i)) →ₛₗ[(B.map h).hom] (Fin n → ↑(B.obj j)) where
  toFun x := fun m => (B.map h).hom (x m)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_mul _ _ _

/-- `coordMap` is functorial: the map along a composite is the composite of the maps. -/
public lemma coordMap_comp {J : Type u} [Preorder J] (B : J ⥤ CommRingCat.{u}) (n : ℕ)
    {i j k : J} (h : i ⟶ j) (h' : j ⟶ k) (x : Fin n → ↑(B.obj i)) :
    coordMap B n (h ≫ h') x = coordMap B n h' (coordMap B n h x) :=
  funext fun m => congrArg (fun t => CommRingCat.Hom.hom t (x m)) (B.map_comp h h')

/-- `coordMap` sends each standard basis vector of `B_i^{⊕n}` to the same basis vector of
`B_j^{⊕n}`. -/
public lemma coordMap_single {J : Type u} [Preorder J] (B : J ⥤ CommRingCat.{u}) (n : ℕ)
    {i j : J} (h : i ⟶ j) (m : Fin n) :
    coordMap B n h (Pi.single m 1) = Pi.single m 1 := by
  funext m'
  change (B.map h).hom ((Pi.single m 1 : Fin n → ↑(B.obj i)) m')
    = (Pi.single m 1 : Fin n → ↑(B.obj j)) m'
  by_cases hm : m' = m
  · subst hm
    rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne hm, Pi.single_eq_of_ne hm, map_zero]

/-- The leg `B_i^{⊕n} → S^{⊕n}` of the cocone of rings, coordinatewise. -/
public def coordLeg {J : Type u} [Preorder J] {S : Type u} [CommRing S]
    {B : J ⥤ CommRingCat.{u}} (n : ℕ)
    (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S)) (i : J) :
    (Fin n → ↑(B.obj i)) →ₛₗ[legHom σ i] (Fin n → S) where
  toFun x := fun m => legHom σ i (x m)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_mul _ _ _

/-- The coordinatewise legs `coordLeg` are compatible with the transition maps `coordMap`. -/
public lemma coordLeg_coordMap {J : Type u} [Preorder J] {S : Type u} [CommRing S]
    {B : J ⥤ CommRingCat.{u}} (n : ℕ)
    (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S)) {i j : J} (h : i ⟶ j)
    (x : Fin n → ↑(B.obj i)) :
    coordLeg n σ j (coordMap B n h x) = coordLeg n σ i x :=
  funext fun m => legHom_map σ h (x m)

/-- Every vector of `A^{⊕n}` is the sum of its coordinates times the standard basis vectors. -/
public lemma sum_smul_single {A : Type u} [CommRing A] {n : ℕ} (x : Fin n → A) :
    ∑ m, x m • (Pi.single m 1 : Fin n → A) = x := by
  have h1 : ∀ m, x m • (Pi.single m 1 : Fin n → A) = Pi.single m (x m) := by
    intro m
    rw [← Pi.single_smul]
    simp
  simp only [h1, Finset.univ_sum_single]

/-- A linear map out of `A^{⊕n}` modulo a submodule is determined by the images of the classes of
the standard basis vectors. -/
private lemma linearMap_mk_eq_sum {A : Type u} [CommRing A] {n : ℕ} {W : Submodule A (Fin n → A)}
    {Q : Type*} [AddCommMonoid Q] [Module A Q] (g : ((Fin n → A) ⧸ W) →ₗ[A] Q)
    (y : Fin n → A) :
    g (Submodule.Quotient.mk y) = ∑ m, y m • g (Submodule.Quotient.mk (Pi.single m 1)) := by
  calc g (Submodule.Quotient.mk y)
      = (g ∘ₗ W.mkQ) (∑ m, y m • (Pi.single m 1 : Fin n → A)) := by
        rw [sum_smul_single y]; rfl
    _ = _ := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun m _ => by rw [map_smul]; rfl

/-- The submodule of relations at stage `i`: the span of the lifted presentation matrix. -/
public def relSpan {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}} {n : ℕ} {ι : Type u}
    (rel : ∀ i : J, ι → Fin n → ↑(B.obj i)) (i : J) :
    Submodule ↑(B.obj i) (Fin n → ↑(B.obj i)) :=
  Submodule.span _ (Set.range (rel i))

/-- The transition map `coordMap` carries the relations at stage `i` into those at stage `j`,
so it descends to the quotients. -/
public lemma relSpan_le_ker {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}} {n : ℕ}
    {ι : Type u} (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    {i j : J} (h : i ⟶ j) :
    relSpan rel i ≤ LinearMap.ker ((relSpan rel j).mkQ ∘ₛₗ coordMap B n h) := by
  rw [relSpan, Submodule.span_le]
  rintro x ⟨k, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero,
    show coordMap B n h (rel i k) = rel j k from funext fun m => hrel h k m]
  exact Submodule.subset_span ⟨k, rfl⟩

/-- The transition map of the module system, semilinear over the transition ring map. -/
public def relQuotMap {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}} {n : ℕ} {ι : Type u}
    (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    {i j : J} (h : i ⟶ j) :
    ((Fin n → ↑(B.obj i)) ⧸ relSpan rel i) →ₛₗ[(B.map h).hom]
      ((Fin n → ↑(B.obj j)) ⧸ relSpan rel j) :=
  Submodule.liftQ _ _ (relSpan_le_ker rel hrel h)

/-- The module system: `i ↦ B_i^{⊕n}` modulo the lifted relations. -/
public def relQuot {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}} {n : ℕ} {ι : Type u}
    (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m) :
    J ⥤ AddCommGrpCat.{u} where
  obj i := AddCommGrpCat.of ((Fin n → ↑(B.obj i)) ⧸ relSpan rel i)
  map h := AddCommGrpCat.ofHom (relQuotMap rel hrel h).toAddMonoidHom
  map_id i := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (coordMap B n (𝟙 i) y) = Submodule.Quotient.mk y
    exact congrArg _ (funext fun m =>
      congrArg (fun g => CommRingCat.Hom.hom g (y m)) (B.map_id i))
  map_comp {i j k} f g := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (coordMap B n (f ≫ g) y)
      = Submodule.Quotient.mk (coordMap B n g (coordMap B n f y))
    exact congrArg _ (coordMap_comp B n f g y)

/-- On the class of a vector, the transition map of `relQuot` is the class of its image under
`coordMap`. -/
public lemma relQuot_map_mk {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}} {n : ℕ}
    {ι : Type u} (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    {i j : J} (h : i ⟶ j) (y : Fin n → ↑(B.obj i)) :
    (relQuot rel hrel).map h (Submodule.Quotient.mk y)
      = Submodule.Quotient.mk (coordMap B n h y) :=
  rfl

/-- The transition maps of the module system are semilinear over those of the ring system. -/
public lemma relQuot_map_smul {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}} {n : ℕ}
    {ι : Type u} (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    ⦃i j : J⦄ (h : i ⟶ j) (b : ↑(B.obj i))
    (m : (Fin n → ↑(B.obj i)) ⧸ relSpan rel i) :
    (relQuot rel hrel).map h (b • m) = (B.map h) b • relQuotMap rel hrel h m :=
  map_smulₛₗ (relQuotMap rel hrel h) b m

/-- Each `N_i` is a finite `B_i`-module: it is a quotient of `B_i^{⊕n}`. -/
public lemma relQuot_finite {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}} {n : ℕ}
    {ι : Type u} (rel : ∀ i : J, ι → Fin n → ↑(B.obj i)) (i : J) :
    Module.Finite ↑(B.obj i) ((Fin n → ↑(B.obj i)) ⧸ relSpan rel i) :=
  Module.Finite.of_surjective (relSpan rel i).mkQ (Submodule.Quotient.mk_surjective _)

/-- **The cartesian condition on the modules.** `N_j` is the base change of `N_i` along
`B_i → B_j`, because a cokernel of a map of finite free modules base-changes to the cokernel of
the same matrix. The proof is the universal property: a `B_i`-linear map out of `N_i` is `n`
elements of the target killing the relations, and after base change the relations are the images
of the same ones, so they impose the same conditions. -/
public lemma isBaseChange_relQuot {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}} {n : ℕ}
    {ι : Type u} (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    {i j : J} (h : i ⟶ j) :
    letI := (B.map h).hom.toAlgebra
    letI : Module ↑(B.obj i) ((Fin n → ↑(B.obj j)) ⧸ relSpan rel j) :=
      Module.compHom _ (B.map h).hom
    letI : IsScalarTower ↑(B.obj i) ↑(B.obj j) ((Fin n → ↑(B.obj j)) ⧸ relSpan rel j) :=
      .of_algebraMap_smul fun _ _ => rfl
    ∀ (f : ((Fin n → ↑(B.obj i)) ⧸ relSpan rel i) →ₗ[↑(B.obj i)]
        ((Fin n → ↑(B.obj j)) ⧸ relSpan rel j)),
      (∀ y : Fin n → ↑(B.obj i),
        f (Submodule.Quotient.mk y) = Submodule.Quotient.mk (coordMap B n h y)) →
      IsBaseChange ↑(B.obj j) f := by
  let _ : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map h).hom.toAlgebra
  let _ : Module ↑(B.obj i) ((Fin n → ↑(B.obj j)) ⧸ relSpan rel j) :=
    Module.compHom _ (B.map h).hom
  let _ : IsScalarTower ↑(B.obj i) ↑(B.obj j) ((Fin n → ↑(B.obj j)) ⧸ relSpan rel j) :=
    .of_algebraMap_smul fun _ _ => rfl
  intro f hf
  have halg : ∀ a : ↑(B.obj i), algebraMap ↑(B.obj i) ↑(B.obj j) a = (B.map h).hom a :=
    fun _ => rfl
  refine IsBaseChange.of_lift_unique f ?_
  intro Q _ _ _ _ g
  -- a module over a ring is an additive group, which is what `Submodule.liftQ` needs
  let _ : AddCommGroup Q := Module.addCommMonoidToAddCommGroup ↑(B.obj j)
  obtain ⟨q, hq⟩ : ∃ q : Fin n → Q,
      ∀ m, q m = g (Submodule.Quotient.mk (Pi.single m 1)) :=
    ⟨fun m => g (Submodule.Quotient.mk (Pi.single m 1)), fun _ => rfl⟩
  set G : (Fin n → ↑(B.obj j)) →ₗ[↑(B.obj j)] Q :=
    Fintype.linearCombination ↑(B.obj j) q with hGdef
  have hG : ∀ y : Fin n → ↑(B.obj j), G y = ∑ m, y m • q m := fun _ => rfl
  -- `g` is determined by its values on the images of the standard basis vectors
  have hgmk : ∀ y : Fin n → ↑(B.obj i),
      g (Submodule.Quotient.mk y) = ∑ m, y m • q m := fun y => by
    simp only [hq]; exact linearMap_mk_eq_sum g y
  -- and `G` agrees with `g` after base change
  have hGcoord : ∀ y : Fin n → ↑(B.obj i),
      G (coordMap B n h y) = ∑ m, y m • q m := by
    intro y
    rw [hG]
    refine Finset.sum_congr rfl fun m _ => ?_
    change (B.map h) (y m) • q m = y m • q m
    rw [← halg (y m), algebraMap_smul]
  have hker : relSpan rel j ≤ LinearMap.ker G := by
    rw [relSpan, Submodule.span_le]
    rintro x ⟨k, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [show rel j k = coordMap B n h (rel i k) from (funext fun m => hrel h k m).symm,
      hGcoord, ← hgmk,
      show (Submodule.Quotient.mk (rel i k) : (Fin n → ↑(B.obj i)) ⧸ relSpan rel i) = 0 from
        (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨k, rfl⟩), map_zero]
  refine ⟨Submodule.liftQ (relSpan rel j) G hker, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (Submodule.liftQ (relSpan rel j) G hker) (f (Submodule.Quotient.mk y))
      = g (Submodule.Quotient.mk y)
    rw [hf y]
    change G (coordMap B n h y) = g (Submodule.Quotient.mk y)
    rw [hGcoord, hgmk]
  · intro g' hg'
    have hbasis : ∀ m : Fin n,
        g' (Submodule.Quotient.mk (Pi.single m 1 : Fin n → ↑(B.obj j))) = q m := by
      intro m
      have h1 : f (Submodule.Quotient.mk (Pi.single m 1 : Fin n → ↑(B.obj i)))
          = Submodule.Quotient.mk (Pi.single m 1 : Fin n → ↑(B.obj j)) := by
        rw [hf, coordMap_single]
      have h2 : g' (f (Submodule.Quotient.mk (Pi.single m 1 : Fin n → ↑(B.obj i))))
          = g (Submodule.Quotient.mk (Pi.single m 1 : Fin n → ↑(B.obj i))) :=
        congrArg (fun t => t (Submodule.Quotient.mk
          (Pi.single m 1 : Fin n → ↑(B.obj i)))) hg'
      rw [h1] at h2
      rw [h2, hq m]
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [linearMap_mk_eq_sum g']
    exact (Finset.sum_congr rfl fun m _ => by rw [hbasis m]).trans (hG y).symm

/-- The leg `N_i → M` of the module cocone, read through the presentation of `M`. -/
public def modLeg {J : Type u} [Preorder J] {S : Type u} [CommRing S]
    {B : J ⥤ CommRingCat.{u}} {n : ℕ} {ι : Type u}
    (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S)) {v : ι → Fin n → S}
    (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hv : ∀ (i : J) (k : ι) (m : Fin n), legHom σ i (rel i k m) = v k m) (i : J) :
    ((Fin n → ↑(B.obj i)) ⧸ relSpan rel i) →ₛₗ[legHom σ i]
      ((Fin n → S) ⧸ Submodule.span S (Set.range v)) := by
  refine Submodule.liftQ _ ((Submodule.span S (Set.range v)).mkQ ∘ₛₗ coordLeg n σ i) ?_
  rw [relSpan, Submodule.span_le]
  rintro x ⟨k, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero,
    show coordLeg n σ i (rel i k) = v k from funext fun m => hv i k m]
  exact Submodule.subset_span ⟨k, rfl⟩

/-- The module cocone `N ⟶ M`. -/
public def modCocone {J : Type u} [Preorder J] {S M : Type u} [CommRing S] [AddCommGroup M]
    [Module S M] {B : J ⥤ CommRingCat.{u}} {n : ℕ} {ι : Type u}
    (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S)) {v : ι → Fin n → S}
    (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    (hv : ∀ (i : J) (k : ι) (m : Fin n), legHom σ i (rel i k m) = v k m)
    (e : M ≃ₗ[S] ((Fin n → S) ⧸ Submodule.span S (Set.range v))) :
    relQuot rel hrel ⟶ (Functor.const J).obj (AddCommGrpCat.of M) where
  app i := AddCommGrpCat.ofHom
    ((e.symm.toLinearMap.toAddMonoidHom).comp (modLeg σ rel hv i).toAddMonoidHom)
  naturality {i j} h := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg e.symm
      (congrArg Submodule.Quotient.mk (coordLeg_coordMap n σ h y))

/-- On the class of a vector, the leg of `modCocone` is `e.symm` of the class of its coordinatewise
image in `S^{⊕n}`. -/
public lemma modCocone_app_mk {J : Type u} [Preorder J] {S M : Type u} [CommRing S]
    [AddCommGroup M] [Module S M] {B : J ⥤ CommRingCat.{u}} {n : ℕ} {ι : Type u}
    (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S)) {v : ι → Fin n → S}
    (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    (hv : ∀ (i : J) (k : ι) (m : Fin n), legHom σ i (rel i k m) = v k m)
    (e : M ≃ₗ[S] ((Fin n → S) ⧸ Submodule.span S (Set.range v)))
    (i : J) (y : Fin n → ↑(B.obj i)) :
    (modCocone σ rel hrel hv e).app i (Submodule.Quotient.mk y)
      = e.symm (Submodule.Quotient.mk (coordLeg n σ i y)) :=
  rfl

/-- **The module cocone of a lifted presentation is a colimit.** Its legs are jointly
surjective because finitely many elements of `S` come from one stage, and an element killed by a
leg dies at a later stage because the relation witnessing its vanishing over `S` descends. -/
public noncomputable def isColimit_modCocone {S M : Type u} [CommRing S] [AddCommGroup M]
    [Module S M] {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (B : J ⥤ CommRingCat.{u}) (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S))
    (hσ : IsColimit (Cocone.mk (CommRingCat.of S) σ))
    {n : ℕ} {ι : Type u} [Finite ι] {v : ι → Fin n → S}
    (e : M ≃ₗ[S] ((Fin n → S) ⧸ Submodule.span S (Set.range v)))
    (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    (hv : ∀ (i : J) (k : ι) (m : Fin n), legHom σ i (rel i k m) = v k m) :
    IsColimit (Cocone.mk (AddCommGrpCat.of M) (modCocone σ rel hrel hv e)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have : IsFiltered J := inferInstance
  refine isColimitAddCommGrpCatOf _ _ (fun x => ?_) (fun i y hy => ?_)
  · obtain ⟨y, hy⟩ :=
      Submodule.Quotient.mk_surjective (Submodule.span S (Set.range v)) (e x)
    obtain ⟨i, -, z, hz⟩ := exists_stage_lift σ hσ y (Classical.arbitrary J)
    refine ⟨i, Submodule.Quotient.mk z, ?_⟩
    rw [modCocone_app_mk, show coordLeg n σ i z = y from funext hz, hy,
      e.symm_apply_apply]
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (relSpan rel i) y
    rw [modCocone_app_mk] at hy
    have h2 := congrArg e hy
    rw [e.apply_symm_apply, map_zero] at h2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1
      ((Submodule.Quotient.mk_eq_zero _).1 h2)
    obtain ⟨j, hij, d, hd⟩ := exists_stage_lift σ hσ c i
    have hcomp : ∀ m, legHom σ j ((∑ k, d k • rel j k) m)
        = legHom σ j ((coordMap B n (homOfLE hij) z) m) := by
      have e1 : coordLeg n σ j (∑ k, d k • rel j k) = ∑ k, c k • v k := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smulₛₗ, hd k, show coordLeg n σ j (rel j k) = v k from
          funext fun m => hv j k m]
      exact congrFun (e1.trans (hc.trans (coordLeg_coordMap n σ (homOfLE hij) z).symm))
    obtain ⟨p, hjp, hp⟩ :=
      exists_eventually_eq σ hσ (∑ k, d k • rel j k) (coordMap B n (homOfLE hij) z) hcomp
    refine ⟨p, homOfLE hij ≫ homOfLE hjp, ?_⟩
    have hmem : coordMap B n (homOfLE hij ≫ homOfLE hjp) z ∈ relSpan rel p := by
      rw [coordMap_comp B n (homOfLE hij) (homOfLE hjp) z,
        show coordMap B n (homOfLE hjp) (coordMap B n (homOfLE hij) z)
          = coordMap B n (homOfLE hjp) (∑ k, d k • rel j k) from funext fun m => (hp m).symm,
        map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [map_smulₛₗ, show coordMap B n (homOfLE hjp) (rel j k) = rel p k from
        funext fun m => hrel (homOfLE hjp) k m]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    change (Submodule.Quotient.mk (coordMap B n (homOfLE hij ≫ homOfLE hjp) z) :
      (Fin n → ↑(B.obj p)) ⧸ relSpan rel p) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 hmem

/-- The legs of the module cocone are semilinear over the legs of the ring cocone: this is what
pins the `S`-module structure on the colimit. -/
public lemma modCocone_app_smul {S M : Type u} [CommRing S] [AddCommGroup M]
    [Module S M] {J : Type u} [Preorder J]
    {B : J ⥤ CommRingCat.{u}} (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S))
    {n : ℕ} {ι : Type u} {v : ι → Fin n → S}
    (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    (hv : ∀ (i : J) (k : ι) (m : Fin n), legHom σ i (rel i k m) = v k m)
    (e : M ≃ₗ[S] ((Fin n → S) ⧸ Submodule.span S (Set.range v)))
    (i : J) (b : B.obj i) (m : (Fin n → ↑(B.obj i)) ⧸ relSpan rel i) :
    ((modCocone σ rel hrel hv e).app i (b • m) : M)
      = HSMul.hSMul (α := S) (β := M) (σ.app i b) ((modCocone σ rel hrel hv e).app i m) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (relSpan rel i) m
  have h1 : (modLeg σ rel hv i) (b • Submodule.Quotient.mk z)
      = legHom σ i b • (modLeg σ rel hv i) (Submodule.Quotient.mk z) :=
    map_smulₛₗ (modLeg σ rel hv i) b (Submodule.Quotient.mk z)
  change e.symm ((modLeg σ rel hv i) (b • Submodule.Quotient.mk z)) = _
  rw [h1, map_smul]
  rfl

/-- **The module system of 00QX built from a presentation of `M` descended to a stage.**

`rel` is the presentation matrix of `M`, lifted to every stage compatibly (`hrel`) and lifting
the matrix `v` over `S` (`hv`); `e` identifies `M` with the cokernel of `v`. -/
public theorem exists_module_system_aux {S M : Type u} [CommRing S] [AddCommGroup M]
    [Module S M] {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (B : J ⥤ CommRingCat.{u}) (σ : B ⟶ (Functor.const J).obj (CommRingCat.of S))
    (hσ : IsColimit (Cocone.mk (CommRingCat.of S) σ))
    {n : ℕ} {ι : Type u} [Finite ι] {v : ι → Fin n → S}
    (e : M ≃ₗ[S] ((Fin n → S) ⧸ Submodule.span S (Set.range v)))
    (rel : ∀ i : J, ι → Fin n → ↑(B.obj i))
    (hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m)
    (hv : ∀ (i : J) (k : ι) (m : Fin n), legHom σ i (rel i k m) = v k m) :
    ∃ (N : J ⥤ AddCommGrpCat.{u}) (_ : ∀ i, Module (B.obj i) (N.obj i))
      (hsmul : ∀ ⦃i j : J⦄ (h : i ⟶ j) (b : B.obj i) (m : N.obj i),
        N.map h (b • m) = B.map h b • N.map h m)
      (ν : N ⟶ (Functor.const J).obj (AddCommGrpCat.of M))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)),
      (∀ (i : J) (b : B.obj i) (m : N.obj i),
        (ν.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M) (σ.app i b) (ν.app i m)) ∧
      (∀ i, Module.Finite (B.obj i) (N.obj i)) ∧
      (∀ ⦃i j : J⦄ (h : i ⟶ j),
        letI := (B.map h).hom.toAlgebra
        letI : Module ↑(B.obj i) ↑(N.obj j) := Module.compHom _ (B.map h).hom
        letI : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(N.obj j) :=
          .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑(B.obj j)
          (⟨(N.map h).hom.toAddHom, hsmul h⟩ :
            ↑(N.obj i) →ₗ[↑(B.obj i)] ↑(N.obj j))) :=
  ⟨relQuot rel hrel,
    fun i => inferInstanceAs (Module ↑(B.obj i) ((Fin n → ↑(B.obj i)) ⧸ relSpan rel i)),
    relQuot_map_smul rel hrel, modCocone σ rel hrel hv e,
    isColimit_modCocone B σ hσ e rel hrel hv, modCocone_app_smul σ rel hrel hv e,
    relQuot_finite rel,
    fun {_ _} h => isBaseChange_relQuot rel hrel h _ (relQuot_map_mk rel hrel h)⟩

/-- **The module half of 00QX, which is all that is left of it.**

Let `B : Λ ⥤ CommRingCat` be a directed system of rings with colimit `S` and let `M` be a
finitely presented `S`-module. Choose a presentation `S^{⊕s} → S^{⊕t} → M → 0`; its `t × s`
matrix has finitely many entries, so all of them come from a single stage `l`, and for `λ ≥ l`
one may take `N_λ` to be the cokernel of the lifted matrix over `B_λ`. Then the `N_λ` form a
functor on the tail `{x // l ≤ x}` with `B_λ`-module structures compatible with the transition
maps, each finite over `B_λ` — a cokernel of a map into `B_λ^{⊕t}` is generated by `t`
elements — with colimit `M`, because cokernels commute with filtered colimits, and cartesian,
because cokernels commute with base change.

Neither locality, nor essential finiteness, nor the cartesian condition (5) on the rings enters
this construction, so it is stated for a bare directed system of rings. -/
private theorem exists_module_system_of_isColimit
    {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    {Λ₀ : Type u} [Preorder Λ₀] [Nonempty Λ₀] [IsDirected Λ₀ (· ≤ ·)]
    (B₀ : Λ₀ ⥤ CommRingCat.{u}) (σ₀ : B₀ ⟶ (Functor.const Λ₀).obj (CommRingCat.of S))
    (hσ₀ : IsColimit (Cocone.mk (CommRingCat.of S) σ₀)) :
    ∃ (l : Λ₀) (N : {x : Λ₀ // l ≤ x} ⥤ AddCommGrpCat.{u})
      (_ : ∀ i, Module ((tailFunctor l ⋙ B₀).obj i) (N.obj i))
      (hsmul : ∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j)
          (b : (tailFunctor l ⋙ B₀).obj i) (m : N.obj i),
        N.map h (b • m) = (tailFunctor l ⋙ B₀).map h b • N.map h m)
      (ν : N ⟶ (Functor.const {x : Λ₀ // l ≤ x}).obj (AddCommGrpCat.of M))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)),
      (∀ (i : {x : Λ₀ // l ≤ x}) (b : (tailFunctor l ⋙ B₀).obj i) (m : N.obj i),
        (ν.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M)
          ((Functor.whiskerLeft (tailFunctor l) σ₀).app i b) (ν.app i m)) ∧
      (∀ i, Module.Finite ((tailFunctor l ⋙ B₀).obj i) (N.obj i)) ∧
      (∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j),
        letI : Algebra ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j) :=
          ((tailFunctor l ⋙ B₀).map h).hom.toAlgebra
        letI : Module ↑((tailFunctor l ⋙ B₀).obj i) ↑(N.obj j) :=
          Module.compHom _ ((tailFunctor l ⋙ B₀).map h).hom
        letI : IsScalarTower ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j)
            ↑(N.obj j) := .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑((tailFunctor l ⋙ B₀).obj j)
          (⟨(N.map h).hom.toAddHom, hsmul h⟩ :
            ↑(N.obj i) →ₗ[↑((tailFunctor l ⋙ B₀).obj i)] ↑(N.obj j))) := by
  classical
  -- a presentation `S^{⊕s} → S^{⊕n} → M → 0` of `M`, its relations indexed by a finite type
  obtain ⟨n, K, e, t, ht⟩ := Module.FinitePresentation.exists_fin S M
  have hspan : Submodule.span S (Set.range (fun x : {x : Fin n → S // x ∈ t} => x.1)) = K := by
    rw [show Set.range (fun x : {x : Fin n → S // x ∈ t} => x.1) = (↑t : Set (Fin n → S)) from
      by ext y; simp]
    exact ht
  -- the finitely many entries of the presentation matrix all come from one stage `l`
  obtain ⟨l, -, z, hz⟩ := exists_stage_lift σ₀ hσ₀
    (fun p : {x : Fin n → S // x ∈ t} × Fin n => p.1.1 p.2) (Classical.arbitrary Λ₀)
  have : Nonempty {x : Λ₀ // l ≤ x} := ⟨⟨l, le_refl l⟩⟩
  have : IsDirected {x : Λ₀ // l ≤ x} (· ≤ ·) := isDirected_tail l
  -- the presentation matrix read at every stage of the tail
  obtain ⟨rel, hreldef⟩ :
      ∃ rel : ∀ i : {x : Λ₀ // l ≤ x}, {x : Fin n → S // x ∈ t} → Fin n →
          ↑((tailFunctor l ⋙ B₀).obj i),
        ∀ (i : {x : Λ₀ // l ≤ x}) (k : {x : Fin n → S // x ∈ t}) (m : Fin n),
          rel i k m = ((tailFunctor l ⋙ B₀).map
            (homOfLE (show (⟨l, le_refl l⟩ : {x : Λ₀ // l ≤ x}) ≤ i from i.2))).hom (z (k, m)) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hrel : ∀ {i j : {x : Λ₀ // l ≤ x}} (h : i ⟶ j)
      (k : {x : Fin n → S // x ∈ t}) (m : Fin n),
      ((tailFunctor l ⋙ B₀).map h).hom (rel i k m) = rel j k m := by
    intro i j h k m
    have hc : ((tailFunctor l ⋙ B₀).map
          (homOfLE (show (⟨l, le_refl l⟩ : {x : Λ₀ // l ≤ x}) ≤ i from i.2)))
        ≫ ((tailFunctor l ⋙ B₀).map h)
        = (tailFunctor l ⋙ B₀).map
          (homOfLE (show (⟨l, le_refl l⟩ : {x : Λ₀ // l ≤ x}) ≤ j from j.2)) := by
      rw [← Functor.map_comp]; rfl
    rw [hreldef, hreldef]
    exact congrArg (fun g => CommRingCat.Hom.hom g (z (k, m))) hc
  have hv : ∀ (i : {x : Λ₀ // l ≤ x}) (k : {x : Fin n → S // x ∈ t}) (m : Fin n),
      legHom (Functor.whiskerLeft (tailFunctor l) σ₀) i (rel i k m) = k.1 m := by
    intro i k m
    rw [hreldef]
    exact (legHom_map (Functor.whiskerLeft (tailFunctor l) σ₀)
      (homOfLE (show (⟨l, le_refl l⟩ : {x : Λ₀ // l ≤ x}) ≤ i from i.2)) (z (k, m))).trans
      (hz (k, m))
  obtain ⟨N, instMod, hsmul, ν, hν, hsemi, hfin, hbc⟩ :=
    exists_module_system_aux (M := M) (tailFunctor l ⋙ B₀)
      (Functor.whiskerLeft (tailFunctor l) σ₀)
      ((Functor.Final.isColimitWhiskerEquiv (tailFunctor l) _).symm hσ₀)
      (e.trans (Submodule.quotEquivOfEq K _ hspan.symm)) rel hrel hv
  exact ⟨l, N, instMod, hsmul, ν, hν, hsemi, hfin, hbc⟩

/-- **The ring system of 00QV, enlarged by the module system of 00QX.**

The ring-side conditions are inherited by the tail `{x // l ≤ x}` of the index on which the
module system lives: the colimit cocones because the tail is final (`tailFunctor_final`), and
everything else because the restricted system is literally the old one at the objects of the
tail. -/
private theorem exists_isColimit_essFiniteType_module_of_ringSystem
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    {Λ₀ : Type u} [Preorder Λ₀] [Nonempty Λ₀] [IsDirected Λ₀ (· ≤ ·)]
    (A₀ B₀ : Λ₀ ⥤ CommRingCat.{u}) (φ₀ : A₀ ⟶ B₀)
    (ρ₀ : A₀ ⟶ (Functor.const Λ₀).obj (CommRingCat.of R))
    (σ₀ : B₀ ⟶ (Functor.const Λ₀).obj (CommRingCat.of S))
    (hρ₀ : IsColimit (Cocone.mk (CommRingCat.of R) ρ₀))
    (hσ₀ : IsColimit (Cocone.mk (CommRingCat.of S) σ₀))
    (hcomm₀ : ∀ i, φ₀.app i ≫ σ₀.app i = ρ₀.app i ≫ CommRingCat.ofHom (algebraMap R S))
    (hAloc : ∀ i, IsLocalRing (A₀.obj i)) (hBloc : ∀ i, IsLocalRing (B₀.obj i))
    (hφloc : ∀ i, IsLocalHom (φ₀.app i).hom) (hρloc : ∀ i, IsLocalHom (ρ₀.app i).hom)
    (hAess : ∀ i, Algebra.EssFiniteType ℤ (A₀.obj i))
    (hφess : ∀ i, (φ₀.app i).hom.EssFiniteType)
    (hcart₀ : ∀ ⦃i j : Λ₀⦄ (h : i ⟶ j),
      letI := (pushout.desc (B₀.map h) (φ₀.app j) (φ₀.naturality h).symm).hom.toAlgebra
      ∃ (p : Ideal ↑(pushout (φ₀.app i) (A₀.map h))) (_ : p.IsPrime),
        IsLocalization p.primeCompl ↑(B₀.obj j)) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (A B : Λ ⥤ CommRingCat.{u}) (φ : A ⟶ B) (N : Λ ⥤ AddCommGrpCat.{u})
      (_ : ∀ i, Module (B.obj i) (N.obj i))
      (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (b : B.obj i) (m : N.obj i),
        N.map h (b • m) = B.map h b • N.map h m)
      (ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (σ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (ν : N ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
      (_ : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
      (_ : IsColimit (Cocone.mk (CommRingCat.of S) σ))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)),
      (∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom (algebraMap R S)) ∧
      (∀ (i : Λ) (b : B.obj i) (m : N.obj i),
        (ν.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M) (σ.app i b) (ν.app i m)) ∧
      (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (B.obj i)) ∧
      (∀ i, IsLocalHom (φ.app i).hom) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧
      (∀ i, Algebra.EssFiniteType ℤ (A.obj i)) ∧
      (∀ i, (φ.app i).hom.EssFiniteType) ∧
      (∀ i, Module.Finite (B.obj i) (N.obj i)) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI := (pushout.desc (B.map h) (φ.app j) (φ.naturality h).symm).hom.toAlgebra
        ∃ (q : Ideal ↑(pushout (φ.app i) (A.map h))) (_ : q.IsPrime),
          IsLocalization q.primeCompl ↑(B.obj j)) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map h).hom.toAlgebra
        letI : Module ↑(B.obj i) ↑(N.obj j) := Module.compHom _ (B.map h).hom
        letI : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(N.obj j) :=
          .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑(B.obj j)
          (⟨(N.map h).hom.toAddHom, hsmul h⟩ :
            ↑(N.obj i) →ₗ[↑(B.obj i)] ↑(N.obj j))) := by
  obtain ⟨l, N, instMod, hsmul, ν, hν, hsemi, hfin, hcart⟩ :=
    exists_module_system_of_isColimit (M := M) B₀ σ₀ hσ₀
  exact ⟨{x : Λ₀ // l ≤ x}, inferInstance, ⟨⟨l, le_refl l⟩⟩, isDirected_tail l,
    tailFunctor l ⋙ A₀, tailFunctor l ⋙ B₀, Functor.whiskerLeft (tailFunctor l) φ₀, N,
    instMod, hsmul,
    Functor.whiskerLeft (tailFunctor l) ρ₀, Functor.whiskerLeft (tailFunctor l) σ₀, ν,
    (Functor.Final.isColimitWhiskerEquiv (tailFunctor l) _).symm hρ₀,
    (Functor.Final.isColimitWhiskerEquiv (tailFunctor l) _).symm hσ₀, hν,
    fun i => hcomm₀ i.1, hsemi, fun i => hAloc i.1, fun i => hBloc i.1,
    fun i => hφloc i.1, fun i => hρloc i.1, fun i => hAess i.1, fun i => hφess i.1, hfin,
    fun {_ _} h => hcart₀ ((tailFunctor l).map h), hcart⟩

/-- **The ring-side system of 00QX.** The first two steps of the source's proof of 00QX, which
say nothing about the module: `S` is a localization at a prime of a finitely presented
`R`-algebra (`exists_finitePresentation_isLocalization_atPrime`), and that presentation is spread
out over a system of local `ℤ`-algebras essentially of finite type by 00QV (`descent_core`), read
here as a pair of functors to `CommRingCat` with colimit cocones. -/
public theorem exists_ringSystem_of_essentiallyOfFinitePresentation
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (A B : Λ ⥤ CommRingCat.{u}) (φ : A ⟶ B)
      (ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (σ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (_ : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
      (_ : IsColimit (Cocone.mk (CommRingCat.of S) σ)),
      (∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom (algebraMap R S)) ∧
      (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (B.obj i)) ∧
      (∀ i, IsLocalHom (φ.app i).hom) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧
      (∀ i, IsLocalHom (σ.app i).hom) ∧
      (∀ i, Algebra.EssFiniteType ℤ (A.obj i)) ∧
      (∀ i, (φ.app i).hom.EssFiniteType) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI := (pushout.desc (B.map h) (φ.app j) (φ.naturality h).symm).hom.toAlgebra
        ∃ (q : Ideal ↑(pushout (φ.app i) (A.map h))) (_ : q.IsPrime),
          IsLocalization q.primeCompl ↑(B.obj j)) := by
  -- Step 1: replace `S` by the localization of a finitely presented `R`-algebra at a prime.
  obtain ⟨P, _, _, _, _, q, hq, hqS, hcomp⟩ :=
    exists_finitePresentation_isLocalization_atPrime hS
  have : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq fun x => (hcomp x).symm
  have := hq
  have := hqS
  -- Step 2: the ring-side system of 00QV.
  obtain ⟨Λ, instP, instNe, instDir, Robj, Sobj, instRC, instSC, instRL, instSL,
      fR, fS, ψ, comm, hRdir, hSdir, hRloc, hSloc, hψloc, ⟨eR, eS, hcomm⟩,
      hRess, hψess, hbc⟩ :=
    descent_core R S (algebraMap R S) inferInstance P inferInstance q.primeCompl hqS rfl
  let _ : Preorder Λ := instP
  let _ : Nonempty Λ := instNe
  let _ : IsDirected Λ (· ≤ ·) := instDir
  let _ : ∀ i, CommRing (Robj i) := instRC
  let _ : ∀ i, CommRing (Sobj i) := instSC
  -- Step 3: read the system as a pair of functors with colimit cocones.
  refine ⟨Λ, instP, instNe, instDir,
    sysFunctor Robj fR hRdir, sysFunctor Sobj fS hSdir,
    sysNatTrans Robj Sobj fR fS hRdir hSdir ψ comm,
    sysCocone Robj fR hRdir R eR, sysCocone Sobj fS hSdir S eS,
    sysIsColimit Robj fR hRdir R eR, sysIsColimit Sobj fS hSdir S eS,
    fun i => ?_, instRL, instSL, hψloc,
    isLocalHom_sysCocone_app Robj fR hRdir R eR hRloc,
    isLocalHom_sysCocone_app Sobj fS hSdir S eS hSloc, hRess, hψess,
    fun {i j} h => isLocalization_primeCompl_pushout_of_isLocalizationAtPrimeOfBaseChange
      Robj Sobj fR fS hRdir hSdir ψ comm h (hbc i j (leOfHom h))⟩
  -- the colimit cocones intertwine `ψ` with `algebraMap R S`
  ext x
  exact directLimit_of_intertwine Robj Sobj fR fS ψ comm eR eS hcomm i x

/-- **Stacks 00QX.** For a local homomorphism `R → S` of local rings which is essentially of
finite presentation and a finitely presented `S`-module `M`, the triple `(R → S, M)` is the
colimit of a directed system `(A i → B i, N i)` of local homomorphisms of local rings and finite
modules, with each `A i` essentially of finite type over `ℤ`, each `A i → B i` essentially of
finite type, each structure map `A i → R` local, each `B j` a localization of
`B i ⊗_{A i} A j` at a prime, and each `N j` the base change of `N i` along `B i → B j`. -/
public theorem solution
    {R S M : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (A B : Λ ⥤ CommRingCat.{u}) (φ : A ⟶ B) (N : Λ ⥤ AddCommGrpCat.{u})
      (_ : ∀ i, Module (B.obj i) (N.obj i))
      (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (b : B.obj i) (m : N.obj i),
        N.map h (b • m) = B.map h b • N.map h m)
      (ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (σ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (ν : N ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
      (_ : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
      (_ : IsColimit (Cocone.mk (CommRingCat.of S) σ))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)),
      (∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom (algebraMap R S)) ∧
      (∀ (i : Λ) (b : B.obj i) (m : N.obj i),
        (ν.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M) (σ.app i b) (ν.app i m)) ∧
      (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (B.obj i)) ∧
      (∀ i, IsLocalHom (φ.app i).hom) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧
      (∀ i, Algebra.EssFiniteType ℤ (A.obj i)) ∧
      (∀ i, (φ.app i).hom.EssFiniteType) ∧
      (∀ i, Module.Finite (B.obj i) (N.obj i)) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI := (pushout.desc (B.map h) (φ.app j) (φ.naturality h).symm).hom.toAlgebra
        ∃ (q : Ideal ↑(pushout (φ.app i) (A.map h))) (_ : q.IsPrime),
          IsLocalization q.primeCompl ↑(B.obj j)) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map h).hom.toAlgebra
        letI : Module ↑(B.obj i) ↑(N.obj j) := Module.compHom _ (B.map h).hom
        letI : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(N.obj j) :=
          .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑(B.obj j)
          (⟨(N.map h).hom.toAddHom, hsmul h⟩ :
            ↑(N.obj i) →ₗ[↑(B.obj i)] ↑(N.obj j))) := by
  obtain ⟨Λ, instP, instNe, instDir, A, B, φ, ρ, σ, hρ, hσ, hcomm, hAloc, hBloc, hφloc,
    hρloc, -, hAess, hφess, hcart⟩ := exists_ringSystem_of_essentiallyOfFinitePresentation hS
  let _ : Preorder Λ := instP
  let _ : Nonempty Λ := instNe
  let _ : IsDirected Λ (· ≤ ·) := instDir
  exact exists_isColimit_essFiniteType_module_of_ringSystem (M := M) A B φ ρ σ hρ hσ hcomm
    hAloc hBloc hφloc hρloc hAess hφess hcart

end Stacks.SpreadingOut.LocalModuleSystem

/-!
# Spreading out a finitely presented module along an essentially finitely presented local map

Let `R → S` be a local homomorphism of local rings which is essentially of finite
presentation, and let `M` be a finitely presented `S`-module. Then the triple
`(R → S, M)` is a filtered colimit of triples `(R_λ → S_λ, M_λ)` in which everything
is of finite character over `ℤ`: each `R_λ` is a local ring essentially of finite type
over `ℤ`, each `R_λ → S_λ` is a local homomorphism of local rings essentially of finite
type, and each `M_λ` is a finite `S_λ`-module. Moreover the system can be chosen
cartesian in the strong sense of the source: for `λ ≤ μ` the ring `S_μ` is a
localization of `S_λ ⊗_{R_λ} R_μ` at a prime ideal, and `M_μ` is the base change
`M_λ ⊗_{S_λ} S_μ`. The last two conditions are what makes such a system usable: by
Remark 00QW an arbitrary system with the first four properties may fail the fifth, so
it has to be built into the statement rather than derived from it.

The system can also be chosen with all the structure maps `R_λ → R` of the colimit
cocone local. This is a genuine strengthening — it does not follow from the six
conditions, see the implementation notes — and it is what makes the system a system of
local rings rather than merely a system of rings with local `R_λ → S_λ`: locality of the
structure maps gives locality of each transition map `R_λ → R_μ`, since for `a ∈ R_λ`
with `a` mapping to a unit of `R_μ` the image of `a` in `R` is a unit; and it identifies
`𝔪_λ` with the contraction of `𝔪_R` along `R_λ → R`, whence `R/𝔪_R` is the colimit of
the residue fields `R_λ/𝔪_λ`, `S/𝔪_R S` the colimit of the `S_λ/𝔪_λ S_λ`, and
`M/𝔪_R M` the colimit of the `M_λ/𝔪_λ M_λ`.

The proof of the source runs through 00QV: write `R` as a colimit of local `ℤ`-algebras
essentially of finite type, spread out a presentation `S = (R[x₁,…,xₙ]/(f₁,…,f_m))_𝔮`
over that system, then spread out a presentation `S^{⊕s} → S^{⊕t} → M → 0` by lifting
its `t × s` matrix at some index `λ₂` and taking `M_λ`, for `λ ≥ λ₂`, to be the
cokernel of the lifted matrix. Locality of the structure maps comes from 00QU, where
`R_λ` is the localization of a subring `R'_λ ⊆ R` at the prime `R'_λ ∩ 𝔪_R`, so that
`𝔪_λ` is by construction the contraction of `𝔪_R`.

## Faithfulness

* Every hypothesis is used: locality of `R`, of `S` and of `algebraMap R S` is what
  makes the `R_λ`, `S_λ` local and the `φ_λ` local; essential finite presentation of
  `algebraMap R S` is what makes (3) and (5) achievable; finite presentation of `M`
  over `S` is what makes (4) and (6) achievable.
* The scalars are the source's: `M_λ` is a module over `S_λ`, not over `R_λ`; (5) is a
  base change along `R_λ → R_μ` and (6) a base change along `S_λ → S_μ`.
* The canonical maps are pinned, not merely asserted to exist: the colimit
  identifications are pinned by the condition intertwining the legs of the two ring
  cocones with `φ_λ` and `algebraMap R S`, and by the semilinearity of the legs of the
  module cocone over the legs of the `S`-cocone, which determines the `S`-action on the
  colimit; (5) pins the map out of `S_λ ⊗_{R_λ} R_μ` as `pushout.desc (B.map h)
  (φ.app j)`; (6) pins the map into `M_μ` as the transition map `N.map h`.
* The source's phrase "a directed system of local homomorphisms of local rings" is read
  as a system in the category of local rings, which is the reading its own construction
  realizes; that is the content of the conjunct on the structure maps `R_λ → R`.
* The instantiation is not degenerate: for `R = S` the localization of `ℤ` at a prime
  `(p)`, `M = S` and `Λ = PUnit`, all six conditions hold, with `q` maximal in (5), and
  the structure maps are the identity, hence local.

## Main results

* `RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module`:
  Tag 00QX.

## Implementation notes

The directed system is a pair of functors `A B : Λ ⥤ CommRingCat` out of a nonempty
directed preorder together with a natural transformation `φ : A ⟶ B`, so the commuting
squares of the system are the naturality of `φ` rather than extra hypotheses. The
modules are a functor `N : Λ ⥤ AddCommGrpCat` with a `B.obj i`-module structure on each
`N.obj i` and the compatibility `N.map h (b • m) = B.map h b • N.map h m`; this is the
shape Mathlib uses for a filtered system of modules over a filtered system of rings
(`CategoryTheory.Limits.IsColimit.module`), and it is what lets (1) be three honest
`IsColimit`s. The colimit of the `M_λ` is `M` as an `S`-module because the legs are
semilinear over the legs of the `S`-cocone, as in
`CategoryTheory.Limits.IsColimit.ι_smul`.

`S_λ ⊗_{R_λ} R_μ` is spelled as the pushout of `φ_λ` along `A.map h` in `CommRingCat`,
which is that tensor product; this keeps the map to `S_μ` canonical (`pushout.desc`)
and avoids transporting three algebra structures and two scalar towers through the
statement. Condition (6) is `IsBaseChange`, the abstract form of
"`M_λ ⊗_{S_λ} S_μ → M_μ` is an isomorphism".

Locality of the structure maps `ρ_λ : R_λ → R` is asserted rather than left to be
derived, because it is not a consequence of conditions (1)–(6). Take `Λ = {0 ≤ 1}`,
`R_0 = S_0 = ℤ_{(p)}` and `R_1 = S_1 = ℚ` with `φ` the identity and `R_0 → R_1` the
localization map, `M_λ = S_λ`, and `R = S = M = ℚ` with the evident structure maps: all
three cocones are colimits, every ring in sight is local, each `φ_λ` is the identity and
so is local and essentially of finite type, `ℤ_{(p)}` and `ℚ` are essentially of finite
type over `ℤ`, condition (5) holds because `ℤ_{(p)} ⊗_{ℤ_{(p)}} ℚ = ℚ` and
`ℚ ⊗_ℚ ℚ = ℚ` are their own localizations at `(0)`, and condition (6) holds; yet neither
the transition map `ℤ_{(p)} → ℚ` nor the structure map `ℤ_{(p)} → ℚ` is local.

Only the `R`-side conjunct is asserted, and it is asserted for the structure maps rather
than for the transition maps, which is the stronger of the two: locality of `ρ_λ` gives
locality of `A.map h` by naturality of `ρ`, and it gives besides that each `𝔪_λ` is the
contraction of `𝔪_R`. Locality of the structure maps `S_λ → S` is not asserted here: it
is not implied by the `R`-side conjunct together with locality of `algebraMap R S` and of
the `φ_λ`. It does hold for the system the construction produces:
`exists_ringSystem_of_essentiallyOfFinitePresentation` asserts it, 00QV's `descent_core`
supplying locality of the transition maps `S_λ → S_μ` and `isLocalHom_sysCocone_app`
turning that into locality of the legs.

Essential finite presentation of a ring map is not in Mathlib; hypothesis (1) uses the
project's `RingHom.EssentiallyOfFinitePresentation`, after Definition 00QM (2).
Conditions (2) and (3) use Mathlib's `Algebra.EssFiniteType` and
`RingHom.EssFiniteType`, whose definition — a localization of a finitely generated
subalgebra — is Definition 00QM (1).

## References

* [Stacks Project, Tag 00QX](https://stacks.math.columbia.edu/tag/00QX)
-/



open CategoryTheory Limits in
/-- **Stacks 00QX.** Let `R → S` be a local homomorphism of local rings which is
essentially of finite presentation and let `M` be a finitely presented `S`-module. Then
there are a nonempty directed set `Λ`, a system `φ : A ⟶ B` of local homomorphisms
`A.obj i → B.obj i` of local rings, and `B.obj i`-modules `N.obj i`, such that (1) the
colimits of `A`, `B` and `N` are `R`, `S` and `M`, compatibly with `algebraMap R S` and
with the `S`-action on `M`; (2) each `A.obj i` is essentially of finite type over `ℤ`;
(3) each `A.obj i → B.obj i` is essentially of finite type; (4) each `N.obj i` is a
finite `B.obj i`-module; (5) for `i ≤ j` the ring `B.obj j` is a localization of
`B.obj i ⊗_{A.obj i} A.obj j` at a prime ideal; (6) for `i ≤ j` the transition map
`N.obj i → N.obj j` exhibits `N.obj j` as the base change of `N.obj i` along
`B.obj i → B.obj j`. Moreover each structure map `A.obj i → R` of the colimit cocone is
a local homomorphism, so that each transition map `A.obj i → A.obj j` is local too and
each `𝔪_{A.obj i}` is the contraction of the maximal ideal of `R`. -/
@[stacks 00QX "The system is a pair of functors `A B : Λ ⥤ CommRingCat` with a natural
transformation `φ : A ⟶ B`, and a functor `N : Λ ⥤ AddCommGrpCat` with `B.obj i`-module
structures compatible with the transition maps; `S_λ ⊗_{R_λ} R_μ` is the pushout in
`CommRingCat` and (6) is `IsBaseChange`. Hypothesis (1) is
`RingHom.EssentiallyOfFinitePresentation` (Definition 00QM (2)), Mathlib having no such
predicate; (2) and (3) are Mathlib's `EssFiniteType` (Definition 00QM (1)). The
conclusion also asserts that each structure map `ρ_λ : A.obj i → R` is local, which is
the source's \"system of local homomorphisms of local rings\" read as a system in the
category of local rings; it is realized by the construction of 00QU and is not implied
by (1)–(6). See the module docstring."]
public theorem RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module
    {R S M : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (A B : Λ ⥤ CommRingCat.{u}) (φ : A ⟶ B) (N : Λ ⥤ AddCommGrpCat.{u})
      (_ : ∀ i, Module (B.obj i) (N.obj i))
      (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (b : B.obj i) (m : N.obj i),
        N.map h (b • m) = B.map h b • N.map h m)
      (ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (σ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (ν : N ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
      (_ : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
      (_ : IsColimit (Cocone.mk (CommRingCat.of S) σ))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)),
      (∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom (algebraMap R S)) ∧
      (∀ (i : Λ) (b : B.obj i) (m : N.obj i),
        (ν.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M) (σ.app i b) (ν.app i m)) ∧
      (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (B.obj i)) ∧
      (∀ i, IsLocalHom (φ.app i).hom) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧
      (∀ i, Algebra.EssFiniteType ℤ (A.obj i)) ∧
      (∀ i, (φ.app i).hom.EssFiniteType) ∧
      (∀ i, Module.Finite (B.obj i) (N.obj i)) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI := (pushout.desc (B.map h) (φ.app j) (φ.naturality h).symm).hom.toAlgebra
        ∃ (q : Ideal ↑(pushout (φ.app i) (A.map h))) (_ : q.IsPrime),
          IsLocalization q.primeCompl ↑(B.obj j)) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map h).hom.toAlgebra
        letI : Module ↑(B.obj i) ↑(N.obj j) := Module.compHom _ (B.map h).hom
        letI : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(N.obj j) :=
          .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑(B.obj j)
          (⟨(N.map h).hom.toAddHom, hsmul h⟩ :
            ↑(N.obj i) →ₗ[↑(B.obj i)] ↑(N.obj j))) :=
  Stacks.SpreadingOut.LocalModuleSystem.solution hS

end
