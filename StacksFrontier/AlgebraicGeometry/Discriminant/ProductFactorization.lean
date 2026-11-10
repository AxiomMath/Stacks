module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement

/-!
# Finite-open factorizations of a product of algebras

The spectrum of a product of two rings is the disjoint union of the two spectra, and this file
transfers finite-open factorizations across that decomposition. Two finite-open factorizations
`A → B' → B` and `A → C' → C` combine into the factorization `A → B' × C' → B × C`, and
conversely a finite-open factorization of `B × C` restricts to one of each factor, keeping the
same intermediate algebra and composing with a projection.

## Main definitions

* `Stacks.Discriminant.productFiniteOpenFactorization` is the product of two finite-open
  factorizations.
* `Stacks.Discriminant.firstFactorization` and `Stacks.Discriminant.secondFactorization`
  restrict a finite-open factorization of a product to its two factors.

## Main results

* `Stacks.Discriminant.prod_comap_isOpenEmbedding`: a product of ring maps whose spectra maps
  are open embeddings again induces an open embedding.
* `Stacks.Discriminant.prod_awayMap_bijective`: the away localizations of a product map at a
  pair are bijective when both components are.

## Implementation notes

The spectrum of `B × C` is identified with the sum of the spectra by
`PrimeSpectrum.primeSpectrumProd`, and the computation of a comap is reduced to the two
projections. Restricting a factorization of a product uses that the projection kills a nilpotent
component: the element inverted in the away localization has nilpotent other coordinate, so the
away localization along the projection is bijective.

## References

* [Stacks Project, Tag 0BT5](https://stacks.math.columbia.edu/tag/0BT5)
-/

@[expose] public section

universe u v w x y z

namespace Stacks.Discriminant

open Topology

/-- The spectrum of a product of ring maps, read through the decomposition of the spectrum of a
product ring as a sum, is the sum of the two spectra maps. -/
lemma prod_comap_components
    {R : Type u} {S : Type v} {B : Type w} {C : Type x}
    [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    (f : R →+* B) (g : S →+* C) (q : PrimeSpectrum (B × C)) :
    PrimeSpectrum.primeSpectrumProd R S
      (PrimeSpectrum.comap
        (RingHom.prod (f.comp (RingHom.fst R S)) (g.comp (RingHom.snd R S))) q) =
      Sum.map (PrimeSpectrum.comap f) (PrimeSpectrum.comap g)
        (PrimeSpectrum.primeSpectrumProd B C q) := by
  obtain ⟨x, rfl⟩ := (PrimeSpectrum.primeSpectrumProd B C).symm.surjective q
  rcases x with p | p
  · rw [Equiv.apply_symm_apply, Sum.map_inl, PrimeSpectrum.primeSpectrumProd_symm_inl,
      ← PrimeSpectrum.comap_comp_apply,
      show (RingHom.fst B C).comp
        (RingHom.prod (f.comp (RingHom.fst R S)) (g.comp (RingHom.snd R S))) =
        f.comp (RingHom.fst R S) from rfl,
      PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.primeSpectrumProd_symm_inl,
      Equiv.apply_symm_apply]
  · rw [Equiv.apply_symm_apply, Sum.map_inr, PrimeSpectrum.primeSpectrumProd_symm_inr,
      ← PrimeSpectrum.comap_comp_apply,
      show (RingHom.snd B C).comp
        (RingHom.prod (f.comp (RingHom.fst R S)) (g.comp (RingHom.snd R S))) =
        g.comp (RingHom.snd R S) from rfl,
      PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.primeSpectrumProd_symm_inr,
      Equiv.apply_symm_apply]

/-- A product of two ring maps whose maps of spectra are open embeddings again induces an open
embedding on spectra. -/
lemma prod_comap_isOpenEmbedding
    {R : Type u} {S : Type v} {B : Type w} {C : Type x}
    [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    (f : R →+* B) (g : S →+* C)
    (hf : Topology.IsOpenEmbedding (PrimeSpectrum.comap f))
    (hg : Topology.IsOpenEmbedding (PrimeSpectrum.comap g)) :
    Topology.IsOpenEmbedding (PrimeSpectrum.comap
      (RingHom.prod (f.comp (RingHom.fst R S)) (g.comp (RingHom.snd R S)))) := by
  let eR := PrimeSpectrum.primeSpectrumProd (R := R) (S := S)
  let eB := PrimeSpectrum.primeSpectrumProd (R := B) (S := C)
  let hR := PrimeSpectrum.primeSpectrumProdHomeo (R := R) (S := S)
  let hB := PrimeSpectrum.primeSpectrumProdHomeo (R := B) (S := C)
  let f' : PrimeSpectrum B → PrimeSpectrum R := PrimeSpectrum.comap f
  let g' : PrimeSpectrum C → PrimeSpectrum S := PrimeSpectrum.comap g
  let h : PrimeSpectrum B ⊕ PrimeSpectrum C → PrimeSpectrum R ⊕ PrimeSpectrum S :=
    Sum.map f' g'
  have hh : Topology.IsOpenEmbedding h := by
    rw [Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap]
    refine ⟨hf.continuous.sumMap hg.continuous, ?_, hf.isOpenMap.sumMap hg.isOpenMap⟩
    intro p q hpq
    cases p with
    | inl p => cases q with
      | inl q => exact congrArg Sum.inl (hf.injective (by simpa [h, f', g'] using hpq))
      | inr q => cases hpq
    | inr p => cases q with
      | inl q => cases hpq
      | inr q => exact congrArg Sum.inr (hg.injective (by simpa [h, f', g'] using hpq))
  have hmap : PrimeSpectrum.comap
      (RingHom.prod (f.comp (RingHom.fst R S)) (g.comp (RingHom.snd R S))) =
      fun q => eR.symm (h (eB q)) := by
    funext q
    apply eR.injective
    rw [eR.apply_symm_apply]
    change PrimeSpectrum.primeSpectrumProd R S
        (PrimeSpectrum.comap
          (RingHom.prod (f.comp (RingHom.fst R S)) (g.comp (RingHom.snd R S))) q) =
      Sum.map (PrimeSpectrum.comap f) (PrimeSpectrum.comap g)
        (PrimeSpectrum.primeSpectrumProd B C q)
    exact prod_comap_components f g q
  rw [hmap]
  exact hR.symm.isOpenEmbedding.comp (hh.comp hB.isOpenEmbedding)

/-- If `f b = f r ^ m * a` and `m ≤ n`, then `f (b * r ^ (n - m)) = f r ^ n * a`. -/
private theorem map_mul_pow_sub_eq {R : Type u} {B : Type w} [CommRing R] [CommRing B]
    (f : R →+* B) {r b : R} {a : B} {m n : ℕ} (h : m ≤ n) (hb : f b = f r ^ m * a) :
    f (b * r ^ (n - m)) = f r ^ n * a := by
  rw [map_mul, map_pow, hb, mul_right_comm, ← pow_add, Nat.add_sub_cancel' h]

/-- The away localization of a product of ring maps at a pair of elements is bijective when
both component away localizations are. -/
lemma prod_awayMap_bijective
    {R : Type u} {S : Type v} {B : Type w} {C : Type x}
    [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    (f : R →+* B) (g : S →+* C)
    (hf : ∀ r : R, (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
      Set.range (PrimeSpectrum.comap f) → Function.Bijective (Localization.awayMap f r))
    (hg : ∀ s : S, (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S)) ⊆
      Set.range (PrimeSpectrum.comap g) → Function.Bijective (Localization.awayMap g s))
    (r : R) (s : S)
    (hr : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
      Set.range (PrimeSpectrum.comap f))
    (hs : (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S)) ⊆
      Set.range (PrimeSpectrum.comap g)) :
    Function.Bijective
      (Localization.awayMap
        (RingHom.prod (f.comp (RingHom.fst R S)) (g.comp (RingHom.snd R S))) (r, s)) := by
  let F := RingHom.prod (f.comp (RingHom.fst R S)) (g.comp (RingHom.snd R S))
  constructor
  · rw [Localization.awayMap_injective_iff]
    intro a ha
    have hfa : f a.1 = 0 := by simpa [F] using congrArg Prod.fst ha
    have hga : g a.2 = 0 := by simpa [F] using congrArg Prod.snd ha
    obtain ⟨n₁, hn₁⟩ := (Localization.awayMap_injective_iff.mp (hf r hr).1) a.1 hfa
    obtain ⟨n₂, hn₂⟩ := (Localization.awayMap_injective_iff.mp (hg s hs).1) a.2 hga
    refine ⟨max n₁ n₂, Prod.ext ?_ ?_⟩
    · exact pow_mul_eq_zero_of_le (Nat.le_max_left n₁ n₂) hn₁
    · exact pow_mul_eq_zero_of_le (Nat.le_max_right n₁ n₂) hn₂
  · rw [Localization.awayMap_surjective_iff]
    intro a
    obtain ⟨b₁, m₁, hb₁⟩ := (Localization.awayMap_surjective_iff.mp (hf r hr).2) a.1
    obtain ⟨b₂, m₂, hb₂⟩ := (Localization.awayMap_surjective_iff.mp (hg s hs).2) a.2
    exact ⟨(b₁ * r ^ (max m₁ m₂ - m₁), b₂ * s ^ (max m₁ m₂ - m₂)), max m₁ m₂,
      Prod.ext (map_mul_pow_sub_eq f (Nat.le_max_left m₁ m₂) hb₁)
        (map_mul_pow_sub_eq g (Nat.le_max_right m₁ m₂) hb₂)⟩

/-- The product of two finite-open factorizations is a finite-open factorization of the product
algebra, with the product of the intermediate algebras as its intermediate algebra. -/
noncomputable def productFiniteOpenFactorization
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C) :
    FiniteOpenFactorization.{u, max v w, max y z} A (B × C) := by
  let : Algebra A FB.middle := FB.algebraMiddle
  let : Algebra A FC.middle := FC.algebraMiddle
  let : Algebra FB.middle B := FB.algebraTarget
  let : Algebra FC.middle C := FC.algebraTarget
  let : IsScalarTower A FB.middle B := FB.scalarTower
  let : IsScalarTower A FC.middle C := FC.scalarTower
  let : Module (B × C) (dualizingModule FB) :=
    Module.compHom _ (RingHom.fst B C)
  let : Module (B × C) (dualizingModule FC) :=
    Module.compHom _ (RingHom.snd B C)
  let f : (FB.middle × FC.middle) →ₐ[A] (B × C) :=
    AlgHom.prod
      ((IsScalarTower.toAlgHom A FB.middle B).comp (AlgHom.fst A FB.middle FC.middle))
      ((IsScalarTower.toAlgHom A FC.middle C).comp (AlgHom.snd A FB.middle FC.middle))
  have hRing : f.toRingHom = RingHom.prod
      ((algebraMap FB.middle B).comp (RingHom.fst FB.middle FC.middle))
      ((algebraMap FC.middle C).comp (RingHom.snd FB.middle FC.middle)) := by
    ext ⟨b, c⟩ <;> rfl
  have hscalar : algebraMap A (B × C) =
      f.toRingHom.comp (algebraMap A (FB.middle × FC.middle)) := by
    apply RingHom.ext
    intro a
    exact (f.commutes' a).symm
  let : Algebra (FB.middle × FC.middle) (B × C) := f.toRingHom.toAlgebra
  let : IsScalarTower A (FB.middle × FC.middle) (B × C) :=
    IsScalarTower.of_algebraMap_eq' hscalar
  refine ⟨FB.middle × FC.middle, inferInstance, inferInstance, f.toRingHom.toAlgebra,
    inferInstance, inferInstance, ?_, ?_⟩
  · exact prod_comap_isOpenEmbedding
      (algebraMap FB.middle B) (algebraMap FC.middle C)
      FB.isOpenEmbedding_comap FC.isOpenEmbedding_comap
  · intro g hg
    let g₁ := g.1
    let g₂ := g.2
    have h₁ : (PrimeSpectrum.basicOpen g₁ : Set (PrimeSpectrum FB.middle)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap FB.middle B)) := by
      intro p hp
      have hpH : PrimeSpectrum.comap (RingHom.fst FB.middle FC.middle) p ∈
          PrimeSpectrum.basicOpen (g₁, g₂) := by
        change (g₁, g₂) ∉ (PrimeSpectrum.comap (RingHom.fst FB.middle FC.middle) p).asIdeal
        simpa [PrimeSpectrum.comap_asIdeal] using hp
      obtain ⟨q, hq⟩ := hg hpH
      have hqH : PrimeSpectrum.primeSpectrumProd FB.middle FC.middle
          (PrimeSpectrum.comap (RingHom.fst FB.middle FC.middle) p) = Sum.inl p := by
        rw [← PrimeSpectrum.primeSpectrumProd_symm_inl]
        exact Equiv.apply_symm_apply _ _
      have hsum : Sum.map (PrimeSpectrum.comap (algebraMap FB.middle B))
          (PrimeSpectrum.comap (algebraMap FC.middle C)) (PrimeSpectrum.primeSpectrumProd B C q) =
          Sum.inl p := by
        calc
          _ = PrimeSpectrum.primeSpectrumProd FB.middle FC.middle
              (PrimeSpectrum.comap f.toRingHom q) := by
                rw [hRing]
                exact (prod_comap_components
                  (algebraMap FB.middle B) (algebraMap FC.middle C) q).symm
          _ = PrimeSpectrum.primeSpectrumProd FB.middle FC.middle
              (PrimeSpectrum.comap (RingHom.fst FB.middle FC.middle) p) :=
            congrArg (PrimeSpectrum.primeSpectrumProd FB.middle FC.middle) hq
          _ = Sum.inl p := hqH
      cases hqp : PrimeSpectrum.primeSpectrumProd B C q with
      | inl qB =>
          refine ⟨qB, ?_⟩
          have h := hsum
          rw [hqp] at h
          exact Sum.inl.inj h
      | inr qC =>
          have h := hsum
          rw [hqp] at h
          cases h
    have h₂ : (PrimeSpectrum.basicOpen g₂ : Set (PrimeSpectrum FC.middle)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap FC.middle C)) := by
      intro p hp
      have hpH : PrimeSpectrum.comap (RingHom.snd FB.middle FC.middle) p ∈
          PrimeSpectrum.basicOpen (g₁, g₂) := by
        change (g₁, g₂) ∉ (PrimeSpectrum.comap (RingHom.snd FB.middle FC.middle) p).asIdeal
        simpa [PrimeSpectrum.comap_asIdeal] using hp
      obtain ⟨q, hq⟩ := hg hpH
      have hqH : PrimeSpectrum.primeSpectrumProd FB.middle FC.middle
          (PrimeSpectrum.comap (RingHom.snd FB.middle FC.middle) p) = Sum.inr p := by
        rw [← PrimeSpectrum.primeSpectrumProd_symm_inr]
        exact Equiv.apply_symm_apply _ _
      have hsum : Sum.map (PrimeSpectrum.comap (algebraMap FB.middle B))
          (PrimeSpectrum.comap (algebraMap FC.middle C)) (PrimeSpectrum.primeSpectrumProd B C q) =
          Sum.inr p := by
        calc
          _ = PrimeSpectrum.primeSpectrumProd FB.middle FC.middle
              (PrimeSpectrum.comap f.toRingHom q) := by
                rw [hRing]
                exact (prod_comap_components
                  (algebraMap FB.middle B) (algebraMap FC.middle C) q).symm
          _ = PrimeSpectrum.primeSpectrumProd FB.middle FC.middle
              (PrimeSpectrum.comap (RingHom.snd FB.middle FC.middle) p) :=
            congrArg (PrimeSpectrum.primeSpectrumProd FB.middle FC.middle) hq
          _ = Sum.inr p := hqH
      cases hqp : PrimeSpectrum.primeSpectrumProd B C q with
      | inr qC =>
          refine ⟨qC, ?_⟩
          have h := hsum
          rw [hqp] at h
          exact Sum.inr.inj h
      | inl qB =>
          have h := hsum
          rw [hqp] at h
          cases h
    have hbij := prod_awayMap_bijective
      (algebraMap FB.middle B) (algebraMap FC.middle C)
      (fun r hr => FB.awayMap_bijective r hr)
      (fun s hs => FC.awayMap_bijective s hs) g₁ g₂ h₁ h₂
    change Function.Bijective (Localization.awayMap f.toRingHom g)
    rw [hRing]
    simpa [g₁, g₂] using hbij

/-- Restrict a finite-open factorization of a product to its first factor. -/
noncomputable def firstFactorization
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C)) :
    FiniteOpenFactorization.{u, v, x} A B := by
  let : Algebra F.middle B :=
    ((RingHom.fst B C).comp (algebraMap F.middle (B × C))).toAlgebra
  let : IsScalarTower A F.middle (B × C) := F.scalarTower
  let : IsScalarTower A F.middle B := .of_algebraMap_eq fun a => by
    simpa [RingHom.algebraMap_toAlgebra] using
      congrArg (RingHom.fst B C) (IsScalarTower.algebraMap_apply A F.middle (B × C) a)
  refine ⟨F.middle, F.commRingMiddle, F.algebraMiddle, inferInstance, inferInstance,
    F.finite_middle, ?_, ?_⟩
  · have hfst : Topology.IsOpenEmbedding (PrimeSpectrum.comap (RingHom.fst B C)) := by
      rw [show PrimeSpectrum.comap (RingHom.fst B C) =
          (PrimeSpectrum.primeSpectrumProdHomeo (R := B) (S := C)).symm ∘ Sum.inl by
        funext p
        exact (PrimeSpectrum.primeSpectrumProd_symm_inl p).symm]
      exact (PrimeSpectrum.primeSpectrumProdHomeo (R := B) (S := C)).symm.isOpenEmbedding.comp
        Topology.IsOpenEmbedding.inl
    have hcomp :
        PrimeSpectrum.comap (algebraMap F.middle B) =
          PrimeSpectrum.comap (algebraMap F.middle (B × C)) ∘
            PrimeSpectrum.comap (RingHom.fst B C) := by
      have hmap : algebraMap F.middle B =
          (RingHom.fst B C).comp (algebraMap F.middle (B × C)) := by
        ext a
        rfl
      rw [hmap, PrimeSpectrum.comap_comp]
    rw [hcomp]
    exact F.isOpenEmbedding_comap.comp hfst
  · intro g hg
    let f : F.middle →+* (B × C) := algebraMap F.middle (B × C)
    let d : B × C := f g
    have hsource : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum F.middle)) ⊆
        Set.range (PrimeSpectrum.comap f) := by
      intro p hp
      obtain ⟨b, hb⟩ := hg hp
      exact ⟨PrimeSpectrum.comap (RingHom.fst B C) b, by
        simpa [f, PrimeSpectrum.comap_comp, RingHom.algebraMap_toAlgebra] using hb⟩
    have hnil : IsNilpotent d.2 := by
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      apply TopologicalSpace.Opens.ext
      ext q
      constructor
      · intro hq
        let qD := PrimeSpectrum.comap (RingHom.snd B C) q
        let qM := PrimeSpectrum.comap f qD
        have hqM : qM ∈ PrimeSpectrum.basicOpen g := by
          simpa [qM, qD, d, f, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
            PrimeSpectrum.mem_basicOpen] using hq
        obtain ⟨b, hb⟩ := hg hqM
        have heq : qD = PrimeSpectrum.comap (RingHom.fst B C) b :=
          F.isOpenEmbedding_comap.injective (by
            simpa [qM, qD, f, PrimeSpectrum.comap_comp,
              RingHom.algebraMap_toAlgebra] using hb.symm)
        have hmem : (1, 0) ∈ qD.asIdeal := by
          change RingHom.snd B C (1, 0) ∈ q.asIdeal
          simp
        have hnot : (1, 0) ∉ (PrimeSpectrum.comap (RingHom.fst B C) b).asIdeal := by
          change RingHom.fst B C (1, 0) ∉ b.asIdeal
          exact fun h => b.2.ne_top ((Ideal.eq_top_iff_one _).mpr h)
        have hnot' : (1, 0) ∉ qD.asIdeal := by simpa [heq] using hnot
        exact hnot' hmem
      · intro hq
        cases hq
    let : Algebra (B × C) B := (RingHom.fst B C).toAlgebra
    have hproj : Function.Bijective (Localization.awayMap (RingHom.fst B C) d) := by
      constructor
      · apply (Localization.awayMap_injective_iff).2
        intro a ha
        obtain ⟨n, hn⟩ := hnil
        refine ⟨n, ?_⟩
        have ha' : a.1 = 0 := ha
        ext <;> simp [ha', hn]
      · apply (Localization.awayMap_surjective_iff).2
        intro b
        exact ⟨(b, 0), 0, by simp⟩
    have hcomp : Localization.awayMap (f := (RingHom.fst B C).comp f) g =
        (Localization.awayMap (RingHom.fst B C) (f g)).comp (Localization.awayMap f g) := by
      apply IsLocalization.map_unique
      intro a
      change Localization.awayMap (RingHom.fst B C) (f g)
          (Localization.awayMap f g (algebraMap F.middle (Localization.Away g) a)) =
        algebraMap B (Localization.Away (RingHom.fst B C (f g))) (f a).1
      rw [show Localization.awayMap f g (algebraMap F.middle (Localization.Away g) a) =
          algebraMap (B × C) (Localization.Away (f g)) (f a) by
        simp [Localization.awayMap, IsLocalization.Away.map]]
      change ((Localization.awayMap (RingHom.fst B C) (f g)).comp
          (algebraMap (B × C) (Localization.Away (f g)))) (f a) =
        ((algebraMap B (Localization.Away (RingHom.fst B C (f g)))).comp
          (RingHom.fst B C)) (f a)
      simp only [Localization.awayMap, IsLocalization.Away.map]
      rw [IsLocalization.map_comp]
    have hF := F.awayMap_bijective g hsource
    have hmap : algebraMap F.middle B = (RingHom.fst B C).comp f := by
      ext a
      rfl
    rw [hmap, hcomp]
    exact hproj.comp hF

/-- Restrict a finite-open factorization of a product to its second factor. -/
noncomputable def secondFactorization
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C)) :
    FiniteOpenFactorization.{u, w, x} A C := by
  let : Algebra A C := inferInstance
  let : Algebra F.middle C :=
    ((RingHom.snd B C).comp (algebraMap F.middle (B × C))).toAlgebra
  let : IsScalarTower A F.middle (B × C) := F.scalarTower
  let : IsScalarTower A F.middle C := .of_algebraMap_eq fun a => by
    simpa [RingHom.algebraMap_toAlgebra] using
      congrArg (RingHom.snd B C) (IsScalarTower.algebraMap_apply A F.middle (B × C) a)
  refine ⟨F.middle, F.commRingMiddle, F.algebraMiddle, inferInstance, inferInstance,
    F.finite_middle, ?_, ?_⟩
  · have hsnd : Topology.IsOpenEmbedding (PrimeSpectrum.comap (RingHom.snd B C)) := by
      rw [show PrimeSpectrum.comap (RingHom.snd B C) =
          (PrimeSpectrum.primeSpectrumProdHomeo (R := B) (S := C)).symm ∘ Sum.inr by
        funext p
        exact (PrimeSpectrum.primeSpectrumProd_symm_inr p).symm]
      exact (PrimeSpectrum.primeSpectrumProdHomeo (R := B) (S := C)).symm.isOpenEmbedding.comp
        Topology.IsOpenEmbedding.inr
    have hcomp :
        PrimeSpectrum.comap (algebraMap F.middle C) =
          PrimeSpectrum.comap (algebraMap F.middle (B × C)) ∘
            PrimeSpectrum.comap (RingHom.snd B C) := by
      have hmap : algebraMap F.middle C =
          (RingHom.snd B C).comp (algebraMap F.middle (B × C)) := by
        ext a
        rfl
      rw [hmap, PrimeSpectrum.comap_comp]
    rw [hcomp]
    exact F.isOpenEmbedding_comap.comp hsnd
  · intro g hg
    let f : F.middle →+* (B × C) := algebraMap F.middle (B × C)
    let d : B × C := f g
    have hsource : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum F.middle)) ⊆
        Set.range (PrimeSpectrum.comap f) := by
      intro p hp
      obtain ⟨c, hc⟩ := hg hp
      exact ⟨PrimeSpectrum.comap (RingHom.snd B C) c, by
        simpa [f, PrimeSpectrum.comap_comp, RingHom.algebraMap_toAlgebra] using hc⟩
    have hnil : IsNilpotent d.1 := by
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      apply TopologicalSpace.Opens.ext
      ext q
      constructor
      · intro hq
        let qD := PrimeSpectrum.comap (RingHom.fst B C) q
        let qM := PrimeSpectrum.comap f qD
        have hqM : qM ∈ PrimeSpectrum.basicOpen g := by
          simpa [qM, qD, d, f, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
            PrimeSpectrum.mem_basicOpen] using hq
        obtain ⟨c, hc⟩ := hg hqM
        have heq : qD = PrimeSpectrum.comap (RingHom.snd B C) c :=
          F.isOpenEmbedding_comap.injective (by
            simpa [qM, qD, f, PrimeSpectrum.comap_comp,
              RingHom.algebraMap_toAlgebra] using hc.symm)
        have hmem : (0, 1) ∈ qD.asIdeal := by
          change RingHom.fst B C (0, 1) ∈ q.asIdeal
          simp
        have hnot : (0, 1) ∉ (PrimeSpectrum.comap (RingHom.snd B C) c).asIdeal := by
          change RingHom.snd B C (0, 1) ∉ c.asIdeal
          exact fun h => c.2.ne_top ((Ideal.eq_top_iff_one _).mpr h)
        have hnot' : (0, 1) ∉ qD.asIdeal := by simpa [heq] using hnot
        exact hnot' hmem
      · intro hq
        cases hq
    let : Algebra (B × C) C := (RingHom.snd B C).toAlgebra
    have hproj : Function.Bijective (Localization.awayMap (RingHom.snd B C) d) := by
      constructor
      · apply (Localization.awayMap_injective_iff).2
        intro a ha
        obtain ⟨n, hn⟩ := hnil
        refine ⟨n, ?_⟩
        have ha' : a.2 = 0 := ha
        ext <;> simp [ha', hn]
      · apply (Localization.awayMap_surjective_iff).2
        intro c
        exact ⟨(0, c), 0, by simp⟩
    have hcomp : Localization.awayMap (f := (RingHom.snd B C).comp f) g =
        (Localization.awayMap (RingHom.snd B C) (f g)).comp (Localization.awayMap f g) := by
      apply IsLocalization.map_unique
      intro a
      change Localization.awayMap (RingHom.snd B C) (f g)
          (Localization.awayMap f g (algebraMap F.middle (Localization.Away g) a)) =
        algebraMap C (Localization.Away (RingHom.snd B C (f g))) (f a).2
      rw [show Localization.awayMap f g (algebraMap F.middle (Localization.Away g) a) =
          algebraMap (B × C) (Localization.Away (f g)) (f a) by
        simp [Localization.awayMap, IsLocalization.Away.map]]
      change ((Localization.awayMap (RingHom.snd B C) (f g)).comp
          (algebraMap (B × C) (Localization.Away (f g)))) (f a) =
        ((algebraMap C (Localization.Away (RingHom.snd B C (f g)))).comp
          (RingHom.snd B C)) (f a)
      simp only [Localization.awayMap, IsLocalization.Away.map]
      rw [IsLocalization.map_comp]
    have hF := F.awayMap_bijective g hsource
    have hmap : algebraMap F.middle C = (RingHom.snd B C).comp f := by
      ext a
      rfl
    rw [hmap, hcomp]
    exact hproj.comp hF

end Stacks.Discriminant
