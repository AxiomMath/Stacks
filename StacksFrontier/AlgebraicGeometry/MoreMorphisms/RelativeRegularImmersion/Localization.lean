module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.UnitMultiples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Flat.Basic

/-!
# Fibre data of a regular immersion, in the concrete localization

Let `A → B` be a ring map, `q` a prime of `B` and `O` a localization of `B` at `q`. A finite family
of `O` in the extension of an ideal `I` of `B` is, up to units, the image of a family in `I`. This
file transfers to `Localization.AtPrime q` the regularity of such a family modulo the fibre, the
inclusion saying that it generates the extended ideal modulo the fibre, and the flatness of the
quotient by the extended ideal.

## Main results

* `Stacks.AlgebraicGeometry.isRegular_map_algebraMap_iff`: regularity of a sequence does not
  depend on which of two rings acting on the module the sequence is read in.
* `Stacks.AlgebraicGeometry.exists_mem_isRegular_fibre_atPrime`: the fibre data, transported from
  an abstract localization at a prime to `Localization.AtPrime`.
* `Stacks.AlgebraicGeometry.flat_quotient_map_atPrime_of_abstract`: flatness of the quotient of
  an abstract localization by an extended ideal, transported to `Localization.AtPrime`.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
-/

@[expose] public noncomputable section

open RingTheory.Sequence

namespace Stacks.AlgebraicGeometry

/-- **Regularity of a sequence is unchanged by pushing it into a larger acting ring.**  If `T → S`
and both act on `M` compatibly, the image in `S` of a sequence `l` of `T` is `M`-regular if and
only if `l` is. -/
theorem isRegular_map_algebraMap_iff {T : Type*} (S : Type*) {M : Type*} [CommRing T]
    [CommRing S] [Algebra T S] [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M]
    (l : List T) : IsRegular M (l.map (algebraMap T S)) ↔ IsRegular M l :=
  (AddEquiv.refl M).isRegular_congr <| List.forall₂_map_left_iff.mpr <|
    List.forall₂_same.mpr fun r _ => algebraMap_smul S r

/-- **Lifting a family in the extended ideal of a localization to the ideal itself.**  Each
member becomes the image of a member of the ideal after multiplication by a unit. -/
private lemma exists_unit_mul_algebraMap_of_mem_map {B O : Type*} [CommRing B] [CommRing O]
    [Algebra B O] (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime O q] {r : ℕ} (I : Ideal B)
    (d : Fin r → O) (hd : ∀ i, d i ∈ I.map (algebraMap B O)) :
    ∃ (c : Fin r → B) (u : Fin r → Oˣ), (∀ i, c i ∈ I) ∧
      ∀ i, algebraMap B O (c i) = (u i : O) * d i := by
  have key : ∀ i : Fin r, ∃ b : B, b ∈ I ∧ ∃ s : B, s ∈ q.primeCompl ∧
      algebraMap B O b = algebraMap B O s * d i := by
    intro i
    obtain ⟨⟨⟨b, hb⟩, ⟨s, hs⟩⟩, hbs⟩ :=
      (IsLocalization.mem_map_algebraMap_iff q.primeCompl O).mp (hd i)
    exact ⟨b, hb, s, hs, by rw [← hbs]; ring⟩
  choose c hc s hs hcs using key
  refine ⟨c, fun i => (IsLocalization.map_units O (⟨s i, hs i⟩ : q.primeCompl)).unit, hc,
    fun i => ?_⟩
  exact hcs i

section Transport

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (q : Ideal B) [q.IsPrime]

/-- Extending an ideal of a ring below `B` (possibly `B` itself) to one localization and comparing
with another localization extends it to the other. -/
private lemma map_algEquiv_map_algebraMap (M N : Type*) [CommRing M] [CommRing N]
    [Algebra B M] [Algebra B N] [Algebra A M] [Algebra A N] [IsScalarTower A B M]
    [IsScalarTower A B N] [IsLocalization q.primeCompl M] [IsLocalization q.primeCompl N]
    (J : Ideal A) :
    Ideal.map (IsLocalization.algEquiv q.primeCompl M N).toRingEquiv.toRingHom
        (J.map (algebraMap A M)) = J.map (algebraMap A N) := by
  rw [Ideal.map_map]
  refine congrArg (fun φ : A →+* N => Ideal.map φ J) (RingHom.ext fun z => ?_)
  change (IsLocalization.algEquiv q.primeCompl M N) (algebraMap A M z) = algebraMap A N z
  rw [IsScalarTower.algebraMap_apply A B M, IsScalarTower.algebraMap_apply A B N]
  exact (IsLocalization.algEquiv q.primeCompl M N).commutes _

variable {O : Type*} [CommRing O] [Algebra B O] [Algebra A O] [IsScalarTower A B O]
  [IsLocalization.AtPrime O q]

/-- **Fibre data, transported to the concrete localization.**  Let `A → B` be a ring
map, let `q` be a prime of `B` and let `O` be an abstract localization of `B` at `q`.  A family in
`O` lying in the extension of an ideal `I` of `B`, regular modulo an ideal `P` of `O` cutting out
the fibre and generating `I O` modulo `P`, gives rise to a family in `I` with the same two
properties read in `Localization.AtPrime q`, generating in `O` the same ideal as the given
family, and still regular modulo `P`. -/
theorem exists_mem_isRegular_fibre_atPrime {r : ℕ} (I : Ideal B) (d : Fin r → O) (P : Ideal O)
    (hP : P = (q.comap (algebraMap A B)).map (algebraMap A O))
    (hd : ∀ i, d i ∈ I.map (algebraMap B O))
    (hreg : IsRegular (O ⧸ P) (List.ofFn fun i => Ideal.Quotient.mk P (d i)))
    (hle : I.map (algebraMap B O) ≤ Ideal.span (Set.range d) ⊔ P) :
    ∃ c : Fin r → B, (∀ i, c i ∈ I) ∧
      IsRegular (Localization.AtPrime q ⧸ (q.comap (algebraMap A B)).map
          (algebraMap A (Localization.AtPrime q)))
        (List.ofFn fun i => algebraMap B (Localization.AtPrime q) (c i)) ∧
      I.map (algebraMap B (Localization.AtPrime q)) ≤
        (Ideal.span (Set.range c)).map (algebraMap B (Localization.AtPrime q)) ⊔
          (q.comap (algebraMap A B)).map (algebraMap A (Localization.AtPrime q)) ∧
      Ideal.span (Set.range d) = (Ideal.span (Set.range c)).map (algebraMap B O) ∧
      IsRegular (O ⧸ P) (List.ofFn fun i => algebraMap B (O ⧸ P) (c i)) := by
  subst hP
  set p : Ideal A := q.comap (algebraMap A B)
  set L : Type _ := Localization.AtPrime q
  set P : Ideal O := p.map (algebraMap A O)
  set K : Ideal L := p.map (algebraMap A L)
  obtain ⟨c, u, hc, hcu⟩ := exists_unit_mul_algebraMap_of_mem_map q I d hd
  have hspan : Ideal.span (Set.range d)
      = (Ideal.span (Set.range c)).map (algebraMap B O) := by
    refine (span_range_eq_of_unit_mul d (fun i => algebraMap B O (c i)) u hcu).trans ?_
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hregO : IsRegular (O ⧸ P) (List.ofFn fun i => algebraMap B (O ⧸ P) (c i)) := by
    refine isRegular_of_forall₂_unit_mul (forall₂_unit_mul_ofFn
      (fun i => Ideal.Quotient.mk P (d i)) (fun i => algebraMap B (O ⧸ P) (c i))
      (fun i => (Units.map (Ideal.Quotient.mk P).toMonoidHom) (u i)) fun i => ?_) hreg
    change Ideal.Quotient.mk P (algebraMap B O (c i)) = _
    rw [hcu i]
    rfl
  have hKP : P = Ideal.map (IsLocalization.algEquiv q.primeCompl L O).toRingEquiv.toRingHom K :=
    (map_algEquiv_map_algebraMap q L O p).symm
  refine ⟨c, hc, ?_, ?_, hspan, hregO⟩
  · have h₁ : IsRegular (O ⧸ P) (List.ofFn c) := by
      refine (isRegular_map_algebraMap_iff (O ⧸ P) (List.ofFn c)).mp ?_
      rwa [List.map_ofFn]
    have h₂ : IsRegular (L ⧸ K) (List.ofFn c) :=
      (LinearEquiv.isRegular_congr (Ideal.quotientEquivAlg K P
        (IsLocalization.algEquiv q.primeCompl L O) hKP).toLinearEquiv (List.ofFn c)).mpr h₁
    have h₃ := (isRegular_map_algebraMap_iff (M := L ⧸ K) L (List.ofFn c)).mpr h₂
    rwa [List.map_ofFn] at h₃
  · have h₄ := Ideal.map_mono
      (f := (IsLocalization.algEquiv q.primeCompl O L).toRingEquiv.toRingHom) (hspan ▸ hle)
    rwa [map_algEquiv_map_algebraMap q O L I, Ideal.map_sup,
      map_algEquiv_map_algebraMap q O L (Ideal.span (Set.range c)),
      map_algEquiv_map_algebraMap q O L p] at h₄

/-- **Flatness of the quotient by an extended ideal, transported to the concrete localization.**
If `O` is a localization of `B` at `q` and `O ⧸ I O` is flat over `A`, then so is
`Localization.AtPrime q ⧸ I (Localization.AtPrime q)`. -/
theorem flat_quotient_map_atPrime_of_abstract (I : Ideal B)
    (hflat : Module.Flat A (O ⧸ I.map (algebraMap B O))) :
    Module.Flat A (Localization.AtPrime q ⧸
      I.map (algebraMap B (Localization.AtPrime q))) := by
  exact Module.Flat.of_linearEquiv (Ideal.quotientEquivAlg
    (I.map (algebraMap B (Localization.AtPrime q))) (I.map (algebraMap B O))
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) O).restrictScalars A)
    (map_algEquiv_map_algebraMap q (Localization.AtPrime q) O I).symm).toLinearEquiv

end Transport

end Stacks.AlgebraicGeometry

end
