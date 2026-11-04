module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalIsomorphism
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalIso
public import StacksCore.Tactic.StacksAttribute

/-!
# Permanence of local isomorphisms in an algebra tower

Both halves of the local-isomorphism notion cancel on the left in a tower `A → B → C`: if the
maps `A → B` and `A → C` are local isomorphisms, so is `B → C`, and the same holds for the
property of identifying local rings. Identifying local rings is moreover transitive along the
tower.

## Main results

* `AlgebraicGeometry.ProEtale.isLocalIso_of_left_of_comp`: left cancellation for local
  isomorphisms.
* `AlgebraicGeometry.ProEtale.identifiesLocalRings_of_left_of_comp`: left cancellation for the
  property of identifying local rings.
* `AlgebraicGeometry.ProEtale.identifiesLocalRings_comp`: composition of two maps identifying
  local rings identifies local rings.

The other half of transitivity along a tower, that a composition of local isomorphisms is a local
isomorphism, is Mathlib's `Algebra.IsLocalIso.trans`; it is registered for the Stacks tag at the
end of this file.

## Implementation notes

The compatibility of the three algebra structures is expressed by `IsScalarTower`. The
local-isomorphism statement uses commutative semirings, as in Mathlib's local-isomorphism
predicate; the local-ring statement likewise, since the local-ring characterization is available
in that generality.

Both local-ring statements rest on the same two facts about `Localization.localRingHom`: it
factors through the middle of the tower, and its bijectivity does not depend on which description
of the contracted prime is used. The latter is needed because the contraction in one step and the
contraction through the middle, while equal, are not definitionally equal, so the two
localizations at them are different types.

## References

* [Stacks Project, Tag 096G](https://stacks.math.columbia.edu/tag/096G)
* [Stacks Project, Tag 096H](https://stacks.math.columbia.edu/tag/096H)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

/-- Standard open immersions cancel on the left in an algebra tower. -/
private lemma standardOpenImmersion_of_left_of_comp
    (A B C : Type*) [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.IsStandardOpenImmersion A B] [Algebra.IsStandardOpenImmersion A C] :
    Algebra.IsStandardOpenImmersion B C := by
  obtain ⟨r, hr⟩ := Algebra.IsStandardOpenImmersion.exists_away A B
  obtain ⟨s, hs⟩ := Algebra.IsStandardOpenImmersion.exists_away A C
  have hrC : IsUnit (algebraMap A C r) := by
    simpa [IsScalarTower.algebraMap_apply A B C] using
      IsUnit.map (algebraMap B C) (IsLocalization.Away.algebraMap_isUnit r)
  let : IsLocalization.Away (algebraMap A C r) C :=
    IsLocalization.away_of_isUnit_of_bijective C hrC Function.bijective_id
  exact ⟨algebraMap A B s,
    IsLocalization.Away.commutes (R := A) (S₁ := B) (S₂ := C) (T := C) r s⟩

/-- **Stacks Project, Tag 096H.** If the base-to-middle and base-to-top maps of an algebra
tower are local isomorphisms, then so is the middle-to-top map. -/
@[stacks 096H "local_isomorphism_permanence"]
theorem isLocalIso_of_left_of_comp
    (A B C : Type*) [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.IsLocalIso A B] [Algebra.IsLocalIso A C] :
    Algebra.IsLocalIso B C := by
  refine ⟨fun q hq ↦ ?_⟩
  let qB : Ideal B := q.comap (algebraMap B C)
  have hqB : qB.IsPrime := hq.comap (algebraMap B C)
  let : qB.IsPrime := hqB
  obtain ⟨h, hh, hAB⟩ := Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion
    (R := A) qB
  obtain ⟨g, hg, hAC⟩ := Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion
    (R := A) q
  let Cg := Localization.Away g
  let B' := Localization.Away h
  let hC : C := algebraMap B C h
  let hCg : Cg := algebraMap C Cg hC
  let T := Localization.Away hCg
  let : Algebra C T := (algebraMap Cg T).comp (algebraMap C Cg) |>.toAlgebra
  let : Algebra B Cg := (algebraMap C Cg).comp (algebraMap B C) |>.toAlgebra
  let : Algebra B T := (algebraMap Cg T).comp (algebraMap B Cg) |>.toAlgebra
  let : Algebra A T := (algebraMap Cg T).comp (algebraMap A Cg) |>.toAlgebra
  let : Algebra B' T := localizationAlgebra (.powers h) Cg
  let : SMul B Cg := Algebra.toSMul
  let : SMul A Cg := Algebra.toSMul
  let : SMul B T := Algebra.toSMul
  let : SMul A T := Algebra.toSMul
  let : SMul Cg T := Algebra.toSMul
  let : SMul C T := Algebra.toSMul
  let : SMul B B' := Algebra.toSMul
  let : SMul B' T := (localizationAlgebra (.powers h) Cg).toSMul
  let : IsScalarTower B C Cg := IsScalarTower.of_algebraMap_eq' rfl
  have hCCgT : IsScalarTower C Cg T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A Cg T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B Cg T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A C T := IsScalarTower.to₁₂₄ A C Cg T
  let : IsScalarTower B C T := IsScalarTower.to₁₂₄ B C Cg T
  have hABTmaps : algebraMap A T = (algebraMap B T).comp (algebraMap A B) := by
    ext a
    simp only [RingHom.comp_apply, IsScalarTower.algebraMap_apply A C T,
      IsScalarTower.algebraMap_apply A B C, IsScalarTower.algebraMap_apply B C T]
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' hABTmaps
  have hABB' : IsScalarTower A B B' := inferInstance
  let : IsScalarTower A B B' := hABB'
  have hBB'T : IsScalarTower B B' T := isScalarTower_localizationAlgebra (.powers h) Cg
  let : IsScalarTower B B' T := hBB'T
  have hAB'Tmaps : algebraMap A T = (algebraMap B' T).comp (algebraMap A B') := by
    ext a
    simp only [RingHom.comp_apply, IsScalarTower.algebraMap_apply A B T,
      IsScalarTower.algebraMap_apply A B B', IsScalarTower.algebraMap_apply B B' T]
  let : IsScalarTower A B' T := IsScalarTower.of_algebraMap_eq' hAB'Tmaps
  have hAT' : Algebra.IsStandardOpenImmersion A T := by
    let : Algebra.IsStandardOpenImmersion A Cg := hAC
    let : Algebra.IsStandardOpenImmersion Cg T := ⟨hCg, inferInstance⟩
    exact .trans A Cg T
  let : Algebra.IsStandardOpenImmersion A B' := hAB
  let : Algebra.IsStandardOpenImmersion A T := hAT'
  have hB'T : Algebra.IsStandardOpenImmersion B' T :=
    standardOpenImmersion_of_left_of_comp A B' T
  have hBT' : Algebra.IsStandardOpenImmersion B T := by
    let : Algebra.IsStandardOpenImmersion B B' := ⟨h, inferInstance⟩
    exact .trans B B' T
  have hc : hC * g ∉ q := by
    have hhC : hC ∉ q := by simpa [hC, qB] using hh
    exact hq.mul_notMem hhC hg
  refine ⟨hC * g, hc, ?_⟩
  have hAway : IsLocalization.Away (hC * g) T :=
    IsLocalization.Away.mul (R := C) Cg T g hC
  let : IsLocalization.Away (hC * g) T := hAway
  let e : T ≃ₐ[C] Localization.Away (hC * g) :=
    IsLocalization.algEquiv (.powers (hC * g)) T _
  exact .of_algEquiv (e.restrictScalars B)

/-- Contracting a prime of the top of an algebra tower to the base can be done in one step or
through the middle. -/
private lemma comap_comap_algebraMap (A B C : Type*) [CommSemiring A] [CommSemiring B]
    [CommSemiring C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (r : Ideal C) : (r.comap (algebraMap B C)).comap (algebraMap A B) = r.comap (algebraMap A C) :=
  by rw [Ideal.comap_comap, IsScalarTower.algebraMap_eq A B C]

/-- In an algebra tower, the canonical map on local rings from the base to a prime of the top is
the composite of the two canonical maps through the middle. -/
private lemma localRingHom_tower_eq_comp (A B C : Type*) [CommSemiring A] [CommSemiring B]
    [CommSemiring C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {r : Ideal C} [r.IsPrime] {q : Ideal B} [q.IsPrime] {p : Ideal A} [p.IsPrime]
    (hq : q = r.comap (algebraMap B C)) (hp : p = q.comap (algebraMap A B))
    (hpr : p = r.comap (algebraMap A C)) :
    Localization.localRingHom p r (algebraMap A C) hpr =
      (Localization.localRingHom q r (algebraMap B C) hq).comp
        (Localization.localRingHom p q (algebraMap A B) hp) := by
  have hcomp : p = r.comap ((algebraMap B C).comp (algebraMap A B)) := by
    rw [hp, hq, Ideal.comap_comap]
  have hstep : Localization.localRingHom p r (algebraMap A C) hpr =
      Localization.localRingHom p r ((algebraMap B C).comp (algebraMap A B)) hcomp := by
    refine (Localization.localRingHom_unique p r _ hcomp fun x => ?_).symm
    rw [Localization.localRingHom_to_map, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply A B C x]
  rw [hstep]
  exact Localization.localRingHom_comp p q r (algebraMap A B) hp (algebraMap B C) hq

/-- Bijectivity of the canonical map on local rings does not depend on which description of the
contracted prime is used. -/
private lemma bijective_localRingHom_congr {A C : Type*} [CommSemiring A] [CommSemiring C]
    (f : A →+* C) {r : Ideal C} [r.IsPrime] {p p' : Ideal A} [p.IsPrime] [p'.IsPrime]
    (hp : p = r.comap f) (hp' : p' = r.comap f)
    (h : Function.Bijective (Localization.localRingHom p r f hp)) :
    Function.Bijective (Localization.localRingHom p' r f hp') := by
  have hpe : p' = p.comap (RingEquiv.refl A) := by
    calc p' = p := hp'.trans hp.symm
      _ = p.comap (RingEquiv.refl A) := by ext x; rfl
  have hpid : p' = p.comap (RingHom.id A) := by simpa using hp'.trans hp.symm
  let e : Localization.AtPrime p' ≃+* Localization.AtPrime p :=
    Localization.localRingEquiv p' p (RingEquiv.refl A) hpe
  have heq : Localization.localRingHom p' r f hp' =
      (Localization.localRingHom p r f hp).comp e.toRingHom := by
    change Localization.localRingHom p' r f hp' =
      (Localization.localRingHom p r f hp).comp
        (Localization.localRingHom p' p (RingHom.id A) hpid)
    simpa [RingHom.comp_id] using
      Localization.localRingHom_comp p' p r (RingHom.id A) hpid f hp
  rw [heq]
  exact h.comp e.bijective

/-- **Stacks Project, Tag 096H.** In an algebra tower, if the base-to-middle and base-to-top
maps identify local rings, then so does the middle-to-top map. -/
@[stacks 096H "identifies_local_rings_permanence"]
theorem identifiesLocalRings_of_left_of_comp
    (A B C : Type*) [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Algebra.IdentifiesLocalRings A B)
    (hAC : Algebra.IdentifiesLocalRings A C) :
    Algebra.IdentifiesLocalRings B C := by
  intro r hr
  let : r.IsPrime := hr
  let q : Ideal B := r.comap (algebraMap B C)
  let : q.IsPrime := Ideal.comap_isPrime _ _
  let p : Ideal A := q.comap (algebraMap A B)
  let : p.IsPrime := Ideal.comap_isPrime _ _
  have hpr : p = r.comap (algebraMap A C) := comap_comap_algebraMap A B C r
  have hbase : Function.Bijective (Localization.localRingHom p r (algebraMap A C) hpr) :=
    bijective_localRingHom_congr (algebraMap A C) rfl hpr (hAC r)
  rw [localRingHom_tower_eq_comp A B C rfl rfl hpr] at hbase
  exact (Function.Bijective.of_comp_iff _ (hAB q)).mp hbase

/-- **Stacks Project, Tag 096G.** In an algebra tower, if the base-to-middle and middle-to-top
maps identify local rings, then so does the base-to-top map. -/
theorem identifiesLocalRings_comp
    (A B C : Type*) [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Algebra.IdentifiesLocalRings A B)
    (hBC : Algebra.IdentifiesLocalRings B C) :
    Algebra.IdentifiesLocalRings A C := by
  intro r hr
  let : r.IsPrime := hr
  let q : Ideal B := r.comap (algebraMap B C)
  let : q.IsPrime := Ideal.comap_isPrime _ _
  let p : Ideal A := q.comap (algebraMap A B)
  let : p.IsPrime := Ideal.comap_isPrime _ _
  have hpr : p = r.comap (algebraMap A C) := comap_comap_algebraMap A B C r
  have hbase : Function.Bijective (Localization.localRingHom p r (algebraMap A C) hpr) := by
    rw [localRingHom_tower_eq_comp A B C rfl rfl hpr]
    exact (hBC r).comp (hAB q)
  exact bijective_localRingHom_congr (algebraMap A C) hpr rfl hbase

end AlgebraicGeometry.ProEtale

add_to_stacks 096G "(1)" Algebra.IsLocalIso.trans
add_to_ega "I 4.5.5" "(i), special case" Algebra.IsLocalIso.trans
