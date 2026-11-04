module

public import Mathlib.RingTheory.Etale.Weakly
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Localization
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractible
public import StacksFrontier.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.Descent

/-!
# Localization along a finitely generated closed subset preserves w-contractibility

If a ring is w-contractible, then its canonical localization along a closed subset cut out by
finitely many elements is w-contractible.

A faithfully flat weakly étale algebra over the localization is enlarged by the localizations
at the chosen generators of the ideal into a faithfully flat weakly étale algebra over the
base ring. A retraction of the latter restricts to the first factor, where the idempotent
cutting it out becomes a unit over the localization, and that restriction is the required
retraction.

## Main results

* `AlgebraicGeometry.ProEtale.isWContractible_localizationRing` gives w-contractibility of
  the localization along a finitely generated ideal.

## Implementation notes

The closed subset `V(I)` is represented by a finitely generated ideal `I`. Its canonical
localization `A^~_{V(I)}` is `AlgebraicGeometry.ProEtale.localizationRing I 1`, since
`D(1) ∩ V(I) = V(I)`. The ambient universe used to test w-contractibility contains the
localized ring and every target ring quantified over by the predicate.

## References

* [Stacks Project, Tag 0987](https://stacks.math.columbia.edu/tag/0987)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u v

/-- The `j`-th component of a ring homomorphism out of a product of rings, available whenever
the homomorphism sends the `j`-th standard idempotent to `1`. -/
private def piComponentRingHom {ι : Type*} [DecidableEq ι]
    (D : ι → Type*) [∀ i, CommRing (D i)] {S : Type*} [CommRing S]
    (ρ : (∀ i, D i) →+* S) (j : ι)
    (h1 : ρ (Pi.single j (1 : D j)) = 1) : D j →+* S where
  toFun x := ρ (Pi.single j x)
  map_zero' := by simp
  map_one' := h1
  map_add' x y := by rw [Pi.single_add, map_add]
  map_mul' x y := by rw [Pi.single_mul, map_mul]

/-- The canonical localization along a finitely generated closed subset of the spectrum of
a w-contractible ring is w-contractible. -/
@[stacks 0987]
theorem isWContractible_localizationRing
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (hA : ProetaleWContractible.IsWContractible.{u, max u v} A) :
    ProetaleWContractible.IsWContractible.{u, max u v}
      (localizationRing I (1 : A)) := by
  classical
  intro T _ _ hweT hffT
  let L := localizationRing I (1 : A)
  have hweT' : Algebra.WeaklyEtale L T := (Algebra.weaklyEtale_iff L T).mpr hweT
  let A' := ULift.{max u v} A
  let e₀ : A' ≃+* A := ULift.ringEquiv
  let f : A →+* A' := e₀.symm.toRingHom
  let g : A' →+* A := e₀.toRingHom
  let : Algebra A A' := f.toAlgebra
  let : Algebra A' A := g.toAlgebra
  let e : A ≃ₐ[A] A' :=
    { toRingEquiv := e₀.symm
      commutes' := fun _ => rfl }
  let e' : A' ≃ₐ[A'] A :=
    { toRingEquiv := e₀
      commutes' := fun _ => rfl }
  let : IsLocalization (IsUnit.submonoid A) A := IsLocalization.self le_rfl
  let : IsLocalization (IsUnit.submonoid A') A' := IsLocalization.self le_rfl
  let : IsLocalization (IsUnit.submonoid A) A' :=
    IsLocalization.isLocalization_of_algEquiv (IsUnit.submonoid A) e
  let : IsLocalization (IsUnit.submonoid A') A :=
    IsLocalization.isLocalization_of_algEquiv (IsUnit.submonoid A') e'
  have hAA' : Algebra.WeaklyEtale A A' :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, max u v, max u v} A).1 A'
      (IsUnit.submonoid A)
  let : Algebra.WeaklyEtale A A' := hAA'
  have hA'A : Algebra.WeaklyEtale A' A :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{max u v, u, max u v} A').1 A
      (IsUnit.submonoid A')
  let : Algebra.WeaklyEtale A' A := hA'A
  have hffAA' : RingHom.FaithfullyFlat f := RingHom.FaithfullyFlat.of_bijective e₀.symm.bijective
  let : Algebra A' L := Algebra.compHom L g
  have hTowerA'L : IsScalarTower A' A L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    rfl
  have : IsScalarTower A' A L := hTowerA'L
  let : Algebra A' T := Algebra.compHom T (algebraMap A' L)
  have hTowerA'T : IsScalarTower A' L T := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    rfl
  have : IsScalarTower A' L T := hTowerA'T
  have hAL : Algebra.WeaklyEtale A L :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} A).1 _
      (localizationSubmonoid I (1 : A))
  let : Algebra.WeaklyEtale A L := hAL
  let : Algebra.WeaklyEtale L T := hweT'
  have hA'L : Algebra.WeaklyEtale A' L :=
    @Algebra.WeaklyEtale.trans A' A _ _ _ L _ _ _ hTowerA'L hA'A hAL
  let : Algebra.WeaklyEtale A' L := hA'L
  have hA'T : Algebra.WeaklyEtale A' T :=
    @Algebra.WeaklyEtale.trans A' L _ _ _ T _ _ _ hTowerA'T hA'L hweT'
  obtain ⟨s, hs⟩ := hI
  let Igens : Set A := ↑s
  let : Fintype Igens := s.finite_toSet.fintype
  let n := Fintype.card Igens
  let eGen : Fin n ≃ Igens := (Fintype.equivFin Igens).symm
  let gen : Fin n → A := fun i => (eGen i).val
  have hgenRange : Set.range gen = Igens := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (eGen i).property
    · intro ha
      refine ⟨eGen.symm ⟨a, ha⟩, ?_⟩
      simp [gen]
  have hspan : Ideal.span (Set.range gen) = I := by
    rw [hgenRange]
    simpa [Igens] using hs
  let D : Fin (n + 1) → Type (max u v) := fun j =>
    Fin.cases T (fun i => Localization.Away (f (gen i))) j
  let : ∀ j, CommRing (D j) := fun j =>
    Fin.cases (inferInstance : CommRing T)
      (fun i => (inferInstance : CommRing (Localization.Away (f (gen i))))) j
  let : ∀ j, Algebra A' (D j) := fun j =>
    Fin.cases (motive := fun j => Algebra A' (D j)) (inferInstance : Algebra A' T)
      (fun i => (inferInstance : Algebra A' (Localization.Away (f (gen i))))) j
  have hweakD : ∀ j, ProetaleWContractible.IsWeaklyEtale A' (D j) := by
    intro j
    exact Fin.cases
      (show ProetaleWContractible.IsWeaklyEtale A' T from
        ⟨hA'T.flat, hA'T.flat_lmul'⟩)
      (fun i => by
        let h : Algebra.WeaklyEtale A' (Localization.Away (f (gen i))) :=
          (weaklyEtale_of_isLocalization_etale_filteredColimit.{max u v, max u v, max u v} A').1
            (Localization.Away (f (gen i)))
            (Submonoid.powers (f (gen i)))
        exact ⟨h.flat, h.flat_lmul'⟩) j
  have hspecBase : ∀ (B : Type (max u v)) [CommRing B] [Algebra A' B] (r : PrimeSpectrum B),
      (ProetaleWContractible.specMapOf A' B).base (⟨r.asIdeal, r.2⟩ :
        AlgebraicGeometry.Spec (CommRingCat.of B)) = PrimeSpectrum.comap (algebraMap A' B) r := by
    intro B _ _ r
    rfl
  have hsurjD : ∀ x : ProetaleWContractible.specOf A',
      ∃ j, x ∈ Set.range (ProetaleWContractible.specMapOf A' (D j)).base := by
    intro x
    let q : PrimeSpectrum A' := x
    let p : PrimeSpectrum A := PrimeSpectrum.comap f q
    by_cases hpI : I ≤ p.asIdeal
    · have hpB : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A L)) := by
        rw [localization_comap_range]
        refine ⟨p, ?_, ?_⟩
        · exact ⟨hpI, by
            simpa [locallyClosedPoints] using p.2.one_notMem⟩
        · exact specializes_refl p
      obtain ⟨pB, hpB⟩ := hpB
      have hffLT : RingHom.FaithfullyFlat (algebraMap L T) :=
        RingHom.faithfullyFlat_algebraMap_iff.mpr hffT
      have hsurjLT : Function.Surjective (PrimeSpectrum.comap (algebraMap L T)) :=
        (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hffLT).2
      obtain ⟨r, hr⟩ := hsurjLT pB
      have hmap : PrimeSpectrum.comap (algebraMap A' T) r = q := by
        calc
          PrimeSpectrum.comap (algebraMap A' T) r =
              PrimeSpectrum.comap (algebraMap A' L) (PrimeSpectrum.comap (algebraMap L T) r) := by
                rw [show algebraMap A' T = (algebraMap L T).comp (algebraMap A' L) by
                  ext a; rfl]
                rw [PrimeSpectrum.comap_comp_apply]
          _ = PrimeSpectrum.comap (algebraMap A' L) pB := by rw [hr]
          _ = PrimeSpectrum.comap g p := by
                rw [show algebraMap A' L = (algebraMap A L).comp g by ext a; rfl]
                rw [PrimeSpectrum.comap_comp_apply, hpB]
          _ = q := by
                change PrimeSpectrum.comap g (PrimeSpectrum.comap f q) = q
                rw [← PrimeSpectrum.comap_comp_apply]
                simp [f, g, e₀]
      exact ⟨0, ⟨r.asIdeal, r.2⟩, (hspecBase T r).trans hmap⟩
    · obtain ⟨a, haGen, haNot⟩ : ∃ a ∈ Igens, a ∉ p.asIdeal := by
        by_contra h
        push Not at h
        apply hpI
        rw [← hspan]
        apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact h (gen i) (eGen i).property
      let i : Fin n := eGen.symm ⟨a, haGen⟩
      have hfi : f (gen i) ∉ q.asIdeal := by
        have hgeni : gen i = a := by
          exact congrArg Subtype.val (eGen.apply_symm_apply ⟨a, haGen⟩)
        rw [hgeni]
        change f a ∉ q.asIdeal
        simpa only [p, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using haNot
      have hmemAway : q ∈ Set.range
          (PrimeSpectrum.comap
            (algebraMap A' (Localization.Away (f (gen i))))) := by
        rw [PrimeSpectrum.localization_away_comap_range
          (Localization.Away (f (gen i))) (f (gen i))]
        exact (PrimeSpectrum.mem_basicOpen _ _).2 hfi
      obtain ⟨r, hrAway⟩ := hmemAway
      exact ⟨Fin.succ i, ⟨r.asIdeal, r.2⟩, (hspecBase _ r).trans hrAway⟩
  obtain ⟨hweakProd, hffProd⟩ :=
    ProetaleWContractible.product_isFaithfullyFlat_weaklyEtale A' (n + 1) D hweakD hsurjD
  let C := ∀ j, D j
  let : Algebra A C := Algebra.compHom C f
  have hTowerAAC : IsScalarTower A A' C := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    rfl
  have : IsScalarTower A A' C := hTowerAAC
  let : Algebra.WeaklyEtale A A' := hAA'
  have hweakAC' : Algebra.WeaklyEtale A C :=
    @Algebra.WeaklyEtale.trans A A' _ _ _ C _ _ _ hTowerAAC hAA'
      ⟨hweakProd.1, hweakProd.2⟩
  have hweakAC : ProetaleWContractible.IsWeaklyEtale A C :=
    ⟨hweakAC'.flat, hweakAC'.flat_lmul'⟩
  have hffAC : Module.FaithfullyFlat A C := by
    have hffA'' : Module.FaithfullyFlat A A' := hffAA'
    have hffA'C : Module.FaithfullyFlat A' C := hffProd
    exact @Module.FaithfullyFlat.trans A _ A' _ _ C _ _ _ hTowerAAC hffA'' hffA'C
  have hdescend : ∀ a : A, algebraMap A C a = algebraMap A' C (f a) := fun a => by
    rw [@IsScalarTower.algebraMap_eq A A' C _ _ _ _ _ _ hTowerAAC]
    rfl
  obtain ⟨σ⟩ := hA C hweakAC hffAC
  let rho : C →+* L := (algebraMap A L).comp σ.toRingHom
  let eT : C := Pi.single (0 : Fin (n + 1)) (1 : D 0)
  have hzero : rho eT = 1 := by
    have haway : ∀ i : Fin n,
        ∀ q : PrimeSpectrum A, I ≤ q.asIdeal →
          PrimeSpectrum.comap σ.toRingHom q ∉
            Set.range (PrimeSpectrum.comap (Pi.evalRingHom D (Fin.succ i))) := by
      intro i q hIq hq
      let j : Fin (n + 1) := Fin.succ i
      let ej : C := Pi.single j (1 : D j)
      rw [ProetaleWContractible.range_comap_evalRingHom D j] at hq
      have hej : ej ∉ (PrimeSpectrum.comap σ.toRingHom q).asIdeal :=
        (PrimeSpectrum.mem_basicOpen ej _).mp hq
      have hej' : σ ej ∉ q.asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hej
      have hiI : gen i ∈ I := by
        rw [← hspan]
        exact Ideal.subset_span ⟨i, rfl⟩
      have hgen : gen i ∈ q.asIdeal := hIq hiI
      have hunit : IsUnit (algebraMap A' (D j) (f (gen i))) := by
        change IsUnit (algebraMap A' (Localization.Away (f (gen i))) (f (gen i)))
        exact IsLocalization.Away.algebraMap_isUnit
          (S := Localization.Away (f (gen i))) (f (gen i))
      obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hunit
      let ez : C := Pi.single j z
      have heq : ej = ej * algebraMap A' C (f (gen i)) * ez := by
        ext k
        change (Pi.single j (1 : D j)) k =
          ((Pi.single j (1 : D j)) * algebraMap A' C (f (gen i)) * Pi.single j z) k
        rw [Pi.mul_apply, Pi.mul_apply]
        by_cases hkj : k = j
        · subst k
          simp only [Pi.single_eq_same, one_mul]
          change 1 = algebraMap A' (D j) (f (gen i)) * z
          exact hz.symm
        · simp [Pi.single_eq_of_ne hkj]
      have hσgen : σ (algebraMap A' C (f (gen i))) = gen i := by
        rw [← hdescend]
        simp
      have heqσ := congrArg σ.toRingHom heq
      simp only [map_mul] at heqσ
      change σ ej = σ ej * σ (algebraMap A' C (f (gen i))) * σ ez at heqσ
      rw [hσgen] at heqσ
      have heq' : σ ej = (σ ez * σ ej) * gen i := by
        calc
          σ ej = σ ej * gen i * σ ez := heqσ
          _ = (σ ez * σ ej) * gen i := by ring
      have hmem : σ ej ∈ q.asIdeal := by
        rw [heq']
        exact q.asIdeal.mul_mem_left (σ ez * σ ej) hgen
      exact hej' hmem
    have hcompZero : ∀ q : PrimeSpectrum A, I ≤ q.asIdeal →
        PrimeSpectrum.comap σ.toRingHom q ∈
          Set.range (PrimeSpectrum.comap (Pi.evalRingHom D (0 : Fin (n + 1)))) := by
      intro q hIq
      have hcover := ProetaleWContractible.iUnion_range_comap_evalRingHom D
      have hmem : PrimeSpectrum.comap σ.toRingHom q ∈
          ⋃ j : Fin (n + 1), Set.range (PrimeSpectrum.comap (Pi.evalRingHom D j)) := by
        rw [hcover]
        exact Set.mem_univ _
      rcases Set.mem_iUnion.mp hmem with ⟨j, hj⟩
      cases j using Fin.cases with
      | zero => exact hj
      | succ i => exact (haway i q hIq hj).elim
    have hnotall : ∀ p : PrimeSpectrum L, rho eT ∉ p.asIdeal := by
      intro p
      let pA : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A L) p
      have hpRange : pA ∈ Set.range (PrimeSpectrum.comap (algebraMap A L)) :=
        ⟨p, rfl⟩
      rw [localization_comap_range I (1 : A)] at hpRange
      rcases hpRange with ⟨q, hq, hspec⟩
      change I ≤ q.asIdeal ∧ (1 : A) ∉ q.asIdeal at hq
      have hqComp := hcompZero q hq.1
      have hqAvoid : eT ∉ (PrimeSpectrum.comap σ.toRingHom q).asIdeal := by
        rw [ProetaleWContractible.range_comap_evalRingHom D 0] at hqComp
        exact (PrimeSpectrum.mem_basicOpen eT _).mp hqComp
      have hpq : pA.asIdeal ≤ q.asIdeal := by
        exact (PrimeSpectrum.asIdeal_le_asIdeal pA q).mpr
          ((PrimeSpectrum.le_iff_specializes pA q).2
            hspec)
      have hcontract :
          (PrimeSpectrum.comap σ.toRingHom pA).asIdeal ≤
            (PrimeSpectrum.comap σ.toRingHom q).asIdeal := by
        rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
        exact Ideal.comap_mono hpq
      have hpAvoid : eT ∉ (PrimeSpectrum.comap σ.toRingHom pA).asIdeal := by
        intro he
        exact hqAvoid (hcontract he)
      simpa [rho, pA, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hpAvoid
    have hu : IsUnit (rho eT) := by
      by_contra hnu
      have hnon : rho eT ∈ nonunits L := by simpa [mem_nonunits_iff] using hnu
      obtain ⟨J, hmax, he⟩ := exists_max_ideal_of_mem_nonunits hnon
      let p : PrimeSpectrum L := ⟨J, hmax.isPrime⟩
      exact hnotall p he
    have heidem : rho eT * rho eT = rho eT := by
      have heT : eT * eT = eT := by
        exact (ProetaleWContractible.single_isIdempotent D (0 : Fin (n + 1))).eq
      rw [← map_mul, heT]
    have hx : rho eT = 1 := by
      have hmul : rho eT * ↑hu.unit⁻¹ = 1 := by
        simp
      calc
        rho eT = rho eT * (rho eT * ↑hu.unit⁻¹) := by rw [hmul]; simp
        _ = rho eT * ↑hu.unit⁻¹ := by rw [← mul_assoc, heidem]
        _ = 1 := hmul
    exact hx
  let gT : T →+* L := piComponentRingHom D rho 0 hzero
  let : Algebra A T := Algebra.compHom T (algebraMap A L)
  have hTowerALT : IsScalarTower A L T := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    rfl
  let : IsScalarTower A L T := hTowerALT
  have hcoord (a : A) : (algebraMap A C a) 0 =
      algebraMap L T (algebraMap A L a) := by
    have hcomponent : (algebraMap A' C (f a)) 0 = algebraMap A' (D 0) (f a) :=
      Pi.algebraMap_apply (Fin (n + 1)) (R := A') D _ 0
    have hfactor : algebraMap A' T ((algebraMap A A') a) =
        algebraMap L T (algebraMap A L a) := by
      rw [@IsScalarTower.algebraMap_eq A' L T _ _ _ _ _ _ hTowerA'T]
      have hgf : g (f a) = a := e₀.apply_symm_apply a
      have hleft : algebraMap A' L (algebraMap A A' a) = algebraMap A L a :=
        congrArg (algebraMap A L) hgf
      simpa only [RingHom.comp_apply] using congrArg (algebraMap L T) hleft
    rw [hdescend a, hcomponent]
    exact hfactor
  have hbase : gT.comp (algebraMap A T) = algebraMap A L := by
    ext a
    change rho (Pi.single 0 (algebraMap A T a)) = algebraMap A L a
    have hsingle : Pi.single (0 : Fin (n + 1)) (algebraMap A T a) =
        eT * algebraMap A C a := by
      ext j
      by_cases hj : j = 0
      · subst j
        have hdiag : Pi.single (0 : Fin (n + 1)) (show D 0 from algebraMap A T a) 0 =
            (show D 0 from algebraMap A T a) :=
          Pi.single_eq_same (M := D) 0 _
        have hunit : eT (0 : Fin (n + 1)) = (1 : D 0) :=
          Pi.single_eq_same (M := D) 0 1
        change Pi.single (0 : Fin (n + 1)) (show D 0 from algebraMap A T a) 0 =
          (eT * algebraMap A C a) 0
        rw [hdiag, Pi.mul_apply, hunit, one_mul, hcoord]
        simpa [@IsScalarTower.algebraMap_eq A L T _ _ _ _ _ _ hTowerALT]
      · have hoff : Pi.single (0 : Fin (n + 1)) (show D 0 from algebraMap A T a) j = 0 :=
          Pi.single_eq_of_ne (M := D) hj _
        have hzeroT : eT j = 0 := Pi.single_eq_of_ne (M := D) hj 1
        change Pi.single (0 : Fin (n + 1)) (show D 0 from algebraMap A T a) j =
          (eT * algebraMap A C a) j
        rw [hoff, Pi.mul_apply, hzeroT, zero_mul]
    rw [hsingle, map_mul, hzero]
    simp [rho, σ.commutes]
  have hgT : gT.comp (algebraMap L T) = RingHom.id L := by
    apply IsLocalization.ringHom_ext (localizationSubmonoid I (1 : A))
    ext a
    simpa [@IsScalarTower.algebraMap_eq A L T _ _ _ _ _ _ hTowerALT] using
      DFunLike.congr_fun hbase a
  refine ⟨{
    toRingHom := gT
    commutes' := by
      intro b
      have hb := RingHom.congr_fun hgT b
      simpa using hb
  }⟩

end AlgebraicGeometry.ProEtale

end
