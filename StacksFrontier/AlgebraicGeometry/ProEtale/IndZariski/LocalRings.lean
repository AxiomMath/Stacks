module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalIsomorphism

/-!
# Ind-Zariski algebras identify local rings

An ind-Zariski map of commutative rings induces an isomorphism on local rings at every prime of
its target.

## Main results

* `AlgebraicGeometry.ProEtale.identifiesLocalRings_of_isIndZariski`: an ind-Zariski algebra
  identifies local rings.

## Implementation notes

The conclusion uses the canonical maps between localizations at corresponding prime ideals, as
in `AlgebraicGeometry.ProEtale.IdentifiesLocalRings`. For a single local isomorphism the
isomorphism is assembled from the two localization-of-a-localization comparisons at the
principal open where the map is a standard open immersion. The colimit argument then transports
a chosen stage: the local ring at a prime of the colimit is the local ring at the induced prime
of any stage, because every element of the colimit is represented at some stage. The argument
applies to the lifted target appearing in `AlgebraicGeometry.ProEtale.IsIndZariski`, and
`ULift.algEquiv` transports the result to the original target.

## References

* [Stacks Project, Tag 096T](https://stacks.math.columbia.edu/tag/096T)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory

universe u v w

/-- A local isomorphism identifies the local rings at every prime of its target: the map on
localizations factors through the principal open on which it is a standard open immersion, where
both localization-of-a-localization comparisons are isomorphisms. -/
private theorem stage_localRingHom_bijective
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.IsLocalIso A S] (q : Ideal S) [hq : q.IsPrime] :
    Function.Bijective (Localization.localRingHom (q.comap (algebraMap A S)) q
      (algebraMap A S) rfl) := by
  let p := q.comap (algebraMap A S)
  have : p.IsPrime := Ideal.comap_isPrime (algebraMap A S) q
  obtain ⟨g, hgq, hg⟩ := Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := A) q
  let T := Localization.Away g
  obtain ⟨r, hr⟩ : (⟨q, hq⟩ : PrimeSpectrum S) ∈
      Set.range (PrimeSpectrum.comap (algebraMap S T)) := by
    rwa [PrimeSpectrum.localization_away_comap_range T g]
  let qT : Ideal T := r.asIdeal
  have : qT.IsPrime := r.isPrime
  have hqTbase : qT.comap (algebraMap S T) = q := by
    simpa [qT] using congrArg PrimeSpectrum.asIdeal hr
  obtain ⟨a, ha⟩ := Algebra.IsStandardOpenImmersion.exists_away A T
  let U := Localization.Away a
  let : IsLocalization.Away a T := ha
  let e : T ≃ₐ[A] U := IsLocalization.algEquiv (.powers a) T U
  let qU : Ideal U := qT.comap e.symm.toRingHom
  have hqU : qT = qU.comap e.toRingHom := by
    ext x
    simp [qU, Ideal.mem_comap]
  have hpu : p = qU.comap (algebraMap A U) := by
    ext x
    show algebraMap A S x ∈ q ↔ algebraMap A U x ∈ qU
    rw [← hqTbase]
    simp [qU, IsScalarTower.algebraMap_apply A S T]
  have : qU.IsPrime := Ideal.comap_isPrime e.symm.toRingHom qT
  let e₁ : Localization.AtPrime qT ≃ₐ[A] Localization.AtPrime qU :=
    Localization.localAlgEquiv qT qU e hqU
  let e₂' := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (.powers a) qU
  let p' : Ideal A := qU.comap (algebraMap A U)
  have : p'.IsPrime := Ideal.comap_isPrime (algebraMap A U) qU
  let c₂ : Localization.AtPrime p ≃+* Localization.AtPrime p' :=
    Localization.localRingEquiv p p' (RingEquiv.refl A) (by change p = p'; exact hpu)
  let : IsScalarTower A S (Localization.AtPrime qT) := IsScalarTower.of_algebraMap_eq' rfl
  let e₃' := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (.powers g) qT
  let qS' : Ideal S := qT.comap (algebraMap S T)
  let : qS'.IsPrime := Ideal.comap_isPrime (algebraMap S T) qT
  let c₃ : Localization.AtPrime q ≃+* Localization.AtPrime qS' :=
    Localization.localRingEquiv q qS' (RingEquiv.refl S) (by change q = qS'; exact hqTbase.symm)
  let ee : Localization.AtPrime p ≃+* Localization.AtPrime q :=
    c₂.trans (e₂'.toRingEquiv.trans (e₁.symm.toRingEquiv.trans
      (e₃'.symm.toRingEquiv.trans c₃.symm)))
  have hh : Localization.localRingHom p q (algebraMap A S) rfl = ee.toRingHom := by
    apply Localization.localRingHom_unique p q (algebraMap A S) rfl
    intro x
    simp only [AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
      AlgEquiv.symm_toEquiv_eq_symm, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_ringHom_trans,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, RingEquiv.coe_mk,
      EquivLike.coe_coe, Function.comp_apply, Localization.localRingEquiv_apply,
      RingEquiv.coe_ringHom_refl, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, Localization.localRingHom_to_map,
      RingHom.id_apply, AlgEquiv.commutes, Localization.localRingEquiv_symm_apply,
      RingEquiv.symm_refl, ee, c₂, e₂', e₁, c₃]
    rw [IsScalarTower.algebraMap_apply A S (Localization.AtPrime qT) x, e₃'.symm.commutes,
      Localization.localRingHom_to_map]
    rfl
  rw [hh]
  exact ee.toEquiv.bijective

/-- Every element of a filtered colimit of algebras is the image of an element of one of the
stages: the subalgebra of such elements receives a map from the colimit splitting the inclusion. -/
private theorem rep_alg_colimit {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] {J : Type w} [CategoryTheory.SmallCategory J] [CategoryTheory.IsFiltered J]
    (pres : CategoryTheory.Limits.ColimitPresentation J (CommAlgCat.of A B)) (b : B) :
    ∃ i x, (pres.ι.app i).hom x = b := by
  classical
  let φ (i : J) : pres.diag.obj i →ₐ[A] B := (pres.ι.app i).hom
  have hjoin : ∀ x y : B, (∃ i, ∃ a : pres.diag.obj i, φ i a = x) →
      (∃ i, ∃ a : pres.diag.obj i, φ i a = y) →
      ∃ k, ∃ a b : pres.diag.obj k, φ k a = x ∧ φ k b = y := by
    rintro _ _ ⟨i, xi, rfl⟩ ⟨j, yj, rfl⟩
    obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
    exact ⟨k, (pres.diag.map f).hom xi, (pres.diag.map g).hom yj, by simp [φ], by simp [φ]⟩
  let D : Subalgebra A B := {
    carrier := {y | ∃ i : J, ∃ x : pres.diag.obj i, φ i x = y}
    add_mem' := by
      intro x y hx hy
      obtain ⟨k, a, b, rfl, rfl⟩ := hjoin x y hx hy
      exact ⟨k, a + b, map_add _ _ _⟩
    mul_mem' := by
      intro x y hx hy
      obtain ⟨k, a, b, rfl, rfl⟩ := hjoin x y hx hy
      exact ⟨k, a * b, map_mul _ _ _⟩
    algebraMap_mem' := by
      intro a
      show ∃ i : J, ∃ x : pres.diag.obj i, φ i x = algebraMap A B a
      exact ⟨Classical.choice IsFiltered.nonempty, algebraMap A _ a, (φ _).commutes a⟩ }
  let coc : CategoryTheory.Limits.Cocone pres.diag := {
    pt := CommAlgCat.of A D
    ι := {
      app := fun i => CommAlgCat.ofHom ((φ i).codRestrict D (by exact ⟨i, ·, rfl⟩))
      naturality := by
        intro i j f
        apply CommAlgCat.hom_ext
        ext x
        apply Subtype.ext
        exact congrArg (fun h => h x) (pres.ι.naturality f)
    }
  }
  let desc := pres.isColimit.desc coc
  have hcat : CommAlgCat.ofHom (D.val.comp desc.hom) =
      CommAlgCat.ofHom (AlgHom.id A B) := by
    apply pres.isColimit.hom_ext
    intro i
    apply CommAlgCat.hom_ext
    ext x
    show D.val (desc.hom (φ i x)) = φ i x
    have hfac' : desc.hom (φ i x) = (φ i).codRestrict D (fun x => ⟨i, x, rfl⟩) x := by
      simpa [desc, coc] using congrArg (fun h => h x) (pres.isColimit.fac coc i)
    rw [hfac']
    exact AlgHom.coe_codRestrict (φ i) D (fun x => ⟨i, x, rfl⟩) x
  have hdesc : D.val.comp desc.hom = AlgHom.id A B := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun h => h x) (congrArg CommAlgCat.Hom.hom hcat)
  have hb : (desc b).val = b := by
    simpa [AlgHom.comp_apply] using congrArg (fun f : B →ₐ[A] B => f b) hdesc
  obtain ⟨i, x, hx⟩ := (desc b).property
  exact ⟨i, x, hx.trans hb⟩

/-- A filtered colimit of local isomorphisms identifies local rings. The local ring of the
colimit at a prime is identified with the local ring of any stage at the induced prime, and the
local ring of the base at the contraction maps isomorphically to each of those. -/
private theorem identifiesLocalRings_of_ind_localIso
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (h : ObjectProperty.ind.{w}
      (fun C : CommAlgCat.{v} A => Algebra.IsLocalIso A C) (CommAlgCat.of A B)) :
    Algebra.IdentifiesLocalRings A B := by
  intro q hq
  classical
  obtain ⟨J, hJsmall, hJfiltered, pres, hstage⟩ := h
  let φ (i : J) : pres.diag.obj i →ₐ[A] B := (pres.ι.app i).hom
  let p : Ideal A := q.comap (algebraMap A B)
  have : p.IsPrime := Ideal.comap_isPrime (algebraMap A B) q
  let qi (i : J) : Ideal (pres.diag.obj i) := q.comap (φ i).toRingHom
  have hqi (i : J) : (qi i).IsPrime := Ideal.comap_isPrime (φ i).toRingHom q
  have hpi (i : J) : p = (qi i).comap (algebraMap A (pres.diag.obj i)) := by
    ext a
    show algebraMap A B a ∈ q ↔ φ i (algebraMap A (pres.diag.obj i) a) ∈ q
    simp [φ]
  let fA (i : J) : A →ₐ[A] pres.diag.obj i := Algebra.ofId A (pres.diag.obj i)
  let ei (i : J) : Localization.AtPrime p →ₐ[A] Localization.AtPrime (qi i) :=
    Localization.localAlgHom p (qi i) (fA i) (hpi i)
  have hei_bij (i : J) : Function.Bijective (ei i) := by
    let : Algebra.IsLocalIso A (pres.diag.obj i) := hstage i
    let : IsScalarTower A (pres.diag.obj i) (Localization.AtPrime (qi i)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let pᵢ := (qi i).comap (algebraMap A (pres.diag.obj i))
    have : pᵢ.IsPrime := Ideal.comap_isPrime (algebraMap A (pres.diag.obj i)) (qi i)
    let c : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime pᵢ :=
      Localization.localAlgEquiv p pᵢ (AlgEquiv.refl : A ≃ₐ[A] A) (by change p = pᵢ; exact hpi i)
    let l : Localization.AtPrime pᵢ →ₐ[A] Localization.AtPrime (qi i) :=
      Localization.localAlgHom pᵢ (qi i) (fA i) rfl
    have hl : Function.Bijective l :=
      stage_localRingHom_bijective (A := A) (S := pres.diag.obj i) (qi i)
    have heq : l.comp c.toAlgHom = ei i := by
      ext
    rw [← heq]
    exact hl.comp c.bijective
  let Ei (i : J) : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime (qi i) :=
    AlgEquiv.ofBijective (ei i) (hei_bij i)
  let inc (i : J) : pres.diag.obj i →ₐ[A] Localization.AtPrime (qi i) := {
    toRingHom := algebraMap (pres.diag.obj i) (Localization.AtPrime (qi i))
    commutes' := by
      intro a
      simp [IsScalarTower.algebraMap_apply A (pres.diag.obj i) (Localization.AtPrime (qi i))]
  }
  let vi (i : J) : Localization.AtPrime (qi i) →ₐ[A] Localization.AtPrime q :=
    Localization.localAlgHom (qi i) q (φ i) rfl
  have hvi (i : J) : (vi i).comp (Ei i).toAlgHom =
      Localization.localAlgHom p q (Algebra.ofId A B) rfl := by
    ext
  let ψ (i : J) : pres.diag.obj i →ₐ[A] Localization.AtPrime p :=
    (Ei i).symm.toAlgHom.comp (inc i)
  have hψ (i j : J) (f : i ⟶ j) : (ψ j).comp (pres.diag.map f).hom = ψ i := by
    apply AlgHom.ext
    intro x
    let u : pres.diag.obj i →ₐ[A] pres.diag.obj j := (pres.diag.map f).hom
    have hqij : qi i = (qi j).comap u := by
      ext y
      show φ i y ∈ q ↔ φ j (u y) ∈ q
      simp [u, φ]
    let vij : Localization.AtPrime (qi i) →ₐ[A] Localization.AtPrime (qi j) :=
      Localization.localAlgHom (qi i) (qi j) u hqij
    have hcomp : (vij.comp (Ei i).toAlgHom) = (Ei j).toAlgHom := by
      ext
    have hinc : vij (inc i x) = inc j (u x) := by
      simp [vij, inc, Localization.localAlgHom]
    show (Ei j).symm ((inc j) (u x)) = (Ei i).symm ((inc i) x)
    rw [← hinc]
    have hx := congrArg (fun g : Localization.AtPrime p →ₐ[A] Localization.AtPrime (qi j) =>
      (Ei j).symm (g ((Ei i).symm (inc i x)))) hcomp
    simpa using hx
  let i₀ : J := Classical.choice (IsFiltered.nonempty (C := J))
  let ψ₀ (i : J) : pres.diag.obj i →ₐ[A] Localization.AtPrime (qi i₀) :=
    (Ei i₀).toAlgHom.comp (ψ i)
  have hψ₀ (i j : J) (f : i ⟶ j) :
      (ψ₀ j).comp (pres.diag.map f).hom = ψ₀ i := by
    have h := congrArg (fun g : pres.diag.obj i →ₐ[A] Localization.AtPrime p =>
      (Ei i₀).toAlgHom.comp g) (hψ i j f)
    simpa [ψ₀, AlgHom.comp_assoc] using h
  let coc : CategoryTheory.Limits.Cocone pres.diag := {
    pt := CommAlgCat.of A (Localization.AtPrime (qi i₀))
    ι := {
      app := fun i => CommAlgCat.ofHom (ψ₀ i)
      naturality := by
        intro i j f
        apply CommAlgCat.hom_ext
        ext x
        exact congrArg (fun g : pres.diag.obj i →ₐ[A] Localization.AtPrime (qi i₀) => g x)
          (hψ₀ i j f)
    }
  }
  let descB : B →ₐ[A] Localization.AtPrime (qi i₀) :=
    (pres.isColimit.desc coc).hom
  have hdescFac (i : J) (x : pres.diag.obj i) : descB (φ i x) = ψ₀ i x := by
    simpa [descB, coc] using congrArg (fun g => g x) (pres.isColimit.fac coc i)
  have hunit (s : q.primeCompl) : IsUnit (descB (s : B)) := by
    obtain ⟨i, x, hxrep⟩ := rep_alg_colimit pres (s : B)
    have hxs : φ i x ∉ q := by
      rw [hxrep]
      exact s.property
    have hx : x ∉ qi i := by simpa [qi] using hxs
    rw [← hxrep, hdescFac]
    show IsUnit ((Ei i₀) ((Ei i).symm (inc i x)))
    exact IsUnit.map (Ei i₀).toRingHom <|
      IsUnit.map (Ei i).symm.toRingHom
        (IsLocalization.map_units _ (⟨x, hx⟩ : (qi i).primeCompl))
  let gRing₀ : Localization.AtPrime q →+* Localization.AtPrime (qi i₀) :=
    IsLocalization.lift hunit
  let gAlg₀ : Localization.AtPrime q →ₐ[A] Localization.AtPrime (qi i₀) := {
    toRingHom := gRing₀
    commutes' := by
      intro a
      show IsLocalization.lift hunit
        (algebraMap B (Localization.AtPrime q) (algebraMap A B a)) = _
      rw [IsLocalization.lift_eq]
      exact descB.commutes a
  }
  let gAlg : Localization.AtPrime q →ₐ[A] Localization.AtPrime p :=
    (Ei i₀).symm.toAlgHom.comp gAlg₀
  let f : Localization.AtPrime p →ₐ[A] Localization.AtPrime q :=
    Localization.localAlgHom p q (Algebra.ofId A B) rfl
  have hleft : gAlg.comp f = AlgHom.id A (Localization.AtPrime p) := by
    ext
  have hright : f.comp gAlg = AlgHom.id A (Localization.AtPrime q) := by
    ext b
    obtain ⟨i, x, hxrep⟩ := rep_alg_colimit pres b
    show f ((Ei i₀).symm (gAlg₀ (algebraMap B (Localization.AtPrime q) b))) =
      algebraMap B (Localization.AtPrime q) b
    calc
      f ((Ei i₀).symm (gAlg₀ (algebraMap B (Localization.AtPrime q) b))) =
          f ((Ei i₀).symm (ψ₀ i x)) := by
        congr 2
        calc
          gAlg₀ (algebraMap B (Localization.AtPrime q) b) = descB b := by
            show IsLocalization.lift hunit
              (algebraMap B (Localization.AtPrime q) b) = descB b
            exact IsLocalization.lift_eq hunit b
          _ = descB (φ i x) := by rw [hxrep]
          _ = ψ₀ i x := hdescFac i x
      _ = f ((Ei i).symm (inc i x)) := by
        simp [ψ₀, ψ]
      _ = vi i (inc i x) := by
        have h := congrArg (fun g : Localization.AtPrime p →ₐ[A]
          Localization.AtPrime q => g ((Ei i).symm (inc i x))) (hvi i)
        simpa using h.symm
      _ = algebraMap B (Localization.AtPrime q) (φ i x) := by
        show Localization.localRingHom (qi i) q (φ i).toRingHom rfl
          (algebraMap (pres.diag.obj i) (Localization.AtPrime (qi i)) x) = _
        exact Localization.localRingHom_to_map (I := qi i) (J := q)
          (f := (φ i).toRingHom) (hIJ := rfl) x
      _ = algebraMap B (Localization.AtPrime q) b := by rw [hxrep]
  exact (AlgEquiv.ofAlgHom f gAlg hright hleft).bijective

/-- An ind-Zariski map identifies the local rings at every prime of its target. -/
@[stacks 096T]
theorem identifiesLocalRings_of_isIndZariski
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (h : IsIndZariski.{u, v, w} A B) :
    Algebra.IdentifiesLocalRings A B := by
  intro q hq
  -- The ind-Zariski presentation has target `ULift B` in the universe of its stages.
  let e : ULift.{u} B ≃ₐ[A] B := ULift.algEquiv
  let q' : Ideal (ULift.{u} B) := q.comap e.toRingHom
  have : q'.IsPrime := Ideal.comap_isPrime e.toRingHom q
  have hbij := identifiesLocalRings_of_ind_localIso A (ULift.{u} B) h q'
  let f : Localization.AtPrime (q.comap (algebraMap A B)) →ₐ[A]
      Localization.AtPrime q' :=
    Localization.localAlgHom _ q' (Algebra.ofId A (ULift.{u} B)) rfl
  let E : Localization.AtPrime q' ≃ₐ[A] Localization.AtPrime q :=
    Localization.localAlgEquiv q' q e rfl
  have hf : Localization.localRingHom (q.comap (algebraMap A B)) q
      (algebraMap A B) rfl = (E.toAlgHom.comp f).toRingHom := by
    apply Localization.localRingHom_unique
    intro a
    show E (f (algebraMap A _ a)) = _
    rw [f.commutes, E.commutes]
    rfl
  rw [hf]
  exact E.bijective.comp hbij

end AlgebraicGeometry.ProEtale

end
