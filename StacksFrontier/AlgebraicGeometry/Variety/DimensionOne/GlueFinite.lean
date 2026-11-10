module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.GlueTwo
public import StacksCore.Tactic.StacksAttribute

/-!
# Gluing finitely many semilocal one-dimensional subrings of a field

Let finitely many Noetherian, one-dimensional semilocal subrings of a field have that field as
their fraction field, and suppose the multiplication map from every pairwise tensor product is
surjective. Their intersection is then again a Noetherian one-dimensional semilocal domain. The
induced maps on spectra are open immersions which cover the spectrum of the intersection, and
each closed point lies in the image of exactly one member of the cover.

The argument is an induction on the finite index set: adjoining one more subring to the
intersection of the others is the two-ring gluing already established, and the ring-theoretic
properties of the result are read off from the open cover it produces.

## Main definitions

* `Subring.gluedSubring` is the intersection of the given subrings.
* `Subring.gluedSubringInclusion` is its canonical inclusion into any member of the family.

## Main results

* `Subring.isNoetherianRing_gluedSubring`, `Subring.finite_maximalSpectrum_gluedSubring` and
  `Subring.ringKrullDim_gluedSubring` give the ring-theoretic properties of the intersection.
* `Subring.isOpenImmersion_specMap_gluedSubringInclusion` says that each induced map on spectra
  is an open immersion.
* `Subring.iUnion_range_comap_gluedSubringInclusion` says that these maps cover the spectrum.
* `Subring.existsUnique_range_comap_gluedSubringInclusion` says that every closed point occurs
  in exactly one member of the cover.

## Implementation notes

The source's finite nonempty list is represented by a finite nonempty index type. Its asserted
subring is made canonical by taking the infimum in `Subring K`. Semilocality is expressed by
finiteness of `MaximalSpectrum`. The maps on the underlying prime spectra are written using
`PrimeSpectrum.comap`; these are the underlying maps of the corresponding affine-scheme
morphisms.

## References

* [Stacks Project, Tag 09N4](https://stacks.math.columbia.edu/tag/09N4)
-/

@[expose] public section

namespace Subring

open CategoryTheory

universe u v

/-- The intersection of a family of subrings of a common ring. -/
abbrev gluedSubring {K : Type u} [CommRing K] {ι : Type v} (B : ι → Subring K) : Subring K :=
  ⨅ i, B i

/-- The canonical inclusion of the intersection into one member of the family. -/
abbrev gluedSubringInclusion {K : Type u} [CommRing K] {ι : Type v}
    (B : ι → Subring K) (i : ι) : gluedSubring B →+* B i :=
  Subring.inclusion (iInf_le B i)

private lemma not_isField_of_ringKrullDim_eq_one {R : Type*} [CommRing R]
    (h : ringKrullDim R = 1) : ¬ IsField R := fun hf => by
  have h0 := ringKrullDim_eq_zero_of_isField hf
  rw [h] at h0
  exact one_ne_zero h0

private lemma krullDimLE_one_of_ringKrullDim_eq_one {R : Type*} [CommRing R]
    (h : ringKrullDim R = 1) : Ring.KrullDimLE 1 R :=
  Ring.krullDimLE_iff.mpr (by simp only [h, Nat.cast_one, le_refl])

private lemma comap_asIdeal_of_comap_eq {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    {q : PrimeSpectrum S} {p : PrimeSpectrum R} (h : PrimeSpectrum.comap f q = p) :
    q.asIdeal.comap f = p.asIdeal := by
  simpa only [PrimeSpectrum.comap, PrimeSpectrum.asIdeal] using congrArg PrimeSpectrum.asIdeal h

private lemma mem_of_mem_jacobson_bot {R : Type*} [CommRing R] {x : R} {M : Ideal R}
    (hx : x ∈ Ideal.jacobson (⊥ : Ideal R)) (hM : M.IsMaximal) : x ∈ M := by
  rw [Ideal.jacobson, Ideal.mem_sInf] at hx
  exact hx ⟨bot_le, hM⟩

private lemma ne_bot_of_comap_ne_bot {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) {I : Ideal S} (h : I.comap f ≠ ⊥) : I ≠ ⊥ := by
  rintro rfl
  exact h (Ideal.comap_bot_of_injective f hf)

private lemma isMaximal_of_comap_isMaximal {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R]
    [IsDomain S] {f : R →+* S} (hf : Function.Injective f) (hR : ringKrullDim R = 1)
    (hS : ringKrullDim S = 1) (q : PrimeSpectrum S) (hq : (q.asIdeal.comap f).IsMaximal) :
    q.asIdeal.IsMaximal := by
  have := krullDimLE_one_of_ringKrullDim_eq_one hS
  refine q.isPrime.isMaximal_of_ne_bot (ne_bot_of_comap_ne_bot hf ?_)
  exact Ring.ne_bot_of_isMaximal_of_not_isField hq (not_isField_of_ringKrullDim_eq_one hR)

private lemma tensorProduct_lift_surjective_of_jacobson_inverse
    {K : Type*} [Field K] (A B : Subring K) [IsFractionRing B K]
    (x : A) (hx : x ≠ 0) (y : B) (hxy : (y : K) = (x : K)⁻¹)
    (hy : y ∈ Ideal.jacobson (⊥ : Ideal B)) (h_dim : ringKrullDim B = 1) :
    Function.Surjective
      (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  classical
  have hdimLE := krullDimLE_one_of_ringKrullDim_eq_one h_dim
  intro z
  obtain ⟨a, b, hb, hdiv⟩ := IsFractionRing.div_surjective B z
  have hb0 : (b : B) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hy_rad : y ∈ (Ideal.span ({b} : Set B)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro p hp
    have hbp : b ∈ p := hp.1 (Ideal.subset_span (by simp))
    have hp_ne : p ≠ ⊥ := fun h => hb0 (by simpa [h] using hbp)
    exact mem_of_mem_jacobson_bot hy (hp.2.isMaximal_of_ne_bot hp_ne)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hy_rad
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hn
  have hcK : (y : K) ^ n = (b : K) * c := congrArg Subtype.val hc
  have hyx : (y : K) * (x : K) = 1 := by
    rw [hxy]
    exact inv_mul_cancel₀ (by exact_mod_cast hx)
  have hbcx : (b : K) * c * (x : K) ^ n = 1 := by
    rw [← hcK, ← mul_pow, hyx, one_pow]
  have hrepr : (z : K) = (a : K) * c * (x : K) ^ n := by
    calc
      (z : K) = (a : K) / (b : K) * ((b : K) * c * (x : K) ^ n) := by
        rw [hbcx, mul_one]
        exact hdiv.symm
      _ = (a : K) * c * (x : K) ^ n := by field_simp [hb0]
  refine ⟨(x ^ n) ⊗ₜ[ℤ] (a * c), ?_⟩
  change (x : K) ^ n * ((a * c : B) : K) = z
  simpa only [Subring.coe_pow, Subring.coe_mul, mul_comm, mul_left_comm, mul_assoc]
    using hrepr.symm

private lemma mem_jacobson_of_openCover
    {K : Type u} [Field K] {ι : Type v} [Finite ι] [Nonempty ι]
    (R : Subring K) (B : ι → Subring K) (f : ∀ i, R →+* B i)
    (hf : ∀ i, Function.Injective (f i))
    (h_dim : ∀ i, ringKrullDim (B i) = 1)
    (h_cover : (⋃ i, Set.range (PrimeSpectrum.comap (f i))) = Set.univ)
    (h_dimR : ringKrullDim R = 1) {x : R}
    (hx : ∀ i, f i x ∈ Ideal.jacobson (⊥ : Ideal (B i))) :
    x ∈ Ideal.jacobson (⊥ : Ideal R) := by
  rw [Ideal.jacobson, Ideal.mem_sInf]
  intro m hm
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
    (Set.eq_univ_iff_forall.mp h_cover (⟨m, hm.2.isPrime⟩ : PrimeSpectrum R))
  obtain ⟨q, hq⟩ := Set.mem_range.mp hi
  have hqcomap : q.asIdeal.comap (f i) = m := comap_asIdeal_of_comap_eq hq
  have hqmax : q.asIdeal.IsMaximal :=
    isMaximal_of_comap_isMaximal (hf i) h_dimR (h_dim i) q (by rw [hqcomap]; exact hm.2)
  rw [← hqcomap]
  exact Ideal.mem_comap.mpr (mem_of_mem_jacobson_bot (hx i) hqmax)

private lemma isNoetherian_of_openCover
    {K : Type u} [Field K] {ι : Type v} [Finite ι]
    (R : Subring K) (B : ι → Subring K) (f : ∀ i, R →+* B i)
    (h_open : ∀ i, AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (f i))))
    (h_cover : (⋃ i, Set.range (PrimeSpectrum.comap (f i))) = Set.univ)
    [∀ i, IsNoetherianRing (B i)] :
    IsNoetherianRing R := by
  let X := AlgebraicGeometry.Spec (CommRingCat.of R)
  let g i := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (f i))
  let U i := AlgebraicGeometry.Scheme.Hom.opensRange (g i)
  let S i : X.affineOpens := ⟨U i,
    AlgebraicGeometry.isAffineOpen_opensRange (g i)⟩
  have hS : (⨆ i, (S i).1 : X.Opens) = ⊤ := by
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    change (⋃ i, Set.range (PrimeSpectrum.comap (f i))) = Set.univ
    exact h_cover
  have hX : AlgebraicGeometry.IsNoetherian X :=
    (AlgebraicGeometry.isNoetherian_iff_of_finite_iSup_eq_top hS).mpr fun i => by
      let e : (B i) ≃+* ↑(X.presheaf.obj (Opposite.op (S i).1)) :=
        (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (B i))).symm ≪≫
          AlgebraicGeometry.IsOpenImmersion.ΓIsoTop (g i)).commRingCatIsoToRingEquiv)
      exact isNoetherianRing_of_ringEquiv (B i) e
  exact (AlgebraicGeometry.isNoetherian_Spec).mp hX

private lemma krullDimLE_one_of_openCover
    {K : Type u} [Field K] {R : Subring K} {ι : Type v} [Finite ι] [Nonempty ι]
    (B : ι → Subring K) (f : ∀ i, R →+* B i)
    (hf : ∀ i, Function.Injective (f i)) (h_dim : ∀ i, ringKrullDim (B i) = 1)
    (h_open : ∀ i, AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (f i))))
    (h_cover : (⋃ i, Set.range (PrimeSpectrum.comap (f i))) = Set.univ) :
    Ring.KrullDimLE 1 R := by
  refine Ring.KrullDimLE.mk₁' fun I hIbot hIprime => ?_
  by_contra hInotmax
  obtain ⟨M, hMmax, hIM⟩ := Ideal.exists_le_maximal I hIprime.ne_top
  let p : PrimeSpectrum R := ⟨I, hIprime⟩
  let r : PrimeSpectrum R := ⟨M, hMmax.isPrime⟩
  obtain ⟨i, hir⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp h_cover r)
  obtain ⟨q, hq⟩ := Set.mem_range.mp hir
  let g := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (f i))
  have : AlgebraicGeometry.IsOpenImmersion g := h_open i
  have hemb : Topology.IsOpenEmbedding g := AlgebraicGeometry.Scheme.Hom.isOpenEmbedding g
  have hprle : p ≤ r := hIM
  let pS : AlgebraicGeometry.Spec (CommRingCat.of R) := p
  let rS : AlgebraicGeometry.Spec (CommRingCat.of R) := r
  let qS : AlgebraicGeometry.Spec (CommRingCat.of (B i)) := q
  have hprS : pS ⤳ rS := (PrimeSpectrum.le_iff_specializes p r).mp hprle
  have hqS : g qS = rS := hq
  have hprange : p ∈ Set.range (PrimeSpectrum.comap (f i)) :=
    hprS.mem_open hemb.isOpen_range ⟨qS, hqS⟩
  obtain ⟨q', hq'⟩ := Set.mem_range.mp hprange
  let q'S : AlgebraicGeometry.Spec (CommRingCat.of (B i)) := q'
  have hq'S : g q'S = pS := hq'
  have hq'specS : q'S ⤳ qS := by
    rwa [← hemb.isInducing.specializes_iff, hq'S, hqS]
  have hq'le : q'.asIdeal ≤ q.asIdeal :=
    (PrimeSpectrum.le_iff_specializes q' q).mpr hq'specS
  have hq'comap : q'.asIdeal.comap (f i) = I := comap_asIdeal_of_comap_eq hq'
  have hqcomap : q.asIdeal.comap (f i) = M := comap_asIdeal_of_comap_eq hq
  have := krullDimLE_one_of_ringKrullDim_eq_one (h_dim i)
  have hq'max : q'.asIdeal.IsMaximal :=
    q'.isPrime.isMaximal_of_ne_bot (ne_bot_of_comap_ne_bot (hf i) (by rwa [hq'comap]))
  apply hInotmax
  rwa [← hq'comap, hq'max.eq_of_le q.isPrime.ne_top hq'le, hqcomap]

private lemma not_isField_of_openImmersion
    {K : Type u} [Field K] {R : Subring K} {ι : Type v} [Nonempty ι]
    (B : ι → Subring K) (f : ∀ i, R →+* B i) (i : ι)
    (h_dim : ringKrullDim (B i) = 1)
    (h_open : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (f i)))) : ¬ IsField R := by
  intro hR
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (B i)
  have hMne : M ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hM (not_isField_of_ringKrullDim_eq_one h_dim)
  let g := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (f i))
  have : AlgebraicGeometry.IsOpenImmersion g := h_open
  let p0 : AlgebraicGeometry.Spec (CommRingCat.of (B i)) := ⟨⊥, Ideal.isPrime_bot⟩
  let p1 : AlgebraicGeometry.Spec (CommRingCat.of (B i)) := ⟨M, hM.isPrime⟩
  have hpne : p0 ≠ p1 := by
    intro h
    apply hMne
    have h' : (⊥ : PrimeSpectrum (B i)) = ⟨M, hM.isPrime⟩ := h
    exact (congrArg PrimeSpectrum.asIdeal h').symm
  let _ : Field R := hR.toField
  have : Unique (PrimeSpectrum R) := inferInstance
  have heq : g p0 = g p1 := Subsingleton.elim _ _
  exact hpne ((AlgebraicGeometry.Scheme.Hom.isOpenEmbedding g).injective heq)

private lemma ringKrullDim_one_of_openCover
    {K : Type u} [Field K] {R : Subring K} {ι : Type v} [Finite ι] [Nonempty ι]
    (B : ι → Subring K) (f : ∀ i, R →+* B i)
    (hf : ∀ i, Function.Injective (f i)) (h_dim : ∀ i, ringKrullDim (B i) = 1)
    (h_open : ∀ i, AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (f i))))
    (h_cover : (⋃ i, Set.range (PrimeSpectrum.comap (f i))) = Set.univ) :
    ringKrullDim R = 1 := by
  have i : ι := Classical.choice ‹Nonempty ι›
  have hnotfield : ¬ IsField R := not_isField_of_openImmersion B f i (h_dim i) (h_open i)
  have hnotle : ¬ ringKrullDim R ≤ 0 := fun hle => by
    have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hle
    exact hnotfield Ring.KrullDimLE.isField_of_isDomain
  exact le_antisymm (Ring.krullDimLE_iff.mp (krullDimLE_one_of_openCover B f hf h_dim h_open
    h_cover)) (Order.succ_le_of_lt (lt_of_not_ge hnotle))

private lemma localRingHom_bijective_of_openImmersion
    {A P : Type u} [CommRing A] [CommRing P] (I : Ideal A)
    [hI : I.IsPrime] (f : A →+* P) (q : PrimeSpectrum P)
    (hIq : I = q.asIdeal.comap f)
    (h_open : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))) :
    Function.Bijective
      (Localization.localRingHom I q.asIdeal f hIq) := by
  let p : PrimeSpectrum A := q.comap f
  let _ : p.asIdeal.IsPrime := p.isPrime
  let g : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal f rfl
  have hStalkIso : CategoryTheory.IsIso
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)).stalkMap q) :=
    (AlgebraicGeometry.IsOpenImmersion.iff_isIso_stalkMap.mp h_open).2 q
  let eR := (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of A) p).hom
  let eP := (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of P) q).inv
  have hfactor : eR ≫ (CommRingCat.ofHom g ≫ eP) =
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)).stalkMap q := by
    simpa [p, g, Category.assoc] using
      AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom f) q
  have : CategoryTheory.IsIso eR := inferInstance
  have : CategoryTheory.IsIso eP := inferInstance
  have : CategoryTheory.IsIso (eR ≫ (CommRingCat.ofHom g ≫ eP)) := by
    rw [hfactor]
    exact hStalkIso
  have : CategoryTheory.IsIso (CommRingCat.ofHom g ≫ eP) :=
    CategoryTheory.IsIso.of_isIso_comp_left eR (CommRingCat.ofHom g ≫ eP)
  have : CategoryTheory.IsIso (CommRingCat.ofHom g) :=
    CategoryTheory.IsIso.of_isIso_comp_right (CommRingCat.ofHom g) eP
  have hbij : Function.Bijective g :=
    ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom g)
  have hIp : I = p.asIdeal.comap (RingEquiv.refl A).toRingHom := by
    have hIp' : I = p.asIdeal := hIq
    rw [hIp']
    ext x
    simp
  let e : Localization.AtPrime I ≃+* Localization.AtPrime p.asIdeal :=
    Localization.localRingEquiv I p.asIdeal (RingEquiv.refl A) hIp
  have hmap : Localization.localRingHom I q.asIdeal f hIq = g.comp e.toRingHom := by
    apply Localization.localRingHom_unique
    intro a
    have he : e.toRingHom (algebraMap A (Localization.AtPrime I) a) =
        algebraMap A (Localization.AtPrime p.asIdeal) a := by
      change e (algebraMap A (Localization.AtPrime I) a) = _
      simp [e, Localization.localRingEquiv, Localization.localRingHom_to_map]
    rw [RingHom.comp_apply, he]
    exact Localization.localRingHom_to_map p.asIdeal q.asIdeal f rfl a
  rw [hmap]
  exact hbij.comp e.bijective

private lemma isFractionRing_atPrime_of_eq_bot {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) [P.IsPrime] (h : P = ⊥) : IsFractionRing R (Localization.AtPrime P) := by
  subst h
  simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal R).primeCompl)

private lemma isFractionRing_of_openImmersion_specMap
    {K : Type u} [Field K] (A B : Subring K) (hAB : A ≤ B)
    [IsFractionRing B K]
    (h_open : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Subring.inclusion hAB)))) :
    IsFractionRing A K := by
  classical
  let fRing := Subring.inclusion hAB
  let _ : IsDomain A := inferInstance
  let _ : IsDomain B := inferInstance
  let _ : Algebra A B := fRing.toAlgebra
  let _ : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let f := AlgebraicGeometry.Spec.map (CommRingCat.ofHom fRing)
  let pB : PrimeSpectrum B := ⊥
  let pA : PrimeSpectrum A := pB.comap fRing
  let _ : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  let _ : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
  have hbotA : pA.asIdeal = ⊥ := by
    change Ideal.comap fRing (⊥ : Ideal B) = ⊥
    exact Ideal.comap_bot_of_injective fRing (Subring.inclusion_injective _)
  let g : Localization.AtPrime pA.asIdeal →+*
      Localization.AtPrime (⊥ : Ideal B) :=
    Localization.localRingHom pA.asIdeal (⊥ : Ideal B) fRing rfl
  have hg : Function.Bijective g :=
    localRingHom_bijective_of_openImmersion pA.asIdeal fRing pB rfl h_open
  have : IsFractionRing A (Localization.AtPrime pA.asIdeal) :=
    isFractionRing_atPrime_of_eq_bot _ hbotA
  have : IsFractionRing B (Localization.AtPrime (⊥ : Ideal B)) :=
    isFractionRing_atPrime_of_eq_bot _ rfl
  let _ : Algebra A (Localization.AtPrime (⊥ : Ideal B)) :=
    ((algebraMap B (Localization.AtPrime (⊥ : Ideal B))).comp fRing).toAlgebra
  let gAlg : Localization.AtPrime pA.asIdeal →ₐ[A]
      Localization.AtPrime (⊥ : Ideal B) :=
    { toRingHom := g
      commutes' := by
        intro a
        change g (algebraMap A (Localization.AtPrime pA.asIdeal) a) =
          algebraMap B (Localization.AtPrime (⊥ : Ideal B)) (fRing a)
        simpa [g] using
          (Localization.localRingHom_to_map pA.asIdeal (⊥ : Ideal B) fRing rfl a) }
  let eAB := AlgEquiv.ofBijective gAlg hg
  let eBK : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[B] K :=
    IsLocalization.algEquiv (nonZeroDivisors B)
      (Localization.AtPrime (⊥ : Ideal B)) K
  let eBKAlg : Localization.AtPrime (⊥ : Ideal B) →ₐ[A] K :=
    { toRingHom := eBK.toRingEquiv.toRingHom
      commutes' := by
        intro a
        change eBK (algebraMap B (Localization.AtPrime (⊥ : Ideal B)) (fRing a)) =
          algebraMap A K a
        rw [eBK.commutes, IsScalarTower.algebraMap_apply A B K a]
        rfl }
  let eBK' : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[A] K :=
    AlgEquiv.ofBijective eBKAlg eBK.bijective
  exact IsFractionRing.of_algEquiv (eAB.trans eBK')

private lemma schemeSpecMap_eq_specMap {R S : CommRingCat} (f : R ⟶ S) :
    AlgebraicGeometry.Scheme.Spec.map f.op = AlgebraicGeometry.Spec.map f := by
  rw [AlgebraicGeometry.Scheme.Spec_map]
  simp

private lemma finite_maximalSpectrum_of_cover
    {K : Type u} [Field K] {R : Subring K} {ι : Type v} [Finite ι] [Nonempty ι]
    (B : ι → Subring K) (f : ∀ i, R →+* B i)
    (hf : ∀ i, Function.Injective (f i)) (h_dim : ∀ i, ringKrullDim (B i) = 1)
    (h_cover : (⋃ i, Set.range (PrimeSpectrum.comap (f i))) = Set.univ)
    (h_dimR : ringKrullDim R = 1) [∀ i, Finite (MaximalSpectrum (B i))] :
    Finite (MaximalSpectrum R) := by
  classical
  let S := {q : Σ i, MaximalSpectrum (B i) |
    (PrimeSpectrum.comap (f q.1) q.2.toPrimeSpectrum).asIdeal.IsMaximal}
  let g : S → MaximalSpectrum R := fun q =>
    ⟨PrimeSpectrum.comap (f q.1.1) q.1.2.toPrimeSpectrum, q.2⟩
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp h_cover x.toPrimeSpectrum)
    obtain ⟨q, hq⟩ := Set.mem_range.mp hi
    have hqcomap : q.asIdeal.comap (f i) = x.asIdeal := comap_asIdeal_of_comap_eq hq
    have hMmax : (q.asIdeal.comap (f i)).IsMaximal := by
      rw [hqcomap]
      exact x.isMaximal
    exact ⟨⟨⟨i, ⟨q.asIdeal, isMaximal_of_comap_isMaximal (hf i) h_dimR (h_dim i) q hMmax⟩⟩,
      hMmax⟩, MaximalSpectrum.ext hqcomap⟩
  exact Finite.of_surjective g hg

private def finiteIntersection {K : Type u} [CommRing K] {ι : Type v}
    (B : ι → Subring K) (s : Finset ι) : Subring K :=
  s.inf B

private lemma mem_finiteIntersection {K : Type u} [CommRing K] {ι : Type v}
    (B : ι → Subring K) (s : Finset ι) (x : K) :
    x ∈ finiteIntersection B s ↔ ∀ i ∈ s, x ∈ B i := by
  simp [finiteIntersection, Finset.inf_eq_iInf]

private def finiteIntersectionInclusion {K : Type u} [CommRing K] {ι : Type v}
    (B : ι → Subring K) (s : Finset ι) (i : {j // j ∈ s}) :
    finiteIntersection B s →+* B i.1 :=
  Subring.inclusion (fun x hx => (mem_finiteIntersection B s x).mp hx i.1 i.2)

private lemma isOpenImmersion_specMap_of_bijective
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) :
    AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) := by
  let e := RingEquiv.ofBijective f hf
  let eCat := RingEquiv.toCommRingCatIso e
  have hcat : CommRingCat.ofHom f = eCat.hom := by
    ext x
    change f x = e x
    exact (RingEquiv.ofBijective_apply f hf x).symm
  have : CategoryTheory.IsIso (CommRingCat.ofHom f) := by
    rw [hcat]
    infer_instance
  have : CategoryTheory.IsIso (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) := inferInstance
  exact AlgebraicGeometry.IsOpenImmersion.of_isIso _

private lemma isOpenImmersion_specMap_comp {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C)
    (hf : AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)))
    (hg : AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom g))) :
    AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (g.comp f))) := by
  rw [CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp]
  infer_instance

private lemma isOpenImmersion_of_eq_comp_bijective {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (e : A →+* B) (he : Function.Bijective e) (φ : B →+* C) (ψ : A →+* C)
    (hψ : ψ = φ.comp e)
    (hφ : AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))) :
    AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ)) := by
  rw [hψ]
  exact isOpenImmersion_specMap_comp e φ (isOpenImmersion_specMap_of_bijective e he) hφ

private lemma comap_eq_of_eq_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (e : A →+* B) (e' : B →+* A) (he : e'.comp e = RingHom.id A) (φ : B →+* C) (ψ : A →+* C)
    (hψ : ψ = φ.comp e) {p : PrimeSpectrum A} {q : PrimeSpectrum C}
    (hq : PrimeSpectrum.comap φ q = PrimeSpectrum.comap e' p) :
    PrimeSpectrum.comap ψ q = p := by
  rw [hψ, PrimeSpectrum.comap_comp_apply, hq, ← PrimeSpectrum.comap_comp_apply, he,
    PrimeSpectrum.comap_id]

private lemma inclusion_bijective_of_eq {K : Type u} [CommRing K] {S T : Subring K}
    (h : S = T) : Function.Bijective (Subring.inclusion h.le) := by
  subst h
  exact ⟨Subring.inclusion_injective _, fun y => ⟨y, rfl⟩⟩

private lemma comap_inclusion_comap_inclusion {K : Type u} [CommRing K] {S T : Subring K}
    (h₁ : S ≤ T) (h₂ : T ≤ S) (p : PrimeSpectrum S) :
    PrimeSpectrum.comap (Subring.inclusion h₁)
      (PrimeSpectrum.comap (Subring.inclusion h₂) p) = p := by
  have h : (Subring.inclusion h₂).comp (Subring.inclusion h₁) = RingHom.id S := by
    ext
    rfl
  rw [← PrimeSpectrum.comap_comp_apply, h, PrimeSpectrum.comap_id]

section Pair

variable {K : Type u} [Field K] (A C : Subring K)
  [IsFractionRing A K] [IsFractionRing C K] [IsNoetherianRing A] [IsNoetherianRing C]
  [Finite (MaximalSpectrum A)] [Finite (MaximalSpectrum C)]
  (hA : ringKrullDim A = 1) (hC : ringKrullDim C = 1)
  (hsurj : Function.Surjective
    (Algebra.TensorProduct.lift (B := C) A.subtype.toIntAlgHom
      C.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)))

include hA hC hsurj

private lemma isOpenImmersion_specMap_inclusion_inf_left :
    AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Subring.inclusion (inf_le_left : A ⊓ C ≤ A)))) := by
  rw [← schemeSpecMap_eq_specMap]
  exact isOpenImmersion_specMap_inf_left A C hA hC hsurj

private lemma isOpenImmersion_specMap_inclusion_inf_right :
    AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Subring.inclusion (inf_le_right : A ⊓ C ≤ C)))) := by
  rw [← schemeSpecMap_eq_specMap]
  exact isOpenImmersion_specMap_inf_right A C hA hC hsurj

private lemma range_comap_inclusion_inf_left_union_right :
    Set.range (PrimeSpectrum.comap (Subring.inclusion (inf_le_left : A ⊓ C ≤ A))) ∪
      Set.range (PrimeSpectrum.comap (Subring.inclusion (inf_le_right : A ⊓ C ≤ C))) =
        Set.univ := by
  have h := range_specMap_inf_left_union_right A C hA hC hsurj
  simp only [schemeSpecMap_eq_specMap] at h
  exact h

private lemma inf_isFractionRing_isNoetherianRing_finite_ringKrullDim :
    IsFractionRing (A ⊓ C : Subring K) K ∧ IsNoetherianRing (A ⊓ C : Subring K) ∧
      Finite (MaximalSpectrum (A ⊓ C : Subring K)) ∧ ringKrullDim (A ⊓ C : Subring K) = 1 := by
  have hl := isOpenImmersion_specMap_inclusion_inf_left A C hA hC hsurj
  have hr := isOpenImmersion_specMap_inclusion_inf_right A C hA hC hsurj
  have hcov := range_comap_inclusion_inf_left_union_right A C hA hC hsurj
  let E : Bool → Subring K := fun b => match b with
    | false => C
    | true => A
  let f : ∀ b : Bool, (A ⊓ C : Subring K) →+* E b := fun b => match b with
    | false => Subring.inclusion (inf_le_right : (A ⊓ C : Subring K) ≤ C)
    | true => Subring.inclusion (inf_le_left : (A ⊓ C : Subring K) ≤ A)
  have hf : ∀ b, Function.Injective (f b) := by
    intro b
    cases b <;> change Function.Injective (Subring.inclusion _) <;>
      exact Subring.inclusion_injective _
  have hOpenE : ∀ b, AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (f b))) := by
    rintro (_ | _)
    exacts [hr, hl]
  have hcoverE : (⋃ b, Set.range (PrimeSpectrum.comap (f b))) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun p => ?_
    rcases Set.eq_univ_iff_forall.mp hcov p with hp | hp
    · exact Set.mem_iUnion.mpr ⟨true, by simpa [f] using hp⟩
    · exact Set.mem_iUnion.mpr ⟨false, by simpa [f] using hp⟩
  have hdimE : ∀ b, ringKrullDim (E b) = 1 := by
    rintro (_ | _)
    exacts [hC, hA]
  have : ∀ b, IsNoetherianRing (E b) := by
    rintro (_ | _)
    exacts [‹IsNoetherianRing C›, ‹IsNoetherianRing A›]
  have : ∀ b, Finite (MaximalSpectrum (E b)) := by
    rintro (_ | _)
    exacts [‹Finite (MaximalSpectrum C)›, ‹Finite (MaximalSpectrum A)›]
  have hdim := ringKrullDim_one_of_openCover (R := A ⊓ C) E f hf hdimE hOpenE hcoverE
  exact ⟨isFractionRing_of_openImmersion_specMap (A ⊓ C) C inf_le_right hr,
    isNoetherian_of_openCover (A ⊓ C) E f hOpenE hcoverE,
    finite_maximalSpectrum_of_cover (R := A ⊓ C) E f hf hdimE hcoverE hdim, hdim⟩

end Pair

private lemma exists_localization_atPrime_embedding {K : Type u} [Field K] (A : Subring K)
    [IsFractionRing A K] (q : Ideal A) [q.IsPrime] :
    ∃ k : Localization.AtPrime q →+* K, Function.Injective k ∧
      ∀ a : A, k (algebraMap A (Localization.AtPrime q) a) = a := by
  let k : Localization.AtPrime q →+* K := IsLocalization.map K (RingHom.id A) (by
    intro z hz
    simpa only [Submonoid.mem_comap, MonoidHom.id_apply, RingHom.id_apply] using
      (q.primeCompl_le_nonZeroDivisors hz))
  have hk : ∀ a : A, k (algebraMap A (Localization.AtPrime q) a) = a := fun a => by
    simp [k, IsLocalization.map_eq, Algebra.algebraMap_ofSubring]
  refine ⟨k, ?_, hk⟩
  apply IsLocalization.injective_of_map_algebraMap_zero (S := Localization.AtPrime q)
    (M := q.primeCompl) k
  intro r hr
  have hr0 : r = 0 := Subtype.ext (by simpa [hk] using hr)
  simp [hr0]

private lemma false_of_inverse_mem_of_localRingHom_surjective {K : Type u} [Field K]
    {R A C : Subring K} [IsFractionRing R K] [IsFractionRing A K] [IsFractionRing C K]
    (hRA : R ≤ A) (hRC : R ≤ C) {m : Ideal R} [m.IsPrime] {qi : Ideal A} [qi.IsPrime]
    {qj : Ideal C} [qj.IsPrime]
    (gi : Localization.AtPrime m →+* Localization.AtPrime qi)
    (gj : Localization.AtPrime m →+* Localization.AtPrime qj) (hgi : Function.Surjective gi)
    (hgi' : ∀ r, gi (algebraMap R _ r) = algebraMap A _ (Subring.inclusion hRA r))
    (hgj' : ∀ r, gj (algebraMap R _ r) = algebraMap C _ (Subring.inclusion hRC r))
    {a : A} (ha0 : a ≠ 0) {b : C} (hba : (b : K) = (a : K)⁻¹) (hb : b ∈ qj) : False := by
  obtain ⟨kR, -, hkR⟩ := exists_localization_atPrime_embedding R m
  obtain ⟨ki, -, hki⟩ := exists_localization_atPrime_embedding A qi
  obtain ⟨kj, hkjinj, hkj⟩ := exists_localization_atPrime_embedding C qj
  have hi : ki.comp gi = kR := IsLocalization.ringHom_ext m.primeCompl <| RingHom.ext fun r =>
    (congrArg ki (hgi' r)).trans ((hki _).trans (hkR r).symm)
  have hj : kj.comp gj = kR := IsLocalization.ringHom_ext m.primeCompl <| RingHom.ext fun r =>
    (congrArg kj (hgj' r)).trans ((hkj _).trans (hkR r).symm)
  obtain ⟨x, hx⟩ := hgi (algebraMap A _ a)
  have hxa : kj (gj x) = a := by
    rw [← RingHom.comp_apply kj gj, hj, ← hi, RingHom.comp_apply, hx, hki]
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha0
  have hprod : gj x * algebraMap C _ b = 1 := hkjinj (by
    rw [map_mul, hxa, hkj, hba, map_one, mul_inv_cancel₀ haK])
  have hbmax : algebraMap C (Localization.AtPrime qj) b ∈ IsLocalRing.maximalIdeal _ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal qj]
    exact Ideal.mem_map_of_mem _ hb
  have hbnotunit : ¬ IsUnit (algebraMap C (Localization.AtPrime qj) b) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using hbmax
  exact hbnotunit (isUnit_iff_exists_inv.mpr ⟨gj x, by simpa [mul_comm] using hprod⟩)

private structure finiteIntersectionData {K : Type u} [Field K] {ι : Type v}
    (B : ι → Subring K) (s : Finset ι) : Prop where
  fraction : IsFractionRing (finiteIntersection B s) K
  noetherian : IsNoetherianRing (finiteIntersection B s)
  semilocal : Finite (MaximalSpectrum (finiteIntersection B s))
  dimension : ringKrullDim (finiteIntersection B s) = 1
  openImmersion : ∀ i : {j // j ∈ s}, AlgebraicGeometry.IsOpenImmersion
    (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (finiteIntersectionInclusion B s i)))
  cover : (⋃ i : {j // j ∈ s}, Set.range
      (PrimeSpectrum.comap (finiteIntersectionInclusion B s i))) = Set.univ

variable {K : Type u} [Field K] {ι : Type v} [Finite ι] [Nonempty ι]
  (B : ι → Subring K)
  [∀ i, IsFractionRing (B i) K]
  [∀ i, IsNoetherianRing (B i)]
  [∀ i, Finite (MaximalSpectrum (B i))]
  (h_dim : ∀ i, ringKrullDim (B i) = 1)
  (h_surj : ∀ i j, i ≠ j → Function.Surjective
    (Algebra.TensorProduct.lift (B := B j) (B i).subtype.toIntAlgHom
      (B j).subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)))

include h_dim h_surj

omit [Nonempty ι] in
private lemma surjective_tensorProduct_lift_finiteIntersection {j : ι} {s : Finset ι}
    (hj : j ∉ s) (hs : s.Nonempty) (d : finiteIntersectionData B s) :
    Function.Surjective
      (Algebra.TensorProduct.lift (B := finiteIntersection B s) (B j).subtype.toIntAlgHom
        (finiteIntersection B s).subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  let C := finiteIntersection B s
  let _ : Nonempty {i // i ∈ s} := ⟨⟨Classical.choose hs, Classical.choose_spec hs⟩⟩
  let _ : IsFractionRing C K := d.fraction
  obtain ⟨x, hx, hys⟩ :=
    Ring.exists_ne_zero_inverse_mem_jacobson_of_tensorProduct_surjective
      (B j) (fun i : {i // i ∈ s} => B i.1) (fun i => h_dim i.1)
      (fun i => h_surj j i.1 fun h => hj (h ▸ i.2))
  let y : C := ⟨(x : K)⁻¹, (mem_finiteIntersection B s _).2 (by
    intro i hi
    obtain ⟨yi, hyi, _⟩ := hys ⟨i, hi⟩
    rw [← hyi]
    exact yi.2)⟩
  have hyjac : y ∈ Ideal.jacobson (⊥ : Ideal C) := by
    refine mem_jacobson_of_openCover C (fun i : {i // i ∈ s} => B i.1)
      (finiteIntersectionInclusion B s) (fun _ => Subring.inclusion_injective _)
      (fun i => h_dim i.1) d.cover d.dimension fun i => ?_
    obtain ⟨yi, hyi, hyijac⟩ := hys i
    have hyieq : finiteIntersectionInclusion B s i y = yi := Subtype.ext hyi.symm
    rw [hyieq]
    exact hyijac
  exact tensorProduct_lift_surjective_of_jacobson_inverse (B j) C x hx y rfl hyjac d.dimension

omit [Nonempty ι] in
private lemma finiteIntersectionData_insert [DecidableEq ι] {j : ι} {s : Finset ι}
    (hj : j ∉ s) (hs : s.Nonempty) (d : finiteIntersectionData B s) :
    finiteIntersectionData B (insert j s) := by
  let C := finiteIntersection B s
  let _ : IsFractionRing C K := d.fraction
  let _ : IsNoetherianRing C := d.noetherian
  let _ : Finite (MaximalSpectrum C) := d.semilocal
  have hsurj := surjective_tensorProduct_lift_finiteIntersection B h_dim h_surj hj hs d
  obtain ⟨hFrac, hNoeth, hsemi, hdim⟩ :=
    inf_isFractionRing_isNoetherianRing_finite_ringKrullDim (B j) C (h_dim j) d.dimension hsurj
  have hl := isOpenImmersion_specMap_inclusion_inf_left (B j) C (h_dim j) d.dimension hsurj
  have hr := isOpenImmersion_specMap_inclusion_inf_right (B j) C (h_dim j) d.dimension hsurj
  have hcov := range_comap_inclusion_inf_left_union_right (B j) C (h_dim j) d.dimension hsurj
  have hIns : finiteIntersection B (insert j s) = B j ⊓ C := by
    simp [finiteIntersection, C, Finset.inf_insert]
  have hbij := inclusion_bijective_of_eq hIns
  have he : (Subring.inclusion hIns.ge).comp (Subring.inclusion hIns.le) = RingHom.id _ := by
    ext
    rfl
  refine ⟨?_, ?_, ?_, ?_, fun ⟨k, hk⟩ => ?_, Set.eq_univ_iff_forall.mpr fun p => ?_⟩
  · rwa [hIns]
  · rwa [hIns]
  · rwa [hIns]
  · rwa [hIns]
  · rcases Finset.mem_insert.mp hk with rfl | hks
    · exact isOpenImmersion_of_eq_comp_bijective _ hbij _ _ (by ext; rfl) hl
    · exact isOpenImmersion_of_eq_comp_bijective _ hbij _ _ (by ext; rfl)
        (isOpenImmersion_specMap_comp _ _ hr (d.openImmersion ⟨k, hks⟩))
  · rcases Set.eq_univ_iff_forall.mp hcov (PrimeSpectrum.comap (Subring.inclusion hIns.ge) p)
      with ⟨q, hq⟩ | ⟨qC, hqC⟩
    · exact Set.mem_iUnion.mpr ⟨⟨j, Finset.mem_insert_self j s⟩, q,
        comap_eq_of_eq_comp _ _ he _ _ (by ext; rfl) hq⟩
    · obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp d.cover qC)
      refine Set.mem_iUnion.mpr ⟨⟨i.1, Finset.mem_insert_of_mem i.2⟩, q,
        comap_eq_of_eq_comp _ _ he
          ((finiteIntersectionInclusion B s i).comp (Subring.inclusion inf_le_right)) _
          (by ext; rfl) ?_⟩
      rw [PrimeSpectrum.comap_comp_apply, hq, hqC]

omit [Finite ι] [Nonempty ι] h_surj in
private lemma finiteIntersectionData_singleton [DecidableEq ι] (j : ι) :
    finiteIntersectionData B (insert j ∅) := by
  have hEq : finiteIntersection B (insert j ∅) = B j := by
    simp [finiteIntersection]
  refine ⟨?_, ?_, ?_, ?_, fun ⟨i, hi⟩ => ?_, Set.eq_univ_iff_forall.mpr fun p => ?_⟩
  · rw [hEq]; infer_instance
  · rw [hEq]; infer_instance
  · rw [hEq]; infer_instance
  · rw [hEq]; exact h_dim j
  · obtain rfl : i = j := by simpa using hi
    exact isOpenImmersion_specMap_of_bijective _ (inclusion_bijective_of_eq hEq)
  · exact Set.mem_iUnion.mpr ⟨⟨j, by simp⟩, PrimeSpectrum.comap (Subring.inclusion hEq.ge) p,
      comap_inclusion_comap_inclusion hEq.le hEq.ge p⟩

omit [Nonempty ι] in
private lemma finiteIntersectionData_of_nonempty
    : ∀ s : Finset ι, s.Nonempty → finiteIntersectionData B s := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    simp at hs
  | @insert j s hj ih =>
    intro hs
    by_cases hsne : s.Nonempty
    · exact finiteIntersectionData_insert B h_dim h_surj hj hsne (ih hsne)
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hsne
      exact finiteIntersectionData_singleton B h_dim j

private lemma finiteIntersectionData_univ [Fintype ι] :
    finiteIntersectionData B Finset.univ :=
  finiteIntersectionData_of_nonempty B h_dim h_surj _ Finset.univ_nonempty

omit [Finite ι] [Nonempty ι] [∀ i, IsFractionRing (B i) K] [∀ i, IsNoetherianRing (B i)]
  [∀ i, Finite (MaximalSpectrum (B i))] h_dim h_surj in
private lemma gluedSubring_eq_finiteIntersection_univ [Fintype ι] :
    gluedSubring B = finiteIntersection B Finset.univ := by
  classical
  ext x
  simp [gluedSubring, finiteIntersection, Finset.inf_eq_iInf]

omit [Finite ι] [Nonempty ι] [∀ i, IsFractionRing (B i) K] [∀ i, IsNoetherianRing (B i)]
  [∀ i, Finite (MaximalSpectrum (B i))] h_dim h_surj in
private lemma gluedSubring_univ_inclusion_bijective [Fintype ι] :
    Function.Bijective
      (Subring.inclusion (le_of_eq
        (gluedSubring_eq_finiteIntersection_univ B))) :=
  inclusion_bijective_of_eq (gluedSubring_eq_finiteIntersection_univ B)

/-- The intersection is Noetherian. -/
@[stacks 09N4 "the Noetherian assertion"]
lemma isNoetherianRing_gluedSubring : IsNoetherianRing (gluedSubring B) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [gluedSubring_eq_finiteIntersection_univ B]
  exact (finiteIntersectionData_univ B h_dim h_surj).noetherian

/-- The intersection is semilocal. -/
@[stacks 09N4 "the semilocal assertion"]
lemma finite_maximalSpectrum_gluedSubring : Finite (MaximalSpectrum (gluedSubring B)) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [gluedSubring_eq_finiteIntersection_univ B]
  exact (finiteIntersectionData_univ B h_dim h_surj).semilocal

/-- The intersection has Krull dimension one. -/
@[stacks 09N4 "the dimension assertion"]
lemma ringKrullDim_gluedSubring : ringKrullDim (gluedSubring B) = 1 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [gluedSubring_eq_finiteIntersection_univ B]
  exact (finiteIntersectionData_univ B h_dim h_surj).dimension

/-- The map on affine spectra induced by inclusion of the intersection into each member is an
open immersion. -/
@[stacks 09N4 "part (1)"]
lemma isOpenImmersion_specMap_gluedSubringInclusion (i : ι) :
    AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (gluedSubringInclusion B i))) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  exact isOpenImmersion_of_eq_comp_bijective _ (gluedSubring_univ_inclusion_bijective B) _ _
    (by ext; rfl) ((finiteIntersectionData_univ B h_dim h_surj).openImmersion
      ⟨i, Finset.mem_univ i⟩)

/-- The images of the spectra of the members cover the spectrum of the intersection. -/
@[stacks 09N4 "part (2)"]
lemma iUnion_range_comap_gluedSubringInclusion :
    (⋃ i, Set.range (PrimeSpectrum.comap (gluedSubringInclusion B i))) = Set.univ := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have d := finiteIntersectionData_univ B h_dim h_surj
  have hEq := gluedSubring_eq_finiteIntersection_univ B
  have he : (Subring.inclusion hEq.ge).comp (Subring.inclusion (le_of_eq hEq)) =
      RingHom.id (gluedSubring B) := by
    ext
    rfl
  refine Set.eq_univ_iff_forall.mpr fun p => ?_
  obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp
    (Set.eq_univ_iff_forall.mp d.cover (PrimeSpectrum.comap (Subring.inclusion hEq.ge) p))
  exact Set.mem_iUnion.mpr ⟨i.1, q, comap_eq_of_eq_comp _ _ he _ _ (by ext; rfl) hq⟩

/-- Every closed point of the spectrum of the intersection is in the image of exactly one
member of the family. -/
@[stacks 09N4 "part (3)"]
lemma existsUnique_range_comap_gluedSubringInclusion
    (x : MaximalSpectrum (gluedSubring B)) :
    ∃! i, x.toPrimeSpectrum ∈ Set.range
      (PrimeSpectrum.comap (gluedSubringInclusion B i)) := by
  classical
  let R := gluedSubring B
  let m : Ideal R := x.toPrimeSpectrum.asIdeal
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp
    (iUnion_range_comap_gluedSubringInclusion B h_dim h_surj) x.toPrimeSpectrum)
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hij
  let fi := gluedSubringInclusion B i
  let fj := gluedSubringInclusion B j
  obtain ⟨qi, hqi⟩ := Set.mem_range.mp hi
  obtain ⟨qj, hqj⟩ := Set.mem_range.mp hj
  have hqiComap : qi.asIdeal.comap fi = m := comap_asIdeal_of_comap_eq hqi
  have hqjComap : qj.asIdeal.comap fj = m := comap_asIdeal_of_comap_eq hqj
  let _ : m.IsPrime := x.toPrimeSpectrum.isPrime
  obtain ⟨a, ha0, ha⟩ :=
    Ring.exists_ne_zero_inverse_mem_jacobson_of_tensorProduct_surjective
      (B i) (fun _ : Unit => B j) (fun _ => h_dim j) (fun _ => h_surj i j (Ne.symm hij))
  obtain ⟨b, hba, hbRad⟩ := ha ()
  have hqjmax : qj.asIdeal.IsMaximal :=
    isMaximal_of_comap_isMaximal (Subring.inclusion_injective _)
      (ringKrullDim_gluedSubring B h_dim h_surj) (h_dim j) qj
      (by rw [hqjComap]; exact x.isMaximal)
  have : IsFractionRing R K := isFractionRing_of_openImmersion_specMap (gluedSubring B)
    (B i) (iInf_le B i) (isOpenImmersion_specMap_gluedSubringInclusion B h_dim h_surj i)
  exact false_of_inverse_mem_of_localRingHom_surjective (iInf_le B i) (iInf_le B j)
    (Localization.localRingHom m qi.asIdeal fi hqiComap.symm)
    (Localization.localRingHom m qj.asIdeal fj hqjComap.symm)
    (localRingHom_bijective_of_openImmersion m fi qi hqiComap.symm
      (isOpenImmersion_specMap_gluedSubringInclusion B h_dim h_surj i)).2
    (Localization.localRingHom_to_map m qi.asIdeal fi hqiComap.symm)
    (Localization.localRingHom_to_map m qj.asIdeal fj hqjComap.symm)
    ha0 hba (mem_of_mem_jacobson_bot hbRad hqjmax)

end Subring
