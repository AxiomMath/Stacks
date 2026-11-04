module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# A finite unramified morphism with a single purely inseparable point

A finite unramified morphism whose fibre over a point of the target consists of a single point,
and whose induced residue-field extension there is purely inseparable, is a closed immersion over
an open neighbourhood of that point.

## Main results

* `exists_open_restrict_isClosedImmersion_of_finite_unramified_fiber_eq_singleton`
  gives the neighbourhood on which the morphism is a closed immersion.

## Implementation notes

The restriction over an open neighbourhood is `Scheme.Hom.restrict`. The algebra structure on the
residue field at the unique point of the fibre is induced by the morphism's canonical
residue-field map, transported along the equality of its image with the given base point.

Unramifiedness makes the residue-field extension separable, so purely inseparable forces it to be
an isomorphism; hence the local homomorphism on stalks is surjective. Since the fibre is a single
prime, surjectivity spreads from the local ring to a localization away from one element, which
cuts out the required affine neighbourhood.

## References

* [Stacks Project, Tag 04DG](https://stacks.math.columbia.edu/tag/04DG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

private lemma residueFieldMap_surjective_of_pure
    {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f]
    (s : S) (x : X) (hxs : f x = s)
    (hpure :
      letI := ((S.residueFieldCongr hxs).inv ≫ f.residueFieldMap x).hom.toAlgebra
      IsPurelyInseparable (S.residueField s) (X.residueField x)) :
    Function.Surjective
      (((S.residueFieldCongr hxs).inv ≫ f.residueFieldMap x).hom) := by
  subst s
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    ((S.residueFieldCongr rfl).inv ≫ f.residueFieldMap x).hom.toAlgebra
  have hpi : IsPurelyInseparable (S.residueField (f x)) (X.residueField x) := hpure
  have hsep : Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) :=
    isSeparable_residueField_of_unramified f x
  exact IsPurelyInseparable.surjective_algebraMap_of_isSeparable _ _

private lemma residueFieldMap_surjective_of_commutes
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C] [IsLocalRing D]
    (f : A →+* B) (g : C →+* D) [IsLocalHom f] [IsLocalHom g]
    (e₁ : A ≃+* C) (e₂ : B ≃+* D)
    (h : g.comp e₁.toRingHom = e₂.toRingHom.comp f)
    (hf : Function.Surjective (IsLocalRing.ResidueField.map f)) :
    Function.Surjective (IsLocalRing.ResidueField.map g) := by
  let : IsLocalHom e₁.toRingHom := e₁.surjective.isLocalHom
  let : IsLocalHom e₂.toRingHom := e₂.surjective.isLocalHom
  let k₁ := IsLocalRing.ResidueField.mapEquiv e₁
  let k₂ := IsLocalRing.ResidueField.mapEquiv e₂
  have hk : (IsLocalRing.ResidueField.map g).comp
        (IsLocalRing.ResidueField.map e₁.toRingHom) =
      (IsLocalRing.ResidueField.map e₂.toRingHom).comp
        (IsLocalRing.ResidueField.map f) := by
    have heq : (⟨g.comp e₁.toRingHom, inferInstance⟩ :
        {k : A →+* D // IsLocalHom k}) = ⟨e₂.toRingHom.comp f, inferInstance⟩ :=
      Subtype.ext h
    let F : {k : A →+* D // IsLocalHom k} →
        IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField D := fun k ↦ by
      let : IsLocalHom k.val := k.property
      exact IsLocalRing.ResidueField.map k.val
    calc
      _ = IsLocalRing.ResidueField.map (g.comp e₁.toRingHom) :=
        (IsLocalRing.ResidueField.map_comp _ _).symm
      _ = IsLocalRing.ResidueField.map (e₂.toRingHom.comp f) := congrArg F heq
      _ = _ := IsLocalRing.ResidueField.map_comp _ _
  intro z
  obtain ⟨z', rfl⟩ := k₂.surjective z
  obtain ⟨x, hx⟩ := hf z'
  refine ⟨k₁ x, ?_⟩
  simpa [k₁, k₂, IsLocalRing.ResidueField.mapEquiv_apply, hx] using DFunLike.congr_fun hk x

private lemma exists_awayMap_surjective_of_localRingHom_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (hq : p.primesOver B = {q})
    (H : Function.Surjective
      (Localization.localRingHom p q (algebraMap A B) (q.over_def p))) :
    ∃ r ∉ p, Function.Surjective
      (IsLocalization.Away.map (Localization.Away r)
        (Localization.Away (algebraMap A B r)) (algebraMap A B) r) := by
  classical
  have key : ∀ x : B, ∃ a : A, ∃ b ∉ p, algebraMap A B b * x = algebraMap A B a := by
    intro x
    have h := (IsLocalization.mk'_surjective p.primeCompl).exists.mp (H (algebraMap _ _ x))
    simp only [Localization.localRingHom_mk', Prod.exists, Subtype.exists,
      Ideal.mem_primeCompl_iff, IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at h
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := h
    obtain ⟨d, hd, t, ht⟩ :=
      Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp hab using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  let r : A := ∏ x ∈ s, b x
  have hr : r ∉ p := Submonoid.prod_mem p.primeCompl (fun x _ ↦ hbp x)
  have hmem : ∀ x ∈ (⊤ : Submodule A B),
      ∃ c : A, algebraMap A B r * x = algebraMap A B c := by
    rw [← hs]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        refine ⟨(∏ y ∈ s.erase x, b y) * a x, ?_⟩
        change algebraMap A B (∏ y ∈ s, b y) * x = _
        rw [← Finset.prod_erase_mul s b hx, map_mul, map_mul, mul_assoc, hab x]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨c, hc⟩ := hx
        obtain ⟨d, hd⟩ := hy
        exact ⟨c + d, by rw [mul_add, hc, hd, map_add]⟩
    | smul t x _ hx =>
        obtain ⟨c, hc⟩ := hx
        refine ⟨t * c, ?_⟩
        rw [Algebra.smul_def, mul_left_comm, hc, map_mul]
  refine ⟨r, hr, ?_⟩
  rw [IsLocalization.Away.map_surjective_iff]
  intro x
  obtain ⟨c, hc⟩ := hmem x Submodule.mem_top
  exact ⟨c, 1, by simpa [r] using hc.symm⟩

/-- A finite unramified morphism with a singleton fibre and purely inseparable residue-field
extension is a closed immersion over some neighbourhood of the point in the target. -/
@[stacks 04DG]
public theorem exists_open_restrict_isClosedImmersion_of_finite_unramified_fiber_eq_singleton
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Unramified f]
    (s : S) (x : X) (hfiber : f ⁻¹' {s} = {x})
    (hpure :
      let hxs : f x = s := by
        have : x ∈ f ⁻¹' {s} := by simp [hfiber]
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using this
      letI := ((S.residueFieldCongr hxs).inv ≫ f.residueFieldMap x).hom.toAlgebra
      IsPurelyInseparable (S.residueField s) (X.residueField x)) :
    ∃ U : S.Opens, s ∈ U ∧ IsClosedImmersion (f ∣_ U) := by
  have hxs : f x = s := by
    have hx : x ∈ f ⁻¹' {s} := by simp [hfiber]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx
  have hresidue : Function.Surjective (f.residueFieldMap x).hom := by
    have hsurr := residueFieldMap_surjective_of_pure f s x hxs hpure
    intro y
    obtain ⟨z, hz⟩ := hsurr y
    refine ⟨(S.residueFieldCongr hxs).inv z, ?_⟩
    simpa [Category.assoc] using hz
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  change IsAffineOpen V at hV
  let W : X.Opens := f ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage f
  have hxW : x ∈ W := by
    change f x ∈ V
    simpa [hxs] using hsV
  let A := Γ(S, V)
  let B := Γ(X, W)
  let φ : A →+* B := (f.appLE V W le_rfl).hom
  let : Algebra A B := φ.toAlgebra
  let qpt : PrimeSpectrum B := hW.primeIdealOf ⟨x, hxW⟩
  let q : Ideal B := qpt.asIdeal
  let ppt : PrimeSpectrum A := hV.primeIdealOf ⟨f x, hxW⟩
  let : q.IsPrime := qpt.2
  let pI : Ideal A := ppt.asIdeal
  have hqOver : q.LiesOver pI := by
    have hcomap := IsAffineOpen.comap_primeIdealOf_appLE V hV W hW le_rfl hxW
    have hideal : q.comap φ = pI := congrArg PrimeSpectrum.asIdeal hcomap
    refine ⟨?_⟩
    simpa [Ideal.under, RingHom.algebraMap_toAlgebra] using hideal.symm
  let : q.LiesOver pI := hqOver
  let := Localization.AtPrime.algebraOfLiesOver pI q
  have hqUnique : pI.primesOver B = {q} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
    rintro q' ⟨hq', hqOver'⟩
    let qpt' : PrimeSpectrum B := ⟨q', hq'⟩
    let yW : W := hW.isoSpec.inv qpt'
    let y : X := yW.1
    have hyW : y ∈ W := yW.2
    have hySpec : hW.isoSpec.hom.base yW = qpt' :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hW.isoSpec)).apply_symm_apply qpt'
    have hqy : (hW.primeIdealOf ⟨y, hyW⟩).comap φ = qpt'.comap φ := by
      apply congrArg (fun z : PrimeSpectrum B => z.comap φ)
      apply PrimeSpectrum.ext
      change (hW.isoSpec.hom.base yW).asIdeal = qpt'.asIdeal
      simpa [IsAffineOpen.primeIdealOf] using congrArg PrimeSpectrum.asIdeal hySpec
    have hcomapEq : qpt'.comap φ = ppt := by
      apply PrimeSpectrum.ext
      change Ideal.comap φ q' = pI
      simpa [Ideal.under, RingHom.algebraMap_toAlgebra] using (q'.over_def pI).symm
    have hprimeY : hV.primeIdealOf ⟨f y, hyW⟩ = ppt := by
      have h := IsAffineOpen.comap_primeIdealOf_appLE V hV W hW le_rfl hyW
      exact h.symm.trans (hqy.trans hcomapEq)
    have hprimeW : hW.primeIdealOf ⟨y, hyW⟩ = qpt' := by
      have hyW_eq : yW = ⟨y, hyW⟩ := by rfl
      have htmp := (congrArg hW.isoSpec.hom.base hyW_eq).symm.trans hySpec
      apply PrimeSpectrum.ext
      simpa only [IsAffineOpen.primeIdealOf] using
        congrArg (fun z : ↥(Spec B) => z.1) htmp
    have hpoint : (⟨f y, hyW⟩ : V) = ⟨f x, hxW⟩ := by
      have hinv := congrArg hV.fromSpec hprimeY
      apply Subtype.ext
      simpa only [ppt, IsAffineOpen.fromSpec_primeIdealOf] using hinv
    have hyx : (y : X) = x := by
      have hbase : f y = s := by simpa [hxs] using congrArg Subtype.val hpoint
      have hyfiber : (y : X) ∈ f ⁻¹' {s} := by simp [Set.mem_preimage, hbase]
      have : (y : X) ∈ ({x} : Set X) := by simpa [hfiber] using hyfiber
      simpa using this
    have hqptEq : qpt' = qpt := by
      calc
        _ = hW.primeIdealOf ⟨y, hyW⟩ := hprimeW.symm
        _ = hW.primeIdealOf ⟨x, hxW⟩ := congrArg hW.primeIdealOf (Subtype.ext hyx)
        _ = _ := by rfl
    exact congrArg PrimeSpectrum.asIdeal hqptEq
  have hfiniteRing : φ.Finite := by
    change (((X.presheaf.map (𝟙 (Opposite.op W))).hom).comp (f.app V).hom).Finite
    have hid : RingHom.Finite ((X.presheaf.map (𝟙 (Opposite.op W))).hom) := by
      simpa using (RingHom.Finite.id B)
    exact RingHom.Finite.comp hid (f.finite_app V hV)
  let : Module.Finite A B := hfiniteRing
  let : Algebra.Unramified A B := by
    have h := (unramified_tfae f).out 1 2
    exact h.mp (inferInstance : Unramified f) W hW V hV le_rfl
  let eStalk := IsAffineOpen.arrowStalkMapIso f V hV W hW le_rfl hxW
  let e₁ := (asIso eStalk.hom.left).commRingCatIsoToRingEquiv
  let e₂ := (asIso eStalk.hom.right).commRingCatIsoToRingEquiv
  have hcomm : (Localization.localRingHom pI q φ (q.over_def pI)).comp e₁.toRingHom =
      e₂.toRingHom.comp (f.stalkMap x).hom :=
    congrArg CommRingCat.Hom.hom eStalk.hom.w
  have hres : Function.Surjective (algebraMap pI.ResidueField q.ResidueField) :=
    residueFieldMap_surjective_of_commutes (f.stalkMap x).hom
      (Localization.localRingHom pI q φ (q.over_def pI)) e₁ e₂ hcomm hresidue
  have hlocal : Function.Surjective (Localization.localRingHom pI q φ (q.over_def pI)) :=
    Localization.localRingHom_surjective_of_primesOver_eq_singleton hqUnique hres
  obtain ⟨r, hr, haway⟩ := exists_awayMap_surjective_of_localRingHom_surjective
    pI q hqUnique hlocal
  let U := S.basicOpen r
  have hU : IsAffineOpen U := hV.basicOpen r
  have hsU : s ∈ U := by
    have hprimeS : hV.primeIdealOf ⟨s, hsV⟩ = ppt :=
      congrArg hV.primeIdealOf (Subtype.ext hxs.symm)
    have hmem : hV.primeIdealOf ⟨s, hsV⟩ ∈ PrimeSpectrum.basicOpen r := by
      apply (PrimeSpectrum.mem_basicOpen r _).2
      simpa [pI, hprimeS] using hr
    have h' : hV.fromSpec (hV.primeIdealOf ⟨s, hsV⟩) ∈ S.basicOpen r := by
      rw [← hV.fromSpec_image_basicOpen r]
      exact ⟨hV.primeIdealOf ⟨s, hsV⟩, hmem, rfl⟩
    simpa only [hV.fromSpec_primeIdealOf] using h'
  let : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  let : IsAffine U.toScheme := hU
  have halg : algebraMap A B = (f.app V).hom := by
    rw [RingHom.algebraMap_toAlgebra]
    ext z
    change (CommRingCat.Hom.hom (X.presheaf.map (𝟙 (Opposite.op W))))
      ((f.app V).hom z) = (f.app V).hom z
    simp
  rw [halg] at haway
  have hsurjLE : Function.Surjective ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom) := by
    rw [Scheme.Hom.appLE, hV.app_basicOpen_eq_away_map f hW r]
    let := hV.isLocalization_basicOpen r
    let := hW.isLocalization_basicOpen (f.app V r)
    let eSrc : Localization.Away r ≃ₐ[A] Γ(S, S.basicOpen r) :=
      IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r)
        Γ(S, S.basicOpen r)
    let eTgt : Localization.Away (f.app V r) ≃ₐ[B]
        Γ(X, X.basicOpen (f.app V r)) :=
      IsLocalization.algEquiv (Submonoid.powers (f.app V r))
        (Localization.Away (f.app V r)) Γ(X, X.basicOpen (f.app V r))
    let awaySrc : Localization.Away r →+* Localization.Away (f.app V r) :=
      IsLocalization.Away.map (Localization.Away r)
        (Localization.Away (f.app V r)) (f.app V).hom r
    let awayBasic : Γ(S, S.basicOpen r) →+* Γ(X, X.basicOpen (f.app V r)) :=
      IsLocalization.Away.map (Γ(S, S.basicOpen r))
        (Γ(X, X.basicOpen (f.app V r))) (f.app V).hom r
    have hconj : awayBasic.comp eSrc.toRingHom = eTgt.toRingHom.comp awaySrc := by
      apply IsLocalization.ringHom_ext (Submonoid.powers r)
      ext a
      change awayBasic (eSrc (algebraMap A (Localization.Away r) a)) =
        eTgt (awaySrc (algebraMap A (Localization.Away r) a))
      rw [eSrc.commutes]
      have hmap : ∀ (P Q : Type u) [CommRing P] [CommRing Q] [Algebra A P] [Algebra B Q]
          [IsLocalization.Away r P] [IsLocalization.Away (f.app V r) Q],
          IsLocalization.Away.map P Q (f.app V).hom r (algebraMap A P a) =
            algebraMap B Q ((f.app V).hom a) := fun P Q _ _ _ _ _ _ ↦ by
        simpa only [IsLocalization.Away.map, B, W] using
          (IsLocalization.map_eq (M := Submonoid.powers r)
            (T := Submonoid.powers (f.app V r)) (Q := Q) (g := (f.app V).hom)
            (hy := by
              rintro z ⟨n, rfl⟩
              exact ⟨n, by simp⟩) a)
      rw [hmap (Γ(S, S.basicOpen r)) (Γ(X, X.basicOpen (f.app V r))),
        hmap (Localization.Away r) (Localization.Away (f.app V r)), eTgt.commutes]
    have hawayBasic : Function.Surjective awayBasic := by
      intro z
      obtain ⟨y, hy⟩ := haway (eTgt.symm z)
      refine ⟨eSrc y, ?_⟩
      calc
        awayBasic (eSrc y) = eTgt (awaySrc y) := by simpa using DFunLike.congr_fun hconj y
        _ = z := by rw [hy]; exact eTgt.apply_symm_apply z
    let e :=
      (asIso (X.presheaf.map
        (eqToHom (Scheme.preimage_basicOpen f r)).op)).commRingCatIsoToRingEquiv
    simp only [homOfLE_refl, op_id, CommRingCat.hom_comp]
    have hid : Function.Surjective
        (CommRingCat.Hom.hom (X.presheaf.map (𝟙 (Opposite.op (f ⁻¹ᵁ U))))) :=
      fun z => ⟨z, by simp⟩
    exact hid.comp (e.surjective.comp hawayBasic)
  have hsurj : Function.Surjective ((f ∣_ U).appTop) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    change Function.Surjective (((f.resLE U (f ⁻¹ᵁ U) le_rfl).app ⊤).hom)
    rw [Scheme.Hom.resLE_app_top]
    let eU := U.topIso.commRingCatIsoToRingEquiv
    let eW := (f ⁻¹ᵁ U).topIso.commRingCatIsoToRingEquiv
    change Function.Surjective
      (eW.symm.toRingHom.comp ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.comp eU.toRingHom))
    exact (eW.symm.surjective.comp (hsurjLE.comp eU.surjective))
  exact ⟨U, hsU, IsClosedImmersion.of_surjective_of_isAffine (f ∣_ U) hsurj⟩

end AlgebraicGeometry

end
