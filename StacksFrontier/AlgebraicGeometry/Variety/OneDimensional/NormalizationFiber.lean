module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Localization.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Stalk
public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.Transfer
public import StacksFrontier.AlgebraicGeometry.ResidueFieldTransport
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.MaximalSpectrum

/-!
# The fibre of the normalization and the stalk of its pushforward

Let `X` be a scheme every quasi-compact open of which has finitely many irreducible components,
and let `ν : X^ν → X` be its normalization. The stalk at `x` of the pushforward `ν_* 𝒪_{X^ν}` is
a localization of the sections of `𝒪_{X^ν}` over the preimage of an affine open around `x`, and
the points of `X^ν` lying over `x` are exactly the maximal ideals of that stalk. The
correspondence is compatible with residue fields: the residue field of `X^ν` at a point of the
fibre is the residue field of the stalk at the matching maximal ideal, as an extension of the
residue field of `X` at `x`.

## Main definitions

* `AlgebraicGeometry.normalizationFiberResidueMap` is the canonical evaluation homomorphism from
  the pushforward stalk to the residue field at a point of the fibre.

## Main results

* `AlgebraicGeometry.normalizationFiberEquivMaximalSpectrum` identifies the normalization fibre
  with the maximal spectrum of the pushforward stalk, compatibly with residue fields over the
  residue field of the base point.

## Implementation notes

For a point and its corresponding maximal ideal, compatibility of residue fields as extensions
of `κ(x)` is expressed by a ring equivalence commuting with the maps from `𝒪_{X,x}`; these maps
factor through the surjection `𝒪_{X,x} → κ(x)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.NormalizationStalkAmbient

universe u

namespace AlgebraicGeometry


/-- Evaluation of the normalization pushforward stalk at a point of the fibre,
followed by passage to that point's residue field. -/
public noncomputable def normalizationFiberResidueMap
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X)
    (y : {y : Scheme.normalizationScheme X hX //
      Scheme.normalization X hX y = x}) :
    normalizationPushforwardStalk X hX x →+*
      (Scheme.normalizationScheme X hX).residueField y :=
  cast (congrArg (fun z : X =>
      normalizationPushforwardStalk X hX z →+*
        (Scheme.normalizationScheme X hX).residueField y) y.property)
    (((Scheme.normalizationScheme X hX).residue y).hom.comp
      (((Scheme.normalizationScheme X hX).presheaf.stalkPushforward CommRingCat
        (Scheme.normalization X hX).base y).hom))

private lemma normalizationFiberResidueMap_comp_algebraMap
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X)
    (y : {y : Scheme.normalizationScheme X hX //
      Scheme.normalization X hX y = x}) :
    letI := normalizationPushforwardStalkAlgebra X hX x
    ((((Scheme.normalization X hX).residueFieldMap y).hom.comp
      (X.residueFieldCongr y.property.symm).hom.hom).comp (X.residue x).hom) =
      (normalizationFiberResidueMap X hX x y).comp
        (algebraMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X hX x)) := by
  rcases y with ⟨y, rfl⟩
  change ((Scheme.normalization X hX).residueFieldMap y).hom.comp
      (X.residue _).hom = _
  rw [← CommRingCat.hom_comp, Scheme.residue_residueFieldMap]
  rfl

private lemma stalk_eqToHom_comp_germ
    {Z : TopCat.{u}} (G : TopCat.Presheaf CommRingCat Z) {a b : Z} (h : a = b)
    (U : Opens Z) (ha : a ∈ U) :
    (eqToHom (congrArg G.stalk h)).hom.comp (G.germ U a ha).hom =
      (G.germ U b (h ▸ ha)).hom := by
  cases h
  rfl

/-! The `residueField_eqToHom_comp_residue` that used to sit here has been hoisted, with the
private copy that used to sit in
`StacksFrontier/AlgebraicGeometry/Morphisms/Integral/PushforwardStalkFibre.lean`,
into the module all its users can import:
`AlgebraicGeometry.residueField_eqToHom_comp_residue` of
`StacksFrontier/AlgebraicGeometry/ResidueFieldTransport.lean`, line 37. -/

private lemma cast_commRingHom_eq_comp
    {α : Type u} (R : α → CommRingCat.{u}) (S : CommRingCat.{u})
    {a b : α} (h : a = b) (f : R a →+* S) :
    cast (congrArg (fun z : α => R z →+* S) h) f =
      f.comp (eqToHom (congrArg R h.symm)).hom := by
  cases h
  rfl

private lemma normalizationPushforwardStalk_isLocalization
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) :
    letI : Algebra Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
        (normalizationPushforwardStalk X hX x) :=
      (((Scheme.normalization X hX).base _* (Scheme.normalizationScheme X hX).presheaf).germ
        U x hx).hom.toAlgebra
    IsLocalization (Submonoid.map ((Scheme.normalization X hX).app U).hom
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (normalizationPushforwardStalk X hX x) := by
  have := Scheme.quasiCompactFromGenericPointResidueFields X hX
  have := Scheme.quasiSeparatedFromGenericPointResidueFields X
  have : QuasiCompact (Scheme.normalization X hX) := by
    dsimp [Scheme.normalization]
    infer_instance
  have : QuasiSeparated (Scheme.normalization X hX) := by
    dsimp [Scheme.normalization]
    infer_instance
  exact Scheme.pushforwardStalk_isLocalization _ U hU x hx

private noncomputable def normalizationPushforwardStalkLocalizationEquiv
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) :
    let ν := Scheme.normalization X hX
    let T := Γ(Scheme.normalizationScheme X hX, ν ⁻¹ᵁ U)
    let p := hU.primeIdealOf ⟨x, hx⟩
    letI : Algebra T (normalizationPushforwardStalk X hX x) :=
      (((ν.base _* (Scheme.normalizationScheme X hX).presheaf).germ U x hx).hom.toAlgebra)
    normalizationPushforwardStalk X hX x ≃ₐ[T]
      Localization (Submonoid.map (ν.app U).hom p.asIdeal.primeCompl) := by
  classical
  let ν := Scheme.normalization X hX
  let T := Γ(Scheme.normalizationScheme X hX, ν ⁻¹ᵁ U)
  let M : Submonoid T := Submonoid.map (ν.app U).hom (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : Algebra T (normalizationPushforwardStalk X hX x) :=
    ((ν.base _* (Scheme.normalizationScheme X hX).presheaf).germ U x hx).hom.toAlgebra
  have : IsLocalization M (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalk_isLocalization X hX x U hU hx
  exact (IsLocalization.algEquiv M (Localization M) _).symm

private lemma disjoint_map_primeCompl_of_comap_eq {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) {p : PrimeSpectrum R} {q : PrimeSpectrum T} (h : q.comap φ = p) :
    Disjoint (Submonoid.map φ p.asIdeal.primeCompl : Set T) q.asIdeal :=
  (Ideal.disjoint_map_primeCompl_iff_comap_le (f := φ) (I := q.asIdeal)).mpr
    (congrArg PrimeSpectrum.asIdeal h).le |>.symm

private lemma comap_primeIdealOf_preimage {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {y : Y} (hy : f y = x)
    (hyV : y ∈ f ⁻¹ᵁ U) :
    ((hU.preimage f).primeIdealOf ⟨y, hyV⟩).comap (f.app U).hom = hU.primeIdealOf ⟨x, hx⟩ := by
  subst hy
  have h := IsAffineOpen.comap_primeIdealOf_appLE (f := f) (x := y) U hU _ (hU.preimage f)
    le_rfl hyV
  rwa [show (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom = (f.app U).hom from
    congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_eq_app f)] at h

/-- For an integral `φ : R →+* T` and a prime `p` of `R`, the primes of `T` over `p` stay maximal
in the localization of `T` at `φ (R ∖ p)`, and every maximal ideal of that localization lies
over `p`. -/
private theorem localizedPrime_isMaximal_and_liesOver
    {R T : Type u} [CommRing R] [CommRing T]
    (φ : R →+* T) (hφ : φ.IsIntegral) (p : PrimeSpectrum R) :
    (∀ q : PrimeSpectrum T, q.comap φ = p →
      (q.asIdeal.map (algebraMap T
        (Localization (Submonoid.map φ p.asIdeal.primeCompl)))).IsMaximal) ∧
    ∀ Q : Ideal (Localization (Submonoid.map φ p.asIdeal.primeCompl)), Q.IsMaximal →
      (Q.comap (algebraMap T
        (Localization (Submonoid.map φ p.asIdeal.primeCompl)))).comap φ = p.asIdeal := by
  classical
  let : Algebra R T := φ.toAlgebra
  let M : Submonoid R := p.asIdeal.primeCompl
  let N : Submonoid T := Algebra.algebraMapSubmonoid T M
  let L := Localization (Submonoid.map φ M)
  let A := Localization M
  let : IsLocalization N L := by
    change IsLocalization (Submonoid.map φ M) L
    infer_instance
  let : Algebra R L := Algebra.compHom L φ
  let : Algebra A L := localizationAlgebra M T
  let : SMul R L := (inferInstance : Algebra R L).toSMul
  let : SMul T L := (inferInstance : Algebra T L).toSMul
  let : SMul A L := (inferInstance : Algebra A L).toSMul
  let : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R A L := isScalarTower_localizationAlgebra M T
  have hMap : (algebraMap A L) =
      IsLocalization.map L φ (M.le_comap_map :
        M ≤ Submonoid.comap φ (Submonoid.map φ M)) := by
    rw [localizationAlgebraMap_def]
    rfl
  have hLocIntegral : (algebraMap A L).IsIntegral := by
    rw [hMap]
    exact isIntegral_localization' (f := φ) hφ M
  let : Algebra.IsIntegral A L := algebraMap_isIntegral_iff.mp hLocIntegral
  refine ⟨fun q hq => ?_, fun Q hQ => ?_⟩
  · let : q.asIdeal.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hq).symm⟩
    have hdisj : Disjoint (N : Set T) q.asIdeal := disjoint_map_primeCompl_of_comap_eq φ hq
    have hOver := IsLocalization.liesOver_of_isPrime_of_disjoint
      (R' := A) (S' := L) M N p.asIdeal (P := q.asIdeal) hdisj
    have hmaxBase : (p.asIdeal.map (algebraMap R A)).IsMaximal := by
      rw [IsLocalization.AtPrime.map_eq_maximalIdeal]
      exact IsLocalRing.maximalIdeal.isMaximal A
    have hmaxContract :
        ((q.asIdeal.map (algebraMap T L)).comap (algebraMap A L)).IsMaximal := by
      have hcontract : (q.asIdeal.map (algebraMap T L)).comap (algebraMap A L) =
          p.asIdeal.map (algebraMap R A) := hOver.over.symm
      rw [hcontract]
      exact hmaxBase
    let : (q.asIdeal.map (algebraMap T L)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint N L q.asIdeal q.isPrime hdisj
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A)
      (q.asIdeal.map (algebraMap T L)) hmaxContract
  · have := hQ.isPrime
    have hQcontract : Q.comap (algebraMap A L) = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (S := L) Q)
    have hComp : (Q.comap (algebraMap T L)).comap φ =
        (Q.comap (algebraMap A L)).comap (algebraMap R A) := by
      ext r
      change algebraMap T L (algebraMap R T r) ∈ Q ↔
        algebraMap A L (algebraMap R A r) ∈ Q
      rw [← IsScalarTower.algebraMap_apply R T L,
        ← IsScalarTower.algebraMap_apply R A L]
    rw [hComp, hQcontract]
    exact IsLocalization.AtPrime.under_maximalIdeal A p.asIdeal

private noncomputable def pointToMaximalLocalization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsIntegralHom f]
    (x : X) (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) (y : {y : Y // f y = x}) :
    MaximalSpectrum (Localization (Submonoid.map (f.app U).hom
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)) := by
  let T := Γ(Y, f ⁻¹ᵁ U)
  let M : Submonoid T := Submonoid.map (f.app U).hom (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let L := Localization M
  have hyV : y.1 ∈ f ⁻¹ᵁ U := (congrArg (· ∈ U) y.2).mpr hx
  let q : PrimeSpectrum T := (hU.preimage f).primeIdealOf ⟨y.1, hyV⟩
  have hqp : q.comap (f.app U).hom = hU.primeIdealOf ⟨x, hx⟩ :=
    comap_primeIdealOf_preimage f hU hx y.2 hyV
  let qL := (IsLocalization.primeSpectrumOrderIso M L).symm
    ⟨q, disjoint_map_primeCompl_of_comap_eq _ hqp⟩
  have hqLmax : qL.asIdeal.IsMaximal := by
    change (q.asIdeal.map (algebraMap T L)).IsMaximal
    exact (localizedPrime_isMaximal_and_liesOver _ (f.isIntegral_app U hU) _).1 q hqp
  exact ⟨qL.asIdeal, hqLmax⟩

private noncomputable def pointOfMaximalLocalization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsIntegralHom f]
    (x : X) (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U)
    (m : MaximalSpectrum (Localization (Submonoid.map (f.app U).hom
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl))) :
    {y : Y // f y = x} := by
  let V := f ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f
  let T := Γ(Y, V)
  let p := hU.primeIdealOf ⟨x, hx⟩
  let M : Submonoid T := Submonoid.map (f.app U).hom p.asIdeal.primeCompl
  let q : PrimeSpectrum T :=
    (IsLocalization.primeSpectrumOrderIso M (Localization M) m.toPrimeSpectrum).1
  have := m.isMaximal
  have hqp : q.comap (f.app U).hom = p :=
    PrimeSpectrum.ext
      ((localizedPrime_isMaximal_and_liesOver _ (f.isIntegral_app U hU) p).2 m.asIdeal
        m.isMaximal)
  let z : V := hV.isoSpec.inv q
  have hspec : Spec.map (f.appLE U V le_rfl) q = p := by
    apply PrimeSpectrum.ext
    change q.asIdeal.comap (CommRingCat.Hom.hom (f.appLE U V le_rfl)) = p.asIdeal
    rw [Scheme.Hom.appLE_eq_app]
    exact congrArg PrimeSpectrum.asIdeal hqp
  have hbase : f (V.ι z) = x := by
    have hp := congrArg (fun g => g q) (IsAffineOpen.SpecMap_appLE_fromSpec (f := f) hU hV le_rfl)
    change hU.fromSpec (Spec.map (f.appLE U V le_rfl) q) = f (V.ι z) at hp
    rw [← hp, hspec]
    exact hU.fromSpec_primeIdealOf ⟨x, hx⟩
  exact ⟨V.ι z, hbase⟩

private noncomputable def pointsOverEquivMaximalLocalization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsIntegralHom f]
    (x : X) (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) :
    {y : Y // f y = x} ≃ MaximalSpectrum
      (Localization (Submonoid.map (f.app U).hom
        (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)) := by
  classical
  let V := f ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f
  let T := Γ(Y, V)
  let M : Submonoid T := Submonoid.map (f.app U).hom (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let L := Localization M
  let eLoc : PrimeSpectrum L ≃o
      {q : PrimeSpectrum T // Disjoint (M : Set T) q.asIdeal} :=
    IsLocalization.primeSpectrumOrderIso M L
  let pointToMax := pointToMaximalLocalization f x U hU hx
  let maxToPoint := pointOfMaximalLocalization f x U hU hx
  have left_inv (y : {y : Y // f y = x}) : maxToPoint (pointToMax y) = y := by
    apply Subtype.ext
    have hyV : y.1 ∈ V := (congrArg (· ∈ U) y.2).mpr hx
    let q : PrimeSpectrum T := hV.primeIdealOf ⟨y.1, hyV⟩
    have hdisj : Disjoint (M : Set T) q.asIdeal :=
      disjoint_map_primeCompl_of_comap_eq _ (comap_primeIdealOf_preimage f hU hx y.2 hyV)
    have hprime : (pointToMax y).toPrimeSpectrum = eLoc.symm ⟨q, hdisj⟩ := PrimeSpectrum.ext rfl
    change hV.fromSpec (eLoc (pointToMax y).toPrimeSpectrum).1 = y.1
    rw [hprime, eLoc.apply_symm_apply]
    exact hV.fromSpec_primeIdealOf _
  have right_inv (m : MaximalSpectrum L) : pointToMax (maxToPoint m) = m := by
    apply MaximalSpectrum.ext
    let z : V := hV.isoSpec.inv (eLoc m.toPrimeSpectrum).1
    have hq : hV.primeIdealOf z = (eLoc m.toPrimeSpectrum).1 :=
      congrArg (fun g => g (eLoc m.toPrimeSpectrum).1)
        (congrArg (fun g : Scheme.Hom _ _ => g.base) hV.isoSpec.inv_hom_id)
    have hdisj : Disjoint (M : Set T) (hV.primeIdealOf z).asIdeal := by
      rw [show (hV.primeIdealOf z).asIdeal = (eLoc m.toPrimeSpectrum).1.asIdeal from
        congrArg PrimeSpectrum.asIdeal hq]
      exact (eLoc m.toPrimeSpectrum).2
    have hsub :
        (⟨hV.primeIdealOf z, hdisj⟩ :
          {q : PrimeSpectrum T // Disjoint (M : Set T) q.asIdeal}) =
          eLoc m.toPrimeSpectrum :=
      Subtype.ext hq
    change (eLoc.symm ⟨hV.primeIdealOf z, hdisj⟩).asIdeal = m.asIdeal
    rw [congrArg eLoc.symm hsub, eLoc.symm_apply_apply]
    rfl
  exact ⟨pointToMax, maxToPoint, left_inv, right_inv⟩

private lemma normalizationFiberResidueMap_comp_germ
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (y : {y : Scheme.normalizationScheme X hX // Scheme.normalization X hX y = x})
    (U : X.Opens) (hxU : x ∈ U) (hyV : y.1 ∈ Scheme.normalization X hX ⁻¹ᵁ U) :
    (normalizationFiberResidueMap X hX x y).comp
        (((Scheme.normalization X hX).base _* (Scheme.normalizationScheme X hX).presheaf).germ
          U x hxU).hom =
      ((Scheme.normalizationScheme X hX).residue y.1).hom.comp
        ((Scheme.normalizationScheme X hX).presheaf.germ _ y.1 hyV).hom := by
  rcases y with ⟨y, rfl⟩
  exact congrArg ((Scheme.normalizationScheme X hX).residue y).hom.comp
    (congrArg CommRingCat.Hom.hom (TopCat.Presheaf.stalkPushforward_germ CommRingCat
      (Scheme.normalization X hX).base (Scheme.normalizationScheme X hX).presheaf U y hxU))

private lemma residueFieldCongr_hom_comp_residue_germ (Z : Scheme.{u}) {a b : Z} (h : a = b)
    (V : Z.Opens) (ha : a ∈ V) (hb : b ∈ V) :
    (Z.residueFieldCongr h).hom.hom.comp ((Z.residue a).hom.comp (Z.presheaf.germ V a ha).hom) =
      (Z.residue b).hom.comp (Z.presheaf.germ V b hb).hom := by
  subst h
  rfl

private lemma IsAffineOpen.residueFieldMap_fromSpec_comp_residue_germ {Z : Scheme.{u}}
    {V : Z.Opens} (hV : IsAffineOpen V) (q : PrimeSpectrum Γ(Z, V)) (hzV : hV.fromSpec q ∈ V) :
    (hV.fromSpec.residueFieldMap q).hom.comp
        ((Z.residue (hV.fromSpec q)).hom.comp (Z.presheaf.germ V (hV.fromSpec q) hzV).hom) =
      ((Spec Γ(Z, V)).residue q).hom.comp
        (((Spec Γ(Z, V)).presheaf.germ ⊤ q trivial).hom.comp
          (Scheme.ΓSpecIso Γ(Z, V)).inv.hom) := by
  have hNat :
      (hV.fromSpec.residueFieldMap q).hom.comp (Z.residue (hV.fromSpec q)).hom =
        ((Spec Γ(Z, V)).residue q).hom.comp (hV.fromSpec.stalkMap q).hom := by
    simpa only [CommRingCat.hom_comp] using
      congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap hV.fromSpec q)
  have hGermJ :
      (hV.fromSpec.stalkMap q).hom.comp (Z.presheaf.germ V (hV.fromSpec q) hzV).hom =
        ((Spec Γ(Z, V)).presheaf.germ (hV.fromSpec ⁻¹ᵁ V) q hzV).hom.comp
          (hV.fromSpec.app V).hom := by
    simpa only [CommRingCat.hom_comp] using
      congrArg CommRingCat.Hom.hom (Scheme.Hom.germ_stalkMap hV.fromSpec V q hzV)
  have hGlobal :
      ((Spec Γ(Z, V)).presheaf.germ (hV.fromSpec ⁻¹ᵁ V) q hzV).hom.comp
          (hV.fromSpec.app V).hom =
        ((Spec Γ(Z, V)).presheaf.germ ⊤ q trivial).hom.comp
          (Scheme.ΓSpecIso Γ(Z, V)).inv.hom := by
    rw [hV.fromSpec_app_self, CommRingCat.hom_comp, ← RingHom.comp_assoc]
    have hres := congrArg CommRingCat.Hom.hom
      ((Spec Γ(Z, V)).presheaf.germ_res (eqToHom hV.fromSpec_preimage_self) q hzV)
    simp only [CommRingCat.hom_comp] at hres
    rw [hres]
  rw [← RingHom.comp_assoc, hNat, RingHom.comp_assoc, hGermJ, hGlobal]

private lemma Scheme.Spec.residueFieldIso_hom_comp_residue_germ_top (T : CommRingCat.{u})
    (q : PrimeSpectrum T) :
    (Scheme.Spec.residueFieldIso (CommRingCat.of T) q).hom.hom.comp
        (((Spec T).residue q).hom.comp
          (((Spec T).presheaf.germ ⊤ q trivial).hom.comp (Scheme.ΓSpecIso T).inv.hom)) =
      algebraMap T q.asIdeal.ResidueField := by
  let specIso := Scheme.Spec.residueFieldIso (CommRingCat.of T) q
  have hInv := congrArg CommRingCat.Hom.hom
    (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of T) q)
  simp only [CommRingCat.hom_comp] at hInv
  change specIso.inv.hom.comp (algebraMap T q.asIdeal.ResidueField) = _ at hInv
  exact (congrArg (fun k => specIso.hom.hom.comp k) hInv.symm).trans
    (RingHom.ext fun _ => specIso.inv_hom_id_apply _)

private noncomputable def IsAffineOpen.residueFieldEquivPrimeIdealOf {Z : Scheme.{u}}
    {V : Z.Opens} (hV : IsAffineOpen V) (z : Z) (hz : z ∈ V) :
    Z.residueField z ≃+* (hV.primeIdealOf ⟨z, hz⟩).asIdeal.ResidueField := by
  let q := hV.primeIdealOf ⟨z, hz⟩
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have : IsIso (hV.fromSpec.stalkMap q) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hV.isOpenImmersion_fromSpec).2 q
  have : IsLocalRing ((Spec Γ(Z, V)).presheaf.stalk q) := (Spec Γ(Z, V)).isLocalRing q
  have : IsIso (hV.fromSpec.residueFieldMap q) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (hV.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  exact (Z.residueFieldCongr (hV.fromSpec_primeIdealOf ⟨z, hz⟩).symm).commRingCatIsoToRingEquiv
    |>.trans (RingEquiv.ofBijective (hV.fromSpec.residueFieldMap q).hom
      (ConcreteCategory.bijective_of_isIso _))
    |>.trans (Scheme.Spec.residueFieldIso (CommRingCat.of Γ(Z, V)) q).commRingCatIsoToRingEquiv

private lemma IsAffineOpen.residueFieldEquivPrimeIdealOf_comp_residue_germ {Z : Scheme.{u}}
    {V : Z.Opens} (hV : IsAffineOpen V) (z : Z) (hz : z ∈ V) :
    (hV.residueFieldEquivPrimeIdealOf z hz).toRingHom.comp
        ((Z.residue z).hom.comp (Z.presheaf.germ V z hz).hom) =
      algebraMap Γ(Z, V) (hV.primeIdealOf ⟨z, hz⟩).asIdeal.ResidueField := by
  let q := hV.primeIdealOf ⟨z, hz⟩
  have hzq : hV.fromSpec q = z := hV.fromSpec_primeIdealOf ⟨z, hz⟩
  have hqV : hV.fromSpec q ∈ V := hzq.symm ▸ hz
  change (Scheme.Spec.residueFieldIso (CommRingCat.of Γ(Z, V)) q).hom.hom.comp
      ((hV.fromSpec.residueFieldMap q).hom.comp
        ((Z.residueFieldCongr hzq.symm).hom.hom.comp
          ((Z.residue z).hom.comp (Z.presheaf.germ V z hz).hom))) = _
  rw [residueFieldCongr_hom_comp_residue_germ _ hzq.symm V hz hqV,
    hV.residueFieldMap_fromSpec_comp_residue_germ q hqV,
    Scheme.Spec.residueFieldIso_hom_comp_residue_germ_top]

private lemma exists_residueField_equiv_quotient_of_localization {T S : Type*} [CommRing T]
    [CommRing S] [Algebra T S] (N : Submonoid T) (eSL : S ≃ₐ[T] Localization N) (q : Ideal T)
    [q.IsPrime] (hdisj : Disjoint (N : Set T) q) (M : Ideal S)
    (hmax : (q.map (algebraMap T (Localization N))).IsMaximal)
    (hM : Ideal.map eSL.toRingEquiv.toRingHom M = q.map (algebraMap T (Localization N))) :
    ∃ e : q.ResidueField ≃+* S ⧸ M,
      ∀ t, e (algebraMap T q.ResidueField t) = Ideal.Quotient.mk M (algebraMap T S t) := by
  let L := Localization N
  let qL : Ideal L := q.map (algebraMap T L)
  have := hmax
  let eLocal : q.ResidueField ≃ₐ[T] qL.ResidueField := by
    have he : (qL.comap (algebraMap T L)).ResidueField ≃ₐ[T] qL.ResidueField :=
      IsLocalRing.ResidueField.mapAlgEquiv
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization N qL)
    exact (Ideal.residueFieldAlgEquiv q (qL.comap (algebraMap T L)) (AlgEquiv.refl (R := T))
      (IsLocalization.under_map_of_isPrime_disjoint _ _ inferInstance hdisj).symm).trans he
  let eQuotL : (L ⧸ qL) ≃+* qL.ResidueField :=
    RingEquiv.ofBijective (algebraMap (L ⧸ qL) qL.ResidueField)
      qL.bijective_algebraMap_quotient_residueField
  let eQuot : (S ⧸ M) ≃+* (L ⧸ qL) := Ideal.quotientEquiv M qL eSL.toRingEquiv hM.symm
  refine ⟨eLocal.toRingEquiv.trans eQuotL.symm |>.trans eQuot.symm, fun t => ?_⟩
  change eQuot.symm (eQuotL.symm (eLocal (algebraMap T q.ResidueField t))) =
    Ideal.Quotient.mk M (algebraMap T S t)
  rw [eLocal.commutes, eQuot.symm_apply_eq, eQuotL.symm_apply_eq]
  change (algebraMap T qL.ResidueField) t =
    algebraMap (L ⧸ qL) qL.ResidueField (Ideal.Quotient.mk qL (eSL (algebraMap T S t)))
  rw [eSL.commutes]
  exact (IsScalarTower.algebraMap_apply T L qL.ResidueField t).trans
    (congrArg (fun k : L →+* qL.ResidueField => k (algebraMap T L t))
      (IsScalarTower.algebraMap_eq L (L ⧸ qL) qL.ResidueField))

private noncomputable def normalizationFiberEquivOfAffine
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U) :
    {y : Scheme.normalizationScheme X hX // Scheme.normalization X hX y = x} ≃
      MaximalSpectrum (normalizationPushforwardStalk X hX x) := by
  let ν := Scheme.normalization X hX
  let T := Γ(Scheme.normalizationScheme X hX, ν ⁻¹ᵁ U)
  let N : Submonoid T := Submonoid.map (ν.app U).hom
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  let : Algebra T (normalizationPushforwardStalk X hX x) :=
    ((ν.base _* (Scheme.normalizationScheme X hX).presheaf).germ U x hxU).hom.toAlgebra
  let eSL : normalizationPushforwardStalk X hX x ≃ₐ[T] Localization N :=
    normalizationPushforwardStalkLocalizationEquiv X hX x U hU hxU
  exact (pointsOverEquivMaximalLocalization ν x U hU hxU).trans
    (MaximalSpectrum.congr eSL.toRingEquiv).symm

private lemma exists_residueFieldEquiv_normalizationFiberEquivOfAffine
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
    (y : {y : Scheme.normalizationScheme X hX // Scheme.normalization X hX y = x}) :
    ∃ e : (Scheme.normalizationScheme X hX).residueField y ≃+*
        (normalizationPushforwardStalk X hX x ⧸
          (normalizationFiberEquivOfAffine X hX x U hU hxU y).asIdeal),
      e.toRingHom.comp (normalizationFiberResidueMap X hX x y) =
        Ideal.Quotient.mk (normalizationFiberEquivOfAffine X hX x U hU hxU y).asIdeal := by
  classical
  let S := normalizationPushforwardStalk X hX x
  let ν := Scheme.normalization X hX
  let V := ν ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage ν
  let T := Γ(Scheme.normalizationScheme X hX, V)
  let φ : Γ(X, U) →+* T := (ν.app U).hom
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let N : Submonoid T := Submonoid.map φ p.asIdeal.primeCompl
  let L := Localization N
  let : Algebra T S :=
    ((ν.base _* (Scheme.normalizationScheme X hX).presheaf).germ U x hxU).hom.toAlgebra
  have : IsLocalization N S := normalizationPushforwardStalk_isLocalization X hX x U hU hxU
  let eSL : S ≃ₐ[T] L := normalizationPushforwardStalkLocalizationEquiv X hX x U hU hxU
  let M : Ideal S := (normalizationFiberEquivOfAffine X hX x U hU hxU y).asIdeal
  have hyV : y.1 ∈ V := (congrArg (· ∈ U) y.property).mpr hxU
  let q : PrimeSpectrum T := hV.primeIdealOf ⟨y.1, hyV⟩
  have hqp : q.comap φ = p := comap_primeIdealOf_preimage ν hU hxU y.property hyV
  let qL : Ideal L := q.asIdeal.map (algebraMap T L)
  have hqLmax : qL.IsMaximal :=
    (localizedPrime_isMaximal_and_liesOver φ (ν.isIntegral_app U hU) p).1 q hqp
  have hM : M = qL.comap eSL.toRingEquiv.toRingHom := rfl
  have hMmap : Ideal.map eSL.toRingEquiv.toRingHom M = qL := by
    rw [hM]
    exact qL.map_comap_of_surjective _ eSL.toRingEquiv.surjective
  obtain ⟨e, he⟩ := exists_residueField_equiv_quotient_of_localization N eSL q.asIdeal
    (disjoint_map_primeCompl_of_comap_eq φ hqp) M hqLmax hMmap
  let eY := hV.residueFieldEquivPrimeIdealOf y.1 hyV
  have hEvalY : (eY.toRingHom.comp (normalizationFiberResidueMap X hX x y)).comp
      (algebraMap T S) = algebraMap T q.asIdeal.ResidueField := by
    have hNchart :
        (normalizationFiberResidueMap X hX x y).comp (algebraMap T S) =
          ((Scheme.normalizationScheme X hX).residue y.1).hom.comp
            ((Scheme.normalizationScheme X hX).presheaf.germ V y.1 hyV).hom :=
      normalizationFiberResidueMap_comp_germ X hX x y U hxU hyV
    rw [RingHom.comp_assoc, hNchart]
    exact hV.residueFieldEquivPrimeIdealOf_comp_residue_germ y.1 hyV
  refine ⟨eY.trans e, IsLocalization.ringHom_ext N (RingHom.ext fun t => ?_)⟩
  have hval : eY (normalizationFiberResidueMap X hX x y (algebraMap T S t)) =
      algebraMap T q.asIdeal.ResidueField t := by
    simpa using RingHom.congr_fun hEvalY t
  change e (eY (normalizationFiberResidueMap X hX x y (algebraMap T S t))) =
    Ideal.Quotient.mk M (algebraMap T S t)
  rw [hval]
  exact he t

/-- Points of the normalization over `x` correspond to maximal ideals of the
pushforward stalk, with compatible residue fields over `κ(x)`. -/
public theorem normalizationFiberEquivMaximalSpectrum
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    letI : Algebra (X.presheaf.stalk x)
        (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    ∃ f : ({y : Scheme.normalizationScheme X hX //
        Scheme.normalization X hX y = x} ≃
        MaximalSpectrum (normalizationPushforwardStalk X hX x)),
      ∀ y : {y : Scheme.normalizationScheme X hX //
          Scheme.normalization X hX y = x},
        ∃ e : (Scheme.normalizationScheme X hX).residueField y ≃+*
          (normalizationPushforwardStalk X hX x ⧸ (f y).asIdeal),
        (e.toRingHom.comp (normalizationFiberResidueMap X hX x y) =
          Ideal.Quotient.mk (f y).asIdeal) ∧
        ((e.toRingHom.comp
            (((Scheme.normalization X hX).residueFieldMap y).hom.comp
              (X.residueFieldCongr y.property.symm).hom.hom)).comp
              (X.residue x).hom =
          (Ideal.Quotient.mk (f y).asIdeal).comp
            (algebraMap (X.presheaf.stalk x)
              (normalizationPushforwardStalk X hX x))) := by
  classical
  let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change IsAffineOpen U at hU
  refine ⟨normalizationFiberEquivOfAffine X hX x U hU hxU, fun y => ?_⟩
  obtain ⟨e, heval⟩ := exists_residueFieldEquiv_normalizationFiberEquivOfAffine X hX x U hU hxU y
  refine ⟨e, heval, ?_⟩
  rw [RingHom.comp_assoc, normalizationFiberResidueMap_comp_algebraMap,
    ← RingHom.comp_assoc, heval]


end AlgebraicGeometry

end
