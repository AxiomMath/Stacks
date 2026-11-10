module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FibreDimensionAffine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.PurelyTranscendentalPrime
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldSpecMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldTrdeg
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.Topology.Separation.IsolatedPoint

/-!
# Factoring a morphism of finite type through affine space over the base

Let `f : X ⟶ S` be locally of finite type, let `x` be a point of `X` and let `n` be the local
dimension of the fibre of `f` through `x`. This file produces a factorisation of `f` through
affine `n`-space over `S`: an affine open `X₀ ⊆ X` containing `x`, an open subscheme `Y₀` of
affine `n`-space over an affine open of `S`, a morphism `π₀ : X₀ ⟶ Y₀` which is locally of
finite type and quasi-finite at `x`, and a morphism `Y₀ ⟶ S` smooth of relative dimension `n`,
such that the residue field of `π₀ x` is a purely transcendental extension of the residue field
of `f x`.

This is the first half of the proof of Stacks 052E. The elementary étale neighbourhood of the
conclusion of 052E is obtained from `π₀` by Stacks 02LK, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/FiniteOverSmooth/Main.lean`.

## Main results

* `purelyTranscendental_of_ringEquiv`: pure transcendence transports along a pair of ring
  isomorphisms of the base field and of the extension.
* `Algebra.exists_quasiFinite_mvPolynomial_away_purelyTranscendental`: Stacks 0520 together
  with the purely transcendental residue field extension it produces.
* `AlgebraicGeometry.residueFieldCongr_hom_residueFieldMap`: the residue field map of a
  morphism of schemes at two equal points.
* `AlgebraicGeometry.exists_quasiFinite_over_affineSpace`: the factorisation.

## Implementation notes

The purely transcendental extension is produced at the level of rings, where the prime of
affine `n`-space is explicitly `(𝔭, x_{r+1}, …, x_n)`, and then transported twice: once along
the residue field isomorphism of a localisation, to change the base from `κ(𝔭 R_a)` to `κ(𝔭)`,
and once along the canonical isomorphisms of `Scheme.Spec.residueFieldIso`, to turn the
statement about residue fields of primes into one about residue fields of schemes. Both
transports go through `purelyTranscendental_of_ringEquiv`.

The prime of affine `n`-space is kept throughout in the form in which Stacks 0520 delivers it,
namely as a contraction along the quasi-finite map; the equality of ideals which identifies it
with the explicit sum is only used to compute its residue field.

## References

* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
* [Stacks Project, Tag 0520](https://stacks.math.columbia.edu/tag/0520)
-/

@[expose] public section

open IntermediateField MvPolynomial

attribute [local instance] Ideal.residueFieldAlgebra

/-- The structure map of `Ideal.residueFieldAlgebra` is `Ideal.ResidueField.map`. -/
private theorem algebraMap_residueFieldAlgebra {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] (p : Ideal R) [p.IsPrime] (q : Ideal T) [q.IsPrime] [q.LiesOver p] :
    algebraMap p.ResidueField q.ResidueField =
      Ideal.ResidueField.map p q (algebraMap R T) (Ideal.over_def q p) := rfl

attribute [local instance] Ideal.isScalarTower_residueField

/-- Pure transcendence transports along a pair of ring isomorphisms of the base and of the
extension which are compatible with the two structure maps. -/
theorem purelyTranscendental_of_ringEquiv {k k' K K' : Type*} [Field k] [Field k'] [Field K]
    [Field K'] [Algebra k K] [Algebra k' K'] (e : k ≃+* k') (E : K ≃+* K')
    (hE : ∀ a : k, E (algebraMap k K a) = algebraMap k' K' (e a))
    [PurelyTranscendental k K] : PurelyTranscendental k' K' := by
  obtain ⟨s, ⟨ψ⟩⟩ := PurelyTranscendental.exists_algEquiv_mvRatFunc k K
  let μ : MvRatFunc s k' ≃+* MvRatFunc s k :=
    IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.mapEquiv ↥s e.symm)
  let τ : MvRatFunc s k' ≃+* K' := μ.trans (ψ.toRingEquiv.trans E)
  refine (AlgEquiv.ofRingEquiv (f := τ) fun a => ?_).purelyTranscendental
  have h1 : μ (algebraMap k' (MvRatFunc s k') a) =
      algebraMap k (MvRatFunc s k) (e.symm a) := by
    rw [IsScalarTower.algebraMap_apply k' (MvPolynomial ↥s k') (MvRatFunc ↥s k'),
      IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsScalarTower.algebraMap_apply k (MvPolynomial ↥s k) (MvRatFunc ↥s k)]
    congr 1
    simp [MvPolynomial.algebraMap_eq]
  change E (ψ (μ (algebraMap k' (MvRatFunc s k') a))) = _
  rw [h1, ψ.commutes, hE, e.apply_symm_apply]

/-- Localising at an element `a ∉ 𝔭` maps `𝔭` to a prime which contracts back to `𝔭`. -/
private theorem isPrime_map_away_and_comap_eq {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    {a : R} (ha : a ∉ p) :
    (p.map (algebraMap R (Localization.Away a))).IsPrime ∧
      (p.map (algebraMap R (Localization.Away a))).comap (algebraMap R (Localization.Away a)) =
        p := by
  have h : Disjoint (Submonoid.powers a : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    rintro _ ⟨j, rfl⟩ h
    exact ha (Ideal.IsPrime.mem_of_pow_mem ‹_› j h)
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) _ p ‹_› h,
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) _ ‹_› h⟩

namespace Algebra

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

/-- The residue field map of a composite of algebra maps is the composite of the residue field
maps. -/
private theorem residueField_map_comp {A : Type*} [CommRing A] [Algebra R A] [Algebra T A]
    [IsScalarTower R T A] (p : Ideal R) [p.IsPrime] (P : Ideal T) [P.IsPrime]
    (Q : Ideal A) [Q.IsPrime] (h₁ : p = P.comap (algebraMap R T))
    (h₂ : P = Q.comap (algebraMap T A)) (h₃ : p = Q.comap (algebraMap R A)) :
    (Ideal.ResidueField.map P Q (algebraMap T A) h₂).comp
        (Ideal.ResidueField.map p P (algebraMap R T) h₁) =
      Ideal.ResidueField.map p Q (algebraMap R A) h₃ := by
  refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun r => ?_)
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap,
    IsScalarTower.algebraMap_apply R T A]

/-- Localising at an element outside a prime does not change the residue field: the induced map
`κ(𝔭) → κ(𝔭 R_a)` is bijective. -/
private theorem bijective_residueField_map_localizationAway (a : R) (p : Ideal R) [p.IsPrime]
    (P : Ideal (Localization.Away a)) [P.IsPrime]
    (h : p = P.comap (algebraMap R (Localization.Away a))) :
    Function.Bijective (Ideal.ResidueField.map p P (algebraMap R (Localization.Away a)) h) :=
  RingHom.SurjectiveOnStalks.residueFieldMap_bijective
    (RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers a) _) p P h

/-- **Stacks 0520, with the residue field clause.** Let `R → T` be of finite type and let
`𝔮 ⊂ T` be a prime lying over `𝔭 ⊂ R` with `dim_𝔮(T/R) = n`. Then there are `a ∉ 𝔭`, `b ∉ 𝔮`
and a quasi-finite `R`-algebra map `Φ : R_a[x_1, …, x_n] → T_b` such that the contraction `Q`
of `𝔮 T_b` along `Φ` is a prime lying over `𝔭` whose residue field is a purely transcendental
extension of `κ(𝔭)`. -/
theorem exists_quasiFinite_mvPolynomial_away_purelyTranscendental
    [Algebra.FiniteType R T] (p : Ideal R) [p.IsPrime] (q : Ideal T) [q.IsPrime] [q.LiesOver p]
    {n : ℕ} (hn : Algebra.relativeDimensionAt R q = n) :
    ∃ a ∉ p, ∃ b ∉ q, ∃ Φ : MvPolynomial (Fin n) (Localization.Away a) →+* Localization.Away b,
      ∃ Q : PrimeSpectrum (MvPolynomial (Fin n) (Localization.Away a)),
        Φ.comp (C.comp (algebraMap R (Localization.Away a))) =
            algebraMap R (Localization.Away b) ∧
          Φ.FiniteType ∧ Φ.QuasiFinite ∧
          Q.asIdeal = (q.map (algebraMap T (Localization.Away b))).comap Φ ∧
          ∃ hQp : p = Q.asIdeal.comap (C.comp (algebraMap R (Localization.Away a))),
            letI : Algebra p.ResidueField Q.asIdeal.ResidueField :=
              (Ideal.ResidueField.map p Q.asIdeal _ hQp).toAlgebra
            PurelyTranscendental p.ResidueField Q.asIdeal.ResidueField := by
  classical
  obtain ⟨r, hr⟩ := Algebra.exists_trdeg_residueField_eq_natCast p q
  obtain ⟨a, ha, b, hb, Φ, hcomm, hft, hqf, hcomap⟩ :=
    Algebra.exists_quasiFinite_mvPolynomial_away_comap_map_eq p q hn hr
  obtain ⟨hPprime, hPp⟩ := isPrime_map_away_and_comap_eq p ha
  set A := Localization.Away a
  set P : Ideal A := p.map (algebraMap R A)
  set s : Set (Fin n) := {i : Fin n | r ≤ (i : ℕ)}
  have hQprime : (Ideal.map C P ⊔ Ideal.span (X '' s)).IsPrime :=
    MvPolynomial.isPrime_mapC_sup_span_X_image P s
  have hCP : (Ideal.map C P ⊔ Ideal.span (X '' s)).comap
      (C : A →+* MvPolynomial (Fin n) A) = P :=
    MvPolynomial.comap_C_mapC_sup_span_X_image P s
  have hQp : p = (Ideal.map C P ⊔ Ideal.span (X '' s)).comap
      (C.comp (algebraMap R A)) := by
    rw [← Ideal.comap_comap, hCP, hPp]
  have hliesover : (Ideal.map C P ⊔ Ideal.span (X '' s)).LiesOver P := ⟨hCP.symm⟩
  have hpt : PurelyTranscendental P.ResidueField
      (Ideal.map C P ⊔ Ideal.span (X '' s)).ResidueField :=
    MvPolynomial.purelyTranscendental_residueField_mapC_sup_span_X_image P s _ rfl
      fun c => by
        rw [algebraMap_residueFieldAlgebra,
          Ideal.ResidueField.map_algebraMap, MvPolynomial.algebraMap_eq]
  let eA : p.ResidueField ≃+* P.ResidueField :=
    RingEquiv.ofBijective _ (bijective_residueField_map_localizationAway a p P hPp.symm)
  let instAlg : Algebra p.ResidueField (Ideal.map C P ⊔ Ideal.span (X '' s)).ResidueField :=
    (Ideal.ResidueField.map p _ _ hQp).toAlgebra
  have hcompat : ∀ z : P.ResidueField,
      (RingEquiv.refl (Ideal.map C P ⊔ Ideal.span (X '' s)).ResidueField)
          (algebraMap P.ResidueField (Ideal.map C P ⊔ Ideal.span (X '' s)).ResidueField z) =
        @algebraMap p.ResidueField _ _ _ instAlg (eA.symm z) := by
    intro z
    obtain ⟨u, rfl⟩ := eA.surjective z
    rw [RingEquiv.symm_apply_apply]
    change Ideal.ResidueField.map P _ (algebraMap A (MvPolynomial (Fin n) A)) _
        (Ideal.ResidueField.map p P (algebraMap R A) hPp.symm u) =
      Ideal.ResidueField.map p _ _ hQp u
    exact RingHom.congr_fun (Algebra.residueField_map_comp (R := R) (T := A)
      (A := MvPolynomial (Fin n) A) p P _ hPp.symm hCP.symm hQp) u
  exact ⟨a, ha, b, hb, Φ, ⟨Ideal.map C P ⊔ Ideal.span (X '' s), hQprime⟩,
    hcomm, hft, hqf, hcomap.symm, hQp,
    @purelyTranscendental_of_ringEquiv _ _ _ _ _ _ _ _ _ instAlg eA.symm (.refl _) hcompat hpt⟩

end Algebra

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- The residue field map of a morphism, read at two equal points and composed with the
canonical isomorphisms transporting the point of the target, is the same map. -/
theorem residueFieldCongr_hom_residueFieldMap {X Y : Scheme.{u}} (g : X ⟶ Y) {x₁ x₂ : X}
    (e : x₁ = x₂) {y : Y} (h₁ : g x₁ = y) (h₂ : g x₂ = y) (w : Y.residueField y) :
    (X.residueFieldCongr e).hom (g.residueFieldMap x₁ ((Y.residueFieldCongr h₁).inv w)) =
      g.residueFieldMap x₂ ((Y.residueFieldCongr h₂).inv w) := by
  subst e
  rw [Scheme.residueFieldCongr_refl]
  rfl

/-- Affine `n`-space over a basic open `D(a)` of an affine open `U ⊆ S` is smooth of relative
dimension `n` over `S`. -/
theorem smoothOfRelativeDimension_specMap_away_C_comp_fromSpec {S : Scheme.{u}} {U : S.Opens}
    (hU : IsAffineOpen U) (a : Γ(S, U)) (n : ℕ) :
    SmoothOfRelativeDimension n
      (Spec.map ((CommRingCat.ofHom (algebraMap Γ(S, U) (Localization.Away a)) :
          Γ(S, U) ⟶ CommRingCat.of (Localization.Away a)) ≫
        CommRingCat.ofHom (C : Localization.Away a →+* MvPolynomial (Fin n) _)) ≫
          hU.fromSpec) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : SmoothOfRelativeDimension 0
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) (Localization.Away a)) :
        Γ(S, U) ⟶ CommRingCat.of (Localization.Away a)) ≫ hU.fromSpec) := inferInstance
  have := smoothOfRelativeDimension_specMap_C (Localization.Away a) n
  have := SmoothOfRelativeDimension.comp_relativeDimension_zero n
    (Spec.map (CommRingCat.ofHom (C : Localization.Away a →+* MvPolynomial (Fin n) _)))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) (Localization.Away a)) :
      Γ(S, U) ⟶ CommRingCat.of (Localization.Away a)) ≫ hU.fromSpec)
  rwa [← Category.assoc, ← Spec.map_comp] at this

/-- A factorisation `φ ≫ Φ = f.appLE U V hVU ≫ β` of ring maps over affine opens `U` and `V`
gives the corresponding commuting square of schemes. -/
theorem specMap_fromSpec_comp_eq_of_comp_eq {X S : Scheme.{u}} (f : X ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    {A B : CommRingCat.{u}} (φ : Γ(S, U) ⟶ A) (Φ : A ⟶ B) (β : Γ(X, V) ⟶ B)
    (h : φ ≫ Φ = f.appLE U V hVU ≫ β) :
    (Spec.map β ≫ hV.fromSpec) ≫ f = Spec.map Φ ≫ Spec.map φ ≫ hU.fromSpec :=
  calc (Spec.map β ≫ hV.fromSpec) ≫ f = Spec.map β ≫ hV.fromSpec ≫ f := Category.assoc _ _ _
    _ = Spec.map β ≫ Spec.map (f.appLE U V hVU) ≫ hU.fromSpec := by
          rw [← hU.SpecMap_appLE_fromSpec f hV hVU]
    _ = Spec.map (f.appLE U V hVU ≫ β) ≫ hU.fromSpec := by
          rw [← Category.assoc, ← Spec.map_comp]
    _ = Spec.map Φ ≫ Spec.map φ ≫ hU.fromSpec := by rw [← h, Spec.map_comp, Category.assoc]

/-- Pure transcendence of the residue field extension of a ring map `φ : Γ(S, U) ⟶ A` at primes
`𝔭 = φ⁻¹ Q` passes to the residue field extension of `Spec A → S` at `Q`. -/
theorem purelyTranscendental_residueField_specMap_comp_fromSpec {S : Scheme.{u}} {U : S.Opens}
    (hU : IsAffineOpen U) {A : CommRingCat.{u}} (φ : Γ(S, U) ⟶ A) (pp : PrimeSpectrum Γ(S, U))
    (Q : PrimeSpectrum A) (hQp : pp.asIdeal = Q.asIdeal.comap φ.hom) {y₀ : Spec A}
    (hQy : (Q : Spec A) = y₀) {s : S} (hy : (Spec.map φ ≫ hU.fromSpec) y₀ = s)
    (hpt : letI := (Ideal.ResidueField.map pp.asIdeal Q.asIdeal φ.hom hQp).toAlgebra
      PurelyTranscendental pp.asIdeal.ResidueField Q.asIdeal.ResidueField) :
    letI := (((S.residueFieldCongr hy).inv ≫
      (Spec.map φ ≫ hU.fromSpec).residueFieldMap y₀).hom).toAlgebra
    PurelyTranscendental (S.residueField s) ((Spec A).residueField y₀) := by
  have hpt' : (Spec.map φ).base Q = pp := PrimeSpectrum.ext hQp.symm
  have hppy : pp = (Spec.map φ).base y₀ :=
    hpt'.symm.trans (congrArg (fun z => (Spec.map φ).base z) hQy)
  have hU2 : hU.fromSpec ((Spec.map φ).base y₀) = s := hy
  have hUpp : hU.fromSpec pp = s := by rwa [hppy]
  have hUopen : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  set Λ : S.residueField s ⟶ (Spec Γ(S, U)).residueField pp :=
    (S.residueFieldCongr hUpp).inv ≫ hU.fromSpec.residueFieldMap pp with hΛ
  have : IsIso (hU.fromSpec.residueFieldMap pp) :=
    (fun _ => inferInstance : ∀ p' : ↥(Spec Γ(S, U)), IsIso (hU.fromSpec.residueFieldMap p')) pp
  have hΛiso : IsIso Λ := by
    rw [hΛ]
    infer_instance
  set eR : pp.asIdeal.ResidueField ≃+* ↥(S.residueField s) :=
    ((Scheme.Spec.residueFieldIso Γ(S, U) pp).symm ≪≫
      (asIso Λ).symm).commRingCatIsoToRingEquiv
  set eM : Q.asIdeal.ResidueField ≃+* ↥((Spec A).residueField y₀) :=
    ((Scheme.Spec.residueFieldIso A Q).symm ≪≫
      (Spec A).residueFieldCongr hQy).commRingCatIsoToRingEquiv
  let instAlg1 : Algebra pp.asIdeal.ResidueField Q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map pp.asIdeal Q.asIdeal _ hQp).toAlgebra
  let instAlg2 : Algebra ↥(S.residueField s) ↥((Spec A).residueField y₀) :=
    (((S.residueFieldCongr hy).inv ≫ (Spec.map φ ≫ hU.fromSpec).residueFieldMap y₀).hom).toAlgebra
  have hcompat : ∀ z : pp.asIdeal.ResidueField,
      eM (@algebraMap _ _ _ _ instAlg1 z) = @algebraMap _ _ _ _ instAlg2 (eR z) := by
    intro z
    obtain ⟨w, rfl⟩ := eR.symm.surjective z
    rw [RingEquiv.apply_symm_apply]
    have hbridge := residueFieldMap_specMap_apply_of_eq φ pp Q hQp hpt' (Λ w)
    have hcompmap := Scheme.residueFieldMap_comp (f := Spec.map φ) hU.fromSpec y₀
    have hfinal : @algebraMap _ _ _ _ instAlg2 w =
        (Spec.map φ).residueFieldMap y₀
          (hU.fromSpec.residueFieldMap ((Spec.map φ) y₀) ((S.residueFieldCongr hy).inv w)) :=
      congrArg (fun m : S.residueField ((Spec.map φ ≫ hU.fromSpec) y₀) ⟶
          (Spec A).residueField y₀ => m ((S.residueFieldCongr hy).inv w)) hcompmap
    rw [hfinal]
    calc eM (@algebraMap _ _ _ _ instAlg1 (eR.symm w))
        = ((Spec A).residueFieldCongr hQy).hom
            ((Spec.map φ).residueFieldMap Q
              (((Spec Γ(S, U)).residueFieldCongr hpt').inv (Λ w))) :=
          congrArg _ ((congrArg (fun u => (Scheme.Spec.residueFieldIso A Q).inv u)
            hbridge).symm.trans ((Scheme.Spec.residueFieldIso A Q).hom_inv_id_apply _))
      _ = (Spec.map φ).residueFieldMap y₀
            (((Spec Γ(S, U)).residueFieldCongr hppy.symm).inv (Λ w)) :=
          residueFieldCongr_hom_residueFieldMap (Spec.map φ) hQy hpt' hppy.symm (Λ w)
      _ = (Spec.map φ).residueFieldMap y₀
            (hU.fromSpec.residueFieldMap ((Spec.map φ) y₀) ((S.residueFieldCongr hy).inv w)) := by
          refine congrArg _ ?_
          exact residueFieldCongr_hom_residueFieldMap hU.fromSpec hppy hUpp hU2 w
  exact @purelyTranscendental_of_ringEquiv _ _ _ _ _ _ _ _ instAlg1 instAlg2 eR eM hcompat hpt

/-- **The factorisation of Stacks 052E over affine opens.** The conclusion of
`exists_quasiFinite_over_affineSpace`, for affine opens `U ⊆ S` and `V ⊆ f⁻¹ U` with `x ∈ V`. -/
theorem exists_quasiFinite_over_affineSpace_of_isAffineOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) (n : ℕ)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n) {U : S.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (hxU : f x ∈ U) (hxV : x ∈ V) :
    ∃ (X₀ Y₀ : Scheme.{u}) (ι : X₀ ⟶ X) (π₀ : X₀ ⟶ Y₀) (hY : Y₀ ⟶ S) (x₀ : X₀),
      IsOpenImmersion ι ∧ ι x₀ = x ∧ SmoothOfRelativeDimension n hY ∧
      LocallyOfFiniteType π₀ ∧ IsIsolatedPoint (π₀.asFiber x₀) ∧
      ι ≫ f = π₀ ≫ hY ∧
      ∃ hy : hY (π₀ x₀) = f x,
        letI : Algebra (S.residueField (f x)) (Y₀.residueField (π₀ x₀)) :=
          (((S.residueFieldCongr hy).inv ≫ hY.residueFieldMap (π₀ x₀)).hom).toAlgebra
        PurelyTranscendental (S.residueField (f x)) (Y₀.residueField (π₀ x₀)) := by
  classical
  have hfiniteType : (f.appLE U V hVU).hom.FiniteType := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have hlies : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver
      (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal :=
    ⟨congr(($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV (f := f))).1).symm⟩
  have hdim' := relativeDimensionAt_appLE_eq_of_fiber_dim f hU hV hVU hxV hdim
  obtain ⟨a, ha, b, hb, Φ, Q, hcomm, hft, hqf, hQdef, hQp, hpt⟩ :=
    Algebra.exists_quasiFinite_mvPolynomial_away_purelyTranscendental
      (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal hdim'
  obtain ⟨hQBprime, hQBq⟩ := isPrime_map_away_and_comap_eq (hV.primeIdealOf ⟨x, hxV⟩).asIdeal hb
  set β : Γ(X, V) ⟶ CommRingCat.of (Localization.Away b) :=
    CommRingCat.ofHom (algebraMap ↥Γ(X, V) (Localization.Away b))
  set α : Γ(S, U) ⟶ CommRingCat.of (Localization.Away a) :=
    CommRingCat.ofHom (algebraMap ↥Γ(S, U) (Localization.Away a))
  set γ : CommRingCat.of (Localization.Away a) ⟶
      CommRingCat.of (MvPolynomial (Fin n) (Localization.Away a)) := CommRingCat.ofHom C
  set Φ' : CommRingCat.of (MvPolynomial (Fin n) (Localization.Away a)) ⟶
      CommRingCat.of (Localization.Away b) := CommRingCat.ofHom Φ
  set ι : Spec (CommRingCat.of (Localization.Away b)) ⟶ X := Spec.map β ≫ hV.fromSpec with hι
  set hYm : Spec (CommRingCat.of (MvPolynomial (Fin n) (Localization.Away a))) ⟶ S :=
    Spec.map (α ≫ γ) ≫ hU.fromSpec
  set x₀ : PrimeSpectrum (Localization.Away b) :=
    ⟨(hV.primeIdealOf ⟨x, hxV⟩).asIdeal.map (algebraMap ↥Γ(X, V) (Localization.Away b)), hQBprime⟩
  have hιx : ι x₀ = x := by
    have h1 : (Spec.map β).base x₀ = hV.primeIdealOf ⟨x, hxV⟩ := PrimeSpectrum.ext hQBq
    change hV.fromSpec ((Spec.map β).base x₀) = x
    rw [h1]
    exact hV.fromSpec_primeIdealOf _
  have hιopen : IsOpenImmersion ι := by
    have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
    rw [hι]
    infer_instance
  have hsq : ι ≫ f = Spec.map Φ' ≫ hYm := by
    refine specMap_fromSpec_comp_eq_of_comp_eq f hU hV hVU (α ≫ γ) Φ' β (CommRingCat.hom_ext ?_)
    change Φ.comp ((MvPolynomial.C).comp (algebraMap ↥Γ(S, U) (Localization.Away a))) =
      (algebraMap ↥Γ(X, V) (Localization.Away b)).comp (f.appLE U V hVU).hom
    rw [hcomm, ← (f.appLE U V hVU).hom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_eq]
  have hπft : LocallyOfFiniteType (Spec.map Φ') :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hft
  have : LocallyQuasiFinite (Spec.map Φ') :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr hqf
  have hy : hYm ((Spec.map Φ') x₀) = f x :=
    (congrArg (fun g : Spec (CommRingCat.of (Localization.Away b)) ⟶ S => g x₀) hsq).symm.trans
      (congrArg (fun z : ↥X => f z) hιx)
  exact ⟨_, _, ι, Spec.map Φ', hYm, x₀, hιopen, hιx,
    smoothOfRelativeDimension_specMap_away_C_comp_fromSpec hU a n, hπft,
    (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber).mp ((Spec.map Φ').quasiFiniteAt x₀),
    hsq, hy, purelyTranscendental_residueField_specMap_comp_fromSpec hU (α ≫ γ) _ Q hQp
      (y₀ := (Spec.map Φ') x₀) (PrimeSpectrum.ext hQdef) hy hpt⟩

/-- **The factorisation of Stacks 052E through affine space.** A morphism `f : X ⟶ S` locally of
finite type whose fibre through `x` has local dimension `n` factors, on an open neighbourhood
`X₀` of `x`, as a morphism `π₀` which is locally of finite type and has `x` isolated in its
fibre, followed by a morphism `Y₀ ⟶ S` smooth of relative dimension `n`; and the residue field
of `Y₀` at `π₀ x` is a purely transcendental extension of the residue field of `S` at `f x`. -/
theorem exists_quasiFinite_over_affineSpace
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) (n : ℕ)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n) :
    ∃ (X₀ Y₀ : Scheme.{u}) (ι : X₀ ⟶ X) (π₀ : X₀ ⟶ Y₀) (hY : Y₀ ⟶ S) (x₀ : X₀),
      IsOpenImmersion ι ∧ ι x₀ = x ∧ SmoothOfRelativeDimension n hY ∧
      LocallyOfFiniteType π₀ ∧ IsIsolatedPoint (π₀.asFiber x₀) ∧
      ι ≫ f = π₀ ≫ hY ∧
      ∃ hy : hY (π₀ x₀) = f x,
        letI : Algebra (S.residueField (f x)) (Y₀.residueField (π₀ x₀)) :=
          (((S.residueFieldCongr hy).inv ≫ hY.residueFieldMap (π₀ x₀)).hom).toAlgebra
        PurelyTranscendental (S.residueField (f x)) (Y₀.residueField (π₀ x₀)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  exact exists_quasiFinite_over_affineSpace_of_isAffineOpen f x n hdim hU hV hVU hxU hxV

end AlgebraicGeometry
