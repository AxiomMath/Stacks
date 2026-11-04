module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Etale.LiftUnitsIdempotents
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization

/-!
# Maps from a finite type algebra to a henselization (Stacks 0AKJ)

Let `C` be a commutative ring and `J ⊆ C` an ideal. The henselization `C^h` of the pair
`(C, J)` is a filtered colimit of étale `C`-algebras and satisfies `C / Jⁿ ≅ C^h / (JC^h)ⁿ`
for every `n`, so the `J`-adic completion of `C` is canonically the `JC^h`-adic completion
of `C^h`; composing with the canonical map of `C^h` into its own completion gives the
canonical `C`-algebra map `C^h → C^∧` of the source.

The second half of the source's statement is that every map of a finite type `A`-algebra `B`
into `C^h` factors through an étale `C`-algebra inducing an isomorphism on the closed fibre.
This is proved here. Over a Noetherian base `B` is finitely presented, so the map
`C ⊗_A B → C^h` it determines factors through one étale stage `E` of the colimit
(Stacks 07C3). The stage need not have `C / J ≅ E / JE`; the retraction
`E → C^h → C^h / JC^h ≅ C / J` decomposes `E / JE` as `C / J × D` (Stacks 0EM1), and
localizing `E` at a lift `h` of the idempotent `(1, 0)` kills the second factor. The
localization still receives `B`, and still maps to `C^h` because `h` becomes a unit there:
its class mod `JC^h` is `1`, and `JC^h` lies in the Jacobson radical of the henselian pair.

## Main definitions

* `Rig.henselizationToAdicCompletion`: the canonical map of the henselization of `(C, J)`
  into the `J`-adic completion of `C`, with its structural-map specification.

## Main results

* `Rig.exists_etale_factorization_algHom_henselization`: **Stacks 0AKJ**, étale
  factorization.

## Implementation notes

`Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective`, from
`StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties`, supplies the bijectivity of the
induced map of adic completions. `Rig.toAdicCompletionOfBijective` lives in
`StacksFrontier.RingTheory.Henselian.Pair.Henselization`, which proves Stacks 0AGU and 0AGV.

The étale algebra produced by the factorization is a localization of a stage of the colimit,
hence lives in the universe of `C`; it is lifted into the universe of the statement with
`ULift`.

## References

* [Stacks Project, Tag 0AKJ](https://stacks.math.columbia.edu/tag/0AKJ)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Rig

/-! ### The canonical map of the henselization into the completion -/

/-- The canonical map from the henselization of `(C, J)` to its `J`-adic
completion, together with its structural-map compatibility. -/
public noncomputable def henselizationToAdicCompletion
    (C : Type w) [CommRing C] (J : Ideal C) :
    { f : (henselization C J : Type w) →ₐ[C] AdicCompletion J C //
      f.toRingHom.comp (algebraMap C (henselization C J : Type w)) =
        algebraMap C (AdicCompletion J C) } :=
  let f : (henselization C J : Type w) →ₐ[C] AdicCompletion J C :=
    toAdicCompletionOfBijective J
      (Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective _ J
        (flat_and_bijective_quotientMap_pow_of_ind_etale C J (henselization C J : Type w)
          (ind_henselization C J) (bijective_quotientMap_henselization C J)).2)
  ⟨f, RingHom.ext fun c ↦ f.commutes c⟩

/-! ### Factorization through an étale neighbourhood of the closed fibre -/

/-- **Stacks 07C3.** Ind-étaleness in the form of the factorization criterion: every map
into `B` from a finitely presented `A`-algebra factors through an étale `A`-algebra.
Replayed from the private development of
`StacksFrontier.RingTheory.Etale.IndEtaleUniverse`. -/
public theorem ind_etale_factorization {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    (hind : (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A B))
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.FinitePresentation A C]
    (f : C →ₐ[A] B) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra A E),
      Algebra.Etale A E ∧ ∃ (g : C →ₐ[A] E) (h : E →ₐ[A] B), h.comp g = f := by
  rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk,
    CommRingCat.ind_under_iff_exists_factorization _
      (fun (C : Under (CommRingCat.of A)) (h : CommRingCat.etale.underObj C) =>
        (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).2.2)] at hind
  obtain ⟨E, g, h, he, het⟩ := hind
    (Under.mk (CommRingCat.ofHom (algebraMap A C)))
    (show (algebraMap A C).FinitePresentation from
      RingHom.finitePresentation_algebraMap.mpr inferInstance)
    (Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext x; exact f.commutes x))
  let := E.hom.hom.toAlgebra
  refine ⟨E.right, inferInstance, inferInstance, RingHom.etale_algebraMap.mp het,
    ⟨g.right.hom, fun x => congr($(Under.w g).hom x)⟩,
    ⟨h.right.hom, fun x => congr($(Under.w h).hom x)⟩, ?_⟩
  ext x
  exact congr($(congrArg Under.Hom.right he).hom x)

/-- An `A`-algebra map of a finitely presented `A`-algebra into an ind-étale `C`-algebra
factors through one étale stage of the colimit. -/
private theorem exists_etale_stage
    {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B]
    {C : Type w} [CommRing C] [Algebra A C]
    {H : Type w} [CommRing H] [Algebra C H] [Algebra A H] [IsScalarTower A C H]
    (hind : (CommAlgCat.etale.{w} C).ind.{w} (CommAlgCat.of C H))
    (f : B →ₐ[A] H) :
    ∃ (E : Type w) (_ : CommRing E) (_ : Algebra C E) (_ : Algebra A E)
      (_ : IsScalarTower A C E), Algebra.Etale C E ∧
      ∃ (g : B →ₐ[A] E) (k : E →ₐ[C] H), (k.restrictScalars A).comp g = f := by
  classical
  have : Algebra.FinitePresentation C (C ⊗[A] B) := Algebra.FinitePresentation.baseChange C
  have : Small.{w} (C ⊗[A] B) := Algebra.FiniteType.small (R := C)
  let eT : Shrink.{w} (C ⊗[A] B) ≃ₐ[C] (C ⊗[A] B) := Shrink.algEquiv C (C ⊗[A] B)
  have : Algebra.FinitePresentation C (Shrink.{w} (C ⊗[A] B)) :=
    Algebra.FinitePresentation.equiv eT.symm
  let fX : (C ⊗[A] B) →ₐ[C] H :=
    Algebra.TensorProduct.lift (Algebra.ofId C H) f (fun _ _ => Commute.all _ _)
  obtain ⟨E, instE, instCE, hEet, g0, k0, hk0⟩ :=
    ind_etale_factorization hind (Shrink.{w} (C ⊗[A] B)) (fX.comp eT.toAlgHom)
  let : Algebra A E := ((algebraMap C E).comp (algebraMap A C)).toAlgebra
  have htow : IsScalarTower A C E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let incl : B →ₐ[A] (C ⊗[A] B) := Algebra.TensorProduct.includeRight
  let gB : B →ₐ[A] E :=
    { toRingHom := g0.toRingHom.comp ((eT.symm.toAlgHom.toRingHom).comp incl.toRingHom)
      commutes' := fun a => by
        show g0 (eT.symm (incl (algebraMap A B a))) = algebraMap A E a
        rw [incl.commutes, IsScalarTower.algebraMap_apply A C (C ⊗[A] B),
          eT.symm.commutes, g0.commutes]
        exact (IsScalarTower.algebraMap_apply A C E a).symm }
  refine ⟨E, instE, instCE, inferInstance, htow, hEet, gB, k0, ?_⟩
  ext b
  exact (AlgHom.congr_fun hk0 (eT.symm (incl b))).trans (by simp [fX, incl])

/-- If `h * (a - b) ∈ I`, then `b - a` lies in the extension of `I` to the localization of `E`
away from `h`. -/
public theorem sub_mem_map_away_of_mul_sub_mem {E : Type*} [CommRing E] {I : Ideal E}
    {h a b : E} (hab : h * (a - b) ∈ I) :
    algebraMap E (Localization.Away h) b - algebraMap E (Localization.Away h) a
      ∈ I.map (algebraMap E (Localization.Away h)) := by
  have hmem := Ideal.mem_map_of_mem (algebraMap E (Localization.Away h)) hab
  rw [map_mul, map_sub, Ideal.unit_mul_mem_iff_mem _
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h)] at hmem
  simpa using neg_mem hmem

/-- Let `σ : E →ₐ[C] C ⧸ J` and `h : E` with `σ h = 1`, such that `h * (a - c) ∈ JE` whenever
`c ≡ σ a` modulo `J`. Then `C ⧸ J → E_h ⧸ JE_h` is bijective. -/
public theorem quotientMap_away_bijective_of_section {C : Type*} [CommRing C] (J : Ideal C)
    {E : Type*} [CommRing E] [Algebra C E] (σ : E →ₐ[C] C ⧸ J) {h : E} (hσh : σ h = 1)
    (hkey : ∀ (a : E) (c : C), Ideal.Quotient.mk J c = σ a →
      h * (a - algebraMap C E c) ∈ J.map (algebraMap C E)) :
    Function.Bijective (Ideal.quotientMap (J.map (algebraMap C (Localization.Away h)))
      (algebraMap C (Localization.Away h)) Ideal.le_comap_map) := by
  let gS : Localization.Away h →ₐ[C] C ⧸ J :=
    IsLocalization.Away.liftAlgHom h (f := σ) (hσh ▸ isUnit_one)
  have hgS (a : E) : gS (algebraMap E (Localization.Away h) a) = σ a :=
    IsLocalization.lift_eq _ a
  refine Ideal.quotientMap_bijective_of_lift (algebraMap C (Localization.Away h)) gS.toRingHom
    gS.commutes ?_
  · have key : (Ideal.quotientMap (J.map (algebraMap C (Localization.Away h)))
          (algebraMap C (Localization.Away h)) Ideal.le_comap_map).comp gS.toRingHom
        = Ideal.Quotient.mk (J.map (algebraMap C (Localization.Away h))) := by
      refine IsLocalization.ringHom_ext (Submonoid.powers h) ?_
      ext a
      show Ideal.quotientMap (J.map (algebraMap C (Localization.Away h)))
            (algebraMap C (Localization.Away h)) Ideal.le_comap_map
            (gS (algebraMap E (Localization.Away h) a))
          = Ideal.Quotient.mk _ (algebraMap E (Localization.Away h) a)
      rw [hgS]
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (σ a)
      rw [← hc, Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
        IsScalarTower.algebraMap_apply C E (Localization.Away h),
        IsScalarTower.algebraMap_eq C E (Localization.Away h), ← Ideal.map_map]
      exact sub_mem_map_away_of_mul_sub_mem (hkey a c hc)
    exact RingHom.congr_fun key

/-- If `e : E ⧸ JE ≃ₐ[C ⧸ J] (C ⧸ J) × D` has first component `σ` and sends `h` to `(1, 0)`,
then `h * (a - c) ∈ JE` whenever `c ≡ σ a` modulo `J`. -/
public theorem mul_sub_mem_map_of_algEquiv_prod {C : Type*} [CommRing C] {J : Ideal C}
    {E : Type*} [CommRing E] [Algebra C E] {σ : E →ₐ[C] C ⧸ J} {D : Type*} [CommRing D]
    [Algebra (C ⧸ J) D] {e : (E ⧸ J.map (algebraMap C E)) ≃ₐ[C ⧸ J] (C ⧸ J) × D}
    (he : ∀ x, (e (Ideal.Quotient.mk (J.map (algebraMap C E)) x)).1 = σ x) {h : E}
    (hem : e (Ideal.Quotient.mk (J.map (algebraMap C E)) h) = (1, 0)) {a : E} {c : C}
    (hc : Ideal.Quotient.mk J c = σ a) :
    h * (a - algebraMap C E c) ∈ J.map (algebraMap C E) := by
  have hmkc : Ideal.Quotient.mk (J.map (algebraMap C E)) (algebraMap C E c)
      = algebraMap (C ⧸ J) (E ⧸ (J.map (algebraMap C E))) (Ideal.Quotient.mk J c) :=
    (Ideal.quotientMap_mk ..).symm
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply e.injective
  rw [map_zero, map_mul, map_sub, map_mul, map_sub, hem, hmkc, e.commutes]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_mul, Prod.fst_sub, Prod.fst_zero, one_mul]
    rw [he a, ← hc]
    simp
  · simp

/-- An étale `C`-algebra mapping to a henselization of `(C, J)` may be localized so that it
induces an isomorphism modulo `J`, without losing the map. -/
private theorem exists_localization_quotient_iso
    {C : Type w} [CommRing C] (J : Ideal C)
    {H : Type w} [CommRing H] [Algebra C H]
    (hquot : Function.Bijective (Ideal.quotientMap (J.map (algebraMap C H))
      (algebraMap C H) Ideal.le_comap_map))
    (hhens : HenselianPair H (J.map (algebraMap C H)))
    (E : Type w) [CommRing E] [Algebra C E] [Algebra.Etale C E]
    (k0 : E →ₐ[C] H) :
    ∃ (h : E) (k : Localization.Away h →ₐ[C] H),
      Function.Bijective (Ideal.quotientMap (J.map (algebraMap C (Localization.Away h)))
        (algebraMap C (Localization.Away h)) Ideal.le_comap_map) ∧
      k.comp (IsScalarTower.toAlgHom C E (Localization.Away h)) = k0 := by
  classical
  let qe : (C ⧸ J) ≃+* (H ⧸ J.map (algebraMap C H)) :=
    RingEquiv.ofBijective _ hquot
  have hqe (c : C) : qe (Ideal.Quotient.mk J c)
      = Ideal.Quotient.mk (J.map (algebraMap C H)) (algebraMap C H c) := by
    show Ideal.quotientMap (J.map (algebraMap C H)) (algebraMap C H) Ideal.le_comap_map
        (Ideal.Quotient.mk J c) = _
    exact Ideal.quotientMap_mk ..
  let σ : E →ₐ[C] C ⧸ J :=
    { toRingHom := qe.symm.toRingHom.comp
        ((Ideal.Quotient.mk (J.map (algebraMap C H))).comp k0.toRingHom)
      commutes' := fun c => by
        show qe.symm (Ideal.Quotient.mk (J.map (algebraMap C H)) (k0 (algebraMap C E c)))
            = Ideal.Quotient.mk J c
        rw [k0.commutes, ← hqe, qe.symm_apply_apply] }
  have hσ (a : E) : qe (σ a) = Ideal.Quotient.mk (J.map (algebraMap C H)) (k0 a) :=
    qe.apply_symm_apply _
  obtain ⟨D, instD, instAlgD, e, he⟩ :=
    exists_quotient_algEquiv_prod_of_etale_section C E J σ
  obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective (e.symm (1, 0))
  have hem : e (Ideal.Quotient.mk (J.map (algebraMap C E)) h) = (1, 0) := by
    rw [hh, e.apply_symm_apply]
  have hσh : σ h = 1 := by rw [← he h, hem]
  have hk0h : IsUnit (k0.toRingHom h) := by
    refine Ideal.isUnit_of_sub_one_mem_jacobson_bot (k0 h) (hhens.le_jacobson ?_)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ← hσ h, hσh, map_one, sub_self]
  let k : Localization.Away h →ₐ[C] H := IsLocalization.Away.liftAlgHom h (f := k0) hk0h
  refine ⟨h, k, quotientMap_away_bijective_of_section J σ hσh
    fun _ _ hc => mul_sub_mem_map_of_algEquiv_prod he hem hc, ?_⟩
  ext a
  exact IsLocalization.lift_eq _ a

/-- Bijectivity of `C ⧸ J → S ⧸ JS` transfers along a `C`-algebra equivalence `S ≃ₐ[C] T`. -/
public theorem quotientMap_bijective_of_algEquiv {C S T : Type*} [CommRing C] [CommRing S]
    [CommRing T] [Algebra C S] [Algebra C T] (J : Ideal C) (e : S ≃ₐ[C] T)
    (hS : Function.Bijective (Ideal.quotientMap (J.map (algebraMap C S))
      (algebraMap C S) Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap (J.map (algebraMap C T))
      (algebraMap C T) Ideal.le_comap_map) := by
  let qq := Ideal.quotientEquivAlg (J.map (algebraMap C S)) (J.map (algebraMap C T)) e (by
    rw [Ideal.map_map]
    exact congrArg (fun f : C →+* T => J.map f) e.toAlgHom.comp_algebraMap.symm)
  have hq : Ideal.quotientMap (J.map (algebraMap C T)) (algebraMap C T) Ideal.le_comap_map =
      qq.toRingEquiv.toRingHom.comp
        (Ideal.quotientMap (J.map (algebraMap C S)) (algebraMap C S) Ideal.le_comap_map) := by
    ext c
    exact congrArg (Ideal.Quotient.mk _) (e.commutes c).symm
  rw [hq, RingHom.coe_comp]
  exact qq.bijective.comp hS

/-- The two halves above, combined and lifted into the universe of the statement. -/
private theorem exists_etale_factorization_aux
    {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B]
    {C : Type w} [CommRing C] [Algebra A C] (J : Ideal C)
    {H : Type w} [CommRing H] [Algebra C H] [Algebra A H] [IsScalarTower A C H]
    (hind : (CommAlgCat.etale.{w} C).ind.{w} (CommAlgCat.of C H))
    (hquot : Function.Bijective (Ideal.quotientMap (J.map (algebraMap C H))
      (algebraMap C H) Ideal.le_comap_map))
    (hhens : HenselianPair H (J.map (algebraMap C H)))
    (f : B →ₐ[A] H) :
    ∃ (Cp : Type (max u v w)) (_ : CommRing Cp) (_ : Algebra C Cp)
      (_ : Algebra A Cp) (_ : IsScalarTower A C Cp) (_ : Algebra.Etale C Cp)
      (g : B →ₐ[A] Cp) (k : Cp →ₐ[C] H),
      Function.Bijective
        (Ideal.quotientMap (J.map (algebraMap C Cp)) (algebraMap C Cp)
          Ideal.le_comap_map) ∧
      (k.restrictScalars A).comp g = f := by
  classical
  obtain ⟨E, instE, instCE, instAE, htowE, hEet, gB, k0, hgk⟩ := exists_etale_stage hind f
  obtain ⟨h, k0', hbij', hkk⟩ := exists_localization_quotient_iso J hquot hhens E k0
  have htow2 : IsScalarTower A C (Localization.Away h) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A E (Localization.Away h),
        IsScalarTower.algebraMap_apply A C E,
        ← IsScalarTower.algebraMap_apply C E (Localization.Away h)]
  let uL : ULift.{max u v, w} (Localization.Away h) ≃ₐ[C] Localization.Away h :=
    ULift.algEquiv
  have hEtL : Algebra.Etale C (ULift.{max u v, w} (Localization.Away h)) :=
    ⟨Algebra.FormallyEtale.of_equiv uL.symm, Algebra.FinitePresentation.equiv uL.symm⟩
  have htowL : IsScalarTower A C (ULift.{max u v, w} (Localization.Away h)) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      congrArg ULift.up (IsScalarTower.algebraMap_apply A C (Localization.Away h) a)
  refine ⟨ULift.{max u v, w} (Localization.Away h), inferInstance, inferInstance,
    inferInstance, htowL, hEtL,
    (uL.symm.toAlgHom.restrictScalars A).comp
      ((IsScalarTower.toAlgHom A E (Localization.Away h)).comp gB),
    k0'.comp uL.toAlgHom, quotientMap_bijective_of_algEquiv J uL.symm hbij', ?_⟩
  ext b
  show k0' (uL (uL.symm (algebraMap E (Localization.Away h) (gB b)))) = f b
  rw [uL.apply_symm_apply]
  exact (AlgHom.congr_fun hkk (gB b)).trans (AlgHom.congr_fun hgk b)

/-- **Stacks Project, Tag 0AKJ (étale factorization).** Every map from a
finite type algebra to the henselization of `(C, IC)` factors through an
étale `C`-algebra whose closed fibre is canonically isomorphic to that of
`C`. -/
@[stacks 0AKJ "étale factorization"]
public lemma exists_etale_factorization_algHom_henselization
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A)
    [CommRing C] [Algebra A C] :
    let H := (henselization C (I.map (algebraMap A C)) : Type w)
    letI : Algebra A H :=
      ((algebraMap C H).comp (algebraMap A C)).toAlgebra
    letI : IsScalarTower A C H :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ f : B →ₐ[A] H,
    ∃ (Cp : Type (max u v w)) (_ : CommRing Cp) (_ : Algebra C Cp)
      (_ : Algebra A Cp) (_ : IsScalarTower A C Cp) (_ : Algebra.Etale C Cp)
      (g : B →ₐ[A] Cp)
      (k : Cp →ₐ[C] H),
      Function.Bijective
        (Ideal.quotientMap ((I.map (algebraMap A C)).map (algebraMap C Cp))
          (algebraMap C Cp) Ideal.le_comap_map) ∧
        (k.restrictScalars A).comp g = f := by
  intro H f
  let : Algebra A H := ((algebraMap C H).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C H := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact exists_etale_factorization_aux (I.map (algebraMap A C))
    (ind_henselization C (I.map (algebraMap A C)))
    (bijective_quotientMap_henselization C (I.map (algebraMap A C)))
    (henselianPair_henselization C (I.map (algebraMap A C))) f

end Rig

end
