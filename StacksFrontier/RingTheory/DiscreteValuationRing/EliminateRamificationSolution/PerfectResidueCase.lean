module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution.AlgClosedResidueExtension

/-!
# Tag 09II from Epp's theorem: formal smoothness transports and the perfect residue field case

Part 2 of the development of Stacks Tag 09II from Epp's theorem (Tag 09F9) in
`StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution`. It contains
transports of adic formal smoothness (`RingHom.FormallySmoothNAdic`) along ring equivalences,
localizations and universe lifts; formal smoothness over a perfect residue field; the fact that a
weak solution is a solution over a perfect residue field; and the cases of Tag 09II in residue
characteristic zero (`exists_finite_extension_isSolution_of_charZero`) and over a perfect residue
field (`exists_finite_extension_isSolution_of_perfectField`).
-/

@[expose] public section

universe uA uB uK uL v uK₁ uL₁ uA₁ uB₁

namespace Stacks.EliminateRamification

open IsLocalRing
open scoped TensorProduct

/-- The adic lifting property is preserved by isomorphisms of local ring maps. -/
theorem formallySmoothNAdic_of_ringEquiv.{w}
    {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsLocalRing B] [IsLocalRing B']
    (f : A →+* B) (f' : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (he : f'.comp eA.toRingHom = eB.toRingHom.comp f)
    (h : RingHom.FormallySmoothNAdic.{w} f (IsLocalRing.maximalIdeal B)) :
    RingHom.FormallySmoothNAdic.{w} f' (IsLocalRing.maximalIdeal B') := by
  intro C _ J hJ α ψ hcomm hk
  have heval (a : A) : f' (eA a) = eB (f a) := DFunLike.congr_fun he a
  have hcomm' : (ψ.comp eB.toRingHom).comp f =
      (Ideal.Quotient.mk J).comp (α.comp eA.toRingHom) := by
    ext a
    show ψ (eB (f a)) = Ideal.Quotient.mk J (α (eA a))
    rw [← heval a]
    exact DFunLike.congr_fun hcomm (eA a)
  obtain ⟨n, hn, hk⟩ := hk
  have hk' : IsLocalRing.maximalIdeal B ^ n ≤ RingHom.ker (ψ.comp eB.toRingHom) := by
    intro x hx
    apply hk
    rw [← IsLocalRing.map_maximalIdeal_of_surjective eB.toRingHom eB.surjective,
      ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨δ, hδ, hδα⟩ := h C J hJ (α.comp eA.toRingHom)
    (ψ.comp eB.toRingHom) hcomm' ⟨n, hn, hk'⟩
  refine ⟨δ.comp eB.symm.toRingHom, ?_, ?_⟩
  · ext b
    simpa using DFunLike.congr_fun hδ (eB.symm b)
  · ext a
    obtain ⟨a, rfl⟩ := eA.surjective a
    show δ (eB.symm (f' (eA a))) = α (eA a)
    rw [heval a, eB.symm_apply_apply]
    exact DFunLike.congr_fun hδα a

/-- Isomorphic ring maps induce isomorphic formally smooth maps on prime localizations. -/
private theorem formallySmoothNAdic_localRingHom_of_ringEquiv
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (eR : R ≃+* R') (eS : S ≃+* S')
    (he : f'.comp eR.toRingHom = eS.toRingHom.comp f)
    (q : Ideal S') [q.IsPrime]
    (h : RingHom.FormallySmoothNAdic.{v}
      (Localization.localRingHom ((q.comap eS.toRingHom).comap f) (q.comap eS.toRingHom) f rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap eS.toRingHom)))) :
    RingHom.FormallySmoothNAdic.{v}
      (Localization.localRingHom (q.comap f') q f' rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  have hp : (q.comap eS.toRingHom).comap f = (q.comap f').comap eR.toRingHom := by
    rw [Ideal.comap_comap, Ideal.comap_comap]
    exact congrArg (Ideal.comap · q) he.symm
  let e₁ := Localization.localRingEquiv ((q.comap eS.toRingHom).comap f) (q.comap f') eR hp
  let e₂ := Localization.localRingEquiv (q.comap eS.toRingHom) q eS rfl
  apply formallySmoothNAdic_of_ringEquiv _ _ e₁ e₂ _ h
  apply IsLocalization.ringHom_ext ((q.comap eS.toRingHom).comap f).primeCompl
  ext r
  show Localization.localRingHom (q.comap f') q f' rfl
      (Localization.localRingHom ((q.comap eS.toRingHom).comap f) (q.comap f') eR.toRingHom hp
        (algebraMap R _ r)) =
    Localization.localRingHom (q.comap eS.toRingHom) q eS.toRingHom rfl
      (Localization.localRingHom ((q.comap eS.toRingHom).comap f) (q.comap eS.toRingHom) f rfl
        (algebraMap R _ r))
  simp only [Localization.localRingHom_to_map]
  exact congrArg (algebraMap S' (Localization.AtPrime q)) (DFunLike.congr_fun he r)

/-- Changing only the source ring preserves local adic formal smoothness. -/
theorem formallySmoothNAdic_localRingHom_of_ringEquiv_left.{u, w, z}
    {R : Type u} {S : Type w} {R' : Type z}
    [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (f' : R' →+* S) (eR : R ≃+* R')
    (he : f'.comp eR.toRingHom = f) (q : Ideal S) [q.IsPrime]
    (h : RingHom.FormallySmoothNAdic.{v}
      (Localization.localRingHom (q.comap f) q f rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))) :
    RingHom.FormallySmoothNAdic.{v}
      (Localization.localRingHom (q.comap f') q f' rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  apply formallySmoothNAdic_localRingHom_of_ringEquiv f f' eR (RingEquiv.refl S)
    (he.trans (RingHom.id_comp f).symm) q
  convert! h using 1

/-- Localizing the target away from a maximal ideal preserves its local smoothness assertion. -/
theorem formallySmoothNAdic_localRingHom_of_isLocalization
    {R S D : Type*} [CommRing R] [CommRing S] [CommRing D] [Algebra S D]
    (f : R →+* S) (M : Submonoid S) [IsLocalization M D]
    (q : Ideal S) [q.IsMaximal] (hq : Disjoint (M : Set S) (q : Set S))
    (h : let n := q.map (algebraMap S D)
      letI : n.IsMaximal := IsLocalization.isMaximal_of_isMaximal_disjoint M D q hq
      RingHom.FormallySmoothNAdic.{v}
        (Localization.localRingHom (n.comap ((algebraMap S D).comp f)) n
          ((algebraMap S D).comp f) rfl)
        (IsLocalRing.maximalIdeal (Localization.AtPrime n))) :
    RingHom.FormallySmoothNAdic.{v}
      (Localization.localRingHom (q.comap f) q f rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  let n := q.map (algebraMap S D)
  have : n.IsMaximal := IsLocalization.isMaximal_of_isMaximal_disjoint M D q hq
  have hn : n.comap (algebraMap S D) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M D inferInstance hq
  have : IsLocalization (q.primeCompl) (Localization.AtPrime n) := by
    simpa only [hn] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
        (Localization.AtPrime n) n)
  have hp : n.comap ((algebraMap S D).comp f) = q.comap f := by
    rw [← Ideal.comap_comap, hn]
  let eR := Localization.localRingEquiv
    (n.comap ((algebraMap S D).comp f)) (q.comap f) (RingEquiv.refl R) (hp.trans (by ext; rfl))
  let eS := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime n) (Localization.AtPrime q)
  apply formallySmoothNAdic_of_ringEquiv _ _ eR eS.toRingEquiv _ h
  apply IsLocalization.ringHom_ext (n.comap ((algebraMap S D).comp f)).primeCompl
  ext r
  show Localization.localRingHom (q.comap f) q f rfl
      (Localization.localRingHom (n.comap ((algebraMap S D).comp f)) (q.comap f)
        (RingHom.id R) (hp.trans (Ideal.comap_id _).symm) (algebraMap R _ r)) =
    eS (Localization.localRingHom (n.comap ((algebraMap S D).comp f)) n
      ((algebraMap S D).comp f) rfl (algebraMap R _ r))
  simp only [Localization.localRingHom_to_map, RingHom.id_apply, RingHom.comp_apply]
  show algebraMap S (Localization.AtPrime q) (f r) =
    eS (algebraMap S (Localization.AtPrime n) (f r))
  exact (eS.commutes (f r)).symm

/-- Testing the adic lifting property in a larger universe includes all smaller test rings. -/
theorem formallySmoothNAdic_of_ulift_testRing.{vTest, wTest}
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (n : Ideal B)
    (h : RingHom.FormallySmoothNAdic.{max vTest wTest} f n) :
    RingHom.FormallySmoothNAdic.{vTest} f n := by
  intro C _ J hJ α ψ hcomm hk
  let C' := ULift.{wTest} C
  let e : C ≃+* C' := ULift.ringEquiv.symm
  let J' := J.map e.toRingHom
  let eQ : C ⧸ J ≃+* C' ⧸ J' := Ideal.quotientEquiv J J' e rfl
  have heQ (x : C) : eQ (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J' (e x) :=
    Ideal.quotientEquiv_mk J J' e rfl x
  have hJ' : J' ^ 2 = 0 := by
    rw [← Ideal.map_pow, hJ]
    exact Ideal.map_bot
  have hcomm' : (eQ.toRingHom.comp ψ).comp f =
      (Ideal.Quotient.mk J').comp (e.toRingHom.comp α) := by
    ext a
    show eQ (ψ (f a)) = Ideal.Quotient.mk J' (e (α a))
    rw [show ψ (f a) = Ideal.Quotient.mk J (α a) from DFunLike.congr_fun hcomm a]
    exact Ideal.quotientEquiv_mk J J' e rfl (α a)
  have hk' : ∃ k : ℕ, 1 ≤ k ∧ n ^ k ≤ RingHom.ker (eQ.toRingHom.comp ψ) := by
    obtain ⟨k, hk, hker⟩ := hk
    refine ⟨k, hk, fun b hb => ?_⟩
    show eQ (ψ b) = 0
    rw [show ψ b = 0 from hker hb, map_zero]
  obtain ⟨δ, hδ, hδα⟩ := h C' J' hJ' (e.toRingHom.comp α)
    (eQ.toRingHom.comp ψ) hcomm' hk'
  refine ⟨e.symm.toRingHom.comp δ, ?_, ?_⟩
  · ext b
    apply eQ.injective
    show eQ (Ideal.Quotient.mk J (e.symm (δ b))) = eQ (ψ b)
    rw [heQ, e.apply_symm_apply]
    exact DFunLike.congr_fun hδ b
  · ext a
    show e.symm (δ (f a)) = α a
    rw [show δ (f a) = e (α a) from DFunLike.congr_fun hδα a, e.symm_apply_apply]

/-- Over a perfect residue field, a weakly unramified extension of discrete valuation
rings is formally smooth for the maximal-ideal-adic topology. -/
private theorem formallySmoothNAdic_of_perfectField_residueField_sameUniverse
    (A : Type uA) (B : Type uB)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    [PerfectField (IsLocalRing.ResidueField A)]
    (h : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    RingHom.FormallySmoothNAdic.{max uA uB} (algebraMap A B)
      (IsLocalRing.maximalIdeal B) :=
  (IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A B).2
    ⟨h, Algebra.isSeparableExtension_of_perfectField _ _⟩

/-- The perfect-residue criterion for formal smoothness holds for test rings in any universe. -/
private theorem formallySmoothNAdic_of_perfectField_residueField
    (A : Type uA) (B : Type uB)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    [PerfectField (IsLocalRing.ResidueField A)]
    (h : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    RingHom.FormallySmoothNAdic.{v} (algebraMap A B)
      (IsLocalRing.maximalIdeal B) := by
  let A' := ULift.{v} A
  let B' := ULift.{v} B
  let eA : A' ≃+* A := ULift.ringEquiv
  let eB : B' ≃+* B := ULift.ringEquiv
  have : IsDomain A' := eA.injective.isDomain eA
  have : IsDomain B' := eB.injective.isDomain eB
  have : IsDiscreteValuationRing A' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eA.symm
  have : IsDiscreteValuationRing B' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eB.symm
  let : Algebra A' B' := ULift.algebra' A B'
  let φ := algebraMap A' B'
  have : FaithfulSMul A' B' := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (eB.symm.injective.comp ((FaithfulSMul.algebraMap_injective A B).comp eA.injective))
  have : IsLocalHom φ := ⟨fun a ha => by
    have hb : IsUnit (algebraMap A B (eA a)) := ha.map eB.toRingHom
    have ha' : IsUnit (eA a) := isUnit_of_map_unit (algebraMap A B) _ hb
    simpa using ha'.map eA.symm.toRingHom⟩
  have : IsDiscreteValuationRing.IsExtension A' B' := {}
  have hA := IsLocalRing.map_maximalIdeal_of_surjective eA.symm.toRingHom eA.symm.surjective
  have hB := IsLocalRing.map_maximalIdeal_of_surjective eB.symm.toRingHom eB.symm.surjective
  have : PerfectField (IsLocalRing.ResidueField A') :=
    PerfectField.of_ringEquiv (K := IsLocalRing.ResidueField A)
    (Ideal.quotientEquiv (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A')
      eA.symm hA.symm)
  have hφ : IsDiscreteValuationRing.IsWeaklyUnramified A' B' := by
    apply (IsDiscreteValuationRing.weaklyUnramified_iff_map_maximalIdeal A' B').2
    rw [← hA, Ideal.map_map]
    have he : φ.comp eA.symm.toRingHom = eB.symm.toRingHom.comp (algebraMap A B) := by
      ext a
      rfl
    show (IsLocalRing.maximalIdeal A).map (φ.comp eA.symm.toRingHom) = _
    rw [he, ← Ideal.map_map,
      (IsDiscreteValuationRing.weaklyUnramified_iff_map_maximalIdeal A B).1 h, hB]
  have hs := formallySmoothNAdic_of_perfectField_residueField_sameUniverse A' B' hφ
  apply formallySmoothNAdic_of_ulift_testRing.{v, max uA uB}
  apply formallySmoothNAdic_of_ringEquiv φ (algebraMap A B) eA eB _ hs
  ext a
  rfl

/-- At discrete valuation localizations with perfect base residue field, ramification
index one implies formal smoothness. -/
private theorem formallySmoothNAdic_localRingHom_of_ramificationIdx_eq_one
    {R : Type uA} {S : Type uB} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime]
    [IsDomain (Localization.AtPrime (q.under R))]
    [IsDiscreteValuationRing (Localization.AtPrime (q.under R))]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    [PerfectField (q.under R).ResidueField]
    (hinj : Function.Injective (Localization.localRingHom (q.under R) q
      (algebraMap R S) rfl))
    (h : q.ramificationIdx R = 1) :
    RingHom.FormallySmoothNAdic.{v}
      (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  let p := q.under R
  let φ := Localization.localRingHom p q (algebraMap R S) rfl
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := φ.toAlgebra
  have : FaithfulSMul (Localization.AtPrime p) (Localization.AtPrime q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsDiscreteValuationRing.IsExtension (Localization.AtPrime p) (Localization.AtPrime q) := {}
  apply formallySmoothNAdic_of_perfectField_residueField
  apply (IsDiscreteValuationRing.weaklyUnramified_iff_map_maximalIdeal _ _).2
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
  have he : (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)).comp
      (algebraMap R (Localization.AtPrime p)) = algebraMap R (Localization.AtPrime q) := by
    ext r
    exact Localization.localRingHom_to_map p q (algebraMap R S) rfl r
  rw [he]
  exact map_under_eq_maximalIdeal_of_ramificationIdx_eq_one q h

/-- A solution induces adic smoothness on the canonical reduced tensor normalization. -/
theorem formallySmoothNAdic_integralClosure_of_isSolution
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁)
    (h : D.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, v})
    (f : integralClosure A K₁ →+*
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (hf : ∀ x, (f x).val = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x.val))
    (q : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
    [q.IsMaximal] :
    RingHom.FormallySmoothNAdic.{v, uK₁, max uL uK₁}
      (R := Localization.AtPrime (q.comap f)) (S := Localization.AtPrime q)
      (Localization.localRingHom (q.comap f) q f rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  classical
  let := D.commRingL₁
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  let := D.algebraBL₁
  let := D.algebraAA₁
  let := D.algebraA₁K₁
  let := D.algebraBB₁
  let := D.algebraB₁L₁
  let := D.algebraAB₁
  let := D.algebraA₁B₁
  let := D.isScalarTowerKLL₁
  let := D.isScalarTowerKK₁L₁
  let := D.isScalarTowerBLL₁
  let := D.isScalarTowerAA₁K₁
  let := D.isScalarTowerBB₁L₁
  let := D.isScalarTowerABB₁
  let := D.isScalarTowerAA₁B₁
  let := D.isIntegralClosureA₁
  let := D.isIntegralClosureB₁
  let Q := (L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)
  let eT : D.L₁ ≃ₐ[B] Q :=
    { D.eL₁.toRingEquiv with
      commutes' := fun b => by
        show D.eL₁ (algebraMap B D.L₁ b) = algebraMap B Q b
        rw [IsScalarTower.algebraMap_apply B L D.L₁, D.eL₁_left]
        rfl }
  let eA := IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁)
  let eB₀ := IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)
  let eB := eB₀.trans eT.mapIntegralClosure
  have heA (x : D.A₁) : (eA x : K₁) = algebraMap D.A₁ K₁ x :=
    IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x
  have heB₀ (x : D.B₁) : (eB₀ x : D.L₁) = algebraMap D.B₁ D.L₁ x :=
    IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x
  have hsquare : f.comp eA.toRingHom = eB.toRingHom.comp (algebraMap D.A₁ D.B₁) := by
    ext x
    show (f (eA x)).val =
      (eT.mapIntegralClosure (eB₀ (algebraMap D.A₁ D.B₁ x))).val
    rw [hf, AlgEquiv.coe_mapIntegralClosure, heA, heB₀, D.ringSquare]
    exact (D.eL₁_right _).symm
  have : (q.comap eB.toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective eB.toRingHom eB.surjective
  exact formallySmoothNAdic_localRingHom_of_ringEquiv
    (algebraMap D.A₁ D.B₁) f eA.toRingEquiv eB.toRingEquiv hsquare q
      (h (q.comap eB.toRingHom) inferInstance)

/-- A weak solution over a discrete valuation ring with perfect residue field
is a solution. -/
private theorem isSolution_of_isWeakSolution_of_perfectField
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁] [PerfectField (IsLocalRing.ResidueField A)]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁) (h : D.IsWeakSolution) :
    D.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, v} := by
  classical
  let := D.commRingL₁
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  let := D.algebraBL₁
  let := D.algebraAA₁
  let := D.algebraA₁K₁
  let := D.algebraBB₁
  let := D.algebraB₁L₁
  let := D.algebraAB₁
  let := D.algebraA₁B₁
  let := D.isScalarTowerKLL₁
  let := D.isScalarTowerKK₁L₁
  let := D.isScalarTowerBLL₁
  let := D.isScalarTowerAA₁K₁
  let := D.isScalarTowerBB₁L₁
  let := D.isScalarTowerABB₁
  let := D.isScalarTowerAA₁B₁
  let := D.isIntegralClosureA₁
  let := D.isIntegralClosureB₁
  let eA := IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁)
  let eB := IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)
  have heA (x : D.A₁) : (eA x : K₁) = algebraMap D.A₁ K₁ x :=
    IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x
  have heB (x : D.B₁) : (eB x : D.L₁) = algebraMap D.B₁ D.L₁ x :=
    IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x
  have hsquare (x : K) : algebraMap L D.L₁ (algebraMap K L x) =
      algebraMap K₁ D.L₁ (algebraMap K K₁ x) := by
    rw [← IsScalarTower.algebraMap_apply K L D.L₁,
      ← IsScalarTower.algebraMap_apply K K₁ D.L₁]
  have hring (x : D.A₁) : algebraMap D.B₁ D.L₁ (algebraMap D.A₁ D.B₁ x) =
      algebraMap K₁ D.L₁ (eA x : K₁) := by
    rw [heA]
    exact D.ringSquare x
  obtain ⟨_, _, _, _, _, _, _, _, _, hlocal, _⟩ :=
    IsDiscreteValuationRing.integralClosures_after_finite_fraction_field_extension
      A B K L K₁ D.L₁ D.A₁ D.B₁ D.eL₁ eA eB
      D.eL₁_left D.eL₁_right heB hsquare hring
  have : Algebra.IsIntegral A D.A₁ := IsIntegralClosure.isIntegral_algebra A K₁
  intro q hq
  have : q.IsMaximal := hq
  obtain ⟨hp, _, _, ⟨hdp, hDVRp⟩, ⟨hdq, hDVRq⟩, φ, hinj, _, hφ⟩ := hlocal q hq
  have := hp
  have := hdp
  have := hDVRp
  have := hdq
  have := hDVRq
  have : PerfectField (q.under D.A₁).ResidueField :=
    perfectField_residueField_of_integral A D.A₁ (q.under D.A₁)
  have heq : φ = Localization.localRingHom (q.under D.A₁) q
      (algebraMap D.A₁ D.B₁) rfl := by
    apply IsLocalization.ringHom_ext (q.under D.A₁).primeCompl
    ext x
    exact (hφ x).trans
      (Localization.localRingHom_to_map (q.under D.A₁) q
        (algebraMap D.A₁ D.B₁) rfl x).symm
  exact formallySmoothNAdic_localRingHom_of_ramificationIdx_eq_one q
    (heq ▸ hinj) (h q hq)

/-- In a finitely generated field extension, an element with prime-power roots of every
order is algebraic over the base field. -/
private theorem isAlgebraic_of_forall_exists_prime_pow
    (k L : Type*) [Field k] [Field L] [Algebra k L] [Algebra.EssFiniteType k L]
    (p : ℕ) [Fact p.Prime] [CharP L p]
    (x : L) (hx : ∀ n : ℕ, 1 ≤ n → ∃ y : L, y ^ (p ^ n) = x) :
    IsAlgebraic k x := by
  classical
  have hp : p.Prime := Fact.out
  have hx' : ∀ n : ℕ, ∃ y : L, y ^ (p ^ n) = x := by
    intro n
    cases n with
    | zero => exact ⟨x, by simp⟩
    | succ n => exact hx _ (by omega)
  choose y hy using hx'
  have hstep (n : ℕ) : y (n + 1) ^ p = y n := by
    apply iterateFrobenius_inj L p n
    show (y (n + 1) ^ p) ^ (p ^ n) = y n ^ (p ^ n)
    rw [← pow_mul, ← pow_succ', hy, hy]
  let F := IntermediateField.adjoin k {x}
  let C := algebraicClosure F L
  have : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp k F L
  have : Module.Finite F C := finiteDimensional_algebraicClosure_of_essFiniteType F L
  have hyint (n : ℕ) : IsIntegral F (y n) := by
    apply IsIntegral.of_pow (pow_pos hp.pos n)
    rw [hy]
    show IsIntegral F (algebraMap F L ⟨x, IntermediateField.subset_adjoin k _ rfl⟩)
    exact isIntegral_algebraMap
  let J (n : ℕ) : IntermediateField F L := IntermediateField.adjoin F {y n}
  have hJ : Monotone J := monotone_nat_of_le_succ fun n => by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro a rfl
    rw [← hstep n]
    exact (J (n + 1)).toSubalgebra.pow_mem (IntermediateField.subset_adjoin F _ rfl) p
  have hJC (n : ℕ) : J n ≤ C := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro a rfl
    exact mem_algebraicClosure_iff.mpr (hyint n).isAlgebraic
  let M : ℕ →o Submodule F C :=
    ⟨fun n => (J n).toSubalgebra.toSubmodule.comap C.val.toLinearMap,
      fun _ _ h => Submodule.comap_mono (hJ h)⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian F C) M
  have he : J n = J (n + 1) := by
    apply le_antisymm (hJ (by omega))
    intro x hx
    let z : C := ⟨x, hJC (n + 1) hx⟩
    have hz : z ∈ M (n + 1) := hx
    rw [← hn (n + 1) (by omega)] at hz
    exact hz
  have hm (i : ℕ) :
      (J i).restrictScalars k = IntermediateField.adjoin k {y i} := by
    show (IntermediateField.adjoin F {y i}).restrictScalars k = _
    rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    apply sup_eq_right.mpr
    apply IntermediateField.adjoin_le_iff.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    rw [← hy i]
    exact (IntermediateField.adjoin k {y i}).toSubalgebra.pow_mem
      (IntermediateField.subset_adjoin k _ rfl) (p ^ i)
  have he' : IntermediateField.adjoin k {y n} = IntermediateField.adjoin k {y (n + 1)} := by
    rw [← hm n, he, hm]
  have halg : IsAlgebraic k (y (n + 1)) :=
    Field.isAlgebraic_of_adjoin_eq_adjoin k L (m := p) (n := 1) hp.ne_one (by
      simpa only [hstep, pow_one] using he')
  rw [← hy (n + 1)]
  exact halg.pow _

/-- Epp's theorem yields a solution over a perfect residue field, given its residue condition. -/
private theorem exists_finite_extension_isSolution_of_eppCondition
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [PerfectField (IsLocalRing.ResidueField A)]
    (hEpp : EppTheorem.{uA, uB, uK, uL})
    (hcond : ∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
      ∀ [ExpChar (IsLocalRing.ResidueField B) p], Stacks.EppTheorem.EppCondition A B p) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁,
        D.IsSolution.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK, v} := by
  obtain ⟨K₁, hfield, halgK, halgA, htower, hfinite, D, hD⟩ := hEpp A B K L hcond
  exact ⟨K₁, hfield, halgK, halgA, htower, hfinite, D,
    isSolution_of_isWeakSolution_of_perfectField D hD⟩

/-- In residue characteristic zero Epp's weak solution is already a solution. -/
theorem exists_finite_extension_isSolution_of_charZero
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [CharZero (IsLocalRing.ResidueField A)]
    (hEpp : EppTheorem.{uA, uB, uK, uL}) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁,
        D.IsSolution.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK, v} := by
  refine exists_finite_extension_isSolution_of_eppCondition A B K L hEpp ?_
  intro p hp hchar
  have := hchar
  exact (hp.ne_zero (Nat.cast_eq_zero.mp
    (CharP.cast_eq_zero (IsLocalRing.ResidueField A) p))).elim

/-- Finitely generated residue extensions over a perfect residue field admit solutions. -/
theorem exists_finite_extension_isSolution_of_perfectField
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [PerfectField (IsLocalRing.ResidueField A)]
    [Algebra.EssFiniteType (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (hEpp : EppTheorem.{uA, uB, uK, uL}) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁,
        D.IsSolution.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK, v} := by
  refine exists_finite_extension_isSolution_of_eppCondition A B K L hEpp ?_
  intro p hp hchar _ x hx
  have := hchar
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (ResidueField B) p := charP_of_injective_algebraMap
    (algebraMap (ResidueField A) (ResidueField B)).injective p
  exact PerfectField.separable_of_irreducible (minpoly.irreducible
    (isAlgebraic_of_forall_exists_prime_pow (ResidueField A) (ResidueField B)
      p x (mem_perfectCore_iff_forall_one_le.mp hx)).isIntegral)

end Stacks.EliminateRamification
