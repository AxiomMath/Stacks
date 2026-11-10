module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.NormalizationComparison

/-!
# Formal smoothness after a finite fraction-field extension

If `A → B` is formally smooth for the maximal-ideal-adic topology, then after a finite extension
`K₁ / K` the integral closure `B₁` of `B` in the reduced compositum is the reduced tensor product
`(B ⊗_A A₁)_red`, and every extension of discrete valuation rings obtained by localizing at a
maximal ideal of `B₁` is again formally smooth.

## Main results

* `IsDiscreteValuationRing.formallySmooth_localizations_after_finite_fraction_field_extension`:
  after a finite fraction-field extension the integral closure is the reduced tensor product and
  all the induced local extensions are formally smooth.

## Implementation notes

The equalities of the sources are represented by algebra equivalences together with the
compatibility equations that pin down both canonical maps, so that applications do not have to
rebuild the comparison data separately.

The result is a corrected form of the source statement for Tag 09EQ: the printed equalities
`L₁ = L ⊗_K K₁` and `B₁ = B ⊗_A A₁` fail for an inseparable `K₁ / K` over a non-excellent base
(the completion example of Tag 00PB), where `L ⊗_K K₁` is not reduced. They are recovered here
under the additional hypothesis that `L ⊗_K K₁` is reduced.

## References

* [The Stacks Project, Tag 09EQ](https://stacks.math.columbia.edu/tag/09EQ)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe uA uB uK uL uK₁ uL₁ uA₁ uB₁

open scoped TensorProduct

noncomputable section

namespace IntegralClosureComparison

private theorem reduced_comparison_injective_of_fractionRing
    (S W V : Type*) [CommRing S] [CommRing W] [CommRing V]
    [Algebra W V]
    (algebraLoc : Algebra (S ⧸ nilradical S) V)
    (g : S →+* W) (hnil : nilradical S ≤ RingHom.ker g)
    (hcompat : letI := algebraLoc
      ∀ s : S, algebraMap (S ⧸ nilradical S) V
        (Ideal.Quotient.mk (nilradical S) s) = algebraMap W V (g s))
    (eFrac : letI := algebraLoc
      FractionRing (S ⧸ nilradical S) ≃ₐ[S ⧸ nilradical S] V) :
    Function.Injective (Ideal.Quotient.lift (nilradical S) g
      (fun _s hs => RingHom.mem_ker.mp (hnil hs))) := by
  let gRed : (S ⧸ nilradical S) →+* W :=
    Ideal.Quotient.lift (nilradical S) g
      (fun s hs => RingHom.mem_ker.mp (hnil hs))
  let : Algebra (S ⧸ nilradical S) V := algebraLoc
  have hinjR : Function.Injective (algebraMap (S ⧸ nilradical S) V) := by
    intro x y h
    apply IsFractionRing.injective (S ⧸ nilradical S) (FractionRing (S ⧸ nilradical S))
    apply eFrac.injective
    simpa only [eFrac.commutes] using h
  have hcomp : (algebraMap W V).comp gRed =
      algebraMap (S ⧸ nilradical S) V := by
    apply Ideal.Quotient.ringHom_ext
    ext s
    exact (hcompat s).symm
  intro x y hxy
  apply hinjR
  have h := congrArg (algebraMap W V) hxy
  simpa only [← hcomp, RingHom.comp_apply] using h

private noncomputable def reduced_comparison_equiv_of_bijective
    (B S W : Type*) [CommRing B] [CommRing S] [CommRing W]
    [Algebra B S] [Algebra B W]
    (g : S →+* W) (hnil : nilradical S ≤ RingHom.ker g)
    (hbase : ∀ b : B, g (algebraMap B S b) = algebraMap B W b)
    (hbij : Function.Bijective (Ideal.Quotient.lift (nilradical S) g
      (fun _s hs => RingHom.mem_ker.mp (hnil hs)))) :
    W ≃ₐ[B] (S ⧸ nilradical S) := by
  let gRed : (S ⧸ nilradical S) →+* W :=
    Ideal.Quotient.lift (nilradical S) g
      (fun s hs => RingHom.mem_ker.mp (hnil hs))
  let gAlg : (S ⧸ nilradical S) →ₐ[B] W :=
    { toRingHom := gRed
      commutes' := by
        intro b
        change g (algebraMap B S b) = algebraMap B W b
        exact hbase b }
  exact (AlgEquiv.ofBijective gAlg hbij).symm

private theorem reduced_comparison_equiv_right
    (A B D W : Type*) [CommRing A] [CommRing B]
    [CommRing D] [CommRing W]
    [Algebra A B] [Algebra A D] [Algebra B W] [Algebra D W]
    (g : (B ⊗[A] D) →+* W)
    (hnil : nilradical (B ⊗[A] D) ≤ RingHom.ker g)
    (hbase : ∀ b : B,
      g ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] D) b) =
        algebraMap B W b)
    (hright : ∀ d : D,
      g ((Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D) d) =
        algebraMap D W d)
    (hbij : Function.Bijective (Ideal.Quotient.lift (nilradical (B ⊗[A] D)) g
      (fun _s hs => RingHom.mem_ker.mp (hnil hs)))) :
    letI : Algebra B (B ⊗[A] D) := Algebra.TensorProduct.leftAlgebra
    ∀ d : D,
      reduced_comparison_equiv_of_bijective B (B ⊗[A] D) W g hnil
        hbase hbij (algebraMap D W d) =
          Ideal.Quotient.mk (nilradical (B ⊗[A] D))
            ((Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D) d) := by
  let : Algebra B (B ⊗[A] D) := Algebra.TensorProduct.leftAlgebra
  intro d
  apply (reduced_comparison_equiv_of_bijective B (B ⊗[A] D) W g hnil hbase hbij).symm.injective
  simp only [AlgEquiv.symm_apply_apply]
  change algebraMap D W d = g
    ((Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D) d)
  exact (hright d).symm

private theorem actual_reduced_tensor_equiv_of_normal
    (A B K L K₁ L₁ A₁ B₁ : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B₁ L₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L L₁] [IsScalarTower K K₁ L₁] [IsScalarTower B L L₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) =
      algebraMap B₁ L₁ x)
    (hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁))
    (hNormal : IsNormalRing ((B ⊗[A] A₁) ⧸ nilradical (B ⊗[A] A₁))) :
    ∃ eB : B₁ ≃ₐ[B] ((B ⊗[A] A₁) ⧸ nilradical (B ⊗[A] A₁)),
      ∀ a : A₁, eB (algebraMap A₁ B₁ a) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a) := by
  let S := B ⊗[A] A₁
  let R := S ⧸ nilradical S
  obtain ⟨algebraLoc, g₀, hnil, hsurj, hleft, hright, hcompat, ⟨eFrac⟩⟩ :=
    actual_reduced_tensor_normalization_surjective_of_normal
      A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
        hfieldSquare hringSquare hNormal
  let : Algebra B S := Algebra.TensorProduct.leftAlgebra
  have hinj : Function.Injective (Ideal.Quotient.lift (nilradical S) g₀
      (fun s hs => RingHom.mem_ker.mp (hnil hs))) :=
    reduced_comparison_injective_of_fractionRing S B₁ L₁
      algebraLoc g₀ hnil hcompat eFrac
  have hbij : Function.Bijective (Ideal.Quotient.lift (nilradical S) g₀
      (fun s hs => RingHom.mem_ker.mp (hnil hs))) := ⟨hinj, hsurj⟩
  let eB := reduced_comparison_equiv_of_bijective B S B₁ g₀ hnil
    (fun b => hleft b) hbij
  exact ⟨eB, reduced_comparison_equiv_right A B A₁ B₁ g₀ hnil
    hleft hright hbij⟩

private theorem reduced_quotient_algEquiv
    (L U V : Type*) [CommRing L] [CommRing U] [CommRing V]
    [Algebra L U] [Algebra L V]
    (eRed : V ≃+* (U ⧸ nilradical U))
    (hleft : ∀ l : L,
      eRed (algebraMap L V l) = Ideal.Quotient.mk (nilradical U)
        (algebraMap L U l))
    (hReduced : IsReduced U) :
    ∃ e : V ≃ₐ[L] U,
      ∀ v : V, Ideal.Quotient.mk (nilradical U) (e v) = eRed v := by
  let : IsReduced U := hReduced
  let eRedL : V ≃ₐ[L] (U ⧸ nilradical U) :=
    { eRed with commutes' := hleft }
  let qeq : (U ⧸ nilradical U) ≃ₐ[L] U :=
    (Ideal.quotientEquivAlgOfEq L (nilradical_eq_bot_iff.mpr hReduced)).trans
      (AlgEquiv.quotientBot L U)
  let e := eRedL.trans qeq
  refine ⟨e, fun v => ?_⟩
  have hmk (x : U) : qeq.symm x = Ideal.Quotient.mk (nilradical U) x := by
    apply qeq.injective
    simp only [qeq, AlgEquiv.apply_symm_apply, AlgEquiv.trans_apply,
      Ideal.quotientEquivAlgOfEq_mk,
      AlgEquiv.quotientBot_mk]
  calc
    Ideal.Quotient.mk (nilradical U) (e v) = qeq.symm (qeq (eRed v)) :=
      (hmk (qeq (eRed v))).symm
    _ = eRed v := qeq.symm_apply_apply _

private theorem reduced_quotient_algEquiv_right
    (L K U V : Type*) [CommRing L] [CommRing K] [CommRing U] [CommRing V]
    [Algebra L U] [Algebra L V] [Algebra K V]
    (includeK : K →+* U)
    (eRed : V ≃+* (U ⧸ nilradical U))
    (hleft : ∀ l : L, eRed (algebraMap L V l) =
      Ideal.Quotient.mk (nilradical U) (algebraMap L U l))
    (hright : ∀ k : K, eRed (algebraMap K V k) =
      Ideal.Quotient.mk (nilradical U) (includeK k))
    (hReduced : IsReduced U) :
    ∃ e : V ≃ₐ[L] U,
      (∀ v : V, Ideal.Quotient.mk (nilradical U) (e v) = eRed v) ∧
      (∀ k : K, e (algebraMap K V k) = includeK k) := by
  obtain ⟨e, he⟩ := reduced_quotient_algEquiv L U V eRed hleft hReduced
  have hinj : Function.Injective (Ideal.Quotient.mk (nilradical U)) := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    simpa only [Ideal.mk_ker] using
      (nilradical_eq_bot_iff.mpr hReduced)
  refine ⟨e, he, fun k => hinj ?_⟩
  rw [he, hright]

private theorem reduced_of_regular_away_equiv_reduced
    (S T U : Type*) [CommRing S] [CommRing T] [CommRing U]
    [Algebra S T] (π : S) (hπ : π ∈ nonZeroDivisors S)
    [IsLocalization.Away π T]
    (e : T ≃+* U) (hReduced : IsReduced U) : IsReduced S := by
  let : IsReduced U := hReduced
  let : IsReduced T := isReduced_of_injective e e.injective
  have hinj : Function.Injective (algebraMap S T) :=
    IsLocalization.injectiveₛ (M := Submonoid.powers π) T (by
      rintro _ ⟨n, rfl⟩
      exact isRegular_iff_mem_nonZeroDivisors.mpr
        ((nonZeroDivisors S).pow_mem hπ n))
  exact isReduced_of_injective (algebraMap S T) hinj

private theorem actual_reduced_generic_fibre_conclusions_of_normal
    (A B K L K₁ L₁ A₁ B₁ : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B₁ L₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L L₁] [IsScalarTower K K₁ L₁] [IsScalarTower B L L₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) =
      algebraMap B₁ L₁ x)
    (hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁))
    (hNormal : IsNormalRing ((B ⊗[A] A₁) ⧸ nilradical (B ⊗[A] A₁))) :
    IsReduced (L ⊗[K] K₁) →
      (∃ eL : L₁ ≃ₐ[L] (L ⊗[K] K₁),
        (∀ x : L₁, Ideal.Quotient.mk _ (eL x) = eL₁ x) ∧
        (∀ x : K₁, eL (algebraMap K₁ L₁ x) =
          (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) ∧
      (∃ eB : B₁ ≃ₐ[B] (B ⊗[A] A₁),
        ∀ x : A₁, eB (algebraMap A₁ B₁ x) =
          (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) x) := by
  intro hReducedU
  let S := B ⊗[A] A₁
  let U := L ⊗[K] K₁
  have hEM := integralClosures_after_finite_fraction_field_extension
    A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
      hfieldSquare hringSquare
  obtain ⟨πA, _, hregular, ⟨genericIso, _, _⟩, _⟩ := hEM.2.2.2.1
  let πS : S := algebraMap A S πA
  have hregS : πS ∈ nonZeroDivisors S :=
    isRegular_iff_mem_nonZeroDivisors.mp hregular
  have hReducedS : IsReduced S :=
    reduced_of_regular_away_equiv_reduced S (Localization.Away πS) U
      πS hregS genericIso hReducedU
  let : Algebra L U := Algebra.TensorProduct.leftAlgebra
  obtain ⟨eL, hLquot, hLright⟩ :=
    reduced_quotient_algEquiv_right L K₁ U L₁
      (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] U).toRingHom
      eL₁.toRingEquiv eL₁_left eL₁_right hReducedU
  obtain ⟨eBred, hBredRight⟩ := actual_reduced_tensor_equiv_of_normal
    A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
      hfieldSquare hringSquare hNormal
  let : Algebra B S := Algebra.TensorProduct.leftAlgebra
  obtain ⟨eB, -, hBright⟩ :=
    reduced_quotient_algEquiv_right B A₁ S B₁
      (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] S).toRingHom
      eBred.toRingEquiv eBred.commutes hBredRight hReducedS
  exact ⟨⟨eL, hLquot, hLright⟩, ⟨eB, hBright⟩⟩

end IntegralClosureComparison

open IsLocalRing in
private theorem formallySmoothNAdic_of_mapped_uniformizer_and_separable
    {D : Type uA₁} {C : Type uB₁} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra D C] [IsExtension D C]
    (π : D) (hπ : Irreducible π)
    (hmax : IsLocalRing.maximalIdeal C = Ideal.span {algebraMap D C π})
    (hsep : Algebra.IsSeparableExtension (ResidueField D) (ResidueField C)) :
    RingHom.FormallySmoothNAdic.{max uA₁ uB₁} (algebraMap D C) (IsLocalRing.maximalIdeal C) := by
  apply (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension D C).mpr
  refine ⟨?_, hsep⟩
  change ramificationIndex D C = 1
  apply ((ramificationIndex_characterization D C).2.2.1 1 le_rfl ?_).symm
  simp [hπ.maximalIdeal_eq, hmax, Ideal.map_span]

private theorem localizationAtPrimeEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime]
    (h : q.comap e.toRingHom = p) :
    ∃ E : Localization.AtPrime p ≃+* Localization.AtPrime q,
      ∀ x : R, E (algebraMap R _ x) = algebraMap S _ (e x) := by
  have hmap : p.primeCompl.map e.toMonoidHom = q.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e x ∉ q
      change x ∉ p at hx
      rwa [← h] at hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e.symm y ∉ p
      rw [← h]
      change e (e.symm y) ∉ q
      simpa using hy
  exact ⟨IsLocalization.ringEquivOfRingEquiv _ _ e hmap,
    IsLocalization.ringEquivOfRingEquiv_eq hmap⟩

/-- Formal smoothness of an extension of discrete valuation rings persists at every local factor
after a finite extension of the fraction field.  The integral closure upstairs is the reduced
tensor product, and it is the unreduced tensor product whenever `L ⊗_K K₁` is reduced. -/
@[stacks 09EQ]
theorem formallySmooth_localizations_after_finite_fraction_field_extension
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    (K₁ : Type uK₁) (L₁ : Type uL₁) (A₁ : Type uA₁) (B₁ : Type uB₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B₁ L₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L L₁] [IsScalarTower K K₁ L₁] [IsScalarTower B L L₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) = algebraMap B₁ L₁ x)
    (hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁))
    (hformal : RingHom.FormallySmoothNAdic.{max uA uB} (algebraMap A B)
      (IsLocalRing.maximalIdeal B)) :
    (∃ eB : B₁ ≃ₐ[B] ((B ⊗[A] A₁) ⧸ nilradical (B ⊗[A] A₁)),
        (∀ x : A₁, eB (algebraMap A₁ B₁ x) = Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) x))) ∧
      (IsReduced (L ⊗[K] K₁) →
        (∃ eL : L₁ ≃ₐ[L] (L ⊗[K] K₁),
        (∀ x : L₁, Ideal.Quotient.mk _ (eL x) = eL₁ x) ∧
        (∀ x : K₁, eL (algebraMap K₁ L₁ x) =
          (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) ∧
      (∃ eB : B₁ ≃ₐ[B] (B ⊗[A] A₁),
        (∀ x : A₁, eB (algebraMap A₁ B₁ x) =
          (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) x))) ∧
      (∀ q : Ideal B₁, q.IsMaximal →
        (q.comap (algebraMap A₁ B₁)).IsMaximal ∧
        ∃ (_ : q.IsPrime) (_ : (q.comap (algebraMap A₁ B₁)).IsPrime),
          (∃ _ : IsDomain (Localization (q.comap (algebraMap A₁ B₁)).primeCompl),
            IsDiscreteValuationRing
              (Localization (q.comap (algebraMap A₁ B₁)).primeCompl)) ∧
          (∃ _ : IsDomain (Localization q.primeCompl),
            IsDiscreteValuationRing (Localization q.primeCompl)) ∧
          ∃ φ : Localization (q.comap (algebraMap A₁ B₁)).primeCompl →+*
              Localization q.primeCompl,
            Function.Injective φ ∧ IsLocalHom φ ∧
              (∀ x : A₁, φ (algebraMap A₁ _ x) =
                algebraMap B₁ _ (algebraMap A₁ B₁ x)) ∧
              RingHom.FormallySmoothNAdic.{max uA₁ uB₁} φ
                (IsLocalRing.maximalIdeal (Localization q.primeCompl))) := by
  have hnormal := ReducedTensorLocalization.actual_normal_ring_reduced_tensor
    A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
      hfieldSquare hringSquare hformal
  obtain ⟨eBred, hBredRight⟩ := IntegralClosureComparison.actual_reduced_tensor_equiv_of_normal
    A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
      hfieldSquare hringSquare hnormal
  refine ⟨⟨eBred, hBredRight⟩, ?_, ?_⟩
  · exact IntegralClosureComparison.actual_reduced_generic_fibre_conclusions_of_normal
      A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
        hfieldSquare hringSquare hnormal
  · intro q hq
    let : q.IsMaximal := hq
    have hEM := integralClosures_after_finite_fraction_field_extension
      A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
        hfieldSquare hringSquare
    obtain ⟨_, _, _, _, _, _, _, _, _, hlocal, _⟩ := hEM
    obtain ⟨hm, hqp, hmp, ⟨hDdomain, hDdvr⟩, ⟨hCdomain, hCdvr⟩,
      φ, hφinj, hφlocal, hφcomp⟩ := hlocal q hq
    let m := q.comap (algebraMap A₁ B₁)
    let : m.IsMaximal := hm
    let : m.IsPrime := hmp
    let : q.IsPrime := hqp
    let D := Localization.AtPrime m
    let C := Localization.AtPrime q
    let : IsDomain D := hDdomain
    let : IsDiscreteValuationRing D := hDdvr
    let : IsDomain C := hCdomain
    let : IsDiscreteValuationRing C := hCdvr
    let : Algebra D C := φ.toAlgebra
    let : IsLocalHom (algebraMap D C) := hφlocal
    let : FaithfulSMul D C := (faithfulSMul_iff_algebraMap_injective D C).mpr hφinj
    let : IsExtension D C := ⟨⟩
    let : IsScalarTower A₁ D C := IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact (hφcomp x).symm)
    let : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap A C x = algebraMap D C (algebraMap A D x)
      rw [IsScalarTower.algebraMap_apply A A₁ D, IsScalarTower.algebraMap_apply A A₁ C]
      exact (hφcomp (algebraMap A A₁ x)).symm)
    obtain ⟨hAD, hfinite⟩ := finite_residueField_localized_integralClosure A K K₁ A₁ eA₁ m
    let : IsLocalHom (algebraMap A D) := hAD
    let : Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D) := hfinite
    let : Algebra.IsIntegral B B₁ := eB₁.isIntegral_iff.mpr inferInstance
    let : IsLocalHom (algebraMap B C) := isLocalHom_of_integral_localization B B₁ C q
    let : IsLocalHom (algebraMap A C) := by
      rw [IsScalarTower.algebraMap_eq A B C]
      infer_instance
    let S := B ⊗[A] A₁
    let R := S ⧸ nilradical S
    let g : S →+* B₁ := eBred.symm.toRingHom.comp (Ideal.Quotient.mk (nilradical S))
    have hg : Function.Surjective g := eBred.symm.surjective.comp Ideal.Quotient.mk_surjective
    have hgleft (b : B) : g ((Algebra.TensorProduct.includeLeft : B →ₐ[A] S) b) =
        algebraMap B B₁ b :=
      eBred.symm.commutes b
    have hgright (a : A₁) : g ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] S) a) =
        algebraMap A₁ B₁ a := by
      apply eBred.injective
      simpa [g] using (hBredRight a).symm
    have hsepAB := (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A B).mp hformal
    let : Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B) := hsepAB.2
    have hsurj := residueTensorMap_surjective A B A₁ B₁ D C q.primeCompl g hg hgleft hgright
    have hsep : Algebra.IsSeparableExtension (IsLocalRing.ResidueField D)
        (IsLocalRing.ResidueField C) :=
      separable_of_surjective_from_tensor _ _ _ _ (residueTensorMap A B D C) hsurj
    have hprincipal : ∃ π : D, Irreducible π ∧ IsLocalRing.maximalIdeal C =
        Ideal.span {algebraMap D C π} := by
      obtain ⟨g', _, _, hg'left, hg'right, _, _, r, hr, hrcomap, _, _, _,
        algebraLoc, hcomp, π, hπ, hmax⟩ :=
        ReducedTensorLocalization.actual_09EM_reduced_branch_specialFiber_isField
          A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
            hfieldSquare hringSquare hformal q
      have hgg : g' = g := by
        apply Algebra.TensorProduct.ringHom_ext
        · ext b
          exact (hg'left b).trans (hgleft b).symm
        · ext a
          exact (hg'right a).trans (hgright a).symm
      let : r.IsPrime := hr
      have hrq : r.comap eBred.toRingHom = q := by
        apply Ideal.comap_injective_of_surjective g hg
        rw [Ideal.comap_comap]
        have he : eBred.toRingHom.comp g = Ideal.Quotient.mk (nilradical S) :=
          RingHom.ext fun _ => eBred.apply_symm_apply _
        rw [he, hrcomap, hgg]
      obtain ⟨E, hE⟩ := localizationAtPrimeEquiv eBred.toRingEquiv q r hrq
      have hEφ : E.toRingHom.comp φ =
          @algebraMap D (Localization.AtPrime r) _ _ algebraLoc := by
        apply IsLocalization.ringHom_ext m.primeCompl
        ext a
        change E (φ (algebraMap A₁ D a)) = _
        rw [hφcomp, hE]
        change algebraMap R (Localization.AtPrime r) (eBred (algebraMap A₁ B₁ a)) = _
        rw [hBredRight]
        exact (hcomp a).symm
      refine ⟨π, hπ, ?_⟩
      apply E.idealComapOrderIso.symm.injective
      change (IsLocalRing.maximalIdeal C).map E.toRingHom =
        (Ideal.span {algebraMap D C π}).map E.toRingHom
      rw [IsLocalRing.map_maximalIdeal_of_surjective E.toRingHom E.surjective,
        Ideal.map_span, Set.image_singleton]
      exact hmax.trans (congrArg (fun x => Ideal.span {x})
        (RingHom.congr_fun hEφ π).symm)
    obtain ⟨π, hπ, hmax⟩ := hprincipal
    exact ⟨hm, hqp, hmp, ⟨hDdomain, hDdvr⟩, ⟨hCdomain, hCdvr⟩,
      φ, hφinj, hφlocal, hφcomp,
      formallySmoothNAdic_of_mapped_uniformizer_and_separable π hπ hmax hsep⟩

end

end

end IsDiscreteValuationRing
