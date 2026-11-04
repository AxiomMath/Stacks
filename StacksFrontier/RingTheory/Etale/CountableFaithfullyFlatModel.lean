module

public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Smooth.Flat
public import StacksFrontier.RingTheory.Spectrum.Prime.DirectedColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Countable étale, faithfully flat models of an étale, faithfully flat algebra

Let `C → A` be a surjective ring map with nil kernel and let `B` be an étale, faithfully flat
`A`-algebra. This file produces a finitely generated, hence countable, subring `P ⊆ C` and an
étale, faithfully flat `P`-algebra `E` with `B = A ⊗_P E`.

## Main results

* `Algebra.Etale.exists_model_of_surjective_of_ker_le_nilradical`: an étale algebra lifts along a
  surjection with nil kernel.
* `Algebra.exists_finsetStage_surjective_comap`: surjectivity on spectra of a finitely presented
  model descends to one of the subalgebras `C₀ ⊔ ℤ[F]`, `F ⊆ C` finite.
* `Algebra.exists_countable_etale_faithfullyFlat_model`: the statement above.

## References

* [Stacks Project, Tag 00U2](https://stacks.math.columbia.edu/tag/00U2)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public section

universe u

open TensorProduct CategoryTheory

namespace Algebra

/-- **An étale algebra lifts along a surjection with nil kernel.** Let `C → A` be surjective with
kernel contained in the nilradical, and let `B` be étale over `A`. Then there is an étale
`C`-algebra `B'` with `A ⊗[C] B' ≃ₐ[A] B`. -/
theorem Etale.exists_model_of_surjective_of_ker_le_nilradical
    {C A B : Type u} [CommRing C] [CommRing A] [CommRing B] [Algebra C A] [Algebra A B]
    [Algebra C B] [IsScalarTower C A B] [Algebra.Etale A B]
    (hα : Function.Surjective (algebraMap C A))
    (hnil : RingHom.ker (algebraMap C A) ≤ nilradical C) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra C B'),
      Algebra.Etale C B' ∧ Nonempty (A ⊗[C] B' ≃ₐ[A] B) := by
  classical
  obtain ⟨ι, σ, _, _, Q, hQ⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp ‹_›).out
  have : Q.HasCoeffs C := ⟨fun x _ => hα x⟩
  let _ := Fintype.ofFinite σ
  let B' := Q.ModelOfHasCoeffs C
  let P₀ := Q.toPreSubmersivePresentation.ofHasCoeffs C
  set d : MvPolynomial ι C :=
    ∑ i, Q.jacobianRelationsOfHasCoeffs C i * Q.relationOfHasCoeffs C i -
      (Q.jacobianOfHasCoeffs C * Q.invJacobianOfHasCoeffs C - 1) with hd
  have hdmap : MvPolynomial.map (algebraMap C A) d = 0 := by
    simp [hd, Algebra.Presentation.map_relationOfHasCoeffs, Q.jacobianRelations_spec]
  have hdnil : IsNilpotent d := by
    have hmem : d ∈ RingHom.ker (MvPolynomial.map (algebraMap C A) :
        MvPolynomial ι C →+* MvPolynomial ι A) := hdmap
    rw [MvPolynomial.ker_map] at hmem
    have hle : Ideal.map (MvPolynomial.C : C →+* MvPolynomial ι C)
        (RingHom.ker (algebraMap C A)) ≤ nilradical (MvPolynomial ι C) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact mem_nilradical.mpr ((mem_nilradical.mp (hnil hx)).map MvPolynomial.C)
    exact mem_nilradical.mp (hle hmem)
  have hjac : IsUnit P₀.jacobian := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have hmk : (Ideal.Quotient.mk _ : MvPolynomial ι C →+* B')
        (Q.jacobianOfHasCoeffs C * Q.invJacobianOfHasCoeffs C) =
        1 - Ideal.Quotient.mk _ d := by
      have hrel : (Ideal.Quotient.mk _ : MvPolynomial ι C →+* B')
          (∑ i, Q.jacobianRelationsOfHasCoeffs C i * Q.relationOfHasCoeffs C i) = 0 := by
        simp only [map_sum, map_mul, Ideal.Quotient.mk_span_range, mul_zero,
          Finset.sum_const_zero]
      rw [hd, map_sub, hrel, map_sub, map_one]
      ring
    have hu : IsUnit ((Ideal.Quotient.mk _ : MvPolynomial ι C →+* B')
        (Q.jacobianOfHasCoeffs C * Q.invJacobianOfHasCoeffs C)) := by
      rw [hmk, sub_eq_add_neg]
      exact (hdnil.map _).neg.isUnit_one_add
    rw [map_mul] at hu
    convert isUnit_of_mul_isUnit_left hu using 1
    have hval : (MvPolynomial.aeval P₀.val : MvPolynomial ι C →ₐ[C] Q.ModelOfHasCoeffs C) =
        Ideal.Quotient.mkₐ C _ := MvPolynomial.algHom_ext fun i => by
      rw [MvPolynomial.aeval_X]
      rfl
    rw [Generators.algebraMap_apply, hval, Ideal.Quotient.mkₐ_eq_mk,
      Algebra.SubmersivePresentation.jacobianOfHasCoeffs]
  let P₁ : SubmersivePresentation C (Q.ModelOfHasCoeffs C) ι σ :=
    { P₀ with jacobian_isUnit := hjac }
  have : IsStandardSmoothOfRelativeDimension 0 C (Q.ModelOfHasCoeffs C) :=
    P₁.isStandardSmoothOfRelativeDimension (by
      rw [← hQ]
      rfl)
  exact ⟨B', inferInstance, inferInstance,
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr this,
    ⟨Q.tensorModelOfHasCoeffsEquiv C⟩⟩

/-- A finitely generated `ℤ`-subalgebra is countable. -/
theorem _root_.Subalgebra.countable_of_fg {C : Type u} [CommRing C] {P : Subalgebra ℤ C}
    (hP : P.FG) : Countable P := by
  obtain ⟨t, rfl⟩ := hP
  have : Countable (MvPolynomial (↥(t : Set C)) ℤ) := Cardinal.mk_le_aleph0_iff.mp
    (MvPolynomial.cardinalMk_le_max_lift.trans (max_le (max_le
      (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)
      (Cardinal.lift_le_aleph0.mpr (Cardinal.mk_le_aleph0_iff.mpr t.finite_toSet.countable)))
      le_rfl))
  rw [Algebra.adjoin_eq_range]
  exact (Set.countable_range
    (MvPolynomial.aeval (R := ℤ) (Subtype.val : ↥(t : Set C) → C))).to_subtype

/-- The subalgebra `C₀ ⊔ ℤ[F]` generated over `C₀` by a finite subset `F` of `C`. -/
noncomputable def finsetStage {C : Type u} [CommRing C] (C₀ : Subalgebra ℤ C) (F : Finset C) :
    Subalgebra ℤ C :=
  C₀ ⊔ Algebra.adjoin ℤ (F : Set C)

/-- The stages are monotone in the finite subset. -/
theorem finsetStage_mono {C : Type u} [CommRing C] (C₀ : Subalgebra ℤ C) {F F' : Finset C}
    (h : F ≤ F') : finsetStage C₀ F ≤ finsetStage C₀ F' :=
  sup_le_sup_left (Algebra.adjoin_mono (by simpa using h)) _

/-- Every stage contains `C₀`. -/
theorem le_finsetStage {C : Type u} [CommRing C] (C₀ : Subalgebra ℤ C) (F : Finset C) :
    C₀ ≤ finsetStage C₀ F :=
  le_sup_left

/-- A stage over a finitely generated `C₀` is finitely generated. -/
theorem finsetStage_fg {C : Type u} [CommRing C] {C₀ : Subalgebra ℤ C} (h₀ : C₀.FG)
    (F : Finset C) : (finsetStage C₀ F).FG :=
  h₀.sup (Subalgebra.fg_adjoin_finset _)

/-- The transition maps of the directed system of stages. -/
noncomputable def finsetStageMap {C : Type u} [CommRing C] (C₀ : Subalgebra ℤ C)
    (F F' : Finset C) (h : F ≤ F') : finsetStage C₀ F →+* finsetStage C₀ F' :=
  (Subalgebra.inclusion (finsetStage_mono C₀ h)).toRingHom

/-- A transition map of the stages is the identity on underlying elements of `C`. -/
theorem finsetStageMap_apply {C : Type u} [CommRing C] (C₀ : Subalgebra ℤ C) {F F' : Finset C}
    (h : F ≤ F') (x : finsetStage C₀ F) : (finsetStageMap C₀ F F' h x : C) = x :=
  Subalgebra.coe_inclusion _ x

/-- The stages, with their inclusions, form a directed system. -/
instance {C : Type u} [CommRing C] (C₀ : Subalgebra ℤ C) :
    DirectedSystem (fun F => finsetStage C₀ F) fun i j h => finsetStageMap C₀ i j h :=
  ⟨fun _ x => Subtype.ext (finsetStageMap_apply C₀ _ x),
    fun _ _ _ _ _ x => Subtype.ext (by rw [finsetStageMap_apply, finsetStageMap_apply,
      finsetStageMap_apply])⟩

/-- The inclusion of a stage into `C`. -/
noncomputable def finsetStageVal {C : Type u} [CommRing C] (C₀ : Subalgebra ℤ C) (F : Finset C) :
    finsetStage C₀ F →+* C :=
  (finsetStage C₀ F).val.toRingHom

/-- The inclusion of a stage into `C` sends an element to itself. -/
theorem finsetStageVal_apply {C : Type u} [CommRing C] (C₀ : Subalgebra ℤ C) (F : Finset C)
    (x : finsetStage C₀ F) : finsetStageVal C₀ F x = x :=
  rfl

/-- The inclusions of the stages into `C` commute with the transition maps. -/
theorem finsetStageVal_map {C : Type u} [CommRing C] (C₀ : Subalgebra ℤ C) {F F' : Finset C}
    (h : F ≤ F') (x : finsetStage C₀ F) :
    finsetStageVal C₀ F' (finsetStageMap C₀ F F' h x) = finsetStageVal C₀ F x := by
  rw [finsetStageVal_apply, finsetStageVal_apply, finsetStageMap_apply]

/-- **Surjectivity on spectra descends to a stage of finitely generated subalgebras.** This is
`PrimeSpectrum.exists_ge_surjective_comap_tensorProduct_of_directed` for the directed system of
the subalgebras `C₀ ⊔ ℤ[F]`, `F` a finite subset of `C`, whose colimit is `C`. -/
theorem exists_finsetStage_surjective_comap {C : Type u} [CommRing C]
    (C₀ : Subalgebra ℤ C) {C₁ : Type u} [CommRing C₁] [Algebra (finsetStage C₀ ∅) C₁]
    (hC₁ : (algebraMap (finsetStage C₀ ∅) C₁).FinitePresentation)
    {D : Type u} [CommRing D] (χ : C →+* D) (θ : C₁ →+* D)
    (hcomm : χ.comp (finsetStageVal C₀ ∅) =
      θ.comp (algebraMap (finsetStage C₀ ∅) C₁))
    (hD : Function.Surjective (PrimeSpectrum.comap χ)) :
    ∃ (F : Finset C) (h : ∅ ≤ F),
      letI := (finsetStageMap C₀ ∅ F h).toAlgebra
      Function.Surjective (PrimeSpectrum.comap
        (algebraMap (finsetStage C₀ F) (finsetStage C₀ F ⊗[finsetStage C₀ ∅] C₁))) :=
  PrimeSpectrum.exists_ge_surjective_comap_tensorProduct_of_directed
    (f := finsetStageMap C₀) (φ := finsetStageVal C₀)
    (fun _ _ h x => finsetStageVal_map C₀ h x)
    (fun a => ⟨{a}, ⟨a, Algebra.mem_sup_right (Algebra.subset_adjoin (by simp))⟩,
      finsetStageVal_apply C₀ _ _⟩)
    (fun i x hx => ⟨i, le_rfl, Subtype.ext (by
      rw [finsetStageMap_apply, ← finsetStageVal_apply C₀ i x, hx]; rfl)⟩)
    hC₁ χ θ hcomm hD

/-- An `A`-algebra isomorphism `A ⊗[R] B ≃ₐ[A] T` makes `T` a pushout of `A` and `B` over `R`. -/
private theorem isPushout_of_algEquiv_tensorProduct (R A B : Type u) {T : Type u} [CommRing R]
    [CommRing A] [CommRing B] [CommRing T] [Algebra R A] [Algebra R B] [Algebra A T]
    (e : A ⊗[R] B ≃ₐ[A] T) :
    CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom (algebraMap A T))
      (CommRingCat.ofHom (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) :=
  (CommRingCat.isPushout_tensorProduct R A B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    e.toRingEquiv.toCommRingCatIso (by simp) (by simp) (by ext a; exact e.commutes a)
    (by ext; rfl)

/-- **A countable étale, faithfully flat model.** Let `C → A` be surjective with nil kernel and
let `B` be an étale, faithfully flat `A`-algebra. Then there are a finitely generated (hence
countable, `Subalgebra.countable_of_fg`) subring `P ⊆ C` and an étale, faithfully flat
`P`-algebra `E` with `B = A ⊗_P E`. -/
@[ega "IV 11.2.7" "special case"]
theorem exists_countable_etale_faithfullyFlat_model
    {C A B : Type u} [CommRing C] [CommRing A] [CommRing B] [Algebra C A] [Algebra A B]
    [Algebra.Etale A B] [Module.FaithfullyFlat A B]
    (hα : Function.Surjective (algebraMap C A))
    (hnil : RingHom.ker (algebraMap C A) ≤ nilradical C) :
    ∃ (P : Subalgebra ℤ C) (E : Type u) (_ : CommRing E) (_ : Algebra P E),
      P.FG ∧ Algebra.Etale P E ∧ Module.FaithfullyFlat P E ∧ ∃ ε : E →+* B,
        CategoryTheory.IsPushout (CommRingCat.ofHom ((algebraMap C A).comp P.val.toRingHom))
          (CommRingCat.ofHom (algebraMap P E)) (CommRingCat.ofHom (algebraMap A B))
          (CommRingCat.ofHom ε) := by
  classical
  let : Algebra C B := ((algebraMap A B).comp (algebraMap C A)).toAlgebra
  have : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨B', _, _, hB', ⟨e⟩⟩ :=
    Etale.exists_model_of_surjective_of_ker_le_nilradical (B := B) hα hnil
  have : IsStandardSmoothOfRelativeDimension 0 C B' :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp hB'
  obtain ⟨C₀, B₀, _, _, hfg, hB₀, ⟨e₀⟩⟩ :=
    IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg (R := ℤ) (A := C) (B := B') 0
  have : Algebra.Etale C₀ B₀ :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr hB₀
  let G₀ := finsetStage C₀ ∅
  let : Algebra C₀ G₀ := (Subalgebra.inclusion (le_finsetStage C₀ ∅)).toRingHom.toAlgebra
  let C₁ := G₀ ⊗[C₀] B₀
  have : Algebra.Etale G₀ C₁ := inferInstance
  have hC₁ : (algebraMap G₀ C₁).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  let ι₀ : G₀ →ₐ[C₀] C :=
    { finsetStageVal C₀ ∅ with commutes' := fun _ => rfl }
  let θ : C₁ →+* B' :=
    e₀.symm.toRingHom.comp (Algebra.TensorProduct.map ι₀ (AlgHom.id C₀ B₀)).toRingHom
  have hcomm : (algebraMap C B').comp (finsetStageVal C₀ ∅) = θ.comp (algebraMap G₀ C₁) := by
    ext x
    show algebraMap C B' (finsetStageVal C₀ ∅ x) =
      e₀.symm ((Algebra.TensorProduct.map ι₀ (AlgHom.id C₀ B₀)) (x ⊗ₜ (1 : B₀)))
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact (e₀.symm.commutes _).symm
  let toB : B' →+* B := e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  have htoB : toB.comp (algebraMap C B') = (algebraMap A B).comp (algebraMap C A) := by
    ext c
    show e (1 ⊗ₜ algebraMap C B' c) = algebraMap A B (algebraMap C A c)
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact e.commutes (algebraMap C A c)
  have hD : Function.Surjective (PrimeSpectrum.comap (algebraMap C B')) := by
    intro p
    obtain ⟨p', hp'⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap C A)) := by
      rw [range_comap_of_surjective A (algebraMap C A) hα]
      exact hnil.trans (nilradical_le_prime p.asIdeal)
    obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) p'
    refine ⟨PrimeSpectrum.comap toB q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, htoB, PrimeSpectrum.comap_comp_apply, hq, hp']
  obtain ⟨F, hF, hsurjF⟩ :=
    exists_finsetStage_surjective_comap C₀ hC₁ (algebraMap C B') θ hcomm hD
  let : Algebra G₀ (finsetStage C₀ F) := (finsetStageMap C₀ ∅ F hF).toAlgebra
  let P := finsetStage C₀ F
  let E := P ⊗[G₀] C₁
  have : Algebra.Etale P E := inferInstance
  have : Module.Flat P E := Algebra.Smooth.flat _ _
  have : Module.FaithfullyFlat P E := Module.FaithfullyFlat.of_comap_surjective hsurjF
  let b₀ : B₀ →+* B' := e₀.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  have sq₁ := CommRingCat.isPushout_tensorProduct C₀ G₀ B₀
  have sq₂ := CommRingCat.isPushout_tensorProduct G₀ P C₁
  have sqL := sq₁.paste_horiz sq₂
  have sq₃ := isPushout_of_algEquiv_tensorProduct C₀ C B₀ e₀.symm
  have sq₄ := isPushout_of_algEquiv_tensorProduct C A B' e
  have sqR := sq₃.paste_horiz sq₄
  have htop : CommRingCat.ofHom (algebraMap C₀ C) ≫ CommRingCat.ofHom (algebraMap C A) =
      (CommRingCat.ofHom (algebraMap C₀ G₀) ≫ CommRingCat.ofHom (algebraMap G₀ P)) ≫
        CommRingCat.ofHom ((algebraMap C A).comp P.val.toRingHom) := by
    ext x
    rfl
  rw [htop] at sqR
  have key := CategoryTheory.IsPushout.of_left' sqR sqL
  let ε : E →+* B := (sqL.desc (CommRingCat.ofHom ((algebraMap C A).comp P.val.toRingHom) ≫
    CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom b₀ ≫ CommRingCat.ofHom toB)
    (by rw [← Category.assoc, sqR.w])).hom
  exact ⟨P, E, inferInstance, inferInstance,
    finsetStage_fg hfg F, inferInstance, inferInstance, ε, key⟩

end Algebra

end
