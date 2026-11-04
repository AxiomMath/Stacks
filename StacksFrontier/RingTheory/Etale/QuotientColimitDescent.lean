module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import StacksFrontier.RingTheory.Flat.FlatteningFGApprox
public import StacksFrontier.RingTheory.Etale.ColimitBaseChange
public import StacksFrontier.RingTheory.Spectrum.Prime.DirectedColimit

/-!
# Étaleness and surjectivity descend from a quotient to a finitely generated subideal

Let `R` be a commutative ring, `K ⊆ R` an ideal and `C` an `R`-algebra of finite presentation. The
ring `R ⧸ K` is the filtered colimit of the rings `R ⧸ J` over the finitely generated ideals
`J ⊆ K`. Consequently, if the base change `R ⧸ K → (R ⧸ K) ⊗_R C` is étale, respectively induces a
surjection on spectra, then so does `R ⧸ J → (R ⧸ J) ⊗_R C` for some finitely generated `J ⊆ K`.

## Main definitions

* `Ideal.FGLe`: the finitely generated ideals contained in `K`, a directed preorder.
* `Ideal.quotientColimitPresentation`: the presentation of `R ⧸ K` as the colimit of the `R ⧸ J`,
  from the colimit `Ideal.isColimitQuotientCocone` of quotients along a monotone family of ideals.

## Main results

* `Ideal.exists_fg_le_etale_tensor`: étaleness descends to a stage (Stacks 07RI).
* `Ideal.exists_fg_le_surjective_comap_tensor`: surjectivity on spectra descends to a stage.

## References

* [Stacks Project, Tag 07RI](https://stacks.math.columbia.edu/tag/07RI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Ideal

variable {R : Type u} [CommRing R] (K : Ideal R)

/-- The finitely generated ideals contained in `K`. -/
abbrev FGLe : Type u := {J : Ideal R // J.FG ∧ J ≤ K}

/-- The zero ideal is a finitely generated ideal inside `K`. -/
instance : Nonempty (FGLe K) := ⟨⟨⊥, Submodule.fg_bot, bot_le⟩⟩

/-- Two finitely generated ideals inside `K` lie in their sum, again finitely generated and
inside `K`. -/
instance : IsDirectedOrder (FGLe K) where
  directed a b := ⟨⟨a.1 ⊔ b.1, Submodule.FG.sup a.2.1 b.2.1, sup_le a.2.2 b.2.2⟩,
    (le_sup_left : a.1 ≤ a.1 ⊔ b.1), (le_sup_right : b.1 ≤ a.1 ⊔ b.1)⟩

/-- The zero ideal, as the least finitely generated ideal inside `K`. -/
def FGLe.bot : FGLe K := ⟨⊥, Submodule.fg_bot, bot_le⟩

/-- Every element of `K` lies in a finitely generated ideal inside `K`. -/
theorem FGLe.exists_mem {a : R} (ha : a ∈ K) : ∃ J : FGLe K, a ∈ J.1 :=
  ⟨⟨Ideal.span {a}, Submodule.fg_span_singleton a, (Ideal.span_singleton_le_iff_mem K).2 ha⟩,
    Ideal.subset_span (Set.mem_singleton a)⟩

/-- The colimit presentation of `R ⧸ K` by the quotients `R ⧸ J`, `J ⊆ K` finitely generated. -/
noncomputable def quotientColimitPresentation :
    ColimitPresentation (FGLe K) (CommAlgCat.of R (R ⧸ K)) where
  diag := quotientDiagram (fun J : FGLe K => J.1) fun _ _ h => h
  ι := (quotientCocone (fun J : FGLe K => J.1) (fun _ _ h => h) K fun J => J.2.2).ι
  isColimit := isColimitQuotientCocone (fun J : FGLe K => J.1) (fun _ _ h => h) K
    (fun J => J.2.2) fun _ ha => FGLe.exists_mem K ha

section Descent

variable {C : Type u} [CommRing C] [Algebra R C]

/-- Étaleness of `A ⊗_R R → A ⊗_R C` is étaleness of `A → A ⊗_R C`. -/
theorem etale_tensorMap_ofId_iff (A : Type u) [CommRing A] [Algebra R A] :
    (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R C)).toRingHom.Etale ↔
      (algebraMap A (A ⊗[R] C)).Etale := by
  have heq : (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R C)).toRingHom =
      (algebraMap A (A ⊗[R] C)).comp
        (Algebra.TensorProduct.rid R R A).toAlgHom.toRingHom := by
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.coe_id, id_eq, Algebra.ofId_apply, RingHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      show a ⊗ₜ[R] (algebraMap R C r) = (r • a) ⊗ₜ[R] (1 : C)
      rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [heq]
  refine ⟨fun h => ?_, RingHom.Etale.respectsIso.2 _ (Algebra.TensorProduct.rid R R A).toRingEquiv⟩
  convert RingHom.Etale.respectsIso.2 _ (Algebra.TensorProduct.rid R R A).symm.toRingEquiv h
    using 1
  ext x
  simp

/-- **Étaleness descends from `R ⧸ K` to `R ⧸ J` for a finitely generated `J ⊆ K`** (Stacks 07RI
for the quotients by the finitely generated subideals of `K`). -/
theorem exists_fg_le_etale_tensor (hC : Algebra.FinitePresentation R C)
    (h : (algebraMap (R ⧸ K) ((R ⧸ K) ⊗[R] C)).Etale) :
    ∃ J : FGLe K, (algebraMap (R ⧸ J.1) ((R ⧸ J.1) ⊗[R] C)).Etale := by
  have hφ : (Algebra.ofId R C).toRingHom.FinitePresentation := by
    show (algebraMap R C).FinitePresentation
    rwa [RingHom.finitePresentation_algebraMap]
  have : IsFiltered (FGLe K) := inferInstance
  have : PreservesColimitsOfShape (FGLe K) (forget CommRingCat.{u}) :=
    CommRingCat.FilteredColimits.forget_preservesFilteredColimits.{u}.preserves_filtered_colimits
      (FGLe K)
  obtain ⟨J, hJ⟩ := RingHom.Etale.exists_baseChange_etale_of_colimitPresentation
    (quotientColimitPresentation K) (Algebra.ofId R C) hφ
    ((etale_tensorMap_ofId_iff (R ⧸ K)).2 h)
  exact ⟨J, (etale_tensorMap_ofId_iff (R ⧸ J.1)).1 hJ⟩

/-- **Surjectivity on spectra descends from `R ⧸ K` to `R ⧸ J` for a finitely generated
`J ⊆ K`** (Stacks 07RR for the quotients by the finitely generated subideals of `K`). -/
theorem exists_fg_le_surjective_comap_tensor (hC : Algebra.FinitePresentation R C)
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap (R ⧸ K) ((R ⧸ K) ⊗[R] C)))) :
    ∃ J : FGLe K,
      Function.Surjective (PrimeSpectrum.comap (algebraMap (R ⧸ J.1) ((R ⧸ J.1) ⊗[R] C))) := by
  classical
  let G : FGLe K → Type u := fun J => R ⧸ J.1
  let f : ∀ i j : FGLe K, i ≤ j → G i →+* G j := fun i j hij => Ideal.Quotient.factor hij
  let φ : ∀ i : FGLe K, G i →+* (R ⧸ K) := fun i => Ideal.Quotient.factor i.2.2
  have : DirectedSystem G fun i j h => f i j h :=
    ⟨fun i x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl,
    fun k j i hij hjk x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl⟩
  have hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x := by
    intro i j h x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have hsurj : ∀ a : R ⧸ K, ∃ (i : FGLe K) (x : G i), φ i x = a := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨FGLe.bot K, Ideal.Quotient.mk _ x, rfl⟩
  have hzero : ∀ (i : FGLe K) (x : G i), φ i x = 0 → ∃ (j : FGLe K) (h : i ≤ j), f i j h x = 0 := by
    intro i x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hxK : x ∈ K := Ideal.Quotient.eq_zero_iff_mem.1 hx
    refine ⟨⟨i.1 ⊔ Ideal.span {x}, Submodule.FG.sup i.2.1 (Submodule.fg_span_singleton x),
      sup_le i.2.2 ((Ideal.span_singleton_le_iff_mem K).2 hxK)⟩,
      (le_sup_left : i.1 ≤ i.1 ⊔ Ideal.span {x}), ?_⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton x)))
  let i := FGLe.bot K
  let C' := G i ⊗[R] C
  have hC' : (algebraMap (G i) C').FinitePresentation := by
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  let θ : C' →+* (R ⧸ K) ⊗[R] C :=
    (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R i.2.2) (AlgHom.id R C)).toRingHom
  have hcomm : (algebraMap (R ⧸ K) ((R ⧸ K) ⊗[R] C)).comp (φ i) =
      θ.comp (algebraMap (G i) C') := by
    refine RingHom.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  obtain ⟨j, hij, hs⟩ := PrimeSpectrum.exists_ge_surjective_comap_tensorProduct_of_directed
    hφ hsurj hzero hC' (algebraMap (R ⧸ K) ((R ⧸ K) ⊗[R] C)) θ hcomm h
  let := (f i j hij).toAlgebra
  have : IsScalarTower R (G i) (G j) := IsScalarTower.of_algebraMap_eq fun r => rfl
  exact ⟨j, PrimeSpectrum.surjective_comap_algebraMap_of_algEquiv
    (Algebra.TensorProduct.cancelBaseChange R (G i) (G j) (G j) C) hs⟩

end Descent

section Pushout

variable {B S P : Type u} [CommRing B] [CommRing S] [CommRing P] [Algebra R B] [Algebra R S]

/-- The comparison of a pushout of `R ⟶ S` and `R ⟶ B` with `S ⊗_R B`, read on the left leg. -/
theorem exists_ringEquiv_tensor_of_isPushout (σ : S →+* P) (β : B →+* P)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom σ) (CommRingCat.ofHom β)) :
    ∃ e : S ⊗[R] B ≃+* P, e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = σ := by
  let H₀ := CommRingCat.isPushout_tensorProduct R S B
  let e := H₀.isoIsPushout _ _ H
  refine ⟨e.commRingCatIsoToRingEquiv, ?_⟩
  exact congrArg (fun f : CommRingCat.of S ⟶ CommRingCat.of P => f.hom)
    (H₀.inl_isoIsPushout_hom _ _ H)

variable (hS : Function.Surjective (algebraMap R S))

include hS in
/-- For a surjection `R ⟶ S` with kernel `K`, the inclusion `S ⟶ S ⊗_R B` is, up to isomorphism,
the inclusion `R ⧸ K ⟶ (R ⧸ K) ⊗_R B`. -/
theorem exists_ringEquiv_quotient_tensor :
    ∃ (e₁ : R ⧸ RingHom.ker (algebraMap R S) ≃+* S)
      (e₂ : (R ⧸ RingHom.ker (algebraMap R S)) ⊗[R] B ≃+* S ⊗[R] B),
      e₂.toRingHom.comp (algebraMap (R ⧸ RingHom.ker (algebraMap R S))
        ((R ⧸ RingHom.ker (algebraMap R S)) ⊗[R] B)) =
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B).comp e₁.toRingHom := by
  let eS : (R ⧸ RingHom.ker (algebraMap R S)) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hS
  refine ⟨eS.toRingEquiv, (Algebra.TensorProduct.congr eS AlgEquiv.refl).toRingEquiv, ?_⟩
  refine RingHom.ext fun x => ?_
  simp [Algebra.TensorProduct.algebraMap_apply]

/-- A pushout leg along a surjection `R ⟶ S` is the base change `R ⧸ K ⟶ (R ⧸ K) ⊗_R B` up to
isomorphisms on both sides. -/
private theorem exists_ringEquiv_comp_eq_of_isPushout (hS : Function.Surjective (algebraMap R S))
    (σ : S →+* P) (β : B →+* P)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom σ) (CommRingCat.ofHom β)) :
    ∃ (e₁ : S ≃+* R ⧸ RingHom.ker (algebraMap R S))
      (e₂ : (R ⧸ RingHom.ker (algebraMap R S)) ⊗[R] B ≃+* P),
      σ = (e₂.toRingHom.comp (algebraMap (R ⧸ RingHom.ker (algebraMap R S))
        ((R ⧸ RingHom.ker (algebraMap R S)) ⊗[R] B))).comp e₁.toRingHom := by
  obtain ⟨e, he⟩ := exists_ringEquiv_tensor_of_isPushout σ β H
  obtain ⟨e₁, e₂, h₁₂⟩ := exists_ringEquiv_quotient_tensor (B := B) hS
  refine ⟨e₁.symm, e₂.trans e, ?_⟩
  rw [← he]
  ext x
  have h := congrArg (fun φ => φ (e₁.symm x)) h₁₂
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply] at h
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.trans_apply, h]

include hS in
/-- **Étaleness of a pushout leg along a surjection is étaleness over the quotient.** -/
theorem etale_iff_etale_quotient_tensor_of_isPushout (σ : S →+* P) (β : B →+* P)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom σ) (CommRingCat.ofHom β)) :
    σ.Etale ↔ (algebraMap (R ⧸ RingHom.ker (algebraMap R S))
      ((R ⧸ RingHom.ker (algebraMap R S)) ⊗[R] B)).Etale := by
  obtain ⟨e₁, e₂, hσ⟩ := exists_ringEquiv_comp_eq_of_isPushout hS σ β H
  rw [hσ]
  refine ⟨fun h => ?_, fun h =>
    RingHom.Etale.respectsIso.2 _ e₁ (RingHom.Etale.respectsIso.1 _ e₂ h)⟩
  convert RingHom.Etale.respectsIso.1 _ e₂.symm (RingHom.Etale.respectsIso.2 _ e₁.symm h)
    using 1
  ext x
  simp

/-- The spectrum map of a ring isomorphism is bijective. -/
theorem bijective_comap_ringEquiv {A A' : Type u} [CommRing A] [CommRing A'] (e : A ≃+* A') :
    Function.Bijective (PrimeSpectrum.comap e.toRingHom) :=
  (PrimeSpectrum.comapEquiv e.symm).bijective

include hS in
/-- **Surjectivity on spectra of a pushout leg along a surjection is surjectivity over the
quotient.** -/
theorem surjective_comap_iff_quotient_tensor_of_isPushout (σ : S →+* P) (β : B →+* P)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom σ) (CommRingCat.ofHom β)) :
    Function.Surjective (PrimeSpectrum.comap σ) ↔
      Function.Surjective (PrimeSpectrum.comap (algebraMap (R ⧸ RingHom.ker (algebraMap R S))
        ((R ⧸ RingHom.ker (algebraMap R S)) ⊗[R] B))) := by
  obtain ⟨e₁, e₂, hσ⟩ := exists_ringEquiv_comp_eq_of_isPushout hS σ β H
  rw [hσ, PrimeSpectrum.comap_comp, PrimeSpectrum.comap_comp]
  have h₁ := bijective_comap_ringEquiv e₁
  have h₂ := bijective_comap_ringEquiv e₂
  exact ⟨fun h => (h.of_comp_left h₁.1).of_comp, fun h => h₁.2.comp (h.comp h₂.2)⟩

end Pushout

section Monotone

variable {C : Type u} [CommRing C] [Algebra R C] {J J' : Ideal R} (hJJ' : J ≤ J')

include hJJ' in
/-- Étaleness of `R ⧸ J ⟶ (R ⧸ J) ⊗_R C` passes to every larger ideal `J'`. -/
theorem etale_tensor_of_le (h : (algebraMap (R ⧸ J) ((R ⧸ J) ⊗[R] C)).Etale) :
    (algebraMap (R ⧸ J') ((R ⧸ J') ⊗[R] C)).Etale := by
  let : Algebra (R ⧸ J) (R ⧸ J') := (Ideal.Quotient.factor hJJ').toAlgebra
  have : IsScalarTower R (R ⧸ J) (R ⧸ J') := IsScalarTower.of_algebraMap_eq fun r => rfl
  have : Algebra.Etale (R ⧸ J) ((R ⧸ J) ⊗[R] C) := RingHom.etale_algebraMap.1 h
  rw [RingHom.etale_algebraMap]
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (R ⧸ J) (R ⧸ J') (R ⧸ J') C)

include hJJ' in
/-- Surjectivity on spectra of `R ⧸ J ⟶ (R ⧸ J) ⊗_R C` passes to every larger ideal `J'`. -/
theorem surjective_comap_tensor_of_le
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap (R ⧸ J) ((R ⧸ J) ⊗[R] C)))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap (R ⧸ J') ((R ⧸ J') ⊗[R] C))) := by
  let : Algebra (R ⧸ J) (R ⧸ J') := (Ideal.Quotient.factor hJJ').toAlgebra
  have : IsScalarTower R (R ⧸ J) (R ⧸ J') := IsScalarTower.of_algebraMap_eq fun r => rfl
  have h' : Function.Surjective (PrimeSpectrum.comap (algebraMap (R ⧸ J')
      ((R ⧸ J') ⊗[R ⧸ J] ((R ⧸ J) ⊗[R] C)))) := fun p =>
    PrimeSpectrum.mem_range_comap_tensorProduct_of_mem_range_comap p (h _)
  exact PrimeSpectrum.surjective_comap_algebraMap_of_algEquiv
    (Algebra.TensorProduct.cancelBaseChange R (R ⧸ J) (R ⧸ J') (R ⧸ J') C) h'

end Monotone

end Ideal

end
