module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsUlift
public import StacksFrontier.Homology.Eta.Perfect.GoodBaseChangeFlat
public import StacksFrontier.Homology.Eta.Perfect.QuotientEtaHomology
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses

/-!
# Rank of the cohomology of the reduced décalage at a prime

Let `f ∈ A` be a nonzerodivisor, `p ∋ f` a prime with localization `R = A_p`, and `M^•` a complex
of `f`-torsion-free `A`-modules whose cohomology becomes finite free over `R`.  For a surjection
`φ : A → C` with kernel `fA` and a prime `q` of `C` over `p` with localization `L = C_q`, the
cohomology of `C ⊗_A η_f M^•` becomes finite free over `L` of the same rank as that of `M^•`
over `R`.

## Main results

* `Stacks.Eta.QuotientHomology.free_finrank_tensor_homology_extendScalars_etaObject`:
  `L ⊗_C H^n(C ⊗_A η_f M^•)` is free over `L`, of the same rank as `R ⊗_A H^n(M^•)` over `R`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.Eta.QuotientHomology

section Helpers

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Flat base change commutes with cohomology, as an `S`-linear equivalence
`H^n(S ⊗_R K) ≃ S ⊗_R H^n(K)`. -/
def homologyExtendScalarsEquiv [Module.Flat R S] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) :
    (((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology n ≃ₗ[S] S ⊗[R] K.homology n :=
  (ModuleCat.extendScalarsHomologyIso.{u, u, u} (algebraMap R S)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) K n).toLinearEquiv.trans
    (ModuleCat.extendScalarsAlgebraEquiv (K.homology n))

/-- Extension of scalars along `algebraMap R S`, applied termwise to a complex `K`, is the
base-change complex `S ⊗_R K`. -/
def extendScalarsMapIsoBaseChangeComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ≅ GoodBaseChange.baseChangeComplex (B := S) K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (ModuleCat.extendScalarsAlgebraEquiv (K.X i)).toModuleIso) fun i j _ => by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul s m => rfl
      | add x y hx hy =>
        change _ = _ at hx hy
        exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

/-- An `S`-module linearly equivalent to `S ⊗_R F`, for `F` finite free over `R`, is finite free
over `S` of the same rank. -/
theorem free_finite_finrank_of_equiv_baseChange [StrongRankCondition R] [StrongRankCondition S]
    {X F : Type u}
    [AddCommGroup X] [Module S X] [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] (e : X ≃ₗ[S] S ⊗[R] F) :
    Module.Free S X ∧ Module.Finite S X ∧ Module.finrank S X = Module.finrank R F :=
  ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, by
    rw [e.finrank_eq, Module.finrank_baseChange]⟩

/-- An element regular in `R` is regular on every free `R`-module. -/
theorem isSMulRegular_of_free {F : Type u} [AddCommGroup F] [Module R F] [Module.Free R F]
    {g : R} (hg : IsSMulRegular R g) : IsSMulRegular F g :=
  (TensorProduct.lid R F).isSMulRegular_congr g |>.mp (hg.rTensor F)

/-- If `f` is regular on `P` and `S` is flat over `R`, the image of `f` in `S` is regular on
`S ⊗_R P`. -/
theorem isSMulRegular_tensor_of_flat [Module.Flat R S] {P : Type u} [AddCommGroup P]
    [Module R P] {f : R} (hP : IsSMulRegular P f) :
    IsSMulRegular (S ⊗[R] P) (algebraMap R S f) :=
  hP.of_flat_of_isBaseChange (TensorProduct.isBaseChange R P S)

end Helpers

section Ring

variable {A : Type u} (R : Type u) {C : Type u} (L : Type u) [CommRing A] [CommRing R]
  [CommRing C] [CommRing L] [Algebra A R] [Algebra C L] (p : Ideal A) [p.IsPrime]
  [IsLocalization.AtPrime R p] {φ : A →+* C} (q : Ideal C) [q.IsPrime] (hq : q.comap φ = p)
  [IsLocalization.AtPrime L q]

include hq in
/-- An element of `A` outside `p` maps outside `q`. -/
theorem notMem_of_notMem {s : A} (hs : s ∈ p.primeCompl) : φ s ∈ q.primeCompl := fun h =>
  hs (hq ▸ h)

/-- If `φ s` lies outside `q`, then `s` lies outside `p`. -/
private theorem mem_primeCompl_of_map_mem (hq : q.comap φ = p) {s : A} {c : C} (hs : φ s = c)
    (hc : c ∈ q.primeCompl) : s ∈ p.primeCompl := fun h =>
  hc (hs ▸ (hq ▸ h : s ∈ q.comap φ))

include hq in
/-- The elements outside `p` become units in `L = C_q`. -/
theorem isUnit_comp_of_notMem (s : p.primeCompl) : IsUnit (((algebraMap C L).comp φ) s) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff (S := L) (I := q) (φ s)).2
    (notMem_of_notMem p q hq s.2)

/-- The map `R = A_p → L = C_q` induced by `φ`. -/
def localizationMap : R →+* L :=
  IsLocalization.lift (M := p.primeCompl) (S := R) (isUnit_comp_of_notMem L p q hq)

/-- `localizationMap` sends the image of `a : A` in `R` to the image of `φ a` in `L`. -/
theorem localizationMap_algebraMap (a : A) :
    localizationMap R L p q hq (algebraMap A R a) = algebraMap C L (φ a) :=
  IsLocalization.lift_eq _ a

variable {p q} (hφ : Function.Surjective φ)

include hφ in
/-- If `φ` is surjective, then so is `localizationMap`. -/
theorem surjective_localizationMap : Function.Surjective (localizationMap R L p q hq) := by
  intro z
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
  obtain ⟨a, rfl⟩ := hφ c
  obtain ⟨s, hs⟩ := hφ t
  have hsp := mem_primeCompl_of_map_mem p q hq hs t.2
  refine ⟨IsLocalization.mk' R a ⟨s, hsp⟩, ?_⟩
  rw [localizationMap, IsLocalization.lift_mk'_spec, RingHom.comp_apply, RingHom.comp_apply]
  change _ = algebraMap C L (φ s) * _
  rw [hs, IsLocalization.mk'_spec']

variable (f : A) (hker : RingHom.ker φ = Ideal.span {f})

include hφ hker in
/-- If `φ` is surjective with kernel `(f)`, then the kernel of `localizationMap` is generated
by the image of `f` in `R`. -/
theorem ker_localizationMap :
    RingHom.ker (localizationMap R L p q hq) = Ideal.span {algebraMap A R f} := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    rw [localizationMap, IsLocalization.lift_mk'_spec, mul_zero, RingHom.comp_apply] at hz
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl L (φ a)).1 hz
    obtain ⟨s', hs'⟩ := hφ m
    have hs'p := mem_primeCompl_of_map_mem p q hq hs' m.2
    have hmem : s' * a ∈ Ideal.span {f} := by
      rw [← hker, RingHom.mem_ker, map_mul, hs', hm]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    refine Ideal.mem_span_singleton'.2 ⟨IsLocalization.mk' R c (s * ⟨s', hs'p⟩), ?_⟩
    rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [Submonoid.coe_mul]
    linear_combination (s : A) * hc
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      localizationMap_algebraMap]
    have : φ f = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self f
    rw [this, map_zero]

/-- For `φ` surjective with kernel `(f)`, the ring isomorphism `R/fR ≃ L` induced by
`localizationMap`. -/
def quotientLocalizationEquiv : R ⧸ Ideal.span {algebraMap A R f} ≃+* L :=
  (Ideal.quotEquivOfEq (ker_localizationMap R L hq hφ f hker).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_localizationMap R L hq hφ))

/-- The composite `A → R → R/fR ≃ L` agrees with `A → C → L`. -/
theorem quotientLocalizationEquiv_comp :
    (quotientLocalizationEquiv R L hq hφ f hker : R ⧸ Ideal.span {algebraMap A R f} →+* L).comp
        ((Ideal.Quotient.mk (Ideal.span {algebraMap A R f})).comp (algebraMap A R)) =
      (algebraMap C L).comp φ := by
  ext a
  change (RingHom.quotientKerEquivOfSurjective (surjective_localizationMap R L hq hφ))
    (Ideal.quotEquivOfEq (ker_localizationMap R L hq hφ f hker).symm
      (Ideal.Quotient.mk (Ideal.span {algebraMap A R f}) (algebraMap A R a))) = _
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    localizationMap_algebraMap]
  rfl

end Ring

section Main

/-- A torsion-free complex in the sense of `EtaComplex.IsTorsionFree` has `f`-regular terms. -/
theorem isSMulRegular_of_isTorsionFree {A : Type u} [CommRing A] {f : A}
    {K : CochainComplex (ModuleCat.{u} A) ℤ} (h : EtaComplex.IsTorsionFree f K) (i : ℤ) :
    IsSMulRegular (K.X i) f := fun x y hxy =>
  sub_eq_zero.mp (h i (x - y) (by rw [smul_sub]; exact sub_eq_zero.mpr hxy))

/-- **The cohomology of the reduced décalage at a prime.**  Let `f ∈ A` be a nonzerodivisor,
`p ∋ f` a prime with localization `R = A_p`, and `M^•` a complex of `f`-torsion-free
`A`-modules with `R ⊗_A H^i(M^•)` finite free for every `i`.  Let `φ : A → C` be surjective with
kernel `fA`, and `q` a prime of `C` over `p` with localization `L = C_q`.  Then
`L ⊗_C H^n(C ⊗_A η_f M^•)` is free over `L`, of the same rank as `R ⊗_A H^n(M^•)` over `R`. -/
theorem free_finrank_tensor_homology_extendScalars_etaObject {A R C L : Type u} [CommRing A]
    [CommRing R] [CommRing C] [CommRing L] [Algebra A R] [Algebra C L] (f : A)
    (hf : IsRegular f) (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime R p]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (hM : ∀ i, IsSMulRegular (M.X i) f)
    (hfree : ∀ i, Module.Free R (R ⊗[A] M.homology i) ∧ Module.Finite R (R ⊗[A] M.homology i))
    (φ : A →+* C) (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {f})
    (q : Ideal C) [q.IsPrime] (hq : q.comap φ = p) [IsLocalization.AtPrime L q] (n : ℤ) :
    Module.Free L (L ⊗[C] (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (EtaComplex.etaObject.{u, u} f M)).homology n) ∧
      Module.finrank L (L ⊗[C] (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (EtaComplex.etaObject.{u, u} f M)).homology n) =
        Module.finrank R (R ⊗[A] M.homology n) := by
  classical
  have : Module.Flat A R := IsLocalization.flat R p.primeCompl
  have : Module.Flat C L := IsLocalization.flat L q.primeCompl
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p
  have : IsLocalRing L := IsLocalization.AtPrime.isLocalRing L q
  set g : R := algebraMap A R f with hg
  let θ := quotientLocalizationEquiv R L hq hφ f hker
  have : Nontrivial (R ⧸ Ideal.span {g}) := θ.toEquiv.nontrivial
  let N := GoodBaseChange.baseChangeComplex (B := R) M
  have hgR : IsSMulRegular R g := IsSMulRegular.of_isLocalization R p.primeCompl hf.left
  have hNX : ∀ i, IsSMulRegular (N.X i) g := fun i => isSMulRegular_tensor_of_flat (hM i)
  let eN : ∀ i, N.homology i ≃ₗ[R] R ⊗[A] M.homology i := fun i =>
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (extendScalarsMapIsoBaseChangeComplex (S := R) M)).toLinearEquiv.symm.trans
        (homologyExtendScalarsEquiv M i)
  have hreg : ∀ {X : Type u} [AddCommGroup X] [Module R X] (i : ℤ),
      (X ≃ₗ[R] R ⊗[A] M.homology i) → IsSMulRegular X g := fun i e => by
    have := (hfree i).1
    exact (e.isSMulRegular_congr g).mpr (isSMulRegular_of_free hgR)
  let η := EtaComplex.etaObject.{u, u} f M
  let ηR := ((ModuleCat.extendScalars.{u, u, u} (algebraMap A R)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj η
  let e5 : ηR ≅ EtaComplex.etaObject.{u, u} g N :=
    extendScalarsMapIsoBaseChangeComplex η ≪≫
      @asIso _ _ _ _ _ (GoodBaseChange.isIso_etaBaseChangeMap_of_flat (B := R) f M)
  let eηR : ∀ i, ηR.homology i ≃ₗ[R] R ⊗[A] M.homology i := fun i =>
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso e5).toLinearEquiv.trans
      ((QuotientHomology.nonempty_homology_etaObject_equiv N hNX i
        (hreg i (eN i))).some.trans (eN i))
  have hηRX : ∀ i, IsSMulRegular (ηR.X i) g := fun i =>
    ((ModuleCat.extendScalarsAlgebraEquiv (S := R) (η.X i)).isSMulRegular_congr g).mpr
      (isSMulRegular_tensor_of_flat
        (isSMulRegular_of_isTorsionFree (EtaComplex.etaObject_torsionFree f M) i))
  let X := ((ModuleCat.extendScalars.{u, u, u} (quotMap g)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj ηR
  obtain ⟨eX⟩ := nonempty_homology_extendScalars_quotient_equiv ηR hηRX n (hreg _ (eηR (n + 1)))
  let : Algebra (R ⧸ Ideal.span {g}) L := (θ : R ⧸ Ideal.span {g} →+* L).toAlgebra
  have : Module.Flat (R ⧸ Ideal.span {g}) L :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective θ.bijective)
  let Y := ((ModuleCat.extendScalars.{u, u, u}
    (algebraMap (R ⧸ Ideal.span {g}) L)).mapHomologicalComplex (ComplexShape.up ℤ)).obj X
  let eY : Y.homology n ≃ₗ[L] L ⊗[R ⧸ Ideal.span {g}] X.homology n :=
    homologyExtendScalarsEquiv X n
  let Φ : ModuleCat.extendScalars.{u, u, u} φ ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap C L) ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A R) ⋙
        ModuleCat.extendScalars.{u, u, u} (quotMap g)) ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap (R ⧸ Ideal.span {g}) L) :=
    (ModuleCat.extendScalarsComp φ (algebraMap C L)).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars
        (quotientLocalizationEquiv_comp R L hq hφ f hker).symm) ≪≫
      ModuleCat.extendScalarsComp ((quotMap g).comp (algebraMap A R))
        (algebraMap (R ⧸ Ideal.span {g}) L) ≪≫
      Functor.isoWhiskerRight (ModuleCat.extendScalarsComp (algebraMap A R) (quotMap g)) _
  let eK : ((ModuleCat.extendScalars.{u, u, u} (algebraMap C L)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj η) ≅ Y :=
    (Functor.mapHomologicalComplexCompIso
        (F := ModuleCat.extendScalars.{u, u, u} φ)
        (G := ModuleCat.extendScalars.{u, u, u} (algebraMap C L)) (Iso.refl _) _).app η ≪≫
      (NatIso.mapHomologicalComplex Φ _).app η ≪≫
      (Functor.mapHomologicalComplexCompIso
        (F := ModuleCat.extendScalars.{u, u, u} (algebraMap A R) ⋙
          ModuleCat.extendScalars.{u, u, u} (quotMap g))
        (G := ModuleCat.extendScalars.{u, u, u} (algebraMap (R ⧸ Ideal.span {g}) L))
        (Iso.refl _) _).symm.app η ≪≫
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap (R ⧸ Ideal.span {g}) L)).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso
        ((Functor.mapHomologicalComplexCompIso
          (F := ModuleCat.extendScalars.{u, u, u} (algebraMap A R))
          (G := ModuleCat.extendScalars.{u, u, u} (quotMap g)) (Iso.refl _) _).symm.app η)
  let eTot : L ⊗[C] (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj η).homology n ≃ₗ[L]
      L ⊗[R ⧸ Ideal.span {g}] ((R ⧸ Ideal.span {g}) ⊗[R] (R ⊗[A] M.homology n)) :=
    (homologyExtendScalarsEquiv _ n).symm.trans
      (((HomologicalComplex.homologyFunctor _ _ n).mapIso eK).toLinearEquiv.trans
        (eY.trans (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
          (eX.trans (TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl (R ⧸ Ideal.span {g}) (R ⧸ Ideal.span {g})) (eηR n))))))
  have := (hfree n).1
  have := (hfree n).2
  obtain ⟨h1, h2, h3⟩ := free_finite_finrank_of_equiv_baseChange
    (LinearEquiv.refl (R ⧸ Ideal.span {g}) ((R ⧸ Ideal.span {g}) ⊗[R] (R ⊗[A] M.homology n)))
  obtain ⟨k1, -, k3⟩ := free_finite_finrank_of_equiv_baseChange eTot
  exact ⟨k1, k3.trans h3⟩

end Main

end Stacks.Eta.QuotientHomology

end
