module

public import StacksFrontier.Homology.Tor.Independence

@[expose] public noncomputable section

/-!
# Localizing Tor modules at primes of the tensor product

For `R`-algebras `A`, `B`, a prime `s` of `A ⊗[R] B`, and the primes `p = A ∩ s`, `q = B ∩ s`
lying over `r ⊂ R`, the localization at `s` of `Tor_i^R(A, B)` agrees with the localization at
`s` of `Tor_i^{R_r}(A_p, B_q)`. This is the identification displayed in the statement of
Stacks 08HX, obtained from the change-of-rings isomorphism of Stacks 08HW.

## Main definitions

* `RingTheory.TorIndependence.localizedModuleTorEquiv`: the `A ⊗[R] B`-linear identification
  `Tor_i^R(A, B)_s ≃ Tor_i^{R_r}(A_p, B_q)_s`.

## Implementation notes

The module `Tor_i^{R_r}(A_p, B_q)` carries its canonical `A_p ⊗[R_r] B_q`-module structure; it
is regarded as an `A ⊗[R] B`-module along the canonical ring map
`A ⊗[R] B → A_p ⊗[R_r] B_q` before being localized at `s`.

## References

* [The Stacks Project, Tag 08HX](https://stacks.math.columbia.edu/tag/08HX)
-/

open CategoryTheory

open scoped TensorProduct

namespace RingTheory.TorIndependence

universe u

/-- Let `D` be a `P`-algebra such that every element of `D`, multiplied by the image of a
suitable element of `S`, lies in the image of `P`, and suppose that `D` maps to the
localization `L` of `P` at `S` as a `P`-algebra. Then for every `P`-module `N` and every
`P`-module `M` identified with `D ⊗[P] N`, the map `N → M_S`, `x ↦ 1 ⊗ x`, is a localization
of `N` at `S`. -/
theorem isLocalizedModule_mkLinearMap_comp_tensorMk
    {P D L : Type*} [CommRing P] [CommRing D] [CommRing L] [Algebra P D] [Algebra P L]
    (S : Submonoid P) [IsLocalization S L] (g : D →ₐ[P] L)
    (H : ∀ d : D, ∃ u ∈ S, ∃ x : P, algebraMap P D u * d = algebraMap P D x)
    {N M : Type*} [AddCommGroup N] [Module P N] [AddCommGroup M] [Module P M]
    (E : D ⊗[P] N ≃ₗ[P] M) :
    IsLocalizedModule S ((LocalizedModule.mkLinearMap S M).comp
      (E.toLinearMap.comp (TensorProduct.mk P D N 1))) := by
  have key : ∀ m : D ⊗[P] N, ∃ u ∈ S, ∃ x : N, u • m = (1 : D) ⊗ₜ[P] x := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => exact ⟨1, S.one_mem, 0, by simp⟩
    | tmul d n =>
      obtain ⟨u, hu, x, hx⟩ := H d
      refine ⟨u, hu, x • n, ?_⟩
      rw [TensorProduct.smul_tmul', Algebra.smul_def, hx, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    | add a b ha hb =>
      obtain ⟨u₁, hu₁, x₁, hx₁⟩ := ha
      obtain ⟨u₂, hu₂, x₂, hx₂⟩ := hb
      refine ⟨u₁ * u₂, S.mul_mem hu₁ hu₂, u₂ • x₁ + u₁ • x₂, ?_⟩
      rw [smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
        ← hx₁, ← hx₂, mul_comm u₁ u₂, mul_smul, mul_comm u₂ u₁, mul_smul u₁ u₂ b]
  constructor
  · intro u
    exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M) u
  · intro y
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S M) y
    obtain ⟨u, hu, x, hx⟩ := key (E.symm m)
    refine ⟨(x, ⟨u, hu⟩ * s), ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.mk_apply] at hs ⊢
    rw [← hx, map_smul, LinearEquiv.apply_symm_apply, map_smul, ← hs, mul_smul]
    rfl
  · intro x₁ x₂ h
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.mk_apply] at h
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S)
      (f := LocalizedModule.mkLinearMap S M) h
    rw [Submonoid.smul_def, Submonoid.smul_def, ← map_smul, ← map_smul, E.injective.eq_iff,
      ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul] at hc
    have hL := congrArg (LinearMap.rTensor N g.toLinearMap) hc
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at hL
    obtain ⟨c', hc'⟩ := IsLocalizedModule.exists_of_eq (S := S)
      (f := TensorProduct.mk P L N 1) hL
    exact ⟨c' * c, by simpa only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul] using hc'⟩

/-- **Stacks 08HX**, the displayed identification. Let `s` be a prime of `A ⊗[R] B` and let
`p = A ∩ s`, `q = B ∩ s` lie over the prime `r` of `R`. Then
`Tor_i^R(A, B)_s ≃ Tor_i^{R_r}(A_p, B_q)_s` as `A ⊗[R] B`-modules, where `Tor_i^{R_r}(A_p, B_q)`
is regarded as an `A ⊗[R] B`-module along the canonical map `A ⊗[R] B → A_p ⊗[R_r] B_q`.
It is the localization at `s` of the canonical change-of-rings map, and comes from the
isomorphism of Stacks 08HW. -/
@[stacks 08HX "the identification Tor_i^R(A,B)_s = Tor_i^{R_r}(A_p,B_q)_s displayed in \
  part (3) of the lemma, as a linear equivalence of localized A ⊗_R B-modules"]
public def localizedModuleTorEquiv
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (s : PrimeSpectrum (A ⊗[R] B))
    (r : PrimeSpectrum R) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    [p.asIdeal.LiesOver r.asIdeal] [q.asIdeal.LiesOver r.asIdeal]
    [Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal)]
    [Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime q.asIdeal)]
    [Localization.AtPrime.IsLiesOverAlgebra r.asIdeal p.asIdeal]
    [Localization.AtPrime.IsLiesOverAlgebra r.asIdeal q.asIdeal]
    (hp : p.asIdeal = s.asIdeal.comap (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B))
    (hq : q.asIdeal = s.asIdeal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B))
    (i : ℕ) :
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B i
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty
      (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) i
    letI : Module (A ⊗[R] B) (TorChangeOfRings.torObj (Localization.AtPrime r.asIdeal) i
        (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) :=
      Module.compHom _ (TorChangeOfRings.tensorProductMap R (Localization.AtPrime r.asIdeal) A B
        (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
        (IsScalarTower.toAlgHom R A _) (IsScalarTower.toAlgHom R B _))
    LocalizedModule s.asIdeal.primeCompl (TorChangeOfRings.torObj R i A B) ≃ₗ[A ⊗[R] B]
      LocalizedModule s.asIdeal.primeCompl
        (TorChangeOfRings.torObj (Localization.AtPrime r.asIdeal) i
          (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) :=
  letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B i
  letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty
    (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime q.asIdeal) i
  let Rr := Localization.AtPrime r.asIdeal
  let Ap := Localization.AtPrime p.asIdeal
  let Bq := Localization.AtPrime q.asIdeal
  let fA := IsScalarTower.toAlgHom R A Ap
  let fB := IsScalarTower.toAlgHom R B Bq
  let D := Ap ⊗[Rr] Bq
  let f := TorChangeOfRings.tensorProductMap R Rr A B Ap Bq fA fB
  letI : Algebra (A ⊗[R] B) D := f.toAlgebra
  letI : Module (A ⊗[R] B) (TorChangeOfRings.torObj Rr i Ap Bq) := Module.compHom _ f
  let e := TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
    R Rr A B Ap Bq i fA fB
  haveI : IsIso e := isIso_torExtensionMap_atPrime R A B r p q i
  let E₀ := (asIso e).toLinearEquiv
  let E : D ⊗[A ⊗[R] B] TorChangeOfRings.torObj R i A B ≃ₗ[A ⊗[R] B]
      TorChangeOfRings.torObj Rr i Ap Bq :=
    { toFun := E₀
      invFun := E₀.symm
      left_inv := E₀.left_inv
      right_inv := E₀.right_inv
      map_add' := E₀.map_add
      map_smul' := fun c x ↦ by
        have : c • x = f c • x := by
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul d t => rfl
          | add x y hx hy => rw [smul_add, hx, hy, smul_add]
        rw [this]
        exact E₀.map_smul (f c) x }
  let gA := Localization.localAlgHom p.asIdeal s.asIdeal
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) hp
  let gB := Localization.localAlgHom q.asIdeal s.asIdeal
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) hq
  let g := (Algebra.TensorProduct.lift gA gB (fun _ _ ↦ Commute.all _ _)).toRingHom.comp
    (IsLocalization.algebraTensorEquiv r.asIdeal.primeCompl Rr Ap Bq).toRingHom
  have hg : g.comp f = algebraMap (A ⊗[R] B) (Localization.AtPrime s.asIdeal) := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hf : f (a ⊗ₜ[R] b) = fA a ⊗ₜ[Rr] fB b := by
        simp [f, TorChangeOfRings.tensorProductMap, Algebra.TensorProduct.tmul_mul_tmul]
      rw [RingHom.comp_apply, hf]
      change gA (fA a) * gB (fB b) = _
      have h₁ : gA (fA a) =
          algebraMap (A ⊗[R] B) (Localization.AtPrime s.asIdeal) (a ⊗ₜ[R] 1) :=
        Localization.localRingHom_to_map p.asIdeal s.asIdeal _ hp a
      have h₂ : gB (fB b) =
          algebraMap (A ⊗[R] B) (Localization.AtPrime s.asIdeal) (1 ⊗ₜ[R] b) :=
        Localization.localRingHom_to_map q.asIdeal s.asIdeal _ hq b
      rw [h₁, h₂, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp_all only [map_add]
  let g' : D →ₐ[A ⊗[R] B] Localization.AtPrime s.asIdeal :=
    { __ := g, commutes' := fun x ↦ congrArg (fun k : _ →+* _ ↦ k x) hg }
  have H : ∀ d : D, ∃ u ∈ s.asIdeal.primeCompl, ∃ x : A ⊗[R] B,
      algebraMap (A ⊗[R] B) D u * d = algebraMap (A ⊗[R] B) D x := by
    intro d
    induction d using TensorProduct.induction_on with
    | zero => exact ⟨1, s.asIdeal.primeCompl.one_mem, 0, by simp⟩
    | tmul a' b' =>
      obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.asIdeal.primeCompl a'
      obtain ⟨⟨b, v⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl b'
      refine ⟨(u : A) ⊗ₜ[R] (v : B), ?_, a ⊗ₜ[R] b, ?_⟩
      · have hu : (u : A) ⊗ₜ[R] (1 : B) ∈ s.asIdeal.primeCompl := by
          intro h
          exact u.2 ((SetLike.ext_iff.mp hp _).mpr h)
        have hv : (1 : A) ⊗ₜ[R] (v : B) ∈ s.asIdeal.primeCompl := by
          intro h
          exact v.2 ((SetLike.ext_iff.mp hq _).mpr h)
        simpa [Algebra.TensorProduct.tmul_mul_tmul] using s.asIdeal.primeCompl.mul_mem hu hv
      · change f _ * _ = f _
        simp only [f, TorChangeOfRings.tensorProductMap, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
          AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        change (algebraMap A Ap (u : A) * _) ⊗ₜ[Rr] (algebraMap B Bq (v : B) * _) =
          algebraMap A Ap a ⊗ₜ[Rr] algebraMap B Bq b
        rw [IsLocalization.mk'_spec', IsLocalization.mk'_spec']
    | add x y hx hy =>
      obtain ⟨u₁, hu₁, x₁, hx₁⟩ := hx
      obtain ⟨u₂, hu₂, x₂, hx₂⟩ := hy
      refine ⟨u₁ * u₂, s.asIdeal.primeCompl.mul_mem hu₁ hu₂, u₂ * x₁ + u₁ * x₂, ?_⟩
      simp only [map_mul, map_add]
      linear_combination (algebraMap (A ⊗[R] B) D u₂) * hx₁ +
        (algebraMap (A ⊗[R] B) D u₁) * hx₂
  haveI := isLocalizedModule_mkLinearMap_comp_tensorMk s.asIdeal.primeCompl g' H E
  IsLocalizedModule.iso s.asIdeal.primeCompl
    ((LocalizedModule.mkLinearMap s.asIdeal.primeCompl _).comp
      (E.toLinearMap.comp (TensorProduct.mk (A ⊗[R] B) D _ 1)))

/-- The identification `localizedModuleTorEquiv` of Stacks 08HX is the localization at `s` of the
canonical change-of-rings map `Tor_i^R(A, B) → Tor_i^{R_r}(A_p, B_q)`. -/
theorem localizedModuleTorEquiv_mk_one
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (s : PrimeSpectrum (A ⊗[R] B))
    (r : PrimeSpectrum R) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    [p.asIdeal.LiesOver r.asIdeal] [q.asIdeal.LiesOver r.asIdeal]
    [Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal)]
    [Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime q.asIdeal)]
    [Localization.AtPrime.IsLiesOverAlgebra r.asIdeal p.asIdeal]
    [Localization.AtPrime.IsLiesOverAlgebra r.asIdeal q.asIdeal]
    (hp : p.asIdeal = s.asIdeal.comap (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B))
    (hq : q.asIdeal = s.asIdeal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B))
    (i : ℕ) (x : TorChangeOfRings.torObj R i A B) :
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B i
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty
      (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) i
    letI : Module (A ⊗[R] B) (TorChangeOfRings.torObj (Localization.AtPrime r.asIdeal) i
        (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) :=
      Module.compHom _ (TorChangeOfRings.tensorProductMap R (Localization.AtPrime r.asIdeal) A B
        (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
        (IsScalarTower.toAlgHom R A _) (IsScalarTower.toAlgHom R B _))
    localizedModuleTorEquiv R A B s r p q hp hq i (LocalizedModule.mk x 1) =
      LocalizedModule.mk (TorChangeOfRings.changeMap TorChangeOfRings.canonicalSystem_nonempty
        R (Localization.AtPrime r.asIdeal) A B (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) i (IsScalarTower.toAlgHom R A _)
        (IsScalarTower.toAlgHom R B _) x) 1 :=
  by
  simp only [localizedModuleTorEquiv, IsLocalizedModule.iso_mk_one]
  let := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty
    (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime q.asIdeal) i
  let : Module (A ⊗[R] B) (TorChangeOfRings.torObj (Localization.AtPrime r.asIdeal) i
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) :=
    Module.compHom _ (TorChangeOfRings.tensorProductMap R (Localization.AtPrime r.asIdeal) A B
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
      (IsScalarTower.toAlgHom R A _) (IsScalarTower.toAlgHom R B _))
  exact congrArg (fun y ↦ LocalizedModule.mk y 1) <|
    (TorChangeOfRings.canonicalLaws TorChangeOfRings.canonicalSystem_nonempty).extension_one_tmul
    R (Localization.AtPrime r.asIdeal) A B (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime q.asIdeal) i (IsScalarTower.toAlgHom R A _)
    (IsScalarTower.toAlgHom R B _) x

end RingTheory.TorIndependence

end
