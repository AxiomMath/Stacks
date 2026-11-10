module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus
public import StacksFrontier.RingTheory.Flat.TowerLTensor

/-!
# Flatness along the inverse image of a closed subset of the base

Let `R → S` be a map of commutative rings, let `I` be an ideal of `R` and let `M` be an
`S`-module. We say that `M` is flat over `R` along the inverse image of the zero locus of `I`
when every localization of `M` at a prime of `S` containing the extension of `I` is flat over
`R`. This condition is stable under arbitrary base change and descends along a base change which
is surjective onto the closed subset and has flat local rings there.

## Main definitions

* `Module.FlatAlongZeroLocus`: the defining condition.

## Main results

* `Module.FlatAlongZeroLocus.baseChange`: stability under base change.
* `Module.FlatAlongZeroLocus.of_baseChange`: descent along a flat cover of the closed subset.
* `Module.Flat.localizedModule_atPrime_of_away`: flatness on a principal open gives flatness at
  each of its primes.

## References

* [The Stacks Project, Tag 052W](https://stacks.math.columbia.edu/tag/052W)
* [The Stacks Project, Tag 052X](https://stacks.math.columbia.edu/tag/052X)
* [The Stacks Project, Tag 05LL](https://stacks.math.columbia.edu/tag/05LL)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x uS uM uL uT uA uB uLam

/-- An `S`-module `M` is flat over `R` along the inverse image of the zero
locus of an ideal `I` of `R` if the localization `M_q` is flat over `R` for every prime ideal `q`
of `S` containing the extension of `I`. -/
@[stacks 052W]
def Module.FlatAlongZeroLocus
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] : Prop :=
  ∀ (q : Ideal S) [q.IsPrime], I.map (algebraMap R S) ≤ q →
    Module.Flat R (LocalizedModule.AtPrime q M)

/-- Let `T` be a pushout of maps of commutative rings `R → S` and `R → R'`.
If an `S`-module `M` is flat over `R` along the inverse image of the zero locus of `I`, and the
extension of `I` to `R'` is contained in `I'`, then `T ⊗[S] M` is flat over `R'` along the
inverse image of the zero locus of `I'`. -/
@[stacks 052X]
lemma Module.FlatAlongZeroLocus.baseChange
    (R : Type u) (S : Type v) (R' : Type w) (T : Type x)
    [CommRing R] [CommRing S] [CommRing R'] [CommRing T]
    [Algebra R S] [Algebra R R'] [Algebra R T] [Algebra S T] [Algebra R' T]
    [IsScalarTower R S T] [IsScalarTower R R' T] [Algebra.IsPushout R R' S T]
    (I : Ideal R) (I' : Ideal R')
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hI : I.map (algebraMap R R') ≤ I')
    (hM : Module.FlatAlongZeroLocus R S I M) :
    Module.FlatAlongZeroLocus R' T I' (TensorProduct S T M) := by
  intro q' hq' hIq'
  let q : Ideal S := q'.comap (algebraMap S T)
  let D := Localization.AtPrime q'
  let Mq := LocalizedModule.AtPrime q M
  have : q.IsPrime := Ideal.comap_isPrime _ q'
  have hIq : I.map (algebraMap R S) ≤ q := by
    intro x hx
    rw [Ideal.mem_comap]
    apply hIq'
    have hxT : algebraMap S T x ∈ I.map (algebraMap R T) := by
      simpa [← Ideal.map_map, IsScalarTower.algebraMap_eq R S T] using
        Ideal.mem_map_of_mem (algebraMap S T) hx
    have hmap : I.map (algebraMap R T) ≤ I'.map (algebraMap R' T) := by
      calc
        I.map (algebraMap R T) =
            (I.map (algebraMap R R')).map (algebraMap R' T) := by
          rw [Ideal.map_map, IsScalarTower.algebraMap_eq R R' T]
        _ ≤ I'.map (algebraMap R' T) := Ideal.map_mono hI
    exact hmap hxT
  have : Module.Flat R Mq := hM q hIq
  have : Module.Flat R' (T ⊗[S] Mq) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange R R' S T Mq)
  have : Module.Flat T D := IsLocalization.flat D q'.primeCompl
  have hflat : Module.Flat R' (D ⊗[T] (T ⊗[S] Mq)) :=
    Module.Flat.tensorProduct_of_flat_left (A := R') (C := T) (D := D) (P := T ⊗[S] Mq)
  let eLoc : LocalizedModule.AtPrime q' (T ⊗[S] M) ≃ₗ[D] D ⊗[T] (T ⊗[S] M) :=
    LocalizedModule.equivTensorProduct q'.primeCompl (T ⊗[S] M)
  let eCancelM : D ⊗[T] (T ⊗[S] M) ≃ₗ[D] D ⊗[S] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S T D D M
  let eCancelMq : D ⊗[T] (T ⊗[S] Mq) ≃ₗ[D] D ⊗[S] Mq :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S T D D Mq
  let Sq := Localization.AtPrime q
  let : q'.LiesOver q := ⟨rfl⟩
  let : Algebra Sq D := Localization.AtPrime.algebraOfLiesOver q q'
  let eMq : Mq ≃ₗ[Sq] Sq ⊗[S] M :=
    LocalizedModule.equivTensorProduct q.primeCompl M
  let eRestrict : D ⊗[Sq] Mq ≃ₗ[Sq] D ⊗[S] Mq :=
    IsLocalization.moduleTensorEquiv q.primeCompl Sq D Mq
  let eBase : D ⊗[Sq] (Sq ⊗[S] M) ≃ₗ[D] D ⊗[S] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S Sq D D M
  let f : D ⊗[S] M →ₗ[D] D ⊗[S] Mq :=
    (TensorProduct.AlgebraTensorModule.lTensor D D)
      (LocalizedModule.mkLinearMap q.primeCompl M)
  have hf : Function.Bijective f := by
    let e : D ⊗[S] M ≃ D ⊗[S] Mq :=
      eBase.symm.toEquiv.trans
        ((TensorProduct.congr (LinearEquiv.refl Sq D) eMq.symm).toEquiv.trans eRestrict.toEquiv)
    have he : (f : D ⊗[S] M → D ⊗[S] Mq) = e := by
      funext z
      induction z using TensorProduct.inductionOn with
      | tmul d m =>
          simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearEquiv.toEquiv_symm,
            IsLocalization.moduleTensorEquiv, TensorProduct.equivOfCompatibleSMul,
            Equiv.trans_apply, LinearEquiv.coe_symm_toEquiv,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
            LinearEquiv.coe_toEquiv, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
            LinearEquiv.coe_mk, TensorProduct.mapOfCompatibleSMul_tmul, f, e, eBase, eMq,
            eRestrict]
          rw [LocalizedModule.equivTensorProduct_symm_apply_tmul_one]
          rfl
      | add z y hz hy => simp [e, hz, hy]
    rw [he]
    exact e.bijective
  let eMiddle : D ⊗[S] M ≃ₗ[D] D ⊗[S] Mq := LinearEquiv.ofBijective f hf
  exact Module.Flat.of_linearEquiv
    ((eLoc.restrictScalars R').trans
      ((eCancelM.restrictScalars R').trans
        ((eMiddle.restrictScalars R').trans (eCancelMq.symm.restrictScalars R'))))

/-! ### Descent of flatness along a closed subset -/

/-- The residue fields of two primes with the same contraction have a nonzero tensor product
over the base. -/
private theorem nontrivial_residueField_tensorProduct
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (q : Ideal S) [q.IsPrime] (p' : Ideal T) [p'.IsPrime]
    (h : q.comap (algebraMap R S) = p'.comap (algebraMap R T)) :
    Nontrivial (q.ResidueField ⊗[R] p'.ResidueField) := by
  let p := q.comap (algebraMap R S)
  let : p.IsPrime := Ideal.comap_isPrime _ _
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R S) rfl).toAlgebra
  let : Algebra p.ResidueField p'.ResidueField :=
    (Ideal.ResidueField.map p p' (algebraMap R T) h).toAlgebra
  have : IsScalarTower R p.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (Ideal.ResidueField.map_algebraMap p q (algebraMap R S) rfl r).symm
  have : IsScalarTower R p.ResidueField p'.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (Ideal.ResidueField.map_algebraMap p p' (algebraMap R T) h r).symm
  let f : q.ResidueField ⊗[R] p'.ResidueField →+*
      q.ResidueField ⊗[p.ResidueField] p'.ResidueField :=
    (Algebra.TensorProduct.mapOfCompatibleSMul p.ResidueField R R
      q.ResidueField p'.ResidueField).toRingHom
  exact f.domain_nontrivial

/-- If `f ∘ i` factors through the residue field of `q` via a map `j` into a ring `C`, then the
contraction along `f ∘ i` of a prime of `C` is `q`, provided its contraction along `j` is `⊥`. -/
private theorem comap_comap_eq_of_comp_eq
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (q : Ideal A) [q.IsPrime] (P : Ideal C) [P.IsPrime] (f : B →+* C) (i : A →+* B)
    (j : q.ResidueField →+* C) (h : f.comp i = j.comp (algebraMap A q.ResidueField)) :
    (P.comap f).comap i = q := by
  rw [Ideal.comap_comap, h, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (P.comap j),
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

/-- Two primes with the same contraction to the base are the contractions of a single prime of
the tensor product. -/
private theorem exists_prime_tensorProduct_comap_eq
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (q : Ideal S) [q.IsPrime] (p' : Ideal T) [p'.IsPrime]
    (h : q.comap (algebraMap R S) = p'.comap (algebraMap R T)) :
    ∃ Q : Ideal (S ⊗[R] T), Q.IsPrime ∧
      Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := T)) = q ∧
      Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).toRingHom = p' := by
  let := nontrivial_residueField_tensorProduct q p' h
  let : IsScalarTower R S q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R T p'.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : S ⊗[R] T →ₐ[R] q.ResidueField ⊗[R] p'.ResidueField :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S q.ResidueField)
      (IsScalarTower.toAlgHom R T p'.ResidueField)
  let P : Ideal (q.ResidueField ⊗[R] p'.ResidueField) :=
    (Classical.choice (inferInstance : Nonempty (PrimeSpectrum
      (q.ResidueField ⊗[R] p'.ResidueField)))).asIdeal
  let : P.IsPrime := (Classical.choice (inferInstance : Nonempty (PrimeSpectrum
      (q.ResidueField ⊗[R] p'.ResidueField)))).isPrime
  let Q := P.comap f.toRingHom
  have hq : Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := T)) = q :=
    comap_comap_eq_of_comp_eq q P f.toRingHom _
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := q.ResidueField)
        (B := p'.ResidueField)) (by ext s; simp [f])
  have hp' :
      Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).toRingHom = p' :=
    comap_comap_eq_of_comp_eq p' P f.toRingHom _
      (Algebra.TensorProduct.includeRight (R := R) (A := q.ResidueField)
        (B := p'.ResidueField)).toRingHom (by ext s; simp [f])
  exact ⟨Q, inferInstance, hq, hp'⟩

/-- Comparing two base changes of one module: if `f` exhibits `M'` as the base change of `M` to
`A` and `g` exhibits `N` as the base change of `M` to `B`, then `B ⊗[A] M'` is `N`. -/
private noncomputable def baseChangeEquivOfBaseChange
    {S A B M M' N : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra A B] [Algebra S B] [IsScalarTower S A B]
    [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] [Module A M'] [IsScalarTower S A M']
    [AddCommGroup N] [Module S N] [Module B N] [IsScalarTower S B N]
    (f : M →ₗ[S] M') (hf : IsBaseChange A f)
    (g : M →ₗ[S] N) (hg : IsBaseChange B g) :
    B ⊗[A] M' ≃ₗ[B] N :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) hf.equiv.symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange S A B B M ≪≫ₗ hg.equiv

/-- A prime of `S ⊗[R] A` lying over a prime `p` of `A` whose local ring is flat over `R` has
local ring flat over `S`. -/
private theorem flat_localization_atPrime_tensorProduct
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    (p : Ideal A) [p.IsPrime]
    (Q : Ideal (S ⊗[R] A)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom = p)
    [Module.Flat R (Localization.AtPrime p)] :
    Module.Flat S (Localization.AtPrime Q) := by
  let T := S ⊗[R] A
  let Ap := Localization.AtPrime p
  let U := S ⊗[R] Ap
  let B := Localization.AtPrime Q
  let : Algebra A Ap := inferInstance
  let : Algebra R Ap := inferInstance
  let : IsScalarTower R A Ap := inferInstance
  let : Algebra T U :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R A Ap)).toAlgebra
  let : IsScalarTower S T U := IsScalarTower.of_algebraMap_eq' (by
    ext s
    change (s ⊗ₜ[R] (1 : Ap)) =
      (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R A Ap))
        (s ⊗ₜ[R] (1 : A))
    simp)
  have hloc : IsLocalization (p.primeCompl.map
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A))) U := by
    apply IsLocalization.tensorProduct_tensorProduct_right R S p.primeCompl Ap
    ext
    simp [RingHom.algebraMap_toAlgebra]
  let : Algebra T B := inferInstance
  have hle : (p.primeCompl.map
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A))) ≤ Q.primeCompl := by
    rintro x ⟨a, ha, rfl⟩
    change (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)) a ∉ Q
    intro hx
    exact ha (hQ ▸ hx)
  let : Algebra U B :=
    (IsLocalization.lift (M := p.primeCompl.map
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)))
      (S := U) (g := algebraMap T B)
      (fun a => IsLocalization.map_units (M := Q.primeCompl)
        (S := B) ⟨a, hle a.2⟩)).toAlgebra
  let : IsScalarTower T U B := IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsScalarTower S T B := IsScalarTower.of_algebraMap_eq' (by ext s; rfl)
  have : IsScalarTower S U B := IsScalarTower.to₁₃₄ S T U B
  have : IsLocalization (Q.primeCompl.map (algebraMap T U)) B :=
    IsLocalization.isLocalization_of_submonoid_le U B _ _ hle
  have : Module.Flat S U := Module.Flat.baseChange R S Ap
  have : Module.Flat U B := IsLocalization.flat B (Q.primeCompl.map (algebraMap T U))
  exact Module.Flat.trans S U B

/-- Let `Q` be a prime of `S ⊗[R] A` lying over primes `q` of `S` and `p` of `A`, where `A_p` is
flat over `R`. Then the map of local rings `S_q → (S ⊗[R] A)_Q` is faithfully flat. -/
private theorem faithfullyFlat_localization_atPrime_tensorProduct
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    (q : Ideal S) [q.IsPrime]
    (p : Ideal A) [p.IsPrime]
    (Q : Ideal (S ⊗[R] A)) [Q.IsPrime]
    (hq : Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := A)) = q)
    (hp : Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom = p)
    [Module.Flat R (Localization.AtPrime p)] :
    letI : Algebra (Localization.AtPrime q) (Localization.AtPrime Q) :=
      (Localization.localRingHom q Q
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := A)) hq.symm).toAlgebra
    Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime Q) := by
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime Q) :=
    (Localization.localRingHom q Q
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := A)) hq.symm).toAlgebra
  have : IsScalarTower S (Localization.AtPrime q) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext s
      change (algebraMap S (Localization.AtPrime Q)) s =
        Localization.localRingHom q Q
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := A)) hq.symm
          ((algebraMap S (Localization.AtPrime q)) s)
      rw [Localization.localRingHom_to_map]
      rfl)
  have hS : Module.Flat S (Localization.AtPrime Q) :=
    flat_localization_atPrime_tensorProduct p Q hp
  have : Module.Flat (Localization.AtPrime q) (Localization.AtPrime Q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime q) q.primeCompl
      (Localization.AtPrime Q)).mpr hS
  have : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime Q)) :=
    Localization.isLocalHom_localRingHom q Q _ hq.symm
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The localization at a prime of `S ⊗[R] A` of the base change of an `S`-module `M` is the
base change of `M` along `S → (S ⊗[R] A)_Q`. -/
private theorem exists_isBaseChange_localizedModule_tensorProduct
    {R S A M : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (Q : Ideal (S ⊗[R] A)) [Q.IsPrime] :
    letI : Algebra S (S ⊗[R] A) := inferInstance
    letI : Algebra S (Localization.AtPrime Q) := inferInstance
    letI : Module S (LocalizedModule.AtPrime Q ((S ⊗[R] A) ⊗[S] M)) := inferInstance
    ∃ f : M →ₗ[S] LocalizedModule.AtPrime Q ((S ⊗[R] A) ⊗[S] M),
      IsBaseChange (Localization.AtPrime Q) f := by
  let T := S ⊗[R] A
  let B := Localization.AtPrime Q
  let N := T ⊗[S] M
  let NQ := LocalizedModule.AtPrime Q N
  let : Algebra S T := inferInstance
  let : Algebra T B := inferInstance
  have : IsScalarTower S T B := IsScalarTower.of_algebraMap_eq' (by ext s; rfl)
  let : Module S NQ := inferInstance
  have : IsScalarTower S T NQ := inferInstance
  have : IsScalarTower S B NQ := inferInstance
  let f0 : M →ₗ[S] N := TensorProduct.mk S T M 1
  let f1 : N →ₗ[T] NQ := LocalizedModule.mkLinearMap Q.primeCompl N
  let f : M →ₗ[S] NQ := (f1.restrictScalars S).comp f0
  have h0 : IsBaseChange T f0 := TensorProduct.isBaseChange S M T
  have h1 : IsBaseChange B f1 := IsLocalizedModule.isBaseChange Q.primeCompl B f1
  exact ⟨f, h0.comp h1⟩

/-- Flatness along the inverse image of a closed subset descends after a
base change which is surjective onto that closed subset and whose local rings there are flat
over the original base. -/
@[stacks 05LL]
theorem Module.FlatAlongZeroLocus.of_baseChange
    (R : Type u) (S : Type v) (R' : Type w) (M : Type x)
    [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R) (I' : Ideal R')
    (_hmap : I.map (algebraMap R R') ≤ I')
    (hsurj : ∀ (p : Ideal R), p.IsPrime → I ≤ p →
      ∃ (p' : Ideal R'), p'.IsPrime ∧ I' ≤ p' ∧
        p'.comap (algebraMap R R') = p)
    (hflat : ∀ (p' : Ideal R') [p'.IsPrime], I' ≤ p' →
      Module.Flat R (Localization.AtPrime p')) :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := R')
    Module.FlatAlongZeroLocus R' (S ⊗[R] R') I'
      ((S ⊗[R] R') ⊗[S] M) →
      Module.FlatAlongZeroLocus R S I M := by
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := R')
  intro hbase q hqPrime hIq
  let : q.IsPrime := hqPrime
  let p := q.comap (algebraMap R S)
  let : p.IsPrime := Ideal.comap_isPrime _ _
  have hIp : I ≤ p := (Ideal.map_le_iff_le_comap).mp hIq
  obtain ⟨p', hp'prime, hp'I, hp'p⟩ := hsurj p inferInstance hIp
  let : p'.IsPrime := hp'prime
  obtain ⟨Q, hQprime, hQq, hQp'⟩ := exists_prime_tensorProduct_comap_eq q p' hp'p.symm
  let : Q.IsPrime := hQprime
  let T := S ⊗[R] R'
  let B := Localization.AtPrime Q
  let Sq := Localization.AtPrime q
  let Ap := Localization.AtPrime p'
  let N := T ⊗[S] M
  let NQ := LocalizedModule.AtPrime Q N
  have hIQ : I'.map (algebraMap R' T) ≤ Q :=
    (Ideal.map_le_iff_le_comap).mpr (hQp' ▸ hp'I)
  have hNQ : Module.Flat R' NQ := hbase Q hIQ
  let : Algebra Ap B :=
    (Localization.localRingHom p' Q
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := R')).toRingHom
      hQp'.symm).toAlgebra
  let : Algebra R' B := inferInstance
  have : IsScalarTower R' T B := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  have : IsScalarTower R' Ap B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change (algebraMap R' B) a =
      Localization.localRingHom p' Q
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := R')).toRingHom
        hQp'.symm ((algebraMap R' Ap) a)
    rw [Localization.localRingHom_to_map]
    rfl)
  have : IsScalarTower R Ap B := IsScalarTower.to₁₃₄ R R' Ap B
  have : IsScalarTower T B NQ := inferInstance
  have : IsScalarTower R' B NQ := IsScalarTower.to₁₃₄ R' T B NQ
  let : Module Ap NQ := Module.compHom NQ (algebraMap Ap B)
  have : IsScalarTower R' Ap NQ := IsScalarTower.of_algebraMap_smul fun a z => by
    change (algebraMap Ap B (algebraMap R' Ap a)) • z = a • z
    rw [← IsScalarTower.algebraMap_apply]
    exact IsScalarTower.algebraMap_smul (A := B) a z
  have : IsScalarTower R Ap NQ := IsScalarTower.to₁₃₄ R R' Ap NQ
  have hApNQ : Module.Flat Ap NQ :=
    (Module.flat_iff_of_isLocalization Ap p'.primeCompl NQ).mpr hNQ
  have : Module.Flat R Ap := hflat p' hp'I
  have hRNQ : Module.Flat R NQ := Module.Flat.trans R Ap NQ
  let : Algebra Sq B :=
    (Localization.localRingHom q Q
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := R'))
      hQq.symm).toAlgebra
  have : IsScalarTower S Sq B := IsScalarTower.of_algebraMap_eq' (by
    ext s
    change (algebraMap S B) s =
      Localization.localRingHom q Q
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := R'))
        hQq.symm ((algebraMap S Sq) s)
    rw [Localization.localRingHom_to_map]
    rfl)
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  have : IsScalarTower R Sq B := IsScalarTower.to₁₃₄ R S Sq B
  have : Module.FaithfullyFlat Sq B :=
    faithfullyFlat_localization_atPrime_tensorProduct q p' Q hQq hQp'
  obtain ⟨g, hg⟩ := exists_isBaseChange_localizedModule_tensorProduct
    (R := R) (S := S) (A := R') (M := M) Q
  let f : M →ₗ[S] LocalizedModule.AtPrime q M :=
    LocalizedModule.mkLinearMap q.primeCompl M
  have hf : IsBaseChange Sq f :=
    IsLocalizedModule.isBaseChange q.primeCompl Sq f
  let e : B ⊗[Sq] LocalizedModule.AtPrime q M ≃ₗ[B] NQ :=
    baseChangeEquivOfBaseChange (S := S) (A := Sq) (B := B)
      (M := M) (M' := LocalizedModule.AtPrime q M) (N := NQ) f hf g hg
  have : Module.Flat R (B ⊗[Sq] LocalizedModule.AtPrime q M) :=
    Module.Flat.of_linearEquiv (e.restrictScalars R)
  exact Module.Flat.of_tensorProduct_of_faithfullyFlat
    (A := R) (C := Sq) (D := B) (P := LocalizedModule.AtPrime q M)

/-! ### Flatness on a principal open versus at a prime -/

/-- Flatness of a principal localization implies flatness at every prime of the principal open
it defines. -/
theorem Module.Flat.localizedModule_atPrime_of_away
    {R : Type*} {S : Type*} {M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (q : Ideal S) [q.IsPrime] (g : S)
    (hg : g ∉ q) [Module.Flat R (LocalizedModule.Away g M)] :
    Module.Flat R (LocalizedModule.AtPrime q M) := by
  have hle : Submonoid.powers g ≤ q.primeCompl := Submonoid.powers_le.mpr hg
  exact Module.Flat.of_isLocalizedModule_of_tower q.primeCompl
    (IsLocalizedModule.liftOfLE (Submonoid.powers g) q.primeCompl hle
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
      (LocalizedModule.mkLinearMap q.primeCompl M))
