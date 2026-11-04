module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient

/-!
# Completions of local rings after completion of the base

Let `X` be a scheme over a local ring `A` and let `Y = X ×_{Spec A} Spec A^` be its base change
to the completion of `A`. At a point of `Y` lying over the closed point of `Spec A`, the local
rings of `X` and of `Y` have isomorphic completions, compatibly with the map on stalks.

## Main results

* `AlgebraicGeometry.stalkMap_adicCompletion_isomorphism` — the isomorphism of completed local
  rings and its compatibility with the map on stalks.

## Implementation notes

The completed base change is the categorical pullback of schemes. That the map on local rings
induces the displayed isomorphism is recorded by asking the isomorphism to commute with the
canonical maps into the two adic completions.

The proof is assembled from four bridges, each a separate lemma below: a compatible system of
isomorphisms of the finite quotients induces one of the inverse-limit completions; reducing a
localization by an ideal is localizing the corresponding quotient; adjoining the completed base
does not change a quotient killed by a power of the base maximal ideal; and a local ring
isomorphism induces one of the completions.

## References

* [Stacks Project, Tag 0BG5](https://stacks.math.columbia.edu/tag/0BG5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TensorProduct

universe u

/-- Any two quotients by the unit ideal are isomorphic, both being trivial. -/
private noncomputable def quotientTopRingEquiv
    {R S : Type u} [CommRing R] [CommRing S] :
    (R ⧸ (⊤ : Ideal R)) ≃+* (S ⧸ (⊤ : Ideal S)) := by
  letI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.2 rfl
  letI : Subsingleton (S ⧸ (⊤ : Ideal S)) := Ideal.Quotient.subsingleton_iff.2 rfl
  let f : (R ⧸ (⊤ : Ideal R)) →+* (S ⧸ (⊤ : Ideal S)) := {
    toFun := fun _ ↦ 0
    map_one' := Subsingleton.elim _ _
    map_mul' := fun _ _ ↦ Subsingleton.elim _ _
    map_zero' := rfl
    map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
  exact RingEquiv.ofBijective f ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
    fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-! The first bridge is purely algebraic: a compatible system of isomorphisms on all finite
quotients induces an isomorphism of the inverse-limit completions. -/

/-- A compatible system of isomorphisms of the finite quotients induces an isomorphism of the
inverse-limit completions. -/
private noncomputable def adicCompletionRingEquivOfQuotientEquivs
    {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S)
    (e : ∀ n : ℕ,
      (R ⧸ (I ^ n • (⊤ : Submodule R R))) ≃+*
        (S ⧸ (J ^ n • (⊤ : Submodule S S))))
    (he : ∀ {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ (I ^ n • (⊤ : Submodule R R))),
      AdicCompletion.transitionMap J S hmn (e n x) =
        e m (AdicCompletion.transitionMap I R hmn x)) :
    AdicCompletion I R ≃+* AdicCompletion J S := by
  let f : AdicCompletion I R →+* AdicCompletion J S := {
    toFun x := ⟨fun n ↦ e n (x.val n), fun {m n} hmn ↦ by
      exact (he hmn (x.val n)).trans (congrArg (e m) (x.property hmn))⟩
    map_one' := by ext n; exact map_one (e n)
    map_mul' x y := by ext n; exact map_mul (e n) (x.val n) (y.val n)
    map_zero' := by ext n; exact map_zero (e n)
    map_add' x y := by ext n; exact map_add (e n) (x.val n) (y.val n) }
  let g : AdicCompletion J S →+* AdicCompletion I R := {
    toFun x := ⟨fun n ↦ (e n).symm (x.val n), fun {m n} hmn ↦ by
      apply (e m).injective
      rw [RingEquiv.apply_symm_apply]
      calc
        _ = AdicCompletion.transitionMap J S hmn
            (e n ((e n).symm (x.val n))) := (he hmn ((e n).symm (x.val n))).symm
        _ = AdicCompletion.transitionMap J S hmn (x.val n) := by simp
        _ = x.val m := x.property hmn⟩
    map_one' := by ext n; exact map_one (e n).symm
    map_mul' x y := by ext n; exact map_mul (e n).symm (x.val n) (y.val n)
    map_zero' := by ext n; exact map_zero (e n).symm
    map_add' x y := by ext n; exact map_add (e n).symm (x.val n) (y.val n) }
  have hgf (x : AdicCompletion I R) : g (f x) = x :=
    AdicCompletion.ext fun n ↦ RingEquiv.symm_apply_apply (e n) (x.val n)
  have hfg (x : AdicCompletion J S) : f (g x) = x :=
    AdicCompletion.ext fun n ↦ RingEquiv.apply_symm_apply (e n) (x.val n)
  exact RingEquiv.ofBijective f ⟨fun x y hxy ↦ by simpa only [hgf] using congrArg g hxy,
    fun y ↦ ⟨g y, hfg y⟩⟩

/-- An isomorphism of quotients carrying one prime to another induces an isomorphism of the
reduced localizations at those primes. -/
private noncomputable def localizationQuotientEquivOfQuotientEquiv
    {R S Rp Sq : Type u} [CommRing R] [CommRing S] [CommRing Rp] [CommRing Sq]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [Algebra R Rp] [IsLocalization.AtPrime Rp p]
    [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    (I : Ideal R) (J : Ideal S) (hIp : I ≤ p) (hJq : J ≤ q)
    (e : (R ⧸ I) ≃+* (S ⧸ J))
    (he : (p.map (Ideal.Quotient.mk I)).map e.toRingHom =
      q.map (Ideal.Quotient.mk J)) :
    letI : Algebra (R ⧸ I) (Sq ⧸ J.map (algebraMap S Sq)) :=
      ((algebraMap (S ⧸ J) (Sq ⧸ J.map (algebraMap S Sq))).comp
        e.toRingHom).toAlgebra
    (Rp ⧸ I.map (algebraMap R Rp)) ≃ₐ[R ⧸ I]
      (Sq ⧸ J.map (algebraMap S Sq)) := by
  let p₀ : Ideal (R ⧸ I) := p.map (Ideal.Quotient.mk I)
  let q₀ : Ideal (S ⧸ J) := q.map (Ideal.Quotient.mk J)
  have hp₀ : p₀.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIp
  have hq₀ : q₀.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hJq
  have hpLoc : IsLocalization.AtPrime
      (Rp ⧸ I.map (algebraMap R Rp)) p₀ :=
    isLocalization_atPrime_quotient p Rp I p₀ (Ideal.comap_map_mk hIp)
  have hqLoc : IsLocalization.AtPrime
      (Sq ⧸ J.map (algebraMap S Sq)) q₀ :=
    isLocalization_atPrime_quotient q Sq J q₀ (Ideal.comap_map_mk hJq)
  have he' : Ideal.map e.toRingHom p₀ = q₀ := by
    simpa [p₀, q₀] using he
  have he_mem (x : R ⧸ I) : e x ∈ q₀ ↔ x ∈ p₀ := by
    rw [← he', Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
    simp
  have hsub : Submonoid.map e.toMonoidHom p₀.primeCompl = q₀.primeCompl := by
    apply Submonoid.ext
    intro x
    change (∃ y, y ∈ p₀.primeCompl ∧ e y = x) ↔ x ∈ q₀.primeCompl
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Ideal.mem_primeCompl_iff] at hy ⊢
      intro hmem
      exact hy ((he_mem y).mp hmem)
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [Ideal.mem_primeCompl_iff] at hx ⊢
      intro hmem
      apply hx
      simpa using (he_mem (e.symm x)).2 hmem
  letI : Algebra (R ⧸ I) (Sq ⧸ J.map (algebraMap S Sq)) :=
    ((algebraMap (S ⧸ J) (Sq ⧸ J.map (algebraMap S Sq))).comp
      e.toRingHom).toAlgebra
  have hlocOverR : IsLocalization p₀.primeCompl
      (Sq ⧸ J.map (algebraMap S Sq)) := by
    have hsubInv : Submonoid.map e.symm.toMonoidHom q₀.primeCompl = p₀.primeCompl := by
      calc
        _ = Submonoid.map e.symm.toMonoidHom
            (Submonoid.map e.toMonoidHom p₀.primeCompl) := congrArg _ hsub.symm
        _ = p₀.primeCompl := by
          ext x
          simp only [Submonoid.mem_map]
          simp
    let : IsLocalization.AtPrime (Sq ⧸ J.map (algebraMap S Sq)) q₀ := hqLoc
    have hqLoc'base : IsLocalization q₀.primeCompl
        (Sq ⧸ J.map (algebraMap S Sq)) := inferInstance
    have hqLoc' : IsLocalization (Submonoid.map e.symm.toMonoidHom q₀.primeCompl)
        (Sq ⧸ J.map (algebraMap S Sq)) :=
      (IsLocalization.isLocalization_iff_of_base_ringEquiv
        (M := q₀.primeCompl) (S := Sq ⧸ J.map (algebraMap S Sq)) e.symm).1 hqLoc'base
    rwa [hsubInv] at hqLoc'
  letI : IsLocalization p₀.primeCompl (Rp ⧸ I.map (algebraMap R Rp)) := hpLoc
  letI : IsLocalization p₀.primeCompl (Sq ⧸ J.map (algebraMap S Sq)) := hlocOverR
  exact IsLocalization.algEquiv p₀.primeCompl
    (Rp ⧸ I.map (algebraMap R Rp)) (Sq ⧸ J.map (algebraMap S Sq))

/-- `localizationQuotientEquivOfQuotientEquiv` is compatible with the maps from the quotient. -/
private theorem localizationQuotientEquivOfQuotientEquiv_commutes
    {R S Rp Sq : Type u} [CommRing R] [CommRing S] [CommRing Rp] [CommRing Sq]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [Algebra R Rp] [IsLocalization.AtPrime Rp p]
    [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    (I : Ideal R) (J : Ideal S) (hIp : I ≤ p) (hJq : J ≤ q)
    (e : (R ⧸ I) ≃+* (S ⧸ J))
    (he : (p.map (Ideal.Quotient.mk I)).map e.toRingHom =
      q.map (Ideal.Quotient.mk J)) (x : R ⧸ I) :
    letI : Algebra (R ⧸ I) (Sq ⧸ J.map (algebraMap S Sq)) :=
      ((algebraMap (S ⧸ J) (Sq ⧸ J.map (algebraMap S Sq))).comp
        e.toRingHom).toAlgebra
    localizationQuotientEquivOfQuotientEquiv (Rp := Rp) (Sq := Sq) p q I J hIp hJq e he
      (algebraMap (R ⧸ I) (Rp ⧸ I.map (algebraMap R Rp)) x) =
        algebraMap (S ⧸ J) (Sq ⧸ J.map (algebraMap S Sq)) (e x) := by
  let : Algebra (R ⧸ I) (Sq ⧸ J.map (algebraMap S Sq)) :=
    ((algebraMap (S ⧸ J) (Sq ⧸ J.map (algebraMap S Sq))).comp
      e.toRingHom).toAlgebra
  exact (localizationQuotientEquivOfQuotientEquiv (Rp := Rp) (Sq := Sq)
    p q I J hIp hJq e he).commutes x

/-- A quotient killed by the `n`-th power of the base maximal ideal is unchanged by adjoining the
completed base. -/
private noncomputable def tensorCompletionQuotientEquiv
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (hfg : (IsLocalRing.maximalIdeal A).FG) (I : Ideal B) (n : ℕ)
    (hI : ((IsLocalRing.maximalIdeal A) ^ n).map (algebraMap A B) ≤ I) :
    ((B ⧸ I) ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ≃ₐ[B ⧸ I] (B ⧸ I) := by
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let M := B ⧸ I
  have hkill : (m ^ n).map (algebraMap A M) = ⊥ := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' : algebraMap A B x ∈ I :=
        hI (Ideal.mem_map_of_mem (algebraMap A B) hx)
      change Ideal.Quotient.mk I (algebraMap A B x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx'
    · exact bot_le
  let T := M ⊗[A] AdicCompletion m A
  let incl : AdicCompletion m A →+* T :=
    (Algebra.TensorProduct.includeRight : AdicCompletion m A →ₐ[A] T).toRingHom
  have hkill' : (m ^ n).map (algebraMap A (AdicCompletion m A)) ≤ RingHom.ker incl := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hzero : algebraMap A M a = 0 := by
      have : algebraMap A M a ∈ (m ^ n).map (algebraMap A M) :=
        Ideal.mem_map_of_mem (algebraMap A M) ha
      rw [hkill] at this
      simpa using this
    change Algebra.TensorProduct.includeRight (algebraMap A (AdicCompletion m A) a) = 0
    have hscalar :
        Algebra.TensorProduct.includeRight (R := A) (A := M) (B := AdicCompletion m A)
            (algebraMap A (AdicCompletion m A) a) =
          Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := M)
            (B := AdicCompletion m A) (algebraMap A M a) := by
      change (1 : M) ⊗ₜ[A] algebraMap A (AdicCompletion m A) a =
        algebraMap A M a ⊗ₜ[A] (1 : AdicCompletion m A)
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) (A := M)
        (B := AdicCompletion m A) a).symm
    rw [hscalar, hzero, map_zero]
  have hmapbot : ((m.map (algebraMap A (AdicCompletion m A))) ^ n).map incl = ⊥ := by
    rw [← Ideal.map_pow]
    exact (Ideal.map_le_iff_le_comap.mpr hkill').antisymm bot_le
  let eS : (AdicCompletion m A ⧸
      ((m.map (algebraMap A (AdicCompletion m A))) ^ n)) ≃ₐ[A] (A ⧸ (m ^ n)) := by
    let ev := AdicCompletion.evalₐ m n
    have hker : RingHom.ker ev.toRingHom =
        (m.map (algebraMap A (AdicCompletion m A))) ^ n := by
      ext x
      change ev x = 0 ↔ x ∈ (m.map (algebraMap A (AdicCompletion m A))) ^ n
      have heval : ev x = 0 ↔ AdicCompletion.eval m A n x = 0 := by
        have h : (m ^ n • (⊤ : Submodule A A)) = m ^ n := by
          ext y
          simp
        let e := Ideal.quotientEquivAlgOfEq A h
        change e (AdicCompletion.eval m A n x) = 0 ↔ _
        exact ⟨fun hx ↦ e.injective (by simpa using hx), fun hx ↦ by simp [hx]⟩
      rw [heval, ← LinearMap.mem_ker,
        ← AdicCompletion.pow_smul_top_eq_ker_eval (I := m) (M := A) hfg,
        Ideal.smul_top_eq_map, Ideal.map_pow]
      rfl
    exact (Ideal.quotientEquivAlgOfEq A hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := ev) (AdicCompletion.surjective_evalₐ m n))
  let eT := Algebra.TensorProduct.tensorQuotientEquiv (R := A) (S := M)
    (T := AdicCompletion m A) (A := M)
    ((m.map (algebraMap A (AdicCompletion m A))) ^ n)
  let eb := (Ideal.quotientEquivAlgOfEq M hkill).trans (AlgEquiv.quotientBot M M)
  let eQ : M ⊗[A] (A ⧸ (m ^ n)) ≃ₐ[M] M :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot M (m ^ n)).symm.trans eb
  let f := Algebra.TensorProduct.map (AlgHom.id A M) eS.toAlgHom
  let eMap : M ⊗[A] (AdicCompletion m A ⧸
      ((m.map (algebraMap A (AdicCompletion m A))) ^ n)) ≃+*
      M ⊗[A] (A ⧸ (m ^ n)) :=
    RingEquiv.ofBijective f.toRingHom
      (Algebra.TensorProduct.map_bijective Function.bijective_id eS.bijective)
  let e : T ⧸ ((m.map (algebraMap A (AdicCompletion m A))) ^ n).map incl ≃+* M :=
    eT.toRingEquiv.symm.trans eMap |>.trans eQ.toRingEquiv
  let eqBot : T ⧸ ((m.map (algebraMap A (AdicCompletion m A))) ^ n).map incl ≃+* T :=
    (Ideal.quotientEquivAlgOfEq M hmapbot).trans (AlgEquiv.quotientBot M T)
  let eFinal := eqBot.symm.trans e
  let eAlg : T →ₐ[M] M := {
    toRingHom := eFinal.toRingHom
    commutes' := by
      intro x
      change eFinal (algebraMap M T x) = x
      rw [RingEquiv.trans_apply]
      have hq : eqBot.symm (algebraMap M T x) =
          Ideal.Quotient.mk
            (Ideal.map incl ((Ideal.map (algebraMap A (AdicCompletion m A)) m) ^ n))
            (Algebra.TensorProduct.includeLeft (R := A) (S := M) (A := M)
              (B := AdicCompletion m A) x) := by
        simp only [eqBot]
        change Ideal.Quotient.mk _ (algebraMap M T x) =
          Ideal.Quotient.mk _ (Algebra.TensorProduct.includeLeft (R := A) (S := M)
            (A := M) (B := AdicCompletion m A) x)
        rfl
      rw [hq]
      change eQ (eMap (eT.symm
        (Ideal.Quotient.mk _ (x ⊗ₜ[A] (1 : AdicCompletion m A))))) = x
      rw [Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul]
      have hmap : eMap (x ⊗ₜ[A]
          (Ideal.Quotient.mk _ (1 : AdicCompletion m A))) = x ⊗ₜ[A] (1 : A ⧸ m ^ n) := by
        simp [eMap, f]
      rw [hmap]
      change eQ (algebraMap M (M ⊗[A] (A ⧸ m ^ n)) x) = x
      exact eQ.commutes x }
  exact AlgEquiv.ofBijective eAlg eFinal.bijective

/-- The `IU`-adic completion of `B` is the quotient of `B ⊗[A] A^` by the extension of `I`, for
`I` containing a power of the base maximal ideal. -/
private noncomputable def tensorBaseCompletionQuotientEquiv
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (hfg : (IsLocalRing.maximalIdeal A).FG) (I : Ideal B) (n : ℕ)
    (hI : ((IsLocalRing.maximalIdeal A) ^ n).map (algebraMap A B) ≤ I) :
    (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸
        I.map (algebraMap B (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A)) ≃+*
      B ⧸ I :=
  (Algebra.TensorProduct.quotientTensorEquiv (R := A) (S := A)
      (A := B) (T := AdicCompletion (IsLocalRing.maximalIdeal A) A) I).toRingEquiv.symm.trans
    (tensorCompletionQuotientEquiv hfg I n hI).toRingEquiv

/-- The inverse of `Algebra.TensorProduct.quotientTensorEquiv` takes the class of the image of
`b` to the image of the class of `b`. -/
private theorem quotientTensorEquiv_symm_mk_algebraMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (T : Type u) [CommRing T] [Algebra A T] (I : Ideal B) (b : B) :
    (Algebra.TensorProduct.quotientTensorEquiv
          (R := A) (S := A) (A := B) (T := T) I).toRingEquiv.symm
        (Ideal.Quotient.mk (I.map (algebraMap B (B ⊗[A] T)))
          (algebraMap B (B ⊗[A] T) b)) =
      algebraMap (B ⧸ I) ((B ⧸ I) ⊗[A] T) (Ideal.Quotient.mk I b) := by
  show (Algebra.TensorProduct.quotientTensorEquiv (R := A) (S := A) (A := B) (T := T) I).symm
    (Ideal.Quotient.mk _ (b ⊗ₜ[A] (1 : T))) = _
  rw [Algebra.TensorProduct.quotientTensorEquiv_symm_apply_tmul]
  rfl

/-- `tensorBaseCompletionQuotientEquiv` takes the class of the image of `b` to the class of `b`. -/
private theorem tensorBaseCompletionQuotientEquiv_mk
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (hfg : (IsLocalRing.maximalIdeal A).FG) (I : Ideal B) (n : ℕ)
    (hI : ((IsLocalRing.maximalIdeal A) ^ n).map (algebraMap A B) ≤ I)
    (b : B) :
    tensorBaseCompletionQuotientEquiv hfg I n hI
      (Ideal.Quotient.mk _ (algebraMap B (B ⊗[A]
        AdicCompletion (IsLocalRing.maximalIdeal A) A) b)) = Ideal.Quotient.mk I b := by
  show (tensorCompletionQuotientEquiv hfg I n hI).toRingEquiv
    ((Algebra.TensorProduct.quotientTensorEquiv (R := A) (S := A)
      (A := B) (T := AdicCompletion (IsLocalRing.maximalIdeal A) A) I).toRingEquiv.symm
      (Ideal.Quotient.mk _ (algebraMap B (B ⊗[A]
        AdicCompletion (IsLocalRing.maximalIdeal A) A) b))) = _
  rw [quotientTensorEquiv_symm_mk_algebraMap
    (AdicCompletion (IsLocalRing.maximalIdeal A) A) I b]
  exact (tensorCompletionQuotientEquiv hfg I n hI).commutes (Ideal.Quotient.mk I b)

/-- A ring isomorphism carrying one ideal onto another induces an isomorphism of the quotients. -/
private noncomputable def quotientRingEquivOfRingEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (h : I.map e.toRingHom = J) : (R ⧸ I) ≃+* (S ⧸ J) :=
  Ideal.quotientEquiv I J e h.symm

/-- `quotientRingEquivOfRingEquiv` acts on residue classes through the given isomorphism. -/
private theorem quotientRingEquivOfRingEquiv_mk
    {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (h : I.map e.toRingHom = J) (r : R) :
    quotientRingEquivOfRingEquiv e I J h (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk J (e r) :=
  rfl

/-- A prime contracting to `I` along `f` and whose quotient receives an isomorphism from `R ⧸ I`
compatible with `f` is the extension of `I`. -/
private theorem prime_eq_map_of_quotientEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hJ : J = I.map f) (q : Ideal S) [q.IsPrime]
    (hq : q.comap f = I) (e : (R ⧸ I) ≃+* (S ⧸ J))
    (he : ∀ r, e (Ideal.Quotient.mk I r) = Ideal.Quotient.mk J (f r)) :
    q = J := by
  have hJq : J ≤ q := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    exact hq.ge
  let q₀ := q.map (Ideal.Quotient.mk J)
  have hq₀ : q₀.comap (Ideal.Quotient.mk J) = q := Ideal.comap_map_mk hJq
  have hcomap : q₀.comap e.toRingHom = ⊥ := by
    ext y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    show e (Ideal.Quotient.mk I r) ∈ q₀ ↔ Ideal.Quotient.mk I r ∈ (⊥ : Ideal (R ⧸ I))
    rw [he, ← Ideal.mem_comap, hq₀]
    show r ∈ q.comap f ↔ Ideal.Quotient.mk I r ∈ (⊥ : Ideal (R ⧸ I))
    rw [hq]
    simp [Ideal.Quotient.eq_zero_iff_mem]
  have hq₀bot : q₀ = ⊥ := by
    have h := Ideal.map_comap_of_surjective e.toRingHom e.surjective q₀
    rw [hcomap, Ideal.map_bot] at h
    exact h.symm
  have hqle : q ≤ J := by
    have hqmap : q.map (Ideal.Quotient.mk J) ≤ ⊥ := by
      show q₀ ≤ ⊥
      rw [hq₀bot]
    rw [Ideal.map_le_iff_le_comap] at hqmap
    simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hqmap
  exact le_antisymm hqle hJq

/-- The map of completions induced by a ring map is computed stagewise by the induced map of
quotients. -/
private theorem adicCompletionMap_eval
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A) (I : Ideal B) (hf : J.map f ≤ I)
    (n : ℕ) (a : AdicCompletion J A) :
    AdicCompletion.evalₐ I n (adicCompletionMap f J I hf a) =
      Ideal.quotientMap (I ^ n) f
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono hf n)) (AdicCompletion.evalₐ J n a) := by
  unfold adicCompletionMap
  rw [AdicCompletion.evalₐ_liftRingHom]
  rfl

/-- The induced maps of completions compose. -/
private theorem completionMapOfRingHom_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (I : Ideal A) (J : Ideal B) (K : Ideal C)
    (hf : I.map f ≤ J) (hg : J.map g ≤ K) :
    (adicCompletionMap g J K hg).comp (adicCompletionMap f I J hf) =
      adicCompletionMap (g.comp f) I K
        (by rw [← Ideal.map_map]; exact (Ideal.map_mono hf).trans hg) := by
  apply RingHom.ext
  intro a
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [RingHom.comp_apply, adicCompletionMap_eval]
  obtain ⟨a', ha'⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  rw [← ha']
  rfl

/-- The map of completions induced by the identity is the identity. -/
public theorem completionMapOfRingHom_id
    {A : Type*} [CommRing A] (I : Ideal A) (h : I.map (RingHom.id A) ≤ I) :
    adicCompletionMap (RingHom.id A) I I h = RingHom.id _ := by
  apply RingHom.ext
  intro a
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [RingHom.id_apply, adicCompletionMap_eval]
  obtain ⟨a', ha'⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  rw [← ha']
  rfl

/-- An isomorphism of local rings induces an isomorphism of their completions at the maximal
ideals. -/
private noncomputable def completionRingEquivOfLocalRingEquiv
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal S) S := by
  letI : IsLocalHom e.toRingHom := isLocalHom_of_leftInverse e.symm e.left_inv
  letI : IsLocalHom e.symm.toRingHom := isLocalHom_of_leftInverse e e.right_inv
  exact RingEquiv.ofRingHom
    (adicCompletionMap e.toRingHom _ _ (IsLocalRing.map_maximalIdeal_le e.toRingHom))
    (adicCompletionMap e.symm.toRingHom _ _ (IsLocalRing.map_maximalIdeal_le e.symm.toRingHom))
    (by
      rw [completionMapOfRingHom_comp]
      simpa using completionMapOfRingHom_id (IsLocalRing.maximalIdeal S) _)
    (by
      rw [completionMapOfRingHom_comp]
      simpa using completionMapOfRingHom_id (IsLocalRing.maximalIdeal R) _)

/-- `completionRingEquivOfLocalRingEquiv` is compatible with the canonical maps into the
completions. -/
private theorem completionRingEquivOfLocalRingEquiv_commutes
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (r : R) :
    completionRingEquivOfLocalRingEquiv e
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
      algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (e r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  let : IsLocalHom e.toRingHom := isLocalHom_of_leftInverse e.symm e.left_inv
  show AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n
      (adicCompletionMap e.toRingHom _ _ (IsLocalRing.map_maximalIdeal_le e.toRingHom)
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)) = _
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
    adicCompletionMap_eval, AdicCompletion.evalₐ_of]
  simp

/-- `tensorBaseCompletionQuotientEquiv` takes the class of `b` back to the class of its image. -/
private theorem tensorBaseCompletionQuotientEquiv_symm_mk
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (hfg : (IsLocalRing.maximalIdeal A).FG) (I : Ideal B) (n : ℕ)
    (hI : ((IsLocalRing.maximalIdeal A) ^ n).map (algebraMap A B) ≤ I) (b : B) :
    (tensorBaseCompletionQuotientEquiv hfg I n hI).symm (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk (I.map (algebraMap B (B ⊗[A] AdicCompletion
          (IsLocalRing.maximalIdeal A) A)))
        (algebraMap B (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) b) := by
  rw [← tensorBaseCompletionQuotientEquiv_mk hfg I n hI b, RingEquiv.symm_apply_apply]

/-- Over the localization at a prime `p`, the `n`-th power of the maximal ideal, as a submodule, is
the extension of `p ^ n`. -/
private theorem maximalIdeal_pow_smul_top_eq_map
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ n) •
        (⊤ : Submodule (Localization.AtPrime p) (Localization.AtPrime p)) =
      (p ^ n).map (algebraMap R (Localization.AtPrime p)) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, ← Ideal.map_pow]
  ext z
  simp

/-- The identifications of `T ⧸ K ^ n • ⊤` with `T ⧸ J` are compatible with the transition maps. -/
private theorem quotientEquivAlgOfEq_transitionMap
    {T : Type u} [CommRing T] (K : Ideal T) {m n : ℕ} (hmn : m ≤ n) {Jm Jn : Ideal T}
    (hm : K ^ m • (⊤ : Submodule T T) = Jm) (hn : K ^ n • (⊤ : Submodule T T) = Jn) (h : Jn ≤ Jm)
    (z : T ⧸ (K ^ n • (⊤ : Submodule T T))) :
    Ideal.quotientEquivAlgOfEq T hm (AdicCompletion.transitionMap K T hmn z) =
      Ideal.Quotient.factor h (Ideal.quotientEquivAlgOfEq T hn z) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp [AdicCompletion.transitionMap, Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.factor]

/-- The comparison of `R ⧸ I` with `S ⧸ J` through the base change identification `R ⊗[A] A^ ≃ S`
sends the class of `r` to the class of its image. -/
private theorem quotientRingEquivOfRingEquiv_symm_mk_baseChange
    {A R S : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S]
    (hfg : (IsLocalRing.maximalIdeal A).FG)
    (eBase : (R ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ≃ₐ[R] S)
    (I : Ideal R) (n : ℕ) (hI : ((IsLocalRing.maximalIdeal A) ^ n).map (algebraMap A R) ≤ I)
    (J : Ideal S)
    (hJ : (I.map (algebraMap R (R ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A))).map
      eBase.toRingEquiv.toRingHom = J) (r : R) :
    quotientRingEquivOfRingEquiv eBase.toRingEquiv _ J hJ
      ((tensorBaseCompletionQuotientEquiv hfg I n hI).symm (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk J (algebraMap R S r) := by
  rw [tensorBaseCompletionQuotientEquiv_symm_mk hfg I n hI r, quotientRingEquivOfRingEquiv_mk]
  exact congrArg (Ideal.Quotient.mk J) (eBase.commutes r)

/-- The algebraic core of `AlgebraicGeometry.stalkMap_adicCompletion_isomorphism`. Let `A` be a
local ring with finitely generated maximal ideal `m`, let `R` be an `A`-algebra and let `S` be the
base change of `R` to the `m`-adic completion of `A`. If `q` is a prime of `S` contracting to a
prime `p` of `R` which contains the extension of `m`, then the `m`-adic completions of `R_p` and
`S_q` are isomorphic, compatibly with the induced map of localizations.

The whole argument is a comparison of the two towers of finite quotients: at each level the
quotient of `S` is the quotient of `R` base changed to the completion, which `m ^ n ⊆ p ^ n`
makes into an isomorphism, and localizing commutes with those quotients. -/
@[ega "IV 7.9.3.1" "more general"]
private theorem exists_adicCompletion_ringEquiv_localRingHom
    {A R S : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S]
    (hfg : (IsLocalRing.maximalIdeal A).FG)
    (eBase : (R ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ≃ₐ[R] S)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : q.comap (algebraMap R S) = p)
    (hAinP : ((IsLocalRing.maximalIdeal A).map (algebraMap A R)) ≤ p) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
            (Localization.AtPrime q),
      ∀ r : Localization.AtPrime p,
        e (algebraMap (Localization.AtPrime p)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (Localization.AtPrime p)) r) =
          algebraMap (Localization.AtPrime q)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
              (Localization.AtPrime q))
            (Localization.localRingHom p q (algebraMap R S) hpq.symm r) := by
  have hI (n : ℕ) : (IsLocalRing.maximalIdeal A ^ n).map (algebraMap A R) ≤ p ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hAinP n
  have hAinP1 : (IsLocalRing.maximalIdeal A ^ 1).map (algebraMap A R) ≤ p := by
    simpa using hAinP
  let pT : Ideal (R ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) := p.map (algebraMap R
      (R ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A))
  have hBaseMap : eBase.toRingEquiv.toRingHom.comp
      (algebraMap R (R ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A)) = algebraMap R S := by
    ext r
    exact eBase.commutes r
  have hpT : pT.map eBase.toRingEquiv.toRingHom =
      p.map (algebraMap R S) := by
    show (p.map (algebraMap R
        (R ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A))).map eBase.toRingEquiv.toRingHom = _
    rw [Ideal.map_map, hBaseMap]
  let eTensorToS := quotientRingEquivOfRingEquiv eBase.toRingEquiv pT
    (p.map (algebraMap R S)) hpT
  let eRtoS := (tensorBaseCompletionQuotientEquiv hfg p 1 hAinP1).symm.trans eTensorToS
  have heRtoS (r : R) :
      eRtoS (Ideal.Quotient.mk p r) =
        Ideal.Quotient.mk (p.map (algebraMap R S)) (algebraMap R S r) := by
    exact quotientRingEquivOfRingEquiv_symm_mk_baseChange hfg eBase p 1 hAinP1 _ hpT r
  have hpw : q = p.map (algebraMap R S) :=
    prime_eq_map_of_quotientEquiv (algebraMap R S) p
      (p.map (algebraMap R S)) rfl q hpq eRtoS heRtoS
  let pI : Ideal R := p
  let qI : Ideal S := q
  have hMap (n : ℕ) : ((pI ^ (n + 1)).map (algebraMap R
      (R ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A))).map
      eBase.toRingEquiv.toRingHom = qI ^ (n + 1) := by
    rw [Ideal.map_map, hBaseMap, Ideal.map_pow]
    simp [pI, qI, hpw]
  let eBaseLevel (n : ℕ) : (R ⧸ pI ^ (n + 1)) ≃+* (S ⧸ qI ^ (n + 1)) :=
    (tensorBaseCompletionQuotientEquiv hfg (pI ^ (n + 1)) (n + 1) (hI (n + 1))).symm.trans
      (quotientRingEquivOfRingEquiv eBase.toRingEquiv _ (qI ^ (n + 1)) (hMap n))
  have hBaseLevelMk (n : ℕ) (r : R) :
      eBaseLevel n (Ideal.Quotient.mk (pI ^ (n + 1)) r) =
        Ideal.Quotient.mk (qI ^ (n + 1)) (algebraMap R S r) := by
    exact quotientRingEquivOfRingEquiv_symm_mk_baseChange hfg eBase (pI ^ (n + 1)) (n + 1)
      (hI (n + 1)) _ (hMap n) r
  have hLevelIdeal (n : ℕ) :
      (pI.map (Ideal.Quotient.mk (pI ^ (n + 1)))).map
          (eBaseLevel n).toRingHom =
        qI.map (Ideal.Quotient.mk (qI ^ (n + 1))) := by
    have hcomp : (Ideal.Quotient.mk (qI ^ (n + 1))).comp (algebraMap R S) =
        ((eBaseLevel n).toRingHom).comp
          (Ideal.Quotient.mk (pI ^ (n + 1))) := by
      ext r
      exact (hBaseLevelMk n r).symm
    calc
      _ = pI.map ((eBaseLevel n).toRingHom.comp
            (Ideal.Quotient.mk (pI ^ (n + 1)))) := by rw [Ideal.map_map]
      _ = pI.map ((Ideal.Quotient.mk (qI ^ (n + 1))).comp (algebraMap R S)) := by
            rw [hcomp]
      _ = (pI.map (algebraMap R S)).map (Ideal.Quotient.mk (qI ^ (n + 1))) := by
            rw [← Ideal.map_map]
      _ = _ := by rw [← hpw]
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime qI
  let pLoc : Ideal Rp := IsLocalRing.maximalIdeal Rp
  let qLoc : Ideal Sq := IsLocalRing.maximalIdeal Sq
  have hpLocEq (n : ℕ) : (pLoc ^ n) • (⊤ : Submodule Rp Rp) =
      (pI ^ n).map (algebraMap R Rp) :=
    maximalIdeal_pow_smul_top_eq_map p n
  have hqLocEq (n : ℕ) : (qLoc ^ n) • (⊤ : Submodule Sq Sq) =
      (qI ^ n).map (algebraMap S Sq) :=
    maximalIdeal_pow_smul_top_eq_map qI n
  have hIp (n : ℕ) : pI ^ (n + 1) ≤ p := Ideal.pow_le_self (show n + 1 ≠ 0 by omega)
  have hIq (n : ℕ) : qI ^ (n + 1) ≤ qI := Ideal.pow_le_self (show n + 1 ≠ 0 by omega)
  let eLocLevel (n : ℕ) :
      (Rp ⧸ (pI ^ (n + 1)).map (algebraMap R Rp)) ≃+*
        (Sq ⧸ (qI ^ (n + 1)).map (algebraMap S Sq)) := by
    let : Algebra (R ⧸ pI ^ (n + 1))
        (Sq ⧸ (qI ^ (n + 1)).map (algebraMap S Sq)) :=
      ((algebraMap (S ⧸ qI ^ (n + 1))
        (Sq ⧸ (qI ^ (n + 1)).map (algebraMap S Sq))).comp
          (eBaseLevel n).toRingHom).toAlgebra
    exact (localizationQuotientEquivOfQuotientEquiv (Rp := Rp) (Sq := Sq) p qI
      (pI ^ (n + 1)) (qI ^ (n + 1)) (hIp n) (hIq n)
      (eBaseLevel n) (hLevelIdeal n)).toRingEquiv
  let fLoc : R →+* Sq := (algebraMap S Sq).comp (algebraMap R S)
  have hPFactor {m n : ℕ} (hmn : m ≤ n) :
      (pI ^ n).map (algebraMap R Rp) ≤ (pI ^ m).map (algebraMap R Rp) :=
    Ideal.map_mono (Ideal.pow_le_pow_right hmn)
  have hQFactor {m n : ℕ} (hmn : m ≤ n) :
      (qI ^ n).map (algebraMap S Sq) ≤ (qI ^ m).map (algebraMap S Sq) :=
    Ideal.map_mono (Ideal.pow_le_pow_right hmn)
  have hsource (n : ℕ) (r : R) :
      Ideal.Quotient.mk ((pI ^ (n + 1)).map (algebraMap R Rp)) (algebraMap R Rp r) =
        algebraMap (R ⧸ pI ^ (n + 1)) (Rp ⧸ (pI ^ (n + 1)).map (algebraMap R Rp))
          (Ideal.Quotient.mk (pI ^ (n + 1)) r) := by
    simp
  have hLocLevelMk (n : ℕ) (r : R) :
      eLocLevel n (Ideal.Quotient.mk ((pI ^ (n + 1)).map (algebraMap R Rp))
        (algebraMap R Rp r)) =
        Ideal.Quotient.mk ((qI ^ (n + 1)).map (algebraMap S Sq)) (fLoc r) := by
    let k := n + 1
    let : Algebra (R ⧸ pI ^ k) (Sq ⧸ (qI ^ k).map (algebraMap S Sq)) :=
      ((algebraMap (S ⧸ qI ^ k) (Sq ⧸ (qI ^ k).map (algebraMap S Sq))).comp
        (eBaseLevel n).toRingHom).toAlgebra
    rw [hsource]
    show localizationQuotientEquivOfQuotientEquiv (Rp := Rp) (Sq := Sq) p qI
      (pI ^ k) (qI ^ k) (hIp n) (hIq n) (eBaseLevel n) (hLevelIdeal n)
        (algebraMap (R ⧸ pI ^ k) (Rp ⧸ (pI ^ k).map (algebraMap R Rp))
          (Ideal.Quotient.mk (pI ^ k) r)) = _
    rw [localizationQuotientEquivOfQuotientEquiv_commutes (Rp := Rp) (Sq := Sq)
      p qI (pI ^ k) (qI ^ k) (hIp n) (hIq n) (eBaseLevel n) (hLevelIdeal n)
      (Ideal.Quotient.mk (pI ^ k) r), hBaseLevelMk]
    have hcomp :
        (algebraMap (S ⧸ qI ^ k) (Sq ⧸ (qI ^ k).map (algebraMap S Sq))).comp
            (algebraMap R (S ⧸ qI ^ k)) =
          (algebraMap S (Sq ⧸ (qI ^ k).map (algebraMap S Sq))).comp
            (algebraMap R S) := by
      ext r
      rfl
    exact congrArg (fun f : R →+* (Sq ⧸ (qI ^ k).map (algebraMap S Sq)) => f r) hcomp
  have hIpowLE {m n : ℕ} (hmn : m ≤ n) :
      (pI ^ (n + 1)).map (algebraMap R Rp) ≤ (pI ^ (m + 1)).map (algebraMap R Rp) :=
    hPFactor (Nat.add_le_add_right hmn 1)
  have hIqowLE {m n : ℕ} (hmn : m ≤ n) :
      (qI ^ (n + 1)).map (algebraMap S Sq) ≤ (qI ^ (m + 1)).map (algebraMap S Sq) :=
    hQFactor (Nat.add_le_add_right hmn 1)
  have hLocCompat {m n : ℕ} (hmn : m ≤ n)
      (z : Rp ⧸ (pI ^ (n + 1)).map (algebraMap R Rp)) :
      Ideal.Quotient.factor (hIqowLE hmn) (eLocLevel n z) =
        eLocLevel m (Ideal.Quotient.factor (hIpowLE hmn) z) := by
    let k := n + 1
    let q := p.map (Ideal.Quotient.mk (pI ^ k))
    have hqprime : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime (hIp n)
    have hlocal : IsLocalization.AtPrime
        (Rp ⧸ (pI ^ k).map (algebraMap R Rp)) q :=
      isLocalization_atPrime_quotient p Rp (pI ^ k) q (Ideal.comap_map_mk (hIp n))
    let := hlocal
    let f := (Ideal.Quotient.factor (hIqowLE hmn)).comp
      (eLocLevel n).toRingHom
    let g := (eLocLevel m).toRingHom.comp
      (Ideal.Quotient.factor (hIpowLE hmn))
    have hfg : f = g := by
      apply IsLocalization.ringHom_ext (R := R ⧸ pI ^ k) q.primeCompl
      apply RingHom.ext
      intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      show f (algebraMap (R ⧸ pI ^ k)
        (Rp ⧸ (pI ^ k).map (algebraMap R Rp)) (Ideal.Quotient.mk (pI ^ k) r)) =
        g (algebraMap (R ⧸ pI ^ k)
        (Rp ⧸ (pI ^ k).map (algebraMap R Rp)) (Ideal.Quotient.mk (pI ^ k) r))
      rw [← hsource n r]
      show Ideal.Quotient.factor (hIqowLE hmn)
          ((eLocLevel n) (Ideal.Quotient.mk
            ((pI ^ (n + 1)).map (algebraMap R Rp)) (algebraMap R Rp r))) =
        (eLocLevel m) (Ideal.Quotient.factor (hIpowLE hmn)
          (Ideal.Quotient.mk ((pI ^ (n + 1)).map (algebraMap R Rp))
            (algebraMap R Rp r))
        )
      calc
        _ = Ideal.Quotient.factor (hIqowLE hmn)
              (Ideal.Quotient.mk ((qI ^ (n + 1)).map (algebraMap S Sq)) (fLoc r)) := by
            rw [hLocLevelMk n r]
        _ = Ideal.Quotient.mk ((qI ^ (m + 1)).map (algebraMap S Sq)) (fLoc r) :=
            Ideal.Quotient.factor_mk (hIqowLE hmn) (fLoc r)
        _ = (eLocLevel m) (Ideal.Quotient.mk
              ((pI ^ (m + 1)).map (algebraMap R Rp)) (algebraMap R Rp r)) :=
            (hLocLevelMk m r).symm
        _ = (eLocLevel m) (Ideal.Quotient.factor
              (hIpowLE hmn)
              (Ideal.Quotient.mk ((pI ^ (n + 1)).map (algebraMap R Rp))
                (algebraMap R Rp r))) := by
            rw [Ideal.Quotient.factor_mk]
    exact DFunLike.congr_fun hfg z
  let cPLevel (n : ℕ) := Ideal.quotientEquivAlgOfEq Rp (hpLocEq n)
  let cQLevel (n : ℕ) := Ideal.quotientEquivAlgOfEq Sq (hqLocEq n)
  have hCastP {m n : ℕ} (hmn : m ≤ n)
      (z : Rp ⧸ (pLoc ^ n • (⊤ : Submodule Rp Rp))) :
      cPLevel m (AdicCompletion.transitionMap pLoc Rp hmn z) =
        Ideal.Quotient.factor (hPFactor hmn) (cPLevel n z) :=
    quotientEquivAlgOfEq_transitionMap pLoc hmn (hpLocEq m) (hpLocEq n) (hPFactor hmn) z
  have hCastQ {m n : ℕ} (hmn : m ≤ n)
      (z : Sq ⧸ (qLoc ^ n • (⊤ : Submodule Sq Sq))) :
      cQLevel m (AdicCompletion.transitionMap qLoc Sq hmn z) =
        Ideal.Quotient.factor (hQFactor hmn) (cQLevel n z) :=
    quotientEquivAlgOfEq_transitionMap qLoc hmn (hqLocEq m) (hqLocEq n) (hQFactor hmn) z
  let eTower (n : ℕ) :
      (Rp ⧸ (pLoc ^ n • (⊤ : Submodule Rp Rp))) ≃+*
        (Sq ⧸ (qLoc ^ n • (⊤ : Submodule Sq Sq))) := by
    cases n with
    | zero =>
      have hP : pLoc ^ 0 • (⊤ : Submodule Rp Rp) = ⊤ := by simp
      have hQ : qLoc ^ 0 • (⊤ : Submodule Sq Sq) = ⊤ := by simp
      let cP := Ideal.quotientEquivAlgOfEq Rp hP
      let cQ := Ideal.quotientEquivAlgOfEq Sq hQ
      exact cP.toRingEquiv.trans ((quotientTopRingEquiv (R := Rp) (S := Sq)).trans
        cQ.toRingEquiv.symm)
    | succ n =>
      exact (cPLevel (n + 1)).toRingEquiv.trans
        ((eLocLevel n).trans (cQLevel (n + 1)).toRingEquiv.symm)
  have hSub0 : Subsingleton (Sq ⧸ (qLoc ^ 0 • (⊤ : Submodule Sq Sq))) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  have heTower : ∀ {m n : ℕ} (hmn : m ≤ n)
      (z : Rp ⧸ (pLoc ^ n • (⊤ : Submodule Rp Rp))),
      AdicCompletion.transitionMap qLoc Sq hmn (eTower n z) =
        eTower m (AdicCompletion.transitionMap pLoc Rp hmn z) := by
    intro m n hmn z
    cases m with
    | zero =>
      exact Subsingleton.elim _ _
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        have hmn' : m ≤ n := by omega
        apply (cQLevel (m + 1)).injective
        calc
          _ = Ideal.Quotient.factor (hQFactor (Nat.add_le_add_right hmn' 1))
              (cQLevel (n + 1) (eTower (n + 1) z)) :=
            hCastQ hmn (eTower (n + 1) z)
          _ = Ideal.Quotient.factor (hQFactor (Nat.add_le_add_right hmn' 1))
              (eLocLevel n (cPLevel (n + 1) z)) := by
            show Ideal.Quotient.factor (hQFactor (Nat.add_le_add_right hmn' 1))
              ((cQLevel (n + 1)).toRingEquiv (eTower (n + 1) z)) =
                Ideal.Quotient.factor (hQFactor (Nat.add_le_add_right hmn' 1))
                  (eLocLevel n ((cPLevel (n + 1)).toRingEquiv z))
            simp only [eTower, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
          _ = eLocLevel m
              (Ideal.Quotient.factor (hPFactor (Nat.add_le_add_right hmn' 1))
                ((cPLevel (n + 1)).toRingEquiv z)) := hLocCompat hmn' _
          _ = eLocLevel m
              ((cPLevel (m + 1)).toRingEquiv
                (AdicCompletion.transitionMap pLoc Rp hmn z)) :=
            congrArg (eLocLevel m) (hCastP hmn z).symm
          _ = cQLevel (m + 1)
              (eTower (m + 1) (AdicCompletion.transitionMap pLoc Rp hmn z)) := by
            show eLocLevel m
              ((cPLevel (m + 1)).toRingEquiv
                (AdicCompletion.transitionMap pLoc Rp hmn z)) =
                (cQLevel (m + 1)).toRingEquiv
                  (eTower (m + 1) (AdicCompletion.transitionMap pLoc Rp hmn z))
            simp only [eTower, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  let eComp := adicCompletionRingEquivOfQuotientEquivs pLoc qLoc eTower heTower
  let hLoc := Localization.localRingHom p qI (algebraMap R S) hpq.symm
  have hLevelLocal (n : ℕ) :
      (eLocLevel n).toRingHom.comp
          (Ideal.Quotient.mk ((pI ^ (n + 1)).map (algebraMap R Rp))) =
        (Ideal.Quotient.mk ((qI ^ (n + 1)).map (algebraMap S Sq))).comp hLoc := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    show (eLocLevel n)
        (Ideal.Quotient.mk ((pI ^ (n + 1)).map (algebraMap R Rp))
          (algebraMap R Rp r)) =
      Ideal.Quotient.mk ((qI ^ (n + 1)).map (algebraMap S Sq))
        (hLoc (algebraMap R Rp r))
    rw [Localization.localRingHom_to_map]
    exact hLocLevelMk n r
  have hTowerLocal (n : ℕ) (r : Rp) :
      eTower n (Ideal.Quotient.mk (pLoc ^ n • (⊤ : Submodule Rp Rp)) r) =
        Ideal.Quotient.mk (qLoc ^ n • (⊤ : Submodule Sq Sq)) (hLoc r) := by
    cases n with
    | zero =>
      exact Subsingleton.elim _ _
    | succ n =>
      apply (cQLevel (n + 1)).toRingEquiv.injective
      have hP : (cPLevel (n + 1)).toRingEquiv
          (Ideal.Quotient.mk (pLoc ^ (n + 1) • (⊤ : Submodule Rp Rp)) r) =
            Ideal.Quotient.mk ((pI ^ (n + 1)).map (algebraMap R Rp)) r := by
        simp [cPLevel, Ideal.quotientEquivAlgOfEq_mk]
      have hQ : (cQLevel (n + 1)).toRingEquiv
          (Ideal.Quotient.mk (qLoc ^ (n + 1) • (⊤ : Submodule Sq Sq)) (hLoc r)) =
            Ideal.Quotient.mk ((qI ^ (n + 1)).map (algebraMap S Sq)) (hLoc r) := by
        simp [cQLevel, Ideal.quotientEquivAlgOfEq_mk]
      calc
        _ = (eLocLevel n)
            ((cPLevel (n + 1)).toRingEquiv
              (Ideal.Quotient.mk (pLoc ^ (n + 1) • (⊤ : Submodule Rp Rp)) r)) := by
              simp only [eTower, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
        _ = (eLocLevel n)
            (Ideal.Quotient.mk ((pI ^ (n + 1)).map (algebraMap R Rp)) r) :=
              congrArg (eLocLevel n) hP
        _ = Ideal.Quotient.mk ((qI ^ (n + 1)).map (algebraMap S Sq)) (hLoc r) :=
              DFunLike.congr_fun (hLevelLocal n) r
        _ = (cQLevel (n + 1)).toRingEquiv
            (Ideal.Quotient.mk (qLoc ^ (n + 1) • (⊤ : Submodule Sq Sq)) (hLoc r)) := hQ.symm
  have hCompLocal (r : Rp) :
      eComp (algebraMap Rp (AdicCompletion pLoc Rp) r) =
        algebraMap Sq (AdicCompletion qLoc Sq) (hLoc r) := by
    apply AdicCompletion.ext
    intro n
    show eTower n ((algebraMap Rp (AdicCompletion pLoc Rp) r).val n) =
      (algebraMap Sq (AdicCompletion qLoc Sq) (hLoc r)).val n
    simpa [AdicCompletion.algebraMap_apply, AdicCompletion.eval_of,
      AdicCompletion.eval_apply] using hTowerLocal n r
  exact ⟨eComp, hCompLocal⟩

namespace AlgebraicGeometry

/-- After base change from a local ring to its completion, the map on local rings at a point
over the closed point induces an isomorphism on completions. -/
@[stacks 0BG5, ega "IV 7.9.3.1"]
theorem stalkMap_adicCompletion_isomorphism
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hfg : (IsLocalRing.maximalIdeal A).FG)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Y : Scheme.{u} := pullback f g
    let π : Y ⟶ X := pullback.fst f g
    ∀ (q : Y),
      f.base (π.base q) =
          (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A) →
        ∃ e : AdicCompletion
              (IsLocalRing.maximalIdeal (X.presheaf.stalk (π.base q)))
              (X.presheaf.stalk (π.base q)) ≃+*
            AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk q))
              (Y.presheaf.stalk q),
          e.toRingHom.comp
              (algebraMap (X.presheaf.stalk (π.base q))
                (AdicCompletion
                  (IsLocalRing.maximalIdeal (X.presheaf.stalk (π.base q)))
                  (X.presheaf.stalk (π.base q)))) =
            (algebraMap (Y.presheaf.stalk q)
              (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk q))
                (Y.presheaf.stalk q))).comp (π.stalkMap q).hom := by
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Y : Scheme := pullback f g
    let π : Y ⟶ X := pullback.fst f g
    show ∀ (q : Y), f.base (π.base q) =
        (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A) → _
    intro q hq
    let x : X := π.base q
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (x := x) (U := ⊤) (by simp)
    have hxW : q ∈ π ⁻¹ᵁ U := hxU
    let W : Y.Opens := π ⁻¹ᵁ U
    let qW : W.toScheme := ⟨q, hxW⟩
    have hW : IsAffineOpen W := by
      let : IsAffine U.toScheme := hU
      let : IsAffine (⊤ : (Spec (.of Ahat)).Opens).toScheme := isAffineOpen_top _
      let : IsAffine (⊤ : (Spec (.of A)).Opens).toScheme := isAffineOpen_top _
      simpa [W] using isAffineOpen_inf_preimage f g (U := U) (V := ⊤) (S₀ := ⊤)
        (by simp) (by simp)
    let pU := hU.primeIdealOf ⟨x, hxU⟩
    let pW := hW.primeIdealOf qW
    have hVU : W ≤ π ⁻¹ᵁ U := le_rfl
    have hstalkIso := IsAffineOpen.arrowStalkMapIso π U hU W hW hVU hxW
    have hprime := IsAffineOpen.comap_primeIdealOf_appLE U hU W hW hVU hxW
    let U₀ : (Spec (.of A)).Opens := ⊤
    let hU₀ : IsAffineOpen U₀ := isAffineOpen_top _
    have hle : U ≤ f ⁻¹ᵁ U₀ := by
      intro y hy
      simp [U₀]
    let α : Opposite.op (CommRingCat.of Γ(X, U)) ⟶ Opposite.op (CommRingCat.of A) :=
      (f.appLE U₀ U hle).op ≫ (Scheme.ΓSpecIso (.of A)).inv.op
    let : Algebra A Γ(X, U) := (CommRingCat.Hom.hom α.unop).toAlgebra
    let R := Γ(X, U)
    let S := Γ(Y, W)
    let φ := CommRingCat.Hom.hom (π.appLE U W hVU)
    let : Algebra R S := φ.toAlgebra
    let eHat := Scheme.ΓSpecIso (.of Ahat)
    let ψ := CommRingCat.Hom.hom (eHat.inv ≫ (pullback.snd f g).appLE
      (⊤ : (Spec (.of Ahat)).Opens) W (by simp [W]))
    let : Algebra Ahat S := ψ.toAlgebra
    have hUY : W = π ⁻¹ᵁ U ⊓ (pullback.snd f g) ⁻¹ᵁ (⊤ : (Spec (.of Ahat)).Opens) := by
      ext z
      simp [W]
    let H : IsPullback π (pullback.snd f g) f g := .of_hasPullback f g
    have hUST : (⊤ : (Spec (.of Ahat)).Opens) ≤ g ⁻¹ᵁ U₀ := by simp [U₀]
    have hsecIso : IsIso (AlgebraicGeometry.pushoutSection H hUST hle hUY) :=
      isIso_pushoutSection_of_isAffineOpen H hUST hle hUY hU₀
        (isAffineOpen_top _) hU
    have hGammaPush : IsPushout (f.appLE U₀ U hle)
        (g.appLE U₀ (⊤ : (Spec (.of Ahat)).Opens) hUST)
        (π.appLE U W hVU)
        ((pullback.snd f g).appLE (⊤ : (Spec (.of Ahat)).Opens) W (by simp [W])) :=
      (isIso_pushoutSection_iff H hUST hle hUY).mp hsecIso
    let eΓ := Scheme.ΓSpecIso (.of A)
    let β : A →+* Ahat := algebraMap A Ahat
    let hPushA : IsPushout (CommRingCat.ofHom (algebraMap A R))
        (CommRingCat.ofHom β)
        (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ) :=
      hGammaPush.of_iso eΓ (Iso.refl _) eHat (Iso.refl _)
        (by
          show f.appLE U₀ U hle = eΓ.hom ≫ α.unop
          dsimp [α]
          exact (Iso.hom_inv_id_assoc eΓ _).symm)
        (by
          show g.appLE U₀ (⊤ : (Spec (.of Ahat)).Opens) hUST ≫ eHat.hom =
            eΓ.hom ≫ CommRingCat.ofHom (algebraMap A Ahat)
          show g.appTop ≫ eHat.hom = eΓ.hom ≫ CommRingCat.ofHom (algebraMap A Ahat)
          exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A Ahat)))
        rfl (by
          show (pullback.snd f g).appLE (⊤ : (Spec (.of Ahat)).Opens) W
              (by simp [W]) = eHat.hom ≫ eHat.inv ≫
                (pullback.snd f g).appLE (⊤ : (Spec (.of Ahat)).Opens) W (by simp [W])
          exact (Iso.hom_inv_id_assoc eHat _).symm)
    have hMaps : φ.comp (algebraMap A R) = ψ.comp β :=
      congrArg CommRingCat.Hom.hom hPushA.w
    let : Algebra A S := (φ.comp (algebraMap A R)).toAlgebra
    let : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq' rfl
    have hTowerMap : algebraMap A S = (algebraMap Ahat S).comp (algebraMap A Ahat) := hMaps
    let : IsScalarTower A Ahat S := IsScalarTower.of_algebraMap_eq' hTowerMap
    let hAlgebraPush : Algebra.IsPushout A R Ahat S :=
      (CommRingCat.isPushout_iff_isPushout.mp hPushA)
    let eBase : (R ⊗[A] Ahat) ≃ₐ[R] S := hAlgebraPush.equiv A R Ahat
    let m : Ideal A := IsLocalRing.maximalIdeal A
    let p := pU.asIdeal
    have hfx : f x = (⟨m, inferInstance⟩ : PrimeSpectrum A) := by
      simpa [x, m] using hq
    have hprimef := IsAffineOpen.comap_primeIdealOf_appLE U₀ hU₀ U hU hle hxU
    have hbaseSpec' : hU₀.fromSpec = Spec.map eΓ.inv := by
      simpa [U₀, hU₀, eΓ] using
        (IsAffineOpen.fromSpec_top (X := Spec (.of A))).trans
          (Scheme.isoSpec_Spec_inv (.of A))
    have htopPrime : PrimeSpectrum.comap eΓ.inv.hom
        (hU₀.primeIdealOf ⟨f x, by simp [U₀]⟩) = f x := by
      show (Spec.map eΓ.inv) (hU₀.primeIdealOf ⟨f x, by simp [U₀]⟩) = f x
      rw [← hbaseSpec']
      exact hU₀.fromSpec_primeIdealOf ⟨f x, by simp [U₀]⟩
    have hbasePrime : PrimeSpectrum.comap (algebraMap A R) pU =
        (⟨m, inferInstance⟩ : PrimeSpectrum A) := by
      show PrimeSpectrum.comap
        ((CommRingCat.Hom.hom (f.appLE U₀ U hle)).comp eΓ.inv.hom) pU = _
      simp only [PrimeSpectrum.comap_comp, Function.comp_apply]
      rw [hprimef, htopPrime]
      exact hfx
    have hAinP : (m.map (algebraMap A R)) ≤ p := by
      rw [Ideal.map_le_iff_le_comap]
      exact (congrArg PrimeSpectrum.asIdeal hbasePrime).ge
    have hprimeIdeal : pW.asIdeal.comap φ = p := congrArg PrimeSpectrum.asIdeal hprime
    obtain ⟨eComp, hCompLocal⟩ :=
      exists_adicCompletion_ringEquiv_localRingHom (A := A) (R := R) (S := S) hfg eBase
        p pW.asIdeal hprimeIdeal hAinP
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime pW.asIdeal
    let hLoc := Localization.localRingHom p pW.asIdeal φ hprimeIdeal.symm
    let eSourceStalk : X.presheaf.stalk (π.base q) ≃+* Rp :=
      (asIso hstalkIso.hom.left).commRingCatIsoToRingEquiv
    let eTargetStalk : Y.presheaf.stalk q ≃+* Sq :=
      (asIso hstalkIso.hom.right).commRingCatIsoToRingEquiv
    let eSourceCompletion := completionRingEquivOfLocalRingEquiv eSourceStalk
    let eTargetCompletionBack := completionRingEquivOfLocalRingEquiv eTargetStalk.symm
    let eFinal := eSourceCompletion.trans (eComp.trans eTargetCompletionBack)
    have hSquare :
        hLoc.comp eSourceStalk.toRingHom =
          eTargetStalk.toRingHom.comp (CommRingCat.Hom.hom (π.stalkMap q)) :=
      congrArg CommRingCat.Hom.hom (Arrow.w_mk hstalkIso.hom)
    refine ⟨eFinal, ?_⟩
    apply RingHom.ext
    intro r
    show eTargetCompletionBack
        (eComp (eSourceCompletion
          (algebraMap (X.presheaf.stalk (π.base q))
            (AdicCompletion (IsLocalRing.maximalIdeal
              (X.presheaf.stalk (π.base q))) (X.presheaf.stalk (π.base q))) r))) =
      algebraMap (Y.presheaf.stalk q)
        (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk q))
          (Y.presheaf.stalk q)) ((CommRingCat.Hom.hom (π.stalkMap q)) r)
    rw [completionRingEquivOfLocalRingEquiv_commutes eSourceStalk r,
      hCompLocal (eSourceStalk r)]
    calc
      _ = algebraMap (Y.presheaf.stalk q)
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk q))
            (Y.presheaf.stalk q))
          (eTargetStalk.symm (hLoc (eSourceStalk r))) :=
            completionRingEquivOfLocalRingEquiv_commutes eTargetStalk.symm
              (hLoc (eSourceStalk r))
      _ = algebraMap (Y.presheaf.stalk q)
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk q))
            (Y.presheaf.stalk q)) ((CommRingCat.Hom.hom (π.stalkMap q)) r) := by
        congr 1
        apply eTargetStalk.injective
        have harg := congrArg (fun F : X.presheaf.stalk (π.base q) →+* Sq => F r) hSquare
        change hLoc (eSourceStalk r) =
          eTargetStalk ((CommRingCat.Hom.hom (π.stalkMap q)) r) at harg
        simpa only [RingEquiv.apply_symm_apply] using harg

end AlgebraicGeometry

end
