module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.AdicFiltration
public import StacksFrontier.RingTheory.Flat.BaseChange
public import StacksFrontier.RingTheory.Flat.ClosedSubset
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus
import StacksFrontier.RingTheory.Flat.LocalizedComap
import StacksFrontier.RingTheory.Support.Basic

/-!
# Flattening over closed subsets of source and base

The standing data of this section is a map of commutative rings `R → S`, an ideal `J` of `S` and
an `S`-module `M`. For a base change `R → R'` and an ideal `I'` of `R'` one asks whether the base
change of `M` is flat over `R'` at every prime of `S ⊗[R] R'` containing the extensions of `I'`
and `J`. This condition is stable under a further base change and under enlarging the ideal on
the new base, it descends along a base change which is surjective onto the closed subset and has
flat local rings there, it descends from a filtered colimit of bases to one stage of that
colimit as soon as `R → S` is essentially of finite presentation and `M` is finitely presented,
and it may be checked after passing to the quotients by the powers of an ideal of the base.

## Main results

* `Module.FlatteningSituation`: the standing data of the section.
* `Module.IsFlatAtPrimesOver`: the flatness condition (15.19.1).
* `Module.IsFlatAtPrimesOver.baseChange`: stability under a further base change.
* `Module.IsFlatAtPrimesOver.of_baseChange`: descent along a flat cover of the closed subset.
* `Module.exists_isFlatAtPrimesOver_of_isColimit`: descent from a filtered colimit of bases to
  one stage of that colimit.
* `Module.flat_localizedModule_atPrime_of_flat_quotient_pow`: flatness modulo every positive
  power of an ideal of the base implies flatness.

## Implementation notes

For the descent from a filtered colimit, the ideal on the colimit is the supremum of the images
of the compatible stage ideals, and the colimit is given as a cocone whose image under the
forgetful functor to types is a colimit; that preservation hypothesis is what expresses the
source's elementwise directed colimit, and it must be stated explicitly because the index
universes and the ring universe are independent. A final directed preorder
(`CategoryTheory.IsFiltered.exists_directed`) reduces the filtered index category to an
elementwise directed system, so the ingredients collected for Stacks Tag 05LM in
`StacksFrontier.RingTheory.Flat.ClosedSubset` apply verbatim. Writing `S` as a localization of a
finitely presented `R`-algebra `C` and `M` as the base change of a finitely presented
`C`-module `N` (Stacks Tag 05N5), openness of the relative flat locus (Stacks Tag 00RC) covers
the relevant closed subset by finitely many flat principal opens of `Spec (C ⊗[R] L)`, and both
those flatnesses and the equation expressing the cover descend to a common stage
(Stacks Tag 02JO).

## References

* [The Stacks Project, Tag 05LP](https://stacks.math.columbia.edu/tag/05LP)
* [The Stacks Project, Tag 05LQ](https://stacks.math.columbia.edu/tag/05LQ)
* [The Stacks Project, Tag 05LR](https://stacks.math.columbia.edu/tag/05LR)
* [The Stacks Project, Tag 05LS](https://stacks.math.columbia.edu/tag/05LS)
* [The Stacks Project, Tag 05LT](https://stacks.math.columbia.edu/tag/05LT)
* [The Stacks Project, Tag 05LU](https://stacks.math.columbia.edu/tag/05LU)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y z

/-- **Stacks Tag 05LP.** The fixed data for flattening over closed subsets of source and base:
a ring map `R → S`, an ideal `J ⊆ S`, and an `S`-module `M`. -/
@[stacks 05LP]
structure Module.FlatteningSituation where
  /-- The base ring. -/
  R : Type u
  /-- The source ring. -/
  S : Type v
  /-- The module whose flattening is studied. -/
  M : Type w
  /-- The commutative ring structure on the base. -/
  [commRingR : CommRing R]
  /-- The commutative ring structure on the source. -/
  [commRingS : CommRing S]
  /-- The ring map from the base to the source. -/
  hom : R →+* S
  /-- The ideal defining the fixed closed subset of the source. -/
  J : Ideal S
  /-- The additive group structure on the module. -/
  [addCommGroupM : AddCommGroup M]
  /-- The `S`-module structure. -/
  [moduleM : Module S M]

/-- **Stacks Tag 05LQ.** Condition (15.19.1): the base change of `M` along `R → R'` is flat over
`R'` at every prime of `S ⊗[R] R'` containing the extensions of both `I'` and `J`. The module
denoted `M ⊗_R R'` in the source is represented by the canonically equivalent extension of
scalars `(S ⊗[R] R') ⊗[S] M`. -/
@[stacks 05LQ]
def Module.IsFlatAtPrimesOver {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (J : Ideal S) {M : Type w} [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] (R' : Type x) [CommRing R'] [Algebra R R']
    (I' : Ideal R') : Prop :=
  let S' := S ⊗[R] R'
  letI : Algebra R' S' := Algebra.TensorProduct.rightAlgebra
  ∀ (q : Ideal S') (_ : q.IsPrime),
    Ideal.map
          (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := R')).toRingHom I' +
        Ideal.map
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := R')) J ≤ q →
      Module.Flat R' (LocalizedModule q.primeCompl (S' ⊗[S] M))

/-! ### Localizing after an extension of scalars -/

/-- Scalar extension carries a localization of modules to a localization at the image of its
denominator submonoid. -/
theorem IsLocalizedModule.lTensor_algebraMapSubmonoid
    {A B X N : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup X] [Module A X]
    [AddCommGroup N] [Module A N] (T : Submonoid A)
    (g : X →ₗ[A] N) [IsLocalizedModule T g] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid B T)
      (TensorProduct.AlgebraTensorModule.lTensor B B g) := by
  let h : B ⊗[A] X →ₗ[B] B ⊗[A] N := TensorProduct.AlgebraTensorModule.lTensor B B g
  have hg : IsLocalizedModule T (TensorProduct.AlgebraTensorModule.rTensor A B g) :=
    IsLocalizedModule.rTensor A T g
  have hh : IsLocalizedModule T (h.restrictScalars A) := by
    let eX := TensorProduct.comm A X B
    let eN := TensorProduct.comm A N B
    have he : h.restrictScalars A =
        eN.toLinearMap ∘ₗ (TensorProduct.AlgebraTensorModule.rTensor A B g) ∘ₗ
          eX.symm.toLinearMap := by
      ext b z
      rfl
    rw [he]
    have : IsLocalizedModule T
        ((TensorProduct.AlgebraTensorModule.rTensor A B g) ∘ₗ eX.symm.toLinearMap) :=
      IsLocalizedModule.of_linearEquiv_right T _ eX.symm
    exact IsLocalizedModule.of_linearEquiv T _ eN
  exact IsLocalizedModule.of_restrictScalars T h

/-- A base-changed flat module stays flat after localizing at a prime whose complement contains
the image of the original denominators. -/
theorem Module.Flat.localizedModule_baseChange
    {R A R₂ B N : Type*} [CommRing R] [CommRing A] [CommRing R₂] [CommRing B]
    [Algebra R A] [Algebra R R₂] [Algebra R B] [Algebra A B] [Algebra R₂ B]
    [IsScalarTower R A B] [IsScalarTower R R₂ B] [Algebra.IsPushout R A R₂ B]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Flat R N]
    {X P : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup P] [Module R₂ P] [Module B P] [IsScalarTower R₂ B P]
    (T : Submonoid A) (g : X →ₗ[A] N) [IsLocalizedModule T g]
    (eP : B ⊗[A] X ≃ₗ[B] P) (q : Ideal B) [q.IsPrime]
    (hT : Algebra.algebraMapSubmonoid B T ≤ q.primeCompl) :
    Module.Flat R₂ (LocalizedModule q.primeCompl P) := by
  let Q := R₂ ⊗[R] N
  let : Algebra.IsPushout R R₂ A B := Algebra.IsPushout.symm inferInstance
  let eQ : B ⊗[A] N ≃ₗ[R₂] Q := Algebra.IsPushout.cancelBaseChange R R₂ A B N
  have : Module.Flat R₂ Q := Module.Flat.baseChange R R₂ N
  have : Module.Flat R₂ (B ⊗[A] N) := Module.Flat.of_linearEquiv eQ
  let f₁ : B ⊗[A] X →ₗ[B] B ⊗[A] N := TensorProduct.AlgebraTensorModule.lTensor B B g
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid B T) f₁ :=
    IsLocalizedModule.lTensor_algebraMapSubmonoid T g
  let f₂ : B ⊗[A] X →ₗ[B] LocalizedModule q.primeCompl P :=
    (LocalizedModule.mkLinearMap q.primeCompl P) ∘ₗ eP.toLinearMap
  have : IsLocalizedModule q.primeCompl f₂ :=
    IsLocalizedModule.of_linearEquiv_right q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl P) eP
  let f : B ⊗[A] N →ₗ[B] LocalizedModule q.primeCompl P :=
    IsLocalizedModule.liftOfLE _ _ hT f₁ f₂
  exact Module.Flat.of_isLocalizedModule_of_tower q.primeCompl f

/-- The denominators of a prime, pushed forward along an algebra map, avoid the prime. -/
private theorem algebraMapSubmonoid_primeCompl_comap_le {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (q : Ideal B) [q.IsPrime] :
    Algebra.algebraMapSubmonoid B (q.comap (algebraMap A B)).primeCompl ≤ q.primeCompl := by
  rintro _ ⟨a, ha, rfl⟩
  exact ha

/-! ### Stability under a further base change -/

/-- **Stacks Tag 05LR.** Flatness at all primes over the extensions of `I'` and `J` is preserved
by a further base change `R' → R''` and by replacing the extension of `I'` with a larger
ideal `I''`. -/
@[stacks 05LR]
lemma Module.IsFlatAtPrimesOver.baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (J : Ideal S) {M : Type w} [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    (R' : Type x) [CommRing R'] [Algebra R R']
    (R'' : Type y) [CommRing R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower R R' R'']
    (I' : Ideal R') (I'' : Ideal R'')
    (hI : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hflat : Module.IsFlatAtPrimesOver (R := R) (S := S) J (M := M) R' I') :
    Module.IsFlatAtPrimesOver (R := R) (S := S) J (M := M) R'' I'' := by
  dsimp only [Module.IsFlatAtPrimesOver] at hflat ⊢
  intro q hq hcontain
  let S' := S ⊗[R] R'
  let S'' := S ⊗[R] R''
  let f : S' →ₐ[R] S'' := Algebra.TensorProduct.map
    (AlgHom.id R S) (IsScalarTower.toAlgHom R R' R'')
  let p : Ideal S' := q.comap f.toRingHom
  have hp : p.IsPrime := hq.comap _
  have hpcontain :
      Ideal.map
            (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := R')).toRingHom I' +
          Ideal.map
            (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := R')) J ≤ p := by
    rw [Ideal.add_eq_sup]
    refine sup_le (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
      (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
    · change f (1 ⊗ₜ[R] a) ∈ q
      rw [Algebra.TensorProduct.map_tmul, map_one]
      exact hcontain (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (hI (Ideal.mem_map_of_mem _ ha))))
    · change f (a ⊗ₜ[R] 1) ∈ q
      rw [Algebra.TensorProduct.map_tmul, map_one]
      exact hcontain (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha))
  have hflatp := hflat p hp hpcontain
  let : Algebra R' S' := Algebra.TensorProduct.rightAlgebra
  let : Algebra R'' S'' := Algebra.TensorProduct.rightAlgebra
  let : Algebra R' S'' := (algebraMap R'' S'').comp (algebraMap R' R'') |>.toAlgebra
  let : IsScalarTower R' R'' S'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra S' S'' := f.toRingHom.toAlgebra
  let : IsScalarTower R' S' S'' := IsScalarTower.of_algebraMap_eq fun a => by
    change f (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] algebraMap R' R'' a
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  let : IsScalarTower S S' S'' := IsScalarTower.of_algebraMap_eq fun a => by
    change a ⊗ₜ[R] 1 = f (a ⊗ₜ[R] 1)
    symm
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  let : Algebra.IsPushout R' S' R'' S'' :=
    ((Algebra.IsPushout.comp_iff R R' S S' (T := R'') (T' := S'')).mp inferInstance).symm
  let : Algebra.IsPushout R' R'' S' S'' := Algebra.IsPushout.symm inferInstance
  have hT : Algebra.algebraMapSubmonoid S'' p.primeCompl ≤ q.primeCompl :=
    algebraMapSubmonoid_primeCompl_comap_le q
  let e : S'' ⊗[S'] (S' ⊗[S] M) ≃ₗ[S''] S'' ⊗[S] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S S' S'' S'' M
  exact Module.Flat.localizedModule_baseChange (R := R') (A := S') (R₂ := R'') (B := S'')
    (N := LocalizedModule p.primeCompl (S' ⊗[S] M))
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl (S' ⊗[S] M))
    e q hT

/-! ### Descent along a flat cover of the closed subset -/

/-- A prime of `B` whose contraction lies under a prime of `C` containing `I` lifts to a prime of
`B ⊗[A] (C ⧸ I)`. -/
theorem Stacks.Flatness.Stratification.exists_prime_tensorProduct_quotient
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (q : Ideal B) [q.IsPrime] (I : Ideal C)
    (h : ∃ p : Ideal C, p.IsPrime ∧ I ≤ p ∧
      p.comap (algebraMap A C) = q.comap (algebraMap A B)) :
    ∃ t : Ideal (B ⊗[A] (C ⧸ I)), t.IsPrime ∧
      t.comap (algebraMap B (B ⊗[A] (C ⧸ I))) = q := by
  obtain ⟨p, hp, hIp, hcomp⟩ := h
  let : p.IsPrime := hp
  let r : Ideal A := q.comap (algebraMap A B)
  let : r.IsPrime := inferInstance
  let pQ : Ideal (C ⧸ I) := p.map (Ideal.Quotient.mk I)
  have hpQ : pQ.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIp
  have hcomap : pQ.comap (algebraMap A (C ⧸ I)) = r := by
    change (p.map (Ideal.Quotient.mk I)).comap
      ((Ideal.Quotient.mk I).comp (algebraMap A C)) = _
    rwa [← Ideal.comap_comap, Ideal.comap_map_mk hIp]
  let : Nontrivial (r.ResidueField ⊗[A] (C ⧸ I)) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap
      (S := C ⧸ I) (⟨r, inferInstance⟩ : PrimeSpectrum A)).mpr
      ⟨⟨pQ, hpQ⟩, PrimeSpectrum.ext hcomap⟩
  let : Nontrivial (q.ResidueField ⊗[B] (B ⊗[A] (C ⧸ I))) :=
    PrimeSpectrum.nontrivial_residueField_tensorProduct_baseChange
      (p := ⟨r, inferInstance⟩) (⟨q, inferInstance⟩ : PrimeSpectrum B) rfl
  obtain ⟨t, ht⟩ := (PrimeSpectrum.nontrivial_iff_mem_rangeComap
    (S := B ⊗[A] (C ⧸ I)) (⟨q, inferInstance⟩ : PrimeSpectrum B)).mp inferInstance
  exact ⟨t.asIdeal, t.2, congrArg PrimeSpectrum.asIdeal ht⟩

/-- Compatible primes lift to a pushout, with the lifted prime containing the image of the
prescribed ideal of the other factor. -/
theorem Stacks.Flatness.Stratification.exists_prime_pushout_of_closed_surjective
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D] [Algebra.IsPushout A B C D]
    (q : Ideal B) [q.IsPrime] (I : Ideal C)
    (h : ∃ p : Ideal C, p.IsPrime ∧ I ≤ p ∧
      p.comap (algebraMap A C) = q.comap (algebraMap A B)) :
    ∃ t : Ideal D, t.IsPrime ∧ t.comap (algebraMap B D) = q ∧
      I ≤ t.comap (algebraMap C D) := by
  obtain ⟨t, ht, hq⟩ := exists_prime_tensorProduct_quotient q I h
  let e : B ⊗[A] C ≃ₐ[B] D := Algebra.IsPushout.equiv A B C D
  let φ : D →+* B ⊗[A] (C ⧸ I) :=
    (Algebra.TensorProduct.map (AlgHom.id A B) (Ideal.Quotient.mkₐ A I)).toRingHom.comp
      e.symm.toRingHom
  have hφB : φ.comp (algebraMap B D) = algebraMap B (B ⊗[A] (C ⧸ I)) := by
    ext b
    simp [φ, e]
  have hφC : φ.comp (algebraMap C D) =
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C ⧸ I)).toRingHom.comp
        (Ideal.Quotient.mk I) := by
    ext c
    simp [φ, e, Algebra.IsPushout.equiv_symm_algebraMap_right]
  refine ⟨t.comap φ, ht.comap _, ?_, ?_⟩
  · change t.comap (φ.comp (algebraMap B D)) = q
    rwa [hφB]
  · intro c hc
    change φ (algebraMap C D c) ∈ t
    rw [← RingHom.comp_apply, hφC, RingHom.comp_apply]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hc]

/-- The localization of a pushout at a prime is flat over the second factor when the localization
of the first factor at the contracted prime is flat over the base. -/
private theorem Module.Flat.localization_atPrime_of_isPushout
    {R' R'' S' S'' : Type*} [CommRing R'] [CommRing R''] [CommRing S'] [CommRing S'']
    [Algebra R' R''] [Algebra R' S'] [Algebra R' S''] [Algebra R'' S''] [Algebra S' S'']
    [IsScalarTower R' R'' S''] [IsScalarTower R' S' S''] [Algebra.IsPushout R' R'' S' S'']
    (q'' : Ideal S'') [q''.IsPrime]
    [Module.Flat R' (Localization.AtPrime (q''.comap (algebraMap R'' S'')))] :
    Module.Flat S' (Localization.AtPrime q'') := by
  let p'' := q''.comap (algebraMap R'' S'')
  have hT : Algebra.algebraMapSubmonoid S'' p''.primeCompl ≤ q''.primeCompl :=
    algebraMapSubmonoid_primeCompl_comap_le q''
  have : Module.Flat S' (LocalizedModule q''.primeCompl S'') :=
    Module.Flat.localizedModule_baseChange (R := R') (A := R'') (R₂ := S') (B := S'')
      (N := Localization.AtPrime p'') p''.primeCompl
      (Algebra.linearMap R'' (Localization.AtPrime p''))
      (TensorProduct.AlgebraTensorModule.rid R'' S'' S'') q'' hT
  exact Module.Flat.of_linearEquiv
    ((IsLocalizedModule.linearEquiv q''.primeCompl
      (LocalizedModule.mkLinearMap q''.primeCompl S'')
      (Algebra.linearMap S'' (Localization.AtPrime q''))).restrictScalars S').symm

/-- A localized extension of scalars that is flat over `R''` is flat over `R'` when the
localization of `R''` at the prime below is flat over `R'`. -/
private theorem Module.Flat.localizedModule_tensor_of_flat_localization
    {R' R'' S S'' : Type*} [CommRing R'] [CommRing R''] [CommRing S] [CommRing S'']
    [Algebra R' R''] [Algebra R'' S''] [Algebra R' S''] [IsScalarTower R' R'' S'']
    [Algebra S S''] {M : Type*} [AddCommGroup M] [Module S M]
    (q'' : Ideal S'') [q''.IsPrime] (p'' : Ideal R'') [p''.IsPrime] [q''.LiesOver p'']
    [Module.Flat R' (Localization.AtPrime p'')]
    (h : Module.Flat R'' (LocalizedModule q''.primeCompl (S'' ⊗[S] M))) :
    Module.Flat R' (LocalizedModule q''.primeCompl (S'' ⊗[S] M)) := by
  let D := Localization.AtPrime q''
  let : Algebra (Localization.AtPrime p'') D :=
    Localization.AtPrime.algebraOfLiesOver p'' q''
  let : Module (Localization.AtPrime p'')
      (LocalizedModule q''.primeCompl (S'' ⊗[S] M)) :=
    Module.compHom _ (algebraMap (Localization.AtPrime p'') D)
  let : IsScalarTower R'' (Localization.AtPrime p'')
      (LocalizedModule q''.primeCompl (S'' ⊗[S] M)) :=
    IsScalarTower.of_algebraMap_smul fun r z => by
      change (algebraMap (Localization.AtPrime p'') D
        (algebraMap R'' (Localization.AtPrime p'') r)) • z = r • z
      rw [Localization.AtPrime.algebraMap_eq,
        Localization.localRingHom_to_map,
        ← IsScalarTower.algebraMap_apply R'' S'' D,
        IsScalarTower.algebraMap_smul D]
  let : IsScalarTower R' (Localization.AtPrime p'')
      (LocalizedModule q''.primeCompl (S'' ⊗[S] M)) :=
    IsScalarTower.of_algebraMap_smul fun r z => by
      change (algebraMap (Localization.AtPrime p'') D
        (algebraMap R' (Localization.AtPrime p'') r)) • z = r • z
      rw [IsScalarTower.algebraMap_apply R' R'' (Localization.AtPrime p''),
        Localization.AtPrime.algebraMap_eq,
        Localization.localRingHom_to_map]
      calc
        (algebraMap S'' D (algebraMap R'' S'' (algebraMap R' R'' r))) • z =
            (algebraMap R'' S'' (algebraMap R' R'' r)) • z :=
          IsScalarTower.algebraMap_smul D _ _
        _ = (algebraMap R' R'' r) • z := IsScalarTower.algebraMap_smul S'' _ _
        _ = r • z := IsScalarTower.algebraMap_smul R'' r z
  have : Module.Flat (Localization.AtPrime p'')
      (LocalizedModule q''.primeCompl (S'' ⊗[S] M)) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p'') p''.primeCompl
      (LocalizedModule q''.primeCompl (S'' ⊗[S] M))).mpr h
  exact Module.Flat.trans R' (Localization.AtPrime p'')
    (LocalizedModule q''.primeCompl (S'' ⊗[S] M))

/-- Flatness of a localized extension of scalars descends along a flat map of local rings
`(S')_q → (S'')_{q''}` from `S''` to `S'`. -/
private theorem Module.Flat.localizedModule_tensor_of_liesOver
    {R' S S' S'' : Type*} [CommRing R'] [CommRing S] [CommRing S'] [CommRing S'']
    [Algebra S S'] [Algebra S S''] [Algebra S' S''] [IsScalarTower S S' S'']
    [Algebra R' S'] [Algebra R' S''] [IsScalarTower R' S' S'']
    {M : Type*} [AddCommGroup M] [Module S M]
    (q : Ideal S') [q.IsPrime] (q'' : Ideal S'') [q''.IsPrime] [q''.LiesOver q]
    (hD : Module.Flat S' (Localization.AtPrime q''))
    (h : Module.Flat R' (LocalizedModule q''.primeCompl (S'' ⊗[S] M))) :
    Module.Flat R' (LocalizedModule q.primeCompl (S' ⊗[S] M)) := by
  let C := Localization.AtPrime q
  let D := Localization.AtPrime q''
  let : Algebra C D := Localization.AtPrime.algebraOfLiesOver q q''
  have : Module.Flat C D := (Module.flat_iff_of_isLocalization C q.primeCompl D).mpr hD
  have : Module.FaithfullyFlat C D := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let N' := S' ⊗[S] M
  let N'' := S'' ⊗[S] M
  let L' := LocalizedModule q.primeCompl N'
  let L'' := LocalizedModule q''.primeCompl N''
  let e₁ : C ⊗[S'] N' ≃ₗ[C] L' :=
    (LocalizedModule.isBaseChange q.primeCompl N').equiv
  let e₂ : D ⊗[S''] N'' ≃ₗ[D] L'' :=
    (LocalizedModule.isBaseChange q''.primeCompl N'').equiv
  let eBase : D ⊗[C] L' ≃ₗ[D] L'' :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl D D) e₁.symm) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S' C D D N') ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S S' D D M) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S S'' D D M).symm ≪≫ₗ e₂
  have : Module.Flat R' (D ⊗[C] L') := Module.Flat.of_linearEquiv (eBase.restrictScalars R')
  exact Module.Flat.of_tensorProduct_of_faithfullyFlat (A := R') (C := C) (D := D) (P := L')

/-- **Stacks Tag 05LS.** Flatness along the closed subsets determined by `I'` and `J` descends
from `R''` to `R'` when `V(I'') → V(I')` is surjective and the localizations of `R''` at primes
containing `I''` are flat over `R'`. -/
@[stacks 05LS]
lemma Module.IsFlatAtPrimesOver.of_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (J : Ideal S) {M : Type w} [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    {R' : Type x} {R'' : Type y} [CommRing R'] [CommRing R'']
    [Algebra R R'] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R'']
    (I' : Ideal R') (I'' : Ideal R'')
    (_hI : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hsurj : ∀ (p' : Ideal R'), p'.IsPrime → I' ≤ p' →
      ∃ p'' : Ideal R'', p''.IsPrime ∧ I'' ≤ p'' ∧
        Ideal.comap (algebraMap R' R'') p'' = p')
    (hflat : ∀ (p'' : Ideal R'') [p''.IsPrime], I'' ≤ p'' →
      Module.Flat R' (Localization p''.primeCompl))
    (h : Module.IsFlatAtPrimesOver (R := R) (M := M) J R'' I'') :
    Module.IsFlatAtPrimesOver (R := R) (M := M) J R' I' := by
  dsimp only [Module.IsFlatAtPrimesOver] at h ⊢
  intro q hq hqcontain
  let : q.IsPrime := hq
  let S' := S ⊗[R] R'
  let S'' := S ⊗[R] R''
  let f : S' →ₐ[R] S'' := Algebra.TensorProduct.map
    (AlgHom.id R S) (IsScalarTower.toAlgHom R R' R'')
  let : Algebra R' S' := Algebra.TensorProduct.rightAlgebra
  let : Algebra R'' S'' := Algebra.TensorProduct.rightAlgebra
  let : Algebra R' S'' := (algebraMap R'' S'').comp (algebraMap R' R'') |>.toAlgebra
  let : IsScalarTower R' R'' S'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra S' S'' := f.toRingHom.toAlgebra
  let : IsScalarTower R' S' S'' := IsScalarTower.of_algebraMap_eq fun a => by
    change f (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] algebraMap R' R'' a
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  let : IsScalarTower S S' S'' := IsScalarTower.of_algebraMap_eq fun a => by
    change a ⊗ₜ[R] 1 = f (a ⊗ₜ[R] 1)
    symm
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  let : Algebra.IsPushout R' S' R'' S'' :=
    ((Algebra.IsPushout.comp_iff R R' S S' (T := R'') (T' := S'')).mp inferInstance).symm
  let p' : Ideal R' := q.comap (algebraMap R' S')
  have hIp' : I' ≤ p' := fun a ha => hqcontain (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
  obtain ⟨q'', hq'', hqf, hIq''⟩ :=
    Stacks.Flatness.Stratification.exists_prime_pushout_of_closed_surjective
      (A := R') (B := S') (C := R'')
      (D := S'') q I'' (hsurj p' inferInstance hIp')
  let : q''.IsPrime := hq''
  have hq''contain :
      Ideal.map (Algebra.TensorProduct.includeRight
          (R := R) (A := S) (B := R'')).toRingHom I'' +
        Ideal.map (Algebra.TensorProduct.includeLeftRingHom
          (R := R) (A := S) (B := R'')) J ≤ q'' := by
    rw [Ideal.add_eq_sup]
    refine sup_le (Ideal.map_le_iff_le_comap.mpr hIq'')
      (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
    have hmem : a ∈ q.comap (algebraMap S S') :=
      hqcontain (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha))
    change algebraMap S S' a ∈ q at hmem
    rw [← hqf] at hmem
    change algebraMap S S'' a ∈ q''
    rwa [IsScalarTower.algebraMap_apply S S' S'']
  have hflatq'' := h q'' hq'' hq''contain
  let p'' : Ideal R'' := q''.comap (algebraMap R'' S'')
  let : p''.IsPrime := inferInstance
  have : Module.Flat R' (Localization.AtPrime p'') := hflat p'' hIq''
  let : Algebra.IsPushout R' R'' S' S'' := Algebra.IsPushout.symm inferInstance
  let : q''.LiesOver p'' := ⟨rfl⟩
  let : q''.LiesOver q := ⟨hqf.symm⟩
  exact Module.Flat.localizedModule_tensor_of_liesOver q q''
    (Module.Flat.localization_atPrime_of_isPushout (R' := R') (R'' := R'') q'')
    (Module.Flat.localizedModule_tensor_of_flat_localization q'' p'' hflatq'')

/-! ### Flatness from flatness modulo the powers of an ideal -/

/-- Modulo `I • M` for an ideal `I` of the base, an `S`-module is killed by `I`. -/
private theorem Module.isTorsionBySet_quotient_map_smul_top
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (A : Ideal R) :
    Module.IsTorsionBySet R (M ⧸ A.map (algebraMap R S) • (⊤ : Submodule S M)) (A : Set R) := by
  intro z r
  induction z using Quotient.inductionOn' with
  | _ m =>
    change (Submodule.Quotient.mk ((r : R) • m) :
      M ⧸ A.map (algebraMap R S) • (⊤ : Submodule S M)) = 0
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [← IsScalarTower.algebraMap_smul S (r : R) m]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem (algebraMap R S) r.2) Submodule.mem_top

/-- A localization of the quotient of an `S`-module by `I • M` is killed by `I`. -/
private theorem Module.isTorsionBySet_localizedModule_quotient_map_smul_top
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (P : Submonoid S) (A : Ideal R) :
    Module.IsTorsionBySet R
      (LocalizedModule P (M ⧸ A.map (algebraMap R S) • (⊤ : Submodule S M))) (A : Set R) := by
  intro z r
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective P
    (LocalizedModule.mkLinearMap P (M ⧸ A.map (algebraMap R S) • (⊤ : Submodule S M))) z
  change (r : R) • IsLocalizedModule.mk'
    (LocalizedModule.mkLinearMap P (M ⧸ A.map (algebraMap R S) • (⊤ : Submodule S M))) z s = 0
  rw [← IsLocalizedModule.mk'_smul, Module.isTorsionBySet_quotient_map_smul_top A]
  exact IsLocalizedModule.mk'_zero _ _

/-- If the localization at `q` of `M / IM` is flat over `R / I`, then so is the quotient of the
localization `M_q` by `I`. -/
private theorem Module.flat_quotient_smul_localizedModule_atPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (q : Ideal S) [q.IsPrime] (A : Ideal R)
    (hn : letI := (Module.isTorsionBySet_localizedModule_quotient_map_smul_top
        (M := M) q.primeCompl A).module
      Module.Flat (R ⧸ A)
        (LocalizedModule q.primeCompl (M ⧸ A.map (algebraMap R S) • (⊤ : Submodule S M)))) :
    Module.Flat (R ⧸ A) (LocalizedModule q.primeCompl M ⧸
      (A • (⊤ : Submodule R (LocalizedModule q.primeCompl M)))) := by
  let B := Localization.AtPrime q
  let N := LocalizedModule q.primeCompl M
  let f : M →ₗ[S] N := LocalizedModule.mkLinearMap q.primeCompl M
  let K := A.map (algebraMap R S) • (⊤ : Submodule S M)
  let := (Module.isTorsionBySet_localizedModule_quotient_map_smul_top
    (M := M) q.primeCompl A).module
  change Module.Flat (R ⧸ A) (LocalizedModule q.primeCompl (M ⧸ K)) at hn
  let _ : Algebra R B := Algebra.ofModule smul_mul_assoc mul_smul_comm
  let _ : Module B N := inferInstance
  let _ : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun r z => by
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
  let L := Submodule.localized' B q.primeCompl f K
  have heq : L.restrictScalars R = A • (⊤ : Submodule R N) := by
    have hloc : L =
        (A.map (algebraMap R S)).localized' B q.primeCompl (Algebra.linearMap S B) •
          (⊤ : Submodule B N) := by
      dsimp [L, K]
      have hsmul := Submodule.localized'_smul B q.primeCompl f
        (⊤ : Submodule S M) (A.map (algebraMap R S))
      rwa [Submodule.localized'_top] at hsmul
    rw [hloc]
    change (((A.map (algebraMap R S)).localized' B q.primeCompl
        (Algebra.linearMap S B) • (⊤ : Submodule B N)).restrictScalars S).restrictScalars R = _
    rw [Submodule.restrictScalars_localized'_smul,
      Ideal.smul_restrictScalars, Submodule.restrictScalars_top,
      Submodule.restrictScalars_top]
  let := hn
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      ((Submodule.quotEquivOfEq _ _ heq).symm.trans
        ((Submodule.Quotient.restrictScalarsEquiv R L).trans
          ((localizedQuotientEquiv q.primeCompl K).restrictScalars R))))

/-- **Stacks Tag 05LU.** Let `R → S` be a map of Noetherian rings, let `J ⊆ S` and `I ⊆ R` be
ideals, and let `M` be a finite `S`-module. If, at every prime `q` containing `J + IS`, the
localization `(M / IⁿM)_q` is flat over `R / Iⁿ` for every `n ≥ 1`, then `M_q` is flat over `R`
at every such prime. -/
@[stacks 05LU]
theorem Module.flat_localizedModule_atPrime_of_flat_quotient_pow
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] (J : Ideal S) (I : Ideal R)
    (hflat : ∀ (n : ℕ) (q : Ideal S) (_ : q.IsPrime),
      J + I.map (algebraMap R S) ≤ q →
        let K := (I ^ (n + 1)).map (algebraMap R S) • (⊤ : Submodule S M)
        let Q := M ⧸ K
        let hQ : Module.IsTorsionBySet R Q ((I ^ (n + 1) : Ideal R) : Set R) := by
          intro z r
          induction z using Quotient.inductionOn' with
          | _ m =>
            change (Submodule.Quotient.mk ((r : R) • m) : M ⧸ K) = 0
            exact (Submodule.Quotient.mk_eq_zero K).mpr
              (show (r : R) • m ∈ K by
                rw [← IsScalarTower.algebraMap_smul S (r : R) m]
                exact Submodule.smul_mem_smul
                  (Ideal.mem_map_of_mem (algebraMap R S) r.2) Submodule.mem_top)
        let N := LocalizedModule q.primeCompl Q
        let hN : Module.IsTorsionBySet R N ((I ^ (n + 1) : Ideal R) : Set R) := by
          intro z r
          obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective q.primeCompl
            (LocalizedModule.mkLinearMap q.primeCompl Q) z
          change (r : R) • IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap q.primeCompl Q) z s = 0
          rw [← IsLocalizedModule.mk'_smul, hQ]
          exact IsLocalizedModule.mk'_zero _ _
        letI := hN.module
        Module.Flat (R ⧸ I ^ (n + 1)) N) :
    ∀ (q : Ideal S) (_ : q.IsPrime), J + I.map (algebraMap R S) ≤ q →
      Module.Flat R (LocalizedModule q.primeCompl M) := by
  intro q hq hJq
  let : q.IsPrime := hq
  let B := Localization.AtPrime q
  let N := LocalizedModule q.primeCompl M
  let f : M →ₗ[S] N := LocalizedModule.mkLinearMap q.primeCompl M
  have hp (n : ℕ) :
      Module.Flat (R ⧸ I ^ (n + 1))
        (N ⧸ (I ^ (n + 1) • (⊤ : Submodule R N))) :=
    Module.flat_quotient_smul_localizedModule_atPrime q (I ^ (n + 1)) (hflat n q hq hJq)
  let _ : Algebra R B := Algebra.ofModule smul_mul_assoc mul_smul_comm
  let _ : Module B N := inferInstance
  let _ : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun r z => by
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
  let p := IsLocalRing.maximalIdeal B
  let : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  have hIp : I.map (algebraMap R B) ≤ p := by
    have halg : algebraMap R B = (algebraMap S B).comp (algebraMap R S) := by
      ext r
      rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul S r (1 : B),
        Algebra.smul_def, mul_one]
      rfl
    rw [halg, ← Ideal.map_map]
    dsimp [p, B]
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono (le_sup_right.trans hJq)
  let : IsLocalizedModule.AtPrime p (LinearMap.id : N →ₗ[B] N) :=
    { map_units := fun s => by
        have hs : IsUnit (s : B) := by
          by_contra hs
          exact s.2 ((IsLocalRing.mem_maximalIdeal (s : B)).2 (mem_nonunits_iff.mpr hs))
        exact hs.map _
      surj := fun z => ⟨(z, 1), one_smul B z⟩
      exists_of_eq := fun h => ⟨1, by simpa using h⟩ }
  exact Module.Flat.of_flat_quotient_pow I N hp p hIp N LinearMap.id

/-! ### Descent of the flatness condition from a filtered colimit -/

/-- A compact closed subset of a spectrum whose image lies in an open relative flat locus is
covered by the inverse images of finitely many flat principal opens.

The closed subset is `V(J)` for an ideal `J` of a second ring `B`, and it is carried to
`Spec A` along a ring map `f : A →+* B`; the conclusion is a finite set `G ⊆ A` of elements
whose localizations of `N` are flat over `R` and whose images generate the unit ideal
together with `J`. -/
private theorem exists_finset_away_flat_of_isOpen_comap
    {R A B N : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (f : A →+* B) (J : Ideal B)
    (hopen : IsOpen {p : PrimeSpectrum A |
      Module.Flat R (LocalizedModule.AtPrime p.asIdeal N)})
    (hflat : ∀ q : PrimeSpectrum B, J ≤ q.asIdeal →
      Module.Flat R (LocalizedModule.AtPrime (q.asIdeal.comap f) N)) :
    ∃ G : Finset A, J ⊔ Ideal.map f (Ideal.span (G : Set A)) = ⊤ ∧
      ∀ g ∈ G, Module.Flat R (LocalizedModule.Away g N) := by
  classical
  let V := PrimeSpectrum.zeroLocus (J : Set B)
  have hV : IsCompact V := (PrimeSpectrum.isClosed_zeroLocus (J : Set B)).isCompact
  have hlocal : ∀ q : V, ∃ g : A,
      PrimeSpectrum.comap f q.1 ∈ PrimeSpectrum.basicOpen g ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
        {p | Module.Flat R (LocalizedModule.AtPrime p.asIdeal N)} := by
    intro q
    obtain ⟨_, ⟨g, rfl⟩, hqg, hg⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hopen
        (PrimeSpectrum.comap f q.1) (hflat q.1 ((PrimeSpectrum.mem_zeroLocus q.1 J).mp q.2))
    exact ⟨g, hqg, hg⟩
  choose g hgmem hgsub using hlocal
  obtain ⟨T, hT⟩ := hV.elim_finite_subcover
    (fun q : V => (PrimeSpectrum.comap f) ⁻¹' (PrimeSpectrum.basicOpen (g q)))
    (fun _ => PrimeSpectrum.isOpen_basicOpen.preimage (PrimeSpectrum.continuous_comap f))
    (fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hgmem ⟨q, hq⟩⟩)
  refine ⟨T.image g, ?_, ?_⟩
  · refine PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
      (Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_)
    have hle : J ⊔ Ideal.map f (Ideal.span (T.image g : Set A)) ≤ q.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus q _).mp hq
    have hqV : q ∈ V := (PrimeSpectrum.mem_zeroLocus q J).mpr
      (show J ≤ q.asIdeal from le_sup_left.trans hle)
    obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.mp (hT hqV)
    exact hqi ((le_sup_right.trans hle : Ideal.map f (Ideal.span (T.image g : Set A)) ≤
      q.asIdeal) (Ideal.mem_map_of_mem f (Ideal.subset_span
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩))))
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Stacks.Flatness.OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime (g i)
      (fun p hp => hgsub i hp)

/-- Finitely many elements of an elementwise directed colimit have representatives at a common
stage. -/
private theorem exists_rep_common_stage
    {R : Type*} [CommRing R] {Λ : Type*} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ) {E : Type*} [Finite E] (z : E → L) :
    ∃ i, ∃ y : E → A i, ∀ e, ρ i (y e) = z e := by
  classical
  let := Fintype.ofFinite E
  choose i y hy using fun e => hc.jointly_surjective (z e)
  obtain ⟨j, hj⟩ := (Finset.univ.image i).exists_le
  have hij e : i e ≤ j := hj (i e) (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩)
  exact ⟨j, fun e => f (hij e) (y e), fun e => (hc.comp (hij e) (y e)).trans (hy e)⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Reading the flatness condition of `Module.IsFlatAtPrimesOver` one layer down a
localization.** The flatness condition at a prime `q` of `S ⊗[R] A` is flatness of the
corresponding module over `C ⊗[R] A` at the contraction of `q`, when `S` is a localization of `C`
at a submonoid `U` and `M` is the base change of `N` along `C → S`.

This is the analytic half of the translation between the vocabulary of Stacks Tag 05ML, whose
algebra is *local*, and the vocabulary of a complete dévissage, whose stage algebras are not: the
local algebra of Stacks Tag 05ML is a localization `C_{q₁}` of a dévissage stage algebra `C`, so
`C_{q₁} ⊗[R] A` is a localization of `C ⊗[R] A` and the primes tested by the condition are the
primes of `C ⊗[R] A` contracting into `q₁`. The combinatorial half — which primes those are — is
`Module.FlatAtPointSituation.conditionOn_iff_forall_prime_comap`. -/
theorem Module.flat_localizedModule_atPrime_comap_tensor_iff
    {R C S A N M : Type*} [CommRing R] [CommRing C] [CommRing S] [CommRing A]
    [Algebra R C] [Algebra R S] [Algebra R A] [Algebra C S] [IsScalarTower R C S]
    [AddCommGroup N] [Module C N]
    [AddCommGroup M] [Module C M] [Module S M] [IsScalarTower C S M]
    (U : Submonoid C) [IsLocalization U S]
    (g : N →ₗ[C] M) (hg : IsBaseChange S g)
    (q : Ideal (S ⊗[R] A)) [q.IsPrime] :
    letI : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra A (C ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
    Module.Flat A (LocalizedModule.AtPrime q ((S ⊗[R] A) ⊗[S] M)) ↔
      Module.Flat A (LocalizedModule.AtPrime
        (q.comap (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C S)
          (AlgHom.id R A)).toRingHom) ((C ⊗[R] A) ⊗[C] N)) := by
  let B := S ⊗[R] A
  let D := C ⊗[R] A
  let : Algebra A B := Algebra.TensorProduct.rightAlgebra
  let : Algebra A D := Algebra.TensorProduct.rightAlgebra
  let τ : D →ₐ[R] B := Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C S)
    (AlgHom.id R A)
  let : Algebra D B := τ.toRingHom.toAlgebra
  have : IsScalarTower C D B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R D B := IsScalarTower.of_algHom τ
  have hτ (a : A) : τ ((1 : C) ⊗ₜ[R] a) = (1 : S) ⊗ₜ[R] a := by
    simpa only [map_one, AlgHom.id_apply] using
      (Algebra.TensorProduct.map_tmul (IsScalarTower.toAlgHom R C S)
        (AlgHom.id R A) (1 : C) a)
  have : IsScalarTower A D B := IsScalarTower.of_algebraMap_eq fun a => (hτ a).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid D U) B :=
    IsLocalization.tensorProduct_tensorProduct R A U S (by ext a; exact hτ a)
  let e : B ⊗[D] (D ⊗[C] N) ≃ₗ[B] B ⊗[S] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange C D B B N).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange C S B B N).symm.trans
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) hg.equiv))
  let fLoc := (LocalizedModule.mkLinearMap q.primeCompl (B ⊗[S] M)) ∘ₗ e.toLinearMap
  have : IsLocalizedModule q.primeCompl fLoc :=
    IsLocalizedModule.of_linearEquiv_right q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl (B ⊗[S] M)) e
  let eLoc := IsLocalizedModule.linearEquiv q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl (B ⊗[D] (D ⊗[C] N))) fLoc
  exact (Module.Flat.equiv_iff (eLoc.restrictScalars A)).symm.trans
    (Module.flat_localizedModule_atPrime_comap_iff (R := A) (N := D ⊗[C] N)
      (Algebra.algebraMapSubmonoid D U) q).symm

/-- The image of the ideal spanned by a family indexed by a finite set `G` equals the image of
the ideal spanned by `G`, when the two maps agree along the family. -/
private theorem Ideal.map_span_range_eq_map_span_finset
    {X Y Z : Type*} [CommRing X] [CommRing Y] [CommRing Z]
    (φ : X →+* Z) (ψ : Y →+* Z) (G : Finset Y) (v : G → X) (h : ∀ a, ψ a.1 = φ (v a)) :
    Ideal.map φ (Ideal.span (Set.range v)) = Ideal.map ψ (Ideal.span (G : Set Y)) := by
  rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp']
  congr 1
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, a.2, h a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, (h ⟨a, ha⟩).symm⟩

/-- If `J` and the image of the ideal spanned by a family generate the unit ideal, then some
member of the family maps outside any prime containing `J`. -/
private theorem Ideal.exists_apply_notMem_of_sup_map_span_eq_top
    {X Z ι : Type*} [CommRing X] [CommRing Z] (φ : X →+* Z) (v : ι → X) {J q : Ideal Z}
    (hq : q.IsPrime) (h : J ⊔ Ideal.map φ (Ideal.span (Set.range v)) = ⊤) (hJ : J ≤ q) :
    ∃ a, φ (v a) ∉ q := by
  by_contra! h'
  have hK : Ideal.map φ (Ideal.span (Set.range v)) ≤ q := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact h' a
  exact hq.ne_top (top_unique (h ▸ sup_le hJ hK))

set_option backward.isDefEq.respectTransparency false in
/-- Flatness on the contracted primes of a compatible closed subset descends to one stage of an
elementwise directed colimit, for a finitely presented algebra `C` and a finitely presented
`C`-module `N`. -/
@[ega "IV 11.2.6.1" "partial"]
private theorem exists_stage_flat_localizedModule_atPrime_comap
    {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C]
    (N : Type*) [AddCommGroup N] [Module C N] [Module.FinitePresentation C N]
    {Λ : Type*} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ)
    {B : Λ → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    {b : ∀ ⦃i j⦄, i ≤ j → B i →ₐ[R] B j}
    {T : Type*} [CommRing T] [Algebra R T] {σ : ∀ i, B i →ₐ[R] T}
    (hB : IsDirectedColimit B b T σ)
    (τ : ∀ i, (C ⊗[R] A i) →ₐ[R] B i) (τ' : (C ⊗[R] L) →ₐ[R] T)
    (hτ : ∀ ⦃i j⦄ (h : i ≤ j) z,
      b h (τ i z) = τ j (Algebra.TensorProduct.map (AlgHom.id R C) (f h) z))
    (hτ' : ∀ i z, σ i (τ i z) =
      τ' (Algebra.TensorProduct.map (AlgHom.id R C) (ρ i) z))
    (J : ∀ i, Ideal (B i))
    (hJ : ∀ ⦃i j⦄ (h : i ≤ j), Ideal.map (b h).toRingHom (J i) ≤ J j)
    (hflat : letI : Algebra L (C ⊗[R] L) := Algebra.TensorProduct.rightAlgebra
      ∀ q : PrimeSpectrum T, (⨆ i, Ideal.map (σ i).toRingHom (J i)) ≤ q.asIdeal →
        Module.Flat L (LocalizedModule.AtPrime (q.asIdeal.comap τ'.toRingHom)
          ((C ⊗[R] L) ⊗[C] N))) :
    ∃ i, letI : Algebra (A i) (C ⊗[R] A i) := Algebra.TensorProduct.rightAlgebra
      ∀ q : PrimeSpectrum (B i), J i ≤ q.asIdeal →
        Module.Flat (A i) (LocalizedModule.AtPrime (q.asIdeal.comap (τ i).toRingHom)
          ((C ⊗[R] A i) ⊗[C] N)) := by
  classical
  let : Algebra L (C ⊗[R] L) := Algebra.TensorProduct.rightAlgebra
  let : ∀ i, Algebra (A i) (C ⊗[R] A i) := fun _ => Algebra.TensorProduct.rightAlgebra
  have : Algebra.FinitePresentation L (C ⊗[R] L) :=
    Algebra.FinitePresentation.tensorProduct_right
  obtain ⟨G, hcover, hGflat⟩ := exists_finset_away_flat_of_isOpen_comap τ'.toRingHom
    (⨆ i, Ideal.map (σ i).toRingHom (J i))
    (Module.isOpen_setOf_flat_localizedModule_atPrime (R := L)
      (S := C ⊗[R] L) (M := (C ⊗[R] L) ⊗[C] N)) hflat
  obtain ⟨i₀, y, hy⟩ := exists_rep_common_stage (hc.tensorLeft C) (fun a : G => a.1)
  let K : Ideal (B i₀) := Ideal.span (Set.range (fun a => τ i₀ (y a)))
  have hmap : Ideal.map (σ i₀).toRingHom K =
      Ideal.map τ'.toRingHom (Ideal.span (G : Set (C ⊗[R] L))) :=
    Ideal.map_span_range_eq_map_span_finset _ _ G (fun a => τ i₀ (y a)) fun a => by
      change τ' a.1 = σ i₀ (τ i₀ (y a))
      rw [hτ', hy]
  obtain ⟨j, hij, hjcover⟩ := Ideal.exists_ge_sup_map_eq_top hB J hJ i₀ K
    (by rwa [hmap])
  have hdesc : ∀ a : G, ∃ k, ∃ hik : i₀ ≤ k, ∀ l (hkl : k ≤ l),
      Module.Flat (A l) (LocalizedModule.Away
        (Algebra.TensorProduct.map (AlgHom.id R C) (f (hik.trans hkl)) (y a))
        ((C ⊗[R] A l) ⊗[C] N)) := fun a => by
    apply Module.Flat.exists_ge_flat_localizationAway_tensorProduct N hc i₀ (y a)
    change Module.Flat L (LocalizedModule.Away
      (Algebra.TensorProduct.map (AlgHom.id R C) (ρ i₀) (y a))
        ((C ⊗[R] L) ⊗[C] N))
    rw [hy]
    exact hGflat a.1 a.2
  choose k hik hk using hdesc
  obtain ⟨l, hl⟩ := (insert j (Finset.univ.image k)).exists_le
  have hjl : j ≤ l := hl j (Finset.mem_insert_self _ _)
  have hi₀l : i₀ ≤ l := hij.trans hjl
  refine ⟨l, fun q hq => ?_⟩
  have hm := congrArg (Ideal.map (b hjl).toRingHom) hjcover
  rw [Ideal.map_sup, Ideal.map_top, Ideal.map_map, show (b hjl).toRingHom.comp (b hij).toRingHom =
    (b hi₀l).toRingHom from RingHom.ext (hB.map_comp hij hjl)] at hm
  have hcoverl : J l ⊔ Ideal.map (b hi₀l).toRingHom K = ⊤ :=
    top_unique (hm ▸ sup_le_sup (hJ hjl) le_rfl)
  obtain ⟨a, ha⟩ := Ideal.exists_apply_notMem_of_sup_map_span_eq_top (b hi₀l).toRingHom
    (fun a => τ i₀ (y a)) q.isPrime hcoverl hq
  replace ha : Algebra.TensorProduct.map (AlgHom.id R C) (f hi₀l) (y a) ∉
      q.asIdeal.comap (τ l).toRingHom := by
    change b hi₀l (τ i₀ (y a)) ∉ q.asIdeal at ha
    rwa [hτ] at ha
  have : Module.Flat (A l) (LocalizedModule.Away
      (Algebra.TensorProduct.map (AlgHom.id R C) (f hi₀l) (y a))
      ((C ⊗[R] A l) ⊗[C] N)) :=
    hk a l (hl (k a) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)))
  exact Module.Flat.localizedModule_atPrime_of_away _ _ ha

/-- Base changing along `C → S` on the left commutes with a map `A → A'` on the right. -/
private theorem Algebra.TensorProduct.map_id_map_toAlgHom_comm
    {R C S A A' : Type*} [CommRing R] [CommRing C] [CommRing S] [CommRing A] [CommRing A']
    [Algebra R C] [Algebra R S] [Algebra R A] [Algebra R A']
    (φ : C →ₐ[R] S) (g : A →ₐ[R] A') (z : C ⊗[R] A) :
    Algebra.TensorProduct.map (AlgHom.id R S) g (Algebra.TensorProduct.map φ (AlgHom.id R A) z) =
      Algebra.TensorProduct.map φ (AlgHom.id R A')
        (Algebra.TensorProduct.map (AlgHom.id R C) g z) := by
  induction z with
  | add z y hz hy => simp only [map_add, hz, hy]
  | tmul c a => simp

/-- Mapping `S ⊗[R] A` to `S ⊗[R] A'` along `A → A'` is compatible with the inclusions of `S`. -/
private theorem map_id_comp_includeLeftRingHom
    {R S A A' : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing A']
    [Algebra R S] [Algebra R A] [Algebra R A'] (g : A →ₐ[R] A') :
    (Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom.comp
        Algebra.TensorProduct.includeLeftRingHom =
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] A') := by
  ext s
  simp

/-- The ideal generated by `I` and `J` in `S ⊗[R] A` maps into the one generated by `I'` and `J`
in `S ⊗[R] A'` along a map `A → A'` carrying `I` into `I'`. -/
private theorem Ideal.map_tensorProduct_map_sup_le
    {R : Type*} {S : Type v} {A A' : Type w} [CommRing R] [CommRing S] [CommRing A]
    [CommRing A'] [Algebra R S] [Algebra R A] [Algebra R A']
    (g : A →ₐ[R] A') (J : Ideal S) {I : Ideal A} {I' : Ideal A'}
    (h : Ideal.map g.toRingHom I ≤ I') :
    Ideal.map (Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom
        (Ideal.map Algebra.TensorProduct.includeRight.toRingHom I ⊔
          Ideal.map (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] A) J) ≤
      Ideal.map Algebra.TensorProduct.includeRight.toRingHom I' ⊔
        Ideal.map (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] A') J := by
  rw [Ideal.map_sup]
  apply sup_le_sup (Ideal.map_includeRight_le_of_map_le g I I' h)
  rw [Ideal.map_map, map_id_comp_includeLeftRingHom]

/-- The supremum over a cocone of the ideals generated by `I i` and `J` in `S ⊗[R] A i` is the
ideal generated by the supremum of the images of the `I i` and by `J`. -/
private theorem Ideal.iSup_map_tensorProduct_map_sup
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {Λ : Type*} [Nonempty Λ] {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {L : Type*} [CommRing L] [Algebra R L] (ρ : ∀ i, A i →ₐ[R] L)
    (I : ∀ i, Ideal (A i)) (J : Ideal S) :
    (⨆ i, Ideal.map (Algebra.TensorProduct.map (AlgHom.id R S) (ρ i)).toRingHom
        (Ideal.map Algebra.TensorProduct.includeRight.toRingHom (I i) ⊔
          Ideal.map (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] A i) J)) =
      Ideal.map Algebra.TensorProduct.includeRight.toRingHom
          (⨆ i, Ideal.map (ρ i).toRingHom (I i)) ⊔
        Ideal.map (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] L) J := by
  simp only [Ideal.map_sup, iSup_sup_eq]
  rw [← Ideal.map_includeRight_iSup_map (S := S) ρ I]
  congr 1
  simp only [Ideal.map_map, map_id_comp_includeLeftRingHom, iSup_const]

set_option backward.isDefEq.respectTransparency false in
/-- The flatness condition over an elementwise directed colimit of `R`-algebras is already
witnessed at one stage, for a source algebra `R → S` which is essentially of finite
presentation. -/
private theorem exists_isFlatAtPrimesOver_of_isDirectedColimit
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FinitePresentation S M] (J : Ideal S)
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    {Λ : Type*} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ)
    (I : ∀ i, Ideal (A i))
    (hI : ∀ ⦃i j⦄ (h : i ≤ j), Ideal.map (f h).toRingHom (I i) ≤ I j)
    (hflat : Module.IsFlatAtPrimesOver (R := R) (M := M) J L
      (⨆ i, Ideal.map (ρ i).toRingHom (I i))) :
    ∃ i, Module.IsFlatAtPrimesOver (R := R) (M := M) J (A i) (I i) := by
  obtain ⟨C, hC, hRC, hCS, hRCS, hfpC, U, hU⟩ := hS
  let : CommRing C := hC
  let : Algebra R C := hRC
  let : Algebra C S := hCS
  have hAlg : (algebraMap R S).toAlgebra = (inferInstance : Algebra R S) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [hAlg] at hRCS
  have : IsScalarTower R C S := hRCS
  have : Algebra.FinitePresentation R C := hfpC
  have : IsLocalization U S := hU
  let : Module C M := Module.compHom M (algebraMap C S)
  have : IsScalarTower C S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨N, hN, hCN, g, _, hg, hfpN⟩ :=
    Module.exists_finite_isBaseChange_of_surjective_algebraMap U S M
      (Function.surjective_id : Function.Surjective (algebraMap S S))
  let : AddCommGroup N := hN
  let : Module C N := hCN
  have : Module.FinitePresentation C N := hfpN inferInstance
  let b : ∀ ⦃i j⦄, i ≤ j → (S ⊗[R] A i) →ₐ[R] (S ⊗[R] A j) :=
    fun {_ _} h => Algebra.TensorProduct.map (AlgHom.id R S) (f h)
  let σ : ∀ i, (S ⊗[R] A i) →ₐ[R] (S ⊗[R] L) :=
    fun i => Algebra.TensorProduct.map (AlgHom.id R S) (ρ i)
  let τ : ∀ i, (C ⊗[R] A i) →ₐ[R] (S ⊗[R] A i) :=
    fun i => Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C S) (AlgHom.id R (A i))
  let τ' : (C ⊗[R] L) →ₐ[R] (S ⊗[R] L) :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C S) (AlgHom.id R L)
  let K : ∀ i, Ideal (S ⊗[R] A i) := fun i =>
    Ideal.map Algebra.TensorProduct.includeRight.toRingHom (I i) ⊔
      Ideal.map Algebra.TensorProduct.includeLeftRingHom J
  have hK : ∀ ⦃i j⦄ (h : i ≤ j), Ideal.map (b h).toRingHom (K i) ≤ K j :=
    fun _ _ h => Ideal.map_tensorProduct_map_sup_le (f h) J (hI h)
  obtain ⟨i, hi⟩ := exists_stage_flat_localizedModule_atPrime_comap N hc
    (IsDirectedColimit.tensorLeft hc S)
    τ τ' (fun {_ _} h z => Algebra.TensorProduct.map_id_map_toAlgHom_comm _ (f h) z)
    (fun i z => Algebra.TensorProduct.map_id_map_toAlgHom_comm _ (ρ i) z)
    K hK (by
      let : Algebra L (S ⊗[R] L) := Algebra.TensorProduct.rightAlgebra
      intro q hq
      apply (Module.flat_localizedModule_atPrime_comap_tensor_iff (R := R) U g hg q.asIdeal).mp
      apply hflat q.asIdeal q.isPrime
      change (⨆ i, Ideal.map (σ i).toRingHom (K i)) ≤ q.asIdeal at hq
      rw [show (⨆ i, Ideal.map (σ i).toRingHom (K i)) = _ from
        Ideal.iSup_map_tensorProduct_map_sup ρ I J] at hq
      simpa only [Ideal.add_eq_sup] using hq)
  refine ⟨i, ?_⟩
  let : Algebra (A i) (S ⊗[R] A i) := Algebra.TensorProduct.rightAlgebra
  intro q hq hIq
  exact (Module.flat_localizedModule_atPrime_comap_tensor_iff (R := R) U g hg q).mpr
    (hi ⟨q, hq⟩ hIq)

open CategoryTheory CategoryTheory.Limits

/-- Compatibility of a family of stage ideals makes the images of those ideals in the apex of a
cocone monotone along every transition map. -/
private theorem ideal_map_cocone_ι_le
    {R : Type u} [CommRing R] {Lambda : Type y} [Category.{z} Lambda]
    (F : Lambda ⥤ CommAlgCat.{x} R) (c : Cocone F)
    (I : (lambda : Lambda) → Ideal (F.obj lambda))
    (hI : ∀ {lambda mu : Lambda} (f : lambda ⟶ mu),
      Ideal.map (F.map f).hom.toRingHom (I lambda) ≤ I mu)
    {lambda mu : Lambda} (f : lambda ⟶ mu) :
    Ideal.map (c.ι.app lambda).hom.toRingHom (I lambda) ≤
      (Ideal.map (c.ι.app mu).hom.toRingHom (I mu) : Ideal c.pt) := by
  have hw : (c.ι.app lambda).hom.toRingHom =
      (c.ι.app mu).hom.toRingHom.comp (F.map f).hom.toRingHom :=
    RingHom.ext fun a => congrArg (fun k : F.obj lambda ⟶ c.pt => k a) (c.w f).symm
  rw [hw, ← Ideal.map_map]
  exact Ideal.map_mono (f := (c.ι.app mu).hom.toRingHom) (hI f)

/-- A cocone of `R`-algebras over a directed preorder whose image under the forgetful functor to
types is a colimit carries the elementwise universal property of a directed colimit. -/
private theorem isDirectedColimit_of_isColimit_mapCocone
    {R : Type*} [CommRing R] {Λ : Type*} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    (F : Λ ⥤ CommAlgCat.{u} R) (c : Cocone F)
    (hc : IsColimit ((forget (CommAlgCat.{u} R)).mapCocone c)) :
    @IsDirectedColimit R _ Λ _ (fun i => F.obj i)
      (fun i => (F.obj i).commRing) (fun i => (F.obj i).algebra)
      (fun {_ _} h => (F.map (homOfLE h)).hom) (c.pt : Type u)
      c.pt.commRing c.pt.algebra (fun i => (c.ι.app i).hom) := by
  refine ⟨fun i j k hij hjk z =>
      (ConcreteCategory.congr_hom (F.map_comp (homOfLE hij) (homOfLE hjk)) z).symm,
    fun i z => ConcreteCategory.congr_hom (F.map_id i) z,
    fun i j hij z => ConcreteCategory.congr_hom (c.w (homOfLE hij)) z,
    fun z => Types.jointly_surjective_of_isColimit hc z, fun i z hz => ?_⟩
  have he : ((forget (CommAlgCat.{u} R)).mapCocone c).ι.app i z =
      ((forget (CommAlgCat.{u} R)).mapCocone c).ι.app i (0 : F.obj i) := by
    simpa using hz
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc z (0 : F.obj i)).mp he
  refine ⟨j, leOfHom f, ?_⟩
  rw [show homOfLE (leOfHom f) = f from Subsingleton.elim _ _]
  change (F.map f).hom z = (F.map f).hom 0 at hf
  simpa only [map_zero] using hf

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks Tag 05LT.** Let `R → S` be essentially of finite presentation, let `J ⊆ S` be an
ideal and let `M` be a finitely presented `S`-module. Let `F` be a filtered system of
`R`-algebras whose colimit cocone `c` is preserved by the forgetful functor to types, and let
`I lambda ⊆ F.obj lambda` be a compatible family of ideals. If the flatness condition
`Module.IsFlatAtPrimesOver` holds over the colimit `c.pt` and the supremum of the images of the
`I lambda`, then it already holds at some stage `lambda`.

Preservation of the colimit by the forgetful functor expresses the source's directed colimit of
rings elementwise: every element and every finite equation in `c.pt` comes from a stage. It is
required explicitly because the index universes and the ring universe are independent. -/
@[stacks 05LT]
theorem Module.exists_isFlatAtPrimesOver_of_isColimit
    {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FinitePresentation S M] (J : Ideal S)
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    {Lambda : Type y} [Category.{z} Lambda] [IsFiltered Lambda]
    (F : Lambda ⥤ CommAlgCat.{x} R) [PreservesColimit F (forget (CommAlgCat.{x} R))]
    (c : Cocone F) (hc : IsColimit c)
    (I : (lambda : Lambda) → Ideal (F.obj lambda))
    (hI : ∀ {lambda mu : Lambda} (f : lambda ⟶ mu),
      Ideal.map (F.map f).hom.toRingHom (I lambda) ≤ I mu)
    (hflat : Module.IsFlatAtPrimesOver (R := R) (S := S) (M := M) J (c.pt : Type x)
      (⨆ lambda, Ideal.map (c.ι.app lambda).hom.toRingHom (I lambda))) :
    ∃ lambda, Module.IsFlatAtPrimesOver (R := R) (S := S) (M := M) J
      (F.obj lambda) (I lambda) := by
  classical
  have : IsFiltered (AsSmall.{0} Lambda) := IsFiltered.of_equivalence AsSmall.equiv
  obtain ⟨α, hα, hd, hn, H₀, hH₀⟩ := IsFiltered.exists_directed (AsSmall.{0} Lambda)
  let H : α ⥤ Lambda := H₀ ⋙ (AsSmall.equiv : Lambda ≌ AsSmall.{0} Lambda).inverse
  have : H.Final := inferInstance
  have hcH : IsColimit ((forget (CommAlgCat.{x} R)).mapCocone (c.whisker H)) :=
    (Functor.Final.isColimitWhiskerEquiv H
      ((forget (CommAlgCat.{x} R)).mapCocone c)).symm (isColimitOfPreserves _ hc)
  have hdir := isDirectedColimit_of_isColimit_mapCocone (H ⋙ F) (c.whisker H) hcH
  have he : (⨆ a, Ideal.map (c.ι.app (H.obj a)).hom.toRingHom
      (I (H.obj a)) : Ideal (c.pt : Type x)) =
      (⨆ i, Ideal.map (c.ι.app i).hom.toRingHom (I i) : Ideal c.pt) := by
    apply le_antisymm
    · exact iSup_le fun a => le_iSup (fun i =>
        (Ideal.map (c.ι.app i).hom.toRingHom (I i) : Ideal (c.pt : Type x))) (H.obj a)
    · refine iSup_le fun i => le_iSup_of_le (Functor.Final.lift H i) ?_
      exact ideal_map_cocone_ι_le F c I hI (Functor.Final.homToLift H i)
  obtain ⟨a, ha⟩ := exists_isFlatAtPrimesOver_of_isDirectedColimit
    (M := M) J hS hdir (fun a => I (H.obj a))
    (fun {_ _} h => hI (H.map (homOfLE h))) (by
      change Module.IsFlatAtPrimesOver (R := R) (M := M) J (c.pt : Type x)
        (⨆ a, Ideal.map (c.ι.app (H.obj a)).hom.toRingHom (I (H.obj a)))
      rwa [he])
  exact ⟨H.obj a, ha⟩
