module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Syntomic morphisms

This file defines *global complete intersection over a field*, *local complete
intersection over a field*, and *syntomic ring map* (equivalently, *flat local complete
intersection*), and proves that being syntomic is local on the source: if a ring `S` is
covered by basic opens `D(g_i)` (i.e. the `g_i` generate the unit ideal of `S`) and each
composite `R → S_{g_i}` is syntomic, then `R → S` is syntomic.

Throughout, all rings are commutative with unit and all ring maps are unital ring
homomorphisms. For a ring map `R → S` we regard `S` as an `R`-algebra. For a prime `p`
of `R`, `κ(p)` denotes the residue field of `R` at `p`, realized here as
`IsLocalRing.ResidueField (Localization.AtPrime p)`. For `f ∈ S`, `S_f` denotes the
localization away from `f`, realized as `Localization.Away f`.

## Main definitions

* `IsGlobalCompleteIntersectionOver`
* `IsLocalCompleteIntersectionOver`
* `IsSyntomic`

## Main results

* `isSyntomic_of_isSyntomic_localization_away`: being syntomic is local on the source.
-/

@[expose] public section

/-- Let `k` be a field and `S` a finite-type `k`-algebra. `S` is a *global complete
intersection over `k`* if there are `n c : ℕ`, a surjective `k`-algebra homomorphism
`π : k[x_1, …, x_n] ↠ S`, and elements `f_1, …, f_c ∈ k[x_1, …, x_n]` with
`ker π = (f_1, …, f_c)` and `dim S = n − c`. By convention the zero ring is a global
complete intersection over every field `k`; this is what the `Subsingleton S` disjunct
records.

The Krull dimension `dim S` lives in `WithBot ℕ∞`, where truncated subtraction is
ill-behaved, so the condition `dim S = n − c` is written in the equivalent additive form
`ringKrullDim S + c = n` (which, in the relevant finite case, also encodes `c ≤ n`). -/
noncomputable def IsGlobalCompleteIntersectionOver
    (k : Type*) [Field k] (S : Type*) [CommRing S] [Algebra k S] : Prop :=
  Subsingleton S ∨
    ∃ (n c : ℕ) (π : MvPolynomial (Fin n) k →ₐ[k] S) (f : Fin c → MvPolynomial (Fin n) k),
      Function.Surjective π ∧
      RingHom.ker π.toRingHom = Ideal.span (Set.range f) ∧
      ringKrullDim S + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)

/-- Let `k` be a field and `S` a finite-type `k`-algebra. `S` is a *local complete
intersection over `k`* if there is a finite family `g_1, …, g_t ∈ S` generating the unit
ideal (`Ideal.span {g_i} = ⊤`, equivalently `Spec S = ⋃ D(g_i)`) such that each
localization `S_{g_i}` is a global complete intersection over `k`. -/
@[ega "IV 19.3.6", sga "6 0 3.2" "special case"]
noncomputable def IsLocalCompleteIntersectionOver
    (k : Type*) [Field k] (S : Type*) [CommRing S] [Algebra k S] : Prop :=
  ∃ (t : ℕ) (g : Fin t → S), Ideal.span (Set.range g) = ⊤ ∧
    ∀ i, IsGlobalCompleteIntersectionOver k (Localization.Away (g i))

/-- A ring map `R → S` is *syntomic*, i.e. a *flat local complete intersection over
`R`*, if it is flat, of finite presentation, and for every prime `p ⊆ R` the fibre ring
`S ⊗_R κ(p)` is a local complete intersection over the residue field `κ(p)`.

The fibre ring is the base change `TensorProduct R S κ` with `κ = κ(p)`, equipped with
the `κ`-algebra structure coming from the right tensor factor
(`Algebra.TensorProduct.rightAlgebra`). -/
@[ega "IV 19.3.6" "affine case"]
noncomputable def IsSyntomic
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] : Prop :=
  Module.Flat R S ∧ Algebra.FinitePresentation R S ∧
    ∀ (p : Ideal R), [p.IsPrime] →
      letI κ := IsLocalRing.ResidueField (Localization.AtPrime p)
      letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
      IsLocalCompleteIntersectionOver κ (TensorProduct R S κ)

/-- Auxiliary: `RingHom.FinitePresentation` transfers across ring isomorphisms of the
source and target, even when the rings live in different universes.  (Mathlib's
`RingHom.RespectsIso` is universe-monomorphic, so we prove this universe-polymorphic
version by hand via restriction of scalars.) -/
private theorem fp_transfer {R : Type*} [CommRing R] {R' : Type*} [CommRing R']
    {S : Type*} [CommRing S] {S' : Type*} [CommRing S']
    (f : R →+* S) (eR : R ≃+* R') (eS : S ≃+* S')
    (hf : f.FinitePresentation) :
    ((eS.toRingHom.comp f).comp eR.symm.toRingHom).FinitePresentation := by
  set f' : R' →+* S' := (eS.toRingHom.comp f).comp eR.symm.toRingHom with hf'
  let : Algebra R S := f.toAlgebra
  let : Algebra R' S' := f'.toAlgebra
  let : Algebra R R' := eR.toRingHom.toAlgebra
  let : Algebra R S' := ((algebraMap R' S').comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [RingHom.FinitePresentation]
  have key : ∀ r : R, eS (algebraMap R S r) = algebraMap R S' r := by
    intro r
    change eS (f r) = (algebraMap R' S').comp (algebraMap R R') r
    simp only [RingHom.coe_comp, Function.comp_apply]
    change eS (f r) = f' (eR r)
    rw [hf']
    simp
  have : Algebra.FinitePresentation R S := hf
  have : Algebra.FinitePresentation R S' :=
    Algebra.FinitePresentation.equiv (AlgEquiv.ofRingEquiv (f := eS) key)
  have : Algebra.FiniteType R R' := by
    have : Algebra.FiniteType R R := Module.Finite.finiteType R
    exact Algebra.FiniteType.of_surjective (Algebra.ofId R R') eR.surjective
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R R' S'

/-- Finite presentation is local on the source: if the `g i` generate the unit ideal of
`S` and each localization `R → S_{g i}` is of finite presentation, then so is `R → S`.

Since the `g i` span `⊤`, there is a partition-of-unity relation `∑ a i * g i = 1` in
`S`, and finite type descends along such a cover. Given a surjection
`R[x_1, …, x_N] ↠ S`, localizing the presentation at each `g i` presents `S_{g i}` with
a finitely generated relation module, and gluing the finitely many relations over the
cover yields a finite generating set for the kernel. -/
@[sga "3 V 9.1" "special case"]
theorem finitePresentation_of_finitePresentation_localization_away
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (m : ℕ) (g : Fin m → S) (hg : Ideal.span (Set.range g) = ⊤)
    (h : ∀ i, Algebra.FinitePresentation R (Localization.Away (g i))) :
    Algebra.FinitePresentation R S := by
  -- `RingHom.finitePresentation_ofLocalizationSpanTarget` (Stacks 00EP) forces `R` and
  -- `S` into a common universe, so we first ULift both into `Type (max u_1 u_2)`, apply
  -- the lemma there, and transfer back along `fp_transfer`.
  rw [← RingHom.finitePresentation_algebraMap]
  set eRr : ULift.{max u_1 u_2} R ≃+* R := ULift.ringEquiv
  set eSr : ULift.{max u_1 u_2} S ≃+* S := ULift.ringEquiv
  set f' : ULift.{max u_1 u_2} R →+* ULift.{max u_1 u_2} S :=
    eSr.symm.toRingHom.comp ((algebraMap R S).comp eRr.toRingHom) with hf'
  have hfp' : f'.FinitePresentation := by
    apply RingHom.finitePresentation_ofLocalizationSpanTarget f'
        (eSr.symm '' (Set.range g))
    · rw [← Ideal.map_span, hg, Ideal.map_top]
    · rintro r
      obtain ⟨x, ⟨i, rfl⟩, hx⟩ := r.property
      set rr : ULift.{max u_1 u_2} S := (r : ULift.{max u_1 u_2} S)
      have hmap : Submonoid.map eSr.symm.toMonoidHom (Submonoid.powers (g i))
          = Submonoid.powers rr := by
        rw [← hx]
        exact Submonoid.map_powers eSr.symm.toMonoidHom (g i)
      let eL : Localization.Away (g i) ≃+* Localization.Away rr :=
        IsLocalization.ringEquivOfRingEquiv (Localization.Away (g i)) (Localization.Away rr)
          eSr.symm hmap
      have hT := fp_transfer (algebraMap R (Localization.Away (g i))) eRr.symm eL
        (RingHom.finitePresentation_algebraMap.mpr (h i))
      convert hT using 1
      ext y
      simp only [RingHom.coe_comp, Function.comp_apply, hf', RingEquiv.symm_symm,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [IsScalarTower.algebraMap_apply R S (Localization.Away (g i)),
        IsLocalization.ringEquivOfRingEquiv_eq hmap]
  have hT := fp_transfer f' eRr eSr hfp'
  have hcomp : ((eSr.toRingHom.comp f').comp eRr.symm.toRingHom) = algebraMap R S := by
    rw [hf']
    ext x
    simp
  rwa [hcomp] at hT

/-- Transport of "global complete intersection over `k`" along a `k`-algebra isomorphism. -/
private theorem aux_gci_transport (k : Type*) [Field k] (A B : Type*) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (hA : IsGlobalCompleteIntersectionOver k A) :
    IsGlobalCompleteIntersectionOver k B := by
  rcases hA with hsub | ⟨n, c, π, f, hπ, hker, hdim⟩
  · exact Or.inl e.symm.injective.subsingleton
  · refine Or.inr ⟨n, c, e.toAlgHom.comp π, f, e.surjective.comp hπ, ?_, ?_⟩
    · have : (e.toAlgHom.comp π).toRingHom = (e.toAlgHom.toRingHom).comp π.toRingHom := rfl
      rwa [this, RingHom.ker_comp_of_injective _ e.injective]
    · rw [← hdim]
      congr 1
      exact (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm

/-- A family of elements generating the unit ideal still does so after applying a ring map. -/
private theorem span_range_comp_eq_top {A B ι : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {g : ι → A} (hg : Ideal.span (Set.range g) = ⊤) :
    Ideal.span (Set.range fun i => f (g i)) = ⊤ := by
  rw [show (Set.range fun i => f (g i)) = f '' Set.range g from Set.range_comp f g,
    ← Ideal.map_span, hg, Ideal.map_top]

/-- Transport of "local complete intersection over `k`" along a `k`-algebra isomorphism. -/
private theorem aux_lci_transport (k : Type*) [Field k] (A B : Type*) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (hA : IsLocalCompleteIntersectionOver k A) :
    IsLocalCompleteIntersectionOver k B := by
  obtain ⟨t, g, hspan, hgci⟩ := hA
  refine ⟨t, fun i => e (g i), ?_, ?_⟩
  · exact span_range_comp_eq_top (e : A →+* B) hspan
  · intro i
    have hmap : Submonoid.map (e : A ≃+* B).toMonoidHom (Submonoid.powers (g i))
        = Submonoid.powers (e (g i)) := Submonoid.map_powers _ _
    let iso : Localization.Away (g i) ≃ₐ[k] Localization.Away (e (g i)) :=
      IsLocalization.algEquivOfAlgEquiv (A := k) (R := A) (P := B)
        (S := Localization.Away (g i)) (Q := Localization.Away (e (g i)))
        (M := Submonoid.powers (g i)) (T := Submonoid.powers (e (g i))) e hmap
    exact aux_gci_transport k _ _ iso (hgci i)

/-- For `x : A` and `s` in the localization `A_x`, with `a` the numerator of `s`, the localization
of `A_x` away from `s` is also a localization of `A` away from `a * x` (transitivity of
localizations away, Stacks 02C6). -/
private theorem aux_key_away_mul (A : Type*) [CommRing A] (x : A) (s : Localization.Away x) :
    IsLocalization.Away ((IsLocalization.Away.sec x s).1 * x) (Localization.Away s) := by
  set a : A := (IsLocalization.Away.sec x s).fst
  set n : ℕ := (IsLocalization.Away.sec x s).snd
  have hspec : s * (algebraMap A (Localization.Away x)) (x ^ n)
      = (algebraMap A (Localization.Away x)) a := IsLocalization.Away.sec_spec x s
  have hunit : IsUnit ((algebraMap A (Localization.Away x)) (x ^ n)) := by
    rw [map_pow]
    exact IsLocalization.Away.algebraMap_pow_isUnit x n
  have hassoc : Associated s ((algebraMap A (Localization.Away x)) a) :=
    ⟨hunit.unit, by rwa [IsUnit.unit_spec]⟩
  have h1 : IsLocalization.Away ((algebraMap A (Localization.Away x)) a) (Localization.Away s) :=
    IsLocalization.Away.of_associated hassoc
  exact IsLocalization.Away.mul (Localization.Away x) (Localization.Away s) x a

/-- A finite cover by basic opens whose localizations are global complete intersections witnesses
that the ring is a local complete intersection. -/
private theorem aux_lci_of_finite_cover (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k A]
    (T : Set A) (hfin : T.Finite) (hspan : Ideal.span T = ⊤)
    (hG : ∀ w ∈ T, IsGlobalCompleteIntersectionOver k (Localization.Away w)) :
    IsLocalCompleteIntersectionOver k A := by
  obtain ⟨F, hF⟩ := hfin.exists_finset_coe
  refine ⟨F.card, fun i => (F.equivFin.symm i : A), ?_, ?_⟩
  · have hrange : Set.range (fun i => (F.equivFin.symm i : A)) = T := by
      rw [← hF]
      ext x
      refine ⟨?_, fun hx => ⟨F.equivFin ⟨x, hx⟩, by simp⟩⟩
      rintro ⟨i, rfl⟩
      exact (F.equivFin.symm i).property
    rwa [hrange]
  · intro i
    apply hG
    rw [← hF]
    exact (F.equivFin.symm i).property

/-- The element `x * (numerator of s)` of `A` produced by `IsLocalization.Away.mulNumerator` has a
localization that is a global complete intersection, provided the inner localization is. -/
private theorem aux_away_mulNumerator_gci (k : Type*) [Field k] (A : Type*) [CommRing A]
    [Algebra k A] (x : A) (s : Localization.Away x)
    (hs : IsGlobalCompleteIntersectionOver k (Localization.Away s)) :
    IsGlobalCompleteIntersectionOver k
      (Localization.Away (x * (IsLocalization.Away.sec x s).1)) := by
  set a := (IsLocalization.Away.sec x s).fst
  have hk : IsLocalization.Away (a * x) (Localization.Away s) := aux_key_away_mul A x s
  have hcanon : IsLocalization.Away (a * x) (Localization.Away (x * a)) := by
    rw [mul_comm x a]
    infer_instance
  let e : Localization.Away (x * a) ≃ₐ[A] Localization.Away s :=
    @IsLocalization.algEquiv A _ (Submonoid.powers (a * x)) (Localization.Away (x * a)) _ _ hcanon
      (Localization.Away s) _ _ hk
  exact aux_gci_transport k _ _ (e.restrictScalars k).symm hs

-- needed: `aux_lci_local_on_source`'s third bullet leaves goals unless defeq unfolds
-- `IsLocalization.Away.mulNumerator` to identify the iterated `Localization.Away` with the
-- one-step localization the goal is stated at.
set_option backward.isDefEq.respectTransparency false in
/-- Local complete intersection is local on the source: a unit-ideal cover by basic opens all of
whose localizations are local complete intersections gives a local complete intersection. -/
private theorem aux_lci_local_on_source (k : Type*) [Field k] (A : Type*) [CommRing A]
    [Algebra k A] (m : ℕ) (cover : Fin m → A) (hcover : Ideal.span (Set.range cover) = ⊤)
    (hLCI : ∀ i, IsLocalCompleteIntersectionOver k (Localization.Away (cover i))) :
    IsLocalCompleteIntersectionOver k A := by
  have hLCI' : ∀ t : ↑(Set.range cover),
      IsLocalCompleteIntersectionOver k (Localization.Away (↑t : A)) := by
    rintro ⟨w, i, rfl⟩
    exact hLCI i
  choose tt innerg hspan_t hgci_t using hLCI'
  set p : (t : ↑(Set.range cover)) → Set (Localization.Away (↑t : A)) :=
    fun t => Set.range (innerg t)
  have hp_span : ∀ t, Ideal.span (p t) = ⊤ := hspan_t
  set W := IsLocalization.Away.mulNumerator (Set.range cover) p with hW_def
  apply aux_lci_of_finite_cover k A (Set.range W)
  · exact Set.finite_range _
  · exact IsLocalization.Away.span_range_mulNumerator_eq_top hcover hp_span
  · rintro w ⟨⟨t, s⟩, rfl⟩
    have hgci_s : IsGlobalCompleteIntersectionOver k
        (Localization.Away (↑s : Localization.Away (↑t : A))) := by
      obtain ⟨j, hj⟩ := s.property
      have := hgci_t t j
      rwa [hj] at this
    have := aux_away_mulNumerator_gci k A (↑t) (↑s) hgci_s
    convert this using 2
    rw [hW_def, IsLocalization.Away.mulNumerator]

/-- The `κ`-linear commutativity isomorphism `S ⊗[R] κ ≃ₐ[κ] κ ⊗[R] S`, where `S ⊗[R] κ` carries
the right (κ-)algebra structure. -/
noncomputable def aux_kcomm (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (κ : Type*) [Field κ] [Algebra R κ] :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
    (TensorProduct R S κ) ≃ₐ[κ] (TensorProduct R κ S) :=
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R S κ).toRingEquiv) (by
    intro c
    change (Algebra.TensorProduct.comm R S κ) ((1 : S) ⊗ₜ[R] c) = c ⊗ₜ[R] (1 : S)
    rw [Algebra.TensorProduct.comm_tmul])

/-- The commutativity isomorphism `aux_kcomm` sends `s ⊗ₜ c` to `c ⊗ₜ s`. -/
theorem aux_kcomm_tmul (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (κ : Type*) [Field κ] [Algebra R κ] (s : S) (c : κ) :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
    (aux_kcomm R S κ) (s ⊗ₜ[R] c) = c ⊗ₜ[R] s := by
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
  change (Algebra.TensorProduct.comm R S κ) (s ⊗ₜ[R] c) = c ⊗ₜ[R] s
  rw [Algebra.TensorProduct.comm_tmul]

/-- Localization commutes with base change: `(S ⊗_R κ)` localized away from `g_i ⊗ 1` is
`κ`-isomorphic to `S_{g_i} ⊗_R κ`. -/
@[ega "0 6.3.2" "special case"]
noncomputable def aux_cruxIso (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (κ : Type*) [Field κ] [Algebra R κ] (gi : S) :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := Localization.Away gi) (B := κ)
    (TensorProduct R (Localization.Away gi) κ) ≃ₐ[κ]
      Localization.Away (gi ⊗ₜ[R] (1 : κ)) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := Localization.Away gi) (B := κ)
  have hval : (aux_kcomm R S κ : (TensorProduct R S κ) ≃+* _).toMonoidHom (gi ⊗ₜ[R] (1:κ))
      = (1:κ) ⊗ₜ[R] gi := by
    change (aux_kcomm R S κ) (gi ⊗ₜ[R] (1:κ)) = (1:κ) ⊗ₜ[R] gi
    rw [aux_kcomm_tmul]
  have hmap : Submonoid.map (aux_kcomm R S κ : (TensorProduct R S κ) ≃+* _).toMonoidHom
      (Submonoid.powers (gi ⊗ₜ[R] (1:κ))) = Submonoid.powers ((1:κ) ⊗ₜ[R] gi) := by
    rw [Submonoid.map_powers, hval]
  let step3 : Localization.Away (gi ⊗ₜ[R] (1:κ)) ≃ₐ[κ] Localization.Away ((1:κ) ⊗ₜ[R] gi) :=
    IsLocalization.algEquivOfAlgEquiv (A := κ) (R := TensorProduct R S κ) (P := TensorProduct R κ S)
      (S := Localization.Away (gi ⊗ₜ[R] (1:κ))) (Q := Localization.Away ((1:κ) ⊗ₜ[R] gi))
      (M := Submonoid.powers (gi ⊗ₜ[R] (1:κ))) (T := Submonoid.powers ((1:κ) ⊗ₜ[R] gi))
      (aux_kcomm R S κ) hmap
  exact (aux_kcomm R (Localization.Away gi) κ).trans
    ((IsLocalization.Away.tensorProductEquivTMulRight R κ gi (Localization.Away gi)).trans
      step3.symm)

/-- Being a local complete intersection on fibres is local on the source: fix a prime
`p ⊆ R` with residue field `κ`. If the `g i` generate the unit ideal of `S` and each
fibre `S_{g i} ⊗_R κ` is a local complete intersection over `κ`, then so is the fibre
`S ⊗_R κ`.

The images `g i ⊗ₜ 1` generate the unit ideal of `S ⊗_R κ`, since base change carries a
unit-ideal family to a unit-ideal family. Localization commutes with base change, so
`(S ⊗_R κ)_{g i ⊗ₜ 1} ≃ₐ[κ] S_{g i} ⊗_R κ`, which is a local complete intersection by
hypothesis. Being a local complete intersection is itself local on the source, so the
fibre is one. -/
theorem isLocalCompleteIntersection_fiber_of_localization_away
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (m : ℕ) (g : Fin m → S) (hg : Ideal.span (Set.range g) = ⊤)
    (p : Ideal R) [p.IsPrime]
    (h : ∀ i,
      letI κ := IsLocalRing.ResidueField (Localization.AtPrime p)
      letI := Algebra.TensorProduct.rightAlgebra (R := R)
        (A := Localization.Away (g i)) (B := κ)
      IsLocalCompleteIntersectionOver κ
        (TensorProduct R (Localization.Away (g i)) κ)) :
    letI κ := IsLocalRing.ResidueField (Localization.AtPrime p)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
    IsLocalCompleteIntersectionOver κ (TensorProduct R S κ) := by
  -- rightAlgebra instances match IsSyntomic; edge case m=0 → zero ring).
  let κ := IsLocalRing.ResidueField (Localization.AtPrime p)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
  -- The images `g i ⊗ₜ 1` form a unit-ideal cover of the fiber `S ⊗_R κ`, and each localization
  -- of the fiber at `g i ⊗ₜ 1` is `κ`-isomorphic to `S_{g i} ⊗_R κ` (localization commutes with
  -- base change), which is a local complete intersection by hypothesis.  LCI is local on the
  -- source, so the fiber is a local complete intersection.
  apply aux_lci_local_on_source κ (TensorProduct R S κ) m (fun i => g i ⊗ₜ[R] (1:κ))
  · exact span_range_comp_eq_top
      (Algebra.TensorProduct.includeLeftRingHom (A := S) (B := κ)) hg
  · intro i
    let := Algebra.TensorProduct.rightAlgebra (R := R) (A := Localization.Away (g i)) (B := κ)
    exact aux_lci_transport κ _ _ (aux_cruxIso R S κ (g i)) (h i)

/-- Syntomic is local on the source: let `R → S` be a ring map and suppose there are
elements `g_1, …, g_m ∈ S` generating the unit ideal of `S` such that for each `i` the
composite `R → S_{g_i}` is syntomic. Then `R → S` is syntomic. -/
@[stacks 00SO]
theorem isSyntomic_of_isSyntomic_localization_away
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (m : ℕ) (g : Fin m → S) (hg : Ideal.span (Set.range g) = ⊤)
    (h : ∀ i, IsSyntomic R (Localization.Away (g i))) :
    IsSyntomic R S := by
  refine ⟨?_, ?_, ?_⟩
  · -- Flatness is local on the source: `S` is covered by the basic opens
    -- `D(g i)` and each `S_{g i}` is `R`-flat, so `S` is `R`-flat.
    apply Module.flat_of_isLocalized_span S S (Set.range g) hg
      (fun r => Localization.Away (r : S))
      (fun r => (Algebra.linearMap S (Localization.Away (r : S))))
    rintro ⟨r, i, rfl⟩
    exact (h i).left
  · -- Finite presentation is local on the source (Stacks 00EP).
    exact finitePresentation_of_finitePresentation_localization_away
      R S m g hg (fun i => (h i).right.left)
  · -- The fiber condition: for each prime `p` of `R`, the fiber `S ⊗_R κ(p)`
    -- is a local complete intersection over `κ(p)`, because the images of the
    -- `g i` cover `Spec (S ⊗_R κ(p))` and each localized fiber
    -- `S_{g i} ⊗_R κ(p) = (S ⊗_R κ(p))_{ḡ i}` is an LCI.
    intro p _
    exact isLocalCompleteIntersection_fiber_of_localization_away
      R S m g hg p (fun i => (h i).right.right p)
