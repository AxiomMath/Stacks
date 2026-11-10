module

public import StacksFrontier.Algebra.Module.FiniteLength.DeterminantProduct
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.BaseChange

/-!
# The fibre of a flat base change of a tame symbol preparation

Let `A → A'` be a flat local homomorphism of local rings, let `A ⊆ B` carry a tame symbol
preparation `P` (Stacks 0EAG), let `𝔮` be a maximal ideal of `B` with local parameter
`π ∈ B_𝔮`, and set `B' = A' ⊗_A B`. Consider the finite `A'`-algebra

`V = (A' ⊗_A B_𝔮) / π = A' ⊗_A (B_𝔮 / π B_𝔮)`.

The maximal ideals of `V` correspond to the maximal ideals `𝔮'` of `B'` lying over `𝔮`, and the
localization of `V` at the maximal ideal corresponding to `𝔮'` is `B'_{𝔮'} / π B'_{𝔮'}`. This is
the decomposition

`(B_𝔮 / π B_𝔮) ⊗_A A' = ⊕_{𝔮'} B'_{𝔮'} / π B'_{𝔮'}`

used in the proof of Stacks 0EPG; with the determinant of multiplication by a unit `u` it gives
the identity `det_{κ'}(u : M ⊗_A A') = ∏ det_{κ'}(u : B'_{𝔮'}/π)`.

## Main definitions

* `AlgebraicGeometry.TameSymbolPreparation.FibreRing` — the ring `V`.
* `AlgebraicGeometry.TameSymbolPreparation.fibreMap` — the ring map `B' → V`.
* `AlgebraicGeometry.TameSymbolPreparation.fibrePoint` — the maximal ideal of `B'` over `𝔮`
  under a maximal ideal of `V`.

## Main results

* `AlgebraicGeometry.TameSymbolPreparation.map_det_pow_eq_det_fibreRing` — flat base change
  of the determinant of multiplication on `B_𝔮 / π` (Stacks 0GT0) computed on `V`.
* `AlgebraicGeometry.TameSymbolPreparation.fibrePoint_bijective` — the correspondence of
  maximal ideals.
* `AlgebraicGeometry.TameSymbolPreparation.det_localization_fibreRing` — the determinant of
  multiplication on a localization of `V` is the one on `B'_{𝔮'} / π`.

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w

namespace AlgebraicGeometry.TameSymbolPreparation

section TensorQuotient

variable {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] [Algebra A A']
  {C : Type w} [CommRing C] [Algebra A C]

/-- Under `A' ⊗_A (C / π) ≅ (A' ⊗_A C) / π`, the base change of multiplication by `x` is
multiplication by `1 ⊗ x`. -/
theorem tensorQuotientEquiv_comp_baseChange (π x : C) :
    (Algebra.TensorProduct.tensorQuotientEquiv (R := A) A' C A' (Ideal.span {π})).toLinearMap.comp
        (LinearMap.baseChange A'
          ((LinearMap.lsmul C (C ⧸ Ideal.span {π}) x).restrictScalars A)) =
      ((LinearMap.lsmul _ _ (Ideal.Quotient.mk
          (Ideal.map (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := C))
            (Ideal.span {π})) (Algebra.TensorProduct.includeRight x))).restrictScalars A').comp
        (Algebra.TensorProduct.tensorQuotientEquiv (R := A) A' C A'
          (Ideal.span {π})).toLinearMap := by
  set I := Ideal.map (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := C))
    (Ideal.span {π})
  set e := Algebra.TensorProduct.tensorQuotientEquiv (R := A) A' C A' (Ideal.span {π})
  refine LinearMap.ext fun t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | tmul s y =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change e (s ⊗ₜ[A] (Ideal.Quotient.mk (Ideal.span {π}) x *
        Ideal.Quotient.mk (Ideal.span {π}) b)) =
      Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight x) *
        e (s ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {π}) b)
    rw [← map_mul, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
      Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, ← map_mul,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] [Module.Flat A A']

/-- **Flat base change of the determinant of multiplication on `C / π` (Stacks 0GT0)**,
computed on `(A' ⊗_A C) / π`: if the closed fibre has length `m`, the image in `κ'` of
`det_κ(x : C/π)^m` is `det_{κ'}(1 ⊗ x : (A' ⊗_A C)/π)`. -/
theorem map_det_pow_eq_det_fibreRing (m : ℕ)
    (hm : Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A)) = m) (π x : C)
    (hM : IsFiniteLength A (C ⧸ Ideal.span {π})) :
    ∃ hV : IsFiniteLength A' ((A' ⊗[A] C) ⧸
        Ideal.map (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := C))
          (Ideal.span {π})),
      ResidueField.map (algebraMap A A')
          (FiniteLengthEndomorphism.det A hM
            ((LinearMap.lsmul C (C ⧸ Ideal.span {π}) x).restrictScalars A) ^ m) =
        FiniteLengthEndomorphism.det A' hV
          ((LinearMap.lsmul _ _ (Ideal.Quotient.mk
            (Ideal.map (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := C))
              (Ideal.span {π})) (Algebra.TensorProduct.includeRight x))).restrictScalars A') := by
  obtain ⟨hMS, h⟩ := FiniteLengthEndomorphism.map_det_pow_eq_det_baseChange m hm hM
    ((LinearMap.lsmul C (C ⧸ Ideal.span {π}) x).restrictScalars A)
  set e := Algebra.TensorProduct.tensorQuotientEquiv (R := A) A' C A' (Ideal.span {π})
  have hV := e.toLinearEquiv.isFiniteLength hMS
  exact ⟨hV, h.trans (FiniteLengthEndomorphism.det_eq_of_linearEquiv hMS hV _ _
    e.toLinearEquiv (tensorQuotientEquiv_comp_baseChange π x))⟩

end TensorQuotient

section Fibre

variable {A : Type u} {A' : Type v} {B : Type w} [CommRing A] [CommRing A'] [CommRing B]
  [IsLocalRing A] [IsLocalRing A'] [Algebra A A'] [IsLocalHom (algebraMap A A')] [Algebra A B]
  {r : ℕ} {a : Fin r → A}

variable (A') in
/-- The map `A' ⊗_A B → A' ⊗_A B_𝔮`. -/
noncomputable def toTensorLocalization (q : Ideal B) [q.IsPrime] :
    A' ⊗[A] B →ₐ[A] A' ⊗[A] Localization.AtPrime q :=
  Algebra.TensorProduct.map (AlgHom.id A A') (IsScalarTower.toAlgHom A B (Localization.AtPrime q))

variable (A') in
/-- The ideal generated by the local parameter at `𝔮` in `A' ⊗_A B_𝔮`. -/
noncomputable def fibreIdeal (P : TameSymbolPreparation a B) (q : Ideal B) [q.IsMaximal] :
    Ideal (A' ⊗[A] Localization.AtPrime q) :=
  Ideal.map (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := Localization.AtPrime q))
    (Ideal.span {P.parameter q})

variable (A') in
/-- The ring `V = (A' ⊗_A B_𝔮) / π`. -/
abbrev FibreRing (P : TameSymbolPreparation a B) (q : Ideal B) [q.IsMaximal] :=
  (A' ⊗[A] Localization.AtPrime q) ⧸ fibreIdeal A' P q

variable (A') in
/-- The ring map `A' ⊗_A B → V`. -/
noncomputable def fibreMap (P : TameSymbolPreparation a B) (q : Ideal B) [q.IsMaximal] :
    A' ⊗[A] B →+* FibreRing A' P q :=
  (Ideal.Quotient.mk _).comp (toTensorLocalization (A := A) A' q).toRingHom

variable (P : TameSymbolPreparation a B) (q : Ideal B) [q.IsMaximal]

omit [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
/-- The map `A' ⊗_A B → V` is compatible with the structure maps from `A'`. -/
theorem fibreMap_algebraMap (x : A') :
    fibreMap A' P q (algebraMap A' (A' ⊗[A] B) x) = algebraMap A' (FibreRing A' P q) x := by
  change Ideal.Quotient.mk _ (toTensorLocalization (A := A) A' q (algebraMap A' (A' ⊗[A] B) x)) =
    Ideal.Quotient.mk _ (algebraMap A' (A' ⊗[A] Localization.AtPrime q) x)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
    toTensorLocalization, Algebra.TensorProduct.map_tmul, map_one]
  rfl

omit [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
/-- The map `A' ⊗_A B → V` sends `1 ⊗ b` to the class of `1 ⊗ (b / 1)`. -/
theorem fibreMap_includeRight (b : B) :
    fibreMap A' P q (Algebra.TensorProduct.includeRight b) =
      Ideal.Quotient.mk (fibreIdeal A' P q)
        (Algebra.TensorProduct.includeRight (algebraMap B (Localization.AtPrime q) b)) :=
  rfl

variable {P q}

omit [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
/-- The ideal of `A' ⊗_A B` under a maximal ideal of `V` is maximal, `V` being finite over
`A'`. -/
theorem comap_fibreMap_isMaximal (hV : IsFiniteLength A' (FibreRing A' P q))
    (p : Ideal (FibreRing A' P q)) [p.IsMaximal] : (p.comap (fibreMap A' P q)).IsMaximal := by
  let := P.finite
  have : IsNoetherian A' (FibreRing A' P q) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hV).1
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A')
  have heq : (p.comap (fibreMap A' P q)).under A' = p.under A' := by
    ext x
    simp only [Ideal.under, Ideal.mem_comap, fibreMap_algebraMap]
  rw [heq]
  exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal p

/-- The maximal ideal of `A' ⊗_A B` under a maximal ideal of `V` lies over `𝔮`. -/
theorem underIdeal_comap_fibreMap (hV : IsFiniteLength A' (FibreRing A' P q))
    (p : Ideal (FibreRing A' P q)) [hp : p.IsMaximal] :
    underIdeal (p.comap (fibreMap A' P q)) = q := by
  have := comap_fibreMap_isMaximal hV p
  refine (P.underIdeal_isMaximal (p.comap (fibreMap A' P q))).eq_of_le
    (Ideal.IsMaximal.ne_top inferInstance) fun b hb ↦ ?_
  by_contra hnot
  have hu : IsUnit (algebraMap B (Localization.AtPrime q) b) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ q b).2 hnot
  have hb' : Ideal.Quotient.mk (fibreIdeal A' P q)
      (Algebra.TensorProduct.includeRight (algebraMap B (Localization.AtPrime q) b)) ∈ p := hb
  exact hp.ne_top (p.eq_top_of_isUnit_mem hb' (hu.map ((Ideal.Quotient.mk _).comp
    (Algebra.TensorProduct.includeRight (R := A) (A := A')
      (B := Localization.AtPrime q)).toRingHom)))

variable (P q) in
/-- The maximal ideal of `A' ⊗_A B` over `𝔮` under a maximal ideal of `V`. -/
noncomputable def fibrePoint (hV : IsFiniteLength A' (FibreRing A' P q))
    (p : MaximalSpectrum (FibreRing A' P q)) :
    {Q : MaximalSpectrum (A' ⊗[A] B) // underIdeal Q.asIdeal = q} :=
  ⟨⟨p.asIdeal.comap (fibreMap A' P q), comap_fibreMap_isMaximal hV p.asIdeal⟩,
    underIdeal_comap_fibreMap hV p.asIdeal⟩

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
/-- `A' ⊗_A B_𝔮` is the localization of `A' ⊗_A B` at the image of `B \ 𝔮`. -/
theorem isLocalization_tensorLocalization :
    letI := (toTensorLocalization (A := A) A' q).toAlgebra
    IsLocalization (q.primeCompl.map
        (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B)))
      (A' ⊗[A] Localization.AtPrime q) := by
  let := (toTensorLocalization (A := A) A' q).toAlgebra
  let : IsScalarTower A' (A' ⊗[A] B) (A' ⊗[A] Localization.AtPrime q) :=
    .of_algebraMap_eq' (by ext; simp [RingHom.algebraMap_toAlgebra, toTensorLocalization])
  exact IsLocalization.tensorProduct_tensorProduct_right A A' q.primeCompl
    (Localization.AtPrime q) (by ext; simp [RingHom.algebraMap_toAlgebra, toTensorLocalization])

/-- Localizing a quotient at a prime: `(R_𝔭) / I` is the localization of `R / I` at a prime over
`𝔭`. -/
theorem isLocalization_quotient_atPrime {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] (I : Ideal R)
    (q : Ideal (R ⧸ I)) [q.IsPrime] (hq : q.comap (Ideal.Quotient.mk I) = p) :
    IsLocalization.AtPrime (Rₚ ⧸ I.map (algebraMap R Rₚ)) q := by
  subst hq
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ I) (q.comap (Ideal.Quotient.mk I)).primeCompl =
      q.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨?_, fun hx ↦ ⟨y, hx, rfl⟩⟩
    rintro ⟨z, hz, hzy⟩ hmem
    refine hz ?_
    have hzz : Ideal.Quotient.mk I z = Ideal.Quotient.mk I y := by
      simpa [Ideal.Quotient.algebraMap_eq] using hzy
    simpa [Ideal.mem_comap, hzz] using hmem
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (R ⧸ I) (q.comap (Ideal.Quotient.mk I)).primeCompl)
      (Rₚ ⧸ I.map (algebraMap R Rₚ)) := inferInstance
  rwa [hsub] at this

/-- Distinct maximal ideals of `V` lie over distinct maximal ideals of `A' ⊗_A B`. -/
theorem fibrePoint_injective (hV : IsFiniteLength A' (FibreRing A' P q)) :
    Function.Injective (fibrePoint P q hV) := by
  let := (toTensorLocalization (A := A) A' q).toAlgebra
  set N := q.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B))
  set L := A' ⊗[A] Localization.AtPrime q
  set I := fibreIdeal A' P q
  have : IsLocalization N L := isLocalization_tensorLocalization
  intro p p' hp
  have hT : p.asIdeal.comap (fibreMap A' P q) = p'.asIdeal.comap (fibreMap A' P q) :=
    congrArg (fun t ↦ t.1.asIdeal) hp
  have hL : p.asIdeal.comap (Ideal.Quotient.mk I) = p'.asIdeal.comap (Ideal.Quotient.mk I) := by
    rw [← IsLocalization.map_under N L (p.asIdeal.comap (Ideal.Quotient.mk I)),
      ← IsLocalization.map_under N L (p'.asIdeal.comap (Ideal.Quotient.mk I))]
    exact congrArg (Ideal.map (algebraMap (A' ⊗[A] B) L)) hT
  exact MaximalSpectrum.ext (by
    simpa only [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] using
      congrArg (Ideal.map (Ideal.Quotient.mk I)) hL)

/-- Every maximal ideal of `A' ⊗_A B` over `𝔮` lies under a maximal ideal of `V`, as soon as one
member of the prepared family is a nonunit. -/
theorem fibrePoint_surjective (hV : IsFiniteLength A' (FibreRing A' P q))
    (hnot : ¬ ∀ i, IsUnit (a i)) : Function.Surjective (fibrePoint P q hV) := by
  let := (toTensorLocalization (A := A) A' q).toAlgebra
  set N := q.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B))
  set L := A' ⊗[A] Localization.AtPrime q
  set I := fibreIdeal A' P q
  have : IsLocalization N L := isLocalization_tensorLocalization
  rintro ⟨⟨QT, hQT⟩, hQTq⟩
  have hd : Disjoint (N : Set (A' ⊗[A] B)) (QT : Set (A' ⊗[A] B)) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨b, hb, rfl⟩ hbQ
    exact hb (hQTq ▸ hbQ)
  set QL : Ideal L := QT.map (algebraMap (A' ⊗[A] B) L)
  have : QL.IsMaximal := IsLocalization.isMaximal_of_isMaximal_disjoint N L QT hd
  have hQLunder : QL.comap (algebraMap (A' ⊗[A] B) L) = QT :=
    IsLocalization.under_map_of_isPrime_disjoint N L hQT.isPrime hd
  set J : Ideal (Localization.AtPrime q) := QL.comap
    (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := Localization.AtPrime q))
  have hJunder : J.comap (algebraMap B (Localization.AtPrime q)) = q := by
    ext b
    change algebraMap (A' ⊗[A] B) L (Algebra.TensorProduct.includeRight b) ∈ QL ↔ _
    rw [← Ideal.mem_comap, hQLunder]
    exact Iff.of_eq (congrArg (b ∈ ·) hQTq)
  have hJ : J = maximalIdeal (Localization.AtPrime q) :=
    (Localization.AtPrime.eq_maximalIdeal_iff_under_eq).mp hJunder
  have hIQL : I ≤ QL := by
    change Ideal.map _ _ ≤ QL
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]
    change P.parameter q ∈ J
    rw [hJ]
    exact P.parameter_mem_maximal hnot q
  set PV : Ideal (FibreRing A' P q) := QL.map (Ideal.Quotient.mk I)
  have : PV.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  refine ⟨⟨PV, inferInstance⟩, Subtype.ext (MaximalSpectrum.ext ?_)⟩
  have hPV : PV.comap (Ideal.Quotient.mk I) = QL := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIQL]
  change (PV.comap (Ideal.Quotient.mk I)).comap (algebraMap (A' ⊗[A] B) L) = QT
  rw [hPV, hQLunder]

/-- **The maximal ideals of `V` correspond to the maximal ideals of `A' ⊗_A B` over `𝔮`**, as
soon as one member of the prepared family is a nonunit (so that `π` lies in the maximal ideal
of `B_𝔮`). -/
theorem fibrePoint_bijective (hV : IsFiniteLength A' (FibreRing A' P q))
    (hnot : ¬ ∀ i, IsUnit (a i)) : Function.Bijective (fibrePoint P q hV) :=
  ⟨fibrePoint_injective hV, fibrePoint_surjective hV hnot⟩

/-- Two ring maps out of the localizations at equal maximal ideals that agree on the image of
the base ring take the same value on a family of local elements. -/
theorem localization_apply_congr {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    (g : ∀ (p : Ideal R) [p.IsMaximal], Localization.AtPrime p)
    {q q' : Ideal R} [q.IsMaximal] [q'.IsMaximal] (h : q = q')
    (f : Localization.AtPrime q →+* C) (f' : Localization.AtPrime q' →+* C)
    (hb : ∀ b : R, f (algebraMap R (Localization.AtPrime q) b) =
      f' (algebraMap R (Localization.AtPrime q') b)) :
    f (g q) = f' (g q') := by
  subst h
  rw [IsLocalization.ringHom_ext q.primeCompl (RingHom.ext hb)]

/-- The localization of `A' ⊗_A B` at a maximal ideal `𝔮'` under a maximal ideal `𝔫` of `V` is
the localization of `A' ⊗_A B_𝔮` at the ideal under `𝔫`, compatibly with the maps from `B`. -/
theorem exists_algEquiv_localization_tensorLocalization
    (p : MaximalSpectrum (FibreRing A' P q)) (Q : MaximalSpectrum (A' ⊗[A] B))
    (hQ : p.asIdeal.comap (fibreMap A' P q) = Q.asIdeal) :
    haveI := P.underIdeal_isMaximal Q.asIdeal
    ∃ e : Localization.AtPrime Q.asIdeal ≃ₐ[A']
        Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk (fibreIdeal A' P q))),
      ∀ b : B, e (P.localMap Q.asIdeal (algebraMap B _ b)) =
        algebraMap (A' ⊗[A] Localization.AtPrime q) _
          (Algebra.TensorProduct.includeRight (algebraMap B (Localization.AtPrime q) b)) := by
  have := P.underIdeal_isMaximal Q.asIdeal
  let := (toTensorLocalization (A := A) A' q).toAlgebra
  let L := A' ⊗[A] Localization.AtPrime q
  let N := q.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B))
  have : IsLocalization N L := isLocalization_tensorLocalization
  let QL : Ideal L := p.asIdeal.comap (Ideal.Quotient.mk (fibreIdeal A' P q))
  have hQL : QL.comap (algebraMap (A' ⊗[A] B) L) = Q.asIdeal := hQ
  have : IsLocalization.AtPrime (Localization.AtPrime QL) Q.asIdeal := by
    have key : ∀ (J : Ideal (A' ⊗[A] B)) [J.IsPrime], J = Q.asIdeal →
        IsLocalization.AtPrime (Localization.AtPrime QL) J →
          IsLocalization.AtPrime (Localization.AtPrime QL) Q.asIdeal := by
      rintro _ _ rfl h
      exact h
    exact key _ hQL (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization N
      (Localization.AtPrime QL) QL)
  let eT : Localization.AtPrime Q.asIdeal ≃ₐ[A' ⊗[A] B] Localization.AtPrime QL :=
    IsLocalization.algEquiv Q.asIdeal.primeCompl _ _
  have heT (t : A' ⊗[A] B) : eT (algebraMap (A' ⊗[A] B) _ t) =
      algebraMap L (Localization.AtPrime QL) (algebraMap (A' ⊗[A] B) L t) := eT.commutes t
  have hA' (x : A') : eT.toRingEquiv (algebraMap A' (Localization.AtPrime Q.asIdeal) x) =
      algebraMap A' (Localization.AtPrime QL) x := by
    change eT _ = _
    rw [IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) (Localization.AtPrime Q.asIdeal), heT,
      IsScalarTower.algebraMap_apply A' L (Localization.AtPrime QL)]
    congr 1
    change toTensorLocalization (A := A) A' q (x ⊗ₜ 1) = x ⊗ₜ 1
    simp [toTensorLocalization]
  refine ⟨AlgEquiv.ofRingEquiv (f := eT.toRingEquiv) hA', fun b ↦ ?_⟩
  change eT (P.localMap Q.asIdeal (algebraMap B _ b)) = _
  rw [localMap_algebraMap, heT]
  rfl

omit [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
/-- The localization of `V` at a maximal ideal `𝔫` is the quotient by `π` of the localization of
`A' ⊗_A B_𝔮` at the ideal under `𝔫`. -/
theorem exists_algEquiv_localization_fibreRing (p : MaximalSpectrum (FibreRing A' P q)) :
    ∃ e : Localization.AtPrime p.asIdeal ≃ₐ[A']
        (Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk (fibreIdeal A' P q))) ⧸
          (fibreIdeal A' P q).map (algebraMap _
            (Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk (fibreIdeal A' P q)))))),
      ∀ x, e (algebraMap (FibreRing A' P q) _ (Ideal.Quotient.mk _ x)) =
        Ideal.Quotient.mk _ (algebraMap _ _ x) := by
  let QL := p.asIdeal.comap (Ideal.Quotient.mk (fibreIdeal A' P q))
  have : IsLocalization.AtPrime (Localization.AtPrime QL ⧸
      (fibreIdeal A' P q).map (algebraMap _ (Localization.AtPrime QL))) p.asIdeal :=
    isLocalization_quotient_atPrime QL (Localization.AtPrime QL) _ p.asIdeal rfl
  let e₀ : Localization.AtPrime p.asIdeal ≃ₐ[FibreRing A' P q] (Localization.AtPrime QL ⧸
      (fibreIdeal A' P q).map (algebraMap _ (Localization.AtPrime QL))) :=
    IsLocalization.algEquiv p.asIdeal.primeCompl _ _
  have hA' (x : A') : e₀.toRingEquiv (algebraMap A' (Localization.AtPrime p.asIdeal) x) =
      algebraMap A' _ x := by
    change e₀ _ = _
    rw [IsScalarTower.algebraMap_apply A' (FibreRing A' P q) (Localization.AtPrime p.asIdeal),
      e₀.commutes]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) hA', fun x ↦ ?_⟩
  change e₀ _ = _
  rw [e₀.commutes]
  rfl

/-- **The localization of `V` at a maximal ideal is `B'_{𝔮'} / π`, compatibly with
multiplication.** Let `𝔫` be a maximal ideal of `V = (A' ⊗_A B_𝔮)/π` and `𝔮'` the maximal ideal
of `B' = A' ⊗_A B` under it. For a family `y` of local elements of `B` there is an isomorphism
`V_𝔫 ≅ B'_{𝔮'} / π` of `A'`-algebras carrying `1 ⊗ y_𝔮` to the class of the image of
`y_{𝔮' ∩ B}`. -/
theorem exists_algEquiv_localization_fibreRing_quotient (hV : IsFiniteLength A' (FibreRing A' P q))
    (p : MaximalSpectrum (FibreRing A' P q)) (Q : MaximalSpectrum (A' ⊗[A] B))
    (hQ : p.asIdeal.comap (fibreMap A' P q) = Q.asIdeal)
    (y : ∀ (p : Ideal B) [p.IsMaximal], Localization.AtPrime p) :
    haveI := P.underIdeal_isMaximal Q.asIdeal
    ∃ e : Localization.AtPrime p.asIdeal ≃ₐ[A'] (Localization.AtPrime Q.asIdeal ⧸
        Ideal.span {P.localMap Q.asIdeal (P.parameter (underIdeal Q.asIdeal))}),
      e (algebraMap (FibreRing A' P q) (Localization.AtPrime p.asIdeal)
          (Ideal.Quotient.mk (fibreIdeal A' P q) (Algebra.TensorProduct.includeRight (y q)))) =
        Ideal.Quotient.mk _ (P.localMap Q.asIdeal (y (underIdeal Q.asIdeal))) := by
  have := P.underIdeal_isMaximal Q.asIdeal
  have hqQ : underIdeal Q.asIdeal = q := hQ ▸ underIdeal_comap_fibreMap hV p.asIdeal
  obtain ⟨e, he⟩ := exists_algEquiv_localization_tensorLocalization p Q hQ
  obtain ⟨eV, heV⟩ := exists_algEquiv_localization_fibreRing p
  set QL := p.asIdeal.comap (Ideal.Quotient.mk (fibreIdeal A' P q))
  have hB : ∀ b : B, ((e : Localization.AtPrime Q.asIdeal →+* Localization.AtPrime QL).comp
        (P.localMap Q.asIdeal)) (algebraMap B _ b) =
      ((algebraMap _ (Localization.AtPrime QL)).comp
        (Algebra.TensorProduct.includeRight (R := A) (A := A')
          (B := Localization.AtPrime q)).toRingHom) (algebraMap B _ b) := he
  have hparam := localization_apply_congr (fun p _ ↦ P.parameter p) hqQ _ _ hB
  have hy := localization_apply_congr y hqQ _ _ hB
  have hIdeal : (fibreIdeal A' P q).map (algebraMap _ (Localization.AtPrime QL)) =
      (Ideal.span {P.localMap Q.asIdeal (P.parameter (underIdeal Q.asIdeal))}).map
        (e : Localization.AtPrime Q.asIdeal →+* Localization.AtPrime QL) := by
    simp only [fibreIdeal, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z ↦ Ideal.span {z}) hparam.symm
  obtain ⟨eQ, heQ⟩ : ∃ eQ : (Localization.AtPrime Q.asIdeal ⧸
      Ideal.span {P.localMap Q.asIdeal (P.parameter (underIdeal Q.asIdeal))}) ≃ₐ[A']
        (Localization.AtPrime QL ⧸
          (fibreIdeal A' P q).map (algebraMap _ (Localization.AtPrime QL))),
      ∀ x, eQ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (e x) :=
    ⟨Ideal.quotientEquivAlg _ _ e hIdeal, fun _ ↦ rfl⟩
  exact ⟨eV.trans eQ.symm, eQ.injective ((eQ.apply_symm_apply _).trans ((heV _).trans
    ((congrArg (Ideal.Quotient.mk _) hy).symm.trans (heQ _).symm)))⟩

/-- **The determinant of multiplication on a localization of `V`.** With `𝔫`, `𝔮'` and `y` as
above, the determinant over `κ'` of multiplication by `1 ⊗ y_𝔮` on `V_𝔫` equals that of
multiplication by the image of `y_{𝔮' ∩ B}` on `B'_{𝔮'} / π`. -/
theorem det_localization_fibreRing (hV : IsFiniteLength A' (FibreRing A' P q))
    (p : MaximalSpectrum (FibreRing A' P q)) (Q : MaximalSpectrum (A' ⊗[A] B))
    (hQ : p.asIdeal.comap (fibreMap A' P q) = Q.asIdeal)
    (y : ∀ (p : Ideal B) [p.IsMaximal], Localization.AtPrime p)
    (hN : haveI := P.underIdeal_isMaximal Q.asIdeal
      IsFiniteLength A' (Localization.AtPrime Q.asIdeal ⧸
        Ideal.span {P.localMap Q.asIdeal (P.parameter (underIdeal Q.asIdeal))})) :
    FiniteLengthEndomorphism.det A' (FiniteLengthEndomorphism.isFiniteLength_localization hV p)
        ((LinearMap.lsmul (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)
          (algebraMap (FibreRing A' P q) (Localization.AtPrime p.asIdeal)
            (Ideal.Quotient.mk (fibreIdeal A' P q)
              (Algebra.TensorProduct.includeRight (y q))))).restrictScalars A') =
      haveI := P.underIdeal_isMaximal Q.asIdeal
      FiniteLengthEndomorphism.det A' hN
        ((LinearMap.lsmul (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal ⧸
          Ideal.span {P.localMap Q.asIdeal (P.parameter (underIdeal Q.asIdeal))})
          (P.localMap Q.asIdeal (y (underIdeal Q.asIdeal)))).restrictScalars A') := by
  have := P.underIdeal_isMaximal Q.asIdeal
  obtain ⟨e, he⟩ := exists_algEquiv_localization_fibreRing_quotient hV p Q hQ y
  exact FiniteLengthEndomorphism.det_lsmul_eq_of_algEquiv_quotient e he _ _

end Fibre

end AlgebraicGeometry.TameSymbolPreparation
