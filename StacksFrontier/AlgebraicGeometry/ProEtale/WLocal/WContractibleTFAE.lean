module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.WeaklyEtaleIndEtaleExtension
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.AlgebraicResidueExtensionWLocal
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.RetractionCharacterization
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField
public import StacksCore.Tactic.StacksAttribute

/-!
# Characterizations of w-contractible rings

A commutative ring `A` is w-contractible when every faithfully flat weakly étale `A`-algebra
admits a retraction. This file proves that the same property for the smaller class of
faithfully flat *ind-étale* algebras already implies it, and that both are equivalent to a
purely local-global condition: `Spec A` is w-local, `π₀(Spec A)` is extremally disconnected,
and the localization of `A` at every maximal ideal is strictly henselian.

The retraction property for ind-étale algebras implies the one for weakly étale algebras
because a weakly étale algebra becomes ind-étale after a faithfully flat ind-étale extension of
its target, and a retraction of the extension restricts to one of the original algebra. For the
converse direction a faithfully flat ind-étale algebra `B` is first replaced by a w-local
ind-Zariski extension `C` whose closed points lie exactly over the closed points of `Spec A`.
Over such a `C` strict henselianity of the local rings of `A` at its maximal ideals forces
`A → C` to identify local rings, which is the hypothesis under which w-locality of `Spec A`
together with extremal disconnectedness of `π₀(Spec A)` produces a retraction; composing with
`B → C` retracts `B`.

## Main results

* `AlgebraicGeometry.ProEtale.faithfullyFlat_of_quotient_bijective`: faithful flatness passes
  from `B` to an extension `C` of `B` that does not change the quotient by the ideal cutting out
  the closed points of `Spec A`.
* `AlgebraicGeometry.ProEtale.identifiesLocalRings_of_weaklyEtale_of_closedPoints`: a weakly
  étale algebra whose closed points lie over closed points of the base identifies local rings as
  soon as the base has strictly henselian local rings at its maximal ideals.
* `AlgebraicGeometry.ProEtale.isWContractible_of_indEtale_faithfullyFlat_retracts`: the
  retraction property for faithfully flat ind-étale algebras implies w-contractibility.
* `AlgebraicGeometry.ProEtale.nonempty_algHom_of_wLocal_extremallyDisconnected_strictlyHenselian`:
  the retraction property for faithfully flat ind-étale algebras from the local-global condition.
* `AlgebraicGeometry.ProEtale.wContractible_tfae`: the three equivalent characterizations.

## Implementation notes

Ind-étaleness is `StacksDraft.IndEtale`, which allows the base and the algebra to lie in
independent universes and which agrees with `(CommAlgCat.etale A).ind (CommAlgCat.of A B)` in a
common universe by `StacksDraft.indEtale_iff`; this is the spelling the rest of the chapter uses.

`faithfullyFlat_of_quotient_bijective` is phrased for an arbitrary tower `A → B → C` together
with the bijectivity of `B ⧸ I·B → C ⧸ I·C`, which is one of the clauses produced by the w-local
extension of Tag 097A. Stated that way it also covers the closed-point lifting performed inline
inside `nonempty_algHom_of_wLocal_extremallyDisconnected`.

## References

* [Stacks Project, Tag 0981](https://stacks.math.columbia.edu/tag/0981)
* [Stacks Project, Tag 0982](https://stacks.math.columbia.edu/tag/0982)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

universe u

/-- Let `A → B` be faithfully flat and let `I` be an ideal of `A` whose zero locus is the set of
closed points of `Spec A`. If a flat extension `B → C` leaves the quotient by the extension of
`I` unchanged, then `A → C` is again faithfully flat: every closed point of `Spec A` lifts to
`Spec B` by faithful flatness, hence to `Spec C` through that isomorphism of quotients, and a
flat ring map whose image contains the closed points is faithfully flat. -/
theorem faithfullyFlat_of_quotient_bijective (A B C : Type u) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (I : Ideal A)
    (hzero : PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (hff : Module.FaithfullyFlat A B)
    (hquot : Function.Bijective
      (algebraMap (B ⧸ Ideal.map (algebraMap A B) I)
        (C ⧸ Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) I))))
    (hflat : Module.Flat A C) : Module.FaithfullyFlat A C := by
  have hffAB : (algebraMap A B).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr hff
  set J : Ideal B := Ideal.map (algebraMap A B) I with hJ
  set K : Ideal C := Ideal.map (algebraMap B C) J
  have hquotFactor : (Ideal.Quotient.mk K).comp (algebraMap A C) =
      (algebraMap (B ⧸ J) (C ⧸ K)).comp ((Ideal.Quotient.mk J).comp (algebraMap A B)) := by
    rw [IsScalarTower.algebraMap_eq A B C]
    exact RingHom.ext fun _ => rfl
  have hlift : ∀ a : PrimeSpectrum A, IsClosed ({a} : Set (PrimeSpectrum A)) →
      a ∈ Set.range (PrimeSpectrum.comap (algebraMap A C)) := by
    intro a ha
    obtain ⟨qB, hqBspec⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hffAB).2 a
    have hIa : I ≤ a.asIdeal := (PrimeSpectrum.mem_zeroLocus a (I : Set A)).mp
      (by rw [hzero]; exact mem_closedPoints_iff.mpr ha)
    have hqBcon : qB.asIdeal.comap (algebraMap A B) = a.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hqBspec
    have hJq : J ≤ qB.asIdeal := by
      rwa [hJ, Ideal.map_le_iff_le_comap, hqBcon]
    let qbarB : Ideal (B ⧸ J) := Ideal.map (Ideal.Quotient.mk J) qB.asIdeal
    have : qbarB.IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    let e : (B ⧸ J) ≃+* (C ⧸ K) := RingEquiv.ofBijective (algebraMap (B ⧸ J) (C ⧸ K)) hquot
    let qbarC : Ideal (C ⧸ K) := qbarB.comap e.symm.toRingHom
    have : qbarC.IsPrime := Ideal.comap_isPrime e.symm.toRingHom qbarB
    let qC : Ideal C := qbarC.comap (Ideal.Quotient.mk K)
    have : qC.IsPrime := Ideal.comap_isPrime (Ideal.Quotient.mk K) qbarC
    have hqbarBcomap : qbarB.comap (Ideal.Quotient.mk J) = qB.asIdeal := by
      rw [show qbarB = Ideal.map (Ideal.Quotient.mk J) qB.asIdeal from rfl,
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        show Ideal.comap (Ideal.Quotient.mk J) ⊥ = J from Ideal.mk_ker]
      exact sup_eq_left.mpr hJq
    have hqbarCcomap : qbarC.comap (algebraMap (B ⧸ J) (C ⧸ K)) = qbarB := by
      rw [show qbarC = qbarB.comap e.symm.toRingHom from rfl, Ideal.comap_comap,
        show e.symm.toRingHom.comp (algebraMap (B ⧸ J) (C ⧸ K)) = RingHom.id (B ⧸ J) from
          RingHom.ext e.symm_apply_apply]
      rfl
    have hcontract : qC.comap (algebraMap A C) = a.asIdeal := by
      rw [show qC = qbarC.comap (Ideal.Quotient.mk K) from rfl, Ideal.comap_comap, hquotFactor,
        ← Ideal.comap_comap, hqbarCcomap, ← Ideal.comap_comap, hqbarBcomap, hqBcon]
    exact ⟨⟨qC, ‹qC.IsPrime›⟩, PrimeSpectrum.ext hcontract⟩
  exact RingHom.faithfullyFlat_algebraMap_iff.mp
    (((faithfullyFlat_tfae00HQ (algebraMap A C)
      (RingHom.flat_algebraMap_iff.mpr hflat)).out 1 3).mpr hlift)

/-- A weakly étale algebra `C` over a ring `A` whose local rings at maximal ideals are strictly
henselian identifies local rings as soon as every closed point of `Spec C` lies over a closed
point of `Spec A`. Identifying local rings may be checked at the maximal ideals of `C`, and over
a maximal ideal `m` of `C` the local map `A_{m ∩ A} → C_m` of local rings is weakly étale with
strictly henselian source, hence bijective. -/
theorem identifiesLocalRings_of_weaklyEtale_of_closedPoints (A C : Type u) [CommRing A]
    [CommRing C] [Algebra A C] (hwe : Algebra.WeaklyEtale A C)
    (hsh : ∀ (m : Ideal A) [m.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime m))
    (hclosed : closedPoints (PrimeSpectrum C) ⊆
      PrimeSpectrum.comap (algebraMap A C) ⁻¹' closedPoints (PrimeSpectrum A)) :
    Algebra.IdentifiesLocalRings A C := by
  have : Algebra.WeaklyEtale A C := hwe
  have hmax : ∀ (m : Ideal C) [m.IsMaximal],
      Function.Bijective (Localization.localRingHom (m.comap (algebraMap A C)) m
        (algebraMap A C) rfl) := by
    intro m hm
    have hmclosed : (⟨m, hm.isPrime⟩ : PrimeSpectrum C) ∈ closedPoints (PrimeSpectrum C) :=
      mem_closedPoints_iff.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm)
    have : (m.comap (algebraMap A C)).IsPrime := Ideal.IsPrime.comap (algebraMap A C)
    have hnmax : (m.comap (algebraMap A C)).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal
        (⟨m.comap (algebraMap A C), inferInstance⟩ : PrimeSpectrum A)).mp
        (mem_closedPoints_iff.mp (hclosed hmclosed))
    set n : Ideal A := m.comap (algebraMap A C)
    let An := Localization.AtPrime n
    let Cm := Localization.AtPrime m
    let : Algebra An Cm := (Localization.localRingHom n m (algebraMap A C) rfl).toAlgebra
    let : Algebra A Cm := ((algebraMap C Cm).comp (algebraMap A C)).toAlgebra
    let : SMul A Cm := (inferInstance : Algebra A Cm).toSMul
    have : IsScalarTower A C Cm := IsScalarTower.of_algebraMap_eq' rfl
    let : SMul An Cm := (inferInstance : Algebra An Cm).toSMul
    have : IsScalarTower A An Cm :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun c =>
        (Localization.localRingHom_to_map n m (algebraMap A C) rfl c).symm)
    have : Algebra.WeaklyEtale A An :=
      (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} A).1 An n.primeCompl
    have : Algebra.WeaklyEtale C Cm :=
      (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} C).1 Cm m.primeCompl
    have : StrictlyHenselianLocalRing An := hsh n
    have : IsLocalHom (algebraMap An Cm) :=
      Localization.isLocalHom_localRingHom n m (algebraMap A C) rfl
    exact bijective_algebraMap_of_weaklyEtale_of_isLocalHom An Cm
      (weaklyEtale_of_comp A An Cm inferInstance (Algebra.WeaklyEtale.trans A C Cm))
  exact identifiesLocalRings_of_isMaximal (algebraMap A C) hmax

/-- If every faithfully flat ind-étale algebra over `A` admits a retraction, then `A` is
w-contractible. A faithfully flat weakly étale algebra `B` admits a faithfully flat ind-étale
extension `B → B'` with `A → B'` ind-étale, and a retraction of `B'` restricts to one of `B`. -/
theorem isWContractible_of_indEtale_faithfullyFlat_retracts (A : Type u) [CommRing A]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      StacksDraft.IndEtale A B → Nonempty (B →ₐ[A] A)) :
    ProetaleWContractible.IsWContractible.{u, u} A := by
  intro B _ inst hwe hff
  have halg : ((algebraMap A B).toAlgebra : Algebra A B) = inst :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hweB : let := (algebraMap A B).toAlgebra; Algebra.WeaklyEtale A B := by
    rw [halg]
    exact (Algebra.weaklyEtale_iff A B).mpr hwe
  obtain ⟨B', hB', g, hgff, -, hAgind⟩ :=
    exists_faithfullyFlat_indEtale_extension (algebraMap A B) hweB
  let : CommRing B' := hB'
  let : Algebra A B' := (g.comp (algebraMap A B)).toAlgebra
  have hffAB' : Module.FaithfullyFlat A B' :=
    RingHom.faithfullyFlat_algebraMap_iff.mp (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff) hgff)
  obtain ⟨r⟩ := h B' hffAB' (indEtale_of_indEtaleUnder A B' hAgind)
  exact ⟨{ toRingHom := (r : B' →+* A).comp g
           commutes' := fun a => r.commutes a }⟩

/-- If `Spec A` is w-local, `π₀(Spec A)` is extremally disconnected and the localization of `A`
at each maximal ideal is strictly henselian, then every faithfully flat ind-étale `A`-algebra `B`
admits a retraction. Tag 097A replaces `B` by a w-local ind-Zariski extension `C` whose closed
points lie exactly over the closed points of `Spec A`; strict henselianity then makes `A → C`
identify local rings, so `C` retracts onto `A` by Tag 09AZ, and `B → C` composed with that
retraction retracts `B`. -/
theorem nonempty_algHom_of_wLocal_extremallyDisconnected_strictlyHenselian (A : Type u)
    [CommRing A] [WLocalSpace (PrimeSpectrum A)]
    (hED : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)))
    (hsh : ∀ (m : Ideal A) [m.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime m))
    (B : Type u) [CommRing B] [Algebra A B] (hff : Module.FaithfullyFlat A B)
    (hie : StacksDraft.IndEtale A B) : Nonempty (B →ₐ[A] A) := by
  have hwe : Algebra.WeaklyEtale A B := Algebra.weaklyEtale_of_ind_etale hie
  obtain ⟨I, hzero⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp
    (WLocalSpace.isClosed_closedPoints (X := PrimeSpectrum A))
  obtain ⟨C, hC, algBC, hIndBC, hquotBij, hW_C, -, hclosedC⟩ :=
    exists_isIndZariski_wLocal_of_isAlgebraic_residueField (algebraMap A B) I hzero.symm
      (fun q _ => (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A B hwe
        (q.comap (algebraMap A B)) q rfl).2)
  let : CommRing C := hC
  let : Algebra B C := algBC
  let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  have hACind : StacksDraft.IndEtale A C :=
    StacksDraft.indEtale_comp hie (indEtale_of_isIndZariski B C hIndBC)
  have hlocalAC : Algebra.IdentifiesLocalRings A C :=
    identifiesLocalRings_of_weaklyEtale_of_closedPoints A C
      (Algebra.weaklyEtale_of_ind_etale hACind) hsh hclosedC.subset
  have hffAC : Module.FaithfullyFlat A C :=
    faithfullyFlat_of_quotient_bijective A B C I hzero.symm hff hquotBij
      (flat_of_identifiesLocalRings A C hlocalAC)
  obtain ⟨r⟩ := nonempty_algHom_of_wLocal_extremallyDisconnected.{u, u} A hED C hffAC hlocalAC
  exact ⟨r.comp (IsScalarTower.toAlgHom A B C)⟩

/-- **Stacks 0982.** For a commutative ring `A` the following are equivalent: `A` is
w-contractible; every faithfully flat ind-étale `A`-algebra admits a retraction; `Spec A` is
w-local, `π₀(Spec A)` is extremally disconnected and the localization of `A` at every maximal
ideal is strictly henselian. -/
@[stacks 0982]
theorem wContractible_tfae (A : Type u) [CommRing A] :
    List.TFAE
      [ProetaleWContractible.IsWContractible.{u, u} A,
        ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          StacksDraft.IndEtale A B → Nonempty (B →ₐ[A] A),
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
            ∀ (m : Ideal A) [m.IsMaximal],
              StrictlyHenselianLocalRing (Localization.AtPrime m)] := by
  tfae_have h12 : 1 → 2 := fun h B _ _ hff hie =>
    indEtale_faithfullyFlat_retracts_of_isWContractible A h B hff hie
  tfae_have h21 : 2 → 1 := isWContractible_of_indEtale_faithfullyFlat_retracts A
  tfae_have h23 : 2 → 3 :=
    wLocal_extremallyDisconnected_strictlyHenselian_of_indEtale_faithfullyFlat_retracts A
  tfae_have h32 : 3 → 2 := by
    rintro ⟨_, hED, hsh⟩ B _ _ hff hie
    exact nonempty_algHom_of_wLocal_extremallyDisconnected_strictlyHenselian A hED hsh B hff hie
  tfae_finish

end AlgebraicGeometry.ProEtale

end
