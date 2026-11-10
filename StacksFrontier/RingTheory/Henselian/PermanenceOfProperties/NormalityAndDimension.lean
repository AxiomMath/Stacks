module

public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties.FlatnessAndReducedness
import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GeometricBranches
import StacksFrontier.RingTheory.Depth.UnqualifiedDepth

/-!
# Permanence under henselization: normality and dimension

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

06DI, 06LK, and the first preliminaries for 06LJ.

## Tag 06DI — Normality of henselizations

A local ring is a normal domain if and only if its henselization is a normal domain, and if and
only if any strict henselization associated to a separable closure of its residue field is a
normal domain.

### Main definitions

Henselizations and strict henselizations are expressed by
`IsLocalRing.IsHenselization`.

### Main results

* `isNormalDomain_tfae_henselization_strictHenselization` gives the three equivalent
  normal-domain conditions.

### Implementation notes

A normal domain is expressed as the conjunction of `IsDomain` and `IsIntegrallyClosed`. The
strict henselization is represented as a henselization whose prescribed residue field is a
separable closure of the residue field of the base local ring.

### References

* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)

## Tag 06LK — Krull dimension of henselizations

The Krull dimension of a local ring agrees with the Krull dimensions of its henselization and
its strict henselization.

### Main definitions

There are no new definitions.

### Main results

* `ringKrullDim_eq_henselization_eq_strictHenselization`: henselization and strict
  henselization preserve the Krull dimension of a local ring.

### Implementation notes

Henselizations are represented by `IsLocalRing.IsHenselization`. A strict henselization is a
henselization whose residue field is a separable closure of the residue field of the original
ring. The chain of equalities in the source is represented by a conjunction of two equalities.

### References

* [Stacks Project, Tag 06LK](https://stacks.math.columbia.edu/tag/06LK)

## Tag 06LJ — Preliminaries

The first private lemmas used for Tag 06LJ: Noetherianity of henselizations, their
maximal-ideal-adic completions, and flatness of these completions. The theorem itself is in
`StacksFrontier.RingTheory.Henselian.PermanenceOfProperties.NoetherianCompletions`.

-/

@[expose] public section

/-! ### Stacks Tag 06DI -/

section

section

universe u v

open CategoryTheory CategoryTheory.Limits

private theorem isNormalRing_of_isDomain_and_isIntegrallyClosed
    (R : Type*) [CommRing R] (h : IsDomain R ∧ IsIntegrallyClosed R) :
    IsNormalRing R := by
  have : IsDomain R := h.1
  have : IsIntegrallyClosed R := h.2
  intro p hp
  exact ⟨IsLocalization.isDomain_of_local_atPrime hp,
    isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p)
      (M := p.primeCompl) p.primeCompl_le_nonZeroDivisors⟩

private theorem isDomain_and_isIntegrallyClosed_of_isNormalRing
    (R : Type*) [CommRing R] [IsLocalRing R] (h : IsNormalRing R) :
    IsDomain R ∧ IsIntegrallyClosed R :=
  h.of_isLocalRing

private theorem isDomain_and_isIntegrallyClosed_of_faithfullyFlat
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] [Module.FaithfullyFlat R S]
    (h : IsDomain S ∧ IsIntegrallyClosed S) :
    IsDomain R ∧ IsIntegrallyClosed R := by
  have hS : IsNormalRing S := isNormalRing_of_isDomain_and_isIntegrallyClosed S h
  have hR : IsNormalRing R :=
    isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat hS
  exact isDomain_and_isIntegrallyClosed_of_isNormalRing R hR

private theorem isLocalHom_of_isHenselization_06di
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [IsLocalRing.IsHenselization R L S] : IsLocalHom (algebraMap R S) := by
  obtain ⟨e, he⟩ :=
    (inferInstance : IsLocalRing.IsHenselization R L S).exists_residueFieldEquiv
  let f : R →+* IsLocalRing.ResidueField S :=
    e.toRingHom.comp ((algebraMap (IsLocalRing.ResidueField R) L).comp
      (IsLocalRing.residue R))
  have hf : IsLocalHom f := by
    dsimp [f]
    infer_instance
  have hcomp : (IsLocalRing.residue S).comp (algebraMap R S) = f := by
    ext x
    exact (he x).symm
  rw [← hcomp] at hf
  exact isLocalHom_of_comp (algebraMap R S) (IsLocalRing.residue S)

private noncomputable def directLimitCocone {J : Type u} [Preorder J]
    (F : J ⥤ CommRingCat.{u}) : Cocone F :=
  { pt := CommRingCat.of (Ring.DirectLimit (fun j => F.obj j)
      (fun i j h => (F.map (homOfLE h)).hom))
    ι.app j := CommRingCat.ofHom (Ring.DirectLimit.of (fun j => F.obj j)
      (fun i j h => (F.map (homOfLE h)).hom) j)
    ι.naturality i j f := by
      apply CommRingCat.hom_ext
      exact RingHom.ext fun x => Ring.DirectLimit.of_f (G := fun j => F.obj j)
        (f := fun i j h => (F.map (homOfLE h)).hom) (leOfHom f) x }

private noncomputable def directLimitCoconeIsColimit {J : Type u} [Preorder J]
    (F : J ⥤ CommRingCat.{u}) : IsColimit (directLimitCocone F) :=
  { desc := fun s => CommRingCat.ofHom
      (Ring.DirectLimit.lift (fun j => F.obj j)
        (fun i j h => (F.map (homOfLE h)).hom) s.pt
        (fun j => (s.ι.app j).hom)
        (fun i j h x => ConcreteCategory.congr_hom (s.w (homOfLE h)) x))
    fac := fun s j => by
      apply CommRingCat.hom_ext
      exact RingHom.ext fun x => Ring.DirectLimit.lift_of (G := fun j => F.obj j)
        (f := fun i j h => (F.map (homOfLE h)).hom) s.pt
        (fun j => (s.ι.app j).hom)
        (fun i j h x => ConcreteCategory.congr_hom (s.w (homOfLE h)) x) j x
    uniq := fun s m hm => by
      apply CommRingCat.hom_ext
      apply Ring.DirectLimit.hom_ext (G := fun j => F.obj j)
        (f := fun i j h => (F.map (homOfLE h)).hom)
      intro j
      exact RingHom.ext fun x => (ConcreteCategory.congr_hom (hm j) x).trans
        (Ring.DirectLimit.lift_of (G := fun j => F.obj j)
          (f := fun i j h => (F.map (homOfLE h)).hom) s.pt
          (fun j => (s.ι.app j).hom)
          (fun i j h x => ConcreteCategory.congr_hom (s.w (homOfLE h)) x) j x).symm }

private theorem isNormalRing_of_isColimit_directed
    {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, IsNormalRing (F.obj j)) : IsNormalRing c.pt := by
  let G : J → Type u := fun j => F.obj j
  let φ : ∀ i j : J, i ≤ j → G i →+* G j :=
    fun i j h => (F.map (homOfLE h)).hom
  have hdir : DirectedSystem G (fun i j h => φ i j h) :=
    { map_self := by
        intro i x
        change (F.map (𝟙 i)).hom x = x
        rw [F.map_id]
        rfl
      map_map := by
        intro k j i hij hjk x
        change ((F.map (homOfLE hij) ≫ F.map (homOfLE hjk)).hom) x = _
        rw [← F.map_comp]
        rfl }
  exact IsNormalRing.congr
    ((directLimitCoconeIsColimit F).coconePointUniqueUpToIso hc).commRingCatIsoToRingEquiv
    (directLimit_isNormalRing G φ hdir hF)

private theorem isNormalRing_of_isColimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, IsNormalRing (F.obj j)) : IsNormalRing c.pt := by
  obtain ⟨α, _, _, _, H, _⟩ := IsFiltered.exists_directed J
  exact isNormalRing_of_isColimit_directed (H ⋙ F) (c.whisker H)
    ((Functor.Final.isColimitWhiskerEquiv H c).symm hc) (fun j => hF (H.obj j))

private noncomputable def isColimit_forget₂_commRingCat
    (R : Type u) [CommRing R]
    {J : Type*} [Category* J] [IsConnected J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{u} R) CommRingCat).mapCocone c) := by
  have : PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} R) CommRingCat) := by
    change PreservesColimitsOfShape J
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R))
    infer_instance
  exact isColimitOfPreserves _ hc

/-- **Normality ascends along an ind-étale algebra.** An ind-étale `R`-algebra is a filtered
colimit of étale, hence smooth, `R`-algebras, each normal over a normal `R`; and normality passes
to a filtered colimit of rings. -/
theorem isNormalRing_of_ind_etale
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (hR : IsNormalRing R)
    (hS : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S)) :
    IsNormalRing S := by
  obtain ⟨J, _, _, pres, hpres⟩ := hS
  have : IsConnected J := IsFiltered.isConnected J
  exact isNormalRing_of_isColimit
    (pres.diag ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat)
    ((forget₂ (CommAlgCat.{u} R) CommRingCat).mapCocone pres.cocone)
    (isColimit_forget₂_commRingCat R pres.diag pres.cocone pres.isColimit)
    (fun j => by
      have : Algebra.Etale R (pres.diag.obj j) := hpres j
      exact Algebra.isNormalRing_of_smooth R (pres.diag.obj j) hR)

@[ega "IV 18.6.9" "(i), special case"]
private theorem henselization_normal_iff
    (R S : Type u) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [IsLocalRing.IsHenselization R L S] :
    (IsDomain S ∧ IsIntegrallyClosed S) ↔ (IsDomain R ∧ IsIntegrallyClosed R) := by
  constructor
  · have : Module.FaithfullyFlat R S := IsLocalRing.IsHenselization.faithfullyFlat (L := L)
    exact isDomain_and_isIntegrallyClosed_of_faithfullyFlat R S
  · intro hR
    exact isDomain_and_isIntegrallyClosed_of_isNormalRing S
      (isNormalRing_of_ind_etale R S
        (isNormalRing_of_isDomain_and_isIntegrallyClosed R hR)
        (IsLocalRing.IsHenselization.ind_etale_of_universe_le L))

/-- Normality of a local ring, its henselization, and its strict henselization are equivalent. -/
@[stacks 06DI, ega "IV 18.6.9" "(i), special case", ega "IV 18.8.12" "(i), special case"]
public theorem isNormalDomain_tfae_henselization_strictHenselization
    (R Rh Rsh : Type u) [CommRing R] [CommRing Rh] [CommRing Rsh]
    [IsLocalRing R] [IsLocalRing Rh] [IsLocalRing Rsh]
    [Algebra R Rh] [Algebra R Rsh]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) Rh]
    (κsep : Type v) [Field κsep] [Algebra (IsLocalRing.ResidueField R) κsep]
    [IsSepClosure (IsLocalRing.ResidueField R) κsep]
    [IsLocalRing.IsHenselization R κsep Rsh] :
    List.TFAE [IsDomain R ∧ IsIntegrallyClosed R,
      IsDomain Rh ∧ IsIntegrallyClosed Rh,
      IsDomain Rsh ∧ IsIntegrallyClosed Rsh] := by
  tfae_have 1 ↔ 2 := (henselization_normal_iff R Rh (IsLocalRing.ResidueField R)).symm
  tfae_have 1 ↔ 3 := (henselization_normal_iff R Rsh κsep).symm
  tfae_finish

end

end

/-! ### Stacks Tag 06LK -/

section

section

@[expose] public section

open CategoryTheory IsLocalRing

universe u v

public lemma ringKrullDim_le_of_ind_etale
    (R H : Type u) [CommRing R] [CommRing H] [Algebra R H]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R H)) :
    ringKrullDim H ≤ ringKrullDim R := by
  rw [ringKrullDim, ringKrullDim]
  have h := Order.krullDim_le_of_krullDim_preimage_le'
    (m := 0) (PrimeSpectrum.comap (algebraMap R H))
      (fun _ _ hxy => Ideal.comap_mono hxy)
  suffices hf : ∀ p : PrimeSpectrum R,
      Order.krullDim (PrimeSpectrum.comap (algebraMap R H) ⁻¹' {p}) ≤ (0 : WithBot ℕ∞) by
    convert h hf using 1
    simp
  intro p
  apply Order.krullDim_nonpos_iff_forall_isMax.mpr
  intro q q' hqq'
  by_contra hnle
  obtain ⟨x, hxq', hxq⟩ := Set.not_subset.mp hnle
  obtain ⟨J, _, _, pres, hstage⟩ := hind
  let P : CommAlgCat R := CommAlgCat.of R (Polynomial R)
  let a : P ⟶ CommAlgCat.of R H := CommAlgCat.ofHom (Polynomial.aeval x)
  let : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  have : CategoryTheory.IsFinitelyPresentable.{u} P := by
    refine (CategoryTheory.isCardinalPresentable_iff_of_isEquivalence P Cardinal.aleph0
      (commAlgCatEquivUnder (CommRingCat.of R)).functor).mp ?_
    apply CommRingCat.isFinitelyPresentable_under
    change (algebraMap R (Polynomial R)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  obtain ⟨j, ψ, hψ⟩ := CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit
    pres.isColimit a
  let y : pres.diag.obj j := ψ.hom Polynomial.X
  have hy : (pres.ι.app j).hom y = x := by
    change (CommAlgCat.Hom.hom (ψ ≫ pres.ι.app j)) Polynomial.X = x
    rw [hψ]
    exact Polynomial.aeval_X x
  let Q : Ideal (pres.diag.obj j) := q.1.asIdeal.comap (pres.ι.app j).hom
  let Q' : Ideal (pres.diag.obj j) := q'.1.asIdeal.comap (pres.ι.app j).hom
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hQle : Q ≤ Q' := Ideal.comap_mono hqq'
  have hunder : Q.under R = Q'.under R := by
    change q.1.asIdeal.comap ((pres.ι.app j).hom.toRingHom.comp
      (algebraMap R (pres.diag.obj j))) = q'.1.asIdeal.comap
      ((pres.ι.app j).hom.toRingHom.comp (algebraMap R (pres.diag.obj j)))
    rw [show (pres.ι.app j).hom.toRingHom.comp (algebraMap R (pres.diag.obj j)) =
      algebraMap R H by ext r; exact (pres.ι.app j).hom.commutes r]
    exact congrArg PrimeSpectrum.asIdeal (q.2.trans q'.2.symm)
  have hQQ' : Q = Q' := Algebra.QuasiFinite.eq_of_le_of_under_eq Q Q' hQle hunder
  apply hxq
  rw [← hy]
  have hyq' : y ∈ Q' := by simpa [Q', hy] using hxq'
  exact (hQQ' ▸ hyq' : y ∈ Q)

public lemma ringKrullDim_le_of_faithfullyFlat
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] : ringKrullDim A ≤ ringKrullDim B := by
  apply ringKrullDim_le_of_goingDown (algebraMap A B) ?_
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  intro p p' hp hp' hle q' hq' hqover
  let : p.IsPrime := hp
  let : p'.IsPrime := hp'
  let : q'.IsPrime := hq'
  let : q'.LiesOver p' := ⟨hqover.symm⟩
  obtain ⟨q, hqle, hqprime, hqover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := p') q' hle
  exact ⟨q, hqprime, hqle, hqover.over.symm⟩

/-- A local ring and any of its henselizations have the same Krull dimension. -/
private theorem ringKrullDim_eq_of_isHenselization
    (R S : Type u) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    (L : Type v) [Field L] [Algebra (ResidueField R) L] [IsHenselization R L S] :
    ringKrullDim R = ringKrullDim S := by
  have : IsLocalHom (algebraMap R S) := IsHenselization.isLocalHom (L := L)
  have : Module.FaithfullyFlat R S :=
    (faithfullyFlat_and_map_maximalIdeal_of_isHenselization (R := R) (L := L) (S := S)).1
  exact le_antisymm (ringKrullDim_le_of_faithfullyFlat R S)
    (ringKrullDim_le_of_ind_etale R S
      (IsHenselization.ind_etale_of_universe_le (R := R) (L := L) (Rh := S)))

/-- A local ring, its henselization, and its strict henselization have equal Krull dimension. -/
@[stacks 06LK, sga "5 I 3.1.3" "more general"]
public theorem ringKrullDim_eq_henselization_eq_strictHenselization
    (R Rh Rsh : Type u)
    [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (κpsep : Type v) [Field κpsep] [Algebra (ResidueField R) κpsep]
    [IsSepClosure (ResidueField R) κpsep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R κpsep Rsh] :
    ringKrullDim R = ringKrullDim Rh ∧ ringKrullDim Rh = ringKrullDim Rsh := by
  have : IsLocalHom (algebraMap R Rh) := IsHenselization.isLocalHom (L := ResidueField R)
  have : IsLocalHom (algebraMap R Rsh) := IsHenselization.isLocalHom (L := κpsep)
  exact ⟨ringKrullDim_eq_of_isHenselization R Rh (ResidueField R),
    (ringKrullDim_eq_of_isHenselization R Rh (ResidueField R)).symm.trans
      (ringKrullDim_eq_of_isHenselization R Rsh κpsep)⟩

end

end

end

/-! ### Stacks Tag 06LJ -/

section

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

private theorem isNoetherianRing_of_henselization.{u, v}
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    [IsHenselization R L S] [IsNoetherianRing S] : IsNoetherianRing R := by
  have := IsHenselization.faithfullyFlat (R := R) (L := L) (Rh := S)
  exact descent_noetherian (algebraMap R S)
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) inferInstance

private theorem adicCompletion_isNoetherianRing_of_fg
    {R : Type*} [CommRing R] [IsLocalRing R] (hfg : (maximalIdeal R).FG) :
    IsNoetherianRing (AdicCompletion (maximalIdeal R) R) := by
  have := AdicCompletion.isLocalRing_of_fg hfg
  apply complete_local_ring_noetherian
  · exact AdicCompletion.isAdicComplete_of_fg hfg
  · rw [AdicCompletion.maximalIdeal_eq_map_of_fg hfg]
    exact hfg.map _

private theorem adicCompletion_completeLocal_of_fg
    {R : Type*} [CommRing R] [IsLocalRing R] (hfg : (maximalIdeal R).FG) :
    ∃ hlocal : IsLocalRing (AdicCompletion (maximalIdeal R) R),
      letI := hlocal
      IsNoetherianRing (AdicCompletion (maximalIdeal R) R) ∧
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R))
        (AdicCompletion (maximalIdeal R) R) :=
  ⟨AdicCompletion.isLocalRing_of_fg hfg,
    adicCompletion_isNoetherianRing_of_fg hfg, AdicCompletion.isAdicComplete_of_fg hfg⟩

private theorem exists_adicCompletion_equiv_of_quotient_equiv
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hIJ : I.map f ≤ J)
    (he : ∀ n : ℕ, ∃ e : (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n),
      ∀ x : R, e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x)) :
    ∃ e : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ x : R, e (algebraMap R (AdicCompletion I R) x) =
        algebraMap S (AdicCompletion J S) (f x) := by
  classical
  choose e he using he
  have hnaturality {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
      e m (Ideal.Quotient.factorPow I hmn x) =
        Ideal.Quotient.factorPow J hmn (e n x) := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, he]
  have hmap (n : ℕ) (x : AdicCompletion I R) :
      AdicCompletion.evalₐ J n (adicCompletionMap f I J hIJ x) =
        e n (AdicCompletion.evalₐ I n x) := by
    rw [adicCompletionMap_evalₐ]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    rw [← hr, Ideal.quotientMap_mk, he]
  let g : AdicCompletion J S →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I
      (fun n => (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom)
      (fun {m n} hmn => by
        ext x
        apply (e m).injective
        change e m (Ideal.Quotient.factorPow I hmn
            ((e n).symm (AdicCompletion.evalₐ J n x))) =
          e m ((e m).symm (AdicCompletion.evalₐ J m x))
        rw [hnaturality, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
          AdicCompletion.factorPow_evalₐ])
  have hg (n : ℕ) (x : AdicCompletion J S) :
      AdicCompletion.evalₐ I n (g x) = (e n).symm (AdicCompletion.evalₐ J n x) :=
    AdicCompletion.evalₐ_liftRingHom I _ _ n x
  have hleft : Function.LeftInverse g (adicCompletionMap f I J hIJ) := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hg, hmap, RingEquiv.symm_apply_apply]
  have hright : Function.RightInverse g (adicCompletionMap f I J hIJ) := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hmap, hg, RingEquiv.apply_symm_apply]
  refine ⟨RingEquiv.ofBijective (adicCompletionMap f I J hIJ)
    ⟨hleft.injective, hright.surjective⟩, fun x => ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ J n (adicCompletionMap f I J hIJ
    (algebraMap R (AdicCompletion I R) x)) = _
  rw [hmap]
  simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of] using he n x

open CategoryTheory CategoryTheory.Limits in
private theorem exists_rep_fin_of_isColimit
    {R : Type*} [CommRing R] {J : Type*} [Category J] [IsFiltered J]
    {F : J ⥤ CommAlgCat R} (c : Cocone F) (hc : IsColimit c)
    {n : ℕ} (x : Fin n → c.pt) :
    ∃ j : J, ∃ y : Fin n → F.obj j, ∀ i, (c.ι.app j).hom (y i) = x i := by
  classical
  have : Nonempty J := IsFiltered.nonempty
  let T (j : J) : Subalgebra R c.pt := (c.ι.app j).hom.range
  have hdir : Directed (· ≤ ·) T := by
    have hle {i j : J} (f : i ⟶ j) : T i ≤ T j := by
      rintro y ⟨a, rfl⟩
      exact ⟨(F.map f).hom a, ConcreteCategory.congr_hom (c.w f) a⟩
    exact fun i j => ⟨IsFiltered.max i j,
      hle (IsFiltered.leftToMax i j), hle (IsFiltered.rightToMax i j)⟩
  have htop : ⨆ j, T j = ⊤ := by
    let U := ⨆ j, T j
    have hmem (j : J) (y : F.obj j) : (c.ι.app j).hom y ∈ U :=
      le_iSup T j ⟨y, rfl⟩
    let d : Cocone F :=
      { pt := CommAlgCat.of R U
        ι.app j := CommAlgCat.ofHom ((c.ι.app j).hom.codRestrict U (hmem j))
        ι.naturality i j f := by
          apply CommAlgCat.hom_ext
          ext a
          exact Subtype.ext (ConcreteCategory.congr_hom (c.w f) a) }
    have hid : hc.desc d ≫ CommAlgCat.ofHom U.val = 𝟙 _ := by
      refine hc.hom_ext fun j => ?_
      rw [← Category.assoc, hc.fac, Category.comp_id]
      apply CommAlgCat.hom_ext
      ext a
      rfl
    refine eq_top_iff.mpr fun z _ => ?_
    have hz : U.val ((hc.desc d).hom z) = z := ConcreteCategory.congr_hom hid z
    exact hz ▸ ((hc.desc d).hom z).property
  have hrep (z : c.pt) : ∃ j, z ∈ T j := by
    have hz : z ∈ (↑(⨆ j, T j) : Set c.pt) := by rw [htop]; trivial
    rw [Subalgebra.coe_iSup_of_directed hdir] at hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    exact ⟨j, hj⟩
  choose j hj using fun i => hrep (x i)
  obtain ⟨k, hk⟩ := hdir.finset_le (Finset.univ.image j)
  have hmem (i : Fin n) : x i ∈ T k :=
    hk (j i) (Finset.mem_image_of_mem j (Finset.mem_univ i)) (hj i)
  choose y hy using hmem
  exact ⟨k, y, hy⟩

open CategoryTheory CategoryTheory.Limits in
private theorem flat_of_ind_etale_of_flat
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Flat R M]
    (hind : (CommAlgCat.etale R).ind (CommAlgCat.of R S)) : Module.Flat S M := by
  classical
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  rw [Module.Flat.iff_forall_isTrivialRelation]
  intro n a x hx
  obtain ⟨j, b, hb⟩ := exists_rep_fin_of_isColimit pres.cocone pres.isColimit a
  let φ : pres.diag.obj j →ₐ[R] S := (pres.ι.app j).hom
  let : Algebra (pres.diag.obj j) S := φ.toRingHom.toAlgebra
  let : Module (pres.diag.obj j) M := Module.compHom M φ.toRingHom
  have htower : IsScalarTower R (pres.diag.obj j) M :=
    ⟨fun r s m => by
      change φ (r • s) • m = r • (φ s • m)
      rw [map_smul, smul_assoc]⟩
  have : Algebra.Etale R (pres.diag.obj j) := hpres j
  have hflat : Module.Flat (pres.diag.obj j) M :=
    Algebra.FormallyUnramified.flat_of_restrictScalars R (pres.diag.obj j) M
  have hrel : ∑ i, b i • x i = 0 := by
    change ∑ i, φ (b i) • x i = 0
    simpa only [φ, hb] using hx
  obtain ⟨k, coeff, y, hy, hcoeff⟩ :=
    Module.Flat.iff_forall_isTrivialRelation.mp hflat hrel
  refine ⟨k, fun i q => φ (coeff i q), y, ?_, ?_⟩
  · intro i
    exact hy i
  · intro q
    simpa only [map_sum, map_mul, φ, hb, map_zero] using congrArg φ (hcoeff q)

private theorem residueField_map_bijective_of_isHenselization.{u}
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsHenselization R (ResidueField R) S] :
    Function.Bijective (ResidueField.map (algebraMap R S)) := by
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv
    (R := R) (L := ResidueField R) (Rh := S)
  have h : ResidueField.map (algebraMap R S) = e := by
    ext x
    obtain ⟨r, rfl⟩ := residue_surjective x
    simpa using (he r).symm
  rw [h]
  exact e.bijective

private theorem isSepClosed_of_ringEquiv {K L : Type*} [Field K] [Field L]
    [IsSepClosed K] (e : K ≃+* L) : IsSepClosed L := by
  let : Algebra K L := e.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic K L := ⟨fun x =>
    (show x = algebraMap K L (e.symm x) by simp [RingHom.algebraMap_toAlgebra]) ▸
      isAlgebraic_algebraMap (e.symm x)⟩
  exact Algebra.IsAlgebraic.isSepClosed (F := K) (E := L)

private theorem henselization_maximalIdeal_fg_and_quotient_equiv.{u, v}
    {R Rh Rsh : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rh Rsh]
    [IsScalarTower R Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    [IsSepClosure (ResidueField R) K]
    [IsHenselization R (ResidueField R) Rh] [IsHenselization R K Rsh] :
    (maximalIdeal Rh).FG ∧ (maximalIdeal Rsh).FG ∧
      ∀ n : ℕ, ∃ e : (R ⧸ maximalIdeal R ^ n) ≃+* (Rh ⧸ maximalIdeal Rh ^ n),
        ∀ x : R, e (Ideal.Quotient.mk _ x) =
          Ideal.Quotient.mk _ (algebraMap R Rh x) := by
  have := IsHenselization.henselian R (ResidueField R) (Rh := Rh)
  have := IsHenselization.henselian R K (Rh := Rsh)
  have := IsHenselization.isLocalHom (R := R) (L := ResidueField R) (Rh := Rh)
  have := IsSepClosure.sep_closed (ResidueField R) (K := K)
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := K) (Rh := Rsh)
  have := isSepClosed_of_ringEquiv e
  obtain ⟨_, _, hm, hms, _, hq, _⟩ :=
    henselization_faithfullyFlat_and_quotient_basis
      (R := R) (Rh := Rh) (Rsh := Rsh) (κsep := K)
      (IsHenselization.ind_etale_of_universe_le (R := R) (ResidueField R))
      residueField_map_bijective_of_isHenselization
      (IsHenselization.ind_etale_of_universe_le (R := R) K) ⟨e, he⟩
  refine ⟨hm ▸ (maximalIdeal R).fg_of_isNoetherianRing.map _,
    hms ▸ (maximalIdeal R).fg_of_isNoetherianRing.map _, fun n => ?_⟩
  have hn : (maximalIdeal R ^ n).map (algebraMap R Rh) = maximalIdeal Rh ^ n := by
    rw [Ideal.map_pow, hm]
  refine ⟨(RingEquiv.ofBijective _ (hq n)).trans
    (Ideal.quotientEquivAlgOfEq Rh hn).toRingEquiv, fun x => ?_⟩
  change (Ideal.quotientEquivAlgOfEq Rh hn)
    (Ideal.Quotient.mk _ (algebraMap R Rh x)) = _
  exact Ideal.quotientEquivAlgOfEq_mk Rh hn _

private theorem flat_of_henselization_of_flat.{u, w, z}
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [IsHenselization R K S]
    (M : Type z) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Flat R M] : Module.Flat S M :=
  flat_of_ind_etale_of_flat M
    (IsHenselization.ind_etale_of_universe_le.{u, w, 0} (R := R) K (Rh := S))

private theorem henselization_completion_equiv_and_flat.{u}
    {R S : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsHenselization R (ResidueField R) S]
    (hfg : (maximalIdeal S).FG)
    (he : ∀ n : ℕ, ∃ e : (R ⧸ maximalIdeal R ^ n) ≃+* (S ⧸ maximalIdeal S ^ n),
      ∀ x : R, e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R S x)) :
    IsNoetherianRing S ∧
      RingHom.Flat (algebraMap S (AdicCompletion (maximalIdeal S) S)) ∧
      ∃ e : AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal S) S,
        ∀ x : R, e (algebraMap R (AdicCompletion (maximalIdeal R) R) x) =
          algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap R S x) := by
  have := IsHenselization.isLocalHom (R := R) (L := ResidueField R) (Rh := S)
  obtain ⟨e, he⟩ := exists_adicCompletion_equiv_of_quotient_equiv (algebraMap R S)
    (maximalIdeal R) (maximalIdeal S) (map_maximalIdeal_le _) he
  have hcomm (x : R) :
      e (algebraMap R (AdicCompletion (maximalIdeal R) R) x) =
        algebraMap R (AdicCompletion (maximalIdeal S) S) x := by
    rw [IsScalarTower.algebraMap_apply R S (AdicCompletion (maximalIdeal S) S)]
    exact he x
  let E : AdicCompletion (maximalIdeal R) R ≃ₐ[R] AdicCompletion (maximalIdeal S) S :=
    AlgEquiv.ofRingEquiv hcomm
  have : Module.Flat R (AdicCompletion (maximalIdeal S) S) :=
    Module.Flat.of_linearEquiv E.symm.toLinearEquiv
  have hflat : Module.Flat S (AdicCompletion (maximalIdeal S) S) :=
    flat_of_henselization_of_flat (R := R) (S := S) (ResidueField R)
      (AdicCompletion (maximalIdeal S) S)
  have := AdicCompletion.isLocalRing_of_fg hfg
  have := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  have := adicCompletion_isNoetherianRing_of_fg hfg
  have hfaith : Module.FaithfullyFlat S (AdicCompletion (maximalIdeal S) S) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨descent_noetherian (algebraMap S (AdicCompletion (maximalIdeal S) S))
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hfaith) inferInstance,
    RingHom.flat_algebraMap_iff.mpr hflat, e, he⟩

private theorem henselization_completion_initial_properties.{u, v}
    {R Rh Rsh : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rh Rsh]
    [IsScalarTower R Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    [IsSepClosure (ResidueField R) K]
    [IsHenselization R (ResidueField R) Rh] [IsHenselization R K Rsh] :
    IsNoetherianRing Rh ∧
    ∃ (hRhLocal : IsLocalRing (AdicCompletion (maximalIdeal Rh) Rh))
      (hRshLocal : IsLocalRing (AdicCompletion (maximalIdeal Rsh) Rsh)),
      letI := hRhLocal
      letI := hRshLocal
      IsNoetherianRing (AdicCompletion (maximalIdeal Rh) Rh) ∧
      IsNoetherianRing (AdicCompletion (maximalIdeal Rsh) Rsh) ∧
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal Rh) Rh))
        (AdicCompletion (maximalIdeal Rh) Rh) ∧
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal Rsh) Rsh))
        (AdicCompletion (maximalIdeal Rsh) Rsh) ∧
      RingHom.Flat (algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh)) ∧
      ∃ e : AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal Rh) Rh,
        ∀ x : R, e (algebraMap R (AdicCompletion (maximalIdeal R) R) x) =
          algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh) (algebraMap R Rh x) := by
  obtain ⟨hRhfg, hRshfg, hquot⟩ :=
    henselization_maximalIdeal_fg_and_quotient_equiv (R := R) (Rh := Rh) (Rsh := Rsh) K
  obtain ⟨hRh, hflat, e, he⟩ := henselization_completion_equiv_and_flat hRhfg hquot
  obtain ⟨hRhLocal, hRhNoeth, hRhComplete⟩ := adicCompletion_completeLocal_of_fg hRhfg
  obtain ⟨hRshLocal, hRshNoeth, hRshComplete⟩ := adicCompletion_completeLocal_of_fg hRshfg
  exact ⟨hRh, hRhLocal, hRshLocal, hRhNoeth, hRshNoeth,
    hRhComplete, hRshComplete, hflat, e, he⟩

private theorem finsupp_mem_smul_top_iff
    {R ι : Type*} [CommRing R] (I : Ideal R) (x : ι →₀ R) :
    x ∈ I • (⊤ : Submodule R (ι →₀ R)) ↔ ∀ i, x i ∈ I := by
  constructor
  · intro hx i
    have h := Submodule.smul_top_le_comap_smul_top I (Finsupp.lapply i) hx
    simpa using h
  · intro hx
    rw [← Finsupp.sum_single x]
    apply Submodule.sum_mem
    intro i hi
    have h := Submodule.smul_mem_smul (hx i)
      (Submodule.mem_top (x := Finsupp.single i (1 : R)))
    simpa using h

private noncomputable def finsuppQuotientEquiv
    {R ι : Type*} [CommRing R] (I : Ideal R) :
    ((ι →₀ R) ⧸ (I • (⊤ : Submodule R (ι →₀ R)))) ≃ₗ[R] (ι →₀ R ⧸ I) := by
  let f : (ι →₀ R) →ₗ[R] (ι →₀ R ⧸ I) :=
    Finsupp.mapRange.linearMap I.mkQ
  have hk : f.ker = I • ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, f, Finsupp.mapRange.linearMap_apply,
      Finsupp.ext_iff, Finsupp.mapRange_apply, Finsupp.zero_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero,
      finsupp_mem_smul_top_iff]
  have hs : Function.Surjective f :=
    Finsupp.mapRange_surjective I.mkQ I.mkQ.map_zero I.mkQ_surjective
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)

private theorem finsuppQuotientEquiv_mk
    {R ι : Type*} [CommRing R] (I : Ideal R) (x : ι →₀ R) :
    finsuppQuotientEquiv (ι := ι) I (Submodule.Quotient.mk x) =
      Finsupp.mapRange (Ideal.Quotient.mk I) (map_zero _) x := by
  rfl

private noncomputable def completionLinearEquivOfQuotients
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (I : Ideal R) (J : Ideal S)
    (f : M →ₗ[R] S)
    (e : ∀ n : ℕ, (M ⧸ (I ^ n • (⊤ : Submodule R M))) ≃ₗ[R]
      (S ⧸ (J ^ n • (⊤ : Submodule S S))))
    (he : ∀ n x, e n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x)) :
    AdicCompletion I M ≃ₗ[R] AdicCompletion J S := by
  have hc {m n : ℕ} (hmn : m ≤ n) (x : M ⧸ (I ^ n • ⊤)) :
      e m (AdicCompletion.transitionMap I M hmn x) =
        AdicCompletion.transitionMap J S hmn (e n x) := by
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    change e m (Submodule.Quotient.mk x) =
      AdicCompletion.transitionMap J S hmn (e n (Submodule.Quotient.mk x))
    rw [he, he]
    rfl
  exact {
    toFun := fun x => ⟨fun n => e n (x.val n), fun hmn => by
      rw [← hc, x.property hmn]⟩
    invFun := fun x => ⟨fun n => (e n).symm (x.val n), fun hmn => by
      apply (e _).injective
      rw [hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, x.property hmn]⟩
    left_inv := fun x => AdicCompletion.ext fun n => (e n).symm_apply_apply _
    right_inv := fun x => AdicCompletion.ext fun n => (e n).apply_symm_apply _
    map_add' := fun x y => AdicCompletion.ext fun n => (e n).map_add _ _
    map_smul' := fun r x => AdicCompletion.ext fun n => (e n).map_smul _ _ }

private theorem quotient_equiv_of_basis
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (x : ι → S)
    (hb : letI : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
        Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
      ∃ b : Module.Basis ι (R ⧸ I) (S ⧸ I.map (algebraMap R S)),
        ∀ i, b i = Ideal.Quotient.mk _ (x i)) :
    ∃ e : ((ι →₀ R) ⧸ (I • (⊤ : Submodule R (ι →₀ R)))) ≃ₗ[R]
      (S ⧸ I.map (algebraMap R S)),
      ∀ y, e (Submodule.Quotient.mk y) =
        Ideal.Quotient.mk _ (Finsupp.linearCombination R x y) := by
  let : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  obtain ⟨b, hb⟩ := hb
  refine ⟨(finsuppQuotientEquiv I).trans (b.repr.symm.restrictScalars R), ?_⟩
  intro y
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add a c ha hc => simpa only [Submodule.Quotient.mk_add, map_add] using congrArg₂ (· + ·) ha hc
  | single i r =>
    simp only [LinearEquiv.trans_apply, finsuppQuotientEquiv_mk,
      Finsupp.mapRange_single, LinearEquiv.restrictScalars_apply,
      Module.Basis.repr_symm_apply, Finsupp.linearCombination_single, hb]
    rfl

private theorem completion_flat_of_quotient_basis
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    (I : Ideal R) (J : Ideal S) (hJ : I.map (algebraMap R S) = J) (x : ι → S)
    (hb : ∀ n : ℕ,
      letI : Algebra (R ⧸ I ^ n)
        (S ⧸ (I ^ n).map (algebraMap R S)) :=
        Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
      ∃ b : Module.Basis ι (R ⧸ I ^ n) (S ⧸ (I ^ n).map (algebraMap R S)),
        ∀ i, b i = Ideal.Quotient.mk _ (x i)) :
    Module.Flat R (AdicCompletion J S) := by
  classical
  have he (n : ℕ) := quotient_equiv_of_basis (I ^ n) x (hb n)
  choose e he using he
  have hpow (n : ℕ) : (I ^ n).map (algebraMap R S) = J ^ n • (⊤ : Submodule S S) := by
    rw [Ideal.map_pow, hJ]
    simp
  let E (n : ℕ) := (e n).trans
    ((Ideal.quotientEquivAlgOfEq R (hpow n)).toLinearEquiv)
  have hE (n : ℕ) (y : ι →₀ R) :
      E n (Submodule.Quotient.mk y) = Submodule.Quotient.mk
        (Finsupp.linearCombination R x y) := by
    dsimp only [E, LinearEquiv.trans_apply]
    rw [he]
    rfl
  let c := completionLinearEquivOfQuotients I J (Finsupp.linearCombination R x) E hE
  have : Module.Flat R (AdicCompletion I (DirectSum ι (fun _ : ι => R))) :=
    AdicCompletion.flat_directSum R I ι
  have : Module.Flat R (AdicCompletion I (ι →₀ R)) :=
    Module.Flat.of_linearEquiv
      ((AdicCompletion.congr I (finsuppLEquivDirectSum R R ι)).restrictScalars R)
  exact Module.Flat.of_linearEquiv c.symm

end

end

end
