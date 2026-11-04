module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Flat.LocalBaseChange
public import StacksFrontier.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.ClosedPoint
public import StacksFrontier.RingTheory.Rig.Flat
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings

/-!
# Naive rig-flatness implies rig-flatness over a Jacobson reduction

Let `φ : A → B` be an adic homomorphism of topological finite type between Noetherian weakly
admissible topological rings and suppose the reduction `A / I` of the source modulo an ideal of
definition is a Jacobson ring.  Then naive rig-flatness of `φ` already implies rig-flatness: each
induced map `ψ` of completed principal localizations is again naively rig-flat.

The argument tests naive rig-flatness of `ψ` on the rig-closed primes `q` of its target, which is
the fourth of the four equivalent conditions of `Rig.naivelyRigFlat_tfae`.  For such a `q` the
Jacobson hypothesis makes the contraction of `q` to `A` rig-closed as well
(`Rig.isRigPointLocalCondition_comap_of_isJacobsonRing_quotient`), hence the induced map of
quotients is finite (`Rig.rigPoint_relative_tfae`); so the localizing element becomes a unit in
that quotient and the contraction of `q` to the completion is already extended from `A`.  Flatness
of the local ring of the target at `q` over the completed source then follows from naive
rig-flatness of `φ` together with the local criterion for flatness.

## Main results

* `Rig.RingHom.isRigFlat_of_isNaivelyRigFlat_of_isJacobsonRing_quotient` — the upgrade of naive
  rig-flatness to rig-flatness.

## Implementation notes

The Jacobson hypothesis names one ideal of definition; the source states it for some, equivalently
any, ideal of definition, and the two are interchangeable because all ideals of definition have
the same radical, namely the topological nilradical.

The completed principal localizations carry the adic topology of the extended ideal, as in the
definition of `Rig.RingHom.IsRigFlat`.

## References

* [Stacks Project, Tag 0GGQ](https://stacks.math.columbia.edu/tag/0GGQ)
-/

@[expose] public section

namespace Rig

namespace RingHom

/-! ### Ideals of definition and the topological nilradical -/

private lemma isClosedPointAwayFrom_topologicalNilradical_of_isRigPointLocalCondition
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] [IsNoetherianRing R]
    [@CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R)] [T2Space R]
    (I : Ideal R) (hI : IsAdic I) (q : Ideal R) [q.IsPrime]
    (hq : Ideal.IsRigPointLocalCondition q) :
    Ideal.IsClosedPointAwayFrom (topologicalNilradical R) q := by
  have hc := ((rigPoint_tfae ⟨I, hI⟩ q).out 8 4).mp hq
  have hcI := hc I (isIdealOfDefinition_of_isAdic hI)
  unfold Ideal.IsClosedPointAwayFrom at hcI ⊢
  rwa [← radical_eq_topologicalNilradical_of_isAdic I hI, PrimeSpectrum.zeroLocus_radical]

/-! ### The induced map of completed principal localizations -/

/-- The map of completed principal localizations is adic on the nose: it carries the extended
ideal of the source to the extended ideal of the target. -/
public theorem completedAwayMap_map_ideal
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (f : A) :
    let A_f := Localization.Away f
    let B_f := Localization.Away (φ f)
    let I_f := I.map (algebraMap A A_f)
    let J_f := (I.map φ).map (algebraMap B B_f)
    (I_f.map (algebraMap A_f (AdicCompletion I_f A_f))).map (completedAwayMap φ I f) =
      J_f.map (algebraMap B_f (AdicCompletion J_f B_f)) := by
  dsimp
  let A_f := Localization.Away f
  let B_f := Localization.Away (φ f)
  let I_f := I.map (algebraMap A A_f)
  let J_f := (I.map φ).map (algebraMap B B_f)
  let φf : A_f →+* B_f := IsLocalization.Away.map A_f B_f φ f
  have hIlocal : I_f.map φf = J_f := by
    dsimp only [I_f, J_f]
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext x
    show φf (algebraMap A A_f x) = algebraMap B B_f (φ x)
    dsimp only [φf, IsLocalization.Away.map]
    apply IsLocalization.map_eq
  calc _ = I_f.map ((completedAwayMap φ I f).comp
        (algebraMap A_f (AdicCompletion I_f A_f))) := Ideal.map_map _ _
    _ = I_f.map ((algebraMap B_f (AdicCompletion J_f B_f)).comp φf) := by
      rw [completedAwayMap_comp_algebraMap]
    _ = (I_f.map φf).map (algebraMap B_f (AdicCompletion J_f B_f)) := (Ideal.map_map _ _).symm
    _ = _ := by rw [hIlocal]

/-- The map of completed principal localizations is an adic ring homomorphism. -/
public theorem isAdic_completedAwayMap
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (f : A) :
    let A_f := Localization.Away f
    let B_f := Localization.Away (φ f)
    let I_f := I.map (algebraMap A A_f)
    let J_f := (I.map φ).map (algebraMap B B_f)
    let I_hat := I_f.map (algebraMap A_f (AdicCompletion I_f A_f))
    let J_hat := J_f.map (algebraMap B_f (AdicCompletion J_f B_f))
    letI : TopologicalSpace (AdicCompletion I_f A_f) := I_hat.adicTopology
    letI : TopologicalSpace (AdicCompletion J_f B_f) := J_hat.adicTopology
    _root_.RingHom.IsAdic (completedAwayMap φ I f) := by
  dsimp
  let A_f := Localization.Away f
  let B_f := Localization.Away (φ f)
  let I_f := I.map (algebraMap A A_f)
  let J_f := (I.map φ).map (algebraMap B B_f)
  let I_hat := I_f.map (algebraMap A_f (AdicCompletion I_f A_f))
  let J_hat := J_f.map (algebraMap B_f (AdicCompletion J_f B_f))
  let : TopologicalSpace (AdicCompletion I_f A_f) := I_hat.adicTopology
  let : TopologicalSpace (AdicCompletion J_f B_f) := J_hat.adicTopology
  have hmap : I_hat.map (completedAwayMap φ I f) = J_hat := completedAwayMap_map_ideal φ I f
  refine ⟨I_hat, rfl, ?_⟩
  rw [hmap]
  rfl

/-- A continuous ring homomorphism maps the topological nilradical into the topological
nilradical. -/
private theorem topologicalNilradical_le_comap_of_continuous
    {R S : Type*} [CommRing R] [TopologicalSpace R] [CommRing S] [TopologicalSpace S]
    [IsLinearTopology R R] [IsLinearTopology S S] (f : R →+* S) (hf : Continuous f) :
    topologicalNilradical R ≤ (topologicalNilradical S).comap f := fun _ hx =>
  IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
    ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).map hf)

/-- The reduction of an adic completion is the reduction of the ring itself, modulo any ideal `a`
with the radical of `I`. -/
private theorem exists_reduction_equiv_adicCompletion
    {R : Type*} [CommRing R] (I a : Ideal R) (ha : I.radical = a) (hIfg : I.FG) :
    let C := AdicCompletion I R
    let I_hat := I.map (algebraMap R C)
    letI : TopologicalSpace C := I_hat.adicTopology
    letI : IsTopologicalRing C := I_hat.nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology C C := I_hat.isLinearTopology
    ∃ e : C ⧸ topologicalNilradical C ≃+* R ⧸ a,
      ∀ r : R, e (Ideal.Quotient.mk (topologicalNilradical C) (algebraMap R C r)) =
        Ideal.Quotient.mk a r := by
  classical
  subst ha
  let C := AdicCompletion I R
  let I_hat := I.map (algebraMap R C)
  let : TopologicalSpace C := I_hat.adicTopology
  let : IsTopologicalRing C := I_hat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology C C := I_hat.isLinearTopology
  have hradC : topologicalNilradical C = I_hat.radical :=
    (radical_eq_topologicalNilradical_of_isAdic I_hat rfl).symm
  let ev : C →+* R ⧸ I := (AdicCompletion.evalOneₐ I).toRingHom
  let fac : R ⧸ I →+* R ⧸ I.radical := Ideal.Quotient.factor Ideal.le_radical
  let ρ : C →+* R ⧸ I.radical := fac.comp ev
  have hker : RingHom.ker ρ = topologicalNilradical C := by
    show Ideal.comap ev (RingHom.ker fac) = _
    rw [Ideal.Quotient.factor_ker,
      Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]),
      Ideal.map_quotient_self, Ideal.comap_radical]
    show (Ideal.comap ev ⊥).radical = _
    rw [← RingHom.ker_eq_comap_bot, AdicCompletion.ker_evalOneₐ_eq_map I hIfg, ← hradC]
  have hsurj : Function.Surjective ρ := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := I.radical) x
    obtain ⟨z, hz⟩ := AdicCompletion.evalOneₐ_surjective I y
    exact ⟨z, by simp [ρ, fac, ev, hz]⟩
  let e0 : C ⧸ RingHom.ker ρ ≃+* R ⧸ I.radical := RingHom.quotientKerEquivOfSurjective hsurj
  let e : C ⧸ topologicalNilradical C ≃+* R ⧸ I.radical :=
    (Ideal.quotEquivOfEq hker.symm).trans e0
  refine ⟨e, fun r => ?_⟩
  show e (Ideal.Quotient.mk (topologicalNilradical C) (algebraMap R C r)) = _
  simp only [e, e0, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  simp [ρ, fac, ev]

/-- The map of completed principal localizations, and the composite from the target, are
topologically of finite type and continuous. -/
@[ega "0 7.6.5" "Case B = A"]
public theorem isTopologicallyOfFiniteType_completedAwayMap
    {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hφ : Continuous φ)
    (hφft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (I : Ideal A) (hI : IsAdic I) (hIφ : IsAdic (I.map φ)) (f : A) :
    let A_loc := Localization.Away f
    let B_loc := Localization.Away (φ f)
    let I_loc := I.map (algebraMap A A_loc)
    let J_loc := (I.map φ).map (algebraMap B B_loc)
    let A_hat := AdicCompletion I_loc A_loc
    let B_hat := AdicCompletion J_loc B_loc
    let I_hat := I_loc.map (algebraMap A_loc A_hat)
    let J_hat := J_loc.map (algebraMap B_loc B_hat)
    letI : TopologicalSpace A_hat := I_hat.adicTopology
    letI : TopologicalSpace B_hat := J_hat.adicTopology
    TopologicalRing.IsTopologicallyOfFiniteType (completedAwayMap φ I f) ∧
      TopologicalRing.IsTopologicallyOfFiniteType ((algebraMap B B_hat).comp φ) ∧
      Continuous (completedAwayMap φ I f) ∧
      Continuous ((algebraMap B B_hat).comp φ) ∧
      I.map ((algebraMap B B_hat).comp φ) = J_hat := by
  classical
  dsimp only
  let A_loc := Localization.Away f
  let B_loc := Localization.Away (φ f)
  let I_loc := I.map (algebraMap A A_loc)
  let J_loc := (I.map φ).map (algebraMap B B_loc)
  let A_hat := AdicCompletion I_loc A_loc
  let B_hat := AdicCompletion J_loc B_loc
  let I_hat := I_loc.map (algebraMap A_loc A_hat)
  let J_hat := J_loc.map (algebraMap B_loc B_hat)
  let : TopologicalSpace A_hat := I_hat.adicTopology
  let : IsTopologicalRing A_hat := I_hat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology A_hat A_hat := I_hat.isLinearTopology
  let : TopologicalSpace B_hat := J_hat.adicTopology
  let : IsTopologicalRing B_hat := J_hat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology B_hat B_hat := J_hat.isLinearTopology
  let ψ := completedAwayMap φ I f
  let φloc : A_loc →+* B_loc := IsLocalization.Away.map A_loc B_loc φ f
  let : Algebra A_loc B_loc := φloc.toAlgebra
  let a := topologicalNilradical A
  let b := topologicalNilradical B
  let a_loc := a.map (algebraMap A A_loc)
  let b_loc := b.map (algebraMap B B_loc)
  let a_hat := topologicalNilradical A_hat
  let b_hat := topologicalNilradical B_hat
  have hψcomp : ψ.comp (algebraMap A_loc A_hat) = (algebraMap B_loc B_hat).comp φloc := by
    simpa [ψ, A_loc, B_loc, I_loc, J_loc] using completedAwayMap_comp_algebraMap φ I f
  have hψmap : I_hat.map ψ = J_hat := completedAwayMap_map_ideal φ I f
  have hψcont : Continuous ψ := by
    show @Continuous A_hat B_hat I_hat.adicTopology J_hat.adicTopology ψ
    exact continuous_adic_of_map_le I_hat J_hat ψ (by rw [hψmap])
  have hradA : I.radical = a := radical_eq_topologicalNilradical_of_isAdic I hI
  have hradB : (I.map φ).radical = b := radical_eq_topologicalNilradical_of_isAdic (I.map φ) hIφ
  have hradAloc : I_loc.radical = a_loc := by
    dsimp only [I_loc, a_loc]
    rw [← IsLocalization.map_radical (Submonoid.powers f) A_loc I, hradA]
  have hradBloc : J_loc.radical = b_loc := by
    dsimp only [J_loc, b_loc]
    rw [← IsLocalization.map_radical (Submonoid.powers (φ f)) B_loc (I.map φ), hradB]
  obtain ⟨eA, heA⟩ :=
    exists_reduction_equiv_adicCompletion I_loc a_loc hradAloc I_loc.fg_of_isNoetherianRing
  obtain ⟨eB, heB⟩ :=
    exists_reduction_equiv_adicCompletion J_loc b_loc hradBloc J_loc.fg_of_isNoetherianRing
  have hnil : a ≤ Ideal.comap φ b := topologicalNilradical_le_comap_of_continuous φ hφ
  let φred : A ⧸ a →+* B ⧸ b := Ideal.quotientMap b φ hnil
  have hφred : φred.FiniteType := by
    have htaut := _root_.RingHom.isTaut_of_isAdic φ hφ ⟨I, hI, hIφ⟩
    show (Ideal.quotientMap b φ hnil).FiniteType
    exact isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType
      φ hφ ⟨I, TopologicalRing.isWeakIdealOfDefinition_of_isAdic hI⟩ htaut hφft
  let SA := A_loc ⧸ a_loc
  let SB := B_loc ⧸ b_loc
  let iA : A ⧸ a →+* SA := Ideal.quotientMap a_loc (algebraMap A A_loc)
    (fun _ hx => Ideal.mem_map_of_mem (algebraMap A A_loc) hx)
  let iB : B ⧸ b →+* SB := Ideal.quotientMap b_loc (algebraMap B B_loc)
    (fun _ hx => Ideal.mem_map_of_mem (algebraMap B B_loc) hx)
  let : Algebra (A ⧸ a) SA := iA.toAlgebra
  let : Algebra (B ⧸ b) SB := iB.toAlgebra
  let : Algebra A SA := Algebra.compHom SA (algebraMap A A_loc)
  let : Algebra B SB := Algebra.compHom SB (algebraMap B B_loc)
  have : IsLocalization.Away (Ideal.Quotient.mk a f) SA := isLocalization_away_quotient a f
  have hφredf : φred (Ideal.Quotient.mk a f) = Ideal.Quotient.mk b (φ f) := by
    simp [φred, Ideal.quotientMap_mk]
  have : IsLocalization.Away (φred (Ideal.Quotient.mk a f)) SB := by
    simpa [hφredf] using isLocalization_away_quotient b (φ f)
  have huunit : IsUnit ((iB.comp φred) (Ideal.Quotient.mk a f)) := by
    show IsUnit (iB (φred (Ideal.Quotient.mk a f)))
    exact IsLocalization.Away.algebraMap_isUnit (φred (Ideal.Quotient.mk a f))
  let u : SA →+* SB :=
    IsLocalization.Away.lift (Ideal.Quotient.mk a f) (g := iB.comp φred) huunit
  have hucomp : u.comp iA = iB.comp φred := by
    dsimp only [u]
    exact IsLocalization.Away.lift_comp (R := A ⧸ a) (S := SA) (P := SB)
      (x := Ideal.Quotient.mk a f) (g := iB.comp φred) huunit
  have : IsLocalization.Away (Ideal.Quotient.mk b (φ f)) SB := by
    rw [← hφredf]
    infer_instance
  have hiBft : (algebraMap (B ⧸ b) SB).FiniteType := by
    rw [_root_.RingHom.finiteType_algebraMap]
    let : IsLocalization (Submonoid.powers (Ideal.Quotient.mk b (φ f))) SB := by
      rw [← hφredf]
      infer_instance
    exact IsLocalization.finiteType_of_monoid_fg
      (Submonoid.powers (Ideal.Quotient.mk b (φ f))) SB
  have huft : u.FiniteType :=
    RingHom.FiniteType.of_comp_finiteType (f := iA) (g := u) (by
      rw [hucomp]
      exact hiBft.comp hφred)
  have hucompat : u.comp (Ideal.Quotient.mk a_loc) = (Ideal.Quotient.mk b_loc).comp φloc := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    ext x
    have hquotA := RingHom.congr_fun (Ideal.quotientMap_comp_mk
      (J := a) (I := a_loc) (f := algebraMap A A_loc)
      (fun _ hx => Ideal.mem_map_of_mem (algebraMap A A_loc) hx)) x
    have hquotB := RingHom.congr_fun (Ideal.quotientMap_comp_mk
      (J := b) (I := b_loc) (f := algebraMap B B_loc)
      (fun _ hx => Ideal.mem_map_of_mem (algebraMap B B_loc) hx)) (φ x)
    calc u (Ideal.Quotient.mk a_loc (algebraMap A A_loc x)) = u (iA (Ideal.Quotient.mk a x)) :=
          congrArg u hquotA.symm
      _ = iB (φred (Ideal.Quotient.mk a x)) :=
        RingHom.congr_fun hucomp (Ideal.Quotient.mk a x)
      _ = iB (Ideal.Quotient.mk b (φ x)) := by simp [φred, Ideal.quotientMap_mk]
      _ = Ideal.Quotient.mk b_loc (algebraMap B B_loc (φ x)) := hquotB
      _ = Ideal.Quotient.mk b_loc (φloc (algebraMap A A_loc x)) := by
        congr 1
        dsimp only [φloc, IsLocalization.Away.map]
        symm
        apply IsLocalization.map_eq
  let redψ : A_hat ⧸ a_hat →+* B_hat ⧸ b_hat :=
    Ideal.quotientMap b_hat ψ (topologicalNilradical_le_comap_of_continuous ψ hψcont)
  have hsurjA : Function.Surjective
      fun z : A_loc => Ideal.Quotient.mk a_hat (algebraMap A_loc A_hat z) := by
    intro x
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := a_loc) (eA x)
    refine ⟨z, ?_⟩
    apply eA.injective
    rwa [heA]
  have hmaps : redψ = eB.symm.toRingHom.comp (u.comp eA.toRingHom) := by
    apply RingHom.ext
    intro x
    obtain ⟨z, rfl⟩ := hsurjA x
    apply eB.injective
    simp only [RingHom.comp_apply]
    show eB (Ideal.Quotient.mk b_hat (ψ ((algebraMap A_loc A_hat) z))) =
      eB (eB.symm (u (eA (Ideal.Quotient.mk a_hat (algebraMap A_loc A_hat z)))))
    rw [show ψ (algebraMap A_loc A_hat z) = algebraMap B_loc B_hat (φloc z) from
      RingHom.congr_fun hψcomp z, heB, RingEquiv.apply_symm_apply, heA]
    exact (RingHom.congr_fun hucompat z).symm
  have hredψ : redψ.FiniteType := by
    rw [hmaps]
    exact RingHom.FiniteType.of_surjective _ eB.symm.surjective |>.comp
      (huft.comp (RingHom.FiniteType.of_surjective _ eA.surjective))
  let : IsNoetherianRing B_hat := inferInstance
  have hBhW := isWeaklyAdmissible_adicCompletion J_loc J_loc.fg_of_isNoetherianRing
  refine And.intro
    (isTopologicallyOfFiniteType_of_isFiniteTypeOnReductions ψ hψcont hBhW hredψ) ?_
  let χ := (algebraMap B B_hat).comp φ
  have hχmap : I.map χ = J_hat := by
    dsimp only [χ, J_hat, J_loc]
    simp only [Ideal.map_map, IsScalarTower.algebraMap_eq B B_loc B_hat, RingHom.comp_assoc]
  have hχcont : Continuous χ := by
    have ht := hI
    unfold IsAdic at ht
    rw [ht]
    exact continuous_adic_of_map_le I J_hat χ hχmap.le
  let redχ : A ⧸ a →+* B_hat ⧸ b_hat := Ideal.quotientMap b_hat χ
    (topologicalNilradical_le_comap_of_continuous χ hχcont)
  have hχred : redχ = eB.symm.toRingHom.comp (iB.comp φred) := by
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply eB.injective
    show eB (Ideal.Quotient.mk b_hat (algebraMap B B_hat (φ x))) =
      eB (eB.symm (iB (φred (Ideal.Quotient.mk a x))))
    rw [IsScalarTower.algebraMap_apply B B_loc B_hat, heB, RingEquiv.apply_symm_apply]
    rfl
  have hχredft : redχ.FiniteType := by
    rw [hχred]
    exact (RingHom.FiniteType.of_surjective _ eB.symm.surjective).comp (hiBft.comp hφred)
  exact ⟨isTopologicallyOfFiniteType_of_isFiniteTypeOnReductions χ hχcont hBhW hχredft,
    hψcont, hχcont, hχmap⟩

/-! ### Local flatness criteria -/

/-- The local criterion for flatness, applied with the target ring in both upper corners. -/
private lemma flat_of_flat_of_map_comap_maximalIdeal
    {A D E : Type*} [CommRing A] [CommRing D] [CommRing E]
    [Algebra A D] [Algebra D E] [Algebra A E] [IsScalarTower A D E]
    [IsLocalRing D] [IsLocalRing E] [IsNoetherianRing D] [IsNoetherianRing E]
    [IsLocalHom (algebraMap D E)] [Module.Flat A D] [Module.Flat A E]
    (hm : ((IsLocalRing.maximalIdeal D).comap (algebraMap A D)).map (algebraMap A D) =
      IsLocalRing.maximalIdeal D) : Module.Flat D E := by
  let p := (IsLocalRing.maximalIdeal D).comap (algebraMap A D)
  let R := Localization.AtPrime p
  have hu : ∀ y : p.primeCompl, IsUnit (algebraMap A D y) := fun y =>
    IsLocalRing.notMem_maximalIdeal.mp y.2
  let g : R →+* D := IsLocalization.lift hu
  let : Algebra R D := g.toAlgebra
  let : IsScalarTower A R D := IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp hu).symm
  let : Algebra R E := ((algebraMap D E).comp g).toAlgebra
  let : IsScalarTower R D E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A R E := IsScalarTower.of_algebraMap_eq' (by
    rw [show algebraMap R E = (algebraMap D E).comp g from rfl, RingHom.comp_assoc,
      IsLocalization.lift_comp]
    exact IsScalarTower.algebraMap_eq A D E)
  have : Module.Flat R D := (Module.flat_iff_of_isLocalization R p.primeCompl D).2 inferInstance
  have : Module.Flat R E := (Module.flat_iff_of_isLocalization R p.primeCompl E).2 inferInstance
  have hm' : (IsLocalRing.maximalIdeal R).map (algebraMap R D) = IsLocalRing.maximalIdeal D := by
    rwa [← IsLocalization.AtPrime.map_eq_maximalIdeal p R, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  exact Module.Flat.baseChange_of_map_maximalIdeal_eq_maximalIdeal
    (R := R) (S := E) (R' := D) (S' := E) (M := E) (M' := E)
    hm' (LinearMap.id : E →ₗ[E] E) (IsBaseChange.ofEquiv (LinearEquiv.refl E E))

/-- Flatness of a composite follows from flatness after inverting an element whose image is
already a unit. -/
private lemma flat_comp_of_flat_away
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (b : B)
    (hφ : ((algebraMap B (Localization.Away b)).comp φ).Flat)
    (hψ : ψ.Flat) (hb : IsUnit (ψ b)) : (ψ.comp φ).Flat := by
  let L := Localization.Away b
  let : Algebra B C := ψ.toAlgebra
  let g : L →+* C := IsLocalization.Away.lift b hb
  let : Algebra L C := g.toAlgebra
  let : IsScalarTower B L C :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp b hb).symm
  have : Module.Flat B C := hψ
  have : Module.Flat L C := (Module.flat_iff_of_isLocalization L (Submonoid.powers b) C).2
    inferInstance
  have hg : g.Flat := _root_.RingHom.flat_algebraMap_iff.2 inferInstance
  have h := hφ.comp hg
  rwa [← RingHom.comp_assoc, IsLocalization.Away.lift_comp] at h

/-- Flatness at a prime of the target descends to the middle ring of a flat tower once the
contraction of that prime is extended from the bottom ring. -/
private lemma flat_atPrime_of_map_comap_eq
    {A D E : Type*} [CommRing A] [CommRing D] [CommRing E]
    [IsNoetherianRing D] [IsNoetherianRing E]
    (i : A →+* D) (ψ : D →+* E) (q : Ideal E) [q.IsPrime] (hi : i.Flat)
    (hE : ((algebraMap E (Localization.AtPrime q)).comp (ψ.comp i)).Flat)
    (hp : (q.comap (ψ.comp i)).map i = q.comap ψ) :
    ((algebraMap E (Localization.AtPrime q)).comp ψ).Flat := by
  let p := q.comap ψ
  let Dp := Localization.AtPrime p
  let Eq := Localization.AtPrime q
  let g := Localization.localRingHom p q ψ rfl
  let : Algebra D Eq := ((algebraMap E Eq).comp ψ).toAlgebra
  let : Algebra Dp Eq := g.toAlgebra
  let : IsScalarTower D Dp Eq := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (Localization.localRingHom_to_map p q ψ rfl x).symm)
  let : Algebra A D := i.toAlgebra
  let : Algebra A Eq := ((algebraMap D Eq).comp i).toAlgebra
  let : IsScalarTower A D Eq := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A Dp Eq := IsScalarTower.of_algebraMap_eq' (by
    rw [show algebraMap A Eq = (algebraMap D Eq).comp i from rfl,
      IsScalarTower.algebraMap_eq D Dp Eq, RingHom.comp_assoc]
    rfl)
  have : Module.Flat A D := hi
  have : Module.Flat A Dp := Module.Flat.trans A D Dp
  have : Module.Flat A Eq := hE
  have : IsLocalHom (algebraMap Dp Eq) := Localization.isLocalHom_localRingHom p q ψ rfl
  have hm : ((IsLocalRing.maximalIdeal Dp).comap (algebraMap A Dp)).map (algebraMap A Dp) =
      IsLocalRing.maximalIdeal Dp := by
    show (((IsLocalRing.maximalIdeal Dp).comap (algebraMap D Dp)).comap i).map
      ((algebraMap D Dp).comp i) = _
    rw [show (IsLocalRing.maximalIdeal Dp).comap (algebraMap D Dp) = p from
      IsLocalization.AtPrime.under_maximalIdeal Dp p,
      ← Ideal.map_map, show (p.comap i).map i = p from hp,
      IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : Module.Flat Dp Eq := flat_of_flat_of_map_comap_maximalIdeal hm
  exact _root_.RingHom.flat_algebraMap_iff.2 (Module.Flat.trans D Dp Eq)

/-- An ideal equals the extension of its contraction once the induced map of quotients is an
isomorphism. -/
private lemma map_comap_eq_of_exists_quotient_equiv
    {A C : Type*} [CommRing A] [CommRing C] (i : A →+* C) (q : Ideal C)
    (h : ∃ e : (A ⧸ q.comap i) ≃+* (C ⧸ (q.comap i).map i),
      ∀ a, e (Ideal.Quotient.mk (q.comap i) a) = Ideal.Quotient.mk ((q.comap i).map i) (i a)) :
    (q.comap i).map i = q := by
  obtain ⟨e, he⟩ := h
  apply le_antisymm Ideal.map_comap_le
  intro x hx
  obtain ⟨z, hz⟩ := e.surjective (Ideal.Quotient.mk ((q.comap i).map i) x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [he] at hz
  have hd : i a - x ∈ (q.comap i).map i := Ideal.Quotient.eq.mp hz
  have ha : a ∈ q.comap i := by
    show i a ∈ q
    simpa using q.add_mem (Ideal.map_comap_le hd) hx
  have hia : i a ∈ (q.comap i).map i := Ideal.mem_map_of_mem i ha
  simpa using ((q.comap i).map i).sub_mem hia hd

/-! ### The main lemma -/

/-- **Stacks 0GGQ.** A naively rig-flat arrow of `WAdm^Noeth` whose source has a Jacobson
reduction modulo an ideal of definition is rig-flat. -/
@[stacks 0GGQ]
public theorem isRigFlat_of_isNaivelyRigFlat_of_isJacobsonRing_quotient
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (_hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (hJacobson : ∃ I : Ideal A,
      TopologicalRing.IsIdealOfDefinition I ∧ IsJacobsonRing (A ⧸ I))
    (hflat : IsNaivelyRigFlat φ) :
    IsRigFlat φ := by
  classical
  obtain ⟨hφ_adic, hφ_tft, hφ_flat⟩ := hflat
  refine ⟨hφ_adic, hφ_tft, ?_⟩
  intro I hI hIφ f
  let A_f := Localization.Away f
  let B_f := Localization.Away (φ f)
  let I_f := I.map (algebraMap A A_f)
  let J_f := (I.map φ).map (algebraMap B B_f)
  let Ahat := AdicCompletion I_f A_f
  let Bhat := AdicCompletion J_f B_f
  let I_hat := I_f.map (algebraMap A_f Ahat)
  let J_hat := J_f.map (algebraMap B_f Bhat)
  let ψ := completedAwayMap φ I f
  let : TopologicalSpace Ahat := I_hat.adicTopology
  let : IsTopologicalRing Ahat := I_hat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology Ahat Ahat := I_hat.isLinearTopology
  let : TopologicalSpace Bhat := J_hat.adicTopology
  let : IsTopologicalRing Bhat := J_hat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology Bhat Bhat := J_hat.isLinearTopology
  obtain ⟨hψft, hχft, hψcont, hχcont, hχmap⟩ :=
    isTopologicallyOfFiniteType_completedAwayMap φ hφ hφ_tft I hI hIφ f
  refine ⟨isAdic_completedAwayMap φ I f, hψft, ?_⟩
  let χ := (algebraMap B Bhat).comp φ
  have hχcomp : ψ.comp (algebraMap A Ahat) = χ := completedAwayMap_comp_base φ I f
  have hAh : TopologicalRing.IsWeaklyAdmissible Ahat :=
    isWeaklyAdmissible_adicCompletion I_f I_f.fg_of_isNoetherianRing
  have hBh : TopologicalRing.IsWeaklyAdmissible Bhat :=
    isWeaklyAdmissible_adicCompletion J_f J_f.fg_of_isNoetherianRing
  let : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := hA.2.1
  let : T2Space A := hA.2.2
  let : @CompleteSpace Bhat (IsTopologicalAddGroup.rightUniformSpace Bhat) := hBh.2.1
  let : T2Space Bhat := hBh.2.2
  apply (naivelyRigFlat_tfae ψ hψcont hAh hBh
    ⟨I_hat, rfl, I_hat.fg_of_isNoetherianRing⟩ ⟨J_hat, rfl, J_hat.fg_of_isNoetherianRing⟩
    (isAdic_completedAwayMap φ I f)).out 4 1 |>.mp
  intro q hqprime hq
  have hqtfae := rigPoint_tfae ⟨J_hat, show IsAdic J_hat from rfl⟩ q
  have hqlocal := (hqtfae.out 1 8).mp hq
  have hplocal := isRigPointLocalCondition_comap_of_isJacobsonRing_quotient
    hA hBh χ hχcont ⟨I, hI, by rw [hχmap]; rfl⟩ hχft q hqlocal hJacobson
  have hqclosed := isClosedPointAwayFrom_topologicalNilradical_of_isRigPointLocalCondition
    J_hat rfl q hqlocal
  have hpclosed := isClosedPointAwayFrom_topologicalNilradical_of_isRigPointLocalCondition
    I hI (q.comap χ) hplocal
  have hfinite := (rigPoint_relative_tfae hA hBh χ hχcont ⟨I, hI, by rw [hχmap]; rfl⟩
    hχft q hqclosed).out 2 3 |>.mp hpclosed
  let quotχ := Ideal.quotientMap (I := q.comap χ) q χ le_rfl
  have : IsLocalHom quotχ := hfinite.to_isIntegral.isLocalHom Ideal.quotientMap_injective
  have hfunit : IsUnit (Ideal.Quotient.mk (q.comap χ) f) := by
    apply IsUnit.of_map quotχ
    show IsUnit (Ideal.Quotient.mk q (algebraMap B Bhat (φ f)))
    rw [IsScalarTower.algebraMap_apply B B_f Bhat]
    exact ((IsLocalization.Away.algebraMap_isUnit (φ f)).map
      (algebraMap B_f Bhat)).map (Ideal.Quotient.mk q)
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : IsAdicComplete I A := hI.isAdicComplete_iff.mpr ⟨hA.2.1, hA.2.2⟩
  obtain ⟨e, he⟩ := quotient_extendedIdeal_equiv I (q.comap χ) f hfunit
  have hp : (q.comap (ψ.comp (algebraMap A Ahat))).map (algebraMap A Ahat) = q.comap ψ := by
    have hc : (q.comap ψ).comap (algebraMap A Ahat) = q.comap χ := by
      rw [Ideal.comap_comap, hχcomp]
    exact map_comap_eq_of_exists_quotient_equiv (algebraMap A Ahat) (q.comap ψ)
      (by rw [hc]; exact ⟨e, he⟩)
  have hnot : ¬ I ≤ q.comap χ := by
    intro hle
    have hmax : ∀ J : Ideal Bhat, TopologicalRing.IsIdealOfDefinition J →
        Ideal.IsMaximalAmongPrimesAvoiding J q := (hqtfae.out 8 3).mp hqlocal
    have havoid := (hmax J_hat
      (isIdealOfDefinition_of_isAdic (show IsAdic J_hat from rfl))).1
    exact havoid (le_of_eq_of_le hχmap.symm (Ideal.map_le_of_le_comap hle))
  obtain ⟨a, haI, haq⟩ := Set.not_subset.mp hnot
  have hBBhat : (algebraMap B Bhat).Flat :=
    _root_.RingHom.flat_algebraMap_iff.mpr (Module.Flat.trans B B_f Bhat)
  have hBq : ((algebraMap Bhat (Localization.AtPrime q)).comp (algebraMap B Bhat)).Flat :=
    hBBhat.comp (_root_.RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hχq : ((algebraMap Bhat (Localization.AtPrime q)).comp χ).Flat :=
    flat_comp_of_flat_away φ
      ((algebraMap Bhat (Localization.AtPrime q)).comp (algebraMap B Bhat)) (φ a)
      (hφ_flat a (isTopologicallyNilpotent_of_mem_isIdealOfDefinition
        (isIdealOfDefinition_of_isAdic hI) haI)) hBq
      ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q (χ a)).mpr haq)
  exact flat_atPrime_of_map_comap_eq (algebraMap A Ahat) ψ q
    (_root_.RingHom.flat_algebraMap_iff.mpr (Module.Flat.trans A A_f Ahat))
    (by rwa [hχcomp]) hp

end RingHom

end Rig

end
