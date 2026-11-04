module

public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties.FlatnessAndReducedness
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties.NormalityAndDimension
import all StacksFrontier.RingTheory.Henselian.PermanenceOfProperties.NormalityAndDimension
import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GeometricBranches
import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
import StacksFrontier.RingTheory.Rig.AdicBasic

/-!
# Permanence under henselization: Noetherian henselizations and completions

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

06LJ.

## Tag 06LJ — Noetherian henselizations and their completions

For a local ring, being Noetherian is equivalent to the henselization and the strict
henselization being Noetherian. In the Noetherian case their completions are complete
Noetherian local rings, and the expected flatness, formal-smoothness, base-change, and
completion comparison results hold.

### Main definitions

There are no new definitions.

### Main results

* `isNoetherianRing_iff_henselizations`: Noetherianity is invariant under the two
  henselizations, independently of any comparison map between them.
* `isNoetherianRing_iff_henselizations_and_completion_properties`: the same
  equivalences, together with the comparison results for their completions.

### Implementation notes

Henselizations are represented by `IsLocalRing.IsHenselization`, and completions by
`AdicCompletion` at the maximal ideal. Canonical maps between completions are characterized by
their compatibility with the maps from the original rings. The source's equalities of rings are
represented by compatible ring equivalences, while its tensor-product description is expressed
by saying that the tensor product is the corresponding strict henselization.

### References

* [A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique IV*, Theorem 18.6.6 and
  Proposition 18.8.8][EGA]
* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ)

-/

@[expose] public section

section

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

private theorem strictHenselization_noetherian_and_completion_flat.{u, v}
    {R Rh Rsh : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rh Rsh]
    [IsScalarTower R Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    [IsSepClosure (ResidueField R) K]
    [IsHenselization R (ResidueField R) Rh] [IsHenselization R K Rsh] :
    IsNoetherianRing Rsh ∧
      RingHom.Flat (algebraMap Rsh (AdicCompletion (maximalIdeal Rsh) Rsh)) := by
  have := IsHenselization.henselian R (ResidueField R) (Rh := Rh)
  have := IsHenselization.henselian R K (Rh := Rsh)
  have := IsHenselization.isLocalHom (R := R) (L := ResidueField R) (Rh := Rh)
  have := IsSepClosure.sep_closed (ResidueField R) (K := K)
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := K) (Rh := Rsh)
  have := isSepClosed_of_ringEquiv e
  obtain ⟨_, _, _, hm, _, _, ι, x, hb⟩ :=
    henselization_faithfullyFlat_and_quotient_basis
      (R := R) (Rh := Rh) (Rsh := Rsh) (κsep := K)
      (IsHenselization.ind_etale_of_universe_le (R := R) (ResidueField R))
      residueField_map_bijective_of_isHenselization
      (IsHenselization.ind_etale_of_universe_le (R := R) K) ⟨e, he⟩
  have : Module.Flat R (AdicCompletion (maximalIdeal Rsh) Rsh) :=
    completion_flat_of_quotient_basis (maximalIdeal R) (maximalIdeal Rsh) hm x hb
  have hflat : Module.Flat Rsh (AdicCompletion (maximalIdeal Rsh) Rsh) :=
    flat_of_ind_etale_of_flat (AdicCompletion (maximalIdeal Rsh) Rsh)
      (IsHenselization.ind_etale_of_universe_le (R := R) K (Rh := Rsh))
  have hfg : (maximalIdeal Rsh).FG :=
    hm ▸ (maximalIdeal R).fg_of_isNoetherianRing.map _
  have := AdicCompletion.isLocalRing_of_fg hfg
  have := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  have := adicCompletion_isNoetherianRing_of_fg hfg
  have hfaith : Module.FaithfullyFlat Rsh (AdicCompletion (maximalIdeal Rsh) Rsh) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨descent_noetherian (algebraMap Rsh (AdicCompletion (maximalIdeal Rsh) Rsh))
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hfaith) inferInstance,
    RingHom.flat_algebraMap_iff.mpr hflat⟩

private theorem noetherian_henselizations.{u, v}
    (R Rh Rsh : Type u) [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    [IsSepClosure (ResidueField R) K]
    [IsHenselization R (ResidueField R) Rh] [IsHenselization R K Rsh] :
    (IsNoetherianRing R ↔ IsNoetherianRing Rh) ∧
      (IsNoetherianRing R ↔ IsNoetherianRing Rsh) := by
  have := IsHenselization.henselian R K (Rh := Rsh)
  have := IsHenselization.isLocalHom (R := R) (L := ResidueField R) (Rh := Rh)
  have := IsHenselization.isLocalHom (R := R) (L := K) (Rh := Rsh)
  let f : Rh →ₐ[R] Rsh := HenselianLocalRing.indEtaleAlgHom
    (Sh := Rsh)
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh))
    residueField_map_bijective_of_isHenselization.surjective
  have hf : IsLocalHom f := HenselianLocalRing.isLocalHom_indEtaleAlgHom
    (Sh := Rsh)
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh))
    residueField_map_bijective_of_isHenselization.surjective
  let : Algebra Rh Rsh := f.toRingHom.toAlgebra
  have : IsScalarTower R Rh Rsh := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  have : IsLocalHom (algebraMap Rh Rsh) := ⟨hf.map_nonunit⟩
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (henselization_completion_initial_properties (R := R) (Rh := Rh) (Rsh := Rsh) K).1
  · exact isNoetherianRing_of_henselization (R := R) (S := Rh) (ResidueField R)
  · exact (strictHenselization_noetherian_and_completion_flat (R := R) (Rh := Rh) (Rsh := Rsh) K).1
  · exact isNoetherianRing_of_henselization (R := R) (S := Rsh) K

open scoped Topology
open Filter

open Stacks.FormallySmooth.TopologicalRings

private alias continuous_adic_of_map_le := Rig.continuous_adic_of_map_le

private theorem adicCompletion_approx
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    (x : AdicCompletion I R) (n : ℕ) :
    ∃ r : R, x - algebraMap R (AdicCompletion I R) r ∈
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  refine ⟨r, ?_⟩
  rw [← AdicCompletion.ker_evalₐ I hI, RingHom.mem_ker, map_sub]
  simpa [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of] using sub_eq_zero.mpr hr.symm

private theorem completion_ext_to_discrete
    {R A : Type*} [CommRing R] [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    (I : Ideal R) (hI : I.FG) (f g : AdicCompletion I R →+* A)
    (hf : @Continuous _ A (I.map (algebraMap R (AdicCompletion I R))).adicTopology _ f)
    (hg : @Continuous _ A (I.map (algebraMap R (AdicCompletion I R))).adicTopology _ g)
    (h : f.comp (algebraMap R (AdicCompletion I R)) =
      g.comp (algebraMap R (AdicCompletion I R))) : f = g := by
  obtain ⟨n, hn⟩ := (continuous_ringHom_to_discrete_iff _ f).mp hf
  obtain ⟨m, hm⟩ := (continuous_ringHom_to_discrete_iff _ g).mp hg
  ext x
  obtain ⟨r, hr⟩ := adicCompletion_approx I hI x (max n m)
  have key (φ : AdicCompletion I R →+* A) (k : ℕ)
      (hk : (I.map (algebraMap R (AdicCompletion I R))) ^ k ≤ RingHom.ker φ)
      (hle : k ≤ max n m) : φ x = φ (algebraMap R (AdicCompletion I R) r) := by
    exact (RingHom.sub_mem_ker_iff φ).mp (hk (Ideal.pow_le_pow_right hle hr))
  rw [key f n hn (le_max_left n m), key g m hm (le_max_right n m)]
  exact RingHom.congr_fun h r

private theorem completion_extend_to_discrete
    {R A : Type*} [CommRing R] [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    (I : Ideal R) (hI : I.FG) (f : R →+* A)
    (hf : @Continuous R A I.adicTopology _ f) :
    ∃ g : AdicCompletion I R →+* A,
      @Continuous _ A (I.map (algebraMap R (AdicCompletion I R))).adicTopology _ g ∧
      g.comp (algebraMap R (AdicCompletion I R)) = f := by
  obtain ⟨n, hn⟩ := (continuous_ringHom_to_discrete_iff I f).mp hf
  let g := (Ideal.Quotient.lift (I ^ n) f hn).comp (AdicCompletion.evalₐ I n).toRingHom
  refine ⟨g, (continuous_ringHom_to_discrete_iff _ g).mpr ⟨n, ?_⟩, ?_⟩
  · rw [← AdicCompletion.ker_evalₐ I hI]
    intro x hx
    show (Ideal.Quotient.lift (I ^ n) f hn) (AdicCompletion.evalₐ I n x) = 0
    rw [show AdicCompletion.evalₐ I n x = 0 from hx, map_zero]
  · ext r
    simp only [g, RingHom.comp_apply, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply,
      AlgHom.toRingHom_eq_coe]
    rfl

private theorem completionMap_comp_algebraMap
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hIJ : I.map f ≤ J) :
    (adicCompletionMap f I J hIJ).comp
      (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f := by
  ext r : 1
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [RingHom.comp_apply, RingHom.comp_apply, adicCompletionMap_evalₐ]
  simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]

private theorem formallySmooth_completionMap.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (hI : I.FG) (hJ : J.FG)
    (f : R →+* S) (hIJ : I.map f ≤ J)
    (hsm : letI : TopologicalSpace R := ⊥
      letI : DiscreteTopology R := ⟨rfl⟩
      letI : TopologicalSpace S := J.adicTopology
      letI : IsTopologicalRing S := J.nonarchimedean.toIsTopologicalRing
      RingHom.FormallySmoothTop.{u} f) :
    let Ihat := I.map (algebraMap R (AdicCompletion I R))
    let Jhat := J.map (algebraMap S (AdicCompletion J S))
    letI : TopologicalSpace (AdicCompletion I R) := Ihat.adicTopology
    letI : IsTopologicalRing (AdicCompletion I R) := Ihat.nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology (AdicCompletion I R) (AdicCompletion I R) := Ihat.isLinearTopology
    letI : TopologicalSpace (AdicCompletion J S) := Jhat.adicTopology
    letI : IsTopologicalRing (AdicCompletion J S) := Jhat.nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology (AdicCompletion J S) (AdicCompletion J S) := Jhat.isLinearTopology
    IsFormallySmooth.{u} (adicCompletionMap f I J hIJ) := by
  let Ihat := I.map (algebraMap R (AdicCompletion I R))
  let Jhat := J.map (algebraMap S (AdicCompletion J S))
  let : TopologicalSpace (AdicCompletion I R) := Ihat.adicTopology
  let : IsTopologicalRing (AdicCompletion I R) := Ihat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (AdicCompletion I R) (AdicCompletion I R) := Ihat.isLinearTopology
  let : TopologicalSpace (AdicCompletion J S) := Jhat.adicTopology
  let : IsTopologicalRing (AdicCompletion J S) := Jhat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (AdicCompletion J S) (AdicCompletion J S) := Jhat.isLinearTopology
  let F := adicCompletionMap f I J hIJ
  have hF := completionMap_comp_algebraMap f I J hIJ
  have hFcont : Continuous F := by
    apply continuous_adic_of_map_le Ihat Jhat F
    show (I.map (algebraMap R (AdicCompletion I R))).map F ≤ Jhat
    rw [Ideal.map_map, hF, ← Ideal.map_map]
    exact Ideal.map_mono hIJ
  refine ⟨hFcont, ?_⟩
  intro A _ _ _ K hK a ha b hb hab
  let : TopologicalSpace S := J.adicTopology
  let : IsTopologicalRing S := J.nonarchimedean.toIsTopologicalRing
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  have hcoeS : Continuous (algebraMap S (AdicCompletion J S)) :=
    continuous_adic_of_map_le J Jhat _ le_rfl
  have hcomm : (b.comp (algebraMap S (AdicCompletion J S))).comp f =
      (Ideal.Quotient.mk K).comp (a.comp (algebraMap R (AdicCompletion I R))) := by
    rw [RingHom.comp_assoc, ← hF, ← RingHom.comp_assoc, hab, RingHom.comp_assoc]
  obtain ⟨g, hg, hgf, hπg⟩ := hsm A K hK
    (a.comp (algebraMap R (AdicCompletion I R))) continuous_of_discreteTopology
    (b.comp (algebraMap S (AdicCompletion J S))) (hb.comp hcoeS) hcomm
  obtain ⟨G, hG, hGg⟩ := completion_extend_to_discrete J hJ g hg
  refine ⟨G, hG, ?_, ?_⟩
  · apply completion_ext_to_discrete I hI (G.comp F) a (hG.comp hFcont) ha
    rw [RingHom.comp_assoc, hF, ← RingHom.comp_assoc, hGg, hgf]
  · have : DiscreteTopology (A ⧸ K) := by
      apply discreteTopology_iff_isOpen_singleton.mpr
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      have h := (QuotientRing.isOpenMap_coe K) {x} (isOpen_discrete _)
      simpa only [Set.image_singleton] using h
    apply completion_ext_to_discrete J hJ ((Ideal.Quotient.mk K).comp G) b
      ((show Continuous (Ideal.Quotient.mk K) from continuous_of_discreteTopology).comp hG) hb
    rw [RingHom.comp_assoc, hGg, hπg]

open CategoryTheory CategoryTheory.Limits in
private theorem ind_etale_of_base_equiv.{u}
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] [Algebra S A] (e : S ≃+* R)
    (he : ∀ s, algebraMap S A s = algebraMap R A (e s))
    (h : (CommAlgCat.etale R).ind.{u} (CommAlgCat.of R A)) :
    (CommAlgCat.etale S).ind.{u} (CommAlgCat.of S A) := by
  let E := (commAlgCatEquivUnder (.of R)).trans
    ((Under.mapIso e.toCommRingCatIso).trans (commAlgCatEquivUnder (.of S)).symm)
  obtain ⟨J, _, _, pres, hp⟩ := h
  refine ⟨J, inferInstance, inferInstance, (pres.map E.functor).ofIso ?_, fun j => ?_⟩
  · let B : CommAlgCat S := E.functor.obj (CommAlgCat.of R A)
    let f : B ≃ₐ[S] A := { toRingEquiv := RingEquiv.refl A, commutes' := fun s => (he s).symm }
    exact CommAlgCat.isoMk f
  · let B := pres.diag.obj j
    let : Algebra S R := e.toRingHom.toAlgebra
    let : Algebra S B := ((algebraMap R B).comp e.toRingHom).toAlgebra
    have : IsScalarTower S R B := IsScalarTower.of_algebraMap_eq' rfl
    have : Algebra.Etale S R := RingHom.Etale.toAlgebra (RingHom.Etale.of_bijective e.bijective)
    have : Algebra.Etale R B := hp j
    exact Algebra.Etale.comp S R B

private theorem henselization_of_base_equiv.{u, v, w}
    {R S A : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [CommRing A] [IsLocalRing A] [Algebra R A] [Algebra S A]
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {L : Type w} [Field L] [Algebra (ResidueField S) L]
    [IsHenselization R K A]
    (e : S ≃+* R) (he : ∀ s, algebraMap S A s = algebraMap R A (e s))
    (eL : L ≃+* K)
    (hL : ∀ s, eL (algebraMap (ResidueField S) L (residue S s)) =
      algebraMap (ResidueField R) K (residue R (e s))) : IsHenselization S L A := by
  obtain ⟨a, ha⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := K) (Rh := A)
  apply IsHenselization.of_ind_etale.{u,w} (IsHenselization.henselian R K)
    (ind_etale_of_base_equiv e he (IsHenselization.ind_etale_of_universe_le.{u,v} K))
  exact ⟨eL.trans a, fun s => by rw [RingEquiv.trans_apply, hL, ha, ← he]⟩

private theorem henselization_of_algEquiv.{u, v}
    {R A B : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    [CommRing B] [IsLocalRing B] [Algebra R B]
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    [IsHenselization R K A] (e : A ≃ₐ[R] B) : IsHenselization R K B := by
  have := IsHenselization.henselian R K (Rh := A)
  obtain ⟨a, ha⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := K) (Rh := A)
  apply IsHenselization.of_ind_etale.{u,v}
    (Stacks.Henselian.henselianLocalRing_of_ringEquiv e.toRingEquiv)
    ((CommAlgCat.etale R).ind.prop_of_iso (CommAlgCat.isoMk e)
      (IsHenselization.ind_etale_of_universe_le.{u,v} K))
  refine ⟨a.trans (ResidueField.mapEquiv e.toRingEquiv), fun r => ?_⟩
  show ResidueField.map (e : A →+* B) (a _) = _
  rw [ha, ResidueField.map_residue]
  exact congrArg (residue B) (e.commutes r)

private theorem isHenselization_self.{u} (R : Type u) [CommRing R] [HenselianLocalRing R] :
    IsHenselization R (ResidueField R) R := by
  apply IsHenselization.of_ind_etale.{u,u} inferInstance
    ((CommAlgCat.etale R).le_ind _ (show Algebra.Etale R R from inferInstance))
  exact ⟨RingEquiv.refl _, fun _ => rfl⟩


private noncomputable def localizationAtMaximalEquiv (R : Type*) [CommRing R] [IsLocalRing R] :
    R ≃ₐ[R] Localization.AtPrime (maximalIdeal R) :=
  IsLocalization.atUnits R (maximalIdeal R).primeCompl (by
    intro x hx
    change ¬¬IsUnit x at hx
    exact not_not.mp hx)

private theorem localizationAtMaximalEquiv_apply
    (R : Type*) [CommRing R] [IsLocalRing R] (x : R) :
    localizationAtMaximalEquiv R x = algebraMap R (Localization.AtPrime (maximalIdeal R)) x :=
  (localizationAtMaximalEquiv R).commutes x

private theorem strictHenselization_tensorProduct.{u}
    (R S Rh Rsh K : Type u)
    [CommRing R] [IsLocalRing R] [CommRing S] [HenselianLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R (ResidueField R) Rh]
    [Algebra Rh S] [IsScalarTower R Rh S] [IsLocalHom (algebraMap Rh S)]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rh Rsh]
    [IsScalarTower R Rh Rsh] [Field K]
    [Algebra (ResidueField R) K] [IsSepClosure (ResidueField R) K]
    [Algebra (ResidueField S) K] [IsSepClosure (ResidueField S) K]
    [IsHenselization R K Rsh]
    (hres : Function.Bijective (ResidueField.map (algebraMap R S)))
    (hK : ∀ x, algebraMap (ResidueField S) K (ResidueField.map (algebraMap R S) x) =
      algebraMap (ResidueField R) K x) :
    ∃ hT : IsLocalRing (TensorProduct Rh S Rsh),
      letI := hT
      IsHenselization S K (TensorProduct Rh S Rsh) := by
  classical
  have hself := isHenselization_self S
  obtain ⟨B, hB, hBloc, aSB, aSB', tSSB, hSB, hhB, hsB, hiB, hmB, eB, heB⟩ :=
    IsLocalRing.exists_strictHenselization S S
      (IsHenselization.ind_etale_of_universe_le.{u,u} (ResidueField S))
      (by simpa using
        (Function.surjective_id : Function.Surjective (id : ResidueField S → ResidueField S))) K
  let : CommRing B := hB
  let : IsLocalRing B := hBloc
  let : Algebra S B := aSB
  have : IsHenselization S K B := IsHenselization.of_ind_etale.{u,u} hhB hiB ⟨eB, heB⟩
  let : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  let : Algebra Rh B := ((algebraMap S B).comp (algebraMap Rh S)).toAlgebra
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Rh S B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R Rh B := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap S B (algebraMap R S r) = algebraMap S B (algebraMap Rh S (algebraMap R Rh r))
    rw [← IsScalarTower.algebraMap_apply R Rh S]
  let Rp := Localization.AtPrime (maximalIdeal R)
  let Sq := Localization.AtPrime (maximalIdeal S)
  let er := (localizationAtMaximalEquiv R).toRingEquiv
  let es := (localizationAtMaximalEquiv S).toRingEquiv
  let kr := ResidueField.mapEquiv er
  let ks := ResidueField.mapEquiv es
  have : (maximalIdeal S).LiesOver (maximalIdeal R) := ⟨(maximalIdeal_comap _).symm⟩
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver _ _
  let : SMul Rp Sq := (inferInstance : Algebra Rp Sq).toSMul
  have hloc (x : Rp) : es.symm (algebraMap Rp Sq x) = algebraMap R S (er.symm x) := by
    obtain ⟨r, rfl⟩ := er.surjective x
    show es.symm (algebraMap Rp Sq (localizationAtMaximalEquiv R r)) = _
    rw [localizationAtMaximalEquiv_apply, Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq,
      Localization.localRingHom_to_map]
    rw [← localizationAtMaximalEquiv_apply]
    show es.symm (es (algebraMap R S r)) = algebraMap R S (er.symm (er r))
    simp
  have hrLoc : IsLocalHom (algebraMap Rp Sq) := by
    show IsLocalHom (Localization.localRingHom _ _ _ _)
    infer_instance
  have hresloc (x : ResidueField Rp) :
      ks.symm (ResidueField.map (algebraMap Rp Sq) x) =
        ResidueField.map (algebraMap R S) (kr.symm x) := by
    obtain ⟨r, rfl⟩ := residue_surjective x
    show ResidueField.map (es.symm : Sq →+* S)
      (ResidueField.map (algebraMap Rp Sq) (residue Rp r)) =
      ResidueField.map (algebraMap R S) (ResidueField.map (er.symm : Rp →+* R) (residue Rp r))
    simp only [ResidueField.map_residue, RingEquiv.coe_toRingHom]
    exact congrArg (residue S) (hloc r)
  have hbij : Function.Bijective (ResidueField.map (algebraMap Rp Sq)) := by
    have heq : ResidueField.map (algebraMap Rp Sq) =
        (ks.toRingHom.comp (ResidueField.map (algebraMap R S))).comp kr.symm.toRingHom := by
      refine RingHom.ext fun x => ks.symm.injective ?_
      show ks.symm (ResidueField.map (algebraMap Rp Sq) x) =
        ks.symm (ks (ResidueField.map (algebraMap R S) (kr.symm x)))
      rw [RingEquiv.symm_apply_apply]
      exact hresloc x
    rw [heq]
    exact ks.bijective.comp (hres.comp kr.symm.bijective)
  let : Algebra (ResidueField Rp) K :=
    ((algebraMap (ResidueField R) K).comp kr.symm.toRingHom).toAlgebra
  let : Algebra (ResidueField Sq) K :=
    ((algebraMap (ResidueField S) K).comp ks.symm.toRingHom).toAlgebra
  have : IsSepClosure (ResidueField Rp) K :=
    AlgebraicGeometry.isSepClosure_of_equiv_equiv kr (RingEquiv.refl K)
      (by ext x; simp [RingHom.algebraMap_toAlgebra])
  have : IsSepClosure (ResidueField Sq) K :=
    AlgebraicGeometry.isSepClosure_of_equiv_equiv ks (RingEquiv.refl K)
      (by ext x; simp [RingHom.algebraMap_toAlgebra])
  have hKloc (x : ResidueField Rp) : algebraMap (ResidueField Sq) K
      (ResidueField.map (algebraMap Rp Sq) x) = algebraMap (ResidueField Rp) K x := by
    show algebraMap (ResidueField S) K (ks.symm _) = algebraMap (ResidueField R) K (kr.symm x)
    rw [hresloc, hK]
  let : Algebra Rp Rh := ((algebraMap R Rh).comp er.symm.toRingHom).toAlgebra
  let : Algebra Sq S := es.symm.toRingHom.toAlgebra
  let : Algebra Rp S := ((algebraMap R S).comp er.symm.toRingHom).toAlgebra
  let : Algebra Rp Rsh := ((algebraMap R Rsh).comp er.symm.toRingHom).toAlgebra
  let : Algebra Sq B := ((algebraMap S B).comp es.symm.toRingHom).toAlgebra
  let : Algebra Rp B := ((algebraMap R B).comp er.symm.toRingHom).toAlgebra
  have : IsHenselization Rp (ResidueField Rp) Rh :=
    henselization_of_base_equiv er.symm (fun _ => rfl) kr.symm (fun _ => rfl)
  have : IsHenselization Sq (ResidueField Sq) S :=
    henselization_of_base_equiv es.symm (fun _ => rfl) ks.symm (fun _ => rfl)
  have : IsHenselization Rp K Rsh :=
    henselization_of_base_equiv er.symm (fun _ => rfl) (RingEquiv.refl K) (fun _ => rfl)
  have : IsHenselization Sq K B :=
    henselization_of_base_equiv es.symm (fun _ => rfl) (RingEquiv.refl K) (fun _ => rfl)
  have : IsScalarTower Rp Rh S := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap R S (er.symm x) = algebraMap Rh S (algebraMap R Rh (er.symm x))
    exact IsScalarTower.algebraMap_apply R Rh S _
  have : IsScalarTower Rp Sq S := IsScalarTower.of_algebraMap_eq (fun x => (hloc x).symm)
  have : IsScalarTower Rp Rh Rsh := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply R Rh Rsh _
  have : IsScalarTower Sq S B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Rp Sq B := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap S B (algebraMap R S (er.symm x)) =
      algebraMap S B (es.symm (algebraMap Rp Sq x))
    rw [hloc]
  have : IsScalarTower Rp Rh B := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply R Rh B _
  obtain ⟨eRsh, heRsh⟩ := IsHenselization.exists_residueFieldEquiv (R := Rp) (L := K) (Rh := Rsh)
  obtain ⟨eB', heB'⟩ := IsHenselization.exists_residueFieldEquiv (R := Sq) (L := K) (Rh := B)
  obtain ⟨g, hg, hgres, e, he⟩ :=
    IsHenselization.exists_algEquiv_tensorProduct_strictHenselization_atPrime
      (R := R) (S := S) (maximalIdeal R) (maximalIdeal S) hbij K hKloc Rh S Rsh B
      eRsh heRsh eB' heB'
  let : IsLocalRing (TensorProduct Rh S Rsh) := e.toRingEquiv.isLocalRing
  exact ⟨inferInstance, henselization_of_algEquiv K e⟩

private theorem quotient_tensor_completion_equiv
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (I : Ideal A) (hI : I.FG) (J : Ideal B) (hJ : I.map (algebraMap A B) = J)
    (e : C ≃ₐ[A] AdicCompletion I A) (n : ℕ) :
    ∃ q : (B ⧸ J ^ n) ≃+*
      ((C ⊗[A] B) ⧸ (J.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B)) ^ n),
      ∀ b : B, q (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk _ (Algebra.TensorProduct.includeRight b) := by
  classical
  let T := C ⊗[A] B
  let l : C →ₐ[A] T := Algebra.TensorProduct.includeLeft
  let r : B →ₐ[A] T := Algebra.TensorProduct.includeRight
  let IC := I.map (algebraMap A C)
  let JT := J.map r
  have hmap : IC.map e.toAlgHom = I.map (algebraMap A (AdicCompletion I A)) := by
    show (I.map (algebraMap A C)).map e.toRingHom = _
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro a
    exact e.commutes a
  have hCJ : IC.map l = JT := by
    show (I.map (algebraMap A C)).map l.toRingHom = J.map r.toRingHom
    rw [← hJ, Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    exact (l.commutes a).trans (r.commutes a).symm
  let γ : C →ₐ[A] A ⧸ I ^ n := (AdicCompletion.evalₐ I n).comp e.toAlgHom
  have hγ (a : A) : γ (algebraMap A C a) = Ideal.Quotient.mk _ a := by
    show AdicCompletion.evalₐ I n (e (algebraMap A C a)) = _
    rw [e.commutes]
    simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  have hker : RingHom.ker γ.toRingHom = IC ^ n := by
    show (RingHom.ker (AdicCompletion.evalₐ I n).toRingHom).comap e.toAlgHom = _
    rw [AdicCompletion.ker_evalₐ I hI, ← hmap, ← Ideal.map_pow,
      Ideal.comap_map_of_bijective e.toAlgHom e.bijective]
  let g : C →ₐ[A] B ⧸ J ^ n :=
    (Ideal.quotientMapₐ (J ^ n) (Algebra.ofId A B)
      (Ideal.map_le_iff_le_comap.mp (by
        show (I ^ n).map (algebraMap A B) ≤ J ^ n
        rw [Ideal.map_pow, hJ]))).comp γ
  let π : T →ₐ[A] T ⧸ JT ^ n := Ideal.Quotient.mkₐ A (JT ^ n)
  let β : (B ⧸ J ^ n) →ₐ[A] T ⧸ JT ^ n :=
    Ideal.quotientMapₐ (JT ^ n) r (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]))
  have hβ (b : B) : β (Ideal.Quotient.mk _ b) = π (r b) := rfl
  have hleft (c : C) : β (g c) = π (l c) := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (γ c)
    have hd : c - algebraMap A C a ∈ IC ^ n := by
      rw [← hker, RingHom.mem_ker]
      show γ (c - algebraMap A C a) = 0
      rw [map_sub, hγ, ← ha, sub_self]
    have heq : π (l c) = π (l (algebraMap A C a)) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hd' := Ideal.mem_map_of_mem l hd
      rwa [Ideal.map_pow, hCJ] at hd'
    rw [heq, l.commutes]
    have hg : g c = Ideal.Quotient.mk _ (algebraMap A B a) := by
      dsimp only [g, AlgHom.comp_apply]
      rw [← ha]
      rfl
    rw [hg, hβ, r.commutes]
  let F : T →ₐ[A] B ⧸ J ^ n :=
    Algebra.TensorProduct.lift g (Ideal.Quotient.mkₐ A (J ^ n)) (fun _ _ => Commute.all _ _)
  have hFr (b : B) : F (r b) = Ideal.Quotient.mk _ b := by
    show Algebra.TensorProduct.lift g (Ideal.Quotient.mkₐ A (J ^ n)) _
      ((1 : C) ⊗ₜ[A] b) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  have hFker : JT ^ n ≤ RingHom.ker F.toRingHom := by
    show (J.map r) ^ n ≤ _
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro b hb
    show F (r b) = 0
    rw [hFr]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
  let δ : T ⧸ JT ^ n →ₐ[A] B ⧸ J ^ n := Ideal.Quotient.liftₐ _ F hFker
  have hround (t : T) : β (F t) = π t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c b =>
      show β (g c * Ideal.Quotient.mk _ b) = _
      rw [map_mul, hleft, hβ, ← map_mul]
      congr 1
      show (c ⊗ₜ[A] (1 : B)) * ((1 : C) ⊗ₜ[A] b) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hδβ : Function.LeftInverse δ β := by
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact hFr b
  have hβδ : Function.RightInverse δ β := by
    intro t
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact hround t
  exact ⟨RingEquiv.ofBijective β.toRingHom ⟨hδβ.injective, hβδ.surjective⟩, fun b => rfl⟩

private theorem henselization_of_residue_equiv.{u, v, w}
    {R A : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    {K : Type v} {L : Type w} [Field K] [Field L]
    [Algebra (ResidueField R) K] [Algebra (ResidueField R) L]
    [IsHenselization R K A] (e : L ≃+* K)
    (he : ∀ x, e (algebraMap (ResidueField R) L x) = algebraMap (ResidueField R) K x) :
    IsHenselization R L A := by
  obtain ⟨a, ha⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := K) (Rh := A)
  exact ⟨IsHenselization.henselian R K,
    IsHenselization.ind_etale (R := R) (L := K), e.trans a,
    fun r => by rw [RingEquiv.trans_apply, he, ha]⟩

private theorem strictHenselization_tensorProduct_of_residue_equiv.{u, v}
    (R S Rh Rsh : Type u) (K : Type v)
    [CommRing R] [IsLocalRing R] [CommRing S] [HenselianLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R (ResidueField R) Rh]
    [Algebra Rh S] [IsScalarTower R Rh S] [IsLocalHom (algebraMap Rh S)]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rh Rsh]
    [IsScalarTower R Rh Rsh] [Field K]
    [Algebra (ResidueField R) K] [IsSepClosure (ResidueField R) K]
    [Algebra (ResidueField S) K] [IsSepClosure (ResidueField S) K]
    [IsHenselization R K Rsh]
    (hres : Function.Bijective (ResidueField.map (algebraMap R S)))
    (hK : ∀ x, algebraMap (ResidueField S) K (ResidueField.map (algebraMap R S) x) =
      algebraMap (ResidueField R) K x) :
    ∃ hT : IsLocalRing (TensorProduct Rh S Rsh),
      letI := hT
      IsHenselization S K (TensorProduct Rh S Rsh) := by
  obtain ⟨a, ha⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := K) (Rh := Rsh)
  let L := ResidueField Rsh
  let : Algebra (ResidueField R) L := (a.toRingHom.comp (algebraMap (ResidueField R) K)).toAlgebra
  let : Algebra (ResidueField S) L := (a.toRingHom.comp (algebraMap (ResidueField S) K)).toAlgebra
  have : IsSepClosure (ResidueField R) L :=
    AlgebraicGeometry.isSepClosure_of_equiv_equiv (RingEquiv.refl _) a (by ext x; rfl)
  have : IsSepClosure (ResidueField S) L :=
    AlgebraicGeometry.isSepClosure_of_equiv_equiv (RingEquiv.refl _) a (by ext x; rfl)
  have : IsHenselization R L Rsh := henselization_of_residue_equiv a.symm
    (fun x => a.symm_apply_apply _)
  have hL (x : ResidueField R) : algebraMap (ResidueField S) L
      (ResidueField.map (algebraMap R S) x) = algebraMap (ResidueField R) L x :=
    congrArg a (hK x)
  obtain ⟨hT, hhT⟩ := strictHenselization_tensorProduct R S Rh Rsh L hres hL
  let := hT
  let := hhT
  exact ⟨hT, henselization_of_residue_equiv a (fun _ => rfl)⟩

private theorem completion_tensor_equiv
    {A B C : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalRing (C ⊗[A] B)]
    (hA : (maximalIdeal A).FG)
    (hB : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hT : (maximalIdeal B).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B) = maximalIdeal (C ⊗[A] B))
    (e : C ≃ₐ[A] AdicCompletion (maximalIdeal A) A) :
    ∃ E : AdicCompletion (maximalIdeal (C ⊗[A] B)) (C ⊗[A] B) ≃+*
      AdicCompletion (maximalIdeal B) B,
      ∀ b : B, E (algebraMap (C ⊗[A] B) _ (Algebra.TensorProduct.includeRight b)) =
        algebraMap B _ b := by
  let r : B →ₐ[A] C ⊗[A] B := Algebra.TensorProduct.includeRight
  have hq (n : ℕ) : ∃ q : (B ⧸ maximalIdeal B ^ n) ≃+*
      ((C ⊗[A] B) ⧸ maximalIdeal (C ⊗[A] B) ^ n),
      ∀ b : B, q (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (r.toRingHom b) := by
    obtain ⟨q, hq⟩ := quotient_tensor_completion_equiv
      (maximalIdeal A) hA (maximalIdeal B) hB e n
    let eq := Ideal.quotientEquivAlgOfEq A (congrArg (fun I => I ^ n) hT)
    refine ⟨q.trans eq.toRingEquiv, fun b => ?_⟩
    show eq (q (Ideal.Quotient.mk _ b)) = _
    rw [hq]
    exact Ideal.quotientEquivAlgOfEq_mk A _ _
  obtain ⟨E, hE⟩ := exists_adicCompletion_equiv_of_quotient_equiv r.toRingHom
    (maximalIdeal B) (maximalIdeal (C ⊗[A] B)) hT.le hq
  refine ⟨E.symm, fun b => ?_⟩
  apply E.injective
  rw [RingEquiv.apply_symm_apply]
  exact (hE b).symm

/-- A local ring is Noetherian if and only if its henselization is, if and only if its strict
henselization is. In that case the latter two rings have complete Noetherian local completions;
completion does not change the henselization, both completion maps are flat, the map from the
completed ring to the completed strict henselization is formally smooth, strict henselization
commutes with base change to the completion, and completing once more gives the completed strict
henselization. -/
@[stacks 06LJ, ega "IV 18.6.6" "(iv), (v)", ega "IV 18.8.8" "(iv)"]
public theorem isNoetherianRing_iff_henselizations_and_completion_properties.{u, v, w}
    (R Rh Rsh : Type u)
    [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R κsep Rsh] :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let Rhhat := AdicCompletion (maximalIdeal Rh) Rh
    let Rshhat := AdicCompletion (maximalIdeal Rsh) Rsh
    ((IsNoetherianRing R ↔ IsNoetherianRing Rh) ∧
      (IsNoetherianRing R ↔ IsNoetherianRing Rsh)) ∧
    (∀ [Algebra Rh Rsh] [IsScalarTower R Rh Rsh]
      [IsLocalHom (algebraMap Rh Rsh)], IsNoetherianRing R →
      ∃ (hRhatLocal : IsLocalRing Rhat)
        (hRhhatLocal : IsLocalRing Rhhat)
        (hRshhatLocal : IsLocalRing Rshhat),
      letI : IsLocalRing Rhat := hRhatLocal
      letI : IsLocalRing Rhhat := hRhhatLocal
      letI : IsLocalRing Rshhat := hRshhatLocal
      IsNoetherianRing Rhhat ∧ IsNoetherianRing Rshhat ∧
      IsAdicComplete (maximalIdeal Rhhat) Rhhat ∧
      IsAdicComplete (maximalIdeal Rshhat) Rshhat ∧
      ∃ e : Rhat ≃+* Rhhat,
        (∀ x : R, e (algebraMap R Rhat x) =
          algebraMap Rh Rhhat (algebraMap R Rh x)) ∧
        RingHom.Flat (algebraMap Rh Rhhat) ∧
        RingHom.Flat (algebraMap Rsh Rshhat) ∧
        (∃ f : Rhat →+* Rshhat,
          (∀ x : R, f (algebraMap R Rhat x) =
            algebraMap Rsh Rshhat (algebraMap R Rsh x)) ∧
          (letI : TopologicalSpace Rhat := (maximalIdeal Rhat).adicTopology
           letI : IsTopologicalRing Rhat :=
             (maximalIdeal Rhat).nonarchimedean.toIsTopologicalRing
           letI : IsLinearTopology Rhat Rhat := (maximalIdeal Rhat).isLinearTopology
           letI : TopologicalSpace Rshhat := (maximalIdeal Rshhat).adicTopology
           letI : IsTopologicalRing Rshhat :=
             (maximalIdeal Rshhat).nonarchimedean.toIsTopologicalRing
           letI : IsLinearTopology Rshhat Rshhat := (maximalIdeal Rshhat).isLinearTopology
           IsFormallySmooth.{w} f)) ∧
        (let algRhRhat : Algebra Rh Rhat :=
            (e.symm.toRingHom.comp (algebraMap Rh Rhhat)).toAlgebra
         letI : Algebra Rh Rhat := algRhRhat
         ∃ hRhatMapLocal : IsLocalHom (algebraMap R Rhat),
           letI : IsLocalHom (algebraMap R Rhat) := hRhatMapLocal
           ∃ algKhat : Algebra (ResidueField Rhat) κsep,
           letI : Algebra (ResidueField Rhat) κsep := algKhat
           (∀ x : ResidueField R,
             algebraMap (ResidueField Rhat) κsep
                 (ResidueField.map (algebraMap R Rhat) x) =
               algebraMap (ResidueField R) κsep x) ∧
           IsSepClosure (ResidueField Rhat) κsep ∧
           ∃ hTensorLocal : IsLocalRing (Rhat ⊗[Rh] Rsh),
           letI : IsLocalRing (Rhat ⊗[Rh] Rsh) := hTensorLocal
           IsHenselization Rhat κsep (Rhat ⊗[Rh] Rsh) ∧
           ∃ ef : AdicCompletion (maximalIdeal (Rhat ⊗[Rh] Rsh))
               (Rhat ⊗[Rh] Rsh) ≃+* Rshhat,
             ∀ x : Rsh,
               ef (algebraMap (Rhat ⊗[Rh] Rsh)
                   (AdicCompletion (maximalIdeal (Rhat ⊗[Rh] Rsh))
                     (Rhat ⊗[Rh] Rsh))
                   (Algebra.TensorProduct.includeRight x)) =
                 algebraMap Rsh Rshhat x)) := by
  refine ⟨noetherian_henselizations R Rh Rsh κsep, ?_⟩
  intro alg tower localMap hR
  have : IsNoetherianRing R := hR
  obtain ⟨hRh, hRhLocal, hRshLocal, hRhNoeth, hRshNoeth, hRhComplete, hRshComplete,
    hRhFlat, e, he⟩ := henselization_completion_initial_properties
      (R := R) (Rh := Rh) (Rsh := Rsh) κsep
  obtain ⟨hRsh, hRshFlat⟩ := strictHenselization_noetherian_and_completion_flat
    (R := R) (Rh := Rh) (Rsh := Rsh) κsep
  have : IsNoetherianRing Rh := hRh
  have : IsNoetherianRing Rsh := hRsh
  let := hRhLocal
  let := hRshLocal
  let : IsLocalRing (AdicCompletion (maximalIdeal R) R) := inferInstance
  refine ⟨inferInstance, hRhLocal, hRshLocal, hRhNoeth, hRshNoeth,
    hRhComplete, hRshComplete, e, he, hRhFlat, hRshFlat, ?_, ?_⟩
  · have := IsHenselization.isLocalHom (R := R) (L := κsep) (Rh := Rsh)
    let F := adicCompletionMap (algebraMap R Rsh)
      (maximalIdeal R) (maximalIdeal Rsh) (map_maximalIdeal_le _)
    refine ⟨F, ?_, ?_⟩
    · exact RingHom.congr_fun (completionMap_comp_algebraMap (algebraMap R Rsh)
        (maximalIdeal R) (maximalIdeal Rsh) (map_maximalIdeal_le _))
    · have hsm := (henselization_formallyEtale_and_isFormallySmooth.{u, v, w, w, w}
        R Rh Rsh κsep).2.2.2.2.2.2
      convert (formallySmooth_completionMap (maximalIdeal R) (maximalIdeal Rsh)
        (maximalIdeal R).fg_of_isNoetherianRing (maximalIdeal Rsh).fg_of_isNoetherianRing
        (algebraMap R Rsh) (map_maximalIdeal_le _) hsm) using 1
      · exact congrArg Ideal.adicTopology
          (AdicCompletion.maximalIdeal_eq_map_of_fg (maximalIdeal R).fg_of_isNoetherianRing)
      · exact congrArg Ideal.adicTopology
          (AdicCompletion.maximalIdeal_eq_map_of_fg (maximalIdeal Rsh).fg_of_isNoetherianRing)
  · let C := AdicCompletion (maximalIdeal R) R
    let D := AdicCompletion (maximalIdeal Rh) Rh
    let : Algebra Rh C := (e.symm.toRingHom.comp (algebraMap Rh D)).toAlgebra
    let E : C ≃ₐ[Rh] D := AlgEquiv.ofRingEquiv (f := e)
      (fun x => e.apply_symm_apply (algebraMap Rh D x))
    have : IsScalarTower R Rh C := IsScalarTower.of_algebraMap_eq fun r => by
      apply e.injective
      show e (algebraMap R C r) = e (e.symm (algebraMap Rh D (algebraMap R Rh r)))
      rw [e.apply_symm_apply]
      exact he r
    have : IsLocalHom (algebraMap Rh C) := by
      show IsLocalHom ((e.symm : D →+* C).comp (algebraMap Rh D))
      infer_instance
    have hRMap : IsLocalHom (algebraMap R C) :=
      AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal R).fg_of_isNoetherianRing
    have : IsAdicComplete (maximalIdeal C) C :=
      AdicCompletion.isAdicComplete_of_fg (maximalIdeal R).fg_of_isNoetherianRing
    have : HenselianLocalRing C := henselianLocalRing_of_isAdicComplete_maximalIdeal C
    have hres : Function.Bijective (ResidueField.map (algebraMap R C)) :=
      AdicCompletion.residueField_map_bijective_of_fg (maximalIdeal R).fg_of_isNoetherianRing
    let er := RingEquiv.ofBijective (ResidueField.map (algebraMap R C)) hres
    let aK : Algebra (ResidueField C) κsep :=
      ((algebraMap (ResidueField R) κsep).comp er.symm.toRingHom).toAlgebra
    let := aK
    have hK (x : ResidueField R) : algebraMap (ResidueField C) κsep
        (ResidueField.map (algebraMap R C) x) = algebraMap (ResidueField R) κsep x := by
      show algebraMap (ResidueField R) κsep (er.symm (er x)) = _
      rw [er.symm_apply_apply]
    have hsep : IsSepClosure (ResidueField C) κsep :=
      AlgebraicGeometry.isSepClosure_of_equiv_equiv er (RingEquiv.refl κsep) (RingHom.ext hK)
    obtain ⟨hT, hhenT⟩ := strictHenselization_tensorProduct_of_residue_equiv
      R C Rh Rsh κsep hres hK
    let T := C ⊗[Rh] Rsh
    let : IsLocalRing T := hT
    let : IsHenselization C κsep T := hhenT
    refine ⟨hRMap, aK, hK, hsep, hT, hhenT, ?_⟩
    have hmB : (maximalIdeal Rh).map (algebraMap Rh Rsh) = maximalIdeal Rsh := by
      rw [← IsHenselization.map_maximalIdeal (R := R) (L := ResidueField R) (Rh := Rh),
        Ideal.map_map, ← IsScalarTower.algebraMap_eq R Rh Rsh]
      exact IsHenselization.map_maximalIdeal (R := R) (L := κsep) (Rh := Rsh)
    have hmC : (maximalIdeal Rh).map (algebraMap Rh C) = maximalIdeal C := by
      show (maximalIdeal Rh).map (e.symm.toRingHom.comp (algebraMap Rh D)) = _
      rw [← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map_of_fg
        (maximalIdeal Rh).fg_of_isNoetherianRing]
      exact map_ringEquiv_maximalIdeal e.symm
    let r : Rsh →ₐ[Rh] T := Algebra.TensorProduct.includeRight
    have hmT : (maximalIdeal Rsh).map r = maximalIdeal T := by
      show (maximalIdeal Rsh).map r.toRingHom = _
      rw [← hmB, Ideal.map_map]
      have hc : r.toRingHom.comp (algebraMap Rh Rsh) =
          (algebraMap C T).comp (algebraMap Rh C) := by
        apply RingHom.ext
        intro x
        exact (r.commutes x).trans (IsScalarTower.algebraMap_apply Rh C T x)
      rw [hc, ← Ideal.map_map, hmC]
      exact IsHenselization.map_maximalIdeal (R := C) (L := κsep) (Rh := T)
    exact completion_tensor_equiv (maximalIdeal Rh).fg_of_isNoetherianRing hmB hmT E

end

end

section

@[expose] public section

open IsLocalRing

open scoped TensorProduct

/-- Noetherianity is equivalent for a local ring and either of its independently specified
henselizations. The comparison map between the henselizations is unnecessary here. -/
public theorem isNoetherianRing_iff_henselizations.{u, v}
    (R Rh Rsh : Type u)
    [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R κsep Rsh] :
    (IsNoetherianRing R ↔ IsNoetherianRing Rh) ∧
      (IsNoetherianRing R ↔ IsNoetherianRing Rsh) :=
  (isNoetherianRing_iff_henselizations_and_completion_properties.{u, v, u}
    R Rh Rsh κsep).1

end

end

end
