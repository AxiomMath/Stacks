module

public import StacksFrontier.RingTheory.NaiveCotangent.Henselization
public import StacksFrontier.RingTheory.Rig.CotangentBaseAcyclic
public import StacksFrontier.RingTheory.Rig.EtaleCompletedCotangent
public import StacksFrontier.RingTheory.Rig.FlatIsLocal
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.CombinedLci
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.FactorizationTransfer
public import StacksFrontier.RingTheory.Rig.RigSmoothStableUnderComposition

/-!
# Rig-smoothness along a tower with an étale step

The proof of Stacks 0GCK compares completed naive cotangent complexes along the horizontal
maps of a localization diagram.  Those maps are completions of étale maps, and the comparison
rests on one fact: the completion of an étale algebra has a completed polynomial presentation
whose completed naive cotangent complex has *bijective* differential (Stacks 0GAF).  This file
proves that fact and draws the three consequences used by the locality statement, each
phrased for a tower `R → B → C` of objects of Stacks 0AL4 and read through the transitivity
diagram of Stacks 0ALM and condition (3) of Stacks 0GAJ.

## Main results

* `Rig.exists_presentation_bijective_of_etale` and
  `Rig.exists_presentation_bijective_canonicalMap` — the completion of an étale algebra has a
  presentation with bijective completed cotangent differential.
* `Rig.isRigSmoothArrow_canonicalMap` — the map to the completion of an étale algebra is
  rig-smooth.
* `Rig.isRigSmooth_of_comp_of_bijective` — cancellation: if `R → B` has bijective completed
  cotangent differential and `R → B → C` is rig-smooth then `B → C` is rig-smooth.
* `Rig.exists_factor_innerBaseChange_of_bijective_outer` — if `B → C` has bijective completed
  cotangent differential and local complete intersection reductions (Stacks 0AQJ) and
  `R → C` is rig-smooth, a power of the ideal factors through `NL^∧_{B/R} ⊗_B C`.
* `Rig.isRigSmooth_of_faithfullyFlat_of_bijective_outer` — if moreover `B → C` is faithfully
  flat, then `R → B` is rig-smooth.

## Implementation notes

The presentation with bijective differential is first produced for Mathlib's adic completion,
which is where Stacks 0GAF is formalized, and then transported to any isomorphic object by
`Rig.CompletedPolynomialPresentation.ofAlgEquiv`, which keeps the variables and the ideal and
changes only the quotient identification.

## References

* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
* [Stacks Project, Tag 0GAF](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 0AQJ](https://stacks.math.columbia.edu/tag/0AQJ)
* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GCM](https://stacks.math.columbia.edu/tag/0GCM)
-/

@[expose] public noncomputable section

open TopologicalRing Rig.CompletedPolynomialPresentation
open scoped TensorProduct

universe u

namespace Rig

/-! ## Two small facts about Noetherian adic rings -/

/-- In a Noetherian adic topological ring the ideal witnessing adicness is finitely generated,
which is the membership condition of Situation 0ANH. -/
public theorem exists_fg_isAdic {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsAdic R) (hN : IsNoetherianRing R) :
    ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I := by
  let := hN
  obtain ⟨I, -, hIadic⟩ := hR.1
  exact ⟨I, Ideal.fg_of_isNoetherianRing I, hIadic⟩

/-- A Noetherian adic topological ring has a finitely generated ideal of definition. -/
public theorem exists_idealOfDefinition_fg {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsAdic R) (hN : IsNoetherianRing R) :
    ∃ I : Ideal R, TopologicalRing.IsIdealOfDefinition I ∧ I.FG := by
  let := hN
  obtain ⟨I, hI, -⟩ := hR.1
  exact ⟨I, hI, Ideal.fg_of_isNoetherianRing I⟩

/-! ## Presentations transported along an isomorphism of objects -/

section Transport

variable {A : Type u} [CommRing A] {I : Ideal A} {X Y : AdicFiniteTypeAlgebra.{u, u} A I}

/-- A completed polynomial presentation of `X` presents every object isomorphic to `X`: keep
the variables and the ideal and compose the quotient identification with the isomorphism. -/
public abbrev CompletedPolynomialPresentation.ofAlgEquiv (Q : CompletedPolynomialPresentation I X)
    (e : X.carrier ≃ₐ[A] Y.carrier) : CompletedPolynomialPresentation I Y where
  variableCount := Q.variableCount
  ideal := Q.ideal
  quotientEquiv := Q.quotientEquiv.trans e

/-- The presenting surjection of `Q.ofAlgEquiv e` is that of `Q` followed by `e`. -/
public theorem CompletedPolynomialPresentation.toAlgHom_ofAlgEquiv
    (Q : CompletedPolynomialPresentation I X) (e : X.carrier ≃ₐ[A] Y.carrier)
    (x : Q.completedPolynomialRing) : (Q.ofAlgEquiv e).toAlgHom x = e (Q.toAlgHom x) := rfl

/-- Bijectivity of the differential of the completed naive cotangent complex survives the
transport of a presentation along an isomorphism of objects: the two presentations have the
same completed polynomial algebra, the same kernel and the same formal partial derivatives, and
their differentials differ by the isomorphism applied coordinatewise. -/
public theorem bijective_differential_ofAlgEquiv [IsNoetherianRing A]
    (Q : CompletedPolynomialPresentation I X) (e : X.carrier ≃ₐ[A] Y.carrier)
    (hQ : Function.Bijective (completedNaiveCotangentComplex X Q).differential) :
    Function.Bijective (completedNaiveCotangentComplex Y (Q.ofAlgEquiv e)).differential := by
  have hmem : ∀ x : Q.completedPolynomialRing,
      x ∈ (Q.ofAlgEquiv e).extension.ker ↔ x ∈ Q.extension.ker :=
    fun x => (map_eq_zero_iff e e.injective : e (Q.toAlgHom x) = 0 ↔ Q.toAlgHom x = 0)
  have hker : (Q.ofAlgEquiv e).extension.ker = Q.extension.ker := Ideal.ext hmem
  refine ⟨?_, fun v => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨g', rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    have h0 : (completedNaiveCotangentComplex X Q).differential
        (Algebra.Extension.Cotangent.mk ⟨g'.1, (hmem _).mp g'.2⟩) =
        (completedNaiveCotangentComplex X Q).differential 0 := by
      rw [(completedNaiveCotangentComplex X Q).differential_mk, map_zero]
      funext i
      have hi := congrFun hx i
      rw [(completedNaiveCotangentComplex Y (Q.ofAlgEquiv e)).differential_mk] at hi
      exact (map_eq_zero_iff e e.injective).mp hi
    have hz := hQ.1 h0
    rw [Algebra.Extension.Cotangent.mk_eq_zero_iff] at hz ⊢
    exact (congrArg (fun J => g'.1 ∈ J ^ 2) hker).mpr hz
  · obtain ⟨x₀, hx₀⟩ := hQ.2 (fun i => e.symm (v i))
    obtain ⟨g₀, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x₀
    refine ⟨Algebra.Extension.Cotangent.mk ⟨g₀.1, (hmem _).mpr g₀.2⟩, ?_⟩
    rw [(completedNaiveCotangentComplex Y (Q.ofAlgEquiv e)).differential_mk]
    funext i
    have hi := congrFun hx₀ i
    rw [(completedNaiveCotangentComplex X Q).differential_mk] at hi
    have hi' : Q.toAlgHom ((completedNaiveCotangentComplex X Q).partialDeriv i g₀.1) =
        e.symm (v i) := hi
    show e (Q.toAlgHom ((completedNaiveCotangentComplex X Q).partialDeriv i g₀.1)) = v i
    rw [hi', e.apply_symm_apply]

end Transport

/-! ## The completion of an étale algebra -/

/-- **A completed étale algebra has a presentation with bijective differential.**  Let `S` be
Noetherian, `J ⊆ S` an ideal, `S → S'` étale and `X` an object of (Stacks 0AL4) over `(S, J)`
isomorphic to the `J`-adic completion of `S'`.  Then `X` has a completed polynomial
presentation whose completed naive cotangent complex has bijective differential: Stacks 0GAF
identifies that differential, for the completion of a presentation of `S'`, with the base
change of the bijective differential of the naive cotangent complex of `S'` over `S`. -/
public theorem exists_presentation_bijective_of_etale {S : Type u} [CommRing S]
    [IsNoetherianRing S] (J : Ideal S) {S' : Type u} [CommRing S'] (f : S →+* S')
    (hf : f.Etale) (X : AdicFiniteTypeAlgebra.{u, u} S J)
    (e : AdicCompletion (J.map f) S' ≃+* X.carrier)
    (he : ∀ s, e (algebraMap S' (AdicCompletion (J.map f) S') (f s)) =
      algebraMap S X.carrier s) :
    ∃ Q : CompletedPolynomialPresentation J X,
      Function.Bijective (completedNaiveCotangentComplex X Q).differential := by
  let : Algebra S S' := f.toAlgebra
  have : Algebra.Etale S S' := hf.toAlgebra
  obtain ⟨n, g, hg⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType S S')
  let G : Algebra.Generators S S' (Fin n) := Algebra.Generators.ofAlgHom g hg
  let e' : (adicCompletionObj J (B := S')).carrier ≃ₐ[S] X.carrier :=
    AlgEquiv.ofRingEquiv (f := e) fun s => he s
  have h0 : Function.Bijective (completedNaiveCotangentComplex (adicCompletionObj J (B := S'))
      (presentationCompletion J G)).differential := bijective_completedDifferential J G
  exact ⟨(presentationCompletion J G).ofAlgEquiv e', bijective_differential_ofAlgEquiv _ e' h0⟩

section CompletionOver

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [IsNoetherianRing B] [CommRing A] (f : B →+* A)

/-- The completion over `B` of an étale `B`-algebra has, over an ideal of definition of `B`
defining its topology, a completed polynomial presentation with bijective differential. -/
public theorem exists_presentation_bijective_canonicalMap
    [IsLinearTopology (CompletionOver f) (CompletionOver f)] (hf : f.Etale)
    (hft : FiniteTypeAdicAlgebraForEveryIdeal (CompletionOver.canonicalMap f))
    {I : Ideal B} (hI : TopologicalRing.IsIdealOfDefinition I) (hIadic : _root_.IsAdic I) :
    ∃ Q : CompletedPolynomialPresentation I
        (adicFiniteTypeAlgebra (CompletionOver.canonicalMap f) hft I hI),
      Function.Bijective (completedNaiveCotangentComplex _ Q).differential := by
  let e₀ := CompletionOver.adicCompletionRingEquiv hI hIadic f
  refine exists_presentation_bijective_of_etale I f hf _ e₀.symm fun b => e₀.injective ?_
  refine (e₀.apply_symm_apply _).trans ?_
  exact (congrFun (congrArg DFunLike.coe
    (adicCompletionRingEquiv_comp_canonicalMap f hI hIadic)) b).symm

omit [IsLinearTopology B B] [IsNoetherianRing B] in
/-- **The canonical map to the completion of an étale algebra is rig-smooth.**  For an étale
`f : B →+* A` out of a Noetherian adic ring whose completion over `B` is Noetherian and adic,
`B → (A)^∧` is rig-smooth, with exponent zero: the completed naive cotangent complex of a
suitable presentation has bijective differential, so every scalar factors through it. -/
public theorem isRigSmoothArrow_canonicalMap (hf : f.Etale) (hB : TopologicalRing.IsAdic B)
    (hC : TopologicalRing.IsAdic (CompletionOver f) ∧ IsNoetherianRing (CompletionOver f)) :
    RingHom.IsRigSmoothArrow (CompletionOver.canonicalMap f) := by
  intro _ _ _ _
  obtain ⟨-, hcont, hadic, htft, -⟩ := canonicalMap_facts f hB hC.1 hf
  have hone : RingHom.IsAdic (CompletionOver.canonicalMap f) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (CompletionOver.canonicalMap f) :=
    ⟨hadic, htft⟩
  have hft : FiniteTypeAdicAlgebraForEveryIdeal (CompletionOver.canonicalMap f) :=
    ((adicFiniteType_tfae _ hcont hB hC.1 (exists_idealOfDefinition_fg hB inferInstance)
      (exists_idealOfDefinition_fg hC.1 hC.2)).out 1 6).mp hone
  obtain ⟨I, hI, hIadic⟩ := hB.1
  obtain ⟨Q, hQ⟩ := exists_presentation_bijective_canonicalMap f hf hft hI hIadic
  refine ⟨hcont, hft, I, hI, (isRigSmooth_iff_cotangentFactorization _ Q).mpr ?_⟩
  unfold HasCotangentFactorization
  refine ⟨0, fun a _ => ?_⟩
  let eQ := LinearEquiv.ofBijective _ hQ
  refine ⟨(algebraMap B (adicFiniteTypeAlgebra (CompletionOver.canonicalMap f) hft I hI).carrier
    a) • eQ.symm.toLinearMap, LinearMap.ext fun x => ?_⟩
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    LinearMap.id_apply]
  rw [show eQ.symm ((completedNaiveCotangentComplex _ Q).differential x) = x from
    eQ.symm_apply_apply x]

end CompletionOver

/-! ## Cancelling a step with acyclic completed cotangent complex -/

/-- **Cancellation along a base with acyclic completed cotangent complex, for objects of Stacks
0AL4.**  Let `C` be Noetherian, `I ⊆ C` an ideal and `base → total` a morphism of objects of
Stacks 0AL4 over `(C, I)`, with `base` Noetherian, and suppose that `base` has a completed
polynomial presentation over `(C, I)` whose completed naive cotangent complex has bijective
differential.  If `total` is rig-smooth over `(C, I)` then it is rig-smooth over
`(base, I base)`, as soon as it is an object of Stacks 0AL4 over that pair.

In the transitivity diagram of Stacks 0ALM for `C → base → total` the left-hand complex
`NL^∧_{base/C} ⊗ total` has bijective differential, and
`Rig.exists_factor_right_of_bijective_left` carries a factorization of `I ^ c` through the
differential of `NL^∧_{total/C}` to one through the differential of `NL^∧_{total/base}`. -/
public theorem isRigSmooth_of_isRigSmooth_of_bijective
    {C : Type u} [CommRing C] [IsNoetherianRing C] {I : Ideal C}
    {base total : AdicFiniteTypeAlgebra.{u, u} C I} [IsNoetherianRing base.carrier]
    [Algebra base.carrier total.carrier] [IsScalarTower C base.carrier total.carrier]
    (hc : IsAdicComplete (base.adicIdeal.map (algebraMap base.carrier total.carrier))
      total.carrier)
    [Algebra.FiniteType (base.carrier ⧸ base.adicIdeal)
      (total.carrier ⧸ base.adicIdeal.map (algebraMap base.carrier total.carrier))]
    (P : CompletedPolynomialPresentation I base)
    (hP : Function.Bijective (completedNaiveCotangentComplex _ P).differential)
    (hrigI : IsRigSmooth total) :
    IsRigSmooth (AdicFiniteTypeAlgebra.of (I := base.adicIdeal) total.carrier hc) := by
  classical
  let fiber : AdicFiniteTypeAlgebra.{u, u} (base.carrier) base.adicIdeal :=
    AdicFiniteTypeAlgebra.of (I := base.adicIdeal) total.carrier hc
  let P' := completedPolynomialPresentation base.adicIdeal
    (Ideal.fg_of_isNoetherianRing _) fiber
  let KF := completedNaiveCotangentComplex fiber P'
  let ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin P'.variableCount)
      →ₐ[base.carrier] total.carrier := P'.toAlgHom
  have hψ : Function.Surjective (ψ.restrictScalars C) := P'.toAlgHom_surjective
  have houter : outerDifferential P'.variableCount ψ hψ (fun j => KF.partialDeriv j) =
      KF.differential := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P'.extension) z
    funext j
    exact (cotangentMapOfDerivation_mk (Algebra.Extension.ofSurjective ψ hψ)
      (KF.partialDeriv j) w).trans (congrFun (KF.differential_mk w).symm j)
  let s := P'.variableCount
  let Pt := P.combinedPresentation s (ψ.restrictScalars C) hψ
  let KB := completedNaiveCotangentComplex base P
  let KC := completedNaiveCotangentComplex total Pt
  obtain ⟨c, hfac⟩ := (isRigSmooth_iff_cotangentFactorization total Pt).mp hrigI
  have hrow := P.exact_cotangentMap_combined s ψ hψ
  have key : ∀ x ∈ I ^ c, ∃ h : (Fin s → fiber.carrier) →ₗ[fiber.carrier] P'.extension.Cotangent,
      h ∘ₗ KF.differential =
        (algebraMap base.carrier fiber.carrier (algebraMap C base.carrier x)) • LinearMap.id := by
    intro x hx
    obtain ⟨h, hh⟩ := hfac x hx
    obtain ⟨h₃, hh₃⟩ := exists_factor_right_of_bijective_left
      (P.innerBaseChangeDifferential (C := total) KB) (P.combinedDifferential s ψ hψ KC)
      (outerDifferential s ψ hψ fun j => KF.partialDeriv j)
      ((Algebra.Extension.Cotangent.map (P.innerExtensionHom s ψ hψ)).liftBaseChange
        total.carrier)
      (Algebra.Extension.Cotangent.map (P.outerExtensionHom s ψ hψ))
      (NaiveCotangent.finInl total.carrier P.variableCount s)
      (NaiveCotangent.finProj total.carrier P.variableCount s)
      (P.bijective_innerBaseChangeDifferential (C := total) KB hP)
      (fun z => LinearMap.congr_fun (P.combinedDifferential_comp_innerCotangentMap s ψ hψ KB KC) z)
      (fun z => LinearMap.congr_fun
        (P.outerDifferential_comp_outerCotangentMap s ψ hψ KC (fun j => KF.partialDeriv j)
          (fun j => KF.partialDeriv_continuous j) (fun j => KF.partialDeriv_polynomial j)) z)
      (fun z => (hrow _).mpr ⟨z, rfl⟩) (P.surjective_cotangentMap_combined s ψ hψ)
      (NaiveCotangent.exact_finInl_finProj total.carrier P.variableCount s)
      (NaiveCotangent.surjective_finProj total.carrier P.variableCount s) _ ⟨h, hh⟩
    refine ⟨h₃, ?_⟩
    rw [← houter]
    refine hh₃.trans ?_
    congr 1
    exact IsScalarTower.algebraMap_apply C base.carrier total.carrier x
  have hle : (I ^ c).map (algebraMap C base.carrier) ≤
      (cotangentFactorizationIdeal KF.differential).comap
        (algebraMap base.carrier total.carrier) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨h, hh⟩ := key x hx
    exact ⟨h, hh⟩
  refine (isRigSmooth_iff_cotangentFactorization fiber P').mpr ?_
  unfold HasCotangentFactorization
  refine ⟨c, fun a ha => ?_⟩
  have ha' : a ∈ (I ^ c).map (algebraMap C base.carrier) := by
    rw [Ideal.map_pow]
    exact ha
  exact hle ha'

/-- **Cancellation along a base with acyclic completed cotangent complex.**  Let `g : C →+* B`
and `f : B →+* A` be continuous arrows of `WAdm^Noeth` satisfying condition (6) of Stacks
0GBW, and suppose that over an ideal of definition `I ⊆ C` the target of `g` has a completed
polynomial presentation whose completed naive cotangent complex has bijective differential.
If `f ∘ g` is rig-smooth then so is `f`.

In the transitivity diagram of Stacks 0ALM for `C → B → A` the left-hand complex
`NL^∧_{B/C} ⊗_B A` then has bijective differential, and
`Rig.exists_factor_right_of_bijective_left` carries a factorization of `I ^ c` through the
differential of `NL^∧_{A/C}` to one through the differential of `NL^∧_{A/B}`. -/
public theorem isRigSmooth_of_comp_of_bijective
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C]
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (f : B →+* A) (g : C →+* B) (hfg : Continuous (f.comp g))
    (hftf : FiniteTypeAdicAlgebraForEveryIdeal f) (hftg : FiniteTypeAdicAlgebraForEveryIdeal g)
    {I : Ideal C} (hI : TopologicalRing.IsIdealOfDefinition I)
    (P : CompletedPolynomialPresentation I (adicFiniteTypeAlgebra g hftg I hI))
    (hP : Function.Bijective (completedNaiveCotangentComplex _ P).differential)
    (hrig : RingHom.IsRigSmooth (f.comp g)) :
    RingHom.IsRigSmooth f := by
  classical
  obtain ⟨hft, I₀, hI₀, hrig₀⟩ := hrig
  have hrigI := (isRigSmooth_iff_forall_idealOfDefinition
    (weaklyAdmissible_of_isAdicRing hC) (weaklyAdmissible_of_isAdicRing hA)
    (f.comp g) hfg hft).mp ⟨I₀, hI₀, hrig₀⟩ I hI
  have hJ : TopologicalRing.IsIdealOfDefinition (I.map g) :=
    Rig.isIdealOfDefinition_of_isAdic (hftg I hI).1
  let : Algebra C B := g.toAlgebra
  let : Algebra B A := f.toAlgebra
  let : Algebra C A := (f.comp g).toAlgebra
  let base := adicFiniteTypeAlgebra g hftg I hI
  let total := adicFiniteTypeAlgebra (f.comp g) hft I hI
  let fiber : AdicFiniteTypeAlgebra.{u, u} (base.carrier) base.adicIdeal :=
    adicFiniteTypeAlgebra f hftf (I.map g) hJ
  let : Algebra (base.carrier) (total.carrier) :=
    (inferInstance : Algebra (base.carrier) (fiber.carrier))
  let : IsScalarTower C (base.carrier) (total.carrier) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.FiniteType (base.carrier ⧸ base.adicIdeal)
      (total.carrier ⧸ base.adicIdeal.map (algebraMap base.carrier total.carrier)) :=
    fiber.property.2
  exact ⟨hftf, I.map g, hJ,
    isRigSmooth_of_isRigSmooth_of_bijective (base := base) (total := total) fiber.property.1 P hP
      hrigI⟩

/-! ## Descending a factorization along a step with acyclic completed cotangent complex -/

section Descent

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
  {base total : AdicFiniteTypeAlgebra.{u, u} R I}
  [Algebra base.carrier total.carrier] [IsScalarTower R base.carrier total.carrier]

/-- **From the total complex to the base-changed base complex.**  Let `base → total` be a
morphism of (Stacks 0AL4) over `(R, I)`, presented over `base` by `ψ` with bijective
differential of `NL^∧_{total/base}`, whose reductions `base / Iⁿ → total / Iⁿ` are local
complete intersections.  If `total` is rig-smooth over `(R, I)` then for any presentation `P`
of `base` a power of `I` factors through the differential of `NL^∧_{base/R} ⊗ total`.

By Stacks 0AQJ the map `total ⊗ J/J² → K/K²` of the transitivity diagram of Stacks 0ALM is
injective, and `Rig.exists_factor_left_of_bijective_right` moves the factorization given by
condition (3) of Stacks 0GAJ for the combined presentation of `total` to the left. -/
public theorem exists_factor_innerBaseChange_of_bijective_outer
    (P : CompletedPolynomialPresentation I base) (s : ℕ)
    (ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s) →ₐ[base.carrier]
      total.carrier)
    (hψ : Function.Surjective (ψ.restrictScalars R))
    (F : Fin s → Derivation base.carrier
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)))
    (hFc : ∀ j, @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s)) (F j))
    (hFp : ∀ (j : Fin s) (q : MvPolynomial (Fin s) base.carrier),
      F j (algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)) q) =
        algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
          (MvPolynomial.pderiv j q))
    (hbij : Function.Bijective (outerDifferential s ψ hψ F))
    (hlci : ∀ n : ℕ, RingHom.IsLocalCompleteIntersection (reductionMap base total (n + 1)))
    (htotal : IsRigSmooth total) :
    ∃ c : ℕ, ∀ a : R, a ∈ I ^ c →
      ∃ h : (Fin P.variableCount → total.carrier) →ₗ[total.carrier]
          total.carrier ⊗[base.carrier] P.extension.Cotangent,
        h ∘ₗ P.innerBaseChangeDifferential (C := total) (completedNaiveCotangentComplex base P) =
          (algebraMap R total.carrier a) • LinearMap.id := by
  classical
  let Pt := P.combinedPresentation s (ψ.restrictScalars R) hψ
  let KB := completedNaiveCotangentComplex base P
  let KC := completedNaiveCotangentComplex total Pt
  obtain ⟨c, hc⟩ := (isRigSmooth_iff_cotangentFactorization total Pt).mp htotal
  refine ⟨c, fun a ha => ?_⟩
  obtain ⟨h, hh⟩ := hc a ha
  exact exists_factor_left_of_bijective_right
    (P.innerBaseChangeDifferential (C := total) KB) (P.combinedDifferential s ψ hψ KC)
    (outerDifferential s ψ hψ F)
    ((Algebra.Extension.Cotangent.map (P.innerExtensionHom s ψ hψ)).liftBaseChange
      total.carrier)
    (Algebra.Extension.Cotangent.map (P.outerExtensionHom s ψ hψ))
    (NaiveCotangent.finInl total.carrier P.variableCount s)
    (NaiveCotangent.finProj total.carrier P.variableCount s) hbij
    (P.injective_cotangentMap_innerExtensionHom_of_lci s ψ hψ hlci)
    (fun z => LinearMap.congr_fun (P.combinedDifferential_comp_innerCotangentMap s ψ hψ KB KC) z)
    (fun z => LinearMap.congr_fun
      (P.outerDifferential_comp_outerCotangentMap s ψ hψ KC F hFc hFp) z)
    (P.exact_cotangentMap_combined s ψ hψ) (P.surjective_cotangentMap_combined s ψ hψ) _
    ⟨h, hh⟩

/-- An isomorphism-invariant property of quotient maps does not see how the ideal of the target
is written. -/
private theorem etale_quotientMap_congr {X Y : Type u} [CommRing X] [CommRing Y] (φ : X →+* Y)
    {K : Ideal X} {L L' : Ideal Y} (hL : L = L') (h : K ≤ L.comap φ) (h' : K ≤ L'.comap φ)
    (hφ : (Ideal.quotientMap L φ h).Etale) : (Ideal.quotientMap L' φ h').Etale := by
  subst hL
  exact hφ

omit [IsNoetherianRing R] in
/-- **The reductions of an étale step are local complete intersections.**  If for every `n`
the map `base / (IB)ⁿ⁺¹ → total / (IB)ⁿ⁺¹ total` is étale, then each reduction
`base / Iⁿ⁺¹ → total / Iⁿ⁺¹` of the morphism `base → total` of (Stacks 0AL4) is a local
complete intersection homomorphism, which is the hypothesis of Stacks 0AQJ. -/
public theorem isLocalCompleteIntersection_reductionMap_of_etale
    (h : ∀ n : ℕ, (Ideal.quotientMap ((base.adicIdeal ^ (n + 1)).map
      (algebraMap base.carrier total.carrier)) (algebraMap base.carrier total.carrier)
      Ideal.le_comap_map).Etale) (n : ℕ) :
    RingHom.IsLocalCompleteIntersection (reductionMap base total (n + 1)) := by
  refine Algebra.isLocalCompleteIntersection_of_etale _ (etale_quotientMap_congr _ ?_ _ _ (h n))
  rw [Ideal.map_pow, AdicFiniteTypeAlgebra.map_adicIdeal_tower]

/-- **Rig-smoothness descends along a faithfully flat step with acyclic completed cotangent
complex.**  In the situation of `Rig.exists_factor_innerBaseChange_of_bijective_outer`, if
moreover `total` is faithfully flat over `base`, then rig-smoothness of `total` over `(R, I)`
implies rig-smoothness of `base`: the factorization through the base change of the
differential of `NL^∧_{base/R}` descends (`Rig.exists_factor_of_faithfullyFlat`). -/
public theorem isRigSmooth_of_faithfullyFlat_of_bijective_outer
    [Module.FaithfullyFlat base.carrier total.carrier] (s : ℕ)
    (ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s) →ₐ[base.carrier]
      total.carrier)
    (hψ : Function.Surjective (ψ.restrictScalars R))
    (F : Fin s → Derivation base.carrier
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)))
    (hFc : ∀ j, @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s)) (F j))
    (hFp : ∀ (j : Fin s) (q : MvPolynomial (Fin s) base.carrier),
      F j (algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)) q) =
        algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
          (MvPolynomial.pderiv j q))
    (hbij : Function.Bijective (outerDifferential s ψ hψ F))
    (hlci : ∀ n : ℕ, RingHom.IsLocalCompleteIntersection (reductionMap base total (n + 1)))
    (htotal : IsRigSmooth total) :
    IsRigSmooth base := by
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I) base
  have : Module.FinitePresentation base.carrier P.extension.Cotangent := by
    let : IsNoetherianRing P.completedPolynomialRing := AdicCompletion.isNoetherianRing _
    let : IsNoetherianRing P.extension.Ring := by
      show IsNoetherianRing P.completedPolynomialRing
      infer_instance
    have hfinite : Module.Finite base.carrier P.extension.Cotangent :=
      Algebra.Extension.Cotangent.finite (Ideal.fg_of_isNoetherianRing _)
    let : IsNoetherianRing base.carrier := Rig.isNoetherianRing base
    exact Module.finitePresentation_of_finite base.carrier P.extension.Cotangent
  obtain ⟨c, hc⟩ := exists_factor_innerBaseChange_of_bijective_outer P s ψ hψ F hFc hFp hbij
    hlci htotal
  refine (isRigSmooth_iff_cotangentFactorization base P).mpr ?_
  unfold HasCotangentFactorization
  refine ⟨c, fun a ha => ?_⟩
  obtain ⟨h, hh⟩ := hc a ha
  refine exists_factor_of_faithfullyFlat (T := total.carrier)
    (completedNaiveCotangentComplex base P).differential (algebraMap R base.carrier a)
    ⟨h, ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  exact hh

end Descent

end Rig

end
