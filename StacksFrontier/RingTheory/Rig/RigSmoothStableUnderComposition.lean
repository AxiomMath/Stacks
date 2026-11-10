module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.CombinedPresentation
public import StacksFrontier.RingTheory.Rig.RigEtaleCriterion
public import StacksFrontier.RingTheory.Rig.RigSmooth
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverFiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties

/-!
# Rig-smoothness is stable under composition

**Stacks 0GCM** asserts that the property `P(φ) = `*`φ` is rig-smooth* on arrows of
`WAdm^Noeth` is stable under composition in the sense of Formal Spaces Remark 0GBK, which for
a local property means plain transitivity: for `B → A` and `C → B` in `WAdm^Noeth`,
`P(B → A)` and `P(C → B)` imply `P(C → A)`.

Fix `f : B →+* A` and `g : C →+* B`, both continuous and rig-smooth, and an ideal of
definition `I ⊆ C`.  Two things have to be produced for `f ∘ g`.

* *Adic of topologically finite type.*  This is condition (6) of Stacks 0GBW for the
  composite, obtained by transporting both hypotheses to condition (1) along the equivalences
  of 0GBW, composing them with Stacks 0GBZ, and transporting back.

* *Rig-smoothness over `(C, I)`.*  Writing `base` for `B` as an object of (0AL4) over `(C, I)`,
  `fiber` for `A` as an object over `(B, I B)` and `total` for `A` as an object over `(C, I)`,
  the combined presentation of Stacks 0ALM presents `total` as `C⟨x, y⟩ / K` out of
  presentations `base = C⟨x⟩ / J` and `fiber = B⟨y⟩ / J'`, and the degree-`0` part of the
  diagram of 0ALM relates the three differentials.  Rig-smoothness is then read through
  condition (3) of Stacks 0GAJ, `Rig.isRigSmooth_iff_cotangentFactorization`: a power of `I`
  factors through the differential of the completed naive cotangent complex.  If `a` factors
  the differential of `NL^∧_{base/C}` and `a'` factors that of `NL^∧_{fiber/base}`, then
  `a · a'` factors the differential of `NL^∧_{total/C}`; hence `I ^ (b + c)` factors the
  last one, the exponents multiplying because the scalars that factor a fixed linear map form
  an ideal (`Rig.cotangentFactorizationIdeal`).

That last step is `Rig.exists_factor_of_exact`, a diagram lemma over any commutative ring: it
needs only the two commuting squares, right exactness of the conormal row, surjectivity of its
right-hand map, and a splitting of the free degree-`0` row.  This replaces the source's
argument through condition (2) of 0GAJ, which localizes at the products `fᵢgⱼ` and glues
finite projective modules; the factorization form of the criterion makes projectivity free,
since the degree-`0` terms of all three complexes are finite free.

## Main results

* `Rig.rigSmooth_comp`: **Stacks 0GCM** — the composite of two continuous rig-smooth
  homomorphisms of Noetherian adic topological rings is rig-smooth.
* `Rig.rigSmooth_isStableUnderCompositionNoetherian`: the same fact packaged in the shape of
  Remark 0GBK, taking the locality of rig-smoothness (Stacks 0GCK) as a hypothesis.
* `Rig.exists_factor_of_exact`: the diagram lemma which multiplies the two factorizations.
* `Rig.rigEtale_comp`: **Stacks 0GCX** — the composite of two continuous rig-étale
  homomorphisms of Noetherian adic topological rings is rig-étale.
* `Rig.rigEtale_isStableUnderCompositionNoetherian`: 0GCX in the shape of Remark 0GBK, taking
  the locality of rig-étaleness (Stacks 0AQL, proved downstream in
  `StacksFrontier.RingTheory.Rig.RigEtaleLocality`) as a hypothesis.
* `Rig.rigEtale_cancel` and `Rig.rigEtale_hasNoetherianCancellationProperty`: **Stacks 0GCY** —
  rig-étaleness has the cancellation property of Remark 0GBP.  That predicate carries no
  locality field, so the bundle is unconditional and the tag sits on it.

The rig-étale half of this file reuses the same tower and the same combined presentation of
Stacks 0ALM, but reads rig-étaleness through condition (3) of Stacks 0AJU — annihilation of
`H⁻¹` and `H⁰` of the completed naive cotangent complex — instead of the factorization
condition (3) of Stacks 0GAJ, and moves those annihilations around the six-term exact sequence
of 0ALM rather than multiplying factorizations.

## Implementation notes

The split of the tag across the two statements is deliberate.  The bare `@[stacks 0GCM]` sits
on `Rig.rigSmooth_comp`, which is the unconditional mathematical content of the tag.  The
bundle `Rig.rigSmooth_isStableUnderCompositionNoetherian` is left **untagged** because it
carries a hypothesis that 0GCM itself does not: the `isLocal` field of
`TopologicalRing.PropertyIsStableUnderCompositionNoetherian` is the locality of
rig-smoothness, which is Stacks 0GCK, a separate tag with a separate two-page proof and no
formalization in this library yet.  A tag over the bundle would therefore stand over a
hypothesis rather than over a theorem.  This follows the precedent of Stacks 0GCL,
where `TopologicalRing.rigSmooth_isStableUnderBaseChangeByAdic` takes locality as an input and
is untagged while only the unconditional content
`Rig.rigSmooth_completedTensorProduct_of_isAdic` carries the tag.

Objects of `WAdm^Noeth` are encoded, as elsewhere in this chapter, by the side condition
`TopologicalRing.IsAdic R ∧ IsNoetherianRing R` together with a bare ring homomorphism and a
continuity hypothesis; there is no category object for `WAdm^Noeth` here.

The three objects of (0AL4) are deliberately spelled so that no transport is needed between
them: `fiber` is introduced at the type `Rig.AdicFiniteTypeAlgebra base.carrier base.adicIdeal`
by ascription, which is definitionally the type of an object over `(B, I B)` because
`base.carrier` reduces to `B` and `base.adicIdeal` to `I.map g`, and the algebra instance
`Algebra base.carrier total.carrier` is installed as the instance carried by `fiber.carrier`.
With those two choices the presenting surjection of `fiber` *is* the surjection
`ψ : B⟨y⟩ ↠ total.carrier` that the combined presentation consumes, and no comparison
isomorphism appears anywhere in the proof.

## References

* [Stacks Project, Tag 0GCM](https://stacks.math.columbia.edu/tag/0GCM)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GBZ](https://stacks.math.columbia.edu/tag/0GBZ)
* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GCI](https://stacks.math.columbia.edu/tag/0GCI)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
-/

@[expose] public noncomputable section

open TopologicalRing Rig.CompletedPolynomialPresentation

universe u

namespace Rig

/-! ## The diagram lemma -/

/-- **Two factorizations multiply.**  Given a commutative diagram of `R`-modules

```
Lbase  --inclusion-->  Ltotal  --projection-->  Lfiber
  ↑ dbase                ↑ dtotal                ↑ dfiber
Mbase  --base-------->  Mtotal  --fiber------->  Mfiber  --> 0
```

in which the bottom row is exact at `Mtotal` with `fiber` surjective, `inclusion` is split by
`left`, and `Lfiber` is projective: if `scalarBase` factors through `dbase` and `scalarFiber`
factors through `dfiber`, then their product factors through `dtotal`.

The factor is assembled from a lift of the fibre factor through `fiber`, which projectivity of
`Lfiber` supplies; the correction term `scalarFiber • id - dtotal ∘ lift ∘ projection` takes
`dtotal e` into the image of `inclusion`, where the base factor can be applied after the
splitting. -/
public theorem exists_factor_of_exact
    {R : Type*} [CommRing R]
    {Mbase Mtotal Mfiber Lbase Ltotal Lfiber : Type*}
    [AddCommGroup Mbase] [Module R Mbase]
    [AddCommGroup Mtotal] [Module R Mtotal]
    [AddCommGroup Mfiber] [Module R Mfiber]
    [AddCommGroup Lbase] [Module R Lbase]
    [AddCommGroup Ltotal] [Module R Ltotal]
    [AddCommGroup Lfiber] [Module R Lfiber] [Module.Projective R Lfiber]
    (dbase : Mbase →ₗ[R] Lbase) (dtotal : Mtotal →ₗ[R] Ltotal)
    (dfiber : Mfiber →ₗ[R] Lfiber)
    (base : Mbase →ₗ[R] Mtotal) (fiber : Mtotal →ₗ[R] Mfiber)
    (inclusion : Lbase →ₗ[R] Ltotal) (projection : Ltotal →ₗ[R] Lfiber)
    (left : Ltotal →ₗ[R] Lbase)
    (hleft : left.comp inclusion = LinearMap.id)
    (hsquareBase : ∀ x, dtotal (base x) = inclusion (dbase x))
    (hsquareFiber : ∀ x, dfiber (fiber x) = projection (dtotal x))
    (hfiberSurjective : Function.Surjective fiber)
    (hrow : LinearMap.range base = LinearMap.ker fiber)
    (scalarBase scalarFiber : R)
    (hbase : ∃ factor : Lbase →ₗ[R] Mbase,
      factor.comp dbase = scalarBase • LinearMap.id)
    (hfiber : ∃ factor : Lfiber →ₗ[R] Mfiber,
      factor.comp dfiber = scalarFiber • LinearMap.id) :
    ∃ factor : Ltotal →ₗ[R] Mtotal,
      factor.comp dtotal = (scalarBase * scalarFiber) • LinearMap.id := by
  classical
  obtain ⟨baseFactor, hbaseFactor⟩ := hbase
  obtain ⟨fiberFactor, hfiberFactor⟩ := hfiber
  obtain ⟨lift, hlift⟩ :=
    Module.projective_lifting_property fiber fiberFactor hfiberSurjective
  let correction := scalarFiber • (LinearMap.id : Ltotal →ₗ[R] Ltotal) -
    dtotal.comp (lift.comp projection)
  refine ⟨base.comp (baseFactor.comp (left.comp correction)) +
    scalarBase • (lift.comp projection), ?_⟩
  ext element
  have hmem : scalarFiber • element - lift (projection (dtotal element)) ∈
      LinearMap.ker fiber := by
    simp only [LinearMap.mem_ker, map_sub, map_smul]
    rw [← hsquareFiber, ← LinearMap.comp_apply, hlift,
      ← LinearMap.comp_apply, hfiberFactor]
    simp
  rw [← hrow] at hmem
  obtain ⟨preimage, hpreimage⟩ := hmem
  have hcorrection : correction (dtotal element) = inclusion (dbase preimage) := by
    rw [← hsquareBase, hpreimage]
    simp [correction]
  have hvalue : baseFactor (left (correction (dtotal element))) =
      scalarBase • preimage := by
    rw [hcorrection,
      show left (inclusion (dbase preimage)) = dbase preimage from
        LinearMap.congr_fun hleft (dbase preimage)]
    simpa using LinearMap.congr_fun hbaseFactor preimage
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  rw [hvalue, map_smul, hpreimage, smul_sub, mul_smul]
  abel

/-! ## Two small facts about adic rings -/

/-- A Noetherian adic topological ring has a finitely generated ideal of definition, in the
two shapes the equivalences of Stacks 0GBW and the composition lemma 0GBZ consume. -/
private lemma exists_isIdealOfDefinition_fg {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsNoetherianRing R] (hR : TopologicalRing.IsAdic R) :
    (∃ I : Ideal R, TopologicalRing.IsIdealOfDefinition I ∧ I.FG) ∧
      ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I := by
  obtain ⟨I, hI, hIadic⟩ := hR.1
  exact ⟨⟨I, hI, Ideal.fg_of_isNoetherianRing I⟩, I, Ideal.fg_of_isNoetherianRing I, hIadic⟩

/-- **Condition (6) of Stacks 0GBW is stable under composition.**  Both hypotheses are
transported to condition (1) along the equivalences of 0GBW, composed there by Stacks 0GBZ,
and transported back. -/
private lemma finiteTypeAdicAlgebraForEveryIdeal_comp
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C]
    (hA : TopologicalRing.IsAdic A) (hB : TopologicalRing.IsAdic B)
    (hC : TopologicalRing.IsAdic C)
    (f : B →+* A) (g : C →+* B) (hf : Continuous f) (hg : Continuous g)
    (hftf : FiniteTypeAdicAlgebraForEveryIdeal f)
    (hftg : FiniteTypeAdicAlgebraForEveryIdeal g) :
    FiniteTypeAdicAlgebraForEveryIdeal (f.comp g) := by
  obtain ⟨hAdef, hAfg⟩ := exists_isIdealOfDefinition_fg hA
  obtain ⟨hBdef, hBfg⟩ := exists_isIdealOfDefinition_fg hB
  obtain ⟨hCdef, hCfg⟩ := exists_isIdealOfDefinition_fg hC
  have hcondf := ((adicFiniteType_tfae f hB hA hBdef hAdef).out 6 1).mp hftf
  have hcondg := ((adicFiniteType_tfae g hC hB hCdef hBdef).out 6 1).mp hftg
  have hcomp := TopologicalRing.adicTopologicallyFiniteType_isStableUnderComposition.comp
    ⟨weaklyAdmissible_of_isAdicRing hA, countablyGenerated_nhds_of_isAdicRing hA⟩
    ⟨weaklyAdmissible_of_isAdicRing hB, countablyGenerated_nhds_of_isAdicRing hB⟩
    ⟨weaklyAdmissible_of_isAdicRing hC, countablyGenerated_nhds_of_isAdicRing hC⟩
    hAfg hBfg hCfg f g hf hg hcondf hcondg
  exact ((adicFiniteType_tfae (f.comp g) hC hA hCdef hAdef).out 1 6).mp hcomp

/-! ## The degree-`0` differential of `NL^∧_{B/A} ⊗_B C` as a base change -/

/-- The differential of `NL^∧_{B/A} ⊗_B C` is the base change of the differential of
`NL^∧_{B/A}`, read through the identification `S ⊗_R (Fin n → R) ≅ (Fin n → S)`.  The
left-hand side here is `Rig.CompletedPolynomialPresentation.innerBaseChangeDifferential`
after that identification; the same equation appears inside the construction of
`Rig.tensorProductH0Equiv`, where it identifies the free term of the base-changed complex. -/
private lemma piScalarRight_comp_baseChange {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    [Algebra R S] {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    (d : M →ₗ[R] (Fin n → R)) :
    (TensorProduct.piScalarRight R S S (Fin n)).toLinearMap ∘ₗ (d.baseChange S) =
      (((Algebra.linearMap R S).compLeft (Fin n)) ∘ₗ d).liftBaseChange S := by
  refine TensorProduct.AlgebraTensorModule.curry_injective ?_
  refine LinearMap.ext fun c => LinearMap.ext fun m => ?_
  funext j
  simp [TensorProduct.piScalarRightHom_tmul, Algebra.smul_def, mul_comm]

/-- A composite of `B`-linear maps equal to the scalar `x : R` base changes along `B → T` to a
composite equal to the scalar `x` in `T`. -/
private lemma baseChange_comp_eq_algebraMap_smul {R B T : Type*} [CommRing R] [CommRing B]
    [CommRing T] [Algebra R B] [Algebra B T] [Algebra R T] [IsScalarTower R B T] {M N : Type*}
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] (u : N →ₗ[B] M) (v : M →ₗ[B] N)
    (x : R) (h : u.comp v = algebraMap R B x • LinearMap.id) :
    (u.baseChange T).comp (v.baseChange T) = algebraMap R T x • LinearMap.id := by
  rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  refine LinearMap.ext fun z => ?_
  change (algebraMap R B x) • z = (algebraMap R T x) • z
  rw [IsScalarTower.algebraMap_apply R B T x]
  exact (algebraMap_smul T (algebraMap R B x) z).symm

/-- A factorization of a scalar through the differential of `NL^∧_{B/A}` base changes to a
factorization of its image through the differential of `NL^∧_{B/A} ⊗_B C`. -/
private lemma exists_factor_innerBaseChangeDifferential
    {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    {base : AdicFiniteTypeAlgebra.{u, u} R I}
    (P : CompletedPolynomialPresentation I base)
    {total : AdicFiniteTypeAlgebra.{u, u} R I}
    [Algebra base.carrier total.carrier] [IsScalarTower R base.carrier total.carrier]
    (KB : CompletedNaiveCotangentComplex P) (x : R)
    (h : (Fin P.variableCount → base.carrier) →ₗ[base.carrier] P.extension.Cotangent)
    (hh : h.comp KB.differential = (algebraMap R base.carrier x) • LinearMap.id) :
    ∃ H : (Fin P.variableCount → total.carrier) →ₗ[total.carrier]
        TensorProduct base.carrier total.carrier P.extension.Cotangent,
      H.comp (P.innerBaseChangeDifferential (C := total) KB) =
        (algebraMap R total.carrier x) • LinearMap.id := by
  classical
  let e := TensorProduct.piScalarRight (base.carrier) (total.carrier) (total.carrier)
    (Fin P.variableCount)
  have hbc := baseChange_comp_eq_algebraMap_smul (T := total.carrier) h KB.differential x hh
  refine ⟨(h.baseChange (total.carrier)).comp e.symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun v => ?_
  have hv : P.innerBaseChangeDifferential (C := total) KB v =
      e (KB.differential.baseChange (total.carrier) v) :=
    (LinearMap.congr_fun (piScalarRight_comp_baseChange
      (S := total.carrier) KB.differential) v).symm
  rw [LinearMap.comp_apply, hv, LinearMap.comp_apply,
    show e.symm.toLinearMap (e (KB.differential.baseChange (total.carrier) v)) =
      KB.differential.baseChange (total.carrier) v from e.symm_apply_apply _]
  exact LinearMap.congr_fun hbc v

/-! ## The factorization condition for the combined presentation -/

/-- **The exponents multiply along a tower.**  Let `base` and `total` be objects of (0AL4) over
`(R, I)` with `total` an algebra over `base`, let `base = R⟨x⟩ / J` be a completed polynomial
presentation and let `ψ : base⟨y⟩ ↠ total` be a presentation of `total` over `base`, so that
`Rig.CompletedPolynomialPresentation.combinedPresentation` presents `total` as `R⟨x, y⟩ / K`.
If `I ^ b` factors through the differential of `NL^∧_{base/R}` and `I ^ c` factors through the
differential of `NL^∧_{total/base}`, then `I ^ (b + c)` factors through the differential of
`NL^∧_{total/R}` for the combined presentation.

The two commuting squares of Stacks 0ALM and the right exactness of its conormal row reduce
this to `Rig.exists_factor_of_exact` on a single product `x · y`; products suffice because the
scalars factoring a fixed map form the ideal `Rig.cotangentFactorizationIdeal`. -/
private lemma hasCotangentFactorization_combinedPresentation
    {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    {base : AdicFiniteTypeAlgebra.{u, u} R I}
    (P : CompletedPolynomialPresentation I base)
    {total : AdicFiniteTypeAlgebra.{u, u} R I}
    [Algebra base.carrier total.carrier] [IsScalarTower R base.carrier total.carrier]
    (s : ℕ)
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
    (b c : ℕ)
    (hbase : ∀ a : R, a ∈ I ^ b →
      ∃ h : (Fin P.variableCount → base.carrier) →ₗ[base.carrier] P.extension.Cotangent,
        h.comp (completedNaiveCotangentComplex base P).differential =
          (algebraMap R base.carrier a) • LinearMap.id)
    (hfiber : ∀ a : R, a ∈ I ^ c →
      ∃ h : (Fin s → total.carrier) →ₗ[total.carrier]
          (Algebra.Extension.ofSurjective ψ hψ).Cotangent,
        h.comp (outerDifferential s ψ hψ F) = (algebraMap R total.carrier a) • LinearMap.id) :
    HasCotangentFactorization total
      (P.combinedPresentation s (ψ.restrictScalars R) hψ) := by
  classical
  let Pt := P.combinedPresentation s (ψ.restrictScalars R) hψ
  let KB := completedNaiveCotangentComplex base P
  let KC := completedNaiveCotangentComplex total Pt
  let dtotal := P.combinedDifferential s ψ hψ KC
  have hsquareBase := P.combinedDifferential_comp_innerCotangentMap s ψ hψ KB KC
  have hsquareFiber := P.outerDifferential_comp_outerCotangentMap s ψ hψ KC F hFc hFp
  have hrow : LinearMap.range ((Algebra.Extension.Cotangent.map
        (P.innerExtensionHom s ψ hψ)).liftBaseChange total.carrier) =
      LinearMap.ker (Algebra.Extension.Cotangent.map (P.outerExtensionHom s ψ hψ)) :=
    (LinearMap.exact_iff.mp (P.exact_cotangentMap_combined s ψ hψ)).symm
  have hleft : (LinearMap.funLeft (total.carrier) (total.carrier)
        (Fin.castAdd s)).comp
      (NaiveCotangent.finInl (total.carrier) P.variableCount s) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    funext i
    exact NaiveCotangent.finInl_apply_castAdd (total.carrier) P.variableCount s v i
  have hmul : I ^ b * I ^ c ≤
      (cotangentFactorizationIdeal dtotal).comap (algebraMap R total.carrier) := by
    refine Ideal.mul_le.mpr fun x hx y hy => ?_
    obtain ⟨hx', hhx⟩ := hbase x hx
    obtain ⟨hy', hhy⟩ := hfiber y hy
    obtain ⟨factor, hfactor⟩ := exists_factor_of_exact
      (P.innerBaseChangeDifferential (C := total) KB) dtotal (outerDifferential s ψ hψ F)
      ((Algebra.Extension.Cotangent.map
        (P.innerExtensionHom s ψ hψ)).liftBaseChange total.carrier)
      (Algebra.Extension.Cotangent.map (P.outerExtensionHom s ψ hψ))
      (NaiveCotangent.finInl (total.carrier) P.variableCount s)
      (NaiveCotangent.finProj (total.carrier) P.variableCount s)
      (LinearMap.funLeft (total.carrier) (total.carrier) (Fin.castAdd s)) hleft
      (fun z => LinearMap.congr_fun hsquareBase z)
      (fun z => LinearMap.congr_fun hsquareFiber z)
      (P.surjective_cotangentMap_combined s ψ hψ) hrow
      (algebraMap R total.carrier x) (algebraMap R total.carrier y)
      (exists_factor_innerBaseChangeDifferential P KB x hx' hhx) ⟨hy', hhy⟩
    refine ⟨factor, ?_⟩
    rw [map_mul]
    exact hfactor
  refine ⟨b + c, fun a ha => ?_⟩
  have hmem : algebraMap R total.carrier a ∈ cotangentFactorizationIdeal dtotal :=
    hmul (by rwa [pow_add] at ha)
  obtain ⟨h, hh⟩ := hmem
  exact ⟨h, hh⟩

/-! ## Stacks 0GCM -/

/-- The ideal of definition of an object of (0AL4) over `(R, I)` is the extension of `I`, so its
powers are extended from powers of `I`. -/
private lemma adicIdeal_pow_eq_map {R : Type u} [CommRing R] {I : Ideal R}
    (base : AdicFiniteTypeAlgebra.{u, u} R I) (c : ℕ) :
    base.adicIdeal ^ c = (I ^ c).map (algebraMap R base.carrier) :=
  (Ideal.map_pow (algebraMap R base.carrier) I c).symm

/-- **Stacks Project, Tag 0GCM.**  Rig-smoothness of arrows of `WAdm^Noeth` is stable under
composition: if `f : B →+* A` and `g : C →+* B` are continuous rig-smooth homomorphisms of
Noetherian adic topological rings, then so is `f ∘ g`.

Condition (6) of Stacks 0GBW for the composite is
`Rig.finiteTypeAdicAlgebraForEveryIdeal_comp`.  For rig-smoothness over an ideal of definition
`I ⊆ C`, Stacks 0GCI moves both hypotheses onto `I` and onto `I B`, Stacks 0ALM presents `A`
over `(C, I)` by combining the two presentations, and
`Rig.hasCotangentFactorization_combinedPresentation` multiplies the two factorizations of
condition (3) of Stacks 0GAJ. -/
@[stacks 0GCM]
public theorem rigSmooth_comp
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C]
    (hA : TopologicalRing.IsAdic A ∧ IsNoetherianRing A)
    (hB : TopologicalRing.IsAdic B ∧ IsNoetherianRing B)
    (hC : TopologicalRing.IsAdic C ∧ IsNoetherianRing C)
    (f : B →+* A) (g : C →+* B) (hf : Continuous f) (hg : Continuous g)
    (hPf : RingHom.IsRigSmoothArrow f) (hPg : RingHom.IsRigSmoothArrow g) :
    RingHom.IsRigSmoothArrow (f.comp g) := by
  classical
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing B := hB.2
  have : IsNoetherianRing C := hC.2
  obtain ⟨-, hftf, hrigf⟩ := hPf
  obtain ⟨-, hftg, hrigg⟩ := hPg
  intro _ _ _ _
  have hft := finiteTypeAdicAlgebraForEveryIdeal_comp hA.1 hB.1 hC.1 f g hf hg hftf hftg
  obtain ⟨I, hI, -⟩ := hC.1.1
  have hJ : TopologicalRing.IsIdealOfDefinition (I.map g) :=
    isIdealOfDefinition_of_isAdic (hftg I hI).1
  refine ⟨hf.comp hg, hft, I, hI, ?_⟩
  have hrigBase := (isRigSmooth_iff_forall_idealOfDefinition
    (weaklyAdmissible_of_isAdicRing hC.1) (weaklyAdmissible_of_isAdicRing hB.1)
    g hg hftg).mp hrigg I hI
  have hrigFiber := (isRigSmooth_iff_forall_idealOfDefinition
    (weaklyAdmissible_of_isAdicRing hB.1) (weaklyAdmissible_of_isAdicRing hA.1)
    f hf hftf).mp hrigf (I.map g) hJ
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
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I) base
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
  obtain ⟨b, hbase⟩ := (isRigSmooth_iff_cotangentFactorization base P).mp hrigBase
  obtain ⟨c, hfiber⟩ := (isRigSmooth_iff_cotangentFactorization fiber P').mp hrigFiber
  refine (isRigSmooth_iff_cotangentFactorization total
    (P.combinedPresentation P'.variableCount (ψ.restrictScalars C) hψ)).mpr ?_
  refine hasCotangentFactorization_combinedPresentation P P'.variableCount ψ hψ
    (fun j => KF.partialDeriv j) (fun j => KF.partialDeriv_continuous j)
    (fun j => KF.partialDeriv_polynomial j) b c hbase (fun a ha => ?_)
  have hmap : algebraMap C (base.carrier) a ∈ base.adicIdeal ^ c := by
    rw [adicIdeal_pow_eq_map]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨h, hh⟩ := hfiber (algebraMap C (base.carrier) a) hmap
  refine ⟨h, ?_⟩
  rw [houter, IsScalarTower.algebraMap_apply C (base.carrier) (total.carrier) a]
  exact hh

/-! ## Rig-étaleness along a tower: Stacks 0GCX and 0GCY

The same tower — `base` over `(C, I)`, `fiber` over `(B, I B)` and `total` over `(C, I)` — and
the same combined presentation of Stacks 0ALM serve both the composition statement 0GCX and the
cancellation statement 0GCY for rig-étaleness.  What changes is the criterion read off the
tower: rig-étaleness is condition (3) of Stacks 0AJU,
`Rig.isRigEtale_iff_exists_annihilator_cohomology`, the annihilation of `H⁻¹ = ker d` and
`H⁰ = coker d` by a power of the ideal, and the six-term exact sequence of 0ALM moves those
annihilations around the tower.  Two of its six terms are needed for 0GCX (exactness at
`H⁻¹(NL^∧_{total/C})` and at `H⁰(NL^∧_{total/C})`) and two for 0GCY (exactness at
`H⁻¹(NL^∧_{fiber/base})` and surjectivity onto `H⁰(NL^∧_{fiber/base})`); the exponents add,
because the annihilation of the middle term of an exact sequence is obtained by multiplying the
two annihilating scalars.
-/

attribute [local instance] HasDerivedCategory.standard

section Cohomology

open NaiveCotangent

variable {S : Type*} [CommRing S]

/-- A scalar realised on both terms of a two-term complex by one section `σ` of the
differential annihilates `H⁻¹ = ker d`: an element of the kernel is `σ` of `0`. -/
private lemma smul_H₁_eq_zero_of_section {M : Type*} [AddCommGroup M] [Module S M] {r : ℕ}
    {d : M →ₗ[S] (Fin r → S)} {a : S} {σ : (Fin r → S) →ₗ[S] M}
    (hneg : ∀ y, σ (d y) = a • y) (z : H₁ (TwoTerm.ofFree d)) : a • z = 0 := by
  have hz : d z.1 = 0 := LinearMap.mem_ker.mp z.2
  have hval : a • z.1 = 0 :=
    ((hneg z.1).symm.trans (congrArg σ hz)).trans (map_zero σ)
  exact Subtype.ext (by simpa using hval)

/-- The same section annihilates `H⁰ = coker d`: `a • w` is `d (σ w)`. -/
private lemma smul_H₀_eq_zero_of_section {M : Type*} [AddCommGroup M] [Module S M] {r : ℕ}
    {d : M →ₗ[S] (Fin r → S)} {a : S} {σ : (Fin r → S) →ₗ[S] M}
    (hzero : ∀ w, d (σ w) = a • w) (z : H₀ (TwoTerm.ofFree d)) : a • z = 0 := by
  obtain ⟨w, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.range (TwoTerm.ofFree d).d) z
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨σ w, hzero w⟩

/-- **Annihilators multiply along an exact sequence.**  If `J` annihilates the left-hand
module and `K` the right-hand one, then `J * K` annihilates the middle one. -/
private lemma mul_le_annihilator_of_exact {X Y Z : Type*} [AddCommGroup X] [Module S X]
    [AddCommGroup Y] [Module S Y] [AddCommGroup Z] [Module S Z]
    {α : X →ₗ[S] Y} {β : Y →ₗ[S] Z} (hex : Function.Exact α β) {J K : Ideal S}
    (hJ : J ≤ Module.annihilator S X) (hK : K ≤ Module.annihilator S Z) :
    J * K ≤ Module.annihilator S Y := by
  refine Ideal.mul_le.mpr fun x hx y hy => Module.mem_annihilator.mpr fun v => ?_
  obtain ⟨u, hu⟩ := (hex (y • v)).mp
    (by rw [map_smul]; exact Module.mem_annihilator.mp (hK hy) _)
  rw [mul_smul, ← hu, ← map_smul, Module.mem_annihilator.mp (hJ hx), map_zero]

/-- A surjection transports an annihilator onto its target. -/
private lemma smul_eq_zero_of_surjective {Y Z : Type*} [AddCommGroup Y] [Module S Y]
    [AddCommGroup Z] [Module S Z] {β : Y →ₗ[S] Z} (hβ : Function.Surjective β) {y : S}
    (hy : ∀ v : Y, y • v = 0) (w : Z) : y • w = 0 := by
  obtain ⟨v, rfl⟩ := hβ w
  rw [← map_smul, hy, map_zero]

end Cohomology

/-- A scalar `x` acting by zero on `NL^∧_{base/R}` in the derived category annihilates `H⁻¹` and
`H⁰` of the base-changed complex `X` of Stacks 0ALM, `NL^∧_{base/R} ⊗_{base} total`.  This is
the rig-étale companion of `Rig.exists_factor_innerBaseChangeDifferential`, which transports only
the one-sided factorization that rig-smoothness provides. -/
private lemma smul_cohomology_innerBaseChangeDifferential_eq_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    {base : AdicFiniteTypeAlgebra.{u, u} R I}
    (P : CompletedPolynomialPresentation I base)
    {total : AdicFiniteTypeAlgebra.{u, u} R I}
    [Algebra base.carrier total.carrier] [IsScalarTower R base.carrier total.carrier] (x : R)
    (hx : algebraMap R base.carrier x •
      CategoryTheory.CategoryStruct.id (derivedCompletedNaiveCotangentComplex base P) = 0) :
    (∀ z : NaiveCotangent.H₁ (NaiveCotangent.TwoTerm.ofFree
        (P.innerBaseChangeDifferential (C := total) (completedNaiveCotangentComplex base P))),
      (algebraMap R total.carrier x) • z = 0) ∧
    (∀ z : NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree
        (P.innerBaseChangeDifferential (C := total) (completedNaiveCotangentComplex base P))),
      (algebraMap R total.carrier x) • z = 0) := by
  classical
  obtain ⟨σ, hneg, hzero⟩ := exists_differential_section_of_smul_id_eq_zero base P _ hx
  set KB := completedNaiveCotangentComplex base P
  let e := TensorProduct.piScalarRight (base.carrier) (total.carrier) (total.carrier)
    (Fin P.variableCount)
  have hbcneg := baseChange_comp_eq_algebraMap_smul (T := total.carrier) σ KB.differential x
    (LinearMap.ext hneg)
  have hbczero := baseChange_comp_eq_algebraMap_smul (T := total.carrier) KB.differential σ x
    (LinearMap.ext hzero)
  have hd : ∀ v, P.innerBaseChangeDifferential (C := total) KB v =
      e (KB.differential.baseChange (total.carrier) v) := fun v =>
    (LinearMap.congr_fun (piScalarRight_comp_baseChange (S := total.carrier)
      KB.differential) v).symm
  refine ⟨smul_H₁_eq_zero_of_section (σ := (σ.baseChange (total.carrier)).comp e.symm.toLinearMap)
    fun y => ?_, smul_H₀_eq_zero_of_section
    (σ := (σ.baseChange (total.carrier)).comp e.symm.toLinearMap) fun w => ?_⟩
  · rw [LinearMap.comp_apply, hd y,
      show e.symm.toLinearMap (e (KB.differential.baseChange (total.carrier) y)) =
        KB.differential.baseChange (total.carrier) y from e.symm_apply_apply _]
    exact LinearMap.congr_fun hbcneg y
  · rw [hd, LinearMap.comp_apply,
      show (KB.differential.baseChange (total.carrier))
          ((σ.baseChange (total.carrier)) (e.symm.toLinearMap w)) =
        (algebraMap R (total.carrier) x) • (e.symm.toLinearMap w) from
          LinearMap.congr_fun hbczero _,
      map_smul]
    exact congrArg _ (e.apply_symm_apply w)

/-- **Condition (6) of Stacks 0GBW cancels.**  If `g` and `f ∘ g` are adic of topologically
finite type, then so is `f`: adicness cancels by Stacks 0GXB and topological finite type by
Stacks 0ANS. -/
private lemma finiteTypeAdicAlgebraForEveryIdeal_of_comp
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C]
    (hA : TopologicalRing.IsAdic A) (hB : TopologicalRing.IsAdic B)
    (hC : TopologicalRing.IsAdic C)
    (f : B →+* A) (g : C →+* B) (hf : Continuous f) (hg : Continuous g)
    (hftfg : FiniteTypeAdicAlgebraForEveryIdeal (f.comp g)) :
    FiniteTypeAdicAlgebraForEveryIdeal f := by
  obtain ⟨hAdef, -⟩ := exists_isIdealOfDefinition_fg hA
  obtain ⟨hBdef, -⟩ := exists_isIdealOfDefinition_fg hB
  obtain ⟨hCdef, -⟩ := exists_isIdealOfDefinition_fg hC
  have hcondfg := ((adicFiniteType_tfae (f.comp g) hC hA hCdef hAdef).out 6 1).mp
    hftfg
  have hcond : RingHom.IsAdic f ∧ TopologicalRing.IsTopologicallyOfFiniteType f :=
    ⟨RingHom.isAdic_of_comp g f hg hf hB.1 hcondfg.1,
      TopologicalRing.isTopologicallyOfFiniteType_of_comp g f hcondfg.2⟩
  exact ((adicFiniteType_tfae f hB hA hBdef hAdef).out 1 6).mp hcond

/-- **Stacks Project, Tag 0GCX.**  Rig-étaleness of arrows of `WAdm^Noeth` is stable under
composition in the sense of Formal Spaces Remark 0GBK: if `f : B →+* A` and `g : C →+* B` are
continuous rig-étale homomorphisms of Noetherian adic topological rings, then so is `f ∘ g`.

Condition (6) of Stacks 0GBW for the composite is
`Rig.finiteTypeAdicAlgebraForEveryIdeal_comp`.  For rig-étaleness over an ideal of definition
`I ⊆ C`, Stacks 0GCU moves both hypotheses onto `I` and onto `I B`, Stacks 0ALM presents `A`
over `(C, I)` by combining the two presentations, and the two exactness statements of its
six-term sequence at the middle complex `NL^∧_{A/C}` multiply the two annihilating ideals of
condition (3) of Stacks 0AJU. -/
@[stacks 0GCX]
public theorem rigEtale_comp
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C]
    (hA : TopologicalRing.IsAdic A) (hB : TopologicalRing.IsAdic B)
    (hC : TopologicalRing.IsAdic C)
    (f : B →+* A) (g : C →+* B) (hf : Continuous f) (hg : Continuous g)
    (hPf : RingHom.IsRigEtale f) (hPg : RingHom.IsRigEtale g) :
    RingHom.IsRigEtale (f.comp g) := by
  classical
  obtain ⟨hftf, hrigf⟩ := hPf
  obtain ⟨hftg, hrigg⟩ := hPg
  have hft := finiteTypeAdicAlgebraForEveryIdeal_comp hA hB hC f g hf hg hftf hftg
  obtain ⟨I, hI, -⟩ := hC.1
  have hJ : TopologicalRing.IsIdealOfDefinition (I.map g) :=
    isIdealOfDefinition_of_isAdic (hftg I hI).1
  obtain ⟨hcB, hfinB, hrigBase'⟩ : Rig.IsRigEtaleOver g I :=
    RingHom.IsRigEtale.forall_idealOfDefinition ⟨hftg, hrigg⟩ hg hC hB I hI
  obtain ⟨hcA, hfinA, hrigFiber'⟩ : Rig.IsRigEtaleOver f (I.map g) :=
    RingHom.IsRigEtale.forall_idealOfDefinition ⟨hftf, hrigf⟩ hf hB hA (I.map g) hJ
  refine ⟨hft, ?_⟩
  refine ⟨I, hI, ?_⟩
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
  have hrigBase : IsRigEtale base := hrigBase'
  have hrigFiber : IsRigEtale fiber := hrigFiber'
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I) base
  let P' := completedPolynomialPresentation base.adicIdeal
    (Ideal.fg_of_isNoetherianRing _) fiber
  let KB := completedNaiveCotangentComplex base P
  let KF := completedNaiveCotangentComplex fiber P'
  let ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin P'.variableCount)
      →ₐ[base.carrier] total.carrier := P'.toAlgHom
  have hψ : Function.Surjective (ψ.restrictScalars C) := P'.toAlgHom_surjective
  let Pt := P.combinedPresentation P'.variableCount (ψ.restrictScalars C) hψ
  let KC := completedNaiveCotangentComplex total Pt
  have houter : outerDifferential P'.variableCount ψ hψ (fun j => KF.partialDeriv j) =
      KF.differential := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P'.extension) z
    funext j
    exact (cotangentMapOfDerivation_mk (Algebra.Extension.ofSurjective ψ hψ)
      (KF.partialDeriv j) w).trans (congrFun (KF.differential_mk w).symm j)
  obtain ⟨_, hexH₁, -, -, hexH₀, -⟩ :=
    P.exists_sixTerm_exact_combined P'.variableCount ψ hψ KB KC
      (fun j => KF.partialDeriv j) (fun j => KF.partialDeriv_continuous j)
      (fun j => KF.partialDeriv_polynomial j)
  obtain ⟨b, hb⟩ := (isRigEtale_iff base P).mp hrigBase
  obtain ⟨c, hc⟩ := (isRigEtale_iff fiber P').mp hrigFiber
  -- The two ends of the six-term sequence are annihilated.
  have hinner : ∀ a : C, a ∈ I ^ b →
      (∀ z : NaiveCotangent.H₁ (NaiveCotangent.TwoTerm.ofFree
          (P.innerBaseChangeDifferential (C := total) KB)),
        (algebraMap C total.carrier a) • z = 0) ∧
      (∀ z : NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree
          (P.innerBaseChangeDifferential (C := total) KB)),
        (algebraMap C total.carrier a) • z = 0) := by
    intro a ha
    exact smul_cohomology_innerBaseChangeDifferential_eq_zero (total := total) P a (hb a ha)
  have houterAnn : ∀ a : C, a ∈ I ^ c →
      (∀ z : NaiveCotangent.H₁ (NaiveCotangent.TwoTerm.ofFree
          (outerDifferential P'.variableCount ψ hψ (fun j => KF.partialDeriv j))),
        (algebraMap C total.carrier a) • z = 0) ∧
      (∀ z : NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree
          (outerDifferential P'.variableCount ψ hψ (fun j => KF.partialDeriv j))),
        (algebraMap C total.carrier a) • z = 0) := by
    intro a ha
    have hmem : algebraMap C (base.carrier) a ∈ base.adicIdeal ^ c := by
      rw [adicIdeal_pow_eq_map]
      exact Ideal.mem_map_of_mem _ ha
    obtain ⟨σ, hσneg, hσzero⟩ := exists_differential_section_of_smul_id_eq_zero fiber P'
      (algebraMap (base.carrier) (fiber.carrier) (algebraMap C (base.carrier) a))
      (hc _ hmem)
    have hscal : algebraMap (base.carrier) (fiber.carrier)
        (algebraMap C (base.carrier) a) = algebraMap C total.carrier a :=
      (IsScalarTower.algebraMap_apply C (base.carrier) (total.carrier) a).symm
    rw [hscal] at hσneg hσzero
    rw [houter]
    exact ⟨smul_H₁_eq_zero_of_section hσneg, smul_H₀_eq_zero_of_section hσzero⟩
  have hres : IsRigEtale total := by
    refine (isRigEtale_iff_exists_annihilator_cohomology total Pt).mpr ⟨b + c, ?_, ?_⟩
    · rw [pow_add, Ideal.map_mul]
      exact mul_le_annihilator_of_exact hexH₁
        (Ideal.map_le_iff_le_comap.mpr fun a ha => Module.mem_annihilator.mpr (hinner a ha).1)
        (Ideal.map_le_iff_le_comap.mpr fun a ha => Module.mem_annihilator.mpr (houterAnn a ha).1)
    · rw [pow_add, Ideal.map_mul]
      exact mul_le_annihilator_of_exact hexH₀
        (Ideal.map_le_iff_le_comap.mpr fun a ha => Module.mem_annihilator.mpr (hinner a ha).2)
        (Ideal.map_le_iff_le_comap.mpr fun a ha => Module.mem_annihilator.mpr (houterAnn a ha).2)
  exact ⟨(isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal (f.comp g) hft I hI).1,
    (isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal (f.comp g) hft I hI).2, hres⟩

/-- **The cancellation step of Stacks 0GCY.**  If `f : B →+* A` and `g : C →+* B` are
continuous homomorphisms of Noetherian adic topological rings with `g` and `f ∘ g` rig-étale,
then `f` is rig-étale.

Condition (6) of Stacks 0GBW for `f` is
`Rig.finiteTypeAdicAlgebraForEveryIdeal_of_comp`.  For rig-étaleness over the ideal of
definition `I B` of `B`, Stacks 0GCU moves both hypotheses onto `I` for an ideal of definition
`I ⊆ C`, Stacks 0ALM presents `A` over `(C, I)` by combining the two presentations, and the
exactness of its six-term sequence at `H⁻¹(NL^∧_{A/B})` together with the surjectivity onto
`H⁰(NL^∧_{A/B})` turn the annihilations of condition (3) of Stacks 0AJU for `NL^∧_{B/C}` and
`NL^∧_{A/C}` into one for `NL^∧_{A/B}`. -/
public theorem rigEtale_cancel
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C]
    (hA : TopologicalRing.IsAdic A) (hB : TopologicalRing.IsAdic B)
    (hC : TopologicalRing.IsAdic C)
    (f : B →+* A) (g : C →+* B) (hf : Continuous f) (hg : Continuous g)
    (hPg : RingHom.IsRigEtale g) (hPfg : RingHom.IsRigEtale (f.comp g)) :
    RingHom.IsRigEtale f := by
  classical
  obtain ⟨hftg, hrigg⟩ := hPg
  obtain ⟨hftfg, hrigfg⟩ := hPfg
  have hftf := finiteTypeAdicAlgebraForEveryIdeal_of_comp hA hB hC f g hf hg hftfg
  obtain ⟨I, hI, -⟩ := hC.1
  have hJ : TopologicalRing.IsIdealOfDefinition (I.map g) :=
    isIdealOfDefinition_of_isAdic (hftg I hI).1
  obtain ⟨hcB, hfinB, hrigBase'⟩ : Rig.IsRigEtaleOver g I :=
    RingHom.IsRigEtale.forall_idealOfDefinition ⟨hftg, hrigg⟩ hg hC hB I hI
  obtain ⟨hcA, hfinA, hrigTotal'⟩ : Rig.IsRigEtaleOver (f.comp g) I :=
    RingHom.IsRigEtale.forall_idealOfDefinition ⟨hftfg, hrigfg⟩ (hf.comp hg) hC hA I hI
  refine ⟨hftf, ?_⟩
  refine ⟨I.map g, hJ, ?_⟩
  let : Algebra C B := g.toAlgebra
  let : Algebra B A := f.toAlgebra
  let : Algebra C A := (f.comp g).toAlgebra
  let base := adicFiniteTypeAlgebra g hftg I hI
  let total := adicFiniteTypeAlgebra (f.comp g) hftfg I hI
  let fiber : AdicFiniteTypeAlgebra.{u, u} (base.carrier) base.adicIdeal :=
    adicFiniteTypeAlgebra f hftf (I.map g) hJ
  let : Algebra (base.carrier) (total.carrier) :=
    (inferInstance : Algebra (base.carrier) (fiber.carrier))
  let : IsScalarTower C (base.carrier) (total.carrier) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hrigBase : IsRigEtale base := hrigBase'
  have hrigTotal : IsRigEtale total := hrigTotal'
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I) base
  let P' := completedPolynomialPresentation base.adicIdeal
    (Ideal.fg_of_isNoetherianRing _) fiber
  let KB := completedNaiveCotangentComplex base P
  let KF := completedNaiveCotangentComplex fiber P'
  let ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin P'.variableCount)
      →ₐ[base.carrier] total.carrier := P'.toAlgHom
  have hψ : Function.Surjective (ψ.restrictScalars C) := P'.toAlgHom_surjective
  let Pt := P.combinedPresentation P'.variableCount (ψ.restrictScalars C) hψ
  let KC := completedNaiveCotangentComplex total Pt
  have houter : outerDifferential P'.variableCount ψ hψ (fun j => KF.partialDeriv j) =
      KF.differential := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P'.extension) z
    funext j
    exact (cotangentMapOfDerivation_mk (Algebra.Extension.ofSurjective ψ hψ)
      (KF.partialDeriv j) w).trans (congrFun (KF.differential_mk w).symm j)
  obtain ⟨_, -, hexH₁, -, -, hsurjH₀⟩ :=
    P.exists_sixTerm_exact_combined P'.variableCount ψ hψ KB KC
      (fun j => KF.partialDeriv j) (fun j => KF.partialDeriv_continuous j)
      (fun j => KF.partialDeriv_polynomial j)
  obtain ⟨b, hb⟩ := (isRigEtale_iff base P).mp hrigBase
  obtain ⟨d, hdker, hdcoker⟩ :=
    (isRigEtale_iff_exists_annihilator_cohomology total Pt).mp hrigTotal
  -- `H⁰(NL^∧_{base/C} ⊗ total)` is annihilated by `I ^ b`.
  have hinner : ∀ a : C, a ∈ I ^ b →
      ∀ z : NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree
          (P.innerBaseChangeDifferential (C := total) KB)),
        (algebraMap C total.carrier a) • z = 0 := by
    intro a ha
    exact (smul_cohomology_innerBaseChangeDifferential_eq_zero (total := total) P a (hb a ha)).2
  have hinnerH₀ : (I ^ b).map (algebraMap C total.carrier) ≤
      Module.annihilator total.carrier (NaiveCotangent.H₀
        (NaiveCotangent.TwoTerm.ofFree (P.innerBaseChangeDifferential (C := total) KB))) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha =>
      Module.mem_annihilator.mpr (hinner a ha)
  -- The ideal of `A` extended from `I B` agrees with the one extended from `I`.
  have hpow : ∀ e : ℕ, (base.adicIdeal ^ e).map (algebraMap base.carrier fiber.carrier) =
      (I ^ e).map (algebraMap C total.carrier) := by
    intro e
    rw [adicIdeal_pow_eq_map, Ideal.map_map]
    congr 1
  have hres : IsRigEtale fiber := by
    refine (isRigEtale_iff_exists_annihilator_cohomology fiber P').mpr ⟨d + b, ?_, ?_⟩
    · rw [hpow, pow_add, Ideal.map_mul]
      exact mul_le_annihilator_of_exact hexH₁ hdker hinnerH₀
    · rw [hpow]
      intro x hx
      have hx' : x ∈ (I ^ d).map (algebraMap C total.carrier) :=
        Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_add_right d b)) hx
      refine Module.mem_annihilator.mpr fun z => ?_
      exact smul_eq_zero_of_surjective hsurjH₀
        (fun v => Module.mem_annihilator.mp (hdcoker hx') v) z
  exact ⟨(isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal f hftf (I.map g) hJ).1,
    (isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal f hftf (I.map g) hJ).2, hres⟩

/-- **Stacks Project, Tag 0GCY.**  Rig-étaleness on arrows of `WAdm^Noeth` has the
cancellation property of Formal Spaces Remark 0GBP: for `f : B →+* A` and `g : C →+* B`
continuous homomorphisms of Noetherian adic topological rings, rig-étaleness of `g` and of
`f ∘ g` implies rig-étaleness of `f`.

Unlike the base-change bundle of Tag 0GCL and the composition bundle of Tag 0GBK, the
cancellation predicate `TopologicalRing.HasNoetherianCancellationProperty` carries no locality
field, so this bundle is exactly what Remark 0GBP defines and exactly what 0GCY asserts; the
tag therefore sits on it.  Its content is `Rig.rigEtale_cancel`. -/
@[stacks 0GCY]
public theorem rigEtale_hasNoetherianCancellationProperty :
    TopologicalRing.HasNoetherianCancellationProperty.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ) := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ f g hA hB hC hf hg h
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing B := hB.2
  have : IsNoetherianRing C := hC.2
  intro _ _ _ _
  exact ⟨hf, rigEtale_cancel hA.1 hB.1 hC.1 f g hf hg (h.1).2 (h.2).2⟩

/-- **Stacks 0GCX in the shape of Formal Spaces Remark 0GBK.**  Rig-étaleness is a morphism
property of `WAdm^Noeth` stable under composition, once its locality — Stacks 0AQL — is
supplied.  The composition field is `Rig.rigEtale_comp`.

This statement is deliberately untagged, for the reason given in the implementation notes for
`Rig.rigSmooth_isStableUnderCompositionNoetherian`: the `isLocal` field is the locality of
rig-étaleness, which is Stacks 0AQL, a separate tag, and 0GCX itself carries no such
hypothesis.  The tag sits on the unconditional `Rig.rigEtale_comp`.  The locality is proved,
as `Rig.rigEtale_isLocalNoetherian` in
`StacksFrontier.RingTheory.Rig.RigEtaleLocality`, which imports this file; so it is supplied at
every use site and the hypothesis here is an artefact of the import order. -/
public theorem rigEtale_isStableUnderCompositionNoetherian
    (hlocal : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ)) :
    TopologicalRing.PropertyIsStableUnderCompositionNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ) where
  isLocal := hlocal
  comp := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC f g hf hg hPf hPg
    have : IsNoetherianRing A := hA.2
    have : IsNoetherianRing B := hB.2
    have : IsNoetherianRing C := hC.2
    intro _ _ _ _
    exact ⟨hf.comp hg, rigEtale_comp hA.1 hB.1 hC.1 f g hf hg (hPf).2 (hPg).2⟩

/-- **Stacks 0GCM in the shape of Formal Spaces Remark 0GBK.**  Rig-smoothness is a morphism
property of `WAdm^Noeth` stable under composition, once its locality — Stacks 0GCK — is
supplied.  The composition field is `Rig.rigSmooth_comp`.

This statement is deliberately untagged: it carries the locality hypothesis, which 0GCM itself
does not, and the tag sits on the unconditional `Rig.rigSmooth_comp` instead.  See the
implementation notes of this file. -/
public theorem rigSmooth_isStableUnderCompositionNoetherian
    (hlocal : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigSmoothArrow φ)) :
    TopologicalRing.PropertyIsStableUnderCompositionNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigSmoothArrow φ) where
  isLocal := hlocal
  comp := fun hA hB hC f g hf hg hPf hPg ↦ rigSmooth_comp hA hB hC f g hf hg hPf hPg

end Rig

end
