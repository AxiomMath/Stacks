module

public import StacksFrontier.RingTheory.Flat.CompleteDevissageStep
public import StacksFrontier.RingTheory.Flat.CompleteDevissageUniverse
public import StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromSmoothLocus

/-!
# The induction step for flat finite modules, with the module universe free

Let `(R, 𝔪)` be a local ring and let `R → S` be a flat ring map, write `𝔭 = 𝔪S` for the generic
point of the closed fibre, let `𝔮 ⊆ S` be a prime over `𝔪` and let `N` be a finite `S`-module.
Stacks 05I3 says that for a map `α : S^(⊕ r) → N` which becomes an isomorphism over `κ(𝔭)` the
flatness of `N_𝔮` over `R` is equivalent to four conditions expressed in terms of `α` and its
cokernel.

The library form `Module.flat_localizedModule_tfae_of_projective` of that statement puts `R`,
`S` and `N` in a single universe. That is not how the statement is used: in a complete dévissage
(Stacks 05HX) the stage algebras `B i` live in the universe of `R` while the stage modules `M i`
live in the universe of the module being devissaged, and Stacks 05I4 applies Stacks 05I3 to
`α i : B i^(⊕ rᵢ) → M i`. This file proves the same statement with the universe of `N`
independent of that of `R` and `S`, which is the form Stacks 05I4 needs.

## Main definitions

There are no new definitions.

## Main results

* `Module.flat_localizedModule_tfae_of_projective'`: the five equivalent conditions of
  Stacks 05I3 with `R S : Type u` and `N : Type w` independent, with projectivity of `S` as an
  `R`-module taken as a hypothesis.
* `Module.flat_localizedModule_tfae`: the same, with every hypothesis of the source present and
  no others, the projectivity being supplied by Stacks 05FT. This is the form the tag 05I3
  sits on.
* `Module.injective_of_flat_localizedModule_of_projective`: the implication (1) ⟹ (3) of
  Stacks 05I3, extracted because it is the one Stacks 05I4 consumes.
* `Module.injective_of_flat_localizedModule_of_projective_finsupp`: the same implication with
  the finite free module written `Fin r →₀ S` and the fibre hypothesis written by
  `LinearMap.baseChange`, which is how a complete dévissage records its data.

The four steps of the argument itself -- `Module.mul_injective_of_notMem_closedFiber`,
`Module.mem_smul_top_of_tmul_zero`, `Module.mapQ_injective_of_residue_injective` and
`Module.localized_surjective_of_residue_surjective` -- are stated once, in
`StacksFrontier/RingTheory/Flat/CompleteDevissageStep.lean`, already with the universe of the module
free, and are reused here and by the spreading out of Stacks 05IA.

## Implementation notes

The universe of `N` is genuinely free; the two universes cannot be separated further, because
`S` is both the base of `α`'s source and an `R`-algebra, so `R` and `S` must share a universe
for `Algebra.closedFiberIdeal` and its residue field to be formed as the statement needs.

Condition (2), universal injectivity of `α` over `R`, is stated with test modules ranging over
`Type (max u w)` -- the smallest universe containing `R`, `S` and `N` -- via
`Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective`, which keeps the source,
  the target and the test modules in
independent universes. The root `UniversallyInjective` of
`StacksFrontier/RingTheory/Flat/UniversallyInjective.lean` cannot be used: it requires the source
and the target of the map to share a universe, which here they do not. For `w = u` the two
predicates are the same statement, so this is a generalization of the library form and not a
change of it.

The three single-universe inputs -- Stacks 05FQ, Stacks 058P and the passage from universal
injectivity to injectivity -- are replaced by their universe-general forms from
`StacksFrontier/RingTheory/Flat/CompleteDevissageUniverse.lean`. Everything else in the argument,
including the whole of the implications (3) ⟹ (4) ⟹ (5) ⟹ (1), is already universe-general in
the library, and the four steps it rests on are taken verbatim from
`StacksFrontier/RingTheory/Flat/CompleteDevissageStep.lean` rather than restated here.

## References

* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
-/

@[expose] public section

open scoped TensorProduct

universe u w

namespace Module

/-- **Stacks Project, Tag 05I3, the five equivalent conditions**, with the universe of the module
independent of that of the base ring and the algebra, and with projectivity of `S` over `R` as a
hypothesis rather than a consequence of Stacks 05FT.

Fix a finite free map whose scalar extension to the residue field of the generic point `p` of the
closed fibre is an isomorphism. For a prime `q` over the maximal ideal, the following are
equivalent: `N_q` is flat over `R`; the map is universally injective over `R` and its localized
cokernel is flat; the map is injective and that cokernel is flat; its localization at `p` is an
isomorphism and that cokernel is flat; and its localization at `q` is injective and that cokernel
is flat.

This generalizes `Module.flat_localizedModule_tfae_of_projective`, which requires `N` to live in
the universe of `R` and `S`. -/
public theorem flat_localizedModule_tfae_of_projective'
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Flat R S] [Module.Projective R S]
    [(Algebra.closedFiberIdeal R S).IsPrime]
    (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (r : ℕ) (alpha : (Fin r → S) →ₗ[S] N)
    (halpha : Function.Bijective (alpha.rTensor (Algebra.closedFiberIdeal R S).ResidueField)) :
    List.TFAE [
      Module.Flat R (LocalizedModule q.primeCompl N),
      Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{max u w}
        (alpha.restrictScalars R) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)),
      Function.Injective alpha ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)),
      Function.Bijective
          (LocalizedModule.map (Algebra.closedFiberIdeal R S).primeCompl alpha) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)),
      Function.Injective (LocalizedModule.map q.primeCompl alpha) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha))] := by
  have : Module.Projective R (Fin r → S) :=
    Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype :
      (Π₀ _ : Fin r, S) ≃ₗ[R] (Fin r → S))
  let p := Algebra.closedFiberIdeal R S
  have hpq : p ≤ q := by
    show Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≤ q
    rw [Ideal.map_le_iff_le_comap, hq]
  let fq := (LocalizedModule.map q.primeCompl alpha).restrictScalars R
  let gq := (LocalizedModule.map q.primeCompl (LinearMap.range alpha).mkQ).restrictScalars R
  have hex : Function.Exact fq gq :=
    LocalizedModule.map_exact q.primeCompl alpha _ alpha.exact_map_mkQ_range
  have hsurj : Function.Surjective gq := LocalizedModule.map_surjective _ _
    (Submodule.mkQ_surjective _)
  have hfree : Module.Flat R (LocalizedModule q.primeCompl (Fin r → S)) := by
    have : Module.Flat S (LocalizedModule q.primeCompl (Fin r → S)) :=
      Module.Flat.trans S (Localization q.primeCompl) _
    exact Module.Flat.trans R S _
  tfae_have 1 → 2 := by
    intro hN
    have hcomp := Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal'
      (((LocalizedModule.mkLinearMap q.primeCompl N).comp alpha).restrictScalars R)
      (mapQ_injective_of_residue_injective R S p q rfl hpq N r alpha halpha.1)
    have hui : ∀ (Q : Type max u w) [AddCommGroup Q] [Module R Q],
        Function.Injective ((alpha.restrictScalars R).rTensor Q) := by
      intro Q _ _
      have hh := hcomp Q
      rw [LinearMap.restrictScalars_comp, LinearMap.rTensor_comp] at hh
      change Function.Injective
        (((LocalizedModule.mkLinearMap q.primeCompl N).restrictScalars R).rTensor Q ∘
          (alpha.restrictScalars R).rTensor Q) at hh
      exact hh.of_comp
    have huq : ∀ (Q : Type max u w) [AddCommGroup Q] [Module R Q],
        Function.Injective (fq.rTensor Q) := fun Q _ _ =>
      IsLocalizedModule.rTensor_injective_of_rTensor_injective q.primeCompl
        (LocalizedModule.mkLinearMap q.primeCompl (Fin r → S))
        (LocalizedModule.mkLinearMap q.primeCompl N) alpha
        (LocalizedModule.map q.primeCompl alpha)
        (IsLocalizedModule.map_comp _ _ _ _) Q (hui Q)
    exact ⟨hui, (flat_of_middle_flat_of_rTensor_injective fq gq hsurj hex huq).2⟩
  tfae_have 2 → 3 := fun ⟨hui, hC⟩ =>
    ⟨injective_of_rTensor_injective (alpha.restrictScalars R) hui, hC⟩
  tfae_have 3 → 4 := fun ⟨hi, hC⟩ =>
    ⟨⟨LocalizedModule.map_injective _ _ hi,
      localized_surjective_of_residue_surjective S p _ N alpha halpha.2⟩, hC⟩
  tfae_have 4 → 5 := by
    rintro ⟨hi, hC⟩
    have hmk : Function.Injective (LocalizedModule.mkLinearMap p.primeCompl (Fin r → S)) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl (Fin r → S))).mp hx
      funext i
      apply mul_injective_of_notMem_closedFiber R S p rfl s s.2
      simpa [Submonoid.smul_def, smul_eq_mul] using congrFun hs i
    have hinj : Function.Injective alpha := by
      intro x y hxy
      apply hmk
      apply hi.1
      simpa only [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk] using
        congrArg (fun z => LocalizedModule.mk z (1 : p.primeCompl)) hxy
    exact ⟨LocalizedModule.map_injective _ _ hinj, hC⟩
  tfae_have 5 → 1 := fun ⟨hi, hC⟩ =>
    flat_of_flat_of_flat fq gq hi hex hsurj
  tfae_finish

/-- **Stacks Project, Tag 05I3, the five equivalent conditions**, with the universe of the module
independent of that of the base ring and the algebra.

Every hypothesis of the source is present and no others: `R` is local, `R → S` is flat of finite
presentation with geometrically integral fibres, `q` lies over the maximal ideal, `N` is a finite
`S`-module and `alpha` becomes an isomorphism over the residue field of `𝔪S`. Projectivity of
`S` over `R`, which the source invokes to run the argument, is Stacks 05FT
(`Algebra.projective_of_geometricallyIntegral_fibres`) applied to the geometrically integral
fibres. -/
@[stacks 05I3 "the five equivalent conditions"]
public theorem flat_localizedModule_tfae
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [(Algebra.closedFiberIdeal R S).IsPrime]
    (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (r : ℕ) (alpha : (Fin r → S) →ₗ[S] N)
    (halpha : Function.Bijective (alpha.rTensor (Algebra.closedFiberIdeal R S).ResidueField)) :
    List.TFAE [
      Module.Flat R (LocalizedModule q.primeCompl N),
      Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{max u w}
        (alpha.restrictScalars R) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)),
      Function.Injective alpha ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)),
      Function.Bijective
          (LocalizedModule.map (Algebra.closedFiberIdeal R S).primeCompl alpha) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha)),
      Function.Injective (LocalizedModule.map q.primeCompl alpha) ∧
        Module.Flat R (LocalizedModule q.primeCompl (N ⧸ LinearMap.range alpha))] := by
  have : Module.Projective R S :=
    Algebra.projective_of_geometricallyIntegral_fibres
      (Algebra.isGeometricallyIntegral_tensorProduct_residueField R S)
  exact flat_localizedModule_tfae_of_projective' R S q hq N r alpha halpha

/-- **Stacks Project, Tag 05I3, the implication (1) ⟹ (3).** If `N_q` is flat over `R` then the
finite free map `alpha` is injective.

This is the consequence of the induction step that Stacks 05I4 consumes, in the universes it
consumes it in: the base ring and the algebra share a universe and the module is free. -/
public theorem injective_of_flat_localizedModule_of_projective
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Flat R S] [Module.Projective R S]
    [(Algebra.closedFiberIdeal R S).IsPrime]
    (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (r : ℕ) (alpha : (Fin r → S) →ₗ[S] N)
    (halpha : Function.Bijective (alpha.rTensor (Algebra.closedFiberIdeal R S).ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Function.Injective alpha := by
  have h := (flat_localizedModule_tfae_of_projective' R S q hq N r alpha halpha).out 1 3
  exact (h.mp hflat).1

/-- **Stacks Project, Tag 05I3, the implication (1) ⟹ (3)**, for a map out of a finite free
module presented as `Fin r →₀ S` and a fibre hypothesis stated by `LinearMap.baseChange`.

This is the exact shape in which a complete dévissage records its maps `alpha i` and their
fibrewise bijectivity (`Module.CompleteDevissage.alpha` and
`Module.CompleteDevissage.fiber_bijective`), so this is the form that discharges the `hinj`
hypothesis of `Module.CompleteDevissage.nonempty_linearEquiv_directSum` and
`Module.CompleteDevissage.finitePresentation_of_injective_alpha`. -/
public theorem injective_of_flat_localizedModule_of_projective_finsupp
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Flat R S] [Module.Projective R S]
    [(Algebra.closedFiberIdeal R S).IsPrime]
    (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (r : ℕ) (alpha : (Fin r →₀ S) →ₗ[S] N)
    (halpha : Function.Bijective
      (alpha.baseChange (Algebra.closedFiberIdeal R S).ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Function.Injective alpha := by
  classical
  set e : (Fin r →₀ S) ≃ₗ[S] (Fin r → S) := Finsupp.linearEquivFunOnFinite S S (Fin r)
  have hbase : Function.Bijective
      ((alpha ∘ₗ e.symm.toLinearMap).rTensor (Algebra.closedFiberIdeal R S).ResidueField) := by
    rw [← LinearMap.lTensor_bij_iff_rTensor_bij, ← LinearMap.baseChange_eq_ltensor,
      LinearMap.baseChange_comp]
    refine halpha.comp ?_
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.lTensor_bij_iff_rTensor_bij,
      ← LinearEquiv.coe_rTensor _ e.symm]
    exact (e.symm.rTensor _).bijective
  have := injective_of_flat_localizedModule_of_projective R S q hq N r
    (alpha ∘ₗ e.symm.toLinearMap) hbase hflat
  intro a b hab
  apply e.injective
  apply this
  simpa using hab

end Module

end
