module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.Flat.MittagLeffler
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.UniversallyExact
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs
public import StacksFrontier.RingTheory.Module.Localization.UniversalInjectivity

/-!
# The induction step for flat finite modules over a dévissage stage

Let `(R, 𝔪)` be a local ring and let `R → S` be a finitely presented flat ring map with
geometrically integral fibres. Write `𝔭 = 𝔪S` for the generic point of the closed fibre, let
`𝔮 ⊆ S` be a prime over `𝔪` and let `N` be a finite `S`-module. Stacks 05I3 produces a map
`α : S^(⊕ r) → N` that becomes an isomorphism over `κ(𝔭)` and shows that for any such `α` the
flatness of `N_𝔮` over `R` is equivalent to four conditions expressed in terms of `α` and its
cokernel. This is the induction step feeding the dévissage decomposition of Stacks 05I4.

## Main definitions

* `Algebra.closedFiberIdeal R S` is the extension `𝔪S` of the maximal ideal of a local base.
* `Module.freeMapAtResidueField` constructs the map from a finite free module together with
  the proof that its scalar extension to a residue field is bijective.

## Main results

* `Algebra.closedFiberIdeal_isPrime`: the generic ideal of the closed fibre is prime, for an
  algebra whose fibres are geometrically integral.
* `Module.injective_of_universallyInjective`: a universally injective linear map is injective.
* `Module.mul_injective_of_notMem_closedFiber`, `Module.mem_smul_top_of_tmul_zero`,
  `Module.mapQ_injective_of_residue_injective` and
  `Module.localized_surjective_of_residue_surjective`: the four steps of the argument, stated for
  a module in a universe independent of that of `R` and `S` wherever that is possible. The
  universe-general form of the induction step
  (`Module.flat_localizedModule_tfae_of_projective'`) and the spreading out of Stacks 05IA reuse
  them verbatim.
* `Module.flat_localizedModule_tfae_of_projective`: the five equivalent conditions of
  Stacks 05I3, with projectivity of `S` as an `R`-module taken as a hypothesis.
* `Algebra.isGeometricallyIntegral_tensorProduct_residueField`: the fibrewise geometric
  integrality of a ring map, extracted from geometric integrality of `Spec.map` of it. This is
  exactly the hypothesis of Stacks 05FT, which is what discharges the projectivity hypothesis
  of `Module.flat_localizedModule_tfae_of_projective`.

## Implementation notes

The residue-field map is written canonically as scalar extension by `LinearMap.rTensor`; its
source is canonically the finite power of the residue field occurring in the source.
Localization of a module is represented by `LocalizedModule`, and an isomorphism of localized
modules by bijectivity of the canonical localized linear map. The cokernel is the quotient by
the range.

Stacks 05I3 derives projectivity of `S` over `R` from Stacks 05FT, a flat finitely presented
algebra with geometrically integral fibres being projective over its base. That lemma is a deep
input and is not available here, so `Module.flat_localizedModule_tfae_of_projective` takes
`Module.Projective R S` as a hypothesis instead of deriving it. With projectivity assumed,
neither finite presentation of `S` over `R` nor geometric integrality of the fibres is used any
more, so those two hypotheses of the source are dropped there and reappear only in the
derivation.
`Algebra.isGeometricallyIntegral_tensorProduct_residueField` supplies the remaining half of the
derivation, namely the translation between the scheme-level geometric integrality of
`Spec S ⟶ Spec R` and the fibrewise algebraic condition in which Stacks 05FT is stated, so that
once Stacks 05FT is available the source's statement follows by combining the two.

## References

* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u v w

/-- The ideal `𝔪S` defining the closed fibre of an algebra over a local ring. -/
public abbrev Algebra.closedFiberIdeal (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [Algebra R S] : Ideal S :=
  (IsLocalRing.maximalIdeal R).map (algebraMap R S)

/-- **Stacks Project, Tag 05I3, the generic point of the closed fibre.** If the fibres of
`Spec S ⟶ Spec R` are geometrically integral, the ideal extending the maximal ideal of the
local ring `R` is prime. -/
@[stacks 05I3 "the generic point of the closed fibre"]
public theorem Algebra.closedFiberIdeal_isPrime
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    (Algebra.closedFiberIdeal R S).IsPrime := by
  have h := (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mp
    (GeometricallyIntegral.geometrically_isIntegral (f :=
      Spec.map (CommRingCat.ofHom (algebraMap R S))))) (IsLocalRing.ResidueField R)
  have hI := CategoryTheory.ObjectProperty.prop_of_iso _
    (pullbackSpecIso R S (IsLocalRing.ResidueField R)) h
  have hD := (affine_isIntegral_iff
    (.of (TensorProduct R S (IsLocalRing.ResidueField R)))).mp hI
  have : IsDomain (S ⊗[R] (R ⧸ IsLocalRing.maximalIdeal R)) := hD
  exact (Ideal.Quotient.isDomain_iff_prime _).mp
    (MulEquiv.isDomain _ (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (IsLocalRing.maximalIdeal R)).toMulEquiv)

/-- **Stacks Project, Tag 05I3, construction of the free map.** For a finite module and a prime
ideal `p`, some map from a finite free module becomes an isomorphism after tensoring with the
residue field at `p`. -/
@[stacks 05I3 "construction of the free map"]
public noncomputable def Module.freeMapAtResidueField
    (S : Type u) [CommRing S] (p : Ideal S) [p.IsPrime]
    (N : Type v) [AddCommGroup N] [Module S N] [Module.Finite S N] :
    Σ r : ℕ, { alpha : (Fin r → S) →ₗ[S] N //
      Function.Bijective (alpha.rTensor p.ResidueField) } := by
  classical
  apply Classical.choice
  have hspan : Submodule.span p.ResidueField
      (Set.range (fun n : N => (1 : p.ResidueField) ⊗ₜ[S] n)) = ⊤ := by
    change Submodule.span p.ResidueField
      (Set.range ((TensorProduct.mk S p.ResidueField N) 1)) = ⊤
    simpa using (Submodule.baseChange_span p.ResidueField (Set.univ : Set N)).symm
  obtain ⟨ι, a, -, hsp, hli⟩ :=
    exists_linearIndependent' p.ResidueField (fun n : N => (1 : p.ResidueField) ⊗ₜ[S] n)
  rw [hspan] at hsp
  let b : Basis ι p.ResidueField (p.ResidueField ⊗[S] N) := Basis.mk hli (by rw [hsp])
  have : Finite ι := Module.Finite.finite_basis b
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let b' := b.reindex e
  let f : (Fin (Fintype.card ι) → S) →ₗ[S] N := (Pi.basisFun S _).constr S (a ∘ e.symm)
  refine ⟨⟨_, f, ?_⟩⟩
  have hf : f.baseChange p.ResidueField = b'.equivFun.symm.toLinearMap ∘ₗ
      (TensorProduct.piScalarRight S p.ResidueField p.ResidueField _).toLinearMap := by
    refine (Pi.basisFun S _ |>.baseChange p.ResidueField).ext fun i => ?_
    simp [f, b', b, Basis.coe_reindex, e, Function.comp_def]
  apply (LinearMap.lTensor_bij_iff_rTensor_bij p.ResidueField f).mp
  change Function.Bijective (f.baseChange p.ResidueField)
  rw [hf]
  exact b'.equivFun.symm.bijective.comp
    (TensorProduct.piScalarRight S p.ResidueField p.ResidueField _).bijective

namespace Module

/-- A universally injective linear map is injective: take the lift of `R` to the universe of the
modules in the defining condition and transport along `M ⊗[R] R ≃ M`. -/
lemma injective_of_universallyInjective {R : Type u} {M N : Type (max u v)} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : UniversallyInjective f) : Function.Injective f := by
  intro x y h
  apply ((TensorProduct.rid R M).symm.trans
    (TensorProduct.congr (LinearEquiv.refl R M) (ULift.moduleEquiv (R := R)).symm)).injective
  apply hf (ULift.{max u v, u} R)
  simp [h]

/-- Multiplication by an element outside the generic point of the closed fibre is injective on a
flat projective algebra over a local ring.

The hypotheses are those of Stacks 05FR as it is used in the proof of Stacks 05I3: the generic
point `p` of the closed fibre is prime, so an element outside it cannot divide zero against the
closed fibre, and the flatness criterion over a local ring turns that into injectivity.

This is the one step of the argument that genuinely uses the locality of `R`, and the spreading
out of Stacks 05IA reaches it by localizing its base at `𝔯`. -/
public theorem mul_injective_of_notMem_closedFiber
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Projective R S] [Module.Flat R S]
    (p : Ideal S) [p.IsPrime]
    (hp : p = Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
    (s : S) (hs : s ∉ p) : Function.Injective (fun x : S => s * x) := by
  let f := (LinearMap.lsmul S S s).restrictScalars R
  apply injective_of_universallyInjective f
  apply Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal
  have hsub : IsLocalRing.maximalIdeal R • (⊤ : Submodule R S) = p.restrictScalars R := by
    simp [hp]
  rw [Stacks.UniversalInjectivity.FGIdealTest.injective_mapQ_iff]
  intro x hx
  rw [Submodule.mem_comap, hsub] at hx
  rw [hsub]
  exact (Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hx).resolve_left hs

/-- An element of a finite free module killed by the residue field at a prime has all its
coordinates in that prime.

Neither `R` nor the locality of `R` enters, which is why the spreading out of Stacks 05IA reuses
this step over a general base. -/
public theorem mem_smul_top_of_tmul_zero (S : Type u) [CommRing S]
    (p : Ideal S) [p.IsPrime] (r : ℕ) (x : Fin r → S)
    (hx : (1 : p.ResidueField) ⊗ₜ[S] x = 0) :
    x ∈ p • (⊤ : Submodule S (Fin r → S)) := by
  classical
  have hi (i : Fin r) : x i ∈ p := by
    simpa [Algebra.smul_def] using congrArg (fun z => TensorProduct.piScalarRight S
      p.ResidueField p.ResidueField (Fin r) z i) hx
  rw [← (Pi.basisFun S (Fin r)).sum_repr x]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (by simpa using hi i)
    Submodule.mem_top

/-- The reduction modulo `𝔪` of the composition of a finite free map with the localization map at
a prime `q` above `𝔪` is injective, as soon as the map becomes injective over the residue field
of the generic point of the closed fibre.

This is the hypothesis of Stacks 05FQ in the induction step of Stacks 05I3. The module `N` lives
in a universe independent of that of `R` and `S`. -/
public theorem mapQ_injective_of_residue_injective
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    (p q : Ideal S) [p.IsPrime] [q.IsPrime]
    (hp : p = Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) (hpq : p ≤ q)
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (r : ℕ) (f : (Fin r → S) →ₗ[S] N) (hf : Function.Injective (f.rTensor p.ResidueField)) :
    let g := ((LocalizedModule.mkLinearMap q.primeCompl N).comp f).restrictScalars R
    Function.Injective (Submodule.mapQ (IsLocalRing.maximalIdeal R • ⊤)
      (IsLocalRing.maximalIdeal R • ⊤) g
      (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R) g)) := by
  classical
  let K := p.ResidueField
  have hu (s : q.primeCompl) : IsUnit (algebraMap S (Module.End S (K ⊗[S] N)) s) := by
    have hs : IsUnit (algebraMap S K s) := by
      apply isUnit_iff_ne_zero.mpr
      simpa [K] using fun h => s.2 (hpq h)
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun z : K ⊗[S] N => (s : S) • z)
    have he : (fun z : K ⊗[S] N => (s : S) • z) =
        (fun z : K ⊗[S] N => algebraMap S K s • z) := by
      funext z
      exact (IsScalarTower.algebraMap_smul K (s : S) z).symm
    rw [he]
    exact hs.smul_bijective
  let t : LocalizedModule q.primeCompl N →ₗ[S] K ⊗[S] N :=
    LocalizedModule.lift q.primeCompl (TensorProduct.mk S K N 1) hu
  have ht (y : LocalizedModule q.primeCompl N)
      (hy : y ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R _)) : t y = 0 := by
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha y _
      rw [← IsScalarTower.algebraMap_smul S a y, map_smul, ← IsScalarTower.algebraMap_smul K,
        show algebraMap S K (algebraMap R S a) = 0 from
          Ideal.algebraMap_residueField_eq_zero.mpr (hp ▸ Ideal.mem_map_of_mem _ ha), zero_smul]
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  dsimp only
  rw [Stacks.UniversalInjectivity.FGIdealTest.injective_mapQ_iff]
  intro x hx
  have hz : (1 : K) ⊗ₜ[S] f x = 0 := (LinearMap.congr_fun
    (LocalizedModule.lift_comp q.primeCompl (TensorProduct.mk S K N 1) hu) (f x)).symm.trans
      (ht _ hx)
  have hxx : (1 : K) ⊗ₜ[S] x = 0 := by
    apply (LinearMap.lTensor_inj_iff_rTensor_inj K f).mpr hf
    simpa using hz
  have hm : x ∈ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
      (⊤ : Submodule S (Fin r → S))).restrictScalars R := by
    rw [← hp]
    exact mem_smul_top_of_tmul_zero S p r x hxx
  simpa only [Ideal.smul_restrictScalars, Submodule.restrictScalars_top] using hm

/-- A map into a finite module which becomes surjective over the residue field at a prime is
surjective after localizing at that prime.

Neither `R` nor the locality of `R` enters, which is why the spreading out of Stacks 05IA reuses
this step over a general base. -/
public theorem localized_surjective_of_residue_surjective
    (S : Type u) [CommRing S] (p : Ideal S) [p.IsPrime]
    (M : Type v) [AddCommGroup M] [Module S M]
    (N : Type w) [AddCommGroup N] [Module S N] [Module.Finite S N]
    (f : M →ₗ[S] N) (hf : Function.Surjective (f.rTensor p.ResidueField)) :
    Function.Surjective (LocalizedModule.map p.primeCompl f) := by
  let C := N ⧸ LinearMap.range f
  let g := (LinearMap.range f).mkQ
  have ht : Function.Surjective (f.lTensor p.ResidueField) :=
    (LinearMap.lTensor_surj_iff_rTensor_surj p.ResidueField f).mpr hf
  have hg : g.lTensor p.ResidueField = 0 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := ht x
    have hgf : g.comp f = 0 := by ext; simp [g]
    simp [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hgf]
  have hC : Subsingleton (p.ResidueField ⊗[S] C) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := g.lTensor_surjective p.ResidueField (Submodule.mkQ_surjective _) x
    obtain ⟨y, rfl⟩ := g.lTensor_surjective p.ResidueField (Submodule.mkQ_surjective _) y
    simp [hg]
  have hCp : Subsingleton (LocalizedModule p.primeCompl C) := by
    apply not_nontrivial_iff_subsingleton.mp
    rw [← Module.mem_support_iff (p := ⟨p, inferInstance⟩),
      Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hC
  exact fun x => (LocalizedModule.map_exact p.primeCompl f g f.exact_map_mkQ_range x).mp
    (Subsingleton.elim _ _)

/-- **Stacks Project, Tag 05I3, the five equivalent conditions**, with projectivity of `S` over
`R` as a hypothesis rather than a consequence of Stacks 05FT.

Fix a finite free map whose scalar extension to the residue field of the generic point `p` of the
closed fibre is an isomorphism. For a prime `q` over the maximal ideal, the following are
equivalent: `N_q` is flat over `R`; the map is universally injective over `R` and its localized
cokernel is flat; the map is injective and that cokernel is flat; its localization at `p` is an
isomorphism and that cokernel is flat; and its localization at `q` is injective and that cokernel
is flat. -/
public theorem flat_localizedModule_tfae_of_projective
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Flat R S] [Module.Projective R S]
    [(Algebra.closedFiberIdeal R S).IsPrime]
    (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (r : ℕ) (alpha : (Fin r → S) →ₗ[S] N)
    (halpha : Function.Bijective (alpha.rTensor (Algebra.closedFiberIdeal R S).ResidueField)) :
    List.TFAE [
      Module.Flat R (LocalizedModule q.primeCompl N),
      UniversallyInjective (alpha.restrictScalars R) ∧
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
  have hpq : p ≤ q := Ideal.map_le_iff_le_comap.mpr hq.ge
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
    have hcomp := Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal
      (((LocalizedModule.mkLinearMap q.primeCompl N).comp alpha).restrictScalars R)
      (mapQ_injective_of_residue_injective R S p q rfl hpq N r alpha halpha.1)
    have hu : UniversallyInjective (alpha.restrictScalars R) := by
      intro Q _ _
      have hh := hcomp Q
      rw [LinearMap.restrictScalars_comp, LinearMap.rTensor_comp] at hh
      change Function.Injective
        (((LocalizedModule.mkLinearMap q.primeCompl N).restrictScalars R).rTensor Q ∘
          (alpha.restrictScalars R).rTensor Q) at hh
      exact hh.of_comp
    have huq : UniversallyInjective fq := by
      intro Q _ _
      exact IsLocalizedModule.rTensor_injective_of_rTensor_injective q.primeCompl
        (LocalizedModule.mkLinearMap q.primeCompl (Fin r → S))
        (LocalizedModule.mkLinearMap q.primeCompl N) alpha
        (LocalizedModule.map q.primeCompl alpha)
        (IsLocalizedModule.map_comp _ _ _ _) Q (hu Q)
    exact ⟨hu, (UniversallyExact.flat_of_middle_flat fq gq
      ⟨injective_of_universallyInjective fq huq, hsurj, hex, huq⟩ hN).2⟩
  tfae_have 2 → 3 := fun ⟨hu, hC⟩ =>
    ⟨injective_of_universallyInjective (alpha.restrictScalars R) hu, hC⟩
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
  tfae_have 5 → 1 := fun ⟨hi, hC⟩ => flat_of_flat_of_flat fq gq hi hex hsurj
  tfae_finish

end Module

/-- The fibrewise form of geometric integrality: if `Spec S ⟶ Spec R` is geometrically integral
then for every prime `p` of `R` the fibre `S ⊗[R] κ(p)` is a geometrically integral
`κ(p)`-algebra.

This is exactly the hypothesis of Stacks 05FT, so combining it with that lemma discharges the
`Module.Projective R S` hypothesis of
`Module.flat_localizedModule_tfae_of_projective`. -/
public theorem Algebra.isGeometricallyIntegral_tensorProduct_residueField
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (p : Ideal R) [p.IsPrime] :
    letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
      Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField) := by
  have hiso : MorphismProperty.RespectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  change GeometricallyIntegral (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : p.ResidueField →ₐ[R]
      S ⊗[R] p.ResidueField).toRingHom))
  have h : GeometricallyIntegral ((pullbackSpecIso R S p.ResidueField).inv ≫
      CategoryTheory.Limits.pullback.snd _ _) := by
    rw [MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)]
    infer_instance
  convert! h using 1
  exact (pullbackSpecIso_inv_snd R S p.ResidueField).symm

end
