module

public import StacksFrontier.AlgebraicGeometry.Algebraization.StalkOfIdealOnOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AlgebraizationFreeStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.ComplementTildeFreeStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.CompletionShrinkFreeLocus
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.CompletionFiniteFreeStalks
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenStalkNonzerodivisor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalShortExactStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.SpecialFibreFiniteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.SpecialFibreLocallyFreeFiniteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FiniteLocallyFreeAdic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentComplementAffine
public import StacksFrontier.RingTheory.LocalCohomology.ComplementTildeTorsionQuotient
public import StacksFrontier.RingTheory.LocalCohomology.DepthExtension.DegreeZero
public import StacksFrontier.RingTheory.LocalCohomology.QuotientLocallyFreeFiniteness
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotientModule
public import StacksFrontier.RingTheory.Module.LocallyFree.PointwiseFreeAway

/-!
# The completion functor at a principal formal locus, on finite locally free objects

Fix the standing situation of [Stacks, Tag 0EHC]: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the
affine scheme `X = Spec(A)`, its closed subschemes `Y = V(I)` and `Z = V(𝔞)`, and the open
complement `U = X ∖ Z`. Assume moreover

1. `I = (f)` is a principal ideal,
2. `A` is complete with respect to the `f`-adic topology,
3. `f` is a nonzerodivisor of `A`, and
4. `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` are finite `A`-modules.

Writing `U₀ = U ∩ V(f)`, [Stacks, Tag 0EKZ] asserts that the completion functor

  `colim_{U₀ ⊆ U' ⊆ U} Coh(𝒪_{U'}) ⟶ Coh(U, f𝒪_U)`

restricts to an equivalence on the full subcategories of finite locally free objects. Its proof is
two citations: full faithfulness is [Stacks, Tag 0EKV] and essential surjectivity is
[Stacks, Tag 0DXW].

This file assembles both halves at the source's own hypotheses (1)–(4).

## Main definitions

* `Stacks.Algebraization.HasFiniteFreeStalks` — hypothesis (2) of [Stacks, Tag 0DXW] read at the
  stalks: every term `F_{n+1}` of the system is finite free over the local ring of `U` modulo the
  `(n+1)`-st power of the stalk of `I 𝒪_U`. This is what a finite locally free
  `𝒪_U/I^{n+1}𝒪_U`-module is at a point.
* `Stacks.Algebraization.IsCompletionNearClosedFiniteLocallyFree` — membership in the essential
  image of the completion functor on finite locally free objects: the system is the completion of
  a finite locally free coherent module on an open neighbourhood of `U ∩ V(I)` in `U`.

## Main results

* `Stacks.Algebraization.finite_specialFibreLocalCohomology_iff_quot` — the two spellings of
  `H^i_𝔞(A/fA)` used by the two halves agree.
* `Stacks.Algebraization.germOfBase_mem_maximalIdeal_of_formalLocus` — at a point of `U ∩ V(f)`
  the germ of `f` is not a unit.
* `Stacks.Algebraization.finite_openCohomology_of_hasFiniteFreeStalks` — the finiteness step of
  the proof of [Stacks, Tag 0DXW]: `H⁰(U, F₁)` and `H¹(U, F₁)` are finite `A`-modules.
* `Stacks.Algebraization.canonicallyExtends_and_isCompletion_of_principal` —
  **[Stacks, Tag 0DXW]**.
* `Stacks.Algebraization.completionFullyFaithful_principal` — full faithfulness in the standing
  situation for a pair of modules defined on `U` itself, in the vocabulary of the completion
  functor; [Stacks, Tag 0EKV] itself is
  `Stacks.Algebraization.completionFullyFaithfulComplete_principal`, the statement for an object
  defined on an arbitrary member of `𝒱`.
* `Stacks.Algebraization.isCompletionNearClosedFiniteLocallyFree_of_principal` — the
  essential-surjectivity half of [Stacks, Tag 0EKZ], with a finite locally free witness.
* `Stacks.Algebraization.completionEquivalence_principal_finiteLocallyFree` —
  **[Stacks, Tag 0EKZ]**.

## References

* [Stacks Project, Tag 0EKZ](https://stacks.math.columbia.edu/tag/0EKZ)
* [Stacks Project, Tag 0EKV](https://stacks.math.columbia.edu/tag/0EKV)
* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry Pointwise
open Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-! ### Finite local freeness over the infinitesimal neighbourhoods -/

/-- **Hypothesis (2) of [Stacks, Tag 0DXW], at the stalks.** Every term `F_{n+1}` of a coherent
`I`-adic system on `U` is finite free over `𝒪_{U,y} / (I 𝒪_U)_y^{n+1}` at every point `y` of
`U`.

A finite locally free `𝒪_U/I^{n+1}𝒪_U`-module has exactly this at every point, and it is all that
the proofs below use, so it is the form the hypothesis takes. -/
abbrev HasFiniteFreeStalks
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) : Prop :=
  ∀ (m : ℕ) (y : S.U.toScheme), ∃ r : ℕ,
    Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj (systemObj S F m)
      ≃ₗ[S.U.toScheme.presheaf.stalk y]
      (Fin r → (S.U.toScheme.presheaf.stalk y ⧸
        AlgebraicGeometry.IdealSheafData.stalk (idealOnOpen S) y ^ (m + 1))))

/-- **Membership in the essential image of the completion functor of [Stacks, Tag 0EKZ] on
finite locally free objects.** The system is the completion of a *finite locally free* coherent
module on some open neighbourhood of `U ∩ V(I)` inside `U`, which is what it means for an object
of `Coh(U, I𝒪_U)` to lie in the image of the full subcategory of finite locally free objects of
`colim_{U₀ ⊆ U' ⊆ U} Coh(𝒪_{U'})`.

This is condition (3) of [Stacks, Tag 0EIL], namely
`Stacks.Algebraization.IsCompletionNearClosed`, with finite local freeness of the module added
and with the ideal sheaf spelled `Stacks.Algebraization.idealOnOpen`. -/
def IsCompletionNearClosedFiniteLocallyFree
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) : Prop :=
  ∃ V : S.U.toScheme.Opens,
    (S.U.ι.base ⁻¹' Set.range S.Yι.base) ⊆ (V : Set S.U.toScheme) ∧
      ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf,
        AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj ∧
        Nonempty (((completionFunctor V.toScheme ((idealOnOpen S).comap V.ι)).obj G).obj ≅
          (F.obj ⋙ AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι))

/-! ### The two spellings of the local cohomology of the special fibre -/

/-- **The two spellings of `H^i_𝔞(A/fA)` agree.** The essential-surjectivity half meets it as
`Stacks.Algebraization.specialFibreLocalCohomology`, the local cohomology with support in `V(𝔞)`
of `A/fA` in the supported-sections model; the full-faithfulness half meets it as the local
cohomology of `Stacks.Algebraization.FormalSections.Quot f A 1` in the coreflection model. The
two modules `A/fA` differ only in the spelling of the submodule `fA`, and the two models of local
cohomology agree over a Noetherian ring. -/
theorem finite_specialFibreLocalCohomology_iff_quot (f : S.A) (i : ℤ) :
    Module.Finite S.A (specialFibreLocalCohomology S f i) ↔
      Module.Finite S.A (Stacks.LocalCohomology.localCohomologyModule S.A S.a
        (Ideal.fg_of_isNoetherianRing S.a)
        (Stacks.Algebraization.FormalSections.Quot f (ModuleCat.of S.A S.A) 1) i) := by
  have hsub : Stacks.Algebraization.FormalSections.powSmul f (ModuleCat.of S.A S.A) 1 =
      (Ideal.span {f} : Ideal S.A) := by
    refine Submodule.ext fun x => ?_
    rw [Stacks.Algebraization.FormalSections.mem_powSmul, Ideal.mem_span_singleton', pow_one]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rwa [mul_comm]⟩, fun ⟨y, hy⟩ => ⟨y, by rwa [mul_comm] at hy⟩⟩
  refine (Module.finite_iff_of_moduleCat_iso
    ((Stacks.LocalCohomology.localCohomologyWithSupportInFunctor.{u, u} S.A
        (PrimeSpectrum.zeroLocus (S.a : Set S.A)) i).mapIso
      (Submodule.quotEquivOfEq (Ideal.span {f})
          (Stacks.Algebraization.FormalSections.powSmul f (ModuleCat.of S.A S.A) 1)
          hsub.symm).toModuleIso)).trans ?_
  exact Module.finite_iff_of_moduleCat_iso
    (Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule S.A S.a
      (Ideal.fg_of_isNoetherianRing S.a)
      (Stacks.Algebraization.FormalSections.Quot f (ModuleCat.of S.A S.A) 1) i)

/-! ### The formal locus -/

/-- **At a point of `U ∩ V(f)` the germ of `f` lies in the maximal ideal.** The stalk of `I 𝒪_U`
at a point of the formal locus is contained in the maximal ideal of the local ring, and for
`I = (f)` that stalk is generated by the germ of `f`. -/
theorem germOfBase_mem_maximalIdeal_of_formalLocus {f : S.A} (hI : S.I = Ideal.span {f})
    (y : S.U.toScheme) (hy : S.U.ι.base y ∈ Set.range S.Yι.base) :
    germOfBase S y f ∈ IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk y) := by
  obtain ⟨z, hz⟩ := hy
  refine stalk_idealOnOpen_le_maximalIdeal S y z hz.symm ?_
  rw [stalk_idealOnOpen_eq_span_germOfBase S hI y]
  exact Ideal.mem_span_singleton_self _

/-! ### Full faithfulness -/

/-- **Full faithfulness in the standing situation, for a pair of modules defined on `U` itself.**
Under hypotheses (1), (2) and the first half of (4): for finite locally free coherent modules
`𝒢`, `ℱ` on `U` the canonical map from `colim_{U₀ ⊆ U' ⊆ U} Hom_{U'}(𝒢|_{U'}, ℱ|_{U'})` to
`Hom_{Coh(U, f𝒪_U)}(𝒢^∧, ℱ^∧)` is bijective.

This is not [Stacks, Tag 0EKV] and carries no part of it. The tag is
`Stacks.Algebraization.completionFullyFaithfulComplete_principal`, the statement for an object
of `colim_𝒱 Coh(𝒪_V)` defined on an arbitrary member of `𝒱`, and it is what the second conjunct
of [Stacks, Tag 0EKZ] below is stated with; written out here is its conclusion for the single
pair of modules on `U`, read through `Stacks.Algebraization.completionFunctor`, whose hom-set is
the target. -/
theorem completionFullyFaithful_principal {f : S.A} (hI : S.I = Ideal.span {f})
    [IsAdicComplete (Ideal.span {f}) S.A] (hnzd : f ∈ nonZeroDivisors S.A)
    (hH1 : Module.Finite S.A (specialFibreLocalCohomology S f 1)) :
    ∀ G F : AlgebraicGeometry.SheafOfModules.CoherentModules
        (complementZeroLocus S.A S.a : Scheme).ringCatSheaf,
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj →
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree F.obj →
        Function.Bijective
          (NeighbourhoodHoms.nbhdHomComparison S.A (Ideal.span {f}) S.a G F) :=
  have hfI : f ∈ S.I := hI ▸ Ideal.mem_span_singleton_self f
  completionFullyFaithful_principal_finiteLocallyFree (S.I_le_a hfI) hnzd
    ((finite_specialFibreLocalCohomology_iff_quot S f 1).mp hH1)

/-! ### Finiteness of the low-degree cohomology of the special fibre -/

/-- **The finiteness step of the proof of [Stacks, Tag 0DXW], from the source's hypotheses.**
Let `(F_n)` be a coherent `I`-adic system on `U` with `I = (f)` principal and with finite free
stalks over the infinitesimal neighbourhoods. If `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` are finite
`A`-modules then so are `H⁰(U, F₁)` and `H¹(U, F₁)`.

The source deduces this from Local Cohomology [Stacks, Tag 0BK0] and [Stacks, Tag 0BLT]. Here it
runs as follows. By clause (1) of [Stacks, Tag 0BK0] the term `F₁` is the restriction to `U` of
the sheaf associated with a finite `A`-module, and since `I F₁ = 0` that module may be taken
killed by `f`, hence to be a finite module `N` over `A/fA`. Finite local freeness at the stalks
makes every localization of `N` away from a member of `𝔞` a finite locally free module over the
corresponding localization of `A/fA`, so [Stacks, Tag 0BPY] over `A/fA` — transported across the
quotient by [Stacks, Tag 0BJB] — turns the finiteness of `H^i_𝔞(A/fA)` for `i ≤ 2` into the
finiteness of `H^i_𝔞(N)` for `i ≤ 2`. Clause (3) of [Stacks, Tag 0BK0] reads that back as the
finiteness of `H^p(U, F₁)` for `p ≤ 1`. -/
theorem finite_openCohomology_of_hasFiniteFreeStalks
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) {f : S.A}
    (hI : S.I = Ideal.span {f})
    (hH1 : Module.Finite S.A (specialFibreLocalCohomology S f 1))
    (hH2 : Module.Finite S.A (specialFibreLocalCohomology S f 2))
    (hfree : HasFiniteFreeStalks S F)
    (p : ℕ) (hp : p ≤ 1) :
    Module.Finite S.A ((openCohomologyFunctor S p).obj (systemObj S F 0)) := by
  classical
  have hfI : f ∈ S.I := by rw [hI]; exact Ideal.mem_span_singleton_self f
  have hcoh : _root_.SheafOfModules.IsCoherent
      (R := (Stacks.LocalCohomology.complementZeroLocus S.A S.a : Scheme).ringCatSheaf)
      (systemObj S F 0) := F.property.1 0
  -- a finite model of `F₁`, by clause (1) of Stacks 0BK0
  obtain ⟨M, hM, ⟨e1'⟩⟩ := (Stacks.LocalCohomology.coherent_complement_affine S.A S.a
    (Ideal.fg_of_isNoetherianRing S.a) (systemObj S F 0)).1
  have := hM
  have e1 : systemObj S F 0 ≅
      (Stacks.LocalCohomology.complementTilde S.A S.a M : S.U.toScheme.Modules) := e1'
  -- multiplication by `f` is zero on the model
  have hzero : Stacks.Coherent.mulSection
        (Stacks.LocalCohomology.complementTopSectionsRingHom S.a f)
        (Stacks.LocalCohomology.complementTilde S.A S.a M) =
      (0 : Stacks.LocalCohomology.complementTilde S.A S.a M ⟶
        Stacks.LocalCohomology.complementTilde S.A S.a M) := by
    set CTM : S.U.toScheme.Modules :=
      (Stacks.LocalCohomology.complementTilde S.A S.a M : S.U.toScheme.Modules) with hCTM
    have h0 : Stacks.Coherent.mulSection (scalarMap S f) (systemObj S F 0) = 0 :=
      Stacks.Coherent.mulSection_eq_zero (idealOnOpen S) (scalarMap S f)
        (restrictTop_scalarMap_mem_idealOnOpen S hfI) (systemObj S F 0) (F.property.2.1 0)
    have hnat := Stacks.Coherent.mulSection_naturality (X := S.U.toScheme) (scalarMap S f) e1.hom
    have key : e1.hom ≫ Stacks.Coherent.mulSection (X := S.U.toScheme) (scalarMap S f) CTM = 0 := by
      rw [← hnat, h0, Limits.zero_comp]
    have h2 := congrArg (fun k => e1.inv ≫ k) key
    simp only [← Category.assoc, e1.inv_hom_id, Category.id_comp, Limits.comp_zero] at h2
    exact h2
  -- so the model may be taken killed by `f`
  obtain ⟨e2'⟩ :=
    Stacks.LocalCohomology.nonempty_iso_complementTilde_quotient_smul_of_mulSection_eq_zero
      S.a f M hzero
  set N₀ : Type u := (M : Type u) ⧸ (f • (⊤ : Submodule S.A (M : Type u))) with hN₀
  have hfinN : Module.Finite S.A N₀ := Module.Finite.quotient S.A _
  have hkill : ∀ x : N₀, f • x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    exact Submodule.smul_mem_pointwise_smul z f ⊤ Submodule.mem_top
  have htor : Module.IsTorsionBySet S.A N₀ (Ideal.span {f} : Ideal S.A) := by
    intro x a
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp a.2
    have h : (a : S.A) • x = c • (f • x) := by rw [smul_smul, ← hc]
    rw [h, hkill, smul_zero]
  let : Module (S.A ⧸ Ideal.span {f}) N₀ := htor.module
  set NQ : ModuleCat.{u} (S.A ⧸ Ideal.span {f}) := ModuleCat.of (S.A ⧸ Ideal.span {f}) N₀ with hNQ
  have e2 : (Stacks.LocalCohomology.complementTilde S.A S.a M : S.U.toScheme.Modules) ≅
      (Stacks.LocalCohomology.complementTilde S.A S.a (ModuleCat.of S.A N₀) :
        S.U.toScheme.Modules) := e2'
  have hiso : ((ModuleCat.restrictScalars
      (Ideal.Quotient.mk (Ideal.span {f}))).obj NQ) ≅ ModuleCat.of S.A N₀ :=
    LinearEquiv.toModuleIso
      { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
        invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hfinNQ : Module.Finite (S.A ⧸ Ideal.span {f}) NQ :=
    (Stacks.LocalCohomology.finite_restrictScalars_quotient_iff (Ideal.span {f}) NQ).mp
      ((Module.finite_iff_of_moduleCat_iso hiso).mpr hfinN)
  -- pointwise freeness of the model
  have hpt : ∀ y : S.U.toScheme, ∃ r : ℕ, Nonempty
      (LocalizedModule (underlyingPrime S y).asIdeal.primeCompl N₀
        ≃ₗ[Localization.AtPrime (underlyingPrime S y).asIdeal]
        (Fin r → (Localization.AtPrime (underlyingPrime S y).asIdeal ⧸
          (Ideal.span {f}).map (algebraMap S.A
            (Localization.AtPrime (underlyingPrime S y).asIdeal))))) := fun y =>
    exists_linearEquiv_localizedModule_of_free_stalk S hI (ModuleCat.of S.A N₀)
      (systemObj S F 0) (e1 ≪≫ e2) y (hfree 0 y)
  -- freeness at the primes of `A ⧸ (f)`
  have hq : ∀ (q : Ideal (S.A ⧸ Ideal.span {f})) (_ : q.IsPrime),
      ¬ S.a.map (Ideal.Quotient.mk (Ideal.span {f})) ≤ q →
      Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl N₀) := by
    intro q hqp hqa
    have := hqp
    have hcomp : ¬ S.a ≤ q.comap (Ideal.Quotient.mk (Ideal.span {f})) := by
      intro hle
      exact hqa (Ideal.map_le_iff_le_comap.mpr hle)
    have hmemU : (⟨q.comap (Ideal.Quotient.mk (Ideal.span {f})), inferInstance⟩ :
        PrimeSpectrum S.A) ∈ S.U := fun hc => hcomp hc
    let y : S.U.toScheme := ⟨⟨q.comap (Ideal.Quotient.mk (Ideal.span {f})), inferInstance⟩, hmemU⟩
    obtain ⟨r, ⟨e⟩⟩ := hpt y
    exact Module.free_localizedModule_atPrime_of_quotient (Ideal.span {f}) NQ q r e
  -- the localizations away from the image of `𝔞` are finite locally free
  have hloc : ∀ g ∈ S.a.map (Ideal.Quotient.mk (Ideal.span {f})),
      Module.IsFiniteLocallyFree (Localization.Away g) (LocalizedModule.Away g N₀) := by
    intro g hg
    exact Module.isFiniteLocallyFree_away_of_free_localizedModule_atPrime N₀ g
      fun q hqp hgq => hq q hqp fun hle => hgq (hle hg)
  -- Stacks 0BPY across the quotient
  have hfinLC : ∀ i : ℕ, i ≤ 2 → Module.Finite S.A
      (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} S.A
        (PrimeSpectrum.zeroLocus (S.a : Set S.A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj NQ)) (i : ℤ)) := by
    refine finite_localCohomologyWithSupportIn_restrictScalars_of_isFiniteLocallyFree
      S.A S.a (Ideal.span {f}) 2 ?_ NQ hloc
    intro i hi
    interval_cases i
    · exact Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_zero.{u, u} _ _
    · exact hH1
    · exact hH2
  -- transport along the model and conclude
  have hmodel : Module.Finite S.A
      (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} S.A
        (PrimeSpectrum.zeroLocus (S.a : Set S.A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj
          (ModuleCat.of S.A N₀)) ((p + 1 : ℕ) : ℤ)) :=
    (Module.finite_iff_of_moduleCat_iso
      ((Stacks.LocalCohomology.localCohomologyWithSupportInFunctor.{u, u} S.A
        (PrimeSpectrum.zeroLocus (S.a : Set S.A)) ((p + 1 : ℕ) : ℤ)).mapIso hiso)).mp
      (hfinLC (p + 1) (by omega))
  exact (finite_openCohomology_iff_finite_localCohomology S F (ModuleCat.of S.A N₀)
    (e1 ≪≫ e2) p).mpr hmodel

/-! ### The short exact sequences -/

/-- The finiteness of `H⁰(U, F₁)` and `H¹(U, F₁)`, with `H⁰` read as the global sections of the
system. -/
private theorem finite_globalSections_and_openCohomology_one
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) {f : S.A}
    (hI : S.I = Ideal.span {f})
    (hH1 : Module.Finite S.A (specialFibreLocalCohomology S f 1))
    (hH2 : Module.Finite S.A (specialFibreLocalCohomology S f 2))
    (hfree : HasFiniteFreeStalks S F) :
    Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)) ∧
      Module.Finite S.A ((openCohomologyFunctor S 1).obj (systemObj S F 0)) :=
  ⟨(finite_globalSections_iff_finite_openCohomology_zero S F).mp
      (finite_openCohomology_of_hasFiniteFreeStalks S F hI hH1 hH2 hfree 0 (by omega)),
    finite_openCohomology_of_hasFiniteFreeStalks S F hI hH1 hH2 hfree 1 le_rfl⟩

/-- **Hypothesis (1) of [Stacks, Tag 0DXW] in use.** When `I = (f)` with `f` a nonzerodivisor of
`A` and the terms of the system have finite free stalks, the sequences
`0 → F_n → F_{n+1} → F_1 → 0` of the source's proof are short exact, which is condition (1) of
[Stacks, Tag 0H39] for multiplication by `f`. The germs of a nonzerodivisor of `A` in the local
rings of `U` are nonzerodivisors, which is the form the hypothesis is used in. -/
theorem hasPrincipalShortExactSequences_of_nonzerodivisor
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) {f : S.A}
    (hI : S.I = Ideal.span {f}) (hnzd : f ∈ nonZeroDivisors S.A)
    (hfree : HasFiniteFreeStalks S F) :
    HasPrincipalShortExactSequences S F f :=
  hasPrincipalShortExactSequences_of_principal S F hI
    (fun y => germOfBase_mem_nonZeroDivisors S hnzd y) hfree

/-! ### Stacks 0DXW -/

/-- **[Stacks, Tag 0DXW].** Let `S` be the standing situation of [Stacks, Tag 0EHC] and let
`(F_n)` be an object of `Coh(U, I𝒪_U)`. Assume

1. `I = (f)` is principal with `f` a nonzerodivisor of `A`,
2. every `F_n` is a finite locally free `𝒪_U/Iⁿ𝒪_U`-module, and
3. `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` are finite `A`-modules.

Then `(F_n)` extends canonically to `X = Spec(A)`; and if moreover `A` is `f`-adically complete,
`(F_n)` is the completion of a coherent `𝒪_U`-module.

Hypothesis (2) is used at the stalks, where a finite locally free `𝒪_U/Iⁿ𝒪_U`-module is a finite
free module over the local ring modulo the `n`-th power of the stalk of `I𝒪_U`; that is
`Stacks.Algebraization.HasFiniteFreeStalks`.

The three conditions (a), (b), (c) of the Mittag-Leffler criterion [Stacks, Tag 0EHH] come from
`Stacks.Algebraization.canonicallyExtends_of_principal_shortExactSequences`, whose two
hypotheses are discharged here: the short exact sequences
`0 → F_n → F_{n+1} → F_1 → 0` by
`Stacks.Algebraization.hasPrincipalShortExactSequences_of_nonzerodivisor`, and the finiteness of
`H⁰(U, F₁)` and `H¹(U, F₁)` by
`Stacks.Algebraization.finite_openCohomology_of_hasFiniteFreeStalks`. The second clause follows
from the first along the chain of [Stacks, Tag 0EIL]. -/
@[stacks 0DXW]
theorem canonicallyExtends_and_isCompletion_of_principal
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) {f : S.A}
    (hI : S.I = Ideal.span {f}) (hnzd : f ∈ nonZeroDivisors S.A)
    (hH1 : Module.Finite S.A (specialFibreLocalCohomology S f 1))
    (hH2 : Module.Finite S.A (specialFibreLocalCohomology S f 2))
    (hfree : HasFiniteFreeStalks S F) :
    CanonicallyExtends S F ∧
      (IsAdicComplete (Ideal.span {f}) S.A →
        (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage
          (kerComapSystem S F)) := by
  have hses := hasPrincipalShortExactSequences_of_nonzerodivisor S F hI hnzd hfree
  obtain ⟨h0, h1⟩ := finite_globalSections_and_openCohomology_one S F hI hH1 hH2 hfree
  exact ⟨canonicallyExtends_of_principal_shortExactSequences S F f hI hses h0 h1,
    fun hcomplete => (isCompletion_iff_nearClosed S (kerComapSystem S F)).mpr
      (isCompletionNearClosed_of_principal_shortExactSequences S F f hI hcomplete hses h0 h1)⟩


/-! ### Stacks 0EKZ -/

/-- **The essential-surjectivity half of [Stacks, Tag 0EKZ], with a finite locally free
witness.** Under hypotheses (1)–(4) of the tag, every object of `Coh(U, f𝒪_U)` whose terms have
finite free stalks is the completion of a *finite locally free* coherent module on an open
neighbourhood of `U ∩ V(f)` inside `U`.

[Stacks, Tag 0DXW] gives a coherent module `𝒢` on such a neighbourhood `V` whose completion is
the system. At a point `y` of `V` lying over `U ∩ V(f)` the germ of `f` is not a unit, the stalk
quotients `𝒢_y / (f ⁿ⁺¹) 𝒢_y` are finite free, and `f` is a nonzerodivisor there, so `𝒢_y` is
free; shrinking `V` to the open locus where `𝒢` is free — which contains `U ∩ V(f)` — leaves the
completion unchanged and makes `𝒢` finite locally free. -/
theorem isCompletionNearClosedFiniteLocallyFree_of_principal
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) {f : S.A}
    (hI : S.I = Ideal.span {f}) (hcomplete : IsAdicComplete (Ideal.span {f}) S.A)
    (hnzd : f ∈ nonZeroDivisors S.A)
    (hH1 : Module.Finite S.A (specialFibreLocalCohomology S f 1))
    (hH2 : Module.Finite S.A (specialFibreLocalCohomology S f 2))
    (hfree : HasFiniteFreeStalks S F) :
    IsCompletionNearClosedFiniteLocallyFree S F := by
  have hses := hasPrincipalShortExactSequences_of_nonzerodivisor S F hI hnzd hfree
  obtain ⟨h0, h1⟩ := finite_globalSections_and_openCohomology_one S F hI hH1 hH2 hfree
  have hES : IsCompletionNearClosed S (⟨F.obj, isCoherentAdicSystem_kerComap S F⟩ :
      Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) :=
    isCompletionNearClosed_of_principal_shortExactSequences S F f hI hcomplete hses h0 h1
  obtain ⟨V, hV, G, ⟨e'⟩⟩ := hES
  have hJ : (idealOnOpen S).comap V.ι = (S.Yι.ker.comap S.U.ι).comap V.ι := by
    rw [idealOnOpen_eq_ker_comap]
  have e : ((completionFunctor V.toScheme ((idealOnOpen S).comap V.ι)).obj G).obj ≅
      F.obj ⋙ AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι :=
    completionFunctorObjCongr hJ G ≪≫ e'
  obtain ⟨V', hV', -, G', hflf, he⟩ :=
    exists_isFiniteLocallyFree_completion_of_free_stalks S F V G e
      (S.U.ι.base ⁻¹' Set.range S.Yι.base) hV
      (fun y hy => free_stalk_of_hasFiniteFreeStalks_completion S hI hnzd F hfree V G e y
        (germOfBase_mem_maximalIdeal_of_formalLocus S hI (V.ι.base y) hy))
  exact ⟨V', hV', G', hflf, he⟩

/-- **[Stacks, Tag 0EKZ].** Let `S` be the standing situation of [Stacks, Tag 0EHC] and write
`U₀ = U ∩ V(f)`. Assume

1. `I = (f)` is a principal ideal,
2. `A` is complete with respect to the `f`-adic topology,
3. `f` is a nonzerodivisor of `A`, and
4. `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` are finite `A`-modules.

Then the completion functor `colim_{U₀ ⊆ U' ⊆ U} Coh(𝒪_{U'}) ⟶ Coh(U, f𝒪_U)` restricts to an
equivalence on the full subcategories of finite locally free objects. Elementwise this is three
statements, and they are the three conjuncts below:

1. the functor carries a finite locally free coherent module on an open neighbourhood `V` of
   `U₀` inside `U` to a finite locally free object of `Coh(V, f𝒪_V)`, and — at the member
   `V = U` of `𝒱` — the stalkwise form of that conclusion;
2. it is fully faithful there: for every open neighbourhood `V` of `U₀` inside `U` and all finite
   locally free `𝒪_V`-modules `𝒢`, `ℱ` the canonical map
   `colim_{U₀ ⊆ W ⊆ V} Hom_{W}(𝒢|_{W}, ℱ|_{W}) ⟶ Hom_{Coh(U, f𝒪_U)}(𝒢^∧, ℱ^∧)` is bijective;
3. it is essentially surjective onto them: every finite locally free object of `Coh(U, f𝒪_U)` is
   the completion of a finite locally free coherent module on some open neighbourhood of `U₀`
   inside `U`.

The objects of `colim_{U₀ ⊆ U' ⊆ U} Coh(𝒪_{U'})` are the coherent modules on the individual
neighbourhoods, so the second conjunct quantifies over a neighbourhood `V` and a pair of finite
locally free modules on it, and renders `Hom_{Coh(U, f𝒪_U)}(𝒢^∧, ℱ^∧)` as the inverse limit of
the morphisms `𝒢|_{U₀,n} ⟶ ℱ|_{U₀,n}` over the infinitesimal neighbourhoods of `U₀`, which is
what a morphism of the two inverse systems `𝒢^∧`, `ℱ^∧` is. That is
`Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete`.

A *finite locally free object* of `Coh(V, ℐ)` is, by the source's own definition, one whose
`n`-th term is a finite locally free `𝒪_V/ℐ^{n+1}`-module. A term of a coherent adic system is
annihilated by `ℐ^{n+1}`, so over `𝒪_V` itself the only finite locally free such term is zero;
the condition has to be read over the closed subscheme cut out by `ℐ^{n+1}`, and that is
`Stacks.Algebraization.IsFiniteLocallyFreeAdic` — the `n`-th term is the direct image of a
finite locally free module on that subscheme. This is the form the first conjunct takes, for a
module defined on an arbitrary member `V` of `𝒱`, the objects of `colim_𝒱 Coh(𝒪_V)` being the
coherent modules on the individual neighbourhoods. Its second half is the same conclusion read
at the stalks at the member `V = U`, namely `Stacks.Algebraization.HasFiniteFreeStalks`; that is
the hypothesis the third conjunct consumes, so the two halves together let the three conjuncts
compose into the equivalence. The quantification is not vacuous: `V = ⊤` is a member of `𝒱`.

The source's proof is two citations: full faithfulness is [Stacks, Tag 0EKV], which is
`Stacks.Algebraization.completionFullyFaithfulComplete_principal`, and essential
surjectivity is [Stacks, Tag 0DXW], which is
`Stacks.Algebraization.canonicallyExtends_and_isCompletion_of_principal`. The first conjunct is
the statement that the functor lands in the finite locally free objects, by
`Stacks.Algebraization.isFiniteLocallyFreeAdic_completion` and
`Stacks.Algebraization.hasFiniteFreeStalks_completionFunctor_of_isFiniteLocallyFree`, and the
finite local freeness of the module produced in the third is obtained by shrinking the
neighbourhood to the locus where it is free. -/
@[stacks 0EKZ]
theorem completionEquivalence_principal_finiteLocallyFree {f : S.A}
    (hI : S.I = Ideal.span {f}) (hcomplete : IsAdicComplete (Ideal.span {f}) S.A)
    (hnzd : f ∈ nonZeroDivisors S.A)
    (hH1 : Module.Finite S.A (specialFibreLocalCohomology S f 1))
    (hH2 : Module.Finite S.A (specialFibreLocalCohomology S f 2)) :
    ((∀ (V : S.U.toScheme.Opens),
          (S.U.ι.base ⁻¹' Set.range S.Yι.base) ⊆ (V : Set S.U.toScheme) →
          ∀ G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf,
            AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj →
            IsFiniteLocallyFreeAdic ((idealOnOpen S).comap V.ι)
              ((completionFunctor V.toScheme ((idealOnOpen S).comap V.ι)).obj G)) ∧
        ∀ G : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf,
          AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj →
          HasFiniteFreeStalks S ((completionFunctor S.U.toScheme (idealOnOpen S)).obj G)) ∧
      NeighbourhoodCompletion.CompletionFullyFaithfulComplete
        (principalFormalLocusι S.A S.a f) ∧
      (∀ F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S),
        HasFiniteFreeStalks S F → IsCompletionNearClosedFiniteLocallyFree S F) :=
  have := hcomplete
  have hfI : f ∈ S.I := hI ▸ Ideal.mem_span_singleton_self f
  ⟨⟨fun V _ G hG =>
      isFiniteLocallyFreeAdic_completion V.toScheme ((idealOnOpen S).comap V.ι) G
        ((AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff G.obj).mp hG),
    fun G hG m y => hasFiniteFreeStalks_completionFunctor_of_isFiniteLocallyFree S G hG m y⟩,
    completionFullyFaithfulComplete_principal (S.I_le_a hfI) hnzd
      ((finite_specialFibreLocalCohomology_iff_quot S f 1).mp hH1),
    fun F hfree =>
      isCompletionNearClosedFiniteLocallyFree_of_principal S F hI hcomplete hnzd hH1 hH2 hfree⟩

end Stacks.Algebraization

end
