module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.InternalHomLocallyFree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsBridge
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ZeroLocusComplBridge
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.FiniteModule
public import StacksFrontier.RingTheory.Depth.LocalizationLocallyFree
public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.Module.LocallyFree.LocalizationAwayRestrict
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SheafHomLocallyFree

/-!
# The depth criterion for full faithfulness of the completion functor

Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` and let `U = Spec(A) ∖ V(𝔞)`. Stacks 0EKT asserts
that if

1. `A` has a dualizing complex and is complete with respect to `f`, and
2. `depth(A_𝔭) + dim((A/𝔭)_𝔮) > 2` for every prime `𝔭 ⊆ A` with `f ∉ 𝔭` and every
   `𝔮 ∈ V(𝔭) ∩ V(𝔞)`,

then the completion functor `Coh(𝒪_U) ⟶ Coh(U, (f)𝒪_U)` of Stacks 0880 is fully faithful on the
finite locally free objects.

## The proof

The source's proof is one line: it follows from Stacks 0EKS together with Faltings' annihilator
theorem, Local Cohomology, Proposition 0EFC. That deduction is carried out here with its
intermediate step made explicit, which is what lets it run without Stacks 0EKP.

Full faithfulness on the finite locally free objects is, by Stacks 0883
(`Stacks.Algebraization.completionFunctor_map_bijective`), the assertion that

`Γ(U, ℋ) ⟶ lim_n Γ(U, ℋ / (f)ⁿ ℋ)`

is an isomorphism for `ℋ = SheafHom(ℱ, 𝒢)` with `ℱ`, `𝒢` finite locally free. That `ℋ` is again
finite locally free is
`Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_internalHomCoherent`, and by
clause (1) of Stacks 0BK0 it is `M̃|_U` for a finite `A`-module `M`. For such an `M` the displayed
map is the map of Stacks 0EII, by
`Stacks.Algebraization.isIso_globalSectionsToLimit_coherentPrincipalTilde`, so what remains is
that `H¹_𝔞(M)` and `H²_𝔞(M)` are annihilated by powers of `f`.

That is where the hypotheses are used. Faltings' annihilator theorem at the module `M`, at the
specialization-stable sets `T = V(𝔞)` and `T' = V(f)` and at `s = 2`, asks for
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > 2` at the same primes. Since `f ∈ 𝔞`, a prime `𝔭` with `f ∉ 𝔭`
lies in `U`, where `ℋ` is finite locally free; so `M_𝔭` is a free — in particular flat —
`A_𝔭`-module and `depth(A_𝔭) ≤ depth(M_𝔭)` by `Module.depth_le_depth_of_flat`. Hypothesis (2),
which is stated for the ring, therefore gives Faltings' hypothesis for `M`.

## Main results

* `Stacks.Algebraization.isIso_globalSectionsToLimit_of_iso` — the theorem on formal functions
  in degree zero depends only on the isomorphism class of the coherent module.
* `Stacks.Algebraization.completionFullyFaithful_of_depth` — **Stacks 0EKT**, at the source's
  own hypotheses.

## Implementation notes

Two spellings of local cohomology meet here. Stacks 0EFC is stated with
`Stacks.LocalCohomology.localCohomologyWithSupportIn`, the derived-supported-sections model at a
specialization-stable subset, while Stacks 0EII is stated with
`Stacks.LocalCohomology.localCohomologyModule`, the coreflection model of Stacks 0A6Q at an
ideal. Over a Noetherian ring the two agree degreewise, which is
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`; the annihilator of
a module is transported along that isomorphism by `LinearEquiv.annihilator_eq`, so no second
statement of either model is introduced.

The depth–dimension inequality is phrased exactly as Stacks 0EFC phrases it, through
`Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt`, so that the two
quantities live in `EInt` and the comparison with `2` is an inequality of extended integers. The
source's index set `𝔮 ∈ V(𝔭) ∩ V(𝔞)` is spelled `𝔞 ≤ 𝔮` together with `𝔭 ≤ 𝔮`.

`Stacks.Algebraization.completionFullyFaithful_of_isAdicComplete_of_depth` is the earlier form
of the same statement, which routed through Stacks 0EKS and so carried the chain (1) ⇒ (4) of
Stacks 0EKP as a hypothesis `hEKP`. It is now a corollary of the unrestricted statement and
does not consume `hEKP`; it is kept, with its signature unchanged, for its existing consumer in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityLocalCase/FullyFaithfulComplete.lean`,
and no longer carries the tag.

## References

* [Stacks Project, Tag 0EKT](https://stacks.math.columbia.edu/tag/0EKT)
* [Stacks Project, Tag 0EKS](https://stacks.math.columbia.edu/tag/0EKS)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open IsLocalRing
open Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Transport along an isomorphism -/

/-- **The theorem on formal functions in degree zero only depends on the isomorphism class.**
An isomorphism of coherent modules induces an isomorphism of the two comparison maps, through
the completion functor and the limit of global sections. -/
public theorem isIso_globalSectionsToLimit_of_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (e : F ≅ G)
    (h : IsIso (globalSectionsToLimit I F)) : IsIso (globalSectionsToLimit I G) := by
  have := h
  have : HasLimit (Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj F)) :=
    inferInstance
  have : HasLimit (Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj G)) :=
    inferInstance
  let α : ((completionFunctor X I).obj F).obj ≅ ((completionFunctor X I).obj G).obj :=
    (ObjectProperty.ι _).mapIso ((completionFunctor X I).mapIso e)
  let β : Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj F) ≅
      Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj G) :=
    Functor.isoWhiskerRight α (_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
  let eF : (_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj F.obj ≅
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj G.obj :=
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso
      ((ObjectProperty.ι _).mapIso e)
  have hcomm : eF.hom ≫ globalSectionsToLimit I G =
      globalSectionsToLimit I F ≫ (HasLimit.isoOfNatIso β).hom := by
    refine limit.hom_ext (F := Stacks.Coherent.globalSectionsSystem
      ((completionFunctor X I).obj G)) fun n => ?_
    let ev := _root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
    calc (eF.hom ≫ globalSectionsToLimit I G) ≫
          limit.π (Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj G)) n
        = eF.hom ≫ (globalSectionsToLimit I G ≫
            limit.π (Stacks.Coherent.globalSectionsSystem
              ((completionFunctor X I).obj G)) n) := Category.assoc _ _ _
      _ = eF.hom ≫ ev.map (completionProjection X I G n.unop) :=
          congrArg (fun k => eF.hom ≫ k) (globalSectionsToLimit_π I G n)
      _ = ev.map (e.hom.hom ≫ completionProjection X I G n.unop) := (ev.map_comp _ _).symm
      _ = ev.map (completionProjection X I F n.unop ≫ α.hom.app n) :=
          congrArg ev.map (completionFunctor_map_quotient X I e.hom n.unop).symm
      _ = ev.map (completionProjection X I F n.unop) ≫ ev.map (α.hom.app n) :=
          ev.map_comp _ _
      _ = (globalSectionsToLimit I F ≫
            limit.π (Stacks.Coherent.globalSectionsSystem
              ((completionFunctor X I).obj F)) n) ≫ β.hom.app n :=
          congrArg (fun k => k ≫ β.hom.app n) (globalSectionsToLimit_π I F n).symm
      _ = globalSectionsToLimit I F ≫ (limit.π (Stacks.Coherent.globalSectionsSystem
            ((completionFunctor X I).obj F)) n ≫ β.hom.app n) := Category.assoc _ _ _
      _ = globalSectionsToLimit I F ≫ ((HasLimit.isoOfNatIso β).hom ≫
            limit.π (Stacks.Coherent.globalSectionsSystem
              ((completionFunctor X I).obj G)) n) :=
          congrArg (fun k => globalSectionsToLimit I F ≫ k)
            (HasLimit.isoOfNatIso_hom_π β n).symm
      _ = (globalSectionsToLimit I F ≫ (HasLimit.isoOfNatIso β).hom) ≫
            limit.π (Stacks.Coherent.globalSectionsSystem
              ((completionFunctor X I).obj G)) n := (Category.assoc _ _ _).symm
  have h1 : IsIso (globalSectionsToLimit I F) := h
  have h2 : IsIso (eF.hom ≫ globalSectionsToLimit I G) := by
    rw [hcomm]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (HasLimit.isoOfNatIso β).isIso_hom
  exact IsIso.of_isIso_comp_left eF.hom (globalSectionsToLimit I G)

/-! ### Stacks 0EKT -/

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {a : Ideal A} {f : A}

/-- The hypotheses of Faltings' annihilator theorem for a module which is finite locally free
away from `f`, deduced from the depth–dimension inequality for the ring. -/
public theorem faltings_hypothesis_of_depth (_hf : f ∈ a) (M : ModuleCat.{u} A)
    [Module.Finite A M]
    (hfree : Module.IsFiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f (M : Type u)))
    (hdepth : ∀ p q : PrimeSpectrum A, f ∉ p.asIdeal → a ≤ q.asIdeal →
      p.asIdeal ≤ q.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl A)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > ((2 : ℤ) : EInt))
    (p q : PrimeSpectrum A) (hp : p ∉ PrimeSpectrum.zeroLocus ({f} : Set A))
    (hq : q ∈ PrimeSpectrum.zeroLocus (a : Set A)) (hpq : p.asIdeal ≤ q.asIdeal) :
    enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl (M : Type u))) +
      krullDimToEInt
        (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > ((2 : ℤ) : EInt) := by
  have hfp : f ∉ p.asIdeal := fun hfp =>
    hp ((PrimeSpectrum.mem_zeroLocus p {f}).2 (Set.singleton_subset_iff.2 hfp))
  have hle := Module.depth_localizedModule_le_of_isFiniteLocallyFree_away (M : Type u) f hfree p hfp
  refine lt_of_lt_of_le (hdepth p q hfp
    (SetLike.coe_subset_coe.1 ((PrimeSpectrum.mem_zeroLocus q (a : Set A)).1 hq)) hpq) ?_
  exact add_le_add (enatToEInt_mono hle) le_rfl

/-- **Stacks 0EKT.** Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` and let
`U = Spec(A) ∖ V(𝔞)`. If `A` has a dualizing complex and is `f`-adically complete, and if
`depth(A_𝔭) + dim((A/𝔭)_𝔮) > 2` for every prime `𝔭` with `f ∉ 𝔭` and every
`𝔮 ∈ V(𝔭) ∩ V(𝔞)`, then the completion functor `Coh(𝒪_U) ⟶ Coh(U, (f)𝒪_U)` is fully faithful
on the full subcategory of finite locally free objects. -/
@[stacks 0EKT]
public theorem completionFullyFaithful_of_depth (A : Type u) [CommRing A] [IsNoetherianRing A]
    (a : Ideal A) (f : A) (hf : f ∈ a)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hdepth : ∀ p q : PrimeSpectrum A, f ∉ p.asIdeal → a ≤ q.asIdeal →
      p.asIdeal ≤ q.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl A)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > ((2 : ℤ) : EInt)) :
    CompletionFullyFaithfulOnFiniteLocallyFree (complementZeroLocus A a : Scheme)
      (complementPrincipalIdealSheaf A a f) := by
  have := hcomplete
  intro P Q hP hQ
  -- The internal hom is a finite locally free coherent module on `U`.
  have hHfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (internalHomCoherent (complementZeroLocus A a : Scheme) P Q).obj :=
    Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_internalHomCoherent P Q hP hQ
  have : _root_.SheafOfModules.IsCoherent
      (R := (AlgebraicGeometry.zeroLocusCompl (A := CommRingCat.of A) a).toScheme.ringCatSheaf)
      (internalHomCoherent (complementZeroLocus A a : Scheme) P Q).obj :=
    (internalHomCoherent (complementZeroLocus A a : Scheme) P Q).property
  -- It is `M̃|_U` for a finite `A`-module `M`.
  obtain ⟨M, hMfin, ⟨eM⟩⟩ :=
    AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl
      (A := CommRingCat.of A) a (internalHomCoherent (complementZeroLocus A a : Scheme) P Q).obj
  have := hMfin
  -- Hence `M_f` is a finite locally free `A_f`-module.
  have hres : Scheme.Modules.IsFiniteLocallyFree
      ((tilde M).restrict (AlgebraicGeometry.zeroLocusCompl (A := CommRingCat.of A) a).ι) :=
    (Scheme.Modules.isFiniteLocallyFree_iff _).2
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso eM.symm (h := hHfree))
  have hfree :=
    Module.isFiniteLocallyFree_localization_away_of_mem_of_isFiniteLocallyFree_zeroLocusCompl
      (A := CommRingCat.of A) a M hres f hf
  -- Faltings' annihilator theorem at `T = V(𝔞)`, `T' = V(f)`, `s = 2` and the module `M`.
  obtain ⟨J, hJT', hJ⟩ :=
    (exists_ideal_le_annihilator_localCohomology_iff A (M : Type u)
        (PrimeSpectrum.zeroLocus (a : Set A)) (PrimeSpectrum.zeroLocus ({f} : Set A))
        (PrimeSpectrum.zeroLocus_anti_mono (Set.singleton_subset_iff.2 hf))
        (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
        (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization 2 (by norm_num)
        omega homega).2
      (fun p q hp hq hpq => faltings_hypothesis_of_depth hf M hfree hdepth p q hp hq hpq)
  -- `V(J) ⊆ V(f)` says that `f` lies in the radical of `J`, so a power of `f` lies in `J`.
  have hJspan : PrimeSpectrum.zeroLocus (J : Set A) ⊆
      PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A) := by
    rw [PrimeSpectrum.zeroLocus_span]
    exact hJT'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, f ^ n ∈ J :=
    Ideal.mem_radical_iff.1
      ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff J (Ideal.span {f})).1 hJspan
        (Ideal.mem_span_singleton_self f))
  -- Transport the annihilation to the coreflection model of local cohomology.
  have key : ∀ i : ℤ, i ≤ 2 →
      ∀ x : localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a) M i, f ^ n • x = 0 := by
    intro i hi
    have hann := LinearEquiv.annihilator_eq
      (localCohomologyWithSupportInIsoLocalCohomologyModule A a
        (Ideal.fg_of_isNoetherianRing a) M i).toLinearEquiv
    exact Module.mem_annihilator.1 (hann.le (hJ i hi hn))
  -- Stacks 0EII for `M`, read as the theorem on formal functions in degree zero for `M̃|_U`.
  have hbij := ComplementTower.bijective_sectionsToLimit a f M n n (key 1 (by norm_num))
    (key 2 le_rfl)
  have hgsl := isIso_globalSectionsToLimit_coherentPrincipalTilde hf M hbij
  rw [principalIdealOnOpen_eq hf] at hgsl
  -- Transport to `H` and apply Stacks 0883.
  refine completionFunctor_map_bijective (complementPrincipalIdealSheaf A a f) P Q ?_
  exact isIso_globalSectionsToLimit_of_iso (complementPrincipalIdealSheaf A a f)
    (ObjectProperty.isoMk _ eM) hgsl

/-- The earlier form of Stacks 0EKT, routed through Stacks 0EKS and therefore carrying the
chain (1) ⇒ (4) of Stacks 0EKP as the hypothesis `hEKP`. That hypothesis is no longer consumed:
the statement is now a corollary of `Stacks.Algebraization.completionFullyFaithful_of_depth`,
which proves the tag at the source's own hypotheses. The signature is kept unchanged for its
existing consumer, `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleRestriction_of_depth`, and
the tag has moved to the unrestricted statement above. -/
public theorem completionFullyFaithful_of_isAdicComplete_of_depth
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (f : A) (hf : f ∈ a)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hdepth : ∀ p q : PrimeSpectrum A, f ∉ p.asIdeal → a ≤ q.asIdeal →
      p.asIdeal ≤ q.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl A)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > ((2 : ℤ) : EInt))
    (hEKP : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (b : Ideal B) (g : B),
      Scheme.IsQuasiAffine (complementZeroLocus B b : Scheme) →
      Function.Bijective (ComplementTower.sectionsToLimit B b g (ModuleCat.of B B)) →
      CompletionFullyFaithfulOnFiniteLocallyFree (complementZeroLocus B b : Scheme)
        (complementPrincipalIdealSheaf B b g)) :
    CompletionFullyFaithfulOnFiniteLocallyFree (complementZeroLocus A a : Scheme)
      (complementPrincipalIdealSheaf A a f) :=
  have := hEKP
  completionFullyFaithful_of_depth A a f hf omega homega hcomplete hdepth

end Stacks.Algebraization

end
