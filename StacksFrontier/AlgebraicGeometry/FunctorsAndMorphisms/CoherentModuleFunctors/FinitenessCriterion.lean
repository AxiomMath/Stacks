module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FiniteTypePushforward
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.SectionsFiniteness
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthEqLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.GlobalSectionsChoice

/-!
# Finiteness from a coherent module with vanishing higher direct images

Let `f : V ⟶ X` be a quasi-finite separated morphism of Noetherian schemes.  If there is a
coherent `𝒪_V`-module `𝒦` whose support is the whole of `V` such that `f_*𝒦` is coherent and
`R^q f_*𝒦 = 0` for every `q > 0`, then `f` is finite.  This is [Stacks, Tag 0FZM].

## Main results

* `isFinite_of_isCoherent_pushforward_of_isZero_higherDirectImages`, in the namespace
  `Stacks.AlgebraicGeometry.CoherentModuleFunctors`: the criterion.

## Implementation notes

Quasi-finiteness is [Stacks, Tag 02NG] — locally quasi-finite and of finite type — spelled in
Mathlib's vocabulary as `AlgebraicGeometry.LocallyQuasiFinite`,
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` together.  The
higher direct images are the positive degrees of `CategoryTheory.Functor.rightDerivedPlus` of
`AlgebraicGeometry.Scheme.Modules.pushforward`, and the support is the stalkwise support
`SheafOfModules.supp`.  The existential over `𝒦` of the source is taken as an explicit
hypothesis, which is the same statement.

The argument runs in three stages.  Finiteness is Zariski local on the target, so one may assume
`X` affine; over an affine target Zariski's main theorem [Stacks, Tag 05K0] factors `f` as a
quasi-compact open immersion `j : V ⟶ Y` followed by a finite morphism, and `Y` is then affine
and Noetherian, so `V` is an open `U` of the spectrum of a Noetherian ring `R`.

The content is the last stage.  Writing `U = Spec R \ V(I)` and `M = Γ(U, 𝒦)`, coherence of the
direct image makes `M` a finite `R`-module, and all of its local cohomology with support in
`V(I)` vanishes: degrees zero and one because the low-degree sequence of [Stacks, Tag 0DWR]
degenerates at the canonical extension, and degree `n + 2` by the comparison
`H^{n+1}(U, 𝒦) ≅ H^{n+2}_{V(I)}(M)` of the same tag together with the vanishing of the
cohomology of `𝒦`, which the affine target supplies through [Stacks, Tag 01XK].  A finite module
with no local cohomology has infinite `I`-depth by [Stacks, Tag 0AVZ], hence `I·M = M`, hence a
support disjoint from `V(I)`.  That support is the support of the direct image, which contains
`U` because `𝒦` has full support; so the support of the direct image is exactly `U`, and it is
closed because the direct image is of finite type.  An open immersion with closed image is a
closed immersion, hence finite.

## References

* [Stacks Project, Tag 0FZM](https://stacks.math.columbia.edu/tag/0FZM)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.CoherentModuleFunctors

attribute [local instance] HasDerivedCategory.standard

/-- Isomorphic abelian groups either both have a nonzero element or both have none. -/
private lemma exists_ne_zero_iff_of_iso {A B : Ab.{u}} (e : A ≅ B) :
    (∃ a : A, a ≠ 0) ↔ ∃ b : B, b ≠ 0 := by
  let φ := e.addCommGroupIsoToAddEquiv
  refine ⟨fun ⟨a, ha⟩ => ⟨φ a, φ.map_ne_zero_iff.mpr ha⟩,
    fun ⟨b, hb⟩ => ⟨φ.symm b, φ.symm.map_ne_zero_iff.mpr hb⟩⟩

/-- Isomorphic sheaves of modules have the same support. -/
private lemma supp_eq_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    SheafOfModules.supp F = SheafOfModules.supp G := by
  ext x
  exact exists_ne_zero_iff_of_iso
    ((TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso ((Scheme.Modules.toPresheaf X).mapIso e))

/-- The support of a direct image along an open immersion meets the image exactly in the image
of the support. -/
private lemma mem_supp_pushforward_iff {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j]
    (F : V.Modules) (v : V) :
    j v ∈ SheafOfModules.supp ((Scheme.Modules.pushforward j).obj F) ↔
      v ∈ SheafOfModules.supp F := by
  let a := TopCat.Presheaf.stalkPushforward Ab.{u} j.base F.presheaf v
  have : IsIso a :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (C := Ab.{u}) j.isOpenEmbedding.isInducing F.presheaf v
  change (∃ s : ((TopCat.Presheaf.pushforward Ab.{u} j.base).obj F.presheaf).stalk (j v), s ≠ 0) ↔
    (∃ s : F.presheaf.stalk v, s ≠ 0)
  exact exists_ne_zero_iff_of_iso (asIso a)

/-- The support of the sheaf associated with a module over a commutative ring is the support of
the module: the stalk at a prime is the localisation there. -/
private alias supp_tilde := _root_.AlgebraicGeometry.supp_tilde

/-- The support of a quasi-coherent module on an affine scheme is the support of its module of
global sections. -/
private lemma supp_eq_module_support {R : CommRingCat.{u}} (Q : (Spec R).Modules)
    [Q.IsQuasicoherent] :
    SheafOfModules.supp Q = (Module.support R (moduleSpecΓFunctor.obj Q) : Set (Spec R)) := by
  rw [← supp_tilde R (moduleSpecΓFunctor.obj Q)]
  exact (supp_eq_of_iso (asIso Q.fromTildeΓ)).symm

/-- Sections over `U = Spec R \ V(I)` of a coherent module with coherent direct image form a
finite `R`-module. -/
private lemma finite_complementGlobalSections (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (F : (Stacks.LocalCohomology.complementZeroLocus R I : Scheme).Modules)
    [F.IsCoherent]
    (hQ : ((Scheme.Modules.pushforward
      (Stacks.LocalCohomology.complementZeroLocus R I).ι).obj F).IsCoherent) :
    Module.Finite R (Stacks.LocalCohomology.complementGlobalSections R I F) :=
  (Stacks.LocalCohomology.isCoherent_pushforward_iff_module_finite_sections (CommRingCat.of R)
    (Stacks.LocalCohomology.complementZeroLocus R I) F).mp hQ

open Stacks.LocalCohomology in
/-- **All local cohomology with support in `V(I)` of a module of sections on the complement
vanishes.** Degrees zero and one are the degeneration of the low-degree sequence of Stacks 0DWR
at the canonical extension; in degree `n + 2` the comparison of Stacks 0DWR above degree zero
turns the statement into the vanishing of `H^{n+1}(U, ℱ)`. -/
private lemma isZero_localCohomologyModule_complementGlobalSections
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (F : (complementZeroLocus R I : Scheme).Modules) [F.IsQuasicoherent]
    (hvanish : ∀ n : ℕ, 1 ≤ n → IsZero
      (((SheafOfModules.evaluation (complementZeroLocus R I : Scheme).ringCatSheaf
        (op ⊤)).rightDerived n).obj F))
    (i : ℕ) :
    IsZero (localCohomologyModule R I hI (complementGlobalSections R I F) (i : ℤ)) := by
  match i with
  | 0 => simpa using isZero_localCohomology_zero_globalSectionsModule R I hI F
  | 1 => simpa using isZero_localCohomology_one_globalSectionsModule R I hI F
  | (n + 2) =>
    obtain ⟨e⟩ := iso_restrict_tilde_globalSectionsModule R I hI F
    have hdeg : ((n + 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [hdeg]
    refine (isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule I hI
      (complementGlobalSections R I F) (n + 1) (by omega)).1 ?_
    refine IsZero.of_iso
      ((isZero_hgroup_iff_isZero_rightDerived (complementZeroLocus R I : Scheme).ringCatSheaf ⊤
        (n + 1) F).mpr (hvanish (n + 1) (by omega)))
      ((Hfunctor (complementZeroLocus R I : Scheme).ringCatSheaf ⊤ (n + 1)).mapIso e).symm

open Stacks.LocalCohomology in
/-- **The complement of a zero locus carrying such a module is closed.** Let `R` be Noetherian,
`U = Spec R \ V(I)` and `ℱ` a coherent `𝒪_U`-module whose support is all of `U`, whose direct
image is coherent and whose positive cohomology vanishes. Then the inclusion `U ⟶ Spec R` is
finite, that is, `U` is closed as well as open.

The module `M = Γ(U, ℱ)` is finite over `R` and has no local cohomology with support in `V(I)`
in any degree, so its `I`-depth is `⊤` and `I·M = M`. Hence the support of `M` misses `V(I)`,
and that support is the support of the direct image, which contains `U` because `ℱ` has full
support. So the support of the direct image is exactly `U`, and it is closed because the direct
image is of finite type. -/
private theorem isFinite_complementZeroLocus_ι (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (F : (complementZeroLocus R I : Scheme).Modules) [F.IsCoherent]
    (hsupp : SheafOfModules.supp F = Set.univ)
    (hQ : ((Scheme.Modules.pushforward (complementZeroLocus R I).ι).obj F).IsCoherent)
    (hvanish : ∀ n : ℕ, 1 ≤ n → IsZero
      (((SheafOfModules.evaluation (complementZeroLocus R I : Scheme).ringCatSheaf
        (op ⊤)).rightDerived n).obj F)) :
    IsFinite (complementZeroLocus R I).ι := by
  classical
  have hI : I.FG := IsNoetherian.noetherian I
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : ((Scheme.Modules.pushforward (complementZeroLocus R I).ι).obj F).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have hMfin : Module.Finite R (complementGlobalSections R I F) :=
    finite_complementGlobalSections R I F hQ
  have hIM : I • (⊤ : Submodule R (complementGlobalSections R I F)) = ⊤ := by
    by_contra hne
    have hlt := Module.depth_lt_top R I (complementGlobalSections R I F) hne
    rw [depth_eq_sInf_nontrivial_localCohomologyWithSupportIn R I
      (complementGlobalSections R I F) hne] at hlt
    obtain ⟨-, ⟨i, -, hi⟩, -⟩ := sInf_lt_iff.mp hlt
    refine (not_nontrivial_iff_subsingleton.mpr ?_) hi
    exact ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_iso
      (isZero_localCohomologyModule_complementGlobalSections R I hI F hvanish i)
      (localCohomologyWithSupportInIsoLocalCohomologyModule R I hI
        (complementGlobalSections R I F) i))
  have hdisj : Module.support R (complementGlobalSections R I F) ∩
      PrimeSpectrum.zeroLocus (I : Set R) = ∅ := by
    rw [← Module.support_quotient I]
    have : Subsingleton (complementGlobalSections R I F ⧸
        I • (⊤ : Submodule R (complementGlobalSections R I F))) :=
      Submodule.Quotient.subsingleton_iff.mpr hIM
    exact Module.support_eq_empty
  have hsuppQ : SheafOfModules.supp ((Scheme.Modules.pushforward
      (complementZeroLocus R I).ι).obj F) = Set.range (complementZeroLocus R I).ι := by
    refine Set.Subset.antisymm (fun x hx => ?_) ?_
    · have hxM : x ∈ Module.support R (complementGlobalSections R I F) :=
        (supp_eq_module_support ((Scheme.Modules.pushforward
          (complementZeroLocus R I).ι).obj F)).subset hx
      refine ⟨⟨x, fun hxI => ?_⟩, rfl⟩
      exact absurd (show x ∈ Module.support R (complementGlobalSections R I F) ∩
        PrimeSpectrum.zeroLocus (I : Set R) from ⟨hxM, hxI⟩) (by rw [hdisj]; exact id)
    · rintro - ⟨v, rfl⟩
      rw [mem_supp_pushforward_iff (complementZeroLocus R I).ι F v, hsupp]
      exact Set.mem_univ _
  have : ((Scheme.Modules.pushforward (complementZeroLocus R I).ι).obj F).IsFiniteType :=
    hQ.isFiniteType
  have hclosed : IsClosed (Set.range (complementZeroLocus R I).ι) :=
    hsuppQ ▸ SheafOfModules.isClosed_supp _
  have : IsClosedImmersion (complementZeroLocus R I).ι :=
    IsClosedImmersion.of_isPreimmersion _ hclosed
  infer_instance

/-- Every open of an affine scheme is the complement of the zero locus of an ideal, namely of
the vanishing ideal of its closed complement. -/
private lemma exists_eq_complementZeroLocus (R : Type u) [CommRing R]
    (U : (Spec (CommRingCat.of R)).Opens) :
    ∃ I : Ideal R, U = Stacks.LocalCohomology.complementZeroLocus R I := by
  refine ⟨PrimeSpectrum.vanishingIdeal (U.1ᶜ), TopologicalSpace.Opens.ext ?_⟩
  change (U.1 : Set (PrimeSpectrum R)) =
    (PrimeSpectrum.zeroLocus
      ((PrimeSpectrum.vanishingIdeal (U.1ᶜ) : Ideal R) : Set R))ᶜ
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact ((congrArg compl (U.isOpen.isClosed_compl).closure_eq).trans (compl_compl _)).symm

/-- **The core of the criterion, for an open of an affine Noetherian scheme.** Let `R` be
Noetherian, `U ⊆ Spec R` an open and `ℱ` a coherent `𝒪_U`-module with full support, coherent
direct image and vanishing positive cohomology. Then `U ⟶ Spec R` is finite.

Every open of `Spec R` is the complement of the zero locus of an ideal, so this is
`isFinite_complementZeroLocus_ι`. -/
private theorem isFinite_opens_ι (R : Type u) [CommRing R] [IsNoetherianRing R]
    (U : (Spec (CommRingCat.of R)).Opens) (F : (U : Scheme).Modules) [F.IsCoherent]
    (hsupp : SheafOfModules.supp F = Set.univ)
    (hQ : ((Scheme.Modules.pushforward U.ι).obj F).IsCoherent)
    (hvanish : ∀ n : ℕ, 1 ≤ n → IsZero
      (((SheafOfModules.evaluation (U : Scheme).ringCatSheaf (op ⊤)).rightDerived n).obj F)) :
    IsFinite U.ι := by
  obtain ⟨I, rfl⟩ := exists_eq_complementZeroLocus R U
  exact isFinite_complementZeroLocus_ι R I F hsupp hQ hvanish

/-- **The criterion for an open immersion into an affine Noetherian scheme.** The source is
identified with an open of the spectrum of the ring of global functions, and the module is
carried along that identification; coherence, full support and the vanishing of positive
cohomology all transport, the last by
`AlgebraicGeometry.Scheme.Modules.rightDerivedEvaluationTopPushforwardIso`. -/
private theorem isFinite_isOpenImmersion_of_isAffine {V Y : Scheme.{u}}
    [IsNoetherian Y] [IsAffine Y] (j : V ⟶ Y) [IsOpenImmersion j]
    (K : V.Modules) [K.IsCoherent] (hsupp : SheafOfModules.supp K = Set.univ)
    (hjK : ((Scheme.Modules.pushforward j).obj K).IsCoherent)
    (hvanish : ∀ n : ℕ, 1 ≤ n → IsZero
      (((SheafOfModules.evaluation V.ringCatSheaf (op ⊤)).rightDerived n).obj K)) :
    IsFinite j := by
  have hNR : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  set g : V ⟶ Spec Γ(Y, ⊤) := j ≫ Y.isoSpec.hom with hgdef
  have hei : g.isoOpensRange.hom ≫ g.opensRange.ι = g := Scheme.Hom.isoOpensRange_hom_ι g
  have hGc : ((Scheme.Modules.pushforward g.isoOpensRange.hom).obj K).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
      g.isoOpensRange.hom K
  have hGs : SheafOfModules.supp
      ((Scheme.Modules.pushforward g.isoOpensRange.hom).obj K) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := g.isoOpensRange.hom.surjective y
    rw [mem_supp_pushforward_iff g.isoOpensRange.hom K x, hsupp]
    exact Set.mem_univ _
  have hGQ : ((Scheme.Modules.pushforward g.opensRange.ι).obj
      ((Scheme.Modules.pushforward g.isoOpensRange.hom).obj K)).IsCoherent := by
    refine ObjectProperty.prop_of_iso
      (P := fun M : SheafOfModules.{u} (Spec Γ(Y, ⊤)).ringCatSheaf => M.IsCoherent)
      ((Scheme.Modules.pushforwardComp j Y.isoSpec.hom).app K ≪≫
        ((Scheme.Modules.pushforwardCongr hei).app K).symm ≪≫
        ((Scheme.Modules.pushforwardComp g.isoOpensRange.hom g.opensRange.ι).app K).symm)
      (Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
        Y.isoSpec.hom _)
  have hGv : ∀ n : ℕ, 1 ≤ n → IsZero (((SheafOfModules.evaluation
      (g.opensRange : Scheme).ringCatSheaf (op ⊤)).rightDerived n).obj
        ((Scheme.Modules.pushforward g.isoOpensRange.hom).obj K)) := by
    intro n hn
    have h0 : Subsingleton
        (((SheafOfModules.evaluation V.ringCatSheaf (op ⊤)).rightDerived n).obj K) :=
      ModuleCat.isZero_iff_subsingleton.mp (hvanish n hn)
    exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr h0)
      (rightDerivedEvaluationTopPushforwardIso g.isoOpensRange.hom K n).symm
  have hU := isFinite_opens_ι (Γ(Y, ⊤) : Type u) g.opensRange
    ((Scheme.Modules.pushforward g.isoOpensRange.hom).obj K) hGs hGQ hGv
  have hg : IsFinite g := by rw [← hei]; infer_instance
  have : IsFinite (g ≫ Y.isoSpec.inv) := inferInstance
  simpa [hgdef] using this

open Stacks.FiniteFactorization Stacks.Cohomology.AffineBase in
/-- **The criterion over an affine target.** Zariski's main theorem [Stacks, Tag 05K0] factors a
quasi-finite separated morphism as a quasi-compact open immersion `j` into a scheme finite over
the target; that scheme is affine and Noetherian. The direct image `j_*𝒦` is coherent because
`f_*𝒦` is and a finite morphism detects finite type [Stacks, Tag 05B3], and the positive
cohomology of `𝒦` vanishes because the target is affine [Stacks, Tag 01XK]. So `j` is finite by
`isFinite_isOpenImmersion_of_isAffine`, and `f = j ≫ π` is finite. -/
private theorem isFinite_of_isAffine_target {V X : Scheme.{u}} (f : V ⟶ X)
    [IsNoetherian V] [IsNoetherian X] [IsAffine X]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [QuasiCompact f] [IsSeparated f]
    (K : V.Modules) [K.IsCoherent] (hsupp : SheafOfModules.supp K = Set.univ)
    (hpush : ((Scheme.Modules.pushforward f).obj K).IsCoherent)
    (hvanish : ∀ q : ℤ, 0 < q →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus q).obj K)) :
    IsFinite f := by
  obtain ⟨Y, j, π, hj, hjqc, hπ, hfactor⟩ := exists_isOpenImmersion_isFinite_factorization f
  have : IsAffine Y := isAffine_of_isAffineHom π
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian Y := ⟨⟩
  have : K.IsQuasicoherent := isQuasicoherent_of_isCoherent K
  have : ((Scheme.Modules.pushforward j).obj K).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs j K
  have hcomp : ((Scheme.Modules.pushforward π).obj
      ((Scheme.Modules.pushforward j).obj K)).IsCoherent :=
    ObjectProperty.prop_of_iso
      (P := fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)
      ((Scheme.Modules.pushforwardCongr hfactor).app K ≪≫
        ((Scheme.Modules.pushforwardComp j π).app K).symm) hpush
  have : ((Scheme.Modules.pushforward j).obj K).IsFiniteType :=
    (AlgebraicGeometry.isFiniteType_iff_pushforward_isFiniteType π
      ((Scheme.Modules.pushforward j).obj K)).mpr hcomp.isFiniteType
  have hjK : ((Scheme.Modules.pushforward j).obj K).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _
  have hcoh : ∀ n : ℕ, 1 ≤ n → IsZero
      (((SheafOfModules.evaluation V.ringCatSheaf (op ⊤)).rightDerived n).obj K) := by
    intro n hn
    have hz : IsZero ((moduleGlobalSections X).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj K)) :=
      (moduleGlobalSections X).map_isZero (hvanish (n : ℤ) (by exact_mod_cast hn))
    have hz1 := IsZero.of_iso hz
      ((cohomologyIsoGlobalSectionsRightDerivedPushforward f (n : ℤ)).app ⟨K, inferInstance⟩)
    have h0 := ModuleCat.isZero_iff_subsingleton.mp hz1
    exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr h0)
      ((Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections V) n).app K)
  rw [hfactor]
  have : IsFinite j := isFinite_isOpenImmersion_of_isAffine j K hsupp hjK hcoh
  infer_instance

open Stacks.AlgebraicGeometry.HigherDirectImage
  Stacks.AlgebraicGeometry.SchemeHigherDirectImage in
/-- **A finiteness criterion.** Let `f : V ⟶ X` be a quasi-finite separated morphism of
Noetherian schemes. If there is a coherent `𝒪_V`-module `𝒦` whose support is all of `V` such
that `f_*𝒦` is coherent and `R^q f_*𝒦 = 0` for every `q > 0`, then `f` is finite.

Quasi-finiteness is [Stacks, Tag 02NG] — locally quasi-finite and of finite type — which in
Mathlib's vocabulary is `AlgebraicGeometry.LocallyQuasiFinite`,
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` together. The
existential over `𝒦` of the source is taken as an explicit hypothesis.

Finiteness is Zariski-local on the target, and every hypothesis restricts to an affine open `U`
of `X`: coherence and the support condition because they are local, and the vanishing of the
higher direct images by the comparison `R^q(f|_U)_*(𝒦|_{f^{-1}U}) ≅ (R^q f_*𝒦)|_U` of
[Stacks, Tag 01E5]. Over an affine target the statement is
`isFinite_of_isAffine_target`. -/
@[stacks 0FZM]
public theorem isFinite_of_isCoherent_pushforward_of_isZero_higherDirectImages
    {V X : Scheme.{u}} (f : V ⟶ X) [IsNoetherian V] [IsNoetherian X]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [QuasiCompact f] [IsSeparated f]
    (K : V.Modules) [K.IsCoherent] (hsupp : SheafOfModules.supp K = Set.univ)
    (hpush : ((Scheme.Modules.pushforward f).obj K).IsCoherent)
    (hvanish : ∀ q : ℤ, 0 < q →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus q).obj K)) :
    IsFinite f := by
  have : K.IsFiniteType := ‹K.IsCoherent›.isFiniteType
  have : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun U : X.affineOpens => (U : X.Opens)) (iSup_affineOpens_eq_top X) fun U => ?_
  have : IsAffine (U.1 : Scheme) := U.2
  have : IsNoetherian (U.1 : Scheme) := ⟨⟩
  have : TopologicalSpace.NoetherianSpace (f ⁻¹ᵁ U.1 : Scheme) :=
    (f ⁻¹ᵁ U.1).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace (f ⁻¹ᵁ U.1 : Scheme) := TopologicalSpace.NoetherianSpace.compactSpace _
  have : IsNoetherian (f ⁻¹ᵁ U.1 : Scheme) := ⟨⟩
  have hK'c : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj K).IsCoherent :=
    AlgebraicGeometry.Modules.isCoherent_restrict K (f ⁻¹ᵁ U.1)
  have hK's : SheafOfModules.supp
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj K) = Set.univ := by
    refine (supp_eq_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U.1).ι).app K)).trans ?_
    refine (Stacks.Modules.supp_pullback (f ⁻¹ᵁ U.1).ι K).trans ?_
    rw [hsupp]
    exact Set.preimage_univ
  have hK'p : ((Scheme.Modules.pushforward (f ∣_ U.1)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj K)).IsCoherent := by
    refine ObjectProperty.prop_of_iso
      (P := fun M : SheafOfModules.{u} (U.1 : Scheme).ringCatSheaf => M.IsCoherent)
      (((Scheme.Modules.restrictFunctor U.1.ι).mapIso (higherDirectImageZeroIso f K)).symm ≪≫
        (rightDerivedPlusRestrictObjIso f U.1 0 K).symm ≪≫
        higherDirectImageZeroIso (f ∣_ U.1) _)
      (AlgebraicGeometry.Modules.isCoherent_restrict
        ((Scheme.Modules.pushforward f).obj K) U.1)
  have hK'v : ∀ q : ℤ, 0 < q → IsZero (((Scheme.Modules.pushforward (f ∣_ U.1)).rightDerivedPlus
      q).obj ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj K)) := by
    intro q hq
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = (n : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg hq.le).symm⟩
    exact IsZero.of_iso
      ((Scheme.Modules.restrictFunctor U.1.ι).map_isZero (hvanish (n : ℤ) hq))
      (rightDerivedPlusRestrictObjIso f U.1 n K)
  exact isFinite_of_isAffine_target (f ∣_ U.1) _ hK's hK'p hK'v

end Stacks.AlgebraicGeometry.CoherentModuleFunctors

end
