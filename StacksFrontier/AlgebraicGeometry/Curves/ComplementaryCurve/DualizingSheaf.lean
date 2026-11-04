module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseShortExact
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafInclusion
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.IdealMultipleKernel
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.SchemeTheoreticUnion
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GeometricallyReducedCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedSingularSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparisonEpi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientComparison.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Algebraization
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ClosedUnion
public import StacksFrontier.AlgebraicGeometry.Modules.LocallyTrivialSections
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.CategoryTheory.Abelian.DisjointSubobjectSequences
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportEquiv
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dualizing sheaves of a closed subcurve and of the closure of its complement

Let `X` be a proper scheme over a field which is Gorenstein, reduced and equidimensional of
dimension one, let `Y ⊆ X` be a reduced closed subscheme equidimensional of dimension one, and let
`Z` be the scheme-theoretic closure of `X \ Y`. [Stacks, Tag 0E34] describes the dualizing sheaves
of `Y` and `Z` in terms of that of `X`, and the exact sequences relating them.

Parts (1) and (2) do not involve the dualizing sheaves. Parts (3)–(5) are proved for a
dualizing sheaf `ω_X` which is invertible, following the source: `ω_X` is trivial on the finite
discrete scheme `Y ∩ Z`, `i_*ω_Y = 𝓗om(i_*𝒪_Y, ω_X)` by [Stacks, Tag 0E33], evaluation at one
identifies it with the annihilator `𝓙ω_X` of `𝓘` in `ω_X`, and the sequences come from
`𝓘ω_X ∩ 𝓙ω_X = 0`, `𝓘ω_X + 𝓙ω_X = (𝓘 + 𝓙)ω_X` and `ω_X/𝓚ω_X ≅ k_*k^*ω_X` ([Stacks, Tag 0EL1]).

## Main results

* `Stacks.Curves.isCohenMacaulay_subscheme`: a reduced closed subscheme of a locally Noetherian
  scheme of dimension at most one is Cohen–Macaulay; in particular `Y` and `Z` are.
* `Stacks.Curves.bijOn_ideal_complementaryCurve` and
  `Stacks.Curves.bijOn_complementaryCurveIdeal_subscheme`: the ideal sheaf `I` of `Y` is the
  direct image of the ideal sheaf `I'` of `Y ∩ Z` in `Z`, and the ideal sheaf `J` of `Z` is the
  direct image of the ideal sheaf `J'` of `Y ∩ Z` in `Y`, read on affine opens.
* `Stacks.Curves.dualizingSheafOverField_subscheme_of_isInvertible`: parts (3), and the second and
  fifth sequences of (5), for a closed subscheme of a reduced curve with locally trivial `ω_X`.
* `Stacks.Curves.discreteTopology_intersectionWithComplementaryCurve`: `Y ∩ Z` is discrete.
* `Stacks.Curves.exists_shortExact_restrictions` and
  `Stacks.Curves.exists_shortExact_idealMultiples`: the Mayer–Vietoris type sequences of a locally
  trivial module for two ideals with zero intersection.
* `Stacks.Curves.dualizingSheafOverField_closedSubcurve_of_isInvertible`: all of
  [Stacks, Tag 0E34] when `ω_X` is invertible.

## Implementation notes

The source writes `𝓘 = i_*𝓘'` and `𝓙 = j_*𝓙'`; since `𝓘'` lives on `Z` and `𝓙'` on `Y`, the
direct images are along `j` and `i` respectively, which is what is proved. "`𝓘 = j_*𝓘'`" means
that the restriction map `𝒪_X ⟶ j_*𝒪_Z` carries `𝓘` isomorphically onto `j_*𝓘'`; both sheaves are
quasi-coherent, so this is the statement that over every affine open `U` restriction to `Z` is a
bijection from `𝓘(U)` onto `𝓘'(Z ∩ U)`.

## References

* [Stacks Project, Tag 0E34](https://stacks.math.columbia.edu/tag/0E34)
* [Stacks Project, Tag 0E33](https://stacks.math.columbia.edu/tag/0E33)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  RingedSpaceModuleAdjunction

universe u

namespace Stacks.Curves

variable {X : Scheme.{u}}

/-- **A reduced closed subscheme of a curve is Cohen–Macaulay.** A reduced closed subscheme of a
locally Noetherian scheme of dimension at most one is again reduced, locally Noetherian and of
dimension at most one, hence Cohen–Macaulay. -/
@[ega "IV 5.7.8" "more general"]
theorem isCohenMacaulay_subscheme [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (C : X.IdealSheafData) [IsReduced C.subscheme] : IsCohenMacaulay C.subscheme :=
  have := LocallyOfFiniteType.isLocallyNoetherian C.subschemeι
  isCohenMacaulay_of_isReduced_of_topologicalKrullDim_le_one C.subscheme
    ((C.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdim)

/-- **The closure of the complement of a closed subscheme of a reduced curve is Cohen–Macaulay.**
It is the scheme-theoretic image of a reduced scheme, hence reduced. -/
theorem isCohenMacaulay_complementaryCurve [IsLocallyNoetherian X] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (C : X.IdealSheafData) :
    IsCohenMacaulay (complementaryCurve C) :=
  isCohenMacaulay_subscheme hdim (complementaryCurveIdeal C)

/-- **[Stacks, Tag 0E34] (2), for the ideal sheaf of `Y`.** On a reduced scheme, the ideal sheaf
of a closed subscheme `C` is the direct image of the ideal sheaf of the intersection
`C ⊔ complementaryCurveIdeal C` inside the closure of the complement: over every affine open,
restriction to the closure of the complement maps `C(U)` bijectively onto that ideal. -/
theorem bijOn_ideal_complementaryCurve [IsReduced X] (C : X.IdealSheafData)
    (U : X.affineOpens) :
    Set.BijOn ((complementaryCurveIdeal C).subschemeι.app U.1) (C.ideal U)
      ((Scheme.IdealSheafData.inclusion
          (le_sup_right : complementaryCurveIdeal C ≤ C ⊔ complementaryCurveIdeal C)).ker.ideal
        ⟨(complementaryCurveIdeal C).subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩) :=
  Stacks.ClosedImmersion.bijOn_subschemeι_app_ideal_ker_inclusion
    (inf_complementaryCurveIdeal_eq_bot C) le_sup_left le_sup_right le_rfl U

/-- **[Stacks, Tag 0E34] (2), for the ideal sheaf of `Z`.** On a reduced scheme, the ideal sheaf
of the closure of the complement of a closed subscheme `C` is the direct image of the ideal sheaf
of the intersection `C ⊔ complementaryCurveIdeal C` inside `C`: over every affine open,
restriction to `C` maps it bijectively onto that ideal. -/
theorem bijOn_complementaryCurveIdeal_subscheme [IsReduced X] (C : X.IdealSheafData)
    (U : X.affineOpens) :
    Set.BijOn (C.subschemeι.app U.1) ((complementaryCurveIdeal C).ideal U)
      ((Scheme.IdealSheafData.inclusion
          (le_sup_left : C ≤ C ⊔ complementaryCurveIdeal C)).ker.ideal
        ⟨C.subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩) :=
  Stacks.ClosedImmersion.bijOn_subschemeι_app_ideal_ker_inclusion
    ((inf_comm _ _).trans (inf_complementaryCurveIdeal_eq_bot C)) le_sup_right le_sup_left
    (sup_comm _ _).le U


/-! ### Sheaf Hom out of a closed subscheme into a locally trivial module -/

section SheafHom

variable {Y : Scheme.{u}}

/-- **Evaluation at one.** For a closed immersion `i : Y ⟶ X` and an `𝒪_X`-module `L`, the map
`i_* 𝓗om(𝒪_Y, L) ⟶ L` evaluating a local homomorphism at the section `1`, the counit of the
adjunction of [Stacks, Tag 0A75]. -/
noncomputable abbrev evaluationAtOne (i : Y ⟶ X) [IsClosedImmersion i] (L : X.Modules) :
    (Scheme.Modules.pushforward i).obj
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).sheafHomExactSupport.obj L) ⟶
      L :=
  (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
      i).modulePushforwardSheafHomExactSupportAdjunction.counit.app
    L

/-- A section lies in the image of evaluation at one exactly when it is annihilated, locally, by
the ideal of the closed subscheme. -/
theorem mem_range_evaluationAtOne_iff (i : Y ⟶ X) [IsClosedImmersion i] (L : X.Modules)
    (U : X.Opens) (s : Γ(L, U)) :
    s ∈ Set.range ((evaluationAtOne i L).app U) ↔
      s ∈ (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        i).sectionsLocallyAnnihilatedByKernelIdeal L U := by
  set S := Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i
  constructor
  · rintro ⟨t, rfl⟩
    have hp := (S.sectionsSheafHomExactSupportEquiv L U _ rfl t).prop
    rwa [S.sectionsSheafHomExactSupportEquiv_apply L U _ rfl t] at hp
  · intro hs
    obtain ⟨t, ht⟩ := (S.sectionsSheafHomExactSupportEquiv L U _ rfl).surjective ⟨s, hs⟩
    refine ⟨t, ?_⟩
    have h := S.sectionsSheafHomExactSupportEquiv_apply L U _ rfl t
    rw [ht] at h
    exact h.symm

/-- Evaluation at one is injective on sections. -/
theorem evaluationAtOne_app_injective (i : Y ⟶ X) [IsClosedImmersion i] (L : X.Modules)
    (U : X.Opens) : Function.Injective ((evaluationAtOne i L).app U) := by
  set S := Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i
  intro s t hst
  apply (S.sectionsSheafHomExactSupportEquiv L U _ rfl).injective
  apply Subtype.ext
  rwa [S.sectionsSheafHomExactSupportEquiv_apply L U _ rfl s,
    S.sectionsSheafHomExactSupportEquiv_apply L U _ rfl t]

/-- Evaluation at one `i_* 𝓗om(𝒪_Y, L) ⟶ L` is a monomorphism of `𝒪_X`-modules. -/
instance mono_evaluationAtOne (i : Y ⟶ X) [IsClosedImmersion i] (L : X.Modules) :
    Mono (evaluationAtOne i L) :=
  Scheme.Modules.mono_of_mono_sheafOfModules _
    (SheafOfModules.mono_of_sectionwise_injective _ fun U =>
      evaluationAtOne_app_injective i L U.unop)

end SheafHom

/-! ### The ideal of the closure of the complement times a locally trivial module -/

section IdealMultiple

open Stacks.AlgebraicGeometry.IdealPower Stacks.AlgebraicGeometry.IdealPowerComparison
  Stacks.LocallyTrivial

/-- On a reduced scheme, a function killed by restriction to the closed subscheme cut out by `C`
annihilates every function in the ideal of the closure of the complement of `C`: the first does
not vanish only off `C`, the second only on `C`. -/
theorem mul_eq_zero_of_app_eq_zero_of_mem_complementaryCurveIdeal [IsReduced X]
    (C : X.IdealSheafData) [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    {U : X.Opens} {a : Γ(X, U)} (ha : C.subschemeι.app U a = 0) (V : X.affineOpens)
    (hVU : V.1 ≤ U) {b : Γ(X, V.1)} (hb : b ∈ (complementaryCurveIdeal C).ideal V) :
    X.presheaf.map (homOfLE hVU).op a * b = 0 := by
  refine eq_zero_of_basicOpen_eq_bot _ ?_
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_res]
  ext x
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
    TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨_, hxa⟩ hxb
  have hxC : x ∈ (C.support : Set X) := (mem_complementaryCurveIdeal_ideal_iff C V b).1 hb x hxb
  rw [← C.range_subschemeι] at hxC
  obtain ⟨y, rfl⟩ := hxC
  have : y ∈ C.subschemeι ⁻¹ᵁ X.basicOpen a := hxa
  rwa [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_zero] at this

/-- On a reduced scheme, the subsheaf `𝓙 · L`, for `𝓙` the ideal of the closure of the complement
of `C`, is annihilated by the ideal of `C`. -/
theorem smul_eq_zero_of_mem_idealPowerMultiple_complementaryCurveIdeal [IsReduced X]
    (C : X.IdealSheafData) [QuasiCompact (Scheme.Opens.ι C.support.compl)] (L : X.Modules)
    [L.IsQuasicoherent] (U : X.Opens) (a : Γ(X, U)) (ha : C.subschemeι.app U a = 0)
    (m : Γ(L, U)) (hm : m ∈ (idealPowerMultiple (complementaryCurveIdeal C) 1 L).obj (op U)) :
    a • m = 0 := by
  refine Scheme.Modules.eq_zero_of_locally_affine L (a • m) fun V hVU => ?_
  have hmV : L.presheaf.map (homOfLE hVU).op m ∈ (complementaryCurveIdeal C).ideal V •
      (⊤ : Submodule Γ(X, V.1) Γ(L, V.1)) := by
    rw [← pow_one ((complementaryCurveIdeal C).ideal V),
      ← obj_idealPowerMultiple (complementaryCurveIdeal C) 1 L V]
    exact (idealPowerMultiple (complementaryCurveIdeal C) 1 L).toSubmodule.map
      (homOfLE hVU).op hm
  rw [Scheme.Modules.map_smul]
  refine Submodule.smul_induction_on hmV (fun b hb n _ => ?_) (fun n n' hn hn' => ?_)
  · rw [smul_smul, mul_eq_zero_of_app_eq_zero_of_mem_complementaryCurveIdeal C ha V hVU hb,
      zero_smul]
  · rw [smul_add, hn, hn', add_zero]

/-- **The image of evaluation at one is `𝓙 · L`.** On a reduced scheme, for a closed subscheme cut
out by `C` and a quasi-coherent `L` locally isomorphic to `𝒪_X`, the image of
`i_* 𝓗om(𝒪_C, L) ⟶ L` is the subsheaf `𝓙 · L`, where `𝓙` is the ideal of the closure of the
complement of `C`. Locally `L` is `𝒪_X`, the image is the annihilator of `C` and `𝓙` is that
annihilator (`Stacks.Curves.complementaryCurveIdeal_ideal_eq_annihilator`). -/
theorem rangeSubmodule_evaluationAtOne_eq [IsReduced X] (C : X.IdealSheafData)
    [QuasiCompact (Scheme.Opens.ι C.support.compl)] (L : X.Modules) [L.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible L] :
    Scheme.Modules.rangeSubmodule (evaluationAtOne C.subschemeι L) =
      idealPowerMultiple (complementaryCurveIdeal C) 1 L := by
  refine le_antisymm (submodule_le_of_locallyTrivial _ _ fun T eT W hW => ?_)
    (Stacks.Algebraization.submodule_le_of_affine _ _ fun W => ?_)
  · rintro _ ⟨t₀, rfl⟩
    let t : Γ((Scheme.Modules.pushforward C.subschemeι).obj
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          C.subschemeι).sheafHomExactSupport.obj
        L), W.1) := t₀
    set s := (evaluationAtOne C.subschemeι L).app W.1 t
    rw [obj_idealPowerMultiple, pow_one]
    have key : trivSections eT hW s ∈ (complementaryCurveIdeal C).ideal W := by
      rw [complementaryCurveIdeal_ideal_eq_annihilator, Submodule.mem_annihilator]
      intro a ha
      have ha' : C.subschemeι.app W.1 a = 0 := by
        rwa [← RingHom.mem_ker, C.ker_subschemeι_app W]
      have h1 : a • s = 0 := by
        have h := (Scheme.Modules.Hom.app_smul (evaluationAtOne C.subschemeι L) a t).symm
        rwa [Stacks.Algebraization.pushforward_smul_eq_zero C.subschemeι
          (M := (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
            C.subschemeι).sheafHomExactSupport.obj L) ha' t, map_zero] at h
      rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← LinearEquiv.map_smul, h1, map_zero]
    exact (mem_smul_top_iff eT hW _ s).2 key
  · intro s hs
    exact (mem_range_evaluationAtOne_iff C.subschemeι L W.1 s).2 fun W' hW' a ha =>
        smul_eq_zero_of_mem_idealPowerMultiple_complementaryCurveIdeal C L W' a ha _
        ((idealPowerMultiple (complementaryCurveIdeal C) 1 L).toSubmodule.map
          (homOfLE hW').op hs)

end IdealMultiple


/-! ### The direct image of the dualizing sheaf of a closed subscheme -/

section Dualizing

open Stacks.AlgebraicGeometry.IdealPower

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **`i_*ω_Y = 𝓙ω_X`, for a locally trivial `ω_X`.** Let `X` be a reduced proper scheme of
dimension at most one over a field whose dualizing sheaf `ω_X` is locally isomorphic to `𝒪_X`, and
let `i : Y ⟶ X` be the closed subscheme cut out by `C`. Then the direct image of the dualizing
sheaf of `Y` is the subsheaf `𝓙 ω_X`, for `𝓙` the ideal of the closure of the complement of `Y`:
by [Stacks, Tag 0E33] it is `𝓗om(i_*𝒪_Y, ω_X)`, which evaluation at one identifies with the
sections of `ω_X` annihilated by the ideal of `Y`, and that subsheaf is `𝓙 ω_X`
(`Stacks.Curves.rangeSubmodule_evaluationAtOne_eq`). -/
theorem nonempty_pushforward_dualizingSheafOverField_iso [IsReduced X]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (C : X.IdealSheafData)
    [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    [(Stacks.Duality.dualizingSheafOverField f).IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible
      (Stacks.Duality.dualizingSheafOverField f)] :
    Nonempty ((Scheme.Modules.pushforward C.subschemeι).obj
        (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f)) ≅
      (idealPowerMultiple (complementaryCurveIdeal C) 1
        (Stacks.Duality.dualizingSheafOverField f)).toSheafOfModules) :=
  ⟨(Scheme.Modules.pushforward C.subschemeι).mapIso
      (Stacks.Duality.dualizingSheafOverFieldClosedImmersionIso f C.subschemeι hdim) ≪≫
    Scheme.Modules.rangeSubmoduleIso
      (evaluationAtOne C.subschemeι (Stacks.Duality.dualizingSheafOverField f)) ≪≫
    eqToIso (by
      rw [rangeSubmodule_evaluationAtOne_eq C (Stacks.Duality.dualizingSheafOverField f)])⟩

end Dualizing


/-! ### Two disjoint ideal multiples of a locally trivial module -/

section Disjoint

open Stacks.AlgebraicGeometry.IdealPower Stacks.AlgebraicGeometry.IdealPowerComparison
  Stacks.LocallyTrivial

variable (L : X.Modules) [L.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible L]

/-- The affine opens contained in a trivializing open of `L`. -/
abbrev IsTrivializingAffine (W : X.affineOpens) : Prop :=
  ∃ (T : X.Opens) (_ : L.over T ≅ SheafOfModules.unit (X.ringCatSheaf.over T)), W.1 ≤ T

/-- Over an affine open inside a trivializing open, a section lies in `I L` iff its trivialization
lies in `I`. -/
private theorem mem_idealPowerMultiple_one_iff (M : X.Modules) [M.IsQuasicoherent]
    {T : X.Opens} (eT : M.over T ≅ SheafOfModules.unit (X.ringCatSheaf.over T))
    (I : X.IdealSheafData) (V : X.affineOpens) (hVT : V.1 ≤ T) (s : Γ(M, V.1)) :
    s ∈ (Stacks.Algebraization.idealPowerMultiple I 1 M).obj (op V.1) ↔
      trivSections eT hVT s ∈ I.ideal V := by
  rw [algebraization_idealPowerMultiple_eq, obj_idealPowerMultiple, pow_one]
  exact mem_smul_top_iff eT hVT _ s

/-- **Disjoint ideals have disjoint multiples of a locally trivial module.** If `I ⊓ J = ⊥`, a
section of `L` lying in both `I L` and `J L` is zero: on an affine open where `L ≅ 𝒪_X` it is a
function in `I ∩ J = 0`. -/
theorem eq_zero_of_mem_idealPowerMultiple_of_mem {I J : X.IdealSheafData} (hbot : I ⊓ J = ⊥)
    {U : X.Opens} (s : Γ(L, U))
    (hI : s ∈ (Stacks.Algebraization.idealPowerMultiple I 1 L).obj (op U))
    (hJ : s ∈ (Stacks.Algebraization.idealPowerMultiple J 1 L).obj (op U)) : s = 0 := by
  refine Scheme.Modules.eq_zero_of_locally L (IsTrivializingAffine L)
    (fun x U hx => exists_trivializing_affine x U hx) s ?_
  rintro V ⟨T, eT, hVT⟩ hVU
  have h1 := (Stacks.Algebraization.idealPowerMultiple I 1 L).toSubmodule.map (homOfLE hVU).op hI
  have h2 := (Stacks.Algebraization.idealPowerMultiple J 1 L).toSubmodule.map (homOfLE hVU).op hJ
  have h3 : trivSections eT hVT (L.presheaf.map (homOfLE hVU).op s) ∈ (I ⊓ J).ideal V :=
    ⟨(mem_idealPowerMultiple_one_iff L eT I V hVT _).1 h1,
      (mem_idealPowerMultiple_one_iff L eT J V hVT _).1 h2⟩
  rw [hbot] at h3
  exact (LinearEquiv.map_eq_zero_iff _).1 h3

omit [SheafOfModules.OnSpace.IsInvertible L] in
/-- Over an affine open on which `L` is trivial, a section of `(I ⊔ J) L` is a sum of a section of
`I L` and one of `J L`. -/
theorem mem_sup_of_mem_idealPowerMultiple_sup (I J : X.IdealSheafData) (V : X.affineOpens)
    (hV : IsTrivializingAffine L V) (s : Γ(L, V.1))
    (hs : s ∈ (Stacks.Algebraization.idealPowerMultiple (I ⊔ J) 1 L).obj (op V.1)) :
    ∃ a ∈ (Stacks.Algebraization.idealPowerMultiple I 1 L).obj (op V.1),
      ∃ b ∈ (Stacks.Algebraization.idealPowerMultiple J 1 L).obj (op V.1),
      a + b = s := by
  obtain ⟨T, eT, hVT⟩ := hV
  have hs' := (mem_idealPowerMultiple_one_iff L eT _ V hVT s).1 hs
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hs'
  refine ⟨(trivSections eT hVT).symm a, ?_, (trivSections eT hVT).symm b, ?_, ?_⟩
  · exact (mem_idealPowerMultiple_one_iff L eT _ V hVT _).2
      (by rwa [LinearEquiv.apply_symm_apply])
  · exact (mem_idealPowerMultiple_one_iff L eT _ V hVT _).2
      (by rwa [LinearEquiv.apply_symm_apply])
  · exact ((trivSections eT hVT).symm.map_add a b).symm.trans
      (by rw [hab, LinearEquiv.symm_apply_apply])

open AlgebraicGeometry.SheafOfModules.Submodule in
/-- **`I L` and `J L` meet in zero** when `I ⊓ J = ⊥`: two maps into them with the same composite
into `L` vanish. -/
theorem idealPowerMultiple_disjoint {I J : X.IdealSheafData} (hbot : I ⊓ J = ⊥) {T : X.Modules}
    (x : T ⟶ (Stacks.Algebraization.idealPowerMultiple I 1 L).asModules)
    (y : T ⟶ (Stacks.Algebraization.idealPowerMultiple J 1 L).asModules)
    (h : x ≫ (Stacks.Algebraization.idealPowerMultiple I 1 L).ιModules =
      y ≫ (Stacks.Algebraization.idealPowerMultiple J 1 L).ιModules) :
    x = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext t
  have hxy : ((x ≫ (Stacks.Algebraization.idealPowerMultiple I 1 L).ιModules).app U) t =
      ((y ≫ (Stacks.Algebraization.idealPowerMultiple J 1 L).ιModules).app U) t := by rw [h]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hxy
  have h0 := eq_zero_of_mem_idealPowerMultiple_of_mem L hbot _
    (mem_of_ιModules_app _ U (x.app U t)) (hxy ▸ mem_of_ιModules_app _ U (y.app U t))
  rw [Scheme.Modules.Hom.zero_app]
  exact eq_zero_of_ιModules_app_eq_zero _ U _ h0


/-- The inclusion `I L ⟶ K L` for `I ≤ K`, as a morphism of `𝒪_X`-modules. -/
noncomputable abbrev idealMultipleHomOfLE {I K : X.IdealSheafData} (h : I ≤ K) :
    (Stacks.Algebraization.idealPowerMultiple I 1 L).asModules ⟶
      (Stacks.Algebraization.idealPowerMultiple K 1 L).asModules :=
  SheafOfModules.Submodule.homOfLE ((Stacks.Algebraization.idealPowerMultiple_le_iff I 1 L _).2
    fun U => (Submodule.smul_mono_left
        (pow_le_pow_left' (Scheme.IdealSheafData.le_def.mp h U) 1)).trans
      ((Stacks.Algebraization.idealPowerMultiple_le_iff K 1 L _).1 le_rfl U))

open AlgebraicGeometry.SheafOfModules.Submodule in
/-- **`(I ⊔ J) L` is the sum of `I L` and `J L`**: the map `I L ⊞ J L ⟶ (I ⊔ J) L` is an
epimorphism, being surjective on sections over the trivializing affine opens. -/
theorem epi_desc_idealMultipleHomOfLE (I J : X.IdealSheafData) :
    Epi (biprod.desc (idealMultipleHomOfLE L (le_sup_left : I ≤ I ⊔ J))
      (idealMultipleHomOfLE L (le_sup_right : J ≤ I ⊔ J))) := by
  refine Stacks.FundamentalGroup.epi_of_isLocallySurjective _ fun U t x hx => ?_
  obtain ⟨V, hV, hxV, hVU⟩ := exists_trivializing_affine (L := L) x U hx
  refine ⟨V.1, hVU, hxV, ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_mem_idealPowerMultiple_sup L I J V hV _
    (mem_of_ιModules_app _ V.1
      ((Stacks.Algebraization.idealPowerMultiple (I ⊔ J) 1 L).asModules.presheaf.map
        (homOfLE hVU).op t))
  set eA := idealMultipleHomOfLE L (le_sup_left : I ≤ I ⊔ J)
  set eB := idealMultipleHomOfLE L (le_sup_right : J ≤ I ⊔ J)
  set P := (Stacks.Algebraization.idealPowerMultiple I 1 L).asModules ⊞
    (Stacks.Algebraization.idealPowerMultiple J 1 L).asModules
  refine ⟨(biprod.inl : _ ⟶ P).app V.1 ⟨a, ha⟩ + (biprod.inr : _ ⟶ P).app V.1 ⟨b, hb⟩, ?_⟩
  have h1 : (biprod.desc eA eB).app V.1 ((biprod.inl : _ ⟶ P).app V.1 ⟨a, ha⟩) =
      eA.app V.1 ⟨a, ha⟩ :=
    congrArg (fun φ => φ.app V.1 ⟨a, ha⟩) (biprod.inl_desc eA eB)
  have h2 : (biprod.desc eA eB).app V.1 ((biprod.inr : _ ⟶ P).app V.1 ⟨b, hb⟩) =
      eB.app V.1 ⟨b, hb⟩ :=
    congrArg (fun φ => φ.app V.1 ⟨b, hb⟩) (biprod.inr_desc eA eB)
  refine (map_add _ _ _).trans ?_
  rw [h1, h2]
  exact Subtype.ext hab

open AlgebraicGeometry.SheafOfModules.Submodule in
/-- The data of the abelian exact sequences for `I L`, `J L` and `(I ⊔ J) L` inside `L`. -/
theorem disjointSubobjects_hypotheses {I J : X.IdealSheafData} (hbot : I ⊓ J = ⊥) :
    idealMultipleHomOfLE L (le_sup_left : I ≤ I ⊔ J) ≫
        (Stacks.Algebraization.idealPowerMultiple (I ⊔ J) 1 L).ιModules =
      (Stacks.Algebraization.idealPowerMultiple I 1 L).ιModules ∧
    idealMultipleHomOfLE L (le_sup_right : J ≤ I ⊔ J) ≫
        (Stacks.Algebraization.idealPowerMultiple (I ⊔ J) 1 L).ιModules =
      (Stacks.Algebraization.idealPowerMultiple J 1 L).ιModules ∧
    Epi (biprod.desc (idealMultipleHomOfLE L (le_sup_left : I ≤ I ⊔ J))
      (idealMultipleHomOfLE L (le_sup_right : J ≤ I ⊔ J))) ∧
    ∀ ⦃T : X.Modules⦄ (x : T ⟶ (Stacks.Algebraization.idealPowerMultiple I 1 L).asModules)
      (y : T ⟶ (Stacks.Algebraization.idealPowerMultiple J 1 L).asModules),
      x ≫ (Stacks.Algebraization.idealPowerMultiple I 1 L).ιModules =
        y ≫ (Stacks.Algebraization.idealPowerMultiple J 1 L).ιModules → x = 0 :=
  ⟨SheafOfModules.Submodule.homOfLE_ι _, SheafOfModules.Submodule.homOfLE_ι _,
    epi_desc_idealMultipleHomOfLE L I J,
    fun _ x y h => idealPowerMultiple_disjoint L hbot x y h⟩

open AlgebraicGeometry.SheafOfModules.Submodule in
/-- **[Stacks, Tag 0EL1] at the first power, for the quotient by `K L`**: `L / K L ≅ k_* k^* L`
for the closed immersion `k` of the subscheme cut out by `K`, compatibly with the projection
from `L` and the adjunction unit. -/
noncomputable def quotientIdealMultipleIso (K : X.IdealSheafData) :
    cokernel (Stacks.Algebraization.idealPowerMultiple K 1 L).ιModules ≅
      (Scheme.Modules.pushforward K.subschemeι).obj
        ((Scheme.Modules.pullback K.subschemeι).obj L) :=
  Stacks.Algebraization.idealQuotientPushforwardIso K 1 L K.subschemeι
    (by rw [Scheme.IdealSheafData.ker_subschemeι, pow_one])

omit [SheafOfModules.OnSpace.IsInvertible L] in
open AlgebraicGeometry.SheafOfModules.Submodule in
/-- The identification `L / K L ≅ k_* k^* L` is normalized by the adjunction unit. -/
theorem π_quotientIdealMultipleIso_hom (K : X.IdealSheafData) :
    cokernel.π (Stacks.Algebraization.idealPowerMultiple K 1 L).ιModules ≫
        (quotientIdealMultipleIso L K).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction K.subschemeι).unit.app L :=
  Stacks.Algebraization.idealQuotientPushforwardMap_π K 1 L K.subschemeι
    (by rw [Scheme.IdealSheafData.ker_subschemeι, pow_one])


/-- The kernel of a morphism followed by an isomorphism is the kernel of the morphism. -/
theorem nonempty_kernel_comp_iso_iso {C : Type*} [Category C] [Abelian C] {P Q R : C}
    (g : P ⟶ Q) (e : Q ⟶ R) [IsIso e] : Nonempty (kernel (g ≫ e) ≅ kernel g) :=
  ⟨kernelCompMono g e⟩

/-- **The kernel of the comparison of restrictions.** For closed immersions `a : T ⟶ Y`,
`b : Y ⟶ X` with `a ≫ b = c`, the kernel of the direct image along `b` of the restriction
`b^*M ⟶ a_* a^* b^* M` is the kernel of the comparison `b_* b^* M ⟶ c_* c^* M`. -/
theorem nonempty_kernel_pushforward_unit_iso {T Y : Scheme.{u}} (a : T ⟶ Y) (b : Y ⟶ X)
    {c : T ⟶ X} (hw : a ≫ b = c) (M : X.Modules) :
    Nonempty (kernel ((Scheme.Modules.pushforward b).map
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          ((Scheme.Modules.pullback b).obj M))) ≅
      kernel (Stacks.Algebraization.pushforwardSectionComparison a b hw M)) := by
  set η := (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
    ((Scheme.Modules.pullback b).obj M)
  set e := (Scheme.Modules.pullbackComp a b).hom.app M ≫ (Scheme.Modules.pullbackCongr hw).hom.app M
  set e₂ := (Scheme.Modules.pushforwardComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
      (Scheme.Modules.pushforwardCongr hw).hom.app ((Scheme.Modules.pullback c).obj M)
  have h : Stacks.Algebraization.pushforwardSectionComparison a b hw M =
      (Scheme.Modules.pushforward b).map η ≫
        ((Scheme.Modules.pushforward b).map ((Scheme.Modules.pushforward a).map e) ≫ e₂) := by
    rw [Stacks.Algebraization.pushforwardSectionComparison, Functor.map_comp, Category.assoc]
  rw [h]
  exact (nonempty_kernel_comp_iso_iso _ _).map Iso.symm

omit [SheafOfModules.OnSpace.IsInvertible L] in
open AlgebraicGeometry.SheafOfModules.Submodule in
/-- **The comparison of restrictions is the quotient map.** For `C ≤ K`, under the
identifications `L / C L ≅ i_* i^* L` and `L / K L ≅ k_* k^* L` of [Stacks, Tag 0EL1], the
comparison of restrictions `i_* i^* L ⟶ k_* k^* L` is the map induced by `C L ≤ K L`. -/
theorem quotientIdealMultipleIso_hom_comp_comparison {C K : X.IdealSheafData} (h : C ≤ K) :
    (quotientIdealMultipleIso L C).hom ≫
        Stacks.Algebraization.pushforwardSectionComparison (Scheme.IdealSheafData.inclusion h)
          C.subschemeι (Scheme.IdealSheafData.inclusion_subschemeι h) L =
      CategoryTheory.DisjointSubobjects.quotientMapLeft
          (Stacks.Algebraization.idealPowerMultiple C 1 L).ιModules
          (Stacks.Algebraization.idealPowerMultiple K 1 L).ιModules
          (idealMultipleHomOfLE L h) (SheafOfModules.Submodule.homOfLE_ι _) ≫
        (quotientIdealMultipleIso L K).hom := by
  apply (cancel_epi (cokernel.π (Stacks.Algebraization.idealPowerMultiple C 1 L).ιModules)).mp
  rw [← Category.assoc, π_quotientIdealMultipleIso_hom,
    Stacks.Algebraization.unit_comp_pushforwardSectionComparison, ← Category.assoc,
    cokernel.π_desc, π_quotientIdealMultipleIso_hom]

open AlgebraicGeometry.SheafOfModules.Submodule in
/-- With `C ⊓ J = ⊥`, the multiple `J L` is the kernel of `L / C L ⟶ L / (C ⊔ J) L`. -/
theorem nonempty_idealMultiple_iso_kernel_quotientMapLeft {C J : X.IdealSheafData}
    (hbot : C ⊓ J = ⊥) :
    Nonempty ((Stacks.Algebraization.idealPowerMultiple J 1 L).asModules ≅
      kernel (CategoryTheory.DisjointSubobjects.quotientMapLeft
          (Stacks.Algebraization.idealPowerMultiple C 1 L).ιModules
          (Stacks.Algebraization.idealPowerMultiple (C ⊔ J) 1 L).ιModules
          (idealMultipleHomOfLE L (le_sup_left : C ≤ C ⊔ J))
          (SheafOfModules.Submodule.homOfLE_ι _))) := by
  obtain ⟨hA, hB, hepi, hdisj⟩ := disjointSubobjects_hypotheses L hbot
  have hS := CategoryTheory.DisjointSubobjects.shortExact_quotient _ _ _ _ _ hA hB hepi hdisj
  have := hS.mono_f
  exact ⟨IsLimit.conePointUniqueUpToIso hS.exact.fIsKernel (limit.isLimit _)⟩

/-- **`0 ⟶ L ⟶ L|_I ⊕ L|_J ⟶ L|_K ⟶ 0`.** For ideals with `I ⊓ J = ⊥` and `I ⊔ J = K`, writing
`L|_I` for the direct image of the restriction of `L` to the closed subscheme cut out by `I`,
there is a short exact sequence `0 ⟶ L ⟶ L|_I ⊞ L|_J ⟶ L|_K ⟶ 0`. -/
theorem exists_shortExact_restrictions {I J K : X.IdealSheafData} (hbot : I ⊓ J = ⊥)
    (hK : I ⊔ J = K) :
    ∃ (a : L ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj L) ⊞
        (Scheme.Modules.pushforward J.subschemeι).obj
          ((Scheme.Modules.pullback J.subschemeι).obj L))
      (b : (Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj L) ⊞
        (Scheme.Modules.pushforward J.subschemeι).obj
          ((Scheme.Modules.pullback J.subschemeι).obj L) ⟶
        (Scheme.Modules.pushforward K.subschemeι).obj
          ((Scheme.Modules.pullback K.subschemeι).obj L))
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  subst hK
  obtain ⟨hA, hB, hepi, hdisj⟩ := disjointSubobjects_hypotheses L hbot
  exact (CategoryTheory.DisjointSubobjects.shortExact_lift _ _ _ _ _ hA hB hepi
    hdisj).exists_of_iso (Iso.refl _)
    (biprod.mapIso (quotientIdealMultipleIso L I) (quotientIdealMultipleIso L J)).symm
    (quotientIdealMultipleIso L (I ⊔ J)).symm

/-- **`0 ⟶ I L ⊕ J L ⟶ L ⟶ L|_K ⟶ 0`.** For ideals with `I ⊓ J = ⊥` and `I ⊔ J = K` there is a
short exact sequence `0 ⟶ I L ⊞ J L ⟶ L ⟶ L|_K ⟶ 0`, for `L|_K` the direct image of the
restriction of `L` to the closed subscheme cut out by `K`. -/
theorem exists_shortExact_idealMultiples {I J K : X.IdealSheafData} (hbot : I ⊓ J = ⊥)
    (hK : I ⊔ J = K) :
    ∃ (a : (Stacks.Algebraization.idealPowerMultiple I 1 L).asModules ⊞
          (Stacks.Algebraization.idealPowerMultiple J 1 L).asModules ⟶ L)
      (b : L ⟶ (Scheme.Modules.pushforward K.subschemeι).obj
          ((Scheme.Modules.pullback K.subschemeι).obj L))
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  subst hK
  obtain ⟨hA, hB, hepi, hdisj⟩ := disjointSubobjects_hypotheses L hbot
  exact (CategoryTheory.DisjointSubobjects.shortExact_desc _ _ _ _ _ hA hB hepi
    hdisj).exists_of_iso (Iso.refl _) (Iso.refl _) (quotientIdealMultipleIso L (I ⊔ J)).symm

end Disjoint

/-! ### The intersection of a subcurve with the closure of its complement -/

section Intersection

/-- **The closure of the complement of a closed subscheme is the union of the components it
misses.** On a reduced scheme with Noetherian underlying space, the support of the ideal of the
closure of the complement of `C` is the union of the irreducible components not contained in the
support of `C`. -/
theorem coe_support_complementaryCurveIdeal [IsReduced X] [NoetherianSpace X]
    (C : X.IdealSheafData) :
    ((complementaryCurveIdeal C).support : Set X) =
      Stacks.LiftInvertible.complementaryComponents X (C.support : Set X) := by
  have h := Scheme.Hom.support_ker_eq_closure_range (Scheme.Opens.ι C.support.compl)
  rw [Scheme.Opens.range_ι] at h
  rw [show ((complementaryCurveIdeal C).support : Set X) =
    closure ((C.support : Set X)ᶜ) from congrArg (fun T : Closeds X => (T : Set X)) h]
  refine Set.Subset.antisymm (closure_minimal (fun x hx => ?_)
    (Stacks.LiftInvertible.isClosed_complementaryComponents X _)) ?_
  · exact ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x,
      fun h => hx (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
  · rintro x ⟨D, ⟨hD, hDC⟩, hxD⟩
    obtain ⟨y, hyD, hyC⟩ : ∃ y ∈ D, y ∈ (C.support : Set X)ᶜ := by
      by_contra h
      push Not at h
      exact hDC fun z hz => by simpa using h z hz
    exact closure_mono Set.inter_subset_right
      (subset_closure_inter_of_isPreirreducible_of_isOpen hD.1.2 C.support.isClosed.isOpen_compl
        ⟨y, hyD, hyC⟩ hxD)

/-- **The intersection of a closed subcurve with the closure of its complement is a discrete
space.** On a reduced Noetherian scheme of dimension at most one, the closed subscheme `Y ∩ Z` cut
out by `C ⊔ complementaryCurveIdeal C` has discrete underlying space: its points are the points of
the support of `C` lying on a component not contained in it, finitely many and all closed. -/
theorem discreteTopology_intersectionWithComplementaryCurve [IsReduced X] [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (C : X.IdealSheafData) :
    DiscreteTopology (intersectionWithComplementaryCurveIdeal C).subscheme := by
  set R : Set X := (C.support : Set X)
  have hdisc := Stacks.LiftInvertible.discreteTopology_inter_complementaryComponents X hdim R
    C.support.isClosed
  have hsupp : ((C ⊔ complementaryCurveIdeal C).support : Set X) =
      R ∩ Stacks.LiftInvertible.complementaryComponents X R := by
    rw [Scheme.IdealSheafData.support_sup, Closeds.coe_inf, coe_support_complementaryCurveIdeal]
  set k := (C ⊔ complementaryCurveIdeal C).subschemeι
  have hk : ∀ w, k w ∈ R ∩ Stacks.LiftInvertible.complementaryComponents X R := fun w => by
    rw [← hsupp, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  exact (k.isClosedEmbedding.isEmbedding.codRestrict _ hk).discreteTopology

/-- **An invertible module is trivial on a scheme with discrete underlying space**: its pullback
along any morphism `W ⟶ X` from such a scheme is invertible ([Stacks, Tag 0B8L]), and an
invertible module on a scheme whose points are open is trivial. -/
theorem nonempty_pullback_iso_unit_of_discreteTopology {W : Scheme.{u}} (k : W ⟶ X)
    [DiscreteTopology W] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Nonempty ((Scheme.Modules.pullback k).obj L ≅ SheafOfModules.unit W.ringCatSheaf) :=
  @Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology W _
    ((Scheme.Modules.pullback k).obj L) (Stacks.Divisors.pullback_isInvertible k L)

end Intersection


/-! ### The dualizing sheaf of a closed subscheme of a curve with locally trivial `ω_X` -/

section Subscheme

open Stacks.AlgebraicGeometry.IdealPowerComparison AlgebraicGeometry.SheafOfModules.Submodule

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- A cokernel sequence of a monomorphism is short exact. -/
theorem shortExact_cokernelSequence {C : Type*} [Category C] [Abelian C] {P Q : C} (g : P ⟶ Q)
    [Mono g] : (ShortComplex.cokernelSequence g).ShortExact where
  mono_f := inferInstanceAs (Mono g)
  exact := ShortComplex.cokernelSequence_exact g

/-- The two sectionwise kernels of a morphism of `𝒪_X`-modules in the library agree. -/
theorem algebraization_kernelSubmodule_eq {P Q : X.Modules} (g : P ⟶ Q) :
    Stacks.Algebraization.kernelSubmodule g =
      AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule g :=
  SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U =>
    Stacks.Algebraization.kernelSubmodule_toSubmodule_obj g U)

/-- **`j_*`-form of [Stacks, Tag 0E34] (2) for a locally trivial module: `𝓙 L = i_*(𝓙' i^*L)`.**
Let `L` be a quasi-coherent, locally trivial module on a reduced scheme, `C` a closed subscheme
`i : Y ⟶ X` meeting the closure of its complement (cut out by `𝓙`) in the subscheme cut out by
`K = C ⊔ 𝓙`, with `C ⊓ 𝓙 = ⊥`, and `𝓙'` the ideal of `Y ∩ Z` in `Y`. Then `i_*(𝓙' · i^*L) ≅ 𝓙 · L`:
both are the kernel of the comparison `i_*i^*L ⟶ k_*k^*L` of restrictions. -/
theorem nonempty_pushforward_idealPowerMultiple_ker_iso [IsReduced X] (L : X.Modules)
    [L.IsQuasicoherent] [AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible L]
    (C K : X.IdealSheafData) (hbot : C ⊓ complementaryCurveIdeal C = ⊥)
    (hK : C ⊔ complementaryCurveIdeal C = K) (hCK : C ≤ K) :
    Nonempty ((Scheme.Modules.pushforward C.subschemeι).obj
        (Stacks.Algebraization.idealPowerMultiple (Scheme.IdealSheafData.inclusion hCK).ker 1
          ((Scheme.Modules.pullback C.subschemeι).obj L)).asModules ≅
      (Stacks.Algebraization.idealPowerMultiple (complementaryCurveIdeal C) 1 L).asModules) := by
  subst hK
  set i := C.subschemeι
  set incl := Scheme.IdealSheafData.inclusion hCK
  set M := (Scheme.Modules.pullback i).obj L
  set η := (Scheme.Modules.pullbackPushforwardAdjunction incl).unit.app M
  have e1 : (Stacks.Algebraization.idealPowerMultiple incl.ker 1 M).asModules ≅ kernel η :=
    eqToIso (by rw [← Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealMultiple M incl,
      algebraization_kernelSubmodule_eq]) ≪≫ Stacks.AlgebraicGeometry.kernelSubmoduleIso η
  have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.pushforward i) :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).rightAdjoint_preservesLimits
  obtain ⟨e3⟩ := nonempty_kernel_pushforward_unit_iso incl i
    (Scheme.IdealSheafData.inclusion_subschemeι hCK) L
  have hcomp' : Stacks.Algebraization.pushforwardSectionComparison incl i
      (Scheme.IdealSheafData.inclusion_subschemeι hCK) L =
      (quotientIdealMultipleIso L C).inv ≫ (CategoryTheory.DisjointSubobjects.quotientMapLeft
          (Stacks.Algebraization.idealPowerMultiple C 1 L).ιModules
          (Stacks.Algebraization.idealPowerMultiple (C ⊔ complementaryCurveIdeal C) 1 L).ιModules
          (idealMultipleHomOfLE L hCK) (SheafOfModules.Submodule.homOfLE_ι _) ≫
        (quotientIdealMultipleIso L (C ⊔ complementaryCurveIdeal C)).hom) := by
    rw [← quotientIdealMultipleIso_hom_comp_comparison L hCK, Iso.inv_hom_id_assoc]
  obtain ⟨e5⟩ := nonempty_idealMultiple_iso_kernel_quotientMapLeft L hbot
  have e4 : kernel (Stacks.Algebraization.pushforwardSectionComparison incl i
      (Scheme.IdealSheafData.inclusion_subschemeι hCK) L) ≅
      kernel (CategoryTheory.DisjointSubobjects.quotientMapLeft
          (Stacks.Algebraization.idealPowerMultiple C 1 L).ιModules
          (Stacks.Algebraization.idealPowerMultiple (C ⊔ complementaryCurveIdeal C) 1 L).ιModules
          (idealMultipleHomOfLE L (le_sup_left : C ≤ C ⊔ complementaryCurveIdeal C))
          (SheafOfModules.Submodule.homOfLE_ι _)) :=
    kernelIsoOfEq hcomp' ≪≫ kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _
  exact ⟨(Scheme.Modules.pushforward i).mapIso e1 ≪≫
    PreservesKernel.iso (Scheme.Modules.pushforward i) η ≪≫ e3 ≪≫ e4 ≪≫ e5.symm⟩

/-- **[Stacks, Tag 0E34] (3) and two of the sequences of (5), for a locally trivial `ω_X`.** Let
`X` be a reduced proper scheme of dimension at most one over a field, whose dualizing sheaf `ω_X`
is locally isomorphic to `𝒪_X`, and let `C` cut out a closed subscheme `i : Y ⟶ X` such that the
ideal of the closure of its complement is `D`, with `C ⊓ D = ⊥` and `C ⊔ D = K`, and `ω_X`
restricted to the intersection `K` trivial. Then, with `J'` the ideal of the intersection in `Y`,
1. `ω_Y ≅ J'(i^* ω_X)`;
2. `i_* ω_Y ≅ D ω_X`;
3. there is a short exact sequence `0 ⟶ ω_Y ⟶ i^* ω_X ⟶ 𝒪_{Y ∩ Z} ⟶ 0`;
4. there is a short exact sequence `0 ⟶ i_* ω_Y ⟶ ω_X ⟶ j_* j^* ω_X ⟶ 0`, for `j` the closed
   immersion cut out by `D`. -/
theorem dualizingSheafOverField_subscheme_of_isInvertible [IsReduced X]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (C D K : X.IdealSheafData)
    (hD : complementaryCurveIdeal C = D) (hbot : C ⊓ D = ⊥) (hK : C ⊔ D = K) (hCK : C ≤ K)
    [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    [(Stacks.Duality.dualizingSheafOverField f).IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible
      (Stacks.Duality.dualizingSheafOverField f)]
    (htriv : Nonempty ((Scheme.Modules.pullback K.subschemeι).obj
      (Stacks.Duality.dualizingSheafOverField f) ≅
        SheafOfModules.unit K.subscheme.ringCatSheaf)) :
    Nonempty (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f) ≅
        (Stacks.Algebraization.idealPowerMultiple (Scheme.IdealSheafData.inclusion hCK).ker 1
          ((Scheme.Modules.pullback C.subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField f))).toSheafOfModules) ∧
      Nonempty ((Scheme.Modules.pushforward C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f)) ≅
        (Stacks.Algebraization.idealPowerMultiple D 1
          (Stacks.Duality.dualizingSheafOverField f)).toSheafOfModules) ∧
      (∃ (a : Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f) ⟶
          (Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f))
        (b : (Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f) ⟶
          (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion hCK)).obj
            (SheafOfModules.unit K.subscheme.ringCatSheaf)) (w : a ≫ b = 0),
        (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : (Scheme.Modules.pushforward C.subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f)) ⟶
          Stacks.Duality.dualizingSheafOverField f)
        (b : Stacks.Duality.dualizingSheafOverField f ⟶
          (Scheme.Modules.pushforward D.subschemeι).obj
            ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f)))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) := by
  subst hD hK
  set L := Stacks.Duality.dualizingSheafOverField f
  set i := C.subschemeι
  set incl := Scheme.IdealSheafData.inclusion hCK
  set M := (Scheme.Modules.pullback i).obj L
  -- (3b)
  obtain ⟨e3b⟩ : Nonempty ((Scheme.Modules.pushforward i).obj
      (Stacks.Duality.dualizingSheafOverField (i ≫ f)) ≅
        (Stacks.Algebraization.idealPowerMultiple (complementaryCurveIdeal C) 1 L).asModules) := by
    obtain ⟨e⟩ := nonempty_pushforward_dualizingSheafOverField_iso f hdim C
    exact ⟨e ≪≫ eqToIso (by rw [algebraization_idealPowerMultiple_eq])⟩
  -- (3a)
  obtain ⟨e3a₀⟩ := nonempty_pushforward_idealPowerMultiple_ker_iso L C _ hbot rfl hCK
  have e3a' : Stacks.Duality.dualizingSheafOverField (i ≫ f) ≅
      (Stacks.Algebraization.idealPowerMultiple incl.ker 1 M).asModules :=
    ((Stacks.ClosedImmersion.fullyFaithfulPushforward i).preimageIso (e3a₀ ≪≫ e3b.symm)).symm
  refine ⟨⟨e3a'⟩, ⟨e3b ≪≫ eqToIso rfl⟩, ?_, ?_⟩
  · -- the sequence on `Y`
    obtain ⟨et⟩ := htriv
    have eq : cokernel (Stacks.Algebraization.idealPowerMultiple incl.ker 1 M).ιModules ≅
        (Scheme.Modules.pushforward incl).obj (SheafOfModules.unit
          (C ⊔ complementaryCurveIdeal C).subscheme.ringCatSheaf) :=
      Stacks.Algebraization.idealQuotientPushforwardIso incl.ker 1 M incl (pow_one _).symm ≪≫
        (Scheme.Modules.pushforward incl).mapIso
          ((Scheme.Modules.pullbackComp incl i).app L ≪≫
            (Scheme.Modules.pullbackCongr (Scheme.IdealSheafData.inclusion_subschemeι hCK)).app L ≪≫
            et)
    exact (shortExact_cokernelSequence
      (Stacks.Algebraization.idealPowerMultiple incl.ker 1 M).ιModules).exists_of_iso
      e3a' (Iso.refl _) eq.symm
  · -- the sequence `0 ⟶ i_* ω_Y ⟶ ω_X ⟶ j_* j^* ω_X ⟶ 0`
    exact (shortExact_cokernelSequence
      (Stacks.Algebraization.idealPowerMultiple (complementaryCurveIdeal C) 1
        L).ιModules).exists_of_iso
      e3b (Iso.refl _) (quotientIdealMultipleIso L (complementaryCurveIdeal C)).symm

end Subscheme

/-! ### The full statement for an invertible `ω_X` -/

section Invertible

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **[Stacks, Tag 0E34] for an invertible `ω_X`.** Let `X` be a reduced proper scheme over a
field, equidimensional of dimension one, whose dualizing sheaf `ω_X` is invertible. Let `C` cut out
a reduced closed subscheme `i : Y ⟶ X` equidimensional of dimension one, let `j : Z ⟶ X` be the
scheme-theoretic closure of `X \ Y`, cut out by `𝓙 = complementaryCurveIdeal C`, and let `Y ∩ Z`
be cut out by `𝓘 ⊔ 𝓙` (`intersectionWithComplementaryCurveIdeal C`). With `𝓘'` and `𝓙'` the ideals
of `Y ∩ Z` in `Z` and in `Y`:
1. `Y` and `Z` are Cohen–Macaulay;
2. `𝓘 = j_*𝓘'` and `𝓙 = i_*𝓙'`, read on affine opens;
3. `ω_Y ≅ 𝓙'(i^*ω_X)` and `i_*ω_Y ≅ 𝓙ω_X`;
4. `ω_Z ≅ 𝓘'(j^*ω_X)` and `j_*ω_Z ≅ 𝓘ω_X`;
5. there are short exact sequences
   `0 ⟶ ω_X ⟶ i_*i^*ω_X ⊕ j_*j^*ω_X ⟶ 𝒪_{Y ∩ Z} ⟶ 0`,
   `0 ⟶ i_*ω_Y ⟶ ω_X ⟶ j_*j^*ω_X ⟶ 0`,
   `0 ⟶ j_*ω_Z ⟶ ω_X ⟶ i_*i^*ω_X ⟶ 0`,
   `0 ⟶ i_*ω_Y ⊕ j_*ω_Z ⟶ ω_X ⟶ 𝒪_{Y ∩ Z} ⟶ 0`,
   `0 ⟶ ω_Y ⟶ i^*ω_X ⟶ 𝒪_{Y ∩ Z} ⟶ 0`,
   `0 ⟶ ω_Z ⟶ j^*ω_X ⟶ 𝒪_{Y ∩ Z} ⟶ 0`,
   where `𝒪_{Y ∩ Z}` denotes the direct image of the structure sheaf of `Y ∩ Z` on whichever
   of `X`, `Y`, `Z` the sequence lives.

The restriction of `ω_X` to `Y ∩ Z` is trivial since `Y ∩ Z` is a finite discrete scheme
(`Stacks.Curves.discreteTopology_intersectionWithComplementaryCurve`). -/
theorem dualizingSheafOverField_closedSubcurve_of_isInvertible [IsReduced X]
    (hXeq : TopologicalSpace.Equidimensional X) (hXdim : topologicalKrullDim X = 1)
    (C : X.IdealSheafData) [IsReduced C.subscheme]
    (hYeq : TopologicalSpace.Equidimensional C.subscheme)
    (hYdim : topologicalKrullDim C.subscheme = 1)
    [hω : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f)] :
    -- (1)
    (IsCohenMacaulay C.subscheme ∧ IsCohenMacaulay (complementaryCurve C)) ∧
    -- (2)
    (∀ U : X.affineOpens,
      Set.BijOn ((complementaryCurveIdeal C).subschemeι.app U.1) (C.ideal U)
        ((Scheme.IdealSheafData.inclusion
            (le_sup_right : complementaryCurveIdeal C ≤
              intersectionWithComplementaryCurveIdeal C)).ker.ideal
          ⟨(complementaryCurveIdeal C).subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩) ∧
      Set.BijOn (C.subschemeι.app U.1) ((complementaryCurveIdeal C).ideal U)
        ((Scheme.IdealSheafData.inclusion
            (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).ker.ideal
          ⟨C.subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩)) ∧
    -- (3)
    (Nonempty (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f) ≅
        (Stacks.Algebraization.idealPowerMultiple
          (Scheme.IdealSheafData.inclusion
            (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).ker 1
          ((Scheme.Modules.pullback C.subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField f))).toSheafOfModules) ∧
      Nonempty ((Scheme.Modules.pushforward C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f)) ≅
        (Stacks.Algebraization.idealPowerMultiple (complementaryCurveIdeal C) 1
          (Stacks.Duality.dualizingSheafOverField f)).toSheafOfModules)) ∧
    -- (4)
    (Nonempty (Stacks.Duality.dualizingSheafOverField
          ((complementaryCurveIdeal C).subschemeι ≫ f) ≅
        (Stacks.Algebraization.idealPowerMultiple
          (Scheme.IdealSheafData.inclusion
            (le_sup_right : complementaryCurveIdeal C ≤
              intersectionWithComplementaryCurveIdeal C)).ker 1
          ((Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField f))).toSheafOfModules) ∧
      Nonempty ((Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField ((complementaryCurveIdeal C).subschemeι ≫ f)) ≅
        (Stacks.Algebraization.idealPowerMultiple C 1
          (Stacks.Duality.dualizingSheafOverField f)).toSheafOfModules)) ∧
    -- (5)
    ((∃ (a : Stacks.Duality.dualizingSheafOverField f ⟶
          (Scheme.Modules.pushforward C.subschemeι).obj
            ((Scheme.Modules.pullback C.subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)) ⊞
          (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            ((Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)))
        (b : (Scheme.Modules.pushforward C.subschemeι).obj
            ((Scheme.Modules.pullback C.subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)) ⊞
          (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            ((Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)) ⟶
          (Scheme.Modules.pushforward (intersectionWithComplementaryCurveIdeal C).subschemeι).obj
            (SheafOfModules.unit (intersectionWithComplementaryCurve C).ringCatSheaf))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : (Scheme.Modules.pushforward C.subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f)) ⟶
            Stacks.Duality.dualizingSheafOverField f)
        (b : Stacks.Duality.dualizingSheafOverField f ⟶
          (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            ((Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField ((complementaryCurveIdeal C).subschemeι ≫ f)) ⟶
            Stacks.Duality.dualizingSheafOverField f)
        (b : Stacks.Duality.dualizingSheafOverField f ⟶
          (Scheme.Modules.pushforward C.subschemeι).obj
            ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f)))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : (Scheme.Modules.pushforward C.subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f)) ⊞
          (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField ((complementaryCurveIdeal C).subschemeι ≫ f)) ⟶
            Stacks.Duality.dualizingSheafOverField f)
        (b : Stacks.Duality.dualizingSheafOverField f ⟶
          (Scheme.Modules.pushforward (intersectionWithComplementaryCurveIdeal C).subschemeι).obj
            (SheafOfModules.unit (intersectionWithComplementaryCurve C).ringCatSheaf))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f) ⟶
          (Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f))
        (b : (Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f) ⟶
          (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
            (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C))).obj
            (SheafOfModules.unit (intersectionWithComplementaryCurve C).ringCatSheaf))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : Stacks.Duality.dualizingSheafOverField
            ((complementaryCurveIdeal C).subschemeι ≫ f) ⟶
          (Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField f))
        (b : (Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField f) ⟶
          (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
            (le_sup_right : complementaryCurveIdeal C ≤
              intersectionWithComplementaryCurveIdeal C))).obj
            (SheafOfModules.unit (intersectionWithComplementaryCurve C).ringCatSheaf))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact)) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType f)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  have hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞) := hXdim.le
  have hDD : complementaryCurveIdeal (complementaryCurveIdeal C) = C :=
    complementaryCurveIdeal_complementaryCurveIdeal (k := k) hXeq hXdim C hYeq hYdim
  have hbot : C ⊓ complementaryCurveIdeal C = ⊥ := inf_complementaryCurveIdeal_eq_bot C
  have hbot' : complementaryCurveIdeal C ⊓ C = ⊥ := (inf_comm _ _).trans hbot
  have : (Stacks.Duality.dualizingSheafOverField f).IsQuasicoherent :=
    Stacks.Duality.isQuasicoherent_dualizingSheafOverField f
  have hω' : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Duality.dualizingSheafOverField f) := hω
  have : AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible
      (Stacks.Duality.dualizingSheafOverField f) :=
    Stacks.LocallyTrivial.onSpace_isInvertible_of_isInvertible _
  have := discreteTopology_intersectionWithComplementaryCurve hdim C
  obtain ⟨et⟩ := nonempty_pullback_iso_unit_of_discreteTopology
    (intersectionWithComplementaryCurveIdeal C).subschemeι
    (Stacks.Duality.dualizingSheafOverField f)
  obtain ⟨⟨e3a⟩, ⟨e3b⟩, hY, h2⟩ := dualizingSheafOverField_subscheme_of_isInvertible f hdim C
    (complementaryCurveIdeal C) (intersectionWithComplementaryCurveIdeal C) rfl hbot rfl
    le_sup_left ⟨et⟩
  obtain ⟨⟨e4a⟩, ⟨e4b⟩, hZ, h3⟩ := dualizingSheafOverField_subscheme_of_isInvertible f hdim
    (complementaryCurveIdeal C) C (intersectionWithComplementaryCurveIdeal C) hDD hbot'
    (sup_comm _ _) le_sup_right ⟨et⟩
  have e₃ :=
    (Scheme.Modules.pushforward (intersectionWithComplementaryCurveIdeal C).subschemeι).mapIso et
  refine ⟨⟨isCohenMacaulay_subscheme hdim C, isCohenMacaulay_complementaryCurve hdim C⟩,
    fun U => ⟨bijOn_ideal_complementaryCurve C U, bijOn_complementaryCurveIdeal_subscheme C U⟩,
    ⟨⟨e3a⟩, ⟨e3b⟩⟩, ⟨⟨e4a⟩, ⟨e4b⟩⟩, ?_, h2, h3, ?_, hY, hZ⟩
  · obtain ⟨_, _, _, h⟩ :=
      exists_shortExact_restrictions (Stacks.Duality.dualizingSheafOverField f) hbot rfl
    exact h.exists_of_iso (Iso.refl _) (Iso.refl _) e₃.symm
  · obtain ⟨_, _, _, h⟩ :=
      exists_shortExact_idealMultiples (Stacks.Duality.dualizingSheafOverField f) hbot'
        (sup_comm _ _)
    exact h.exists_of_iso (biprod.mapIso e3b e4b) (Iso.refl _) e₃.symm

/-- **Stacks Project, Tag 0E34.** Let `X` be a proper scheme over a field which is Gorenstein,
reduced, and equidimensional of dimension one. Let `C` cut out a reduced closed subscheme
`i : Y ⟶ X` equidimensional of dimension one, let `j : Z ⟶ X` be the scheme-theoretic closure of
`X \ Y`, cut out by `𝓙 = complementaryCurveIdeal C`, and let `Y ∩ Z` be cut out by `𝓘 ⊔ 𝓙`. With
`𝓘'` and `𝓙'` the ideals of `Y ∩ Z` in `Z` and in `Y`:
1. `Y` and `Z` are Cohen–Macaulay;
2. `𝓘 = j_*𝓘'` and `𝓙 = i_*𝓙'`, read on affine opens;
3. `ω_Y ≅ 𝓙'(i^*ω_X)` and `i_*ω_Y ≅ 𝓙ω_X`;
4. `ω_Z ≅ 𝓘'(j^*ω_X)` and `j_*ω_Z ≅ 𝓘ω_X`;
5. the six short exact sequences of
   `Stacks.Curves.dualizingSheafOverField_closedSubcurve_of_isInvertible`.

Since `X` is Gorenstein and its closed points have one-dimensional local rings, `ω_X` is
invertible (`AlgebraicGeometry.isInvertible_dualizingSheafOverField`), and the statement is
`Stacks.Curves.dualizingSheafOverField_closedSubcurve_of_isInvertible`. -/
@[stacks 0E34 "in (2) and (4) the source swaps the roles of i and j: the forms stated are
I = j_* I', J = i_* J', omega_Z = I'(j^* omega_X) and j_* omega_Z = I omega_X"]
theorem dualizingSheafOverField_closedSubcurve [IsReduced X] [IsGorenstein X]
    (hXeq : TopologicalSpace.Equidimensional X) (hXdim : topologicalKrullDim X = 1)
    (C : X.IdealSheafData) [IsReduced C.subscheme]
    (hYeq : TopologicalSpace.Equidimensional C.subscheme)
    (hYdim : topologicalKrullDim C.subscheme = 1) :
    -- (1)
    (IsCohenMacaulay C.subscheme ∧ IsCohenMacaulay (complementaryCurve C)) ∧
    -- (2)
    (∀ U : X.affineOpens,
      Set.BijOn ((complementaryCurveIdeal C).subschemeι.app U.1) (C.ideal U)
        ((Scheme.IdealSheafData.inclusion
            (le_sup_right : complementaryCurveIdeal C ≤
              intersectionWithComplementaryCurveIdeal C)).ker.ideal
          ⟨(complementaryCurveIdeal C).subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩) ∧
      Set.BijOn (C.subschemeι.app U.1) ((complementaryCurveIdeal C).ideal U)
        ((Scheme.IdealSheafData.inclusion
            (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).ker.ideal
          ⟨C.subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩)) ∧
    -- (3)
    (Nonempty (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f) ≅
        (Stacks.Algebraization.idealPowerMultiple
          (Scheme.IdealSheafData.inclusion
            (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).ker 1
          ((Scheme.Modules.pullback C.subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField f))).toSheafOfModules) ∧
      Nonempty ((Scheme.Modules.pushforward C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f)) ≅
        (Stacks.Algebraization.idealPowerMultiple (complementaryCurveIdeal C) 1
          (Stacks.Duality.dualizingSheafOverField f)).toSheafOfModules)) ∧
    -- (4)
    (Nonempty (Stacks.Duality.dualizingSheafOverField
          ((complementaryCurveIdeal C).subschemeι ≫ f) ≅
        (Stacks.Algebraization.idealPowerMultiple
          (Scheme.IdealSheafData.inclusion
            (le_sup_right : complementaryCurveIdeal C ≤
              intersectionWithComplementaryCurveIdeal C)).ker 1
          ((Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField f))).toSheafOfModules) ∧
      Nonempty ((Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField ((complementaryCurveIdeal C).subschemeι ≫ f)) ≅
        (Stacks.Algebraization.idealPowerMultiple C 1
          (Stacks.Duality.dualizingSheafOverField f)).toSheafOfModules)) ∧
    -- (5)
    ((∃ (a : Stacks.Duality.dualizingSheafOverField f ⟶
          (Scheme.Modules.pushforward C.subschemeι).obj
            ((Scheme.Modules.pullback C.subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)) ⊞
          (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            ((Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)))
        (b : (Scheme.Modules.pushforward C.subschemeι).obj
            ((Scheme.Modules.pullback C.subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)) ⊞
          (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            ((Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)) ⟶
          (Scheme.Modules.pushforward (intersectionWithComplementaryCurveIdeal C).subschemeι).obj
            (SheafOfModules.unit (intersectionWithComplementaryCurve C).ringCatSheaf))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : (Scheme.Modules.pushforward C.subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f)) ⟶
            Stacks.Duality.dualizingSheafOverField f)
        (b : Stacks.Duality.dualizingSheafOverField f ⟶
          (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            ((Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
              (Stacks.Duality.dualizingSheafOverField f)))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField ((complementaryCurveIdeal C).subschemeι ≫ f)) ⟶
            Stacks.Duality.dualizingSheafOverField f)
        (b : Stacks.Duality.dualizingSheafOverField f ⟶
          (Scheme.Modules.pushforward C.subschemeι).obj
            ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f)))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : (Scheme.Modules.pushforward C.subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f)) ⊞
          (Scheme.Modules.pushforward (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField ((complementaryCurveIdeal C).subschemeι ≫ f)) ⟶
            Stacks.Duality.dualizingSheafOverField f)
        (b : Stacks.Duality.dualizingSheafOverField f ⟶
          (Scheme.Modules.pushforward (intersectionWithComplementaryCurveIdeal C).subschemeι).obj
            (SheafOfModules.unit (intersectionWithComplementaryCurve C).ringCatSheaf))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ f) ⟶
          (Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f))
        (b : (Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f) ⟶
          (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
            (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C))).obj
            (SheafOfModules.unit (intersectionWithComplementaryCurve C).ringCatSheaf))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) ∧
      (∃ (a : Stacks.Duality.dualizingSheafOverField
            ((complementaryCurveIdeal C).subschemeι ≫ f) ⟶
          (Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField f))
        (b : (Scheme.Modules.pullback (complementaryCurveIdeal C).subschemeι).obj
            (Stacks.Duality.dualizingSheafOverField f) ⟶
          (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
            (le_sup_right : complementaryCurveIdeal C ≤
              intersectionWithComplementaryCurveIdeal C))).obj
            (SheafOfModules.unit (intersectionWithComplementaryCurve C).ringCatSheaf))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact)) := by
  have : LocallyOfFiniteType f := inferInstance
  have := AlgebraicGeometry.isInvertible_dualizingSheafOverField k f hXdim.le
    fun x hx => ringKrullDim_stalk_eq_one_of_equidimensional k f hXeq hXdim x hx
  exact dualizingSheafOverField_closedSubcurve_of_isInvertible f hXeq hXdim C hYeq hYdim

end Invertible

end Stacks.Curves
