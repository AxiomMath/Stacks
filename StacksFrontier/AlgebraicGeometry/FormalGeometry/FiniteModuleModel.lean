module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictSupported
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.FiniteModule
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Finite module models of coherent adic systems on the open complement

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X \ V(𝔞)`. An inverse system `(M_n)` of `A`-modules
is a *finite module model* when every `M_n` is a finite `A`-module annihilated by `Iⁿ` and the
canonical map `M_{n+1}/Iⁿ M_{n+1} → M_n` has `𝔞`-power torsion kernel and cokernel. The systems
`(M_n^~|_U)` obtained this way are exactly the coherent `I`-adic systems on `U`.

## Main definitions

* `Stacks.Algebraization.restrictedTildeSystem` — the system `(M_n^~|_U)`.
* `Stacks.Algebraization.IsFiniteModuleModel` — the three conditions of Stacks 0DXT.
* `Stacks.Algebraization.coherentAdicSystemOfFiniteModuleModel` — `(M_n^~|_U)` as an object of
  `Coh(U, I 𝒪_U)`.

## Main results

* `Stacks.Algebraization.restrictedTildeSystem_isCoherentAdicSystem` — the forward implication of
  Stacks 0DXT.
* `Stacks.Algebraization.exists_finiteModuleModel` — its converse.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and zero-indexed: term `n` is the source's `M_{n+1}`. Both
conditions (2) and (3) carry the same shift, so they stay aligned.

Condition (3) is phrased as the existence of a map `M_{n+1}/I^{n+1} M_{n+1} → M_n` factoring the
transition map of the system, with `𝔞`-power torsion kernel and cokernel. Since the quotient
projection is surjective, that map is unique, so this says exactly that the *induced* map has
torsion kernel and cokernel — the factorisation condition is what ties the statement to the
system's own transitions rather than to some unrelated map of quotients.

The converse produces the model as an inverse system, not merely termwise: the isomorphism is an
isomorphism in `Coh(U, I 𝒪_U)`, hence a natural isomorphism commuting with every transition map.
It is built by recursion, each stage extending a coherent module on `U` together with its map to
the previous stage, and then quotienting to force the annihilation condition.

The crux is `restrictedTilde_map_isIso_iff`: for a map of `A`-modules, the restricted tilde
functor sends it to an isomorphism exactly when its kernel and cokernel are `𝔞`-power torsion.
That is what turns condition (3) into the quotient-transition clause of a coherent adic system
and back.

## References

* [The Stacks Project, Lemma 52.11.1 (0DXT)](https://stacks.math.columbia.edu/tag/0DXT)
* [The Stacks Project, Situation 52.11.0 (0EHC)](https://stacks.math.columbia.edu/tag/0EHC)
* [The Stacks Project, Lemma 51.8.2 (0BK0)](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

variable (S : Stacks.Algebraization.AlgebraizationSituation.{u})

/-- The inverse system of sheaves obtained by sheafifying finite modules and
restricting to `U`. -/
public def restrictedTildeSystem
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) : ℕᵒᵖ ⥤ S.U.toScheme.Modules :=
  M ⋙ tilde.functor (CommRingCat.of S.A) ⋙ Scheme.Modules.pullback S.U.ι

/-- The source's three conditions on a system of finite modules. The final
condition uses the actual reduction of the transition map. -/
public def IsFiniteModuleModel (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) : Prop :=
  (∀ n : ℕ, Module.Finite S.A (M.obj (op n))) ∧
  (∀ n : ℕ, S.I ^ (n + 1) • (⊤ : Submodule S.A (M.obj (op n))) = ⊥) ∧
  (∀ n : ℕ,
    let N := M.obj (op (n + 1))
    let P := S.I ^ (n + 1) • (⊤ : Submodule S.A N)
    ∃ f : (N ⧸ P) →ₗ[S.A] M.obj (op n),
      (f.comp P.mkQ = (M.map (homOfLE (Nat.le_succ n)).op).hom) ∧
      IsIPowerTorsion S.A (LinearMap.ker f) S.a ∧
      IsIPowerTorsion S.A ((M.obj (op n)) ⧸ LinearMap.range f) S.a)

private theorem isCompact_open : IsCompact (S.U : Set S.X) :=
  (TopologicalSpace.noetherianSpace_iff_opens S.X).mp inferInstance S.U

private theorem exists_finite_extension_of_term
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S)) (n : ℕ) :
    ∃ M : ModuleCat.{u} S.A, Module.Finite S.A M ∧
      Nonempty (((tilde.functor (CommRingCat.of S.A)).obj M).restrict S.U.ι ≅
        F.obj.obj (op n)) := by
  have hc : (F.obj.obj (op n)).IsCoherent := F.property.1 n
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (F.obj.obj (op n))
  exact AlgebraicGeometry.exists_finiteModule_tilde_restrict (A := CommRingCat.of S.A) S.U
    (isCompact_open S) (F.obj.obj (op n))

-- Converting the restricted pullback to the local finite-presentation criterion
-- for coherence requires more reduction than the default heartbeat budget.
private theorem finite_module_restricted_tilde_isCoherent (M : ModuleCat.{u} S.A)
    (hM : Module.Finite S.A M) :
    ((Scheme.Modules.pullback S.U.ι).obj
      ((tilde.functor (CommRingCat.of S.A)).obj M)).IsCoherent := by
  let F := (tilde.functor (CommRingCat.of S.A)).obj M
  let : Module.Finite S.A M := hM
  have hfp : F.IsFinitePresentation :=
    (AlgebraicGeometry.tilde_isFinitePresentation_iff (ModuleCat.of (CommRingCat.of S.A) M)).2
      (Module.finitePresentation_of_finite (CommRingCat.of S.A)
        (ModuleCat.of (CommRingCat.of S.A) M))
  have hfpPull : ((Scheme.Modules.pullback S.U.ι).obj F).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      S.U.ι.toLRSHom.toShHom F hfp
  let : IsLocallyNoetherian S.U.toScheme := inferInstance
  exact ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae S.U.toScheme
    ((Scheme.Modules.pullback S.U.ι).obj F)).out 3 1).mp hfpPull

private theorem torsion_tilde_stalk_subsingleton {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (x : PrimeSpectrum.Top R)
    (h : ¬ Nontrivial (LocalizedModule x.asIdeal.primeCompl M)) :
    Subsingleton ((tilde M).presheaf.stalk x) := by
  have : Subsingleton (LocalizedModule x.asIdeal.primeCompl M) :=
    not_nontrivial_iff_subsingleton.mp h
  let e := IsLocalizedModule.iso x.asIdeal.primeCompl (tilde.toStalk M x).hom
  exact ⟨fun s t => e.symm.injective (Subsingleton.elim _ _)⟩

private theorem iPowerTorsion_tilde_restrict_isZero
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : ModuleCat.{u} R) (hM : IsIPowerTorsion R M I) :
    IsZero (((tilde.functor (CommRingCat.of R)).obj M).restrict
      (Stacks.LocalCohomology.complementZeroLocus R I).ι) := by
  let V := Stacks.LocalCohomology.complementZeroLocus R I
  let G := ((tilde.functor (CommRingCat.of R)).obj M).restrict V.ι
  have hstalk (x : V) : Subsingleton (G.presheaf.stalk x) := by
    have hxI : ¬ I ≤ x.1.asIdeal := by
      have hxout : (x.1 : PrimeSpectrum R) ∉ PrimeSpectrum.zeroLocus (I : Set R) := by
        show (x.1 : PrimeSpectrum R) ∈ (PrimeSpectrum.zeroLocus (I : Set R))ᶜ
        exact x.2
      intro hle
      exact hxout ((PrimeSpectrum.mem_zeroLocus x.1 (I : Set R)).mpr hle)
    have hloc := (isIPowerTorsion_iff_localization_eq_zero R M I hI).mp hM
      x.1 hxI
    have hsub := torsion_tilde_stalk_subsingleton M x.1 hloc
    let e := (Scheme.Modules.restrictStalkNatIso V.ι x).app
      ((tilde.functor (CommRingCat.of R)).obj M)
    exact (AddCommGrpCat.isZero_iff_subsingleton.mp
      (IsZero.of_iso (AddCommGrpCat.isZero_iff_subsingleton.mpr hsub) e))
  let Gsheaf : TopCat.Sheaf Ab (TopCat.of V) := ⟨G.presheaf, G.isSheaf⟩
  have hGsheaf : IsZero Gsheaf := by
    rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
    intro x
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr (hstalk x)
  have hGpresheaf : IsZero G.presheaf :=
    Functor.map_isZero (TopCat.Sheaf.forget Ab (TopCat.of V)) hGsheaf
  apply (IsZero.iff_id_eq_zero G).mpr
  apply Functor.map_injective (Scheme.Modules.toPresheaf V)
  simp only [Functor.map_zero]
  exact (IsZero.iff_id_eq_zero G.presheaf).mp hGpresheaf

private lemma localized_subsingleton_of_tilde_stalk {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (p : PrimeSpectrum.Top R)
    (h : Subsingleton ((tilde M).presheaf.stalk p)) :
    Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  let e := IsLocalizedModule.iso p.asIdeal.primeCompl (tilde.toStalk M p).hom
  exact ⟨fun s t ↦ e.injective (@Subsingleton.elim _ h _ _)⟩

private theorem isIPowerTorsion_of_restrict_tilde_isZero
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : ModuleCat.{u} R)
    (hM : IsZero ((tilde (R := CommRingCat.of R) M).restrict
      (Stacks.LocalCohomology.complementZeroLocus R I).ι)) : IsIPowerTorsion R M I := by
  rw [isIPowerTorsion_iff_localization_eq_zero R M I hI]
  intro p hp hnt
  let V := Stacks.LocalCohomology.complementZeroLocus R I
  let x : V := ⟨p, hp⟩
  have : (Scheme.Modules.toPresheaf V).PreservesZeroMorphisms := ⟨by intros; rfl⟩
  have hzero := Functor.map_isZero (TopCat.Presheaf.stalkFunctor Ab.{u} x)
    (Functor.map_isZero (Scheme.Modules.toPresheaf V) hM)
  let e := (Scheme.Modules.restrictStalkNatIso V.ι x).app (tilde (R := CommRingCat.of R) M)
  have hs : Subsingleton ((tilde (R := CommRingCat.of R) M).presheaf.stalk p) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp (hzero.of_iso e.symm)
  exact @not_subsingleton _ hnt (localized_subsingleton_of_tilde_stalk (R := .of R) M p hs)

section

open scoped AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-- The sections of the zero subsheaf vanish, with the ambient module ascribed at `X.Modules`.

`SheafOfModules.Submodule.bot_obj` is stated for the generic `SheafOfModules R`; instance
search does not see that `X.ringCatSheaf` is a sheaf for `Opens.grothendieckTopology X`, so the
rewrite only fires at this spelling. -/
private alias bot_obj_modules := Stacks.Algebraization.bot_obj_schemeModules

/-- Comparison of subsheaves is comparison of their sections, at the `X.Modules` spelling. -/
private lemma le_iff_modules {X : Scheme.{u}} {M : X.Modules} {P Q : M.Submodule} :
    P ≤ Q ↔ ∀ U : X.Opensᵒᵖ, P.obj U ≤ Q.obj U :=
  Iff.rfl

private lemma idealPowerMultiple_eq_bot_iff {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) :
    Stacks.Algebraization.idealPowerMultiple I n M = ⊥ ↔
      ∀ U : X.affineOpens, I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) = ⊥ := by
  rw [← le_bot_iff, Stacks.Algebraization.idealPowerMultiple_le_iff]
  refine forall_congr' fun U => ?_
  rw [bot_obj_modules]
  exact le_bot_iff

/-- A morphism of modules on a scheme, on sections over `U`, as a linear map with the ring and
both modules at the `Γ(·, U)` spelling.

`f.val.app (op U)` has `M.val.obj (op U)` for the type of its source, and at that spelling
instance search finds neither the `Module Γ(X, U)` action nor anything built from it. Being a
definition, the ascription here is checked at default transparency and so is accepted; every
lemma below about sections is stated through it. -/
private def appHom {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  (f.val.app (op U)).hom

private lemma appHom_comp {X : Scheme.{u}} {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (U : X.Opens) (x : Γ(M, U)) : appHom (f ≫ g) U x = appHom g U (appHom f U x) :=
  rfl

private lemma appHom_inv_hom {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (x : Γ(N, U)) : appHom e.hom U (appHom e.inv U x) = x := by
  rw [← appHom_comp, e.inv_hom_id]
  rfl

/-- Membership in the sections of the sectionwise kernel, at the `Γ(·, U)` spelling.

`Stacks.Algebraization.kernelSubmodule_toSubmodule_obj` identifies those sections with a
`LinearMap.ker`, but over the ring `X.ringCatSheaf.obj.obj (op U)`, at which no lemma about
`Submodule Γ(X, U) Γ(M, U)` applies. -/
private lemma mem_kernelSubmodule_obj {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    {U : X.Opens} (x : Γ(M, U)) :
    x ∈ ((Stacks.Algebraization.kernelSubmodule f).toSubmodule.obj (op U) :
      Submodule Γ(X, U) Γ(M, U)) ↔ appHom f U x = 0 := by
  rw [show ((Stacks.Algebraization.kernelSubmodule f).toSubmodule.obj (op U) :
      Submodule Γ(X, U) Γ(M, U)) = (appHom f U).ker from
    Stacks.Algebraization.kernelSubmodule_toSubmodule_obj f (op U)]
  exact LinearMap.mem_ker

private lemma idealOnOpen_ideal (S : Stacks.Algebraization.AlgebraizationSituation.{u})
    (U : S.U.toScheme.affineOpens) :
    (Stacks.Algebraization.idealOnOpen S).ideal U =
      (S.I.map (((S.X.presheaf.map (homOfLE le_top).op).hom).comp
        (Scheme.ΓSpecIso (.of S.A)).inv.hom)).map (S.U.ι.appIso U).hom.hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  exact Ideal.comap_symm (S.U.ι.appIso U).commRingCatIsoToRingEquiv

private lemma tilde_smul_eq_zero {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (a : R) (ha : ∀ m : M, a • m = 0)
    (U : (Spec R).Opens) (x : Γ(tilde M, U)) : a • x = 0 := by
  apply Subtype.ext
  funext p
  show (algebraMap R (Localization.AtPrime p.val.asIdeal) a) • x.val p = 0
  rw [algebraMap_smul]
  induction x.val p using LocalizedModule.induction_on with
  | h m s => simp [LocalizedModule.smul'_mk, ha]

private lemma restrict_tilde_idealPowerMultiple_eq_bot
    (S : Stacks.Algebraization.AlgebraizationSituation.{u}) (M : ModuleCat.{u} S.A) (n : ℕ)
    (h : S.I ^ n • (⊤ : Submodule S.A M) = ⊥) :
    Stacks.Algebraization.idealPowerMultiple (Stacks.Algebraization.idealOnOpen S) n
      ((tilde M).restrict S.U.ι) = ⊥ := by
  rw [idealPowerMultiple_eq_bot_iff]
  intro U
  rw [idealOnOpen_ideal, ← Ideal.map_pow, ← Ideal.map_pow,
    ← Submodule.le_annihilator_iff, Ideal.map_le_iff_le_comap,
    Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, Submodule.mem_annihilator]
  intro x hx
  have hh := tilde_smul_eq_zero (R := CommRingCat.of S.A) M a
    (fun m ↦ Submodule.mem_annihilator.mp (Submodule.le_annihilator_iff.mpr h ha) m trivial)
    (S.U.ι ''ᵁ U) x
  apply (ConcreteCategory.bijective_of_isIso
    ((tilde (R := CommRingCat.of S.A) M).restrictAppIso S.U.ι U).hom).1
  rw [map_zero, Scheme.Modules.smul_restrictAppIso_hom_apply]
  simp only [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  exact hh

private lemma tilde_map_smul_apply {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (a : R) (U : (Spec R).Opens) (x : Γ(tilde M, U)) :
    ((tilde.functor R).map (ModuleCat.ofHom (a • LinearMap.id))).val.app (op U) x =
      a • x := by
  apply Subtype.ext
  funext p
  show LocalizedModule.map p.val.asIdeal.primeCompl (a • LinearMap.id) (x.val p) =
    (algebraMap R (Localization.AtPrime p.val.asIdeal) a) • x.val p
  rw [algebraMap_smul]
  induction x.val p using LocalizedModule.induction_on with
  | h m s => simp [LocalizedModule.smul'_mk]

private lemma submodule_comp_eq_zero_iff {X : Scheme.{u}} {M N : X.Modules}
    (P : M.Submodule) (f : M ⟶ N) : P.ιModules ≫ f = 0 ↔ P ≤ kernelSubmodule f := by
  rw [le_iff_modules]
  constructor
  · intro h U x hx
    rw [kernelSubmodule_toSubmodule_obj]
    have he := congrArg (fun g : P.asModules ⟶ N => g.val.app U) h
    exact ConcreteCategory.congr_hom he ⟨x, hx⟩
  · intro h
    ext U x
    have hx := h (op U) x.property
    rwa [kernelSubmodule_toSubmodule_obj] at hx

private lemma idealPowerMultiple_comp_eq_zero_iff {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules} (f : M ⟶ N) :
    (Stacks.Algebraization.idealPowerMultiple I n M).ιModules ≫ f = 0 ↔
      ∀ U : X.affineOpens, ∀ a ∈ I.ideal U ^ n, ∀ x : Γ(M, U),
        appHom f U.1 (a • x) = 0 := by
  rw [submodule_comp_eq_zero_iff, Stacks.Algebraization.idealPowerMultiple_le_iff]
  refine forall_congr' fun U => ?_
  constructor
  · exact fun h a ha x ↦ (mem_kernelSubmodule_obj f _).mp
      (h (Submodule.smul_mem_smul ha Submodule.mem_top))
  · intro h y hy
    have hle : I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) ≤ (appHom f U.1).ker :=
      Submodule.smul_le.mpr fun a ha x _ ↦ LinearMap.mem_ker.mpr (h a ha x)
    exact (mem_kernelSubmodule_obj f y).mpr (LinearMap.mem_ker.mp (hle hy))

private lemma hom_eq_zero_of_affine {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (h : ∀ U : X.affineOpens, appHom f U.1 = 0) : f = 0 := by
  ext U x
  apply TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf N)
  intro p hp
  obtain ⟨V, hV, hpV, hVU⟩ := exists_isAffineOpen_mem_and_subset hp
  refine ⟨V, hVU, hpV, ?_⟩
  have hz : ∀ y : Γ(M, V), appHom f V y = 0 := fun y ↦
    (DFunLike.congr_fun (h ⟨V, hV⟩) y).trans (LinearMap.zero_apply y)
  show N.val.map (homOfLE hVU).op ((f.val.app (op U)) x) = N.val.map (homOfLE hVU).op 0
  rw [map_zero]
  exact (PresheafOfModules.naturality_apply f.val (homOfLE hVU).op x).symm.trans (hz _)

private abbrev scalarMapOn (S : Stacks.Algebraization.AlgebraizationSituation.{u})
    (U : S.U.toScheme.Opens) : S.A →+* Γ(S.U.toScheme, U) :=
  (S.U.ι.appIso U).hom.hom.comp
    ((S.X.presheaf.map (homOfLE le_top).op).hom.comp (Scheme.ΓSpecIso (.of S.A)).inv.hom)

private lemma restrict_tilde_map_smul_apply
    (S : Stacks.Algebraization.AlgebraizationSituation.{u}) (M : ModuleCat.{u} S.A)
    (a : S.A) (U : S.U.toScheme.Opens)
    (x : Γ((tilde (R := CommRingCat.of S.A) M).restrict S.U.ι, U)) :
    ((tilde.functor (.of S.A) ⋙ Scheme.Modules.restrictFunctor S.U.ι).map
      (ModuleCat.ofHom (a • LinearMap.id))).val.app (op U) x = scalarMapOn S U a • x := by
  apply (ConcreteCategory.bijective_of_isIso
    ((tilde (R := CommRingCat.of S.A) M).restrictAppIso S.U.ι U).hom).1
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  show ((tilde.functor (.of S.A)).map (ModuleCat.ofHom (a • LinearMap.id))).val.app
      (op (S.U.ι ''ᵁ U)) x = _
  refine (tilde_map_smul_apply (R := CommRingCat.of S.A) M a (S.U.ι ''ᵁ U) x).trans ?_
  show _ = ((tilde (R := CommRingCat.of S.A) M).smul
    ((S.U.ι.appIso U).inv.hom ((S.U.ι.appIso U).hom.hom _))).asHom x
  simp only [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rfl

private lemma smul_top_le_ker_iff {A B : Type u} [CommRing A] [CommRing B]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (φ : A →+* B) (J : Ideal A) (f : M →ₗ[B] N) :
    J.map φ • (⊤ : Submodule B M) ≤ f.ker ↔
      ∀ a ∈ J, ∀ x : M, f (φ a • x) = 0 := by
  have h : ∀ K : Ideal B, K • (⊤ : Submodule B M) ≤ f.ker ↔ K ≤ f.range.annihilator := by
    intro K
    rw [Submodule.smul_le]
    constructor
    · intro h a ha
      rw [Submodule.mem_annihilator]
      rintro _ ⟨x, rfl⟩
      rw [← map_smul]
      exact h a ha x trivial
    · intro h a ha x hx
      show f (a • x) = 0
      rw [map_smul]
      exact Submodule.mem_annihilator.mp (h ha) _ ⟨x, rfl⟩
  rw [h, Ideal.map_le_iff_le_comap]
  constructor
  · intro h a ha x
    rw [map_smul]
    exact Submodule.mem_annihilator.mp (h ha) _ ⟨x, rfl⟩
  · intro h a ha
    rw [Ideal.mem_comap, Submodule.mem_annihilator]
    rintro _ ⟨x, rfl⟩
    simpa only [map_smul] using h a ha x

/-- The composite `N ↦ N^~|_U` of sheafification on `X = Spec(A)` with restriction to the open
complement `U`. -/
public abbrev restrictedTildeFunctor (S : Stacks.Algebraization.AlgebraizationSituation.{u}) :=
  tilde.functor (.of S.A) ⋙ Scheme.Modules.restrictFunctor S.U.ι

/-- `restrictedTildeFunctor` is a left adjoint, being a composite of two left adjoints. Its
right adjoint takes a module on `U` to the `A`-module of its sections over `U`. -/
public abbrev restrictedTildeAdjunction (S : Stacks.Algebraization.AlgebraizationSituation.{u}) :=
  (tilde.adjunction (R := .of S.A)).comp (Scheme.Modules.restrictAdjunction S.U.ι)

local instance : (tilde.functor (.of S.A)).Additive := ⟨by intros; exact tilde.map_add _ _⟩
local instance : (Scheme.Modules.restrictFunctor S.U.ι).Additive := ⟨by intros; rfl⟩

local instance (X : Scheme.{u}) : PreservesFiniteLimits (Scheme.Modules.toPresheaf X) :=
  inferInstance

local instance : PreservesFiniteLimits (Scheme.Modules.restrictFunctor S.U.ι) := by
  have he : Scheme.Modules.restrictFunctor S.U.ι ⋙ Scheme.Modules.toPresheaf _ =
      Scheme.Modules.toPresheaf _ ⋙
        (Functor.whiskeringLeft _ _ Ab).obj S.U.ι.opensFunctor.op := rfl
  have : PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor S.U.ι ⋙ Scheme.Modules.toPresheaf _) := by
    rw [he]
    have : PreservesFiniteLimits
        ((Functor.whiskeringLeft _ _ Ab.{u}).obj S.U.ι.opensFunctor.op) :=
      ⟨fun J _ _ ↦ CategoryTheory.whiskeringLeft_preservesLimitsOfShape J _⟩
    exact comp_preservesFiniteLimits _ _
  have : ReflectsLimits (Scheme.Modules.toPresheaf S.U.toScheme) :=
    reflectsLimits_of_reflectsIsomorphisms
  exact ⟨fun J _ _ ↦
    preservesLimitsOfShape_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf _)⟩

/-- Sheafification and restriction to an open both preserve finite limits, hence so does their
composite. -/
public theorem restrictedTilde_preservesFiniteLimits :
    PreservesFiniteLimits (restrictedTildeFunctor S) := by
  have := AlgebraicGeometry.tilde.preservesFiniteLimits (.of S.A)
  exact comp_preservesFiniteLimits _ _

attribute [local instance] restrictedTilde_preservesFiniteLimits

/-- `restrictedTildeFunctor` is a left adjoint. -/
public theorem restrictedTilde_isLeftAdjoint : (restrictedTildeFunctor S).IsLeftAdjoint :=
  (restrictedTildeAdjunction S).isLeftAdjoint

attribute [local instance] restrictedTilde_isLeftAdjoint

private theorem restrictedTilde_preservesColimits :
    PreservesColimitsOfSize.{u, u} (restrictedTildeFunctor S) := inferInstance
attribute [local instance] restrictedTilde_preservesColimits

private theorem restrictedTilde_preservesSmallestColimits :
    PreservesColimitsOfSize.{0, 0} (restrictedTildeFunctor S) :=
  preservesSmallestColimits_of_preservesColimits _

attribute [local instance] restrictedTilde_preservesSmallestColimits

private lemma isZero_iff_of_iso {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) :
    IsZero X ↔ IsZero Y := ⟨fun h ↦ h.of_iso e.symm, fun h ↦ h.of_iso e⟩

private lemma restrictedTilde_map_isIso_iff (M N : ModuleCat.{u} S.A) (f : M ⟶ N) :
    IsIso ((restrictedTildeFunctor S).map f) ↔
      IsIPowerTorsion S.A f.hom.ker S.a ∧
      IsIPowerTorsion S.A (N ⧸ f.hom.range) S.a := by
  let L := restrictedTildeFunctor S
  have hzero (P : ModuleCat.{u} S.A) : IsZero (L.obj P) ↔ IsIPowerTorsion S.A P S.a := by
    rw [show L.obj P = (tilde P).restrict
      (Stacks.LocalCohomology.complementZeroLocus S.A S.a).ι by rfl]
    exact ⟨isIPowerTorsion_of_restrict_tilde_isZero _ _ (Ideal.fg_of_isNoetherianRing _) _,
      iPowerTorsion_tilde_restrict_isZero _ _ (Ideal.fg_of_isNoetherianRing _) _⟩
  have hk : IsZero (kernel (L.map f)) ↔ IsIPowerTorsion S.A f.hom.ker S.a := by
    rw [← isZero_iff_of_iso (PreservesKernel.iso L f),
      isZero_iff_of_iso (L.mapIso (ModuleCat.kernelIsoKer f))]
    exact hzero _
  have hc : IsZero (cokernel (L.map f)) ↔
      IsIPowerTorsion S.A (N ⧸ f.hom.range) S.a := by
    rw [← isZero_iff_of_iso (PreservesCokernel.iso L f),
      isZero_iff_of_iso (L.mapIso (ModuleCat.cokernelIsoRangeQuotient f))]
    exact hzero _
  constructor
  · intro _
    exact ⟨hk.mp ((Preadditive.mono_iff_isZero_kernel _).mp inferInstance),
      hc.mp ((Preadditive.epi_iff_isZero_cokernel _).mp inferInstance)⟩
  · rintro ⟨h₁, h₂⟩
    have := Preadditive.mono_of_isZero_kernel (L.map f) (hk.mpr h₁)
    have := Preadditive.epi_of_isZero_cokernel (L.map f) (hc.mpr h₂)
    exact isIso_of_mono_of_epi _

private lemma adjunction_map_comp_zero_iff
    {A : Type u} [CommRing A] {C : Type*} [Category C] [Preadditive C]
    {L : ModuleCat.{u} A ⥤ C} {R : C ⥤ ModuleCat.{u} A} (adj : L ⊣ R)
    [L.Additive] {M N : ModuleCat.{u} A} {F : C} (g : N ⟶ M) (f : L.obj M ⟶ F) :
    L.map g ≫ f = 0 ↔ g ≫ adj.homEquiv M F f = 0 := by
  rw [← (adj.homEquiv N F).injective.eq_iff,
    adj.homEquiv_naturality_left, adj.homAddEquiv_zero]

private lemma map_ideal_subtype_comp_zero_iff
    {A : Type u} [CommRing A] {C : Type*} [Category C] [Preadditive C]
    {L : ModuleCat.{u} A ⥤ C} {R : C ⥤ ModuleCat.{u} A} (adj : L ⊣ R)
    [L.Additive] (M : ModuleCat.{u} A) (J : Ideal A) {F : C} (f : L.obj M ⟶ F) :
    L.map (ModuleCat.ofHom (J • (⊤ : Submodule A M)).subtype) ≫ f = 0 ↔
      ∀ a ∈ J, L.map (ModuleCat.ofHom (a • LinearMap.id : M →ₗ[A] M)) ≫ f = 0 := by
  simp only [adjunction_map_comp_zero_iff adj]
  let g := (adj.homEquiv M F f).hom
  have h₁ : ModuleCat.ofHom (J • (⊤ : Submodule A M)).subtype ≫
      adj.homEquiv M F f = 0 ↔ J • (⊤ : Submodule A M) ≤ g.ker := by
    constructor
    · intro h x hx
      exact ConcreteCategory.congr_hom h ⟨x, hx⟩
    · intro h
      ext x
      exact h x.property
  rw [h₁, Submodule.smul_le]
  simp only [Submodule.mem_top, forall_true_left]
  exact ⟨fun h a ha ↦ by ext x; exact h a ha x,
    fun h a ha x ↦ ConcreteCategory.congr_hom (h a ha) x⟩

private lemma idealPowerMultiple_restricted_comp_zero_iff
    (M : ModuleCat.{u} S.A) (n : ℕ) {F : S.U.toScheme.Modules}
    (f : (restrictedTildeFunctor S).obj M ⟶ F) :
    (Stacks.Algebraization.idealPowerMultiple (Stacks.Algebraization.idealOnOpen S) n
      ((restrictedTildeFunctor S).obj M)).ιModules ≫ f = 0 ↔
      (restrictedTildeFunctor S).map
        (ModuleCat.ofHom (S.I ^ n • (⊤ : Submodule S.A M)).subtype) ≫ f = 0 := by
  rw [map_ideal_subtype_comp_zero_iff (restrictedTildeAdjunction S),
    idealPowerMultiple_comp_eq_zero_iff]
  have hlocal (U : S.U.toScheme.affineOpens) :
      (∀ a ∈ (Stacks.Algebraization.idealOnOpen S).ideal U ^ n,
          ∀ x : Γ((restrictedTildeFunctor S).obj M, U.1), appHom f U.1 (a • x) = 0) ↔
      ∀ a ∈ S.I ^ n, ∀ x : Γ((restrictedTildeFunctor S).obj M, U.1),
        appHom f U.1 (scalarMapOn S U a • x) = 0 := by
    have hh : (Stacks.Algebraization.idealOnOpen S).ideal U ^ n •
          (⊤ : Submodule Γ(S.U.toScheme, U) Γ((restrictedTildeFunctor S).obj M, U)) ≤
          (appHom f U.1).ker ↔
        ∀ a ∈ (Stacks.Algebraization.idealOnOpen S).ideal U ^ n,
          ∀ x : Γ((restrictedTildeFunctor S).obj M, U.1), appHom f U.1 (a • x) = 0 := by
      simp only [Submodule.smul_le, Submodule.mem_top, forall_true_left, LinearMap.mem_ker]
    rw [← hh, idealOnOpen_ideal, ← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map]
    exact smul_top_le_ker_iff _ _ _
  constructor
  · intro h a ha
    refine hom_eq_zero_of_affine _ fun U ↦ ?_
    ext x
    show appHom f U.1
      (((restrictedTildeFunctor S).map (ModuleCat.ofHom (a • LinearMap.id))).val.app
        (op U.1) x) = 0
    exact (congrArg (fun y ↦ appHom f U.1 y)
      (restrict_tilde_map_smul_apply S M a U.1 x)).trans ((hlocal U).mp (h U) a ha x)
  · intro h U
    apply (hlocal U).mpr
    intro a ha x
    have he := congrArg (fun g : (restrictedTildeFunctor S).obj M ⟶ F ↦
      g.val.app (op U.1)) (h a ha)
    have hh := ConcreteCategory.congr_hom he x
    change appHom f U.1
      (((restrictedTildeFunctor S).map (ModuleCat.ofHom (a • LinearMap.id))).val.app
        (op U.1) x) = 0 at hh
    exact (congrArg (fun y ↦ appHom f U.1 y)
      (restrict_tilde_map_smul_apply S M a U.1 x)).symm.trans hh

private def moduleQuotientIsCokernel {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) (P : Submodule A M) :
    IsColimit (CokernelCofork.ofπ (ModuleCat.ofHom P.mkQ)
      (show ModuleCat.ofHom P.subtype ≫ ModuleCat.ofHom P.mkQ = 0 by ext x; simp)) := by
  apply ModuleCat.isColimitCokernelCofork
  · exact LinearMap.exact_iff.mpr (by simp)
  · exact P.mkQ_surjective

/-- The sheaf quotient `M / I ^ n M`, with the inclusion of `I ^ n M` ascribed at `X.Modules`.

`Stacks.Algebraization.idealPowerQuotient` is the cokernel of the generic
`SheafOfModules.Submodule.ι`. Composing that with a morphism of `X.Modules` builds a hom type
whose objects come from one spelling and whose category instance from the other, and at such a
type the numeral `0` has no `OfNat` instance; the lemmas below are therefore stated through
`ιModules`, the same inclusion ascribed at `X.Modules`. -/
private abbrev powerQuotient {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) :
    X.Modules :=
  cokernel (Stacks.Algebraization.idealPowerMultiple I n M).ιModules

/-- The quotient-transition clause of a coherent adic system at the two spellings of the
inclusion of `I ^ n M`. They are definitionally equal, so this is the whole bridge between the
statements below and `Stacks.Coherent.IsCoherentAdicSystem`. -/
private lemma exists_powerQuotient_iso_iff {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (f : M ⟶ N) :
    (∃ i : powerQuotient I n M ≅ N,
        cokernel.π (Stacks.Algebraization.idealPowerMultiple I n M).ιModules ≫ i.hom = f) ↔
      ∃ i : Stacks.Algebraization.idealPowerQuotient I n M ≅ N,
        cokernel.π (Stacks.Algebraization.idealPowerMultiple I n M).ι ≫ i.hom = f :=
  Iff.rfl

private theorem restrictedQuotientIsCokernel (M : ModuleCat.{u} S.A) (n : ℕ) :
    ∃ h : (Stacks.Algebraization.idealPowerMultiple (Stacks.Algebraization.idealOnOpen S) n
        ((restrictedTildeFunctor S).obj M)).ιModules ≫
        (restrictedTildeFunctor S).map
          (ModuleCat.ofHom (S.I ^ n • (⊤ : Submodule S.A M)).mkQ) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ h)) := by
  let P := S.I ^ n • (⊤ : Submodule S.A M)
  let L := restrictedTildeFunctor S
  have hw : ModuleCat.ofHom P.subtype ≫ ModuleCat.ofHom P.mkQ = 0 := by ext x; simp
  let hc := isColimitCoforkMapOfIsColimit' L hw (moduleQuotientIsCokernel M P)
  have hw' := (idealPowerMultiple_restricted_comp_zero_iff S M n _).mpr
    (show L.map (ModuleCat.ofHom P.subtype) ≫ L.map (ModuleCat.ofHom P.mkQ) = 0 by
      rw [← L.map_comp, hw, L.map_zero])
  exact ⟨hw', ⟨CokernelCofork.isColimitOfIsColimitOfIff' hc _
    (fun {W} f ↦ (idealPowerMultiple_restricted_comp_zero_iff S M n f).symm)⟩⟩

private lemma exists_cokernel_iso_iff {C : Type*} [Category C] [HasZeroMorphisms C]
    {P M N : C} (i : P ⟶ M) [HasCokernel i] (f : M ⟶ N) :
    (∃ e : cokernel i ≅ N, cokernel.π i ≫ e.hom = f) ↔
      ∃ h : i ≫ f = 0, Nonempty (IsColimit (CokernelCofork.ofπ f h)) := by
  constructor
  · rintro ⟨e, he⟩
    have h : i ≫ f = 0 := by rw [← he, ← Category.assoc, cokernel.condition, zero_comp]
    exact ⟨h, ⟨(cokernelIsCokernel i).ofIsoColimit (Cofork.ext e he)⟩⟩
  · rintro ⟨h, ⟨hc⟩⟩
    exact ⟨(cokernelIsCokernel i).coconePointUniqueUpToIso hc,
      (cokernelIsCokernel i).comp_coconePointUniqueUpToIso_hom hc WalkingParallelPair.one⟩

/-- **`(M^~|_U) / Iⁿ (M^~|_U)` is `(M / IⁿM)^~|_U`.** The sheaf quotient of the restriction to
`U` of the sheaf associated to an `A`-module by the `n`-th power of `I 𝒪_U` is the restriction to
`U` of the sheaf associated to the module quotient, compatibly with the two quotient
projections.

This is the iso form of `restrictedQuotientIsCokernel`: restriction of the sheafification is a
left adjoint, so it carries the module presentation `M ⟶ M / IⁿM` to a cokernel, and the
subsheaf that presentation kills is exactly `Iⁿ (M^~|_U)`. -/
public theorem restrictedTilde_idealPowerQuotient_iso (M : ModuleCat.{u} S.A) (n : ℕ) :
    ∃ e : Stacks.Algebraization.idealPowerQuotient (Stacks.Algebraization.idealOnOpen S) n
        ((restrictedTildeFunctor S).obj M) ≅
        (restrictedTildeFunctor S).obj
          (ModuleCat.of S.A (M ⧸ S.I ^ n • (⊤ : Submodule S.A M))),
      cokernel.π (Stacks.Algebraization.idealPowerMultiple
          (Stacks.Algebraization.idealOnOpen S) n ((restrictedTildeFunctor S).obj M)).ι ≫ e.hom =
        (restrictedTildeFunctor S).map
          (ModuleCat.ofHom (S.I ^ n • (⊤ : Submodule S.A M)).mkQ) :=
  (exists_powerQuotient_iso_iff _ _ _).mp
    ((exists_cokernel_iso_iff _ _).mpr (restrictedQuotientIsCokernel S M n))

private lemma idealPowerMultiple_comp_iso_iff {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) {M N F : X.Modules} (e : M ≅ N) (f : N ⟶ F) :
    (Stacks.Algebraization.idealPowerMultiple I n M).ιModules ≫ e.hom ≫ f = 0 ↔
      (Stacks.Algebraization.idealPowerMultiple I n N).ιModules ≫ f = 0 := by
  simp only [idealPowerMultiple_comp_eq_zero_iff, appHom_comp]
  constructor
  · intro h U a ha x
    have hh := h U a ha (appHom e.inv U.1 x)
    rwa [map_smul, appHom_inv_hom] at hh
  · intro h U a ha x
    rw [map_smul]
    exact h U a ha _

private lemma powerQuotient_congr {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {M N M' N' : X.Modules} (e : M ≅ M') (d : N ≅ N')
    (f : M ⟶ N) (g : M' ⟶ N') (w : f ≫ d.hom = e.hom ≫ g)
    (h : ∃ i : powerQuotient I n M' ≅ N',
      cokernel.π (Stacks.Algebraization.idealPowerMultiple I n M').ιModules ≫ i.hom = g) :
    ∃ i : powerQuotient I n M ≅ N,
      cokernel.π (Stacks.Algebraization.idealPowerMultiple I n M).ιModules ≫ i.hom = f := by
  obtain ⟨hg, ⟨hc⟩⟩ := (exists_cokernel_iso_iff _ _).mp h
  let hc' := CokernelCofork.isColimitOfIsColimitOfIff hc
    (Stacks.Algebraization.idealPowerMultiple I n M).ιModules e
    (fun {W} φ ↦ (idealPowerMultiple_comp_iso_iff I n e φ).symm)
  obtain ⟨i, hi⟩ := (exists_cokernel_iso_iff _ _).mpr ⟨_, ⟨hc'⟩⟩
  refine ⟨i ≪≫ d.symm, ?_⟩
  show _ ≫ i.hom ≫ d.inv = f
  rw [← Category.assoc, hi]
  show (e.hom ≫ g) ≫ d.inv = f
  rw [← w]
  simp

private lemma restrictedTilde_quotient_transition
    (M N : ModuleCat.{u} S.A) (n : ℕ)
    (f : (M ⧸ S.I ^ n • (⊤ : Submodule S.A M)) →ₗ[S.A] N)
    (hf : IsIPowerTorsion S.A f.ker S.a ∧
      IsIPowerTorsion S.A (N ⧸ f.range) S.a) :
    ∃ e : powerQuotient (Stacks.Algebraization.idealOnOpen S) n
        ((restrictedTildeFunctor S).obj M) ≅ (restrictedTildeFunctor S).obj N,
      cokernel.π (Stacks.Algebraization.idealPowerMultiple (Stacks.Algebraization.idealOnOpen S) n
          ((restrictedTildeFunctor S).obj M)).ιModules ≫ e.hom =
        (restrictedTildeFunctor S).map
          (ModuleCat.ofHom (f.comp (S.I ^ n • (⊤ : Submodule S.A M)).mkQ)) := by
  obtain ⟨e, he⟩ := (exists_cokernel_iso_iff _ _).mpr (restrictedQuotientIsCokernel S M n)
  have := (restrictedTilde_map_isIso_iff S _ _ (ModuleCat.ofHom f)).mpr hf
  refine ⟨e ≪≫ asIso ((restrictedTildeFunctor S).map (ModuleCat.ofHom f)), ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, he, asIso_hom, ← Functor.map_comp]
  rfl

/-- **The quotient-transition clause of a coherent adic system, for sheafified finite modules.**
If a map `M/IⁿM → N` of `A`-modules has `𝔞`-power torsion kernel and cokernel, then `N^~|_U` is
the sheaf quotient `Stacks.Algebraization.idealPowerQuotient` of `M^~|_U` by the `n`-th
ideal-power multiple, compatibly with the map itself. -/
public lemma restrictedTilde_quotient_transition_idealPowerQuotient
    (M N : ModuleCat.{u} S.A) (n : ℕ)
    (f : (M ⧸ S.I ^ n • (⊤ : Submodule S.A M)) →ₗ[S.A] N)
    (hf : IsIPowerTorsion S.A f.ker S.a ∧
      IsIPowerTorsion S.A (N ⧸ f.range) S.a) :
    ∃ e : Stacks.Algebraization.idealPowerQuotient (Stacks.Algebraization.idealOnOpen S) n
        ((restrictedTildeFunctor S).obj M) ≅ (restrictedTildeFunctor S).obj N,
      cokernel.π (Stacks.Algebraization.idealPowerMultiple (Stacks.Algebraization.idealOnOpen S) n
          ((restrictedTildeFunctor S).obj M)).ι ≫ e.hom =
        (restrictedTildeFunctor S).map
          (ModuleCat.ofHom (f.comp (S.I ^ n • (⊤ : Submodule S.A M)).mkQ)) :=
  (exists_powerQuotient_iso_iff _ _ _).mp (restrictedTilde_quotient_transition S M N n f hf)

/-- **The sheaf quotient `F / Iⁿ F` of `F ≅ M̃|_U` is `(M / IⁿM)~|_U`.** For a module `F` on
`U` identified with `M̃|_U` by `e`, the image under `N ↦ Ñ|_U` of the quotient map
`M ⟶ M / IⁿM`, precomposed with `e`, is a cokernel of the inclusion of `Iⁿ F`; so there is an
isomorphism from the sheaf quotient to `(M / IⁿM)~|_U` under which the quotient projection of
`F` is that map. No finiteness of `M` is needed. -/
public theorem exists_idealPowerQuotient_iso_restrictedTilde (M : ModuleCat.{u} S.A) (n : ℕ)
    {F : S.U.toScheme.Modules} (e : F ≅ (restrictedTildeFunctor S).obj M) :
    ∃ i : Stacks.Algebraization.idealPowerQuotient (Stacks.Algebraization.idealOnOpen S) n F ≅
        (restrictedTildeFunctor S).obj (ModuleCat.of S.A (M ⧸ S.I ^ n • (⊤ : Submodule S.A M))),
      cokernel.π (Stacks.Algebraization.idealPowerMultiple
          (Stacks.Algebraization.idealOnOpen S) n F).ι ≫ i.hom =
        e.hom ≫ (restrictedTildeFunctor S).map
          (ModuleCat.ofHom (S.I ^ n • (⊤ : Submodule S.A M)).mkQ) :=
  (exists_powerQuotient_iso_iff _ _ _).mp
    (powerQuotient_congr _ n e (Iso.refl _) _ _ (by simp)
      ((exists_cokernel_iso_iff _ _).mpr (restrictedQuotientIsCokernel S M n)))

private lemma restrictedTilde_quotient_map_isIso (M : ModuleCat.{u} S.A) (n : ℕ)
    (h : Stacks.Algebraization.idealPowerMultiple (Stacks.Algebraization.idealOnOpen S) n
      ((restrictedTildeFunctor S).obj M) = ⊥) :
    IsIso ((restrictedTildeFunctor S).map
      (ModuleCat.ofHom (S.I ^ n • (⊤ : Submodule S.A M)).mkQ)) := by
  obtain ⟨hw, ⟨hc⟩⟩ := restrictedQuotientIsCokernel S M n
  apply CokernelCofork.IsColimit.isIso_π _ hc
  have hi : (Stacks.Algebraization.idealPowerMultiple (Stacks.Algebraization.idealOnOpen S) n
      ((restrictedTildeFunctor S).obj M)).ιModules ≫ 𝟙 _ = 0 :=
    (submodule_comp_eq_zero_iff _ _).mpr (h.trans_le bot_le)
  simpa using hi

private lemma ideal_smul_quotient_eq_bot {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) (J : Ideal A) :
    J • (⊤ : Submodule A (M ⧸ J • (⊤ : Submodule A M))) = ⊥ := by
  rw [← Submodule.le_annihilator_iff]
  intro a ha
  rw [Submodule.mem_annihilator]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    show (Submodule.Quotient.mk (a • x) : M ⧸ J • (⊤ : Submodule A M)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha trivial)

private lemma ideal_smul_le_ker_of_annihilated {A : Type u} [CommRing A]
    {M N : ModuleCat.{u} A} (f : M →ₗ[A] N) (J : Ideal A)
    (h : J • (⊤ : Submodule A N) = ⊥) : J • (⊤ : Submodule A M) ≤ f.ker := by
  rw [Submodule.smul_le]
  intro a ha x hx
  show f (a • x) = 0
  rw [map_smul]
  exact Submodule.mem_annihilator.mp (Submodule.le_annihilator_iff.mpr h ha) _ trivial

private lemma exists_finite_extension_morphism (M : ModuleCat.{u} S.A)
    (G : S.U.toScheme.Modules) (hG : G.IsCoherent)
    (φ : G ⟶ (restrictedTildeFunctor S).obj M) :
    ∃ (N : ModuleCat.{u} S.A), Module.Finite S.A N ∧
      ∃ (f : N ⟶ M) (e : (restrictedTildeFunctor S).obj N ≅ G),
        e.hom ≫ φ = (restrictedTildeFunctor S).map f := by
  have : G.IsFinitePresentation :=
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae S.U.toScheme G).out 1 3).mp hG
  obtain ⟨H, hH, ψ, e, he⟩ := AlgebraicGeometry.exists_finitePresentation_extension_of_hom
    (tilde (R := .of S.A) M) S.U (isCompact_iff_compactSpace.mpr inferInstance) G φ
  have : H.IsFinitePresentation := hH
  have : H.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData H).choose.isQuasicoherent
  let N := (moduleSpecΓFunctor (R := .of S.A)).obj H
  -- `fromTildeΓ` states its source as `tilde ((modulesSpecToSheaf.obj H).presheaf.obj (op ⊤))`,
  -- which is only definitionally `tilde N`; ascribing the latter here would leave instance
  -- search unable to recognize the `IsIso` instance for `fromTildeΓ`.
  let eN := asIso H.fromTildeΓ
  have hfp : (tilde (R := .of S.A) N).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation S.X.ringCatSheaf).prop_of_iso eN.symm hH
  have : Module.FinitePresentation (CommRingCat.of S.A) N :=
    (AlgebraicGeometry.tilde_isFinitePresentation_iff N).mp hfp
  have : (tilde.functor (.of S.A)).Full := (tilde.fullyFaithfulFunctor (R := .of S.A)).full
  let f : N ⟶ M := (tilde.functor (.of S.A)).preimage (eN.hom ≫ ψ)
  refine ⟨N, inferInstance, f, (Scheme.Modules.restrictFunctor S.U.ι).mapIso eN ≪≫ e, ?_⟩
  show (Scheme.Modules.restrictFunctor S.U.ι).map eN.hom ≫ e.hom ≫ φ = _
  refine (congrArg (fun k ↦ (Scheme.Modules.restrictFunctor S.U.ι).map eN.hom ≫ k) he).trans ?_
  refine ((Scheme.Modules.restrictFunctor S.U.ι).map_comp eN.hom ψ).symm.trans ?_
  exact congrArg (Scheme.Modules.restrictFunctor S.U.ι).map
    (Functor.map_preimage (tilde.functor (.of S.A)) (eN.hom ≫ ψ)).symm

private structure TermModel
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S)) (n : ℕ) where
  module : ModuleCat.{u} S.A
  finite : Module.Finite S.A module
  annihilated : S.I ^ (n + 1) • (⊤ : Submodule S.A module) = ⊥
  iso : (restrictedTildeFunctor S).obj module ≅ F.obj.obj (op n)

private def quotientTermModel
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S)) (n : ℕ)
    (M : ModuleCat.{u} S.A) (hM : Module.Finite S.A M)
    (e : (restrictedTildeFunctor S).obj M ≅ F.obj.obj (op n)) : TermModel S F n := by
  let P := S.I ^ (n + 1) • (⊤ : Submodule S.A M)
  haveI := hM
  have h := Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso _ e _ (F.property.2.1 n)
  haveI := restrictedTilde_quotient_map_isIso S M (n + 1) h
  exact ⟨ModuleCat.of S.A (M ⧸ P), inferInstance, ideal_smul_quotient_eq_bot M _,
    (asIso ((restrictedTildeFunctor S).map (ModuleCat.ofHom P.mkQ))).symm ≪≫ e⟩

private lemma exists_initial_termModel
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S)) :
    Nonempty (TermModel S F 0) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_finite_extension_of_term S F 0
  exact ⟨quotientTermModel S F 0 M hM e⟩

private lemma exists_next_termModel
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S)) (n : ℕ)
    (M : TermModel S F n) :
    ∃ N : TermModel S F (n + 1), ∃ f : N.module ⟶ M.module,
      (restrictedTildeFunctor S).map f ≫ M.iso.hom =
        N.iso.hom ≫ F.obj.map (homOfLE (Nat.le_succ n)).op := by
  let t := F.obj.map (homOfLE (Nat.le_succ n)).op
  obtain ⟨N, hN, f, e, he⟩ := exists_finite_extension_morphism S M.module
    (F.obj.obj (op (n + 1))) (F.property.1 (n + 1)) (t ≫ M.iso.inv)
  let P := S.I ^ (n + 1 + 1) • (⊤ : Submodule S.A N)
  have hkill : S.I ^ (n + 1 + 1) • (⊤ : Submodule S.A M.module) = ⊥ := eq_bot_iff.mpr
    ((Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ _))).trans M.annihilated.le)
  let f' : (N ⧸ P) →ₗ[S.A] M.module := P.liftQ f.hom
    (ideal_smul_le_ker_of_annihilated f.hom _ hkill)
  let Q := quotientTermModel S F (n + 1) N hN e
  refine ⟨Q, ModuleCat.ofHom f', ?_⟩
  have hq : IsIso ((restrictedTildeFunctor S).map (ModuleCat.ofHom P.mkQ)) :=
    restrictedTilde_quotient_map_isIso S N (n + 1 + 1)
      (Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso _ e _ (F.property.2.1 (n + 1)))
  -- Restate the goal without `Q`, whose `module` and `iso` fields are only definitionally the
  -- quotient and the composite below; a rewrite would build its motive at a transparency at
  -- which the composite is not type-correct.
  show (restrictedTildeFunctor S).map (ModuleCat.ofHom f') ≫ M.iso.hom =
    ((asIso ((restrictedTildeFunctor S).map (ModuleCat.ofHom P.mkQ))).inv ≫ e.hom) ≫ t
  apply (cancel_epi ((restrictedTildeFunctor S).map (ModuleCat.ofHom P.mkQ))).mp
  rw [← Category.assoc, ← Functor.map_comp]
  show (restrictedTildeFunctor S).map (ModuleCat.ofHom (f'.comp P.mkQ)) ≫ M.iso.hom = _
  rw [Submodule.liftQ_mkQ]
  show (restrictedTildeFunctor S).map f ≫ M.iso.hom =
    (restrictedTildeFunctor S).map (ModuleCat.ofHom P.mkQ) ≫
      (asIso ((restrictedTildeFunctor S).map (ModuleCat.ofHom P.mkQ))).inv ≫ e.hom ≫ t
  rw [← he]
  simp [Category.assoc]

private def chosenTermModels
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S)) :
    ∀ n, TermModel S F n
  | 0 => Classical.choice (exists_initial_termModel S F)
  | n + 1 => (exists_next_termModel S F n (chosenTermModels F n)).choose

private def chosenTransition
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S)) (n : ℕ) :
    (chosenTermModels S F (n + 1)).module ⟶ (chosenTermModels S F n).module :=
  (exists_next_termModel S F n (chosenTermModels S F n)).choose_spec.choose

private lemma chosenTransition_compatibility
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S)) (n : ℕ) :
    (restrictedTildeFunctor S).map (chosenTransition S F n) ≫
      (chosenTermModels S F n).iso.hom =
      (chosenTermModels S F (n + 1)).iso.hom ≫
        F.obj.map (homOfLE (Nat.le_succ n)).op :=
  (exists_next_termModel S F n (chosenTermModels S F n)).choose_spec.choose_spec

private lemma reduction_torsion_of_powerQuotient
    (M N : ModuleCat.{u} S.A) (n : ℕ) (f : M ⟶ N)
    (hN : S.I ^ n • (⊤ : Submodule S.A N) = ⊥)
    (h : ∃ e : powerQuotient (Stacks.Algebraization.idealOnOpen S) n
        ((restrictedTildeFunctor S).obj M) ≅ (restrictedTildeFunctor S).obj N,
      cokernel.π (Stacks.Algebraization.idealPowerMultiple (Stacks.Algebraization.idealOnOpen S) n
          ((restrictedTildeFunctor S).obj M)).ιModules ≫ e.hom =
        (restrictedTildeFunctor S).map f) :
    ∃ g : (M ⧸ S.I ^ n • (⊤ : Submodule S.A M)) →ₗ[S.A] N,
      g.comp (S.I ^ n • (⊤ : Submodule S.A M)).mkQ = f.hom ∧
      IsIPowerTorsion S.A g.ker S.a ∧ IsIPowerTorsion S.A (N ⧸ g.range) S.a := by
  let P := S.I ^ n • (⊤ : Submodule S.A M)
  let g := P.liftQ f.hom (ideal_smul_le_ker_of_annihilated f.hom _ hN)
  have hg : g.comp P.mkQ = f.hom := Submodule.liftQ_mkQ _ _ _
  refine ⟨g, hg, ?_⟩
  apply (restrictedTilde_map_isIso_iff S _ _ (ModuleCat.ofHom g)).mp
  obtain ⟨e, he⟩ := (exists_cokernel_iso_iff _ _).mpr (restrictedQuotientIsCokernel S M n)
  obtain ⟨d, hd⟩ := h
  have hcomp : e.hom ≫ (restrictedTildeFunctor S).map (ModuleCat.ofHom g) = d.hom := by
    apply (cancel_epi (cokernel.π _)).mp
    rw [← Category.assoc, he, ← Functor.map_comp, hd]
    show (restrictedTildeFunctor S).map (ModuleCat.ofHom (g.comp P.mkQ)) = _
    rw [hg]
    rfl
  rw [← isIso_comp_left_iff e.hom, hcomp]
  infer_instance

/-- The coherence clause of a coherent adic system for `(M_n^~|_U)`: the terms of a system of
finite modules sheafify to coherent modules on `U`. -/
public theorem restrictedTildeSystem_isCoherent (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (hfinite : ∀ n : ℕ, Module.Finite S.A (M.obj (op n))) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} ((restrictedTildeSystem S M).obj (op n)) :=
  finite_module_restricted_tilde_isCoherent S (M.obj (op n)) (hfinite n)

/-- The annihilation clause of a coherent adic system for `(M_n^~|_U)`: if `Iⁿ⁺¹` annihilates
`M_n`, then `I ^ (n + 1) (M_n^~|_U)` vanishes.

This needs only the annihilation hypothesis, not finiteness, so it is available to systems
whose terms are not finite `A`-modules. -/
public theorem restrictedTildeSystem_idealPowerMultiple_eq_bot (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (hannihilated : ∀ n : ℕ, S.I ^ (n + 1) • (⊤ : Submodule S.A (M.obj (op n))) = ⊥) (n : ℕ) :
    Stacks.Algebraization.idealPowerMultiple (Stacks.Algebraization.idealOnOpen S) (n + 1)
      ((restrictedTildeSystem S M).obj (op n)) = ⊥ :=
  Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso _
    ((Scheme.Modules.restrictFunctorIsoPullback S.U.ι).app (tilde (M.obj (op n)))).symm _
    (restrict_tilde_idealPowerMultiple_eq_bot S (M.obj (op n)) (n + 1) (hannihilated n))

/-- The quotient-transition clause of a coherent adic system for `(M_n^~|_U)`: the reduction
condition on the modules makes each term the sheaf quotient of the next by `I ^ (n + 1)`,
compatibly with the transition map.

This needs only the reduction hypothesis, not finiteness. -/
public theorem restrictedTildeSystem_transition (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (htransition : ∀ n : ℕ,
      let N := M.obj (op (n + 1))
      let P := S.I ^ (n + 1) • (⊤ : Submodule S.A N)
      ∃ f : (N ⧸ P) →ₗ[S.A] M.obj (op n),
        (f.comp P.mkQ = (M.map (homOfLE (Nat.le_succ n)).op).hom) ∧
        IsIPowerTorsion S.A (LinearMap.ker f) S.a ∧
        IsIPowerTorsion S.A ((M.obj (op n)) ⧸ LinearMap.range f) S.a)
    (n : ℕ) :
    ∃ e : Stacks.Algebraization.idealPowerQuotient (Stacks.Algebraization.idealOnOpen S) (n + 1)
        ((restrictedTildeSystem S M).obj (op (n + 1))) ≅
        (restrictedTildeSystem S M).obj (op n),
      cokernel.π ((Stacks.Algebraization.idealPowerMultiple
          (Stacks.Algebraization.idealOnOpen S) (n + 1)
          ((restrictedTildeSystem S M).obj (op (n + 1)))).ι) ≫ e.hom =
        (restrictedTildeSystem S M).map (homOfLE (Nat.le_succ n)).op := by
  obtain ⟨f, hf, hker, hcoker⟩ := htransition n
  let e := (Scheme.Modules.restrictFunctorIsoPullback S.U.ι).app
    ((tilde.functor (.of S.A)).obj (M.obj (op (n + 1))))
  let d := (Scheme.Modules.restrictFunctorIsoPullback S.U.ι).app
    ((tilde.functor (.of S.A)).obj (M.obj (op n)))
  refine (exists_powerQuotient_iso_iff _ _ _).mp ?_
  apply powerQuotient_congr _ _ e.symm d.symm _
    ((restrictedTildeFunctor S).map (M.map (homOfLE (Nat.le_succ n)).op))
  · exact (Scheme.Modules.restrictFunctorIsoPullback S.U.ι).inv.naturality _
  · obtain ⟨i, hi⟩ := restrictedTilde_quotient_transition S
      (M.obj (op (n + 1))) (M.obj (op n)) (n + 1) f ⟨hker, hcoker⟩
    rw [hf] at hi
    exact ⟨i, hi⟩

/-- The functor `N ↦ N^~|_U` through which `restrictedTildeSystem` is formed, with restriction
written as the inverse image. -/
public abbrev pullbackTildeFunctor (S : Stacks.Algebraization.AlgebraizationSituation.{u}) :=
  tilde.functor (.of S.A) ⋙ Scheme.Modules.pullback S.U.ι

/-- `pullbackTildeFunctor` is a left adjoint, being a composite of two left adjoints. -/
public abbrev pullbackTildeAdjunction (S : Stacks.Algebraization.AlgebraizationSituation.{u}) :=
  (tilde.adjunction (R := .of S.A)).comp (Scheme.Modules.pullbackPushforwardAdjunction S.U.ι)

public theorem restrictedTildeSystem_eq_comp (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) :
    restrictedTildeSystem S M = M ⋙ pullbackTildeFunctor S := rfl

/-- `pullbackTildeFunctor` is a left adjoint. -/
public theorem pullbackTilde_isLeftAdjoint : (pullbackTildeFunctor S).IsLeftAdjoint :=
  (pullbackTildeAdjunction S).isLeftAdjoint

/-- The sheafification of an `A`-module, restricted to `U`, is quasi-coherent. -/
public theorem isQuasicoherent_pullbackTilde (N : ModuleCat.{u} S.A) :
    ((pullbackTildeFunctor S).obj N).IsQuasicoherent :=
  inferInstanceAs (((Scheme.Modules.pullback S.U.ι).obj
    ((tilde.functor (.of S.A)).obj N)).IsQuasicoherent)

/-- Sheafification and inverse image along an open immersion both preserve finite limits. -/
public theorem pullbackTilde_preservesFiniteLimits :
    PreservesFiniteLimits (pullbackTildeFunctor S) := by
  have := restrictedTilde_preservesFiniteLimits S
  exact preservesFiniteLimits_of_natIso
    (Functor.isoWhiskerLeft (tilde.functor (.of S.A))
      (Scheme.Modules.restrictFunctorIsoPullback S.U.ι))

/-- The transpose along `pullbackTildeAdjunction` of an injection of an `A`-module into the
sections of a quasi-coherent module on `U` is a monomorphism.

This is the form in which Stacks 01Y1 gets applied to the comparison maps of chapter 52:
sheafification followed by restriction preserves monomorphisms because it preserves finite
limits, and the counit of the adjunction is an isomorphism at a quasi-coherent module, because
`tilde` is a left inverse to global sections on quasi-coherent modules and `pushforward` along
an open immersion is fully faithful. -/
public theorem mono_pullbackTilde_homEquiv_symm (G : S.U.toScheme.Modules)
    (hG : G.IsQuasicoherent) {N : ModuleCat.{u} S.A}
    (φ : N ⟶ moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward S.U.ι).obj G))
    (hφ : Mono φ) :
    Mono (((pullbackTildeAdjunction S).homEquiv N G).symm φ) := by
  have : PreservesFiniteLimits (pullbackTildeFunctor S) :=
    pullbackTilde_preservesFiniteLimits S
  have hmono : Mono ((pullbackTildeFunctor S).map φ) := Functor.map_mono _ φ
  have h₁ : IsIso ((tilde.adjunction (R := .of S.A)).counit.app
      ((Scheme.Modules.pushforward S.U.ι).obj G)) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pushforward S.U.ι).obj G).fromTildeΓ)
  have : IsIso ((pullbackTildeAdjunction S).counit.app G) := by
    rw [Adjunction.comp_counit_app]
    infer_instance
  rw [Adjunction.homEquiv_counit]
  have := IsIso.mono_of_iso ((pullbackTildeAdjunction S).counit.app G)
  exact mono_comp _ _

/-- A finite module model gives a coherent adic system on the punctured
spectrum. -/
@[stacks 0DXT "forward implication"]
public theorem restrictedTildeSystem_isCoherentAdicSystem
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (hM : IsFiniteModuleModel S M) :
    Stacks.Coherent.IsCoherentAdicSystem (Stacks.Algebraization.idealOnOpen S)
      (restrictedTildeSystem S M) :=
  ⟨restrictedTildeSystem_isCoherent S M hM.1,
    restrictedTildeSystem_idealPowerMultiple_eq_bot S M hM.2.1,
    restrictedTildeSystem_transition S M hM.2.2⟩

/-- The coherent adic object determined by a finite module model. -/
public def coherentAdicSystemOfFiniteModuleModel
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (hM : IsFiniteModuleModel S M) :
    Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S) :=
  ⟨restrictedTildeSystem S M, restrictedTildeSystem_isCoherentAdicSystem S M hM⟩

/-- Every coherent adic system on `U` has a finite module model, compatible
with the whole inverse-system structure. -/
@[stacks 0DXT "converse"]
public theorem exists_finiteModuleModel
    (F : Stacks.Coherent.CoherentAdicSystems (Stacks.Algebraization.idealOnOpen S)) :
    ∃ M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A,
      ∃ hM : IsFiniteModuleModel S M,
        Nonempty (coherentAdicSystemOfFiniteModuleModel S M hM ≅ F) := by
  let M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A :=
    Functor.ofOpSequence (X := fun n ↦ (chosenTermModels S F n).module)
      (chosenTransition S F)
  have hM : IsFiniteModuleModel S M := by
    refine ⟨fun n ↦ (chosenTermModels S F n).finite,
      fun n ↦ (chosenTermModels S F n).annihilated, ?_⟩
    intro n
    have hm : M.map (homOfLE (Nat.le_succ n)).op = chosenTransition S F n :=
      Functor.ofOpSequence_map_homOfLE_succ _ _
    dsimp only
    rw [hm]
    exact reduction_torsion_of_powerQuotient S
      (chosenTermModels S F (n + 1)).module (chosenTermModels S F n).module
      (n + 1) (chosenTransition S F n) (chosenTermModels S F n).annihilated
      (powerQuotient_congr _ _ (chosenTermModels S F (n + 1)).iso
        (chosenTermModels S F n).iso _ _ (chosenTransition_compatibility S F n)
        ((exists_powerQuotient_iso_iff _ _ _).mpr (F.property.2.2 n)))
  let η : M ⋙ restrictedTildeFunctor S ⟶ F.obj :=
    NatTrans.ofOpSequence (fun n ↦ (chosenTermModels S F n).iso.hom) (by
      intro n
      simp only [Functor.comp_map, M, Functor.ofOpSequence_map_homOfLE_succ]
      exact chosenTransition_compatibility S F n)
  let e : M ⋙ restrictedTildeFunctor S ≅ F.obj :=
    NatIso.ofComponents (fun n ↦ (chosenTermModels S F n.unop).iso)
      (fun f ↦ η.naturality f)
  let d : restrictedTildeSystem S M ≅ M ⋙ restrictedTildeFunctor S :=
    Functor.isoWhiskerLeft M (Functor.isoWhiskerLeft (tilde.functor (.of S.A))
      (Scheme.Modules.restrictFunctorIsoPullback S.U.ι).symm)
  exact ⟨M, hM, ⟨ObjectProperty.isoMk _ (d ≪≫ e)⟩⟩

end

end Stacks.Algebraization

end
