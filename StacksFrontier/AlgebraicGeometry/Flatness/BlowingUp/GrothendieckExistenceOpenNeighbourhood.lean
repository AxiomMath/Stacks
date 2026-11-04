module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineHomologyEdge
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceProperSupport
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceSectionsOverOpen
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveHomologySplitting
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeDegreeZero
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationNextCohomology
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTopDegree

/-!
# The local analysis of Stacks 0CTH

In Situation [Stacks, Tag 0CTC], let `K` be the object of [Stacks, Tag 0CTD]. The proof of
[Stacks, Tag 0CTH] shows, around a point `x` of `X₀`, that the cohomology sheaves of `K` vanish
outside degree zero and that `H⁰(K)` is of finite presentation. It goes by downward induction on
the top degree `t ≥ 1` of `K` on an affine neighbourhood `U` of `x`:

* the cohomology sheaf `Hᵗ(K)|_U` is of finite type, because `K` is pseudo-coherent relative to
  `A` ([Stacks, Tag 0CTF], [Stacks, Tag 08DN]);
* `Γ(U, Hᵗ(K)) ⊗_A A₀ = 0`: by [Stacks, Tag 0CTG] the derived base change
  `RΓ(U, K) ⊗_A^𝐋 A₀` is `RΓ(U₀, ℱ₀)`, which has no cohomology in degree `t ≠ 0`, while the top
  cohomology of a derived base change is the base change of the top cohomology;
* hence `Hᵗ(K)` vanishes near `x`: its pullback to `U₀ = U ∩ X₀` has no sections, so its support
  misses `U₀` ([Stacks, Tag 056J]).

This file proves these steps.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.isZero_extendScalars_of_comp_eq`: vanishing of a base
  change transported along a square of rings.
* `isFiniteType_homology_restrict_of_isPseudoCoherentFromAfterPushforward`:
  the top cohomology sheaf of a relatively pseudo-coherent object is of finite type.
* `ExistenceSituation.homologySectionsOverIso`:
  `Hⁱ(RΓ(U, E)) = Γ(U, Hⁱ(E))` over an affine open, for `E` bounded below with quasi-coherent
  cohomology.
* `ExistenceSituation.isZero_extendScalars_of_isIso_sectionsOverComparison`:
  the vanishing of `Γ(U, Hᵗ(K)) ⊗_A Aₙ` from the comparison of [Stacks, Tag 0CTG].
* `ExistenceSituation.exists_open_isZero_restrict_of_isZero_extendScalars`:
  the Nakayama step.

## Implementation notes

The derived categories are the standard ones, scoped to each declaration that needs them, as
[Stacks, Tag 09UI] and the derived base-change map of `D(A)` are available at that model only.
The affine edge isomorphism of `Stacks.BoundedBelowEdge` is read at that model in
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.affineEdgeIso`.

## References

* [Stacks Project, Tag 0CTH](https://stacks.math.columbia.edu/tag/0CTH)
* [Stacks Project, Tag 0CTG](https://stacks.math.columbia.edu/tag/0CTG)
* [Stacks Project, Tag 0CTF](https://stacks.math.columbia.edu/tag/0CTF)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open Stacks.AlgebraicGeometry.CoherentTFAE (isQuasicoherent_isFiniteType_of_isFinitePresentation)
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.GrothendieckExistence

/-- **Vanishing of a base change is transported along a square of rings.** Let
`φ ∘ ρ = ψ ∘ π` for ring maps `ρ : A ⟶ B`, `φ : B ⟶ B'`, `π : A ⟶ A'`, `ψ : A' ⟶ B'`, and let `M`
be a `B`-module. If `A' ⊗_A M = 0` then `B' ⊗_B M = 0`: the unit `M ⟶ B' ⊗_B M`, read over `A`,
factors through `A' ⊗_A M`. -/
theorem isZero_extendScalars_of_comp_eq {A A' B B' : Type u} [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] (π : A →+* A') (ρ : A →+* B) (φ : B →+* B') (ψ : A' →+* B')
    (h : φ.comp ρ = ψ.comp π) (M : ModuleCat.{u} B)
    (hM : IsZero ((ModuleCat.extendScalars π).obj ((ModuleCat.restrictScalars ρ).obj M))) :
    IsZero ((ModuleCat.extendScalars φ).obj M) := by
  let adjφ := ModuleCat.extendRestrictScalarsAdj φ
  let adjπ := ModuleCat.extendRestrictScalarsAdj π
  let N := (ModuleCat.extendScalars φ).obj M
  let e : (ModuleCat.restrictScalars ρ).obj ((ModuleCat.restrictScalars φ).obj N) ≅
      (ModuleCat.restrictScalars π).obj ((ModuleCat.restrictScalars ψ).obj N) :=
    (ModuleCat.restrictScalarsComp'App ρ φ (φ.comp ρ) rfl N).symm ≪≫
      ModuleCat.restrictScalarsComp'App π ψ (φ.comp ρ) h N
  have hv : (ModuleCat.restrictScalars ρ).map (adjφ.unit.app M) ≫ e.hom = 0 := by
    have h0 : ∀ w : (ModuleCat.restrictScalars ρ).obj M ⟶
        (ModuleCat.restrictScalars π).obj ((ModuleCat.restrictScalars ψ).obj N), w = 0 :=
      fun w => by
        rw [← (adjπ.homEquiv _ _).apply_symm_apply w, hM.eq_of_src ((adjπ.homEquiv _ _).symm w) 0,
          Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    exact h0 _
  have hu : adjφ.unit.app M = 0 := by
    apply (ModuleCat.restrictScalars ρ).map_injective
    rw [Functor.map_zero, ← cancel_mono e.hom, hv, zero_comp]
  rw [IsZero.iff_id_eq_zero]
  have := adjφ.left_triangle_components M
  rw [hu, Functor.map_zero, zero_comp] at this
  exact this.symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The homology of a pushforward of a restriction, `Hʲ(i_*(E|_U)) ≅ i_*(Hʲ(E)|_U)`. -/
def homologyPushforwardRestrictIso {X Y : Scheme.{u}} (U : X.Opens) (i : (U : Scheme.{u}) ⟶ Y)
    [IsClosedImmersion i] (E : DerivedCategory X.Modules) (j : ℤ) :
    (DerivedCategory.homologyFunctor Y.Modules j).obj
        ((Scheme.Modules.pushforward i).mapDerivedCategory.obj
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E)) ≅
      (Scheme.Modules.pushforward i).obj
        (((DerivedCategory.homologyFunctor X.Modules j).obj E).restrict U.ι) :=
  ((Scheme.Modules.pushforward i).mapDerivedCategoryHomologyIso j).app _ ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso j).app E)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The top cohomology sheaf of a relatively pseudo-coherent object is of finite type**, at one
affine chart: if the restriction of `E` to an open `U` becomes `t`-pseudo-coherent after
pushforward along a closed immersion `i` of `U`, and `E` has no cohomology above `t` on `U`,
then `Hᵗ(E)|_U` is of finite type ([Stacks, Tag 08DN] on the ambient space, and
[Stacks, Tag 01C4] for the closed immersion). Stated at the standard model, at which
[Stacks, Tag 09UI] is. -/
theorem isFiniteType_homology_restrict_of_isPseudoCoherentFromAfterPushforward {X Y : Scheme.{u}}
    (U : X.Opens) (i : (U : Scheme.{u}) ⟶ Y) [IsClosedImmersion i] (E : DerivedCategory X.Modules)
    (t : ℤ) (h : Scheme.Modules.IsPseudoCoherentFromAfterPushforward i
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) t)
    (hv : ∀ j, t < j →
      IsZero (((DerivedCategory.homologyFunctor X.Modules j).obj E).restrict U.ι)) :
    (((DerivedCategory.homologyFunctor X.Modules t).obj E).restrict U.ι).IsFiniteType := by
  rw [Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff] at h
  let E' := (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E
  have hft := RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom.{u, u + 1}
    (X := Y.toRingedSpace) ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E') t h
    fun j hj => ((Scheme.Modules.pushforward i).map_isZero (hv j hj)).of_iso
      (homologyPushforwardRestrictIso U i E j)
  rw [← Scheme.Modules.isFiniteType_pushforward_iff i]
  exact SheafOfModules.IsFiniteType.of_iso hft (homologyPushforwardRestrictIso U i E t)

namespace ExistenceSituation

variable (S : ExistenceSituation.{u})

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The affine edge isomorphism `Hⁱ(RΓ(Y, E)) ≅ Γ(Y, Hⁱ(E))` of `Stacks.BoundedBelowEdge`, read at
the standard model: `Y` affine over `R`, `E` bounded below with quasi-coherent cohomology. -/
def affineEdgeIso {R : Type u} [CommRing R] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R))
    [IsAffine Y] (E : DerivedCategory Y.Modules) (n : ℤ) [E.IsGE n]
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor Y.Modules j).obj E).IsQuasicoherent)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj ((derivedGlobalSectionsOver g).obj E) ≅
      (globalSectionsOver g).obj ((DerivedCategory.homologyFunctor Y.Modules i).obj E) :=
  haveI : IsIso ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison
      (globalSectionsOver g) (derivedGlobalSectionsOver g) (derivedGlobalSectionsOverUnit g)
      (Scheme.Modules.exists_quasiIso_isKInjective Y) i).app E) :=
    Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE
      (globalSectionsOver g) (derivedGlobalSectionsOver g) (derivedGlobalSectionsOverUnit g)
      (Scheme.Modules.exists_quasiIso_isKInjective Y) i E n
      fun j => have := hqc j
        rightAcyclic_globalSectionsOver_of_isQuasicoherent g
          ((DerivedCategory.homologyFunctor _ j).obj E)
  asIso ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison
      (globalSectionsOver g) (derivedGlobalSectionsOver g) (derivedGlobalSectionsOverUnit g)
      (Scheme.Modules.exists_quasiIso_isKInjective Y) i).app E)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The cohomology of `RΓ(U, E)` over an affine open.** For `U` affine and `E` bounded below
with quasi-coherent cohomology sheaves, `Hⁱ(RΓ(U, E)) = Γ(U, Hⁱ(E))` as `A`-modules. -/
def homologySectionsOverIso (U : S.X.left.Opens) (hU : IsAffineOpen U)
    (E : DerivedCategory S.X.left.Modules) (n : ℤ) [E.IsGE n]
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor S.X.left.Modules j).obj E).IsQuasicoherent)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj ((S.sectionsOver U).obj E) ≅
      (globalSectionsOver (U.ι ≫ S.X.hom)).obj
        (((DerivedCategory.homologyFunctor S.X.left.Modules i).obj E).restrict U.ι) := by
  haveI : IsAffine U.toScheme := hU
  let E' := (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E
  let e : ∀ j, (DerivedCategory.homologyFunctor _ j).obj E' ≅
      ((DerivedCategory.homologyFunctor S.X.left.Modules j).obj E).restrict U.ι := fun j =>
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso j).app E
  haveI : E'.IsGE n := by
    rw [DerivedCategory.isGE_iff]
    exact fun j hj => ((Scheme.Modules.restrictFunctor U.ι).map_isZero
      (DerivedCategory.isZero_of_isGE E n j hj)).of_iso (e j)
  have hqc' : ∀ j, ((DerivedCategory.homologyFunctor _ j).obj E').IsQuasicoherent := fun j =>
    haveI := hqc j
    (SheafOfModules.isQuasicoherent.{u} U.toScheme.ringCatSheaf).prop_of_iso (e j).symm
      (isQuasicoherent_restrict ((DerivedCategory.homologyFunctor S.X.left.Modules j).obj E) U)
  exact affineEdgeIso (U.ι ≫ S.X.hom) E' n hqc' i ≪≫
    (globalSectionsOver (U.ι ≫ S.X.hom)).mapIso (e i)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `Uₙ` is affine when `U` is. -/
theorem isAffineOpen_levelOpen (U : S.X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    IsAffineOpen (S.levelOpen U n) := by
  have := S.closedSchemeProjection n
  exact hU.preimage (S.closedImmersion n)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The cohomology of `RΓ(Uₙ, ℱₙ)` above degree zero vanishes** for `U` affine. -/
theorem isZero_homology_levelSectionsOver (U : S.X.left.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj (S.levelSectionsOver U n)) := by
  have : IsAffine (S.levelOpen U n).toScheme := S.isAffineOpen_levelOpen U hU n
  have := S.finitelyPresented n
  have hqcF : ((Scheme.Modules.pullback (S.levelOpen U n).ι).obj (S.F n)).IsQuasicoherent := by
    have : (S.F n).IsQuasicoherent :=
      (isQuasicoherent_isFiniteType_of_isFinitePresentation
        _ (S.finitelyPresented n)).1
    have := isQuasicoherent_restrict (S.F n) (S.levelOpen U n)
    exact (SheafOfModules.isQuasicoherent.{u} _).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (S.levelOpen U n).ι).app (S.F n)) ‹_›
  refine IsZero.of_iso ?_ (affineEdgeIso _ _ 0 (fun j => ?_) i)
  · exact (globalSectionsOver _).map_isZero
      (DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj _ hi)
  · rcases eq_or_ne j 0 with rfl | hj
    · exact (SheafOfModules.isQuasicoherent.{u} _).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm hqcF
    · exact (isQuasicoherent_isFiniteType_of_isFinitePresentation
        _ (isFinitePresentation_of_isZero _
          (DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj _ hj))).1

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `RΓ(U, K)` has no cohomology above `t` if `K` has none over `U`. -/
theorem isLE_sectionsOver (d : S.DerivedLimitQCoh) (U : S.X.left.Opens) (hU : IsAffineOpen U)
    (t : ℤ) (hvan : ∀ i, t < i →
      IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules i).obj d.K).restrict U.ι)) :
    ((S.sectionsOver U).obj d.K).IsLE t := by
  have : d.K.IsGE 0 := d.isGE_zero_and_exists_isLE.1
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact ((globalSectionsOver (U.ι ≫ S.X.hom)).map_isZero (hvan i hi)).of_iso
    (S.homologySectionsOverIso U hU d.K 0 d.quasicoherent i)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The vanishing input of [Stacks, Tag 0CTH] from [Stacks, Tag 0CTG].** Over an affine open
`U` on which `K` has no cohomology above a degree `t ≠ 0`, if the comparison of
[Stacks, Tag 0CTG] at level `n` is invertible then `Γ(U, Hᵗ(K)) ⊗_A Aₙ = 0`. -/
theorem isZero_extendScalars_of_isIso_sectionsOverComparison (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (U : S.X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) (t : ℤ) (ht : t ≠ 0)
    (hvan : ∀ i, t < i →
      IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules i).obj d.K).restrict U.ι))
    (hΦ : IsIso (S.sectionsOverComparison d p U n)) :
    IsZero ((ModuleCat.extendScalars (limit.π S.system (op n)).hom).obj
      ((globalSectionsOver (U.ι ≫ S.X.hom)).obj
        (((DerivedCategory.homologyFunctor S.X.left.Modules t).obj d.K).restrict U.ι))) := by
  have : d.K.IsGE 0 := d.isGE_zero_and_exists_isLE.1
  have := S.isLE_sectionsOver d U hU t hvan
  have := StacksDraft.TopDegreeExtendScalars.isIso_topDegreeComparison
    (limit.π S.system (op n)).hom ((S.sectionsOver U).obj d.K) t
  have h1 : IsZero ((DerivedCategory.homologyFunctor _ t).obj
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
        (limit.π S.system (op n)).hom).functor.obj ((S.sectionsOver U).obj d.K))) :=
    (S.isZero_homology_levelSectionsOver U hU n t ht).of_iso
      ((DerivedCategory.homologyFunctor _ t).mapIso (asIso (S.sectionsOverComparison d p U n)))
  exact (h1.of_iso (asIso (StacksDraft.TopDegreeExtendScalars.topDegreeComparison
    (limit.π S.system (op n)).hom ((S.sectionsOver U).obj d.K) t))).of_iso
      ((ModuleCat.extendScalars _).mapIso
        (S.homologySectionsOverIso U hU d.K 0 d.quasicoherent t)).symm

/-- A module whose support misses an open restricts to zero on it. -/
theorem isZero_restrict_of_disjoint_supp {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
    (h : ∀ x ∈ V, x ∉ SheafOfModules.supp M) : IsZero (M.restrict V.ι) := by
  refine isZero_of_forall_isZero_stalk _ fun y => ?_
  have hy : y ∉ SheafOfModules.supp (M.restrict V.ι) := by
    rw [Scheme.Modules.supp_restrict V.ι M]
    exact h _ y.2
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact ⟨fun a b => sub_eq_zero.mp (not_not.mp fun hab => hy ⟨a - b, hab⟩)⟩

/-- The ring map on global sections of `Uₙ ⟶ U` is its `appTop`. -/
theorem levelOpenImmersion_appTop_eq (U : S.X.left.Opens) (n : ℕ) :
    (S.levelOpenImmersion U n).appLE ⊤ ⊤ le_top = (S.levelOpenImmersion U n).appTop :=
  Scheme.Hom.appLE_eq_app _

/-- **The pullback of `M|_U` to `U₀` vanishes** when `Γ(U, M) ⊗_A A₀ = 0`, for `U` an affine open
and `M|_U` quasi-coherent: the pullback is quasi-coherent on the affine `U₀` and its global
sections are the base change `Γ(U, M) ⊗_A A₀`. -/
theorem isZero_pullback_levelOpenImmersion_of_isZero_extendScalars (U : S.X.left.Opens)
    (hU : IsAffineOpen U) (M : S.X.left.Modules) [(M.restrict U.ι).IsQuasicoherent]
    (hz : IsZero ((ModuleCat.extendScalars (limit.π S.system (op 0)).hom).obj
      ((globalSectionsOver (U.ι ≫ S.X.hom)).obj (M.restrict U.ι)))) :
    IsZero ((Scheme.Modules.pullback (S.levelOpenImmersion U 0)).obj (M.restrict U.ι)) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine (S.levelOpen U 0).toScheme := S.isAffineOpen_levelOpen U hU 0
  let G := M.restrict U.ι
  let l := S.levelOpenImmersion U 0
  have hsq := globalSectionsOver_ringHom_comp_eq l (U.ι ≫ S.X.hom)
    ((S.levelOpen U 0).ι ≫ pullback.snd S.X.hom (baseProjection S.system 0))
    (limit.π S.system (op 0)).hom (S.levelOpenImmersion_comp U 0)
  have h1 := isZero_extendScalars_of_comp_eq (limit.π S.system (op 0)).hom
    ((Scheme.ΓSpecIso (.of ↑(limit S.system))).inv ≫ (U.ι ≫ S.X.hom).appTop).hom
    l.appTop.hom _ hsq _ hz
  have h2 : IsZero ((SheafOfModules.evaluation _ (op ⊤)).obj
      ((Scheme.Modules.pullback l).obj G)) := by
    refine IsZero.of_iso ?_ (affinePullbackSectionsBaseChangeIso l G (isAffineOpen_top _)
      (isAffineOpen_top _) le_top).symm
    rw [S.levelOpenImmersion_appTop_eq U 0]
    exact h1
  have : ((Scheme.Modules.pullback l).obj G).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback l G
  exact Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine _ h2

/-- **The Nakayama step of [Stacks, Tag 0CTH].** Let `U` be an affine open and `M` an
`𝒪_X`-module whose restriction to `U` is quasi-coherent of finite type with
`Γ(U, M) ⊗_A A₀ = 0`. Then `M` vanishes on an open neighbourhood of every point of `U ∩ X₀`: the
pullback of `M|_U` to `U₀ = U ∩ X₀` has no sections, hence vanishes, so its support, which is the
preimage of the support of `M|_U` ([Stacks, Tag 056J]), is empty. -/
theorem exists_open_isZero_restrict_of_isZero_extendScalars (U : S.X.left.Opens)
    (hU : IsAffineOpen U) (M : S.X.left.Modules) [(M.restrict U.ι).IsQuasicoherent]
    [(M.restrict U.ι).IsFiniteType]
    (hz : IsZero ((ModuleCat.extendScalars (limit.π S.system (op 0)).hom).obj
      ((globalSectionsOver (U.ι ≫ S.X.hom)).obj (M.restrict U.ι))))
    (x : S.X.left) (hx0 : x ∈ Set.range (S.closedImmersion 0)) (hxU : x ∈ U) :
    ∃ V : S.X.left.Opens, x ∈ V ∧ V ≤ U ∧ IsZero (M.restrict V.ι) := by
  let G := M.restrict U.ι
  let l := S.levelOpenImmersion U 0
  have h3 : IsZero ((Scheme.Modules.pullback l).obj G) :=
    S.isZero_pullback_levelOpenImmersion_of_isZero_extendScalars U hU M hz
  have h4 : ∀ y, l y ∉ SheafOfModules.supp G := by
    intro y hy
    rw [← Set.mem_preimage, ← Stacks.Modules.supp_pullback] at hy
    obtain ⟨a, ha⟩ := hy
    have hst := (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        y).map_isZero h3
    exact ha (((AddCommGrpCat.isZero_iff_subsingleton).mp hst).elim a 0)
  obtain ⟨z, rfl⟩ := hx0
  have hzU : z ∈ S.levelOpen U 0 := hxU
  have hxG : (⟨S.closedImmersion 0 z, hxU⟩ : U.toScheme) ∉ SheafOfModules.supp G := by
    have := h4 ⟨z, hzU⟩
    have heq : l ⟨z, hzU⟩ = (⟨S.closedImmersion 0 z, hxU⟩ : U.toScheme) :=
      Subtype.ext (morphismRestrict_base_coe (S.closedImmersion 0) U ⟨z, hzU⟩)
    rwa [heq] at this
  let V' : U.toScheme.Opens :=
    ⟨(SheafOfModules.supp G)ᶜ, (SheafOfModules.isClosed_supp G).isOpen_compl⟩
  refine ⟨U.ι ''ᵁ V', ⟨_, hxG, rfl⟩, ?_, ?_⟩
  · simpa [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange V'
  · refine isZero_restrict_of_disjoint_supp M _ ?_
    rintro _ ⟨w, hw, rfl⟩ hwM
    apply hw
    change w ∈ SheafOfModules.supp (M.restrict U.ι)
    rwa [Scheme.Modules.supp_restrict U.ι M]

/-- Vanishing on an open is inherited by smaller opens. -/
theorem isZero_restrict_of_le {X : Scheme.{u}} (M : X.Modules) {W V : X.Opens} (h : W ≤ V)
    (hV : IsZero (M.restrict V.ι)) : IsZero (M.restrict W.ι) :=
  ((Scheme.Modules.restrictFunctor (X.homOfLE h)).map_isZero hV).of_iso
    (restrictRestrictIso M h)

/-- The affine pair `(U, Spec A)` of an affine open `U`. -/
abbrev affinePairTop (U : S.X.left.Opens) (hU : IsAffineOpen U) :
    S.X.left.affineOpens × (limitBase S.system).affineOpens :=
  (⟨U, hU⟩, ⟨⊤, isAffineOpen_top _⟩)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The top cohomology sheaf of `K` over an affine open is of finite type**, granted that `K` is
pseudo-coherent relative to `A`, which is [Stacks, Tag 0CTF]. -/
theorem isFiniteType_homology_restrict (K : DerivedCategory S.X.left.Modules)
    (hpc : S.X.hom.IsPseudoCoherent K) (U : S.X.left.Opens) (hU : IsAffineOpen U) (t : ℤ)
    (hv : ∀ j, t < j →
      IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj K).restrict U.ι)) :
    (((DerivedCategory.homologyFunctor S.X.left.Modules t).obj K).restrict U.ι).IsFiniteType := by
  obtain ⟨N, i, hi, -, hpc'⟩ := Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom
    S.X.hom (hpc t) ⟨U, hU⟩ ⟨⊤, isAffineOpen_top _⟩ (by simp)
  have := hi
  exact isFiniteType_homology_restrict_of_isPseudoCoherentFromAfterPushforward U i K t hpc' hv

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **One more degree of vanishing, on a smaller affine neighbourhood.** If the cohomology sheaves
of `K` vanish above a degree `t ≠ 0` on an affine open `U` around a point `x` of `X₀`, then they
vanish in degrees `≥ t` on a smaller affine open around `x`: `Hᵗ(K)|_U` is of finite type by
[Stacks, Tag 0CTF], has `Γ(U, Hᵗ(K)) ⊗_A A₀ = 0` by [Stacks, Tag 0CTG], hence vanishes near `x`
by the Nakayama step. -/
theorem exists_isAffineOpen_isZero_homology_restrict_le_of_lt (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hpc : S.X.hom.IsPseudoCoherent d.K)
    (hG : ∀ U : S.X.left.Opens, IsAffineOpen U → IsIso (S.sectionsOverComparison d p U 0))
    (x : S.X.left) (hx : x ∈ Set.range (S.closedImmersion 0)) {t : ℤ} (ht : t ≠ 0)
    (U : S.X.left.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
    (hv : ∀ j, t < j →
      IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj d.K).restrict U.ι)) :
    ∃ U' : S.X.left.Opens, IsAffineOpen U' ∧ x ∈ U' ∧ ∀ j : ℤ, t ≤ j →
      IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj d.K).restrict U'.ι) := by
  have := S.isFiniteType_homology_restrict d.K hpc U hU t hv
  have : ((DerivedCategory.homologyFunctor S.X.left.Modules t).obj d.K).IsQuasicoherent :=
    d.quasicoherent t
  have := isQuasicoherent_restrict ((DerivedCategory.homologyFunctor S.X.left.Modules t).obj d.K) U
  have hz := S.isZero_extendScalars_of_isIso_sectionsOverComparison d p U hU 0 t ht hv (hG U hU)
  obtain ⟨V, hxV, hVU, hVz⟩ := S.exists_open_isZero_restrict_of_isZero_extendScalars U hU _
    hz x hx hxU
  obtain ⟨U', hU', hxU', hU'V⟩ := exists_isAffineOpen_mem_and_subset hxV
  refine ⟨U', hU', hxU', fun j hj => ?_⟩
  rcases eq_or_lt_of_le hj with rfl | hjt
  · exact isZero_restrict_of_le _ hU'V hVz
  · exact isZero_restrict_of_le _ (hU'V.trans hVU) (hv j hjt)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The vanishing half of [Stacks, Tag 0CTH], at a point.** Granted [Stacks, Tag 0CTF] (relative
pseudo-coherence of `K`) and [Stacks, Tag 0CTG] at level `0` over affine opens, every point of
`X₀` has an affine open neighbourhood on which the cohomology sheaves of `K` vanish outside degree
zero. The proof is the downward induction on the top degree of the source. -/
theorem exists_isAffineOpen_isZero_homology_restrict (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hpc : S.X.hom.IsPseudoCoherent d.K)
    (hG : ∀ U : S.X.left.Opens, IsAffineOpen U → IsIso (S.sectionsOverComparison d p U 0))
    (x : S.X.left) (hx : x ∈ Set.range (S.closedImmersion 0)) :
    ∃ U : S.X.left.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ j : ℤ, j ≠ 0 →
      IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj d.K).restrict U.ι) := by
  obtain ⟨hge, c, hc⟩ := d.isGE_zero_and_exists_isLE
  have key : ∀ k : ℕ, ∃ U : S.X.left.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ j : ℤ,
      max 1 (c + 1 - k) ≤ j →
        IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj d.K).restrict U.ι) := by
    intro k
    induction k with
    | zero =>
      obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
      refine ⟨U, hU, hxU, fun j hj => ?_⟩
      exact (Scheme.Modules.restrictFunctor U.ι).map_isZero
        (DerivedCategory.isZero_of_isLE d.K c j (by omega))
    | succ k ih =>
      obtain ⟨U, hU, hxU, hvan⟩ := ih
      by_cases ht : c - k < 1
      · exact ⟨U, hU, hxU, fun j hj => hvan j (by omega)⟩
      · obtain ⟨U', hU', hxU', hv⟩ := S.exists_isAffineOpen_isZero_homology_restrict_le_of_lt d p
          hpc hG x hx (t := c - k) (by omega) U hU hxU fun j hj => hvan j (by omega)
        exact ⟨U', hU', hxU', fun j hj => hv j (by omega)⟩
  obtain ⟨U, hU, hxU, hvan⟩ := key c.toNat
  refine ⟨U, hU, hxU, fun j hj => ?_⟩
  rcases lt_or_gt_of_ne hj with hj | hj
  · exact (Scheme.Modules.restrictFunctor U.ι).map_isZero
      (DerivedCategory.isZero_of_isGE d.K 0 j hj)
  · exact hvan j (by omega)

/-- A restriction `resLE` of a morphism locally of finite presentation is locally of finite
presentation. -/
private theorem locallyOfFinitePresentation_resLE_aux {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : LocallyOfFinitePresentation f) (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    LocallyOfFinitePresentation (f.resLE V U e) := by
  have : LocallyOfFinitePresentation (f ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip hf
  delta Scheme.Hom.resLE
  exact MorphismProperty.comp_mem _ _ _ inferInstance this

/-- **A closed immersion into affine space over a base is of finite presentation** as soon as its
composite with the projection to the base is locally of finite presentation
([Stacks, Tag 05B4]). -/
theorem finitePresentation_of_isClosedImmersion_affineSpace {n : ℕ} {Z B : Scheme.{u}}
    (i : Z ⟶ AffineSpace (ULift.{u} (Fin n)) B) [IsClosedImmersion i]
    (h : LocallyOfFinitePresentation (i ≫ (AffineSpace.over (ULift.{u} (Fin n)) B).hom)) :
    FinitePresentation i := by
  refine ⟨?_, inferInstance, inferInstance⟩
  have hA : LocallyOfFinitePresentation (AffineSpace.over (ULift.{u} (Fin n)) B).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (𝔸(ULift.{u} (Fin n); B) ↘ B))
  have : LocallyOfFiniteType (AffineSpace.over (ULift.{u} (Fin n)) B).hom := inferInstance
  exact locallyOfFinitePresentation_of_comp i (AffineSpace.over (ULift.{u} (Fin n)) B).hom

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`H⁰(K)` is of finite presentation over an affine open on which `K` has no cohomology in
positive degrees**, granted that `K` is pseudo-coherent relative to `A` ([Stacks, Tag 0CTF]):
`K` is `(-1)`-pseudo-coherent after pushforward along a closed immersion into an affine space,
which makes its zeroth cohomology there of finite presentation ([Stacks, Tag 08DN]), and finite
presentation descends along the closed immersion ([Stacks, Tag 05B4]). -/
theorem isFinitePresentation_homology_zero_restrict (K : DerivedCategory S.X.left.Modules)
    (hpc : S.X.hom.IsPseudoCoherent K)
    (hqc : ((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj K).IsQuasicoherent)
    (U : S.X.left.Opens) (hU : IsAffineOpen U)
    (hv : ∀ j, 0 < j →
      IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj K).restrict U.ι)) :
    (((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj K).restrict
        U.ι).IsFinitePresentation := by
  obtain ⟨N, i, hi, hio, hpc'⟩ :=
    Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom S.X.hom (hpc (-1))
      ⟨U, hU⟩ ⟨⊤, isAffineOpen_top _⟩ (by simp)
  have := hi
  rw [Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff] at hpc'
  let E' := (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K
  let Y := AffineSpace (ULift.{u} (Fin N)) (⊤ : (limitBase S.system).Opens).toScheme
  have hfp := RingedSpace.isFinitePresentation_homology_of_isPseudoCoherentFrom.{u, u + 1}
    (X := Y.toRingedSpace) ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E') (-1) hpc'
    fun j hj => ((Scheme.Modules.pushforward i).map_isZero (hv j (by omega))).of_iso
      (homologyPushforwardRestrictIso U i K j)
  have hfp' : ((Scheme.Modules.pushforward i).obj
      (((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj K).restrict
          U.ι)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation.{u, u, u} Y.ringCatSheaf).prop_of_iso
      (homologyPushforwardRestrictIso U i K 0) hfp
  have := isQuasicoherent_restrict ((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj K) U
  have hfin : FinitePresentation i :=
    finitePresentation_of_isClosedImmersion_affineSpace i <| by
      rw [hio]
      exact locallyOfFinitePresentation_resLE_aux S.X.hom S.finitePresentation.1 _ _ _
  exact (isFinitePresentation_iff_pushforward_isFinitePresentation i hfin _).mpr hfp'

/-- A point of an open on which a module vanishes is not in the support of the module. -/
theorem not_mem_supp_of_isZero_restrict {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
    (hV : IsZero (M.restrict V.ι)) {x : X} (hx : x ∈ V) : x ∉ SheafOfModules.supp M := by
  intro hxM
  have h := _root_.SheafOfModules.supp_eq_empty_of_isZero hV
  rw [Scheme.Modules.supp_restrict V.ι M] at h
  exact Set.eq_empty_iff_forall_notMem.mp h ⟨x, hx⟩ hxM

/-- **Vanishing glues along a union of opens.** -/
theorem isZero_restrict_iSup {X : Scheme.{u}} (M : X.Modules) {I : Type*} (U : I → X.Opens)
    (hU : ∀ i, IsZero (M.restrict (U i).ι)) : IsZero (M.restrict (⨆ i, U i).ι) :=
  isZero_restrict_of_disjoint_supp M _ fun x hx => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    exact not_mem_supp_of_isZero_restrict M (U i) (hU i) hi

/-- Finite presentation on a smaller open `U ≤ W` is finite presentation of the restriction to
`W` further restricted to the preimage of `U`. -/
theorem isFinitePresentation_restrict_preimage {X : Scheme.{u}} (M : X.Modules) {U W : X.Opens}
    (h : U ≤ W) [(M.restrict U.ι).IsFinitePresentation] :
    ((M.restrict W.ι).restrict (W.ι ⁻¹ᵁ U).ι).IsFinitePresentation := by
  let e : (M.restrict W.ι).restrict (W.ι ⁻¹ᵁ U).ι ≅
      (M.restrict U.ι).restrict (Scheme.Opens.isoOfLE h).hom :=
    ((Scheme.Modules.restrictFunctorComp (W.ι ⁻¹ᵁ U).ι W.ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (Scheme.Opens.isoOfLE_hom_ι h).symm).app M ≪≫
      (Scheme.Modules.restrictFunctorComp (Scheme.Opens.isoOfLE h).hom U.ι).app M
  exact (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso e.symm
    (Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_restrict _ _)

/-- **Finite presentation glues along a union of opens**, for a quasi-coherent module. -/
theorem isFinitePresentation_restrict_iSup {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {I : Type*} (U : I → X.Opens) (hU : ∀ i, (M.restrict (U i).ι).IsFinitePresentation) :
    (M.restrict (⨆ i, U i).ι).IsFinitePresentation := by
  let W := ⨆ i, U i
  have := isQuasicoherent_restrict M W
  refine isFinitePresentation_of_isOpenCover (M.restrict W.ι) (fun i => W.ι ⁻¹ᵁ U i) ?_
    fun i => ?_
  · exact top_unique fun x _ => Opens.mem_iSup.2 ((Opens.mem_iSup (s := U)).1 x.2)
  · have := hU i
    exact isFinitePresentation_restrict_preimage M (le_iSup U i)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Parts (1) and (2) of [Stacks, Tag 0CTH].** Granted [Stacks, Tag 0CTF] (relative
pseudo-coherence of `K`) and [Stacks, Tag 0CTG] at level `0` over affine opens, there is an open
`W ⊇ X₀` on which the cohomology sheaves of `K` vanish outside degree zero and `H⁰(K)` is of
finite presentation. -/
theorem exists_open_isZero_homology_restrict_and_isFinitePresentation (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hpc : S.X.hom.IsPseudoCoherent d.K)
    (hG : ∀ U : S.X.left.Opens, IsAffineOpen U → IsIso (S.sectionsOverComparison d p U 0)) :
    ∃ W : S.X.left.Opens, Set.range (S.closedImmersion 0) ⊆ W ∧
      (∀ j : ℤ, j ≠ 0 →
        IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj d.K).restrict W.ι)) ∧
      (((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K).restrict
        W.ι).IsFinitePresentation := by
  choose U hU hxU hvan using fun x : Set.range (S.closedImmersion 0) =>
    S.exists_isAffineOpen_isZero_homology_restrict d p hpc hG x.1 x.2
  have : ((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K).IsQuasicoherent :=
    d.quasicoherent 0
  refine ⟨⨆ x, U x, fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU _⟩,
    fun j hj => isZero_restrict_iSup _ U fun x => hvan x j hj,
    isFinitePresentation_restrict_iSup _ U fun x => ?_⟩
  exact S.isFinitePresentation_homology_zero_restrict d.K hpc (d.quasicoherent 0) (U x) (hU x)
    fun j hj => hvan x j (by omega)

end ExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
