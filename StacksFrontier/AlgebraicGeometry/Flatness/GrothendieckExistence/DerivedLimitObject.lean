module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.Existence
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.LimitBaseQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.InverseLimitQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UpperBoundedness
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived limit of Situation 0DIB and its coherator

In Situation [Stacks, Tag 0DIB] we have an inverse system of rings `(Aₙ)` with surjective
transition maps whose kernels are locally nilpotent, `A = lim Aₙ`, a scheme `X` proper, flat and
of finite presentation over `A`, its base changes `Xₙ = X ×_{Spec A} Spec Aₙ` viewed as closed
subschemes `iₙ : Xₙ → X`, and a system `(Kₙ, φₙ)` of pseudo-coherent objects `Kₙ` of `D(𝒪_{Xₙ})`
with `φₙ : Liₙ^* Kₙ₊₁ ≅ Kₙ` for the inclusions `tₙ : Xₙ → Xₙ₊₁`. This file builds the object of
[Stacks, Tag 0DIC],

`K = R lim_{D_QCoh(𝒪_X)}(Kₙ) = DQ_X(R lim_{D(𝒪_X)} Kₙ)`,

together with its projections `K ⟶ R(iₙ)_* Kₙ`, and proves the displayed equality. That `K` lies
in `D^-_QCoh(𝒪_X)` is proved, from the uniform bound on the `Kₙ`, in
`StacksFrontier/AlgebraicGeometry/Flatness/GrothendieckExistence/DerivedLimitBoundedAbove.lean`.

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.tower` — the inverse system
  `(R(iₙ)_* Kₙ)` of `D(𝒪_X)` at the model of the situation, with the transition maps
  `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.towerTransition` built from
  the `φₙ`. This is the system the source writes `(Kₙ)`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.towerLocallySmall` — the same
  system at the locally small model, where the coherator lives.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.derivedLimit` — a chosen
  derived limit `R lim_{D(𝒪_X)} Kₙ`, with its projections
  `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.derivedLimitπ`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.qcohTower` — the system in
  `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.coheratorLimit` —
  `DQ_X(R lim_{D(𝒪_X)} Kₙ)`, an object of `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitObject` — **the object
  `K` of [Stacks, Tag 0DIC]**, read in `D(𝒪_X)` at the model of the situation, with its
  projections `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitProjection`
  onto the `R(iₙ)_* Kₙ`.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.surjective_transitionScheme`
  — each `tₙ : Xₙ → Xₙ₊₁` is surjective, the kernels of the `Aₙ₊₁ → Aₙ` being locally nilpotent.
* `AlgebraicGeometry.GrothendieckExistence.affineAmplitudeLE_of_isDerivedLimit` — the Milnor
  sequence of [Stacks, Tag 0D60] bounds the affine hypercohomology of a derived limit from above.
* `DerivedExistenceSituation.limitProjection_comp_towerTransition`
  — the projections are compatible with the tower.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.isDerivedLimit_coheratorLimit`
  — the displayed equality of the tag: `DQ_X(R lim Kₙ)` is a derived limit of the system in
  `D_QCoh(𝒪_X)`.
* `DerivedExistenceSituation.isQuasicoherent_homology_limitObject`
  — `K` has quasi-coherent cohomology sheaves.
* `DerivedExistenceSituation.exists_isLE_coheratorLimit_of_forall_isLE`
  — a uniform upper bound on the `Kₙ` bounds `K` above.

## The shape of the proof

This is the source's proof. The functor `DQ_X` exists because `X` is quasi-compact and
quasi-separated ([Stacks, Tag 0CR0]); being a right adjoint it commutes with products and hence
with derived limits, which is the equality in the statement. `DQ_X` has bounded cohomological
dimension ([Stacks, Tag 0CSA], in the one-sided form
`Stacks.Duality.Coherator.exists_isLE_coherator_obj_of_qcqs`, since the `Kₙ` are not bounded
below), so it suffices to bound the affine hypercohomology of `R lim Kₙ` from above. By the
Milnor sequence of [Stacks, Tag 0D60] it suffices that the `Kₙ` are bounded above independently
of `n`: their cohomology sheaves are quasi-coherent ([Stacks, Tag 08E5]), so over an affine open
their hypercohomology is bounded by the same integer ([Stacks, Tag 08D4] with Serre vanishing,
the content of the source's appeal to [Stacks, Tag 06Z0]). The uniform bound on the `Kₙ` is the
last paragraph of the source's proof, in the companion file.

## Implementation notes

*Models.* The objects `Kₙ` of
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation` live in the derived category
of `𝒪_{Xₙ}`-modules at `CategoryTheory.HasDerivedCategory.standard`, and the tower of their
derived direct images is formed there. The coherator of [Stacks, Tag 0CR0] exists at the locally
small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, so the tower is carried there
along the comparison equivalence `StacksDraft.DerivedModel.modelEquiv` of the two models, its
derived limit is taken and `DQ_X` applied, and the result is carried back. The cohomology sheaves
are unchanged along the comparison (`StacksDraft.DerivedModel.modelHomologyFunctorIso`).

*The transition maps.* The source's `φₙ : Kₙ₊₁ ⟶ Rtₙ,* Kₙ` is the adjoint, under
`Ltₙ^* ⊣ Rtₙ,*`, of the isomorphism `Ltₙ^* Kₙ₊₁ ≅ Kₙ` recorded in the situation; pushed forward
along `iₙ₊₁` and composed with `iₙ₊₁ ∘ tₙ = iₙ` it is the transition map of the system,
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.towerTransition`.

*The choice of `R lim`.* A derived limit is unique up to non-unique isomorphism; one is chosen
(`CategoryTheory.Pretriangulated.exists_isDerivedLimit`), exactly as the source writes
`R lim Kₙ` for one. The countable products it is built from exist in `D(𝒪_X)` at every model,
`𝒪_X`-modules having K-injective resolutions.

## References

* [Stacks Project, Tag 0DIC](https://stacks.math.columbia.edu/tag/0DIC)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Duality Stacks.Duality.Coherator

universe w u

namespace AlgebraicGeometry.GrothendieckExistence

/-! ### The Milnor squeeze, from above -/

/-- **The Milnor squeeze, upper half.** If every term of an inverse system `(Lₙ)` in `D(𝒪_X)` has
its hypercohomology over the affine opens of `X` vanishing above `b`, then a derived limit of the
system has its hypercohomology over the affine opens vanishing above `b + 1`.

For an affine open `U` and `m > b + 1` both `m` and `m - 1` exceed `b`, so in the Milnor short
exact sequence `0 ⟶ R¹lim H^{m-1}(U, Lₙ) ⟶ H^m(U, R lim Lₙ) ⟶ lim H^m(U, Lₙ) ⟶ 0` of
[Stacks, Tag 0D60] the outer terms are a quotient of a product of zero modules and a limit of
zero modules. -/
theorem affineAmplitudeLE_of_isDerivedLimit (X : Scheme.{u})
    (L : ℕᵒᵖ ⥤ DerivedCategory X.Modules) [HasProduct fun n : ℕ => L.obj ⟨n⟩]
    (K : DerivedCategory X.Modules) (hK : IsDerivedLimit L K) (b : ℤ)
    (hL : ∀ n : ℕ, AffineAmplitudeLE X b (L.obj ⟨n⟩)) :
    AffineAmplitudeLE X (b + 1) K := by
  intro U m hm
  obtain ⟨hprod, hlim⟩ := isDerivedLimit_map_derivedSectionsLocallySmall X U.1 L K hK
  have := hprod
  obtain ⟨p, c, -, hseq⟩ := DerivedCategory.isDerivedLimit_homology_shortExact
    (L ⋙ derivedSectionsLocallySmall X U.1) ((derivedSectionsLocallySmall X U.1).obj K) hlim
  obtain ⟨-, i, q, w, -, -, -, hshort⟩ := hseq m
  have hprev : IsZero (∏ᶜ fun n : ℕ =>
      ((L ⋙ derivedSectionsLocallySmall X U.1) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) (m - 1)).obj (op n)) :=
    (limit.isLimit _).isZero_pt ((Functor.isZero_iff _).mpr fun n => hL n.as U (m - 1) (by omega))
  exact hshort.exact.isZero_X₂ ((hprev.of_epi (cokernel.π _)).eq_zero_of_src _)
    (((limit.isLimit _).isZero_pt ((Functor.isZero_iff _).mpr
      fun n => hL n.unop U m (by omega))).eq_zero_of_tgt _)

namespace DerivedExistenceSituation

variable (S : DerivedExistenceSituation.{u})

/-! ### The geometry of the situation -/

/-- The closed immersion `iₙ : Xₙ → X` of the base change at level `n`. -/
abbrev closedImmersion (n : ℕ) : schemeAt S.system S.X n ⟶ S.X.left :=
  schemeProjection S.system S.X n

/-- Each `iₙ : Xₙ → X` is a closed immersion. -/
instance (n : ℕ) : IsClosedImmersion (S.closedImmersion n) := S.closedSchemeProjection n

/-- Each transition `tₙ : Xₙ → Xₙ₊₁` is a closed immersion. -/
instance (n : ℕ) : IsClosedImmersion (S.transitionScheme n) := S.closedTransitionScheme n

/-- The scheme of Situation [Stacks, Tag 0DIB] is quasi-compact, being of finite presentation over
the affine inverse-limit base. -/
instance compactSpace : CompactSpace S.X.left :=
  have : QuasiCompact S.X.hom := S.finitePresentation.quasiCompact
  QuasiCompact.compactSpace_of_compactSpace S.X.hom

/-- The scheme of Situation [Stacks, Tag 0DIB] is quasi-separated over the inverse-limit base,
being of finite presentation there; with
`AlgebraicGeometry.GrothendieckExistence.quasiSeparatedSpace_left_of_quasiSeparated` this makes it
quasi-separated. -/
instance quasiSeparated_hom : QuasiSeparated S.X.hom := S.finitePresentation.quasiSeparated

/-- Each base change `Xₙ` is quasi-compact, being a closed subscheme of `X`. -/
instance compactSpace_schemeAt (n : ℕ) : CompactSpace (schemeAt S.system S.X n) :=
  QuasiCompact.compactSpace_of_compactSpace (S.closedImmersion n)

/-- The affine base at level `n` lies over the affine base at level `n + 1`. -/
theorem baseProjection_eq (n : ℕ) :
    baseProjection S.system n = baseTransition S.system n ≫ baseProjection S.system (n + 1) := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, limit.w]

/-- The transition `Spec Aₙ ⟶ Spec Aₙ₊₁` of affine bases is surjective: its ring map is surjective
with locally nilpotent kernel, and every prime ideal contains every nilpotent element. -/
theorem surjective_baseTransition (n : ℕ) : Function.Surjective (baseTransition S.system n) := by
  intro p
  have hp : (show PrimeSpectrum (S.system.obj (op (n + 1))) from p) ∈ Set.range
      (PrimeSpectrum.comap (S.system.map (homOfLE (Nat.le_succ n)).op).hom) := by
    rw [range_comap_of_surjective _ _ (S.transition_surjective n),
      PrimeSpectrum.mem_zeroLocus]
    intro x hx
    obtain ⟨k, hk⟩ := S.transition_locallyNilpotent n x hx
    exact p.isPrime.mem_of_pow_mem k (by rw [hk]; exact zero_mem _)
  exact hp

/-- The closed subschemes `Xₙ` and `Xₙ₊₁` of `X` have the same underlying set. -/
theorem range_closedImmersion_succ (n : ℕ) :
    Set.range (S.closedImmersion (n + 1)) = Set.range (S.closedImmersion n) := by
  simp only [closedImmersion, schemeProjection, Scheme.Pullback.range_fst]
  rw [S.baseProjection_eq n]
  congr 1
  ext y
  simp only [Set.mem_range, Scheme.Hom.comp_apply]
  refine ⟨fun ⟨x, hx⟩ => ?_, fun ⟨x, hx⟩ => ⟨_, hx⟩⟩
  obtain ⟨z, rfl⟩ := S.surjective_baseTransition n x
  exact ⟨z, hx⟩

/-- **The inclusion `tₙ : Xₙ → Xₙ₊₁` is surjective**: `Xₙ` and `Xₙ₊₁` have the same image in `X`
and `Xₙ₊₁ → X` is injective. -/
theorem surjective_transitionScheme (n : ℕ) :
    Function.Surjective (S.transitionScheme n) := by
  intro x
  obtain ⟨z, hz⟩ : S.closedImmersion (n + 1) x ∈ Set.range (S.closedImmersion n) := by
    rw [← S.range_closedImmersion_succ n]
    exact ⟨x, rfl⟩
  refine ⟨z, (S.closedImmersion (n + 1)).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, S.transition_fst n]
  exact hz

/-! ### The tower `(R(iₙ)_* Kₙ)` at the model of the situation -/

/-- **The inverse system `(R(iₙ)_* Kₙ)` of `D(𝒪_X)`** attached to Situation [Stacks, Tag 0DIB], at
the standard model at which the `Kₙ` are given. Its transition maps are
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.towerTransition`: the image
under `R(iₙ₊₁)_*` of the adjoint `Kₙ₊₁ ⟶ R(tₙ)_* Kₙ` of `φₙ`, followed by
`R(iₙ₊₁)_* R(tₙ)_* = R(iₙ)_*`. The source writes this system `(Kₙ)`, identifying `Kₙ` with its
image in `D(𝒪_X)`. -/
def tower : ℕᵒᵖ ⥤ @DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace))
    SheafOfModules.instCategory (SheafOfModules.instAbelian _) (HasDerivedCategory.standard _) :=
  letI := fun n : ℕ => @HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing (schemeAt S.system S.X n).toRingedSpace))
    SheafOfModules.instCategory (SheafOfModules.instAbelian _)
  letI := @HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace))
    SheafOfModules.instCategory (SheafOfModules.instAbelian _)
  Functor.ofOpSequence (X := fun n =>
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
      (S.levelInclusion n)).obj (S.K n)) S.towerTransition

/-- The map `n + 1 ⟶ n` of the tower `(R(iₙ)_* Kₙ)` is its transition map
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.towerTransition`. -/
lemma tower_map_succ (n : ℕ) :
    S.tower.map (homOfLE (Nat.le_succ n)).op = S.towerTransition n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- `D(𝒪_X)` has countable products, at every model: `𝒪_X`-modules form a Grothendieck abelian
category, so every complex has a K-injective resolution ([Stacks, Tag 079P]), and countable
products of K-injective complexes compute products in the derived category. -/
instance hasProductsOfShape_derivedCategory (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules] :
    HasProductsOfShape ℕ (DerivedCategory X.Modules) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective
    fun K => ⟨(Stacks.Injectives.kInjectiveResolutionFunctor _).obj K,
      (Stacks.Injectives.kInjectiveResolutionInclusion _).app K, inferInstance, inferInstance⟩

/-! ### The tower at the locally small model, and its derived limit -/

/-- **The tower `(R(iₙ)_* Kₙ)` read at the locally small model of `D(𝒪_X)`**, the model at which
the coherator of [Stacks, Tag 0CR0] exists, along the comparison equivalence
`StacksDraft.DerivedModel.modelEquiv` of the two models. -/
def towerLocallySmall : ℕᵒᵖ ⥤ DerivedCategory S.X.left.Modules :=
  S.tower ⋙ (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard S.X.left.Modules)
    (Scheme.Modules.hasDerivedCategory S.X.left)).functor

/-- **`R lim_{D(𝒪_X)} Kₙ`**: a chosen derived limit of the system `(R(iₙ)_* Kₙ)` in `D(𝒪_X)`. A
derived limit is unique up to non-unique isomorphism; this is one of them, as `R lim Kₙ` is in
the source. -/
def derivedLimit : DerivedCategory S.X.left.Modules :=
  (exists_isDerivedLimit S.towerLocallySmall).choose

/-- `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.derivedLimit` is a derived
limit of the system `(R(iₙ)_* Kₙ)`. -/
theorem isDerivedLimit_derivedLimit : IsDerivedLimit S.towerLocallySmall S.derivedLimit :=
  (exists_isDerivedLimit S.towerLocallySmall).choose_spec

/-- The map `R lim Kₙ ⟶ ∏ R(iₙ)_* Kₙ` of a distinguished triangle presenting the derived limit
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.derivedLimit`. -/
def derivedLimitToProduct :
    S.derivedLimit ⟶ ∏ᶜ fun n : ℕ => S.towerLocallySmall.obj (op n) :=
  S.isDerivedLimit_derivedLimit.choose

/-- **The projection `R lim Kₙ ⟶ R(iₙ)_* Kₙ`** out of the derived limit. -/
def derivedLimitπ (n : ℕ) : S.derivedLimit ⟶ S.towerLocallySmall.obj (op n) :=
  S.derivedLimitToProduct ≫ Pi.π _ n

/-- The projections out of the derived limit are compatible with the transition maps: the first
two maps of a distinguished triangle compose to zero. -/
theorem derivedLimitπ_comp_map (n : ℕ) :
    S.derivedLimitπ (n + 1) ≫ S.towerLocallySmall.map (homOfLE (Nat.le_succ n)).op =
      S.derivedLimitπ n := by
  obtain ⟨δ, hT⟩ := S.isDerivedLimit_derivedLimit.choose_spec
  have h := congrArg (· ≫ Pi.π (fun n : ℕ => S.towerLocallySmall.obj (op n)) n)
    (comp_distTriang_mor_zero₁₂ _ hT)
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₁,
    Triangle.mk_mor₂, Category.assoc, limit.lift_π, Fan.mk_π_app, zero_comp,
    Preadditive.comp_sub] at h
  simp only [derivedLimitπ, Category.assoc]
  exact (sub_eq_zero.mp h).symm

/-! ### The terms of the system -/

/-- **The cohomology sheaves of `R(iₙ)_* Kₙ` are the direct images of those of `Kₙ`**, direct
image along a closed immersion being exact: the derived direct image is the functor induced on
derived categories by the exact functor `iₙ,*`
(`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`), which commutes with
cohomology. -/
def homologyTowerLocallySmallObjIso (n : ℕ) (j : ℤ) :
    letI := HasDerivedCategory.standard (schemeAt S.system S.X n).Modules
    (DerivedCategory.homologyFunctor S.X.left.Modules j).obj (S.towerLocallySmall.obj (op n)) ≅
      (Scheme.Modules.pushforward (S.closedImmersion n)).obj
        ((DerivedCategory.homologyFunctor (schemeAt S.system S.X n).Modules j).obj (S.K n)) :=
  letI := HasDerivedCategory.standard (schemeAt S.system S.X n).Modules
  letI := HasDerivedCategory.standard S.X.left.Modules
  (StacksDraft.DerivedModel.modelHomologyFunctorIso (HasDerivedCategory.standard _)
      (Scheme.Modules.hasDerivedCategory S.X.left) j).app (S.tower.obj (op n)) ≪≫
    (DerivedCategory.homologyFunctor S.X.left.Modules j).mapIso
      ((Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
        (Scheme.Modules.pushforward (S.closedImmersion n))).symm.app (S.K n)) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.pushforward (S.closedImmersion n)) j).app (S.K n)

/-- **The terms of the system have quasi-coherent cohomology.** The cohomology sheaves of the
pseudo-coherent `Kₙ` are quasi-coherent ([Stacks, Tag 08E5]), and direct image along the closed
immersion `iₙ`, an affine morphism, preserves quasi-coherence ([Stacks, Tag 02KG]). -/
theorem isQuasicoherent_homology_towerLocallySmall_obj (n : ℕ) (j : ℤ) :
    ((DerivedCategory.homologyFunctor S.X.left.Modules j).obj
      (S.towerLocallySmall.obj (op n))).IsQuasicoherent := by
  let := HasDerivedCategory.standard (schemeAt S.system S.X n).Modules
  let := HasDerivedCategory.standard
    (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace)
  have : ((DerivedCategory.homologyFunctor (schemeAt S.system S.X n).Modules j).obj
      (S.K n)).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent (schemeAt S.system S.X n) (S.K n)
      (S.pseudoCoherent n) j
  exact (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf).prop_of_iso
    (S.homologyTowerLocallySmallObjIso n j).symm
    (Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
      (S.closedImmersion n) _)

/-- **An upper bound on `Kₙ` is one on `R(iₙ)_* Kₙ`**, direct image along a closed immersion
being exact. -/
theorem isLE_towerLocallySmall_obj (n : ℕ) (a : ℤ)
    (h :
      letI := HasDerivedCategory.standard
        (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace)
      (S.K n).IsLE a) :
    (S.towerLocallySmall.obj (op n)).IsLE a := by
  let := HasDerivedCategory.standard (schemeAt S.system S.X n).Modules
  let := HasDerivedCategory.standard
    (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace)
  refine (DerivedCategory.isLE_iff _ a).2 fun j hj => ?_
  exact ((Scheme.Modules.pushforward (S.closedImmersion n)).map_isZero
    (@DerivedCategory.isZero_of_isLE _ _ _ _ (S.K n) a j hj h)).of_iso
      (S.homologyTowerLocallySmallObjIso n j)

/-! ### The object `K` of Stacks 0DIC -/

/-- **The system `(Kₙ)` in `D_QCoh(𝒪_X)`**: the system `(R(iₙ)_* Kₙ)`, whose terms have
quasi-coherent cohomology, at the locally small model. Its derived limit is the
`R lim_{D_QCoh(𝒪_X)}(Kₙ)` of [Stacks, Tag 0DIC]. -/
def qcohTower : ℕᵒᵖ ⥤ quasiCoherentDerivedCategory S.X.left :=
  ObjectProperty.lift _ S.towerLocallySmall fun n j =>
    S.isQuasicoherent_homology_towerLocallySmall_obj n.unop j

/-- **`DQ_X(R lim_{D(𝒪_X)} Kₙ)`**, the coherator of [Stacks, Tag 0CR0] applied to the chosen
derived limit `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.derivedLimit`: the
object `K` of [Stacks, Tag 0DIC] as an object of `D_QCoh(𝒪_X)`, at the locally small model at which
the coherator exists. -/
def coheratorLimit : quasiCoherentDerivedCategory S.X.left :=
  (derivedCoherator S.X.left).obj S.derivedLimit

/-- **The object `K = DQ_X(R lim_{D(𝒪_X)} Kₙ)` of [Stacks, Tag 0DIC]**, as an object of `D(𝒪_X)`
at the model of the situation: the image of
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.coheratorLimit` under the
comparison equivalence of the locally small model with the standard one. -/
def limitObject :
    @DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace) _ _
      (HasDerivedCategory.standard _) :=
  (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard S.X.left.Modules)
    (Scheme.Modules.hasDerivedCategory S.X.left)).inverse.obj
      ((quasiCoherentι S.X.left).obj S.coheratorLimit)

/-- **The projection `K ⟶ R(iₙ)_* Kₙ`**, at the model of the situation: the counit
`ι DQ_X(R lim Kₙ) ⟶ R lim Kₙ` of the coherator adjunction followed by the projection of the derived
limit, carried back along the comparison equivalence of the two models (the adjoint, under that
equivalence, of the composite at the locally small model). -/
def limitProjection (n : ℕ) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing (schemeAt S.system S.X n).toRingedSpace))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace))
    S.limitObject ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        (S.levelInclusion n)).obj (S.K n) :=
  ((StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard S.X.left.Modules)
      (Scheme.Modules.hasDerivedCategory S.X.left)).symm.toAdjunction.homEquiv _
        (S.tower.obj (op n))).symm
    ((derivedCoheratorAdjunction S.X.left).counit.app S.derivedLimit ≫ S.derivedLimitπ n)

/-- **The projections `K ⟶ R(iₙ)_* Kₙ` are compatible with the tower.** -/
theorem limitProjection_comp_towerTransition (n : ℕ) :
    S.limitProjection (n + 1) ≫ S.towerTransition n = S.limitProjection n := by
  rw [← S.tower_map_succ n]
  refine (Adjunction.homEquiv_naturality_right_symm _ _ _).symm.trans ?_
  exact congrArg _ ((Category.assoc _ _ _).trans (congrArg _ (S.derivedLimitπ_comp_map n)))

/-- **The displayed equality of [Stacks, Tag 0DIC]**:
`R lim_{D_QCoh(𝒪_X)}(Kₙ) = DQ_X(R lim_{D(𝒪_X)} Kₙ)`. The object
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.coheratorLimit` is a derived
limit of the system `(Kₙ)` in `D_QCoh(𝒪_X)`; the existence of the product it is built from is part
of the conclusion.

This is the source's argument: `DQ_X` is a right adjoint, so it commutes with products, and it is
exact, so it carries a derived-limit triangle to a derived-limit triangle
(`Stacks.Duality.Coherator.isDerivedLimit_coherator_obj`). -/
theorem isDerivedLimit_coheratorLimit :
    ∃ _ : HasProduct fun n : ℕ => S.qcohTower.obj (op n),
      IsDerivedLimit S.qcohTower S.coheratorLimit :=
  @Stacks.Duality.Coherator.isDerivedLimit_coherator_obj S.X.left
    (inferInstance : HasDerivedCategory S.X.left.Modules) (derivedCoherator S.X.left)
    (derivedCoheratorAdjunction S.X.left)
    (inferInstance : (derivedCoherator S.X.left).CommShift ℤ)
    (inferInstance : (derivedCoheratorAdjunction S.X.left).IsTriangulated) S.qcohTower
    (inferInstance : HasProduct fun n : ℕ => S.towerLocallySmall.obj (op n)) S.derivedLimit
    S.isDerivedLimit_derivedLimit

/-- **`DQ_X(R lim Kₙ)` is bounded above as soon as the `Kₙ` are, uniformly.** If `a` bounds every
`Kₙ` from above, then the cohomology sheaves of `DQ_X(R lim Kₙ)` vanish above `a + 1 + N`, where
`N` is the integer of [Stacks, Tag 0CSA] for `X` (in its one-sided form,
`Stacks.Duality.Coherator.exists_isLE_coherator_obj_of_qcqs`).

The terms `R(iₙ)_* Kₙ` have quasi-coherent cohomology vanishing above `a`, so their affine
hypercohomology vanishes above `a` (`Stacks.Duality.Coherator.affineAmplitudeLE_of_isLE`); the
Milnor sequence moves that to `a + 1` for the derived limit
(`AlgebraicGeometry.GrothendieckExistence.affineAmplitudeLE_of_isDerivedLimit`); and the bounded
cohomological dimension of the coherator concludes. -/
theorem exists_isLE_coheratorLimit_of_forall_isLE (a : ℤ)
    (ha : ∀ n : ℕ,
      letI := HasDerivedCategory.standard
        (StrictlyPerfect.OXMod.{u, u, u} (schemeAt S.system S.X n).toRingedSpace)
      (S.K n).IsLE a) :
    ∃ c : ℤ, ((quasiCoherentι S.X.left).obj S.coheratorLimit).IsLE c := by
  obtain ⟨N, hN⟩ := exists_isLE_coherator_obj_of_qcqs S.X.left (derivedCoherator S.X.left)
    (derivedCoheratorAdjunction S.X.left)
  exact ⟨a + 1 + N, hN (a + 1) S.derivedLimit
    (affineAmplitudeLE_of_isDerivedLimit S.X.left S.towerLocallySmall S.derivedLimit
      S.isDerivedLimit_derivedLimit a fun n =>
        affineAmplitudeLE_of_isLE S.X.left _ (S.isQuasicoherent_homology_towerLocallySmall_obj n)
          a (S.isLE_towerLocallySmall_obj n a (ha n)))⟩

/-- The cohomology sheaves of `K`, at the model of the situation, are those of
`DQ_X(R lim Kₙ)` at the locally small model. -/
def homologyLimitObjectIso (j : ℤ) :
    letI := HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace)
    (DerivedCategory.homologyFunctor _ j).obj S.limitObject ≅
      (@DerivedCategory.homologyFunctor S.X.left.Modules _ _
        (Scheme.Modules.hasDerivedCategory S.X.left) j).obj
          ((quasiCoherentι S.X.left).obj S.coheratorLimit) :=
  ((StacksDraft.DerivedModel.modelHomologyFunctorIso (HasDerivedCategory.standard _)
      (Scheme.Modules.hasDerivedCategory S.X.left) j).app S.limitObject).symm ≪≫
    (@DerivedCategory.homologyFunctor S.X.left.Modules _ _
      (Scheme.Modules.hasDerivedCategory S.X.left) j).mapIso
      ((StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard S.X.left.Modules)
        (Scheme.Modules.hasDerivedCategory S.X.left)).counitIso.app
          ((quasiCoherentι S.X.left).obj S.coheratorLimit))

/-- **`K` lies in `D_QCoh(𝒪_X)`**: its cohomology sheaves are quasi-coherent. -/
theorem isQuasicoherent_homology_limitObject (j : ℤ) :
    letI := HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace)
    ((DerivedCategory.homologyFunctor _ j).obj S.limitObject).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf).prop_of_iso
    (S.homologyLimitObjectIso j).symm (S.coheratorLimit.2 j)

/-- An upper bound on `DQ_X(R lim Kₙ)` is one on `K`. -/
theorem isLE_limitObject_of_isLE (c : ℤ)
    (h : ((quasiCoherentι S.X.left).obj S.coheratorLimit).IsLE c) :
    letI := HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace)
    S.limitObject.IsLE c := by
  let := HasDerivedCategory.standard
    (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace)
  refine (DerivedCategory.isLE_iff _ c).2 fun j hj => ?_
  exact (@DerivedCategory.isZero_of_isLE _ _ _ _ _ c j hj h).of_iso
    (S.homologyLimitObjectIso j)

end DerivedExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
