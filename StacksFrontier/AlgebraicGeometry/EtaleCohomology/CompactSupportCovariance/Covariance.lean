module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCovariance.DerivedTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InverseImageTorsion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FlatLength
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Covariance of compactly supported cohomology ([Stacks, Tag 0GKS])

Let `k` be a field and `f : X ⟶ Y` a morphism of separated schemes of finite type over `k`, with
structure morphisms `p = f ≫ q : X ⟶ Spec k` and `q : Y ⟶ Spec k`. Suppose that

1. `f` is étale, or
2. `f` is flat and quasi-finite, or
3. `f` is quasi-finite and `Y` is geometrically unibranch, or
4. `f` is quasi-finite and there is a weighting `w : X → ℤ` of `f`.

Let `Λ` be a ring and `K` an object of `D⁺_tors(Y_étale, Λ)`, or of `D(Y_étale, Λ)` if `Λ` is
torsion. Then compactly supported cohomology is covariant along `f`: there is a trace map
`Tr_{f, w, K} : f_! f^{-1}K ⟶ K`, and with it the map

`RΓ_c(X, f^{-1}K) = RΓ(Spec k, Rp_! f^{-1}K) = RΓ(Spec k, Rq_! f_! f^{-1}K)`
`  ⟶ RΓ(Spec k, Rq_! K) = RΓ_c(Y, K)`,

the middle identification being `Rp_! = Rq_! ∘ Rf_!` ([Stacks, Tag 0F7J]) and `Rf_! = f_!`
([Stacks, Tag 0GKM]). For a torsion ring this gives `Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ)`.

The weightings of cases (1)–(3) are those of [Stacks, Tag 0GKI] (the canonical weighting of a
flat, locally quasi-finite morphism locally of finite presentation, [Stacks, Tag 0F3D]) and
[Stacks, Tag 0GKJ] (the generic separable degree, [Stacks, Tag 0F3E]); the morphism `f` is
locally of finite presentation and `Y` is locally Noetherian since both are of finite type over a
field.

## Main definitions

* `Stacks.EtaleCohomology.compactlySupportedCohomologyTraceOfWeighting` and its cases
  `…OfEtale`, `…OfFlat` and `compactlySupportedCohomologyGenericSeparableDegreeTrace`: the natural
  transformation `RΓ_c(X, f^{-1}K) ⟶ RΓ_c(Y, K)` of functors of `K ∈ D⁺_tors(Y_étale, Λ)`.
  Case (3) uses the generic separable degree `AlgebraicGeometry.genericSeparableDegreeWeight`;
  the older `…OfGeometricallyUnibranch` maps use an unspecified weighting and are not the
  canonical ones.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyUnboundedTraceOfWeighting` and its cases:
  the same for `K ∈ D(Y_étale, Λ)` and `Λ` torsion.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyConstantTraceOfWeighting` and its cases:
  `Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ)` for `Λ` torsion.

## Implementation notes

`RΓ_c` is computed through arbitrary compactifications `jp` of `p` and `jq` of `q`, as in
`Stacks.EtaleCohomology.compactlySupportedCohomology`. The functor `f_! = Rf_!` is computed
through a compactification of `f` finite over `Y`
(`Stacks.EtaleCohomology.covarianceCompactification`, Zariski's main theorem
[Stacks, Tag 05K0]), for which `Rf_! = f̄_* ∘ j_!` is the direct image
with compact support of [Stacks, Tag 0F6R] ([Stacks, Tag 0GKM]) and the trace map of
[Stacks, Tag 0GKG] is defined (`Stacks.EtaleCohomology.derivedLowerShriekWeightedTrace`).
The coefficient ring lives in the universe of the schemes, `Λ : Type u`, where that trace map
is available on Mathlib's small étale sites.

## References

* [Stacks Project, Tag 0GKS](https://stacks.math.columbia.edu/tag/0GKS)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
* [Stacks Project, Tag 0GKM](https://stacks.math.columbia.edu/tag/0GKM)
* [Stacks Project, Tag 0GKI](https://stacks.math.columbia.edu/tag/0GKI)
* [Stacks Project, Tag 0GKJ](https://stacks.math.columbia.edu/tag/0GKJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace AlgebraicGeometry.CompactificationOf

/-- **A compactification finite over the base** ([Stacks, Tag 05K0]): a quasi-finite separated
morphism `f : X ⟶ Y` with `Y` quasi-compact and quasi-separated factors as an open immersion
followed by a finite morphism. -/
@[ega "IV 18.12.13", sga "4 XVII 3.2.2" "more general"]
theorem exists_isFinite_toBase_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    ∃ jf : CompactificationOf (Over.mk f), IsFinite jf.toBase := by
  obtain ⟨T, i, π, hi, -, hπ, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization f
  have : IsFinite π := hπ
  exact ⟨⟨StructuredArrow.mk (Y := Over.mk π) (Over.homMk i hfac.symm),
    ⟨hi, (inferInstance : IsProper π)⟩⟩, hπ⟩

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions (`Field ?k`, `QuasiCompact ?f`, ...) match every goal and send instance search
-- through `Submodule ?R ?R`; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-! ### Inverse image on `D⁺_tors` -/

section Torsion

variable (Λ : Type w) [Ring Λ]

/-- Inverse image of sheaves of `Λ`-modules preserves torsion sheaves, at every coefficient
universe. -/
@[sga "4 IX 1.2" "(iv)"]
theorem isTorsionEtaleModule_etaleModuleInverseImage_obj_univ {W X : Scheme.{u}} (e : W ⟶ X)
    (M : EtaleModules.{u, w} Λ X) (hM : IsTorsionEtaleModule.{u, w} Λ X M) :
    IsTorsionEtaleModule.{u, w} Λ W ((etaleModuleInverseImage.{u, w} Λ e).obj M) :=
  Stacks.Torsion.torsionSheafProperty_of_iso W.smallEtaleTopology
    ((etaleModuleForgetInverseImageIso.{u, w} Λ e).app M)
    (torsionSheafProperty_etaleAbelianInverseImage.{u, w} e _ hM)

/-- **Inverse image preserves `D⁺_tors`**, at every coefficient universe. -/
theorem isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj_univ {W X : Scheme.{u}}
    (e : W ⟶ X) (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ X))
    (hK : isTorsionPlus.{u, w} Λ X K) :
    isTorsionPlus.{u, w} Λ W ((etaleModuleDerivedInverseImagePlus.{u, w} Λ e).obj K) := fun q =>
  IsTorsionEtaleModule.of_iso_univ Λ
    (etaleModuleDerivedInverseImagePlusHomologyIsoUniv Λ e K q).symm
    (isTorsionEtaleModule_etaleModuleInverseImage_obj_univ Λ e _ (hK q))

/-- The inverse image `e⁻¹ : D⁺_tors(X_étale, Λ) ⥤ D⁺_tors(W_étale, Λ)`. -/
def etaleModuleDerivedInverseImageTorsion {W X : Scheme.{u}} (e : W ⟶ X) :
    (isTorsionPlus.{u, w} Λ X).FullSubcategory ⥤ (isTorsionPlus.{u, w} Λ W).FullSubcategory :=
  ObjectProperty.lift _
    ((isTorsionPlus.{u, w} Λ X).ι ⋙ etaleModuleDerivedInverseImagePlus.{u, w} Λ e)
    (fun K => isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj_univ Λ e K.obj K.property)

end Torsion

section Covariance

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (q : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
  [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
  [LocallyOfFiniteType (f ≫ q)] [QuasiCompact (f ≫ q)] [IsSeparated (f ≫ q)]
  (jp : CompactificationOf (Over.mk (f ≫ q))) (jq : CompactificationOf (Over.mk q))
  (Λ : Type u) [Ring Λ]

omit [IsSeparated q] in
include q in
/-- A quasi-finite morphism of separated schemes of finite type over a field has a
compactification finite over the target (Zariski's main theorem, [Stacks, Tag 05K0]). -/
@[ega "III 4.4.12" "special case"]
theorem exists_isFinite_toBase_of_covariance [LocallyQuasiFinite f] :
    ∃ jf : CompactificationOf (Over.mk f), IsFinite jf.toBase :=
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ q)
  haveI : IsSeparated f := IsSeparated.of_comp f q
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f q
  haveI : QuasiCompact f := quasiCompact_of_compactSpace f
  CompactificationOf.exists_isFinite_toBase_of_locallyQuasiFinite f

/-- A chosen compactification of the quasi-finite morphism `f` whose structure morphism to `Y` is
finite. -/
def covarianceCompactification [LocallyQuasiFinite f] : CompactificationOf (Over.mk f) :=
  (exists_isFinite_toBase_of_covariance k q f).choose

/-- The structure morphism to `Y` of `covarianceCompactification k q f` is finite. -/
instance [LocallyQuasiFinite f] : IsFinite (covarianceCompactification k q f).toBase :=
  (exists_isFinite_toBase_of_covariance k q f).choose_spec

omit [QuasiCompact q] [IsSeparated q] in
include q in
/-- `Y` is locally Noetherian, being of finite type over a field. -/
theorem isLocallyNoetherian_of_covariance : IsLocallyNoetherian Y :=
  LocallyOfFiniteType.isLocallyNoetherian q

variable {w : X → ℤ} (hw : IsWeighting f w)

/-! ### Case (4): a weighting -/

include hw in
/-- **Stacks Project, Tag 0GKS**, case (4), on `D⁺_tors`. For `f : X ⟶ Y` a quasi-finite
morphism of separated schemes of finite type over a field `k` and `w` a weighting of `f`, the
natural map

`RΓ_c(X, f^{-1}K) = RΓ(Spec k, Rp_! f^{-1}K) = RΓ(Spec k, Rq_! f_! f^{-1}K)`
`  ⟶ RΓ(Spec k, Rq_! K) = RΓ_c(Y, K)`

of `K ∈ D⁺_tors(Y_étale, Λ)`: the middle identification is [Stacks, Tag 0F7J]
(`Stacks.EtaleCohomology.derivedLowerShriekCompIsoUniv`), with `f_! = Rf_!` computed through a
compactification of `f` finite over `Y`, and the arrow is `RΓ(Spec k, Rq_! Tr_{f, w, K})` for the
trace map `Stacks.EtaleCohomology.derivedLowerShriekWeightedTrace`. -/
@[stacks 0GKS "case (4), K in D⁺_tors(Y_étale, Λ): the map RΓ_c(X, f⁻¹K) ⟶ RΓ_c(Y, K), natural \
in K, defined as RΓ(Spec k, Rp_! f⁻¹K) = RΓ(Spec k, Rq_! f_! f⁻¹K) ⟶ RΓ(Spec k, Rq_! K) with \
Rq_! ∘ f_! = Rp_! by 0F7J and the trace Tr_{f,w,K}; f quasi-finite, w a weighting of f, X and Y \
separated of finite type over the field k, p = f ≫ q", sga "4 XVII 6.2.7" "more general"]
def compactlySupportedCohomologyTraceOfWeighting [LocallyQuasiFinite f] :
    (isTorsionPlus.{u, u} Λ Y).ι ⋙ etaleModuleDerivedInverseImagePlus.{u, u} Λ f ⋙
        compactlySupportedCohomology.{u, u} k (f ≫ q) jp Λ ⟶
      (isTorsionPlus.{u, u} Λ Y).ι ⋙ compactlySupportedCohomology.{u, u} k q jq Λ :=
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ q)
  haveI : QuasiSeparated (f ≫ q) := IsSeparated.instQuasiSeparated (f ≫ q)
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (f ≫ q)
  haveI : IsSeparated f := IsSeparated.of_comp f q
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f q
  let jf := covarianceCompactification k q f
  Functor.whiskerLeft (etaleModuleDerivedInverseImageTorsion.{u, u} Λ f)
      (Functor.whiskerRight (derivedLowerShriekCompIsoUniv.{u, u} Λ f q jf jq jp).hom
        (etaleModuleDerivedGlobalSections.{u, u} Λ (Spec (.of k)))) ≫
    Functor.whiskerLeft (isTorsionPlus.{u, u} Λ Y).ι
      (Functor.whiskerRight (derivedLowerShriekWeightedTrace Λ f jf hw)
        (derivedLowerShriek.{u, u} q jq Λ ⋙
          etaleModuleDerivedGlobalSections.{u, u} Λ (Spec (.of k))))

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

include hw hΛ in
/-- **Stacks Project, Tag 0GKS**, case (4), on `D(Y_étale, Λ)` for a torsion ring `Λ`: the
natural map `RΓ_c(X, f^{-1}K) ⟶ RΓ_c(Y, K)` of `K ∈ D(Y_étale, Λ)`, through
`Rp_! = Rq_! ∘ f_!` ([Stacks, Tag 0F7J],
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`) and `RΓ(Spec k, Rq_! Tr_{f, w, K})`
for the trace map `Stacks.EtaleCohomology.derivedLowerShriekUnboundedWeightedTrace`. -/
@[stacks 0GKS "case (4), K in D(Y_étale, Λ) with Λ torsion: the map RΓ_c(X, f⁻¹K) ⟶ RΓ_c(Y, K), \
natural in K, defined as RΓ(Spec k, Rp_! f⁻¹K) = RΓ(Spec k, Rq_! f_! f⁻¹K) ⟶ RΓ(Spec k, Rq_! K) \
with Rq_! ∘ f_! = Rp_! by 0F7J and the trace Tr_{f,w,K}", sga "4 XVII 6.2.7" "partial"]
def compactlySupportedCohomologyUnboundedTraceOfWeighting [LocallyQuasiFinite f] :
    (etaleModuleInverseImage.{u, u} Λ f).mapDerivedCategory ⋙
        compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ ⟶
      compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ :=
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ q)
  haveI : QuasiSeparated (f ≫ q) := IsSeparated.instQuasiSeparated (f ≫ q)
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (f ≫ q)
  haveI : IsSeparated f := IsSeparated.of_comp f q
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f q
  let jf := covarianceCompactification k q f
  Functor.whiskerLeft (etaleModuleInverseImage.{u, u} Λ f).mapDerivedCategory
      (Functor.whiskerRight (derivedLowerShriekUnboundedCompIso.{u, u} Λ hΛ f q jf jq jp).hom
        (etaleModuleDerivedGlobalSectionsUnbounded.{u, u} Λ (Spec (.of k)))) ≫
    Functor.whiskerRight (derivedLowerShriekUnboundedWeightedTrace Λ f jf hw)
      (derivedLowerShriekUnbounded.{u, u} q jq Λ ⋙
        etaleModuleDerivedGlobalSectionsUnbounded.{u, u} Λ (Spec (.of k)))

/-- `f⁻¹ Λ_Y ≅ Λ_X` in `D(X_étale, Λ)`, for the constant sheaves with value `Λ` placed in degree
zero. -/
def etaleModuleDerivedInverseImageConstantIso :
    (etaleModuleInverseImage.{u, u} Λ f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ Y) 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) ≅
      (DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ X) 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (ULift.{u + 1} Λ))) :=
  ((etaleModuleInverseImage.{u, u} Λ f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ X) 0).mapIso
      ((etaleModuleInverseImageConstantIso.{u, u} Λ f).app (ModuleCat.of Λ (ULift.{u + 1} Λ)))

include hw hΛ in
/-- **Stacks Project, Tag 0GKS**, case (4), the constant coefficients: for a torsion ring `Λ`,
`Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ)`, the map `RΓ_c(X, f^{-1}Λ) ⟶ RΓ_c(Y, Λ)` at the constant sheaf
`Λ` read through `f^{-1}Λ_Y = Λ_X`. -/
@[stacks 0GKS "case (4), the arrow Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ) for a torsion ring Λ",
  sga "4 XVII 6.2.7" "special case"]
def compactlySupportedCohomologyConstantTraceOfWeighting [LocallyQuasiFinite f] :
    (compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ X) 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) ⟶
      (compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ Y) 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) :=
  (compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ).map
      (etaleModuleDerivedInverseImageConstantIso f Λ).inv ≫
    (compactlySupportedCohomologyUnboundedTraceOfWeighting k q f jp jq Λ hw hΛ).app _

omit hw

/-! ### Cases (1) and (2): étale, and flat quasi-finite -/

omit [QuasiCompact q] [IsSeparated q] [QuasiCompact (f ≫ q)] [IsSeparated (f ≫ q)] in
include q in
/-- In cases (1) and (2) of [Stacks, Tag 0GKS] the canonical weighting of [Stacks, Tag 0GKI],
[Stacks, Tag 0F3D], is a weighting of `f`: `f` is locally of finite presentation, being locally of
finite type over the locally Noetherian `Y`. -/
theorem isWeighting_flatQuasiFiniteWeight_of_covariance [Flat f] [LocallyQuasiFinite f] :
    IsWeighting f (flatQuasiFiniteWeight f) :=
  haveI := isLocallyNoetherian_of_covariance k q
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f q
  flatQuasiFiniteWeight_isWeighting f

/-- **Stacks Project, Tag 0GKS**, case (1), on `D⁺_tors`: `f` étale. The weighting is the
canonical one of [Stacks, Tag 0GKI]. -/
@[stacks 0GKS "case (1), f étale, K in D⁺_tors(Y_étale, Λ): the map RΓ_c(X, f⁻¹K) ⟶ RΓ_c(Y, K)",
  sga "4 XVII 6.2.7" "special case"]
def compactlySupportedCohomologyTraceOfEtale [Etale f] :
    (isTorsionPlus.{u, u} Λ Y).ι ⋙ etaleModuleDerivedInverseImagePlus.{u, u} Λ f ⋙
        compactlySupportedCohomology.{u, u} k (f ≫ q) jp Λ ⟶
      (isTorsionPlus.{u, u} Λ Y).ι ⋙ compactlySupportedCohomology.{u, u} k q jq Λ :=
  compactlySupportedCohomologyTraceOfWeighting k q f jp jq Λ
    (isWeighting_flatQuasiFiniteWeight_of_covariance k q f)

/-- **Stacks Project, Tag 0GKS**, case (2), on `D⁺_tors`: `f` flat and quasi-finite. The
weighting is the canonical one of [Stacks, Tag 0GKI]. -/
@[stacks 0GKS "case (2), f flat and quasi-finite, K in D⁺_tors(Y_étale, Λ): the map \
RΓ_c(X, f⁻¹K) ⟶ RΓ_c(Y, K)", sga "4 XVII 6.2.7" "partial"]
def compactlySupportedCohomologyTraceOfFlat [Flat f] [LocallyQuasiFinite f] :
    (isTorsionPlus.{u, u} Λ Y).ι ⋙ etaleModuleDerivedInverseImagePlus.{u, u} Λ f ⋙
        compactlySupportedCohomology.{u, u} k (f ≫ q) jp Λ ⟶
      (isTorsionPlus.{u, u} Λ Y).ι ⋙ compactlySupportedCohomology.{u, u} k q jq Λ :=
  compactlySupportedCohomologyTraceOfWeighting k q f jp jq Λ
    (isWeighting_flatQuasiFiniteWeight_of_covariance k q f)

include hΛ in
/-- **Stacks Project, Tag 0GKS**, case (1), on `D(Y_étale, Λ)` for a torsion ring `Λ`. -/
@[stacks 0GKS "case (1), f étale, K in D(Y_étale, Λ) with Λ torsion: the map \
RΓ_c(X, f⁻¹K) ⟶ RΓ_c(Y, K)", sga "4 XVII 6.2.7" "special case"]
def compactlySupportedCohomologyUnboundedTraceOfEtale [Etale f] :
    (etaleModuleInverseImage.{u, u} Λ f).mapDerivedCategory ⋙
        compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ ⟶
      compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ :=
  compactlySupportedCohomologyUnboundedTraceOfWeighting k q f jp jq Λ
    (isWeighting_flatQuasiFiniteWeight_of_covariance k q f) hΛ

include hΛ in
/-- **Stacks Project, Tag 0GKS**, case (2), on `D(Y_étale, Λ)` for a torsion ring `Λ`. -/
@[stacks 0GKS "case (2), f flat and quasi-finite, K in D(Y_étale, Λ) with Λ torsion: the map \
RΓ_c(X, f⁻¹K) ⟶ RΓ_c(Y, K)", sga "4 XVII 6.2.7" "special case"]
def compactlySupportedCohomologyUnboundedTraceOfFlat [Flat f] [LocallyQuasiFinite f] :
    (etaleModuleInverseImage.{u, u} Λ f).mapDerivedCategory ⋙
        compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ ⟶
      compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ :=
  compactlySupportedCohomologyUnboundedTraceOfWeighting k q f jp jq Λ
    (isWeighting_flatQuasiFiniteWeight_of_covariance k q f) hΛ

include hΛ in
/-- **Stacks Project, Tag 0GKS**, case (1), the arrow `Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ)` for `f`
étale and `Λ` torsion. -/
@[stacks 0GKS "case (1), f étale: the arrow Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ) for a torsion ring Λ",
  sga "4 XVII 6.2.7" "special case"]
def compactlySupportedCohomologyConstantTraceOfEtale [Etale f] :
    (compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ X) 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) ⟶
      (compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ Y) 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) :=
  compactlySupportedCohomologyConstantTraceOfWeighting k q f jp jq Λ
    (isWeighting_flatQuasiFiniteWeight_of_covariance k q f) hΛ

include hΛ in
/-- **Stacks Project, Tag 0GKS**, case (2), the arrow `Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ)` for `f`
flat and quasi-finite and `Λ` torsion. -/
@[stacks 0GKS "case (2), f flat and quasi-finite: the arrow Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ) for a \
torsion ring Λ", sga "4 XVII 6.2.7" "special case"]
def compactlySupportedCohomologyConstantTraceOfFlat [Flat f] [LocallyQuasiFinite f] :
    (compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ X) 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) ⟶
      (compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ Y) 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) :=
  compactlySupportedCohomologyConstantTraceOfWeighting k q f jp jq Λ
    (isWeighting_flatQuasiFiniteWeight_of_covariance k q f) hΛ

/-! ### Case (3): quasi-finite over a geometrically unibranch target -/

variable (hY : IsGeometricallyUnibranch Y)

omit [QuasiCompact q] [IsSeparated q] [QuasiCompact (f ≫ q)] [IsSeparated (f ≫ q)] in
include q hY in
/-- In case (3) of [Stacks, Tag 0GKS] the morphism `f` has a weighting, for instance the generic
separable degree of [Stacks, Tag 0GKJ], [Stacks, Tag 0F3E]: `Y` is locally Noetherian, being of
finite type over a field. This only asserts existence; the weighting of case (3) is
`AlgebraicGeometry.genericSeparableDegreeWeight`
(`Stacks.EtaleCohomology.isWeighting_genericSeparableDegreeWeight_of_covariance`). -/
theorem exists_isWeighting_of_isGeometricallyUnibranch [LocallyQuasiFinite f] :
    ∃ w : X → ℤ, IsWeighting f w :=
  haveI := isLocallyNoetherian_of_covariance k q
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f q
  let h := exists_weighting_genericSeparableDegree f hY
  ⟨fun x => (h.choose x : ℤ), h.choose_spec.1⟩

include hY in
/-- A map `RΓ_c(X, f^{-1}K) ⟶ RΓ_c(Y, K)` of `K ∈ D⁺_tors(Y_étale, Λ)` for `f` quasi-finite and
`Y` geometrically unibranch, through the trace map of an unspecified weighting of `f` (chosen from
`Stacks.EtaleCohomology.exists_isWeighting_of_isGeometricallyUnibranch`, which forgets the values
of the weighting). It is not the canonical map of case (3) of [Stacks, Tag 0GKS], which uses the
generic separable degree of [Stacks, Tag 0GKJ]; that map is
`Stacks.EtaleCohomology.compactlySupportedCohomologyGenericSeparableDegreeTrace`. -/
def compactlySupportedCohomologyTraceOfGeometricallyUnibranch [LocallyQuasiFinite f] :
    (isTorsionPlus.{u, u} Λ Y).ι ⋙ etaleModuleDerivedInverseImagePlus.{u, u} Λ f ⋙
        compactlySupportedCohomology.{u, u} k (f ≫ q) jp Λ ⟶
      (isTorsionPlus.{u, u} Λ Y).ι ⋙ compactlySupportedCohomology.{u, u} k q jq Λ :=
  compactlySupportedCohomologyTraceOfWeighting k q f jp jq Λ
    (exists_isWeighting_of_isGeometricallyUnibranch k q f hY).choose_spec

include hY hΛ in
/-- A map `RΓ_c(X, f^{-1}K) ⟶ RΓ_c(Y, K)` of `K ∈ D(Y_étale, Λ)`, `Λ` torsion, for `f`
quasi-finite and `Y` geometrically unibranch, through the trace map of an unspecified weighting of
`f`. It is not the canonical map of case (3) of [Stacks, Tag 0GKS], which uses the generic
separable degree of [Stacks, Tag 0GKJ]; that map is
`Stacks.EtaleCohomology.compactlySupportedCohomologyUnboundedGenericSeparableDegreeTrace`. -/
def compactlySupportedCohomologyUnboundedTraceOfGeometricallyUnibranch [LocallyQuasiFinite f] :
    (etaleModuleInverseImage.{u, u} Λ f).mapDerivedCategory ⋙
        compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ ⟶
      compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ :=
  compactlySupportedCohomologyUnboundedTraceOfWeighting k q f jp jq Λ
    (exists_isWeighting_of_isGeometricallyUnibranch k q f hY).choose_spec hΛ

include hY hΛ in
/-- An arrow `RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ)` for `f` quasi-finite, `Y` geometrically unibranch and `Λ`
torsion, through the trace map of an unspecified weighting of `f`. It is not the arrow `Tr_f` of
case (3) of [Stacks, Tag 0GKS], which uses the generic separable degree of [Stacks, Tag 0GKJ];
that arrow is
`Stacks.EtaleCohomology.compactlySupportedCohomologyConstantGenericSeparableDegreeTrace`. -/
def compactlySupportedCohomologyConstantTraceOfGeometricallyUnibranch [LocallyQuasiFinite f] :
    (compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ X) 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) ⟶
      (compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ Y) 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) :=
  compactlySupportedCohomologyConstantTraceOfWeighting k q f jp jq Λ
    (exists_isWeighting_of_isGeometricallyUnibranch k q f hY).choose_spec hΛ

/-! ### Case (3) with the generic separable degree -/

omit [QuasiCompact q] [IsSeparated q] [LocallyOfFiniteType (f ≫ q)] [QuasiCompact (f ≫ q)]
  [IsSeparated (f ≫ q)] in
include q in
/-- In case (3) of [Stacks, Tag 0GKS] the generic separable degree of [Stacks, Tag 0GKJ],
[Stacks, Tag 0F3E], `AlgebraicGeometry.genericSeparableDegreeWeight`, is a weighting of `f`: `Y`
is locally Noetherian, being of finite type over a field. -/
theorem isWeighting_genericSeparableDegreeWeight_of_covariance [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] :
    IsWeighting f (fun x ↦ (genericSeparableDegreeWeight f hY x : ℤ)) :=
  haveI := isLocallyNoetherian_of_covariance k q
  isWeighting_genericSeparableDegreeWeight f hY

include hY in
/-- **Stacks Project, Tag 0GKS**, case (3), on `D⁺_tors`: `f` quasi-finite and `Y` geometrically
unibranch. The map `RΓ_c(X, f^{-1}K) ⟶ RΓ_c(Y, K)` of `K ∈ D⁺_tors(Y_étale, Λ)` of
`Stacks.EtaleCohomology.compactlySupportedCohomologyTraceOfWeighting` for the weighting of
[Stacks, Tag 0GKJ], the generic separable degree `AlgebraicGeometry.genericSeparableDegreeWeight`
(`Stacks.EtaleCohomology.compactlySupportedCohomologyGenericSeparableDegreeTrace_eq`). -/
@[stacks 0GKS "case (3), f quasi-finite and Y geometrically unibranch, K in D⁺_tors(Y_étale, Λ): \
the map RΓ_c(X, f⁻¹K) ⟶ RΓ_c(Y, K) through the trace Tr_{f,w,K} for w the generic separable \
degree of 0GKJ (AlgebraicGeometry.genericSeparableDegreeWeight, determined by its values by \
eq_genericSeparableDegreeWeight); replaces \
compactlySupportedCohomologyTraceOfGeometricallyUnibranch, which used an unspecified weighting"]
def compactlySupportedCohomologyGenericSeparableDegreeTrace [LocallyQuasiFinite f] :
    (isTorsionPlus.{u, u} Λ Y).ι ⋙ etaleModuleDerivedInverseImagePlus.{u, u} Λ f ⋙
        compactlySupportedCohomology.{u, u} k (f ≫ q) jp Λ ⟶
      (isTorsionPlus.{u, u} Λ Y).ι ⋙ compactlySupportedCohomology.{u, u} k q jq Λ :=
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f q
  compactlySupportedCohomologyTraceOfWeighting k q f jp jq Λ
    (isWeighting_genericSeparableDegreeWeight_of_covariance k q f hY)

/-- The map of case (3) of [Stacks, Tag 0GKS] is the map of case (4) for the generic separable
degree `AlgebraicGeometry.genericSeparableDegreeWeight` of [Stacks, Tag 0GKJ]. -/
theorem compactlySupportedCohomologyGenericSeparableDegreeTrace_eq [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] :
    compactlySupportedCohomologyGenericSeparableDegreeTrace k q f jp jq Λ hY =
      compactlySupportedCohomologyTraceOfWeighting k q f jp jq Λ
        (isWeighting_genericSeparableDegreeWeight_of_covariance k q f hY) :=
  rfl

include hY hΛ in
/-- **Stacks Project, Tag 0GKS**, case (3), on `D(Y_étale, Λ)` for a torsion ring `Λ`: the map
`RΓ_c(X, f^{-1}K) ⟶ RΓ_c(Y, K)` of `K ∈ D(Y_étale, Λ)` through the trace map of the generic
separable degree `AlgebraicGeometry.genericSeparableDegreeWeight` of [Stacks, Tag 0GKJ]. -/
@[stacks 0GKS "case (3), f quasi-finite and Y geometrically unibranch, K in D(Y_étale, Λ) with Λ \
torsion: the map RΓ_c(X, f⁻¹K) ⟶ RΓ_c(Y, K) through the trace Tr_{f,w,K} for w the generic \
separable degree of 0GKJ; replaces \
compactlySupportedCohomologyUnboundedTraceOfGeometricallyUnibranch, which used an unspecified \
weighting"]
def compactlySupportedCohomologyUnboundedGenericSeparableDegreeTrace [LocallyQuasiFinite f] :
    (etaleModuleInverseImage.{u, u} Λ f).mapDerivedCategory ⋙
        compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ ⟶
      compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ :=
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f q
  compactlySupportedCohomologyUnboundedTraceOfWeighting k q f jp jq Λ
    (isWeighting_genericSeparableDegreeWeight_of_covariance k q f hY) hΛ

/-- The map of case (3) of [Stacks, Tag 0GKS] on `D(Y_étale, Λ)` is the map of case (4) for the
generic separable degree `AlgebraicGeometry.genericSeparableDegreeWeight`. -/
theorem compactlySupportedCohomologyUnboundedGenericSeparableDegreeTrace_eq
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    compactlySupportedCohomologyUnboundedGenericSeparableDegreeTrace k q f jp jq Λ hΛ hY =
      compactlySupportedCohomologyUnboundedTraceOfWeighting k q f jp jq Λ
        (isWeighting_genericSeparableDegreeWeight_of_covariance k q f hY) hΛ :=
  rfl

include hY hΛ in
/-- **Stacks Project, Tag 0GKS**, case (3), the arrow `Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ)` for `f`
quasi-finite, `Y` geometrically unibranch and `Λ` torsion, through the trace map of the generic
separable degree `AlgebraicGeometry.genericSeparableDegreeWeight` of [Stacks, Tag 0GKJ]. -/
@[stacks 0GKS "case (3), f quasi-finite and Y geometrically unibranch: the arrow \
Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ) for a torsion ring Λ, for w the generic separable degree of 0GKJ; \
replaces compactlySupportedCohomologyConstantTraceOfGeometricallyUnibranch, which used an \
unspecified weighting"]
def compactlySupportedCohomologyConstantGenericSeparableDegreeTrace [LocallyQuasiFinite f] :
    (compactlySupportedCohomologyUnbounded.{u, u} k (f ≫ q) jp Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ X) 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) ⟶
      (compactlySupportedCohomologyUnbounded.{u, u} k q jq Λ).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u} Λ Y) 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) :=
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f q
  compactlySupportedCohomologyConstantTraceOfWeighting k q f jp jq Λ
    (isWeighting_genericSeparableDegreeWeight_of_covariance k q f hY) hΛ

/-- The arrow `Tr_f` of case (3) of [Stacks, Tag 0GKS] is the arrow of case (4) for the generic
separable degree `AlgebraicGeometry.genericSeparableDegreeWeight`. -/
theorem compactlySupportedCohomologyConstantGenericSeparableDegreeTrace_eq
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    compactlySupportedCohomologyConstantGenericSeparableDegreeTrace k q f jp jq Λ hΛ hY =
      compactlySupportedCohomologyConstantTraceOfWeighting k q f jp jq Λ
        (isWeighting_genericSeparableDegreeWeight_of_covariance k q f hY) hΛ :=
  rfl

end Covariance

end Stacks.EtaleCohomology

end
