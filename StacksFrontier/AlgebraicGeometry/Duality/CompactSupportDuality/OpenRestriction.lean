module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroCovariance
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomRestrictionStructureSheaf

/-!
# Duality for compactly supported cohomology and restriction to an open

Let `p : U ⟶ Spec k` be separated of finite type over a field `k`, with a compactification
`U ⊆ X`, `q : X ⟶ Spec k` proper, and let `V ⊆ U` be an open, compactified by `V ⊆ U ⊆ X`.
[Stacks, Tag 0G5B] says that the duality isomorphisms
`Hom_k(H^i(U, K), k) ≅ H^{-i}_c(U, R𝓗om(K, ω_{U/k}^•))` of [Stacks, Tag 0G5A] for `U` and for `V`
are compatible with the contragredient of restriction `H^i(U, K) ⟶ H^i(V, K|_V)` and the map
`H^{-i}_c(V, -|_V) ⟶ H^{-i}_c(U, -)` of [Stacks, Remark 0G56].

## Main definitions

* `AlgebraicGeometry.cohomologyRestrict`: the restriction `H^i(U, K) ⟶ H^i(V, K|_V)`, through
  `H^i(U, K) = Hom(𝒪_U, K[i])`.
* `AlgebraicGeometry.compactificationOpen`: the compactification `V ⊆ U ⊆ X` of `V`.
* `AlgebraicGeometry.openDualShiftRestrictHom`: the canonical identification
  `R𝓗om(K|_V, ω_V^•)[-i] ⟶ (R𝓗om(K, ω_U^•)[-i])|_V` ([Stacks, Tag 08DL]).
* `AlgebraicGeometry.extensionByZeroCompactificationOpenCovariance`: the canonical map
  `Rj'_!(L|_V) ⟶ Rj_! L` of [Stacks, Tag 0G4Y] for `j : U ⟶ X`, `j' : V ⟶ X`.
* `AlgebraicGeometry.compactSupportOpenDualMap`: the map of [Stacks, Remark 0G56] (its second
  construction, `Rq_*` of the map of [Stacks, Tag 0G4Y]).

## Main results

* `AlgebraicGeometry.openDualityLinearEquiv_restrict`: the identification
  `H^i(U, K) = Hom((D_U K)[-i], ω_X^•|_U)` of the proof of [Stacks, Tag 0G5A] commutes with
  restriction to `V`.
* `AlgebraicGeometry.compactSupportDualityEquiv_restrict`: **[Stacks, Tag 0G5B]**.

## Implementation notes

Several statements go through lemmas about one abstract category, applied by `exact`, because the
categories of modules on `V` have two spellings that agree only at default transparency.

Standard model: uses `AlgebraicGeometry.compactSupportDualityEquiv` ([Stacks, Tag 0G5A]) and
`Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`, which exist only at
`CategoryTheory.HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0G5B](https://stacks.math.columbia.edu/tag/0G5B)
* [Stacks Project, Tag 0G5A](https://stacks.math.columbia.edu/tag/0G5A)
* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
* [Stacks Project, Tag 0G4Y](https://stacks.math.columbia.edu/tag/0G4Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Duality

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of k))
  [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]

/-- An open of a scheme separated of finite type over a field is separated over the field. -/
instance isSeparated_opens_ι_comp (V : U.Opens) : IsSeparated (V.ι ≫ p) := inferInstance

/-- An open of a scheme separated of finite type over a field is of finite type over the field. -/
instance locallyOfFiniteType_opens_ι_comp (V : U.Opens) : LocallyOfFiniteType (V.ι ≫ p) :=
  inferInstance

/-- An open of a scheme of finite type over a field is quasi-compact over the field. -/
instance quasiCompact_opens_ι_comp (V : U.Opens) : QuasiCompact (V.ι ≫ p) := by
  have := isNoetherian_of_locallyOfFiniteType p
  infer_instance

section Restriction

variable (V : U.Opens)

/-- `R(K[i]) ≅ (R K)[i]` for restriction `R` to `V`, on `D^b_{Coh}`. -/
def restrictShiftIso (K : BoundedCoherentDerived U) (i : ℤ) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    (restrictBoundedCoherentLift V.ι).obj (K⟦i⟧) ≅ ((restrictBoundedCoherentLift V.ι).obj K)⟦i⟧ :=
  have := isNoetherian_of_locallyOfFiniteType p
  ObjectProperty.isoMk _
    ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.mapIso
        (((boundedCoherentDerived U).ι.commShiftIso i).app K) ≪≫
      ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.commShiftIso i).app K.obj ≪≫
      (((boundedCoherentDerived V.toScheme).ι.commShiftIso i).app
        ((restrictBoundedCoherentLift V.ι).obj K)).symm)

/-- `H^i(T, K) = Hom(𝒪_T, K[i])`, `k`-linearly. -/
def cohomologyUnitHomLinearEquiv {T : Scheme.{u}} (q : T ⟶ Spec (CommRingCat.of k))
    (K : BoundedCoherentDerived T) (i : ℤ) :
    letI : Linear k T.Modules := modulesLinear k (Over.mk q)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver q).obj K.obj)) ≃ₗ[k]
      (derivedUnitObject T ⟶ (K⟦i⟧).obj) :=
  let : Linear k T.Modules := modulesLinear k (Over.mk q)
  (openDualityCohomologyShiftIso q K i).symm.toLinearEquiv ≪≫ₗ
    (structureSheafHomLinearEquiv q (K⟦i⟧).obj).symm

/-- Restriction of morphisms `𝒪_U ⟶ K[i]` to `𝒪_V ⟶ (K|_V)[i]`: restrict to `V`, then precompose
with the canonical morphism `𝒪_V ⟶ 𝒪_U|_V` and postcompose with `(K[i])|_V ≅ (K|_V)[i]`. -/
def unitHomRestrict (K : BoundedCoherentDerived U) (i : ℤ) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    letI : Linear k U.Modules := modulesLinear k (Over.mk p)
    letI : Linear k V.toScheme.Modules := modulesLinear k (Over.mk (V.ι ≫ p))
    (derivedUnitObject U ⟶ (K⟦i⟧).obj) →ₗ[k]
      (derivedUnitObject V.toScheme ⟶ (((restrictBoundedCoherentLift V.ι).obj K)⟦i⟧).obj) :=
  have := isNoetherian_of_locallyOfFiniteType p
  let : Linear k U.Modules := modulesLinear k (Over.mk p)
  let : Linear k V.toScheme.Modules := modulesLinear k (Over.mk (V.ι ≫ p))
  have := mapDerivedCategory_restrictFunctor_linear p (V.ι ≫ p) V.ι rfl
  { toFun := fun a => Stacks.SheafOfModules.derivedUnitRestrictHom V ≫
      (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map a ≫
      (restrictShiftIso p V K i).hom.hom
    map_add' := fun a b => by
      rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
    map_smul' := fun a b => by
      rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
      rfl }

/-- **The restriction map `H^i(U, K) ⟶ H^i(V, K|_V)`**, through `H^i(U, K) = Hom(𝒪_U, K[i])`:
a morphism `𝒪_U ⟶ K[i]` restricts to `𝒪_V = 𝒪_U|_V ⟶ (K[i])|_V = (K|_V)[i]`. -/
def cohomologyRestrict (K : BoundedCoherentDerived U) (i : ℤ) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver p).obj K.obj)) →ₗ[k]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver (V.ι ≫ p)).obj
          ((restrictBoundedCoherentLift V.ι).obj K).obj)) :=
  have := isNoetherian_of_locallyOfFiniteType p
  let : Linear k U.Modules := modulesLinear k (Over.mk p)
  let : Linear k V.toScheme.Modules := modulesLinear k (Over.mk (V.ι ≫ p))
  (cohomologyUnitHomLinearEquiv (V.ι ≫ p) ((restrictBoundedCoherentLift V.ι).obj K)
      i).symm.toLinearMap ∘ₗ
    unitHomRestrict p V K i ∘ₗ (cohomologyUnitHomLinearEquiv p K i).toLinearMap

end Restriction

section Compactification

variable (c : CompactificationOf (Over.mk p)) (V : U.Opens)

/-- The compactification `V ⊆ U ⊆ X` of an open `V` of `U` induced by a compactification
`U ⊆ X` of `U`: the same proper scheme `X`, with the composite open immersion. -/
abbrev compactificationOpen : CompactificationOf (Over.mk (V.ι ≫ p)) :=
  c.precompOpen V.ι

/-- Restricting from `X` to `U` and then to `V` is restricting from `X` to `V`, on `D(𝒪)`. -/
def compactificationOpenRestrictIso :
    (Scheme.Modules.restrictFunctor c.immersion).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor (V.ι ≫ c.immersion)).mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Scheme.Modules.restrictFunctorComp V.ι c.immersion) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm

/-- Restricting from `X` to `U` and then to `V` is restricting from `X` to `V`, on
`D^b_{Coh}`. -/
def compactificationOpenRestrictLiftIso :
    haveI : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
    restrictBoundedCoherentLift c.immersion ⋙ restrictBoundedCoherentLift V.ι ≅
      restrictBoundedCoherentLift (V.ι ≫ c.immersion) :=
  have : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
  NatIso.ofComponents
    (fun L => ObjectProperty.isoMk _ ((compactificationOpenRestrictIso p c V).app L.obj))
    (fun ψ => ObjectProperty.hom_ext _
      ((compactificationOpenRestrictIso p c V).hom.naturality ψ.hom))

/-- **`ω_{V/k}^• ≅ ω_{U/k}^•|_V`**: both are the restriction of `ω_{X/k}^•`
(`AlgebraicGeometry.standardUpperShriekDualizingComplexIso`). -/
def dualizingComplexRestrictIso :
    (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        (standardUpperShriekDualizingComplex p c) ≅
      standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V) :=
  (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.mapIso
      (standardUpperShriekDualizingComplexIso p c) ≪≫
    (compactificationOpenRestrictIso p c V).app (standardRelativeDualizingComplex c.toBase) ≪≫
    (standardUpperShriekDualizingComplexIso (V.ι ≫ p) (compactificationOpen p c V)).symm

/-- **`R𝓗om(N|_V, ω_V^•) ⟶ R𝓗om(N, ω_U^•)|_V`**, the inverse of [Stacks, Tag 08DL] read through
`ω_V^• ≅ ω_U^•|_V`. -/
def derivedDualRestrictHom (N : DerivedCategory U.Modules) :
    (schemeDerivedDualFunctor (standardUpperShriekDualizingComplex (V.ι ≫ p)
        (compactificationOpen p c V))).obj
        (op ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj N)) ⟶
      (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        ((schemeDerivedDualFunctor (standardUpperShriekDualizingComplex p c)).obj (op N)) :=
  ((RingedSite.derivedSheafHomBifunctor
      (Stacks.SheafOfModules.ringedSite V.toScheme.sheaf)).flip.map
        (dualizingComplexRestrictIso p c V).inv).app
      (op ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj N)) ≫
    (Stacks.SheafOfModules.restrictDerivedSheafHomIso V N
      (standardUpperShriekDualizingComplex p c)).inv

/-- `D_V(M|_V) ⟶ (D_U M)|_V` on `D^b_{Coh}`, for `D = R𝓗om(-, ω^•)`. -/
def openDualRestrictHom (M : BoundedCoherentDerived U) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    haveI := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
    openDualObj (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
        (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
          (compactificationOpen p c V))
        ((restrictBoundedCoherentLift V.ι).obj M) ⟶
      (restrictBoundedCoherentLift V.ι).obj
        (openDualObj (standardUpperShriekDualizingComplex p c)
          (isDualizingComplex_standardUpperShriekDualizingComplex p c) M) :=
  have := isNoetherian_of_locallyOfFiniteType p
  have := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
  ObjectProperty.homMk (derivedDualRestrictHom p c V M.obj)

/-- **The canonical identification `R𝓗om(K|_V, ω_V^•)[-i] ⟶ (R𝓗om(K, ω_U^•)[-i])|_V`**:
`R𝓗om(K|_V, ω_V^•)[-i] = R𝓗om((K|_V)[i], ω_V^•) = R𝓗om((K[i])|_V, ω_V^•) =
R𝓗om(K[i], ω_U^•)|_V = (R𝓗om(K, ω_U^•)[-i])|_V`, by `R𝓗om(-, ω)` commuting with shifts
(`AlgebraicGeometry.openDualShiftIso`), restriction commuting with shifts
(`AlgebraicGeometry.restrictShiftIso`) and [Stacks, Tag 08DL]
(`AlgebraicGeometry.openDualRestrictHom`). -/
def openDualShiftRestrictHom (K : BoundedCoherentDerived U) (i : ℤ) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    haveI := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
    (openDualObj (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
        (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
          (compactificationOpen p c V))
        ((restrictBoundedCoherentLift V.ι).obj K))⟦-i⟧ ⟶
      (restrictBoundedCoherentLift V.ι).obj
        ((openDualObj (standardUpperShriekDualizingComplex p c)
          (isDualizingComplex_standardUpperShriekDualizingComplex p c) K)⟦-i⟧) :=
  have := isNoetherian_of_locallyOfFiniteType p
  have := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
  (openDualShiftIso _ _ ((restrictBoundedCoherentLift V.ι).obj K) i).inv ≫
    openDualMap _ _ (restrictShiftIso p V K i).hom ≫
    openDualRestrictHom p c V (K⟦i⟧) ≫
    (restrictBoundedCoherentLift V.ι).map (openDualShiftIso _ _ K i).hom

/-- **[Stacks, Tag 0G4Y] for `V ⊆ U ⊆ X`**: the canonical map `Rj'_!(L|_V) ⟶ Rj_! L` of
pro-objects of `D^b_{Coh}(𝒪_X)`, for the open immersions `j : U ⟶ X` and
`j' : V ⟶ U ⟶ X`, functorial in `L`. It is `CategoryTheory.extensionByZeroCovariance`: on morphisms
into a constant pro-object it is restriction from `U` to `V`
(`CategoryTheory.extensionByZeroHomEquiv_covariance`). -/
def extensionByZeroCompactificationOpenCovariance :
    haveI := isNoetherian_of_locallyOfFiniteType p
    haveI : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
    haveI := isNoetherian_of_locallyOfFiniteType c.toBase
    restrictBoundedCoherentLift V.ι ⋙ extensionByZeroOpenImmersion (V.ι ≫ c.immersion) ⟶
      extensionByZeroOpenImmersion c.immersion :=
  have := isNoetherian_of_locallyOfFiniteType p
  have : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
  have := isNoetherian_of_locallyOfFiniteType c.toBase
  CategoryTheory.extensionByZeroCovariance (restrictBoundedCoherentLift c.immersion)
    (restrictBoundedCoherentLift (V.ι ≫ c.immersion)) (restrictBoundedCoherentLift V.ι)
    (compactificationOpenRestrictLiftIso p c V) (DeligneSystem.values c.immersion).toAssignment
    (DeligneSystem.values (V.ι ≫ c.immersion)).toAssignment

/-- The pro-morphism `Rj'_!(R𝓗om(K|_V, ω_V^•)[-i]) ⟶ Rj_!(R𝓗om(K, ω_U^•)[-i])`: the canonical
identification `AlgebraicGeometry.openDualShiftRestrictHom` followed by the map of
[Stacks, Tag 0G4Y]. -/
def openDualExtensionByZeroMap (K : BoundedCoherentDerived U) (i : ℤ) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    haveI : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
    haveI := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
    haveI := isNoetherian_of_locallyOfFiniteType c.toBase
    (extensionByZeroOpenImmersion (V.ι ≫ c.immersion)).obj
        ((openDualObj (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
          (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
            (compactificationOpen p c V))
          ((restrictBoundedCoherentLift V.ι).obj K))⟦-i⟧) ⟶
      (extensionByZeroOpenImmersion c.immersion).obj
        ((openDualObj (standardUpperShriekDualizingComplex p c)
          (isDualizingComplex_standardUpperShriekDualizingComplex p c) K)⟦-i⟧) :=
  have := isNoetherian_of_locallyOfFiniteType p
  have := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
  have := isNoetherian_of_locallyOfFiniteType c.toBase
  have : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
  (extensionByZeroOpenImmersion (V.ι ≫ c.immersion)).map (openDualShiftRestrictHom p c V K i) ≫
    (extensionByZeroCompactificationOpenCovariance p c V).app _

/-- **The map `H^{-i}_c(V, R𝓗om(K|_V, ω_V^•)) ⟶ H^{-i}_c(U, R𝓗om(K, ω_U^•))` of
[Stacks, Remark 0G56]**, in its second construction: `Rq_*` applied to the canonical map
`Rj'_!(L|_V) ⟶ Rj_! L` of [Stacks, Tag 0G4Y], for a compactification `j : U ⟶ X`,
`q : X ⟶ Spec k` of `U` and the induced compactification `j' : V ⟶ U ⟶ X` of `V`, read through
the canonical identification of `R𝓗om(K|_V, ω_V^•)` with `R𝓗om(K, ω_U^•)|_V`. -/
def compactSupportOpenDualMap (K : BoundedCoherentDerived U) (i : ℤ) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    haveI := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
    compactSupportCohomology (compactificationOpen p c V)
        (openDualObj (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
          (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
            (compactificationOpen p c V))
          ((restrictBoundedCoherentLift V.ι).obj K)) (-i) →
      compactSupportCohomology c
        (openDualObj (standardUpperShriekDualizingComplex p c)
          (isDualizingComplex_standardUpperShriekDualizingComplex p c) K) (-i) :=
  have := isNoetherian_of_locallyOfFiniteType p
  have := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
  have := isNoetherian_of_locallyOfFiniteType c.toBase
  fun y => y ≫ (ProSeq.map (properPushforwardBoundedCoherent c.toBase)).map
    (openDualExtensionByZeroMap p c V K i)

attribute [local instance] linearModulesCompactification linearModulesSource
  linearModulesSpecField

omit [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] in
/-- **Duality on the compactification, across `V ⊆ U ⊆ X`.** A morphism
`g : Rj'_! L' ⟶ Rj_! L` of pro-objects of `D^b_{Coh}(𝒪_X)` and a linear map `φ : W ⟶ W'`
compatible with the identifications of `W`, `W'` with the points of `Rj_! L`, `Rj'_! L'` at
`ω_X^•` carry `l ↦ l ∘ φ` to composition with `Rq_* g`. -/
theorem compactSupportDualityOfPoints_compactificationOpen {W W' : Type*} [AddCommGroup W]
    [Module k W] [AddCommGroup W'] [Module k W']
    (L : BoundedCoherentDerived (Over.mk p).left)
    (L' : BoundedCoherentDerived (Over.mk (V.ι ≫ p)).left) (i : ℤ)
    (ρ : W ≃ₗ[k] (L⟦i⟧ ⟶ (restrictBoundedCoherentLift c.immersion).obj
      (compactificationDualizingObj c)))
    (ρ' : W' ≃ₗ[k] (L'⟦i⟧ ⟶ (restrictBoundedCoherentLift (compactificationOpen p c V).immersion).obj
      (compactificationDualizingObj (compactificationOpen p c V))))
    (g : (extensionByZeroOpenImmersion (compactificationOpen p c V).immersion).obj (L'⟦i⟧) ⟶
      (extensionByZeroOpenImmersion c.immersion).obj (L⟦i⟧))
    (φ : W →ₗ[k] W')
    (hg : ∀ w : W, g.unop.hom.app (compactificationDualizingObj c) (ρ w) = ρ' (φ w))
    (l : Module.Dual k W') :
    compactSupportDualityOfPoints c L i ρ (l ∘ₗ φ) =
      compactSupportDualityOfPoints (compactificationOpen p c V) L' i ρ' l ≫
        (ProSeq.map (properPushforwardBoundedCoherent c.toBase)).map g :=
  ProSeq.proDualityLinearEquiv_naturality (properPushforwardBoundedCoherent c.toBase)
    (structureSheafPushforwardHomLinearEquiv c)
    (fun g a => structureSheafPushforwardHomLinearEquiv_comp c g a) (compactificationTrace c)
    (extensionByZeroIso _ (DeligneSystem.values (compactificationOpen p c V).immersion).toAssignment
      (L'⟦i⟧)) ρ'.toEquiv
    (pointsColimitMap (compactificationOpen p c V) L' i ρ')
    (pointsColimitMap_spec (compactificationOpen p c V) L' i ρ')
    (fun _ => bijective_compPairing_compactificationTrace c _)
    (extensionByZeroIso _ (DeligneSystem.values c.immersion).toAssignment (L⟦i⟧)) ρ.toEquiv
    (pointsColimitMap c L i ρ) (pointsColimitMap_spec c L i ρ)
    (fun _ => bijective_compPairing_compactificationTrace c _) g φ hg l

/-- Given commuting squares `l₁ ≫ y = x ≫ l₂` and `z ≫ i₂.hom = i₁.hom ≫ y` with `i₁` and `i₂`
isomorphisms, `(l₁ ≫ i₁.inv) ≫ z = x ≫ l₂ ≫ i₂.inv`. -/
theorem comp_inv_comp_eq_of_squares {C : Type*} [Category C] {P₁ P₂ Q₁ Q₂ S₁ S₂ : C}
    (x : P₁ ⟶ P₂) (y : Q₁ ⟶ Q₂) (z : S₁ ⟶ S₂) (l₁ : P₁ ⟶ Q₁) (l₂ : P₂ ⟶ Q₂) (i₁ : S₁ ≅ Q₁)
    (i₂ : S₂ ≅ Q₂) (hn : l₁ ≫ y = x ≫ l₂) (h : z ≫ i₂.hom = i₁.hom ≫ y) :
    (l₁ ≫ i₁.inv) ≫ z = x ≫ l₂ ≫ i₂.inv := by
  rw [← cancel_mono i₂.hom]
  simp only [Category.assoc, h, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, hn]

/-- `R𝓗om(N|_V, ω_V^•) ⟶ R𝓗om(N, ω_U^•)|_V` is natural in `N`. -/
theorem derivedDualRestrictHom_naturality {A B : DerivedCategory U.Modules} (f : A ⟶ B) :
    derivedDualRestrictHom p c V B ≫
        (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map
          ((schemeDerivedDualFunctor (standardUpperShriekDualizingComplex p c)).map f.op) =
      (schemeDerivedDualFunctor (standardUpperShriekDualizingComplex (V.ι ≫ p)
          (compactificationOpen p c V))).map
          ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map f).op ≫
        derivedDualRestrictHom p c V A := by
  let := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := U.ringCatSheaf) V
  let := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := U.ringCatSheaf) V
  exact comp_inv_comp_eq_of_squares _ _ _ _ _ _ _
    (((RingedSite.derivedSheafHomBifunctor
      (Stacks.SheafOfModules.ringedSite V.toScheme.sheaf)).flip.map
        (dualizingComplexRestrictIso p c V).inv).naturality
      ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map f).op).symm
    (Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso_natural_left V
      (standardUpperShriekDualizingComplex p c) f)

/-- Cancelling a natural isomorphism against its inverse at an object, in one abstract
category. -/
theorem comp_inv_app_hom_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) (X : C) {Y : D} (a : Y ⟶ G.obj X) : (a ≫ e.inv.app X) ≫ e.hom.app X = a := by
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- `ω_V^• ≅ ω_U^•|_V` against the identifications of both with restrictions of `ω_X^•`. -/
theorem dualizingComplexRestrictIso_inv_comp :
    (dualizingComplexRestrictIso p c V).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map
          (standardUpperShriekDualizingComplexIso p c).hom ≫
        (compactificationOpenRestrictIso p c V).hom.app
          (standardRelativeDualizingComplex c.toBase) =
      (standardUpperShriekDualizingComplexIso (V.ι ≫ p) (compactificationOpen p c V)).hom := by
  change (((standardUpperShriekDualizingComplexIso (V.ι ≫ p) (compactificationOpen p c V)).hom ≫
      ((compactificationOpenRestrictIso p c V).app
        (standardRelativeDualizingComplex c.toBase)).inv) ≫
      (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map
        (standardUpperShriekDualizingComplexIso p c).inv) ≫ _ = _
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.app_inv]
  exact comp_inv_app_hom_app _ _ _

/-- A diagram chase in one category: the relations `h₁`, `h₂`, `h₃` and `h₄` give
`(lf ≫ i.inv) ≫ eta ≫ m = e₀ ≫ n₀ ≫ s`. -/
theorem derivedDualRestrictHom_structureSheaf_chase {C : Type*} [Category C]
    {A A' B B' S T W M : C} (lf : A ⟶ B) (i : S ≅ B) (eta : S ⟶ T) (m : T ⟶ M) (e₁ : B ⟶ B')
    (n₁ : B' ⟶ T) (e₀ : A ⟶ A') (lf' : A' ⟶ B') (n₀ : A' ⟶ W) (li : W ⟶ T) (s : W ⟶ M)
    (h₁ : i.hom ≫ e₁ ≫ n₁ = eta) (h₂ : lf ≫ e₁ = e₀ ≫ lf') (h₃ : lf' ≫ n₁ = n₀ ≫ li)
    (h₄ : li ≫ m = s) :
    (lf ≫ i.inv) ≫ eta ≫ m = e₀ ≫ n₀ ≫ s := by
  rw [← h₁, ← h₄]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h₂, reassoc_of% h₃]

/-- **`D_V(𝒪_U|_V) ⟶ (D_U 𝒪_U)|_V` against `D 𝒪 ≅ ω^•`.** -/
theorem derivedDualRestrictHom_structureSheaf :
    derivedDualRestrictHom p c V (derivedUnitObject U) ≫
        (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map
          (Stacks.SheafOfModules.schemeStructureSheafHomIso U
            (standardUpperShriekDualizingComplex p c)).hom ≫
        (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map
          (standardUpperShriekDualizingComplexIso p c).hom ≫
        (compactificationOpenRestrictIso p c V).hom.app
          (standardRelativeDualizingComplex c.toBase) =
      (schemeDerivedDualFunctor (standardUpperShriekDualizingComplex (V.ι ≫ p)
          (compactificationOpen p c V))).map (Stacks.SheafOfModules.derivedUnitRestrictHom V).op ≫
        (Stacks.SheafOfModules.schemeStructureSheafHomIso V.toScheme
          (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))).hom ≫
        (standardUpperShriekDualizingComplexIso (V.ι ≫ p) (compactificationOpen p c V)).hom :=
  derivedDualRestrictHom_structureSheaf_chase _ _ _ _ _ _ _ _ _ _ _
    (Stacks.SheafOfModules.restrictDerivedSheafHomIso_structureSheaf V
      (standardUpperShriekDualizingComplex p c))
    (((RingedSite.derivedSheafHomBifunctor
      (Stacks.SheafOfModules.ringedSite V.toScheme.sheaf)).flip.map
        (dualizingComplexRestrictIso p c V).inv).naturality
      (Stacks.SheafOfModules.derivedUnitRestrictHom V).op).symm
    (Stacks.SheafOfModules.schemeStructureSheafHomIso_naturality V.toScheme
      (dualizingComplexRestrictIso p c V).inv)
    (dualizingComplexRestrictIso_inv_comp p c V)

/-- Reassociation, in one abstract category. -/
theorem comp_comp_assoc_eq {C : Type*} [Category C] {W X Y Z T : C} (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) (d : Z ⟶ T) : a ≫ (b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

/-- `D_V(M|_V) ⟶ (D_U M)|_V` is natural in `M`, on `D^b_{Coh}`. -/
theorem openDualRestrictHom_naturality {A B : BoundedCoherentDerived U} (f : A ⟶ B) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    haveI := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
    openDualRestrictHom p c V B ≫
        (restrictBoundedCoherentLift V.ι).map
          (openDualMap (standardUpperShriekDualizingComplex p c)
            (isDualizingComplex_standardUpperShriekDualizingComplex p c) f) =
      openDualMap (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
          (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
            (compactificationOpen p c V))
          ((restrictBoundedCoherentLift V.ι).map f) ≫
        openDualRestrictHom p c V A := by
  have := isNoetherian_of_locallyOfFiniteType p
  have := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
  exact ObjectProperty.hom_ext _ (derivedDualRestrictHom_naturality p c V f.hom)

/-- The canonical morphism `𝒪_V ⟶ 𝒪_U|_V` on `D^b_{Coh}`. -/
def unitRestrictHom :
    haveI := isNoetherian_of_locallyOfFiniteType p
    structureSheafBoundedCoherent V.toScheme ⟶
      (restrictBoundedCoherentLift V.ι).obj (structureSheafBoundedCoherent U) :=
  have := isNoetherian_of_locallyOfFiniteType p
  ObjectProperty.homMk (Stacks.SheafOfModules.derivedUnitRestrictHom V)

/-- `D_V(𝒪_U|_V) ⟶ (D_U 𝒪_U)|_V` against `D 𝒪 ≅ ω^•`, on `D^b_{Coh}`. -/
theorem openDualRestrictHom_structureSheaf :
    haveI := isNoetherian_of_locallyOfFiniteType p
    haveI : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
    haveI := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
    haveI := isNoetherian_of_locallyOfFiniteType c.toBase
    openDualRestrictHom p c V (structureSheafBoundedCoherent U) ≫
        (restrictBoundedCoherentLift V.ι).map
          (openDualStructureSheafIso (standardUpperShriekDualizingComplex p c)
            (isDualizingComplex_standardUpperShriekDualizingComplex p c)
            ((restrictBoundedCoherentLift c.immersion).obj (compactificationDualizingObj c))
            (standardUpperShriekDualizingComplexIso p c).symm).hom ≫
        (compactificationOpenRestrictLiftIso p c V).hom.app (compactificationDualizingObj c) =
      openDualMap (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
          (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
            (compactificationOpen p c V)) (unitRestrictHom p V) ≫
        (openDualStructureSheafIso
          (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
          (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
            (compactificationOpen p c V))
          ((restrictBoundedCoherentLift (compactificationOpen p c V).immersion).obj
            (compactificationDualizingObj (compactificationOpen p c V)))
          (standardUpperShriekDualizingComplexIso (V.ι ≫ p)
            (compactificationOpen p c V)).symm).hom := by
  have := isNoetherian_of_locallyOfFiniteType p
  have : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
  have := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
  have := isNoetherian_of_locallyOfFiniteType c.toBase
  refine ObjectProperty.hom_ext _ ?_
  have h2 : ((restrictBoundedCoherentLift V.ι).map
      (openDualStructureSheafIso (standardUpperShriekDualizingComplex p c)
        (isDualizingComplex_standardUpperShriekDualizingComplex p c)
        ((restrictBoundedCoherentLift c.immersion).obj (compactificationDualizingObj c))
        (standardUpperShriekDualizingComplexIso p c).symm).hom).hom =
      (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map
          (Stacks.SheafOfModules.schemeStructureSheafHomIso U
            (standardUpperShriekDualizingComplex p c)).hom ≫
        (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map
          (standardUpperShriekDualizingComplexIso p c).hom :=
    Functor.map_comp _ _ _
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, h2]
  exact (comp_comp_assoc_eq _ _ _ _).trans (derivedDualRestrictHom_structureSheaf p c V)

/-- A diagram chase across a functor `G : 𝒰 ⥤ 𝒱`: the relations `hD`, `h₁` and `h₂` give
`(s ≫ dσ ≫ Θ₁ ≫ G.map sh.hom) ≫ G.map ((sh.inv ≫ df) ≫ η) ≫ eω = (s ≫ dcomp) ≫ η'`. -/
theorem openDualityLinearEquiv_restrict_chase {𝒰 𝒱 : Type*} [Category 𝒰] [Category 𝒱]
    (G : 𝒰 ⥤ 𝒱) {X₀ X₁ X₂ X₃ X₄ W' : 𝒱} {Y₀ Y₁ Y₂ W : 𝒰}
    (s : X₀ ⟶ X₁) (dσ : X₁ ⟶ X₂) (Θ₁ : X₂ ⟶ G.obj Y₁) (sh : Y₁ ≅ Y₂) (df : Y₁ ⟶ Y₀)
    (η : Y₀ ⟶ W) (eω : G.obj W ⟶ W') (dRf : X₂ ⟶ X₃) (Θ₀ : X₃ ⟶ G.obj Y₀) (dε : X₃ ⟶ X₄)
    (η' : X₄ ⟶ W') (dcomp : X₁ ⟶ X₄) (hD : dcomp = dσ ≫ dRf ≫ dε)
    (h₁ : Θ₁ ≫ G.map df = dRf ≫ Θ₀) (h₂ : Θ₀ ≫ G.map η ≫ eω = dε ≫ η') :
    (s ≫ dσ ≫ Θ₁ ≫ G.map sh.hom) ≫ G.map ((sh.inv ≫ df) ≫ η) ≫ eω = (s ≫ dcomp) ≫ η' := by
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc, hD]
  rw [reassoc_of% h₁, h₂]

/-- **The identification `H^i(U, K) = Hom((D_U K)[-i], ω_X^•|_U)` of [Stacks, Tag 0G5A] is
compatible with restriction to `V`.** -/
theorem openDualityLinearEquiv_restrict (K : BoundedCoherentDerived U) (i : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
      ((derivedGlobalSectionsOver p).obj K.obj)) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    haveI : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
    haveI := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
    haveI := isNoetherian_of_locallyOfFiniteType c.toBase
    openDualShiftRestrictHom p c V K i ≫
        (restrictBoundedCoherentLift V.ι).map
          (openDualityLinearEquiv p (standardUpperShriekDualizingComplex p c)
            (isDualizingComplex_standardUpperShriekDualizingComplex p c)
            ((restrictBoundedCoherentLift c.immersion).obj (compactificationDualizingObj c))
            (standardUpperShriekDualizingComplexIso p c).symm K i x) ≫
        (compactificationOpenRestrictLiftIso p c V).hom.app (compactificationDualizingObj c) =
      openDualityLinearEquiv (V.ι ≫ p)
        (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
        (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
          (compactificationOpen p c V))
        ((restrictBoundedCoherentLift (compactificationOpen p c V).immersion).obj
          (compactificationDualizingObj (compactificationOpen p c V)))
        (standardUpperShriekDualizingComplexIso (V.ι ≫ p) (compactificationOpen p c V)).symm
        ((restrictBoundedCoherentLift V.ι).obj K) i (cohomologyRestrict p V K i x) := by
  have := isNoetherian_of_locallyOfFiniteType p
  have : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
  have := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
  have := isNoetherian_of_locallyOfFiniteType c.toBase
  let : Linear k U.Modules := modulesLinear k (Over.mk p)
  let : Linear k V.toScheme.Modules := modulesLinear k (Over.mk (V.ι ≫ p))
  set a := (structureSheafHomLinearEquiv p (K⟦i⟧).obj).symm
    ((openDualityCohomologyShiftIso p K i).inv.hom x) with ha
  have hr : (structureSheafHomLinearEquiv (V.ι ≫ p)
        (((restrictBoundedCoherentLift V.ι).obj K)⟦i⟧).obj).symm
        ((openDualityCohomologyShiftIso (V.ι ≫ p) ((restrictBoundedCoherentLift V.ι).obj K)
            i).inv.hom
          (cohomologyRestrict p V K i x)) =
      Stacks.SheafOfModules.derivedUnitRestrictHom V ≫
        (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map a ≫
        (restrictShiftIso p V K i).hom.hom := by
    change cohomologyUnitHomLinearEquiv (V.ι ≫ p) ((restrictBoundedCoherentLift V.ι).obj K) i
      (cohomologyRestrict p V K i x) = _
    simp only [cohomologyRestrict, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rfl
  have hf : (openDualityUnitHomLinearEquiv (V.ι ≫ p) (((restrictBoundedCoherentLift V.ι).obj K)⟦i⟧)
        (Stacks.SheafOfModules.derivedUnitRestrictHom V ≫
          (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map a ≫
          (restrictShiftIso p V K i).hom.hom)) =
      unitRestrictHom p V ≫ (restrictBoundedCoherentLift V.ι).map
        (openDualityUnitHomLinearEquiv p (K⟦i⟧) a) ≫ (restrictShiftIso p V K i).hom :=
    ObjectProperty.hom_ext _ rfl
  rw [openDualityLinearEquiv_apply, openDualityLinearEquiv_apply, hr, hf]
  exact openDualityLinearEquiv_restrict_chase (restrictBoundedCoherentLift V.ι)
    _ _ _ _ _ _ _ _ _ _ _ _
    (by rw [openDualMap_comp, openDualMap_comp]; simp only [Category.assoc])
    (openDualRestrictHom_naturality p c V (openDualityUnitHomLinearEquiv p (K⟦i⟧) a))
    (openDualRestrictHom_structureSheaf p c V)

/-- Let `p : U ⟶ Spec k` be separated of finite type over a field `k`, with a compactification
`c : U ⊆ X` at which `p^!` and `H^*_c` are computed, as in [Stacks, Tag 0G5A]
(`AlgebraicGeometry.compactSupportDualityEquiv`), and let `V ⊆ U` be an open, with the induced
compactification `V ⊆ U ⊆ X` (`AlgebraicGeometry.compactificationOpen`). Then the square

`Hom_k(H^i(U, K), k)       ⟶  H^{-i}_c(U, R𝓗om(K, ω_{U/k}^•))`
`        ↑                                  ↑`
`Hom_k(H^i(V, K|_V), k)    ⟶  H^{-i}_c(V, R𝓗om(K|_V, ω_{V/k}^•))`

commutes, for every `K ∈ D^b_{Coh}(𝒪_U)` and `i ∈ ℤ`: for every linear form `l` on
`H^i(V, K|_V)`, the image of `l ∘ res` under the duality isomorphism of `U` is the image under the
right vertical arrow of the image of `l` under the duality isomorphism of `V`. Here the horizontal
arrows are the isomorphisms of [Stacks, Tag 0G5A], the left vertical arrow is the contragredient
of the restriction map `res : H^i(U, K) ⟶ H^i(V, K|_V)` (`AlgebraicGeometry.cohomologyRestrict`),
and the right vertical arrow is the map of [Stacks, Remark 0G56]
(`AlgebraicGeometry.compactSupportOpenDualMap`): `Rq_*` of the canonical map
`Rj'_!(L|_V) ⟶ Rj_! L` of [Stacks, Tag 0G4Y], read through the canonical identification of
`R𝓗om(K|_V, ω_{V/k}^•)` with `R𝓗om(K, ω_{U/k}^•)|_V`. -/
@[stacks 0G5B]
theorem compactSupportDualityEquiv_restrict (K : BoundedCoherentDerived U) (i : ℤ) :
    haveI := isNoetherian_of_locallyOfFiniteType p
    haveI := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
    ∀ l : Module.Dual k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
      ((derivedGlobalSectionsOver (V.ι ≫ p)).obj ((restrictBoundedCoherentLift V.ι).obj K).obj)),
    compactSupportDualityEquiv p c K i (l ∘ₗ cohomologyRestrict p V K i) =
      compactSupportOpenDualMap p c V K i
        (compactSupportDualityEquiv (V.ι ≫ p) (compactificationOpen p c V)
          ((restrictBoundedCoherentLift V.ι).obj K) i l) := by
  have := isNoetherian_of_locallyOfFiniteType p
  have := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
  have := isNoetherian_of_locallyOfFiniteType c.toBase
  have : IsNoetherian (Over.mk p).left := isNoetherian_of_locallyOfFiniteType p
  have : IsNoetherian (Over.mk (V.ι ≫ p)).left := isNoetherian_of_locallyOfFiniteType (V.ι ≫ p)
  intro l
  exact compactSupportDualityOfPoints_compactificationOpen p c V
    (openDualObj (standardUpperShriekDualizingComplex p c)
      (isDualizingComplex_standardUpperShriekDualizingComplex p c) K)
    (openDualObj (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
      (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
        (compactificationOpen p c V))
      ((restrictBoundedCoherentLift V.ι).obj K)) (-i)
    (openDualityLinearEquiv p (standardUpperShriekDualizingComplex p c)
      (isDualizingComplex_standardUpperShriekDualizingComplex p c)
      ((restrictBoundedCoherentLift c.immersion).obj (compactificationDualizingObj c))
      (standardUpperShriekDualizingComplexIso p c).symm K i)
    (openDualityLinearEquiv (V.ι ≫ p)
      (standardUpperShriekDualizingComplex (V.ι ≫ p) (compactificationOpen p c V))
      (isDualizingComplex_standardUpperShriekDualizingComplex (V.ι ≫ p)
        (compactificationOpen p c V))
      ((restrictBoundedCoherentLift (compactificationOpen p c V).immersion).obj
        (compactificationDualizingObj (compactificationOpen p c V)))
      (standardUpperShriekDualizingComplexIso (V.ι ≫ p) (compactificationOpen p c V)).symm
      ((restrictBoundedCoherentLift V.ι).obj K) i)
    (openDualExtensionByZeroMap p c V K i) (cohomologyRestrict p V K i)
    (fun x => openDualityLinearEquiv_restrict p c V K i x) l

end Compactification

end AlgebraicGeometry
