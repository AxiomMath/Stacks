module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.DisjointUnion.Modules
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale

/-!
# The derived category of a disjoint union of algebraic spaces

Let `Z` be the disjoint union of a family `X i` of algebraic spaces over `S`, with injections
`j i : X i ⟶ Z`. Restriction to the summands identifies `D(𝒪_Z)` with `∏ i, D(𝒪_{X i})` and
`D_QCoh(𝒪_Z)` with `∏ i, D_QCoh(𝒪_{X i})`. Since each `j i` is étale, restriction is the derived
pullback `L(j i)^*`, so the equivalence is `K ↦ (L(j i)^* K)_i`.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_pi'_etaleModulePullback_mapDerivedCategory`: the
  restrictions identify `D(𝒪_Z)` with `∏ i, D(𝒪_{X i})`, for any choice of models of the derived
  categories.
* `AlgebraicGeometry.Space.isEquivalence_pi'_smallEtaleDerivedModulePullback`: the same for the
  derived pullbacks `L(j i)^*`.
* `AlgebraicGeometry.Space.derivedQuasicoherent_iff_forall_derivedQuasicoherentPullback`: an
  object of `D(𝒪_Z)` lies in `D_QCoh(𝒪_Z)` if and only if each of its restrictions does.
* `AlgebraicGeometry.Space.isEquivalence_pi'_quasicoherentDerivedEtalePullback`: the
  restrictions identify `D_QCoh(𝒪_Z)` with `∏ i, D_QCoh(𝒪_{X i})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] modules_abelian Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {ι : Type u} {X : ι → AlgebraicSpaces B S hS} {Z : AlgebraicSpaces B S hS}
  {j : ∀ i, X i ⟶ Z}
  (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Z)
    fun i => (algebraicSpacesToSheaf B S hS).map (j i)))

/-- **The derived category of a disjoint union**, at any models of the derived categories:
restriction to the summands identifies `D(𝒪_Z)` with `∏ i, D(𝒪_{X i})`. -/
theorem isEquivalence_pi'_etaleModulePullback_mapDerivedCategory
    {_ : HasDerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)}
    {_ : ∀ i : ι, HasDerivedCategory (Modules.{u, u} B S hS (X i).1 (X i).2)} :
    (Functor.pi' fun i : ι => (etaleModulePullback.{u, u} B S hS (j i)
      (isEtale_cofanInj_of_isColimit hc i)).mapDerivedCategory).IsEquivalence :=
  have := isEquivalence_pi'_etaleModulePullback_of_isColimit hc
  inferInstance

attribute [local instance] HasDerivedCategory.standard

include hc in
/-- **The derived category of a disjoint union**: the derived pullbacks along the injections
identify `D(𝒪_Z)` with `∏ i, D(𝒪_{X i})`. -/
theorem isEquivalence_pi'_smallEtaleDerivedModulePullback :
    (Functor.pi' (C := fun i : ι => DerivedCategory (Modules.{u, u} B S hS (X i).1 (X i).2))
      fun i : ι => smallEtaleDerivedModulePullback B S hS (j i)).IsEquivalence :=
  @Functor.isEquivalence_of_iso _ _ _ _ _ _ (NatIso.pi' fun i =>
    Functor.pi'CompEval _ i ≪≫
      (smallEtaleDerivedModulePullbackIsoEtale B S hS (j i)
        (isEtale_cofanInj_of_isColimit hc i)).symm ≪≫
      (Functor.pi'CompEval
        (C := fun i : ι => DerivedCategory (Modules.{u, u} B S hS (X i).1 (X i).2))
        (fun i : ι => smallEtaleDerivedModulePullback B S hS (j i)) i).symm)
    (isEquivalence_pi'_etaleModulePullback_mapDerivedCategory hc)

include hc in
/-- **Quasi-coherence on a disjoint union is checked on the summands**: an object of `D(𝒪_Z)`
lies in `D_QCoh(𝒪_Z)` if and only if each of its restrictions to the summands does. -/
theorem derivedQuasicoherent_iff_forall_derivedQuasicoherentPullback
    (K : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :
    DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))) K ↔
      ∀ i : ι,
        DerivedQuasicoherentPullback B S hS (j i) (isEtale_cofanInj_of_isColimit hc i) K := by
  refine ⟨fun h i => derivedQuasicoherent_etaleModulePullback B S hS (j i) _ K h,
    fun h n => ?_⟩
  have := QuasiCoherentDescent.isCoverDense_memberFunctor B S hS X j
    (isEtale_cofanInj_of_isColimit hc) (isEtaleCovering_cofanInj_of_isColimit hc)
  exact QuasiCoherentDescent.isQuasicoherentOnSite_of_forall_etaleModulePullback B S hS X j
    (isEtale_cofanInj_of_isColimit hc) _ fun i =>
      (derivedQuasicoherentPullback_iff B S hS (j i) _ K).1 (h i) n

/-- The restricted étale restriction acts on morphisms of `D_QCoh` as étale restriction. -/
theorem quasicoherentDerivedEtalePullback_map_hom {Y : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    (hf : IsEtale B S hS f.hom) {K L : QuasicoherentDerivedCategory.{u, u} B S hS Z.1 Z.2}
    (φ : K ⟶ L) :
    ((quasicoherentDerivedEtalePullback B S hS f hf).map φ).hom =
      (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.map φ.hom :=
  rfl

include hc in
/-- **The quasi-coherent derived category of a disjoint union**: restriction to the summands
identifies `D_QCoh(𝒪_Z)` with `∏ i, D_QCoh(𝒪_{X i})`. -/
theorem isEquivalence_pi'_quasicoherentDerivedEtalePullback :
    (Functor.pi' fun i : ι => quasicoherentDerivedEtalePullback B S hS (j i)
      (isEtale_cofanInj_of_isColimit hc i)).IsEquivalence := by
  have hΦ : (Functor.pi' fun i : ι => (etaleModulePullback.{u, u} B S hS (j i)
      (isEtale_cofanInj_of_isColimit hc i)).mapDerivedCategory).IsEquivalence :=
    isEquivalence_pi'_etaleModulePullback_mapDerivedCategory hc
  have : (Functor.pi' fun i : ι => quasicoherentDerivedEtalePullback B S hS (j i)
      (isEtale_cofanInj_of_isColimit hc i)).Faithful := by
    refine ⟨fun {K L} φ ψ h => ObjectProperty.hom_ext _ ?_⟩
    refine hΦ.faithful.map_injective (funext fun i => ?_)
    exact (quasicoherentDerivedEtalePullback_map_hom (j i) _ φ).symm.trans
      ((congrArg (fun a => a.hom) (congrFun h i)).trans
        (quasicoherentDerivedEtalePullback_map_hom (j i) _ ψ))
  have : (Functor.pi' fun i : ι => quasicoherentDerivedEtalePullback B S hS (j i)
      (isEtale_cofanInj_of_isColimit hc i)).Full := by
    refine ⟨fun {K L} g => ?_⟩
    obtain ⟨f, hf⟩ := hΦ.full.map_surjective (X := K.obj) (Y := L.obj) fun i => (g i).hom
    exact ⟨ObjectProperty.homMk f, funext fun i => ObjectProperty.hom_ext _ (congrFun hf i)⟩
  have : (Functor.pi' fun i : ι => quasicoherentDerivedEtalePullback B S hS (j i)
      (isEtale_cofanInj_of_isColimit hc i)).EssSurj := by
    refine ⟨fun N => ?_⟩
    obtain ⟨K, ⟨e⟩⟩ := hΦ.essSurj.mem_essImage fun i => (N i).obj
    have hK : DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))) K :=
      (derivedQuasicoherent_iff_forall_derivedQuasicoherentPullback hc K).2 fun i =>
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS (X i).1 (X i).2).O)))).prop_of_iso
          (Pi.isoApp e i).symm (N i).property
    exact ⟨⟨K, hK⟩, ⟨Pi.isoMk fun i => ObjectProperty.isoMk _ (Pi.isoApp e i)⟩⟩
  exact { }

end AlgebraicGeometry.Space

end
