module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.ChartSliceTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.RepresentedAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFormalPullbackCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentSelfChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Filtration
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08IK, (1) ⇒ (2): coherent cohomology gives pseudo-coherence on a Noetherian space

Let `S` be a scheme, `X` a Noetherian algebraic space over `S` and `E` an object of
`D_QCoh(𝒪_X)`.  If `Hⁱ(E)` is coherent for `i ≥ m` and zero for `i ≫ 0`, then `E` is
`m`-pseudo-coherent.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_isCoherent_homology`: **Stacks 08IK,
  (1) ⇒ (2)**, for a locally Noetherian algebraic space.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_isCoherent_homology_of_isNoetherian`: the same
  for a Noetherian algebraic space.
* `AlgebraicGeometry.Space.isPseudoCoherent_of_isCoherent_homology_of_isNoetherian`: the
  "in particular" in the direction proved here: an object of `D⁻_Coh(𝒪_X)` is pseudo-coherent.

## References

* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] SmallEtale.preservesFiniteLimits_associatedModule

/-- **The restriction of a quasi-coherent module on the scheme of a chart is read off the étale
restriction of a module on `X` whose associated module it is.**  If `N` is a quasi-coherent
module on the scheme `V₀` of an étale chart `V` of `X` and `ε^*N ≅ M|_V` on the small étale site
of `h_V`, then `N` is the restriction of `M` to the scheme of the chart. -/
def chartSchemeIsoOfRepresentedAssociatedModuleIso (V : SmallEtale B S hS X.1)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (N : SheafOfModules.{u}
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)).ringCatSheaf)
    (hN : SheafOfModules.IsQuasicoherent N)
    (e : (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj V)
        (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj V))).obj N ≅
      (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).obj M) :
    N ≅ restrictToChartScheme B S hS X.1 X.2 M V :=
  (restrictToChart_selfChart_representedQuasicoherentIso B S hS
      ((SmallEtale.toOver B S hS X.1).obj V) N hN).symm ≪≫
    (representedZariskiRestrictionFunctor B S hS ((SmallEtale.toOver B S hS X.1).obj V)
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj V))).mapIso e ≪≫
    restrictToChartIsoRestrictToChartScheme B S hS _ _ _ ≪≫
    eqToIso (restrictToChartScheme_etaleModulePullback_idEtaleChart B S hS X M V)

/-- **Stacks 08IK, (1) ⇒ (2), on an affine Noetherian étale chart.**  Let `E` be an object of
`D(𝒪_X)` with quasi-coherent cohomology, coherent in degrees `≥ m` and zero above `b`.  Over a
Noetherian affine étale chart `V` of `X`, the étale restriction `E|_V` is `m`-pseudo-coherent on
the small étale site of the algebraic space represented by `V`. -/
theorem isPseudoCoherentFrom_etaleModulePullback_chartToSpace (V : SmallEtale B S hS X.1)
    (hV : IsNoetherianAffineChart B S hS X.1 V)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m b : ℤ)
    (hqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        E).IsQuasicoherentOnSite)
    (hcoh : ∀ i : ℤ, m ≤ i →
      IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ i).obj E))
    (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj E)) :
    (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1
      (chartSpace B S hS X V).2).IsPseudoCoherentFrom
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E) m := by
  let T := (SmallEtale.toOver B S hS X.1).obj V
  let F := etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
    (isEtale_chartToSpace B S hS X V)
  have hH : ∀ i : ℤ, (DerivedCategory.homologyFunctor _ i).obj (F.mapDerivedCategory.obj E) ≅
      F.obj ((DerivedCategory.homologyFunctor _ i).obj E) := fun i =>
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app E
  have hM' : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))) (F.mapDerivedCategory.obj E) := fun n =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso (hH n).symm
      (isQuasicoherentOnSite_etaleModulePullback_chartToSpace B S hS X _ (hqc n) V)
  obtain ⟨ω, hωqc, ⟨eω⟩⟩ :=
    exists_representedDerivedAssociatedModule_iso B S hS T (F.mapDerivedCategory.obj E) hM'
  let G := representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  have hG : ∀ i : ℤ, G.obj ((DerivedCategory.homologyFunctor _ i).obj ω) ≅
      F.obj ((DerivedCategory.homologyFunctor _ i).obj E) := fun i =>
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso G i).app ω).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso eω ≪≫ hH i
  have hN : ∀ i : ℤ, (DerivedCategory.homologyFunctor _ i).obj ω ≅
      chartSchemeModule B S hS X
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E) (hqc i) V :=
    fun i =>
    chartSchemeIsoOfRepresentedAssociatedModuleIso B S hS X V _ _ (hωqc i) (hG i) ≪≫
      restrictToChartSchemeIsoChartSchemeModule B S hS X _ (hqc i) V
  have : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj T) :=
    isNoetherian_chartScheme_of_isNoetherianAffineChart B S hS X V hV
  have hpc0 : RingedSpace.IsPseudoCoherentFrom
      (X := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) ω m := by
    refine (isPseudoCoherentFrom_iff_coherent_homology ((BigFppfOver.toScheme B S hS).obj T)
      ⟨ω, hωqc⟩ m).2 ⟨fun i hi => ?_, ⟨b, fun i hi => ?_⟩⟩
    · exact Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso' (hN i)
        (isCoherent_chartSchemeModule B S hS X _ (hcoh i hi) V hV)
    · refine isZero_of_isZero_representedAssociatedModule B S hS T
        (isAlgebraicSpace_yoneda B S hS T) _ (hωqc i) ?_
      exact (Functor.map_isZero F (hb i hi)).of_iso (hG i)
  exact RingedSite.isPseudoCoherentFrom_of_iso _ m
    (isPseudoCoherentFrom_representedDerivedAssociatedModule B S hS T ω m hpc0) eω.symm

/-- **Stacks 08IK, (1) ⇒ (2)**, over a locally Noetherian algebraic space.  Let `E` be an object
of `D(𝒪_X)` with quasi-coherent cohomology sheaves which are coherent in every degree `≥ m` and
vanish in every degree `> b`.  Then `E` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_isCoherent_homology
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m b : ℤ)
    (hqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        E).IsQuasicoherentOnSite)
    (hcoh : ∀ i : ℤ, m ≤ i →
      IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ i).obj E))
    (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj E)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m := by
  have := Fact.mk hN
  refine isPseudoCoherentFrom_of_forall_affineChart_etaleModulePullback B S hS X E m fun V hV => ?_
  exact isPseudoCoherentFrom_etaleModulePullback_chartToSpace B S hS X V
    (isNoetherianAffineChart_of_isAffine B S hS X.1 X.2 hV) E m b hqc hcoh hb

/-- On a Noetherian algebraic space, an object of `D_QCoh(𝒪_X)` whose cohomology is coherent in
degrees `≥ m` and zero in degrees `> b` is `m`-pseudo-coherent. -/
@[stacks 08IK "(1) ⇒ (2)"]
theorem isPseudoCoherentFrom_of_isCoherent_homology_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXN : IsNoetherian B S hS hZ X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m b : ℤ)
    (hqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        E).IsQuasicoherentOnSite)
    (hcoh : ∀ i : ℤ, m ≤ i →
      IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ i).obj E))
    (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj E)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m :=
  isPseudoCoherentFrom_of_isCoherent_homology B S hS X hXN.2.2 E m b hqc hcoh hb

/-- On a Noetherian algebraic space an object of `D(𝒪_X)` with coherent cohomology sheaves
vanishing in large degrees is pseudo-coherent. -/
@[stacks 08IK "in particular: an object of D⁻_Coh is pseudo-coherent"]
theorem isPseudoCoherent_of_isCoherent_homology_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXN : IsNoetherian B S hS hZ X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ i : ℤ, IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ i).obj E))
    (hb : DerivedCategoryB.IsBoundedAbove E) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E := by
  obtain ⟨b, hb⟩ := hb
  have h : ∀ m : ℤ, (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m := fun m =>
    isPseudoCoherentFrom_of_isCoherent_homology_of_isNoetherian B S hS X hZ hXN E m b
      (fun i => (hcoh i).toIsQuasicoherentOnSite) (fun i _ => hcoh i) hb
  refine ⟨DerivedCategory.Q.objPreimage E, fun m => ?_, ⟨DerivedCategory.Q.objObjPreimageIso E⟩⟩
  exact RingedSite.isPseudoCoherentComplexFrom_of_iso_general _ E m (h m) _
    (DerivedCategory.Q.objObjPreimageIso E)

end AlgebraicGeometry.Space

end
