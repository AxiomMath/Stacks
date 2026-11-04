module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction

/-!
# Maps of modules which are isomorphisms over an open subspace

Let `W ⊆ X` be an open subspace with inclusion `j`.  A map `φ : K → K'` of `𝒪_X`-modules whose
pullback `j^*φ` is invertible is bijective on the sections over every étale chart of `X` whose
points lie in `W`: such a chart is the composite of a chart of `W` with `j` (Stacks 03IE), and the
étale restriction of `φ` reads sections over exactly those composites.  Combined with
`AlgebraicGeometry.Space.bijective_localizedMap_geometricModuleStalkLinearMap` this gives the form
in which the stalkwise proof of Stacks 0AF0 uses "an isomorphism over `U`": the map of geometric
stalks becomes bijective after inverting the germ of any regular function whose basic open lies in
`U`.

## Main results

* `AlgebraicGeometry.Space.bijective_val_app_smallEtalePostcomp_of_isIso_modulePullback`: an
  invertible pullback along an étale `j` makes `φ` bijective over the composite charts.
* `AlgebraicGeometry.Space.isIso_modulePullback_map_unit_of_isOpenImmersion`: the pullback of the
  unit `G ⟶ j_*j^*G` along an open immersion is invertible.
* `AlgebraicGeometry.Space.exists_smallEtalePostcomp_eq_of_points`: a chart whose points lie in an
  open subspace comes from a chart of the subspace, by an equality of charts.
* `AlgebraicGeometry.Space.bijective_localizedMap_of_isIso_modulePullback`: **the stalk map of a
  map of quasi-coherent modules which is invertible over `W` becomes bijective after inverting the
  germ of a function whose basic open lies in `W`.**

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of sheaves of modules is bijective on the sections over every object. -/
theorem bijective_val_app_of_isIso {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) [IsIso φ] (T : SmallEtale B S hS X.1) :
    Function.Bijective (φ.val.app (op T)) := by
  let e : M.val.obj (op T) ≅ N.val.obj (op T) :=
    { hom := φ.val.app (op T)
      inv := (inv φ).val.app (op T)
      hom_inv_id := by
        rw [← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, IsIso.hom_inv_id]
        rfl
      inv_hom_id := by
        rw [← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, IsIso.inv_hom_id]
        rfl }
  exact e.toLinearEquiv.bijective

variable {U X : AlgebraicSpaces B S hS} (j : U ⟶ X) (hj : IsEtale B S hS j.hom)

/-- **Étale restriction reads sections on the composite charts.**  If the étale restriction of
`φ` along `j` is an isomorphism, then `φ` is bijective on the sections over every chart of `X`
which is the composite of a chart of `U` with `j`. -/
theorem bijective_val_app_smallEtalePostcomp {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hφ : IsIso ((etaleModulePullback.{u, u} B S hS j hj).map φ)) (T : SmallEtale B S hS U.1) :
    Function.Bijective (φ.val.app (op ((smallEtalePostcomp B S hS j hj).obj T))) :=
  bijective_val_app_of_isIso B S hS ((etaleModulePullback.{u, u} B S hS j hj).map φ) T

/-- The same, with the pullback of Stacks 03LU in place of étale restriction. -/
theorem bijective_val_app_smallEtalePostcomp_of_isIso_modulePullback
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hφ : IsIso ((modulePullback B S hS j).map φ)) (T : SmallEtale B S hS U.1) :
    Function.Bijective (φ.val.app (op ((smallEtalePostcomp B S hS j hj).obj T))) := by
  refine bijective_val_app_smallEtalePostcomp B S hS j hj φ ?_ T
  have h := (modulePullbackIsoEtaleModulePullback B S hS j hj).hom.naturality φ
  have : IsIso ((modulePullback B S hS j).map φ ≫
      (modulePullbackIsoEtaleModulePullback B S hS j hj).hom.app N) := inferInstance
  rw [h] at this
  exact IsIso.of_isIso_comp_left ((modulePullbackIsoEtaleModulePullback B S hS j hj).hom.app M) _

/-- **The unit of Stacks 03LU along an open immersion becomes invertible after pulling back.**
The direct image along an open immersion is fully faithful, so the counit is invertible and the
triangle identity inverts the pullback of the unit. -/
theorem isIso_modulePullback_map_unit_of_isOpenImmersion (hj' : IsOpenImmersion B S hS j.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((modulePullback B S hS j).map ((modulePullbackAdjunction B S hS j).unit.app G)) := by
  have hff := fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj'
  have := hff.full
  have := hff.faithful
  have ht := (modulePullbackAdjunction B S hS j).left_triangle_components G
  have : IsIso ((modulePullback B S hS j).map ((modulePullbackAdjunction B S hS j).unit.app G) ≫
      (modulePullbackAdjunction B S hS j).counit.app ((modulePullback B S hS j).obj G)) := by
    rw [ht]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((modulePullbackAdjunction B S hS j).counit.app ((modulePullback B S hS j).obj G))

/-- The unit `G ⟶ j_*j^*G` along an open immersion is bijective on the sections over every chart
of `X` which comes from a chart of `U`. -/
theorem bijective_unit_val_app_smallEtalePostcomp (hj' : IsOpenImmersion B S hS j.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (T : SmallEtale B S hS U.1) :
    Function.Bijective (((modulePullbackAdjunction B S hS j).unit.app G).val.app
      (op ((smallEtalePostcomp B S hS j hj).obj T))) :=
  bijective_val_app_smallEtalePostcomp_of_isIso_modulePullback B S hS j hj _
    (isIso_modulePullback_map_unit_of_isOpenImmersion B S hS j hj' G) T

/-- **A chart whose points lie in an open subspace comes from a chart of the subspace.**  If
every point of the étale chart `T` of `X` lies in the open subspace `W`, then `T` is the
composite of an étale chart of `W` with the inclusion. -/
theorem exists_smallEtalePostcomp_eq_of_points {X : AlgebraicSpaces B S hS} (W : Subfunctor X.1)
    (hW : IsOpenSubspace B S hS W) (hι : IsEtale B S hS W.ι) (T : SmallEtale B S hS X.1)
    (hT : Set.range (pointsMap B S hS _ T.1.hom) ⊆ Set.range (pointsMap B S hS W.toFunctor W.ι)) :
    ∃ T₀ : SmallEtale B S hS W.toFunctor,
      (smallEtalePostcomp B S hS (X := ⟨W.toFunctor, hW.1⟩) (ObjectProperty.homMk W.ι) hι).obj T₀
        = T := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS X.2
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _) W hW T.1.hom).2 hT
  refine ⟨⟨CostructuredArrow.mk g, ?_⟩, ?_⟩
  · exact presheaf_etale_of_postcomp B S hS (presheaf_etale_of_isOpenImmersion B S hS hW.2)
      T.property hg
  · exact ObjectProperty.FullSubcategory.ext
      (congrArg (fun α : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj T) ⟶ X.1 =>
        (CostructuredArrow.mk α : CostructuredArrow yoneda X.1)) hg)

section Neighborhoods

variable {X : AlgebraicSpaces B S hS} {x : GeometricPoint B S hS X.1}
  (N₀ : SmallEtaleNeighborhood x) (g : chartRing B S hS X.1 X.2 N₀.chart)

/-- The basic-open chart of `g|_M` over a refinement `M` of `N₀` maps into the basic-open chart
of `g`, so its points are among the points of the latter. -/
theorem range_pointsMap_basicOpenChartOver_subset {M : SmallEtaleNeighborhood x} (d : M ⟶ N₀) :
    Set.range (pointsMap B S hS _ (basicOpenChartOver B S hS X x N₀ g d).1.hom) ⊆
      Set.range (pointsMap B S hS _
        (openChart B S hS X.1 N₀.chart ((chartScheme N₀.chart).basicOpen g)).1.hom) := by
  have hO : chartSchemeMap d.hom ⁻¹ᵁ (chartScheme N₀.chart).basicOpen g =
      (chartScheme M.chart).basicOpen (chartRestrict (hF := X.2) d.hom g) :=
    Scheme.preimage_basicOpen_top _ g
  have m : basicOpenChartOver B S hS X x N₀ g d ⟶
      openChart B S hS X.1 N₀.chart ((chartScheme N₀.chart).basicOpen g) := by
    unfold basicOpenChartOver
    rw [← hO]
    exact openChartRestrict B S hS X.1 d.hom ((chartScheme N₀.chart).basicOpen g)
  rw [← yoneda_map_toOver_map_comp_hom m, pointsMap_comp]
  exact Set.range_comp_subset_range _ _

/-- **Isomorphism over an open subspace, read after localizing a stalk.**  Let `φ : K → K'` be a
map of quasi-coherent `𝒪_X`-modules whose pullback to the open subspace `W` is invertible, and
let `g` be a regular function on the chart of a neighbourhood `N₀` of `x̄` whose basic open lies
in `W`.  Then `K_x̄ → K'_x̄` is bijective after inverting the germ of `g`. -/
theorem bijective_localizedMap_of_isIso_modulePullback (W : Subfunctor X.1)
    (hW : IsOpenSubspace B S hS W) {K K' : Modules.{u, u} B S hS X.1 X.2}
    (hK : K.IsQuasicoherentOnSite) (hK' : K'.IsQuasicoherentOnSite) (φ : K ⟶ K')
    (hφ : IsIso ((modulePullback B S hS
      (ObjectProperty.homMk W.ι : (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).map φ))
    (hg : Set.range (pointsMap B S hS _
        (openChart B S hS X.1 N₀.chart ((chartScheme N₀.chart).basicOpen g)).1.hom) ⊆
      Set.range (pointsMap B S hS W.toFunctor W.ι)) :
    Function.Bijective (LocalizedModule.map
      (Submonoid.powers (etaleLocalRingGerm B S hS X.1 x (op N₀) g))
      (geometricModuleStalkLinearMap B S hS X x φ)) := by
  have hι : IsEtale B S hS W.ι := isEtale_of_isOpenImmersion B S hS hW.2
  have key : ∀ (M : SmallEtaleNeighborhood x) (d : M ⟶ N₀), IsAffine (chartScheme M.chart) →
      Function.Bijective (φ.val.app (op (basicOpenChartOver B S hS X x N₀ g d))) := by
    intro M d _
    have hpts := (range_pointsMap_basicOpenChartOver_subset B S hS N₀ g d).trans hg
    obtain ⟨T₀, hT₀⟩ := exists_smallEtalePostcomp_eq_of_points B S hS W hW hι
      (basicOpenChartOver B S hS X x N₀ g d) hpts
    have h := bijective_val_app_smallEtalePostcomp_of_isIso_modulePullback B S hS
      (ObjectProperty.homMk W.ι : (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X) hι φ hφ T₀
    rw [hT₀] at h
    exact h
  exact bijective_localizedMap_geometricModuleStalkLinearMap B S hS X x φ N₀ g hK hK' key

/-- `bijective_localizedMap_of_isIso_modulePullback` for an inclusion `j : U ⟶ X` presented as
the inclusion of the open subspace `W` only up to the definitional identification of `U` with the
algebraic space of `W` (as for the named spaces and inclusions of a formal glueing situation). -/
theorem bijective_localizedMap_of_isIso_modulePullback_of_heq (W : Subfunctor X.1)
    (hW : IsOpenSubspace B S hS W) {U : AlgebraicSpaces B S hS} (j : U ⟶ X)
    (hU : U = ⟨W.toFunctor, hW.1⟩)
    (hj : HEq j (ObjectProperty.homMk W.ι : (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X))
    {K K' : Modules.{u, u} B S hS X.1 X.2}
    (hK : K.IsQuasicoherentOnSite) (hK' : K'.IsQuasicoherentOnSite) (φ : K ⟶ K')
    (hφ : IsIso ((modulePullback B S hS j).map φ))
    (hg : Set.range (pointsMap B S hS _
        (openChart B S hS X.1 N₀.chart ((chartScheme N₀.chart).basicOpen g)).1.hom) ⊆
      Set.range (pointsMap B S hS W.toFunctor W.ι)) :
    Function.Bijective (LocalizedModule.map
      (Submonoid.powers (etaleLocalRingGerm B S hS X.1 x (op N₀) g))
      (geometricModuleStalkLinearMap B S hS X x φ)) := by
  subst hU
  cases eq_of_heq hj
  exact bijective_localizedMap_of_isIso_modulePullback B S hS N₀ g W hW hK hK' φ hφ hg

end Neighborhoods

end AlgebraicGeometry.Space

end
