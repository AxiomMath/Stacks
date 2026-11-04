module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtFromStrictlyPerfectResolution

/-!
# Naturality in the target of the Ext sheaves of a strictly perfect resolution

Let `(X, O_X)` be a ringed space and let `P` be a bounded complex of `O_X`-modules each of whose
terms is a direct summand of a finite free module. For a complex `K` resolved by `P`, that is
for a quasi-isomorphism `P ⟶ K`, the Ext sheaf `Ext^n_{O_X}(K, M)` is the `n`-th cohomology
sheaf of the internal Hom complex `SheafHom^•(P, M)`, for every complex `M` of `O_X`-modules.

This file proves that the identification is natural in `M`. A morphism `α : M ⟶ M'` of complexes
acts on the Ext sheaves as the map induced covariantly by `Q(α)` in the second variable, and on
the cohomology sheaves as the map induced by the morphism of internal Hom complexes
`SheafHom^•(P, M) ⟶ SheafHom^•(P, M')`; the resulting square commutes. So the Ext sheaves out of
a fixed source, computed through a fixed strictly perfect resolution of it, form a functor in the
target, and that functor is `SheafHom^•(P, -)` followed by the `n`-th cohomology sheaf.

## Main results

* `Stacks.SheafOfModules.derivedSheafExtIsoHomologySheafHomComplex_naturality_target`: the
  derived-category form of the identification is natural in the target.
* `Stacks.SheafOfModules.derivedSheafExtIsoHomologyOfResolution_naturality_target`: the
  resolution form of the identification is natural in the target.

## References

* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08I5](https://stacks.math.columbia.edu/tag/08I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- Three commuting squares laid end to end paste to a commuting rectangle. -/
private lemma paste_three_squares {C : Type*} [Category C] {E E' F F' G G' L L' : C}
    (f₁ : E ⟶ E') (f₂ : E ⟶ F) (f₂' : E' ⟶ F') (d : F ⟶ F') (b : F ⟶ G) (b' : F' ⟶ G')
    (g : G ⟶ G') (v : G ⟶ L) (v' : G' ⟶ L') (w : L ⟶ L')
    (h₁ : f₁ ≫ f₂' = f₂ ≫ d) (h₂ : d ≫ b' = b ≫ g) (h₃ : g ≫ v' = v ≫ w) :
    f₁ ≫ f₂' ≫ b' ≫ v' = (f₂ ≫ b ≫ v) ≫ w := by
  simp only [Category.assoc]
  rw [← h₃, ← Category.assoc b, ← h₂, Category.assoc d, ← Category.assoc f₂, ← h₁,
    Category.assoc f₁]

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (P M : CochainComplex (StructureSheafModules Rc) ℤ)

/-- The identification of Ext sheaves with the cohomology of the naive Hom complex is natural in
the target: for `P` bounded with every term a direct summand of a finite free `O_X`-module, for `A`
an object of `D(O_X)` presented by an isomorphism `Q(P) ≅ A`, and for a morphism `α : M ⟶ M'` of
complexes, the square formed by `Stacks.SheafOfModules.derivedSheafExtIsoHomologySheafHomComplex`
at `M` and at `M'`, the map of Ext sheaves induced by `Q(α)` in the second variable, and the map on
cohomology sheaves induced by `α` on internal Hom complexes, commutes. -/
theorem derivedSheafExtIsoHomologySheafHomComplex_naturality_target (n : ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (P.X i))
    (A : DerivedCategory (StructureSheafModules Rc))
    (e : DerivedCategory.Q.obj P ≅ A)
    {M' : CochainComplex (StructureSheafModules Rc) ℤ} (α : M ⟶ M') :
    derivedSheafExtMap Rc n (𝟙 A) (DerivedCategory.Q.map α) ≫
        (derivedSheafExtIsoHomologySheafHomComplex Rc P M' n hbdd hterm A e).hom =
      (derivedSheafExtIsoHomologySheafHomComplex Rc P M n hbdd hterm A e).hom ≫
        HomologicalComplex.homologyMap (RingedSite.homMap (ringedSite Rc) (𝟙 P) α) n := by
  have hM := strictlyPerfectHomComparison_isIso Rc P M hbdd hterm
  have hM' := strictlyPerfectHomComparison_isIso Rc P M' hbdd hterm
  have hcmp : DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 P) α) ≫
        strictlyPerfectHomComparison Rc P M' =
      strictlyPerfectHomComparison Rc P M ≫
        derivedSheafHomMap Rc (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map α) :=
    (RingedSite.strictlyPerfectHomComparison_naturality
        (ringedSite Rc) (derivedInternalHom Rc) P P M M' (𝟙 P) α).trans
      (congrArg (fun u : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P =>
          strictlyPerfectHomComparison Rc P M ≫
            derivedSheafHomMap Rc u (DerivedCategory.Q.map α))
        (DerivedCategory.Q.map_id P))
  have hA : (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 P) α)) ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (strictlyPerfectHomComparison Rc P M') =
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (strictlyPerfectHomComparison Rc P M) ≫
        derivedSheafExtMap Rc n (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map α) :=
    (((DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map_comp
          (DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 P) α))
          (strictlyPerfectHomComparison Rc P M')).symm.trans
      (congrArg (fun u => (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map u)
        hcmp)).trans
      ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map_comp
        (strictlyPerfectHomComparison Rc P M)
        (derivedSheafHomMap Rc (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map α)))
  have key : derivedSheafExtMap Rc n (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map α) ≫
        ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).mapIso
          (@asIso _ _ _ _ _ hM')).inv =
      ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).mapIso
          (@asIso _ _ _ _ _ hM)).inv ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 P) α)) := by
    rw [Iso.comp_inv_eq, Category.assoc]
    exact (Iso.eq_inv_comp _).mpr hA.symm
  have hsplit : derivedSheafExtMap Rc n (𝟙 A) (DerivedCategory.Q.map α) ≫
        derivedSheafExtMap Rc n e.hom (𝟙 (DerivedCategory.Q.obj M')) =
      derivedSheafExtMap Rc n e.hom (𝟙 (DerivedCategory.Q.obj M)) ≫
        derivedSheafExtMap Rc n (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map α) := by
    rw [derivedSheafExtMap_comp, derivedSheafExtMap_comp]
    simp only [Category.comp_id, Category.id_comp]
  have hfac := DerivedCategory.homologyFunctorFactors_hom_naturality
    (C := StructureSheafModules Rc) (RingedSite.homMap (ringedSite Rc) (𝟙 P) α) n
  dsimp only [derivedSheafExtIsoHomologySheafHomComplex, Iso.trans_hom]
  exact paste_three_squares _ _ _ _ _ _ _ _ _ _ hsplit key hfac

/-- The Ext sheaves computed by a strictly perfect resolution are natural in the target. Let
`π : P ⟶ K` be a quasi-isomorphism with `P` bounded and every term of `P` a direct summand of a
finite free `O_X`-module, and let `α : M ⟶ M'` be a morphism of complexes. The identification
`Stacks.SheafOfModules.derivedSheafExtIsoHomologyOfResolution` carries the map of Ext sheaves
`Ext^n_{O_X}(K, M) ⟶ Ext^n_{O_X}(K, M')` induced by `Q(α)` to the map
`H^n(SheafHom^•(P, M)) ⟶ H^n(SheafHom^•(P, M'))` induced by `α` on internal Hom complexes. -/
theorem derivedSheafExtIsoHomologyOfResolution_naturality_target (n : ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (P.X i))
    {K : CochainComplex (StructureSheafModules Rc) ℤ} (π : P ⟶ K) [QuasiIso π]
    {M' : CochainComplex (StructureSheafModules Rc) ℤ} (α : M ⟶ M') :
    derivedSheafExtMap Rc n (𝟙 (DerivedCategory.Q.obj K)) (DerivedCategory.Q.map α) ≫
        (derivedSheafExtIsoHomologyOfResolution Rc P M' n hbdd hterm π).hom =
      (derivedSheafExtIsoHomologyOfResolution Rc P M n hbdd hterm π).hom ≫
        HomologicalComplex.homologyMap (RingedSite.homMap (ringedSite Rc) (𝟙 P) α) n := by
  have : IsIso (DerivedCategory.Q.map π) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ π).2 inferInstance
  exact derivedSheafExtIsoHomologySheafHomComplex_naturality_target Rc P M n hbdd hterm
    (DerivedCategory.Q.obj K) (asIso (DerivedCategory.Q.map π)) α

end Stacks.SheafOfModules

end
