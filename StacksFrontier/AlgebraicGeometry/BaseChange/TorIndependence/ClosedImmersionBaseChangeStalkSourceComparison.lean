module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeStalkSource

/-!
# The source chain of the stalk diagram, against the comparison of Stacks 0661

For a cochain complex `P` of `𝒪_Z`-modules, the source chain
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkSourceIso` at `DerivedCategory.Q.obj P`,
followed by the comparison `alphaG` of Stacks 0661, is the derived pullback along `f` and the
derived stalk of the comparison of `Ri_*` with the degreewise pushforward, followed by
`DerivedCategory.Q` of a map of complexes. No hypothesis on `P` is needed.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkSourceIso_hom_app_Q_comp_alphaG`: the
  source chain at a complex, against the comparison of Stacks 0661.
* `Stacks.Cohomology.ClosedImmersionBaseChange.germTransport_comp_restrictFactors`: the transport
  of the point, followed by the germ bridge of the closed immersion and the factorization of
  restriction of scalars, is the factorization of the stalk functor at `f (i' w)` followed by
  `DerivedCategory.Q` of a map of complexes.
* `StacksDraft.DerivedStalkSourceComparisonChase.germChase` and
  `StacksDraft.DerivedStalkSourceComparisonChase.sourceComparisonChase`: the two diagram chases
  behind them, at free objects and morphisms of arbitrary categories.

## Implementation notes

The concrete equations mix `AlgebraicGeometry.Scheme.Modules` with
`CategoryTheory.SheafOfModules (structureSheafRing _)` and the two germ-map spellings
`i.stalkMap` and `i.toLRSHom.toShHom.hom.stalkMap`, which are definitionally but not reducibly
equal, so such a goal is not type-correct at the transparency at which `rw`, `simp` and `conv`
check their motives. The chases are therefore stated for free objects and morphisms and applied
by `exact`.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

namespace StacksDraft.DerivedStalkSourceComparisonChase

variable {C : Type*} [Category C] {C' : Type*} [Category C'] {D : Type*} [Category D]

/-- For a functor `Rc`, if `ν = u₁ ≫ u₂ ≫ u₃ ≫ Rc.map sinv`, `sinv ≫ c₁ = 𝟙`,
`u₃ ≫ Rc.map c₂ = w ≫ u₃'`, `u₃' ≫ fc = 𝟙` and `θ = u₂ ≫ w`, then
`ν ≫ Rc.map (c₁ ≫ c₂) ≫ fc = u₁ ≫ θ`. -/
theorem germChase (Rc : C' ⥤ C) {m a₁ a₂ a₃ : C} {b₁ b₂ b₃ : C'}
    (u₁ : m ⟶ a₁) (u₂ : a₁ ⟶ a₂) (u₃ : a₂ ⟶ Rc.obj b₁) (sinv : b₁ ⟶ b₂) (c₁ : b₂ ⟶ b₁)
    (c₂ : b₁ ⟶ b₃) (fc : Rc.obj b₃ ⟶ a₃) (w : a₂ ⟶ a₃) (u₃' : a₃ ⟶ Rc.obj b₃)
    {ν : m ⟶ Rc.obj b₂} {θ : a₁ ⟶ a₃}
    (hν : ν = u₁ ≫ u₂ ≫ u₃ ≫ Rc.map sinv)
    (hs : sinv ≫ c₁ = CategoryStruct.id b₁)
    (hnat : u₃ ≫ Rc.map c₂ = w ≫ u₃')
    (hfc : u₃' ≫ fc = CategoryStruct.id a₃)
    (hθ : θ = u₂ ≫ w) :
    ν ≫ Rc.map (c₁ ≫ c₂) ≫ fc = u₁ ≫ θ := by
  rw [hν, hθ, Rc.map_comp]
  slice_lhs 4 5 => rw [← Rc.map_comp, hs, Rc.map_id]
  rw [Category.id_comp]
  slice_lhs 3 4 => rw [hnat]
  slice_lhs 4 5 => rw [hfc]
  simp

/-- For functors `F`, `Rc` and `LG`, if `ψ = A ≫ Bst ≫ F.map ν ≫ F.map (Rc.map μfull) ≫ EX`,
`μfull = μ ≫ ρ`, `ρ ≫ r = 𝟙`, `F.map (Rc.map ρ) ≫ EX = E3 ≫ LG.map ρ`,
`E3 ≫ α = F.map fc ≫ cmpM ≫ qe`, `ν ≫ Rc.map μ ≫ fc = sfm ≫ qθ`,
`F.map qθ ≫ cmpM = cmpA ≫ qx` and `Bst ≫ F.map sfm ≫ cmpA = G₁ ≫ G₂`, then
`ψ ≫ LG.map r ≫ α = A ≫ G₁ ≫ G₂ ≫ qx ≫ qe`. -/
theorem sourceComparisonChase (F : C ⥤ D) (Rc : C' ⥤ C) (LG : C' ⥤ D)
    {O₀ N : D} {m a a₃ : C} {b₂ b₃ bX : C'} {Ω Ω' Ω'' Ω₃ : D}
    (A : O₀ ⟶ N) (Bst : N ⟶ F.obj m) (ν : m ⟶ Rc.obj b₂) (μ : b₂ ⟶ b₃) (ρ : b₃ ⟶ bX)
    (EX : F.obj (Rc.obj bX) ⟶ LG.obj bX) (E3 : F.obj (Rc.obj b₃) ⟶ LG.obj b₃)
    (r : bX ⟶ b₃) (α : LG.obj b₃ ⟶ Ω) (fc : Rc.obj b₃ ⟶ a₃)
    (cmpM : F.obj a₃ ⟶ Ω') (qe : Ω' ⟶ Ω) (sfm : m ⟶ a) (qθ : a ⟶ a₃)
    (cmpA : F.obj a ⟶ Ω'') (qx : Ω'' ⟶ Ω') (G₁ : N ⟶ Ω₃) (G₂ : Ω₃ ⟶ Ω'')
    (μfull : b₂ ⟶ bX) {ψ : O₀ ⟶ LG.obj bX}
    (h₀ : ψ = A ≫ Bst ≫ F.map ν ≫ F.map (Rc.map μfull) ≫ EX)
    (hsplit : μfull = μ ≫ ρ)
    (hρr : ρ ≫ r = CategoryStruct.id b₃)
    (hnatE : F.map (Rc.map ρ) ≫ EX = E3 ≫ LG.map ρ)
    (hE : E3 ≫ α = F.map fc ≫ cmpM ≫ qe)
    (hgerm : ν ≫ Rc.map μ ≫ fc = sfm ≫ qθ)
    (hcmp : F.map qθ ≫ cmpM = cmpA ≫ qx)
    (hchar : Bst ≫ F.map sfm ≫ cmpA = G₁ ≫ G₂) :
    ψ ≫ LG.map r ≫ α = A ≫ G₁ ≫ G₂ ≫ qx ≫ qe := by
  rw [h₀, hsplit]
  rw [Rc.map_comp, F.map_comp]
  slice_lhs 5 6 => rw [hnatE]
  slice_lhs 6 7 => rw [← LG.map_comp, hρr, LG.map_id]
  rw [Category.id_comp]
  slice_lhs 5 6 => rw [hE]
  slice_lhs 3 5 => rw [← F.map_comp, ← F.map_comp, hgerm]
  rw [F.map_comp]
  slice_lhs 4 5 => rw [hcmp]
  slice_lhs 2 4 => rw [hchar]
  simp

end StacksDraft.DerivedStalkSourceComparisonChase

universe u

namespace Stacks.Cohomology.ClosedImmersionBaseChange

attribute [local instance] HasDerivedCategory.standard

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}
  [AlgebraicGeometry.IsClosedImmersion i]

omit [AlgebraicGeometry.IsClosedImmersion i] in
/-- The inverse transport of the point from `f (i' w)` to `i (g w)`,
followed by the derived stalk of the comparison of `Ri_*` with the degreewise pushforward and the
factorization of restriction of scalars along the germ map of `i`, is the factorization of the
stalk functor at `f (i' w)` followed by `DerivedCategory.Q` of the degreewise transport and the
degreewise germ bridge. -/
theorem germTransport_comp_restrictFactors (w : Z') (hpt : i (g w) = f (i' w))
    (P : CochainComplex Z.Modules ℤ) :
    (derivedStalkFunctorCongr hpt.symm).inv.app
          (DerivedCategory.Q.obj (((Scheme.Modules.pushforward i).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (X.presheaf.stalkCongr
              (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X
                (i (g w))).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pushforward i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pushStalkMap i (g w)) (ComplexShape.up ℤ)).app P)) ≫
        (ModuleCat.restrictScalars.{u, u, u}
              (X.presheaf.stalkCongr
                (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.restrictScalars.{u, u, u}
              (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) =
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X
            (f (i' w))).mapDerivedCategoryFactors.hom.app
          (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (modulesStalkFunctorCongr hpt.symm)
                (ComplexShape.up ℤ)).inv.app
              (((Scheme.Modules.pushforward i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            ((ModuleCat.restrictScalars.{u, u, u}
              (X.presheaf.stalkCongr
                (Inseparable.of_eq hpt.symm)).hom.hom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
              ((NatTrans.mapHomologicalComplex
                (Stacks.ModuleSkyscraper.pushStalkMap i (g w)) (ComplexShape.up ℤ)).app P)) :=
  StacksDraft.DerivedStalkSourceComparisonChase.germChase
    (ModuleCat.restrictScalars.{u, u, u}
      (X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategory
    _ _ _ _ _ _ _ _ _
    (derivedStalkFunctorCongr_inv_app_Q hpt.symm
      (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (Iso.inv_hom_id_app
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X (i (g w))).mapDerivedCategoryFactors
      (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (((ModuleCat.restrictScalars.{u, u, u}
        (X.presheaf.stalkCongr
          (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategoryFactors.inv.naturality
      ((NatTrans.mapHomologicalComplex
        (Stacks.ModuleSkyscraper.pushStalkMap i (g w)) (ComplexShape.up ℤ)).app P)).symm)
    (Iso.inv_hom_id_app
      (ModuleCat.restrictScalars.{u, u, u}
        (X.presheaf.stalkCongr
          (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategoryFactors
      (((ModuleCat.restrictScalars.{u, u, u}
        (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)))
    (DerivedCategory.Q.map_comp _ _)

/-- For a cochain complex `P` of `𝒪_Z`-modules, the component of `derivedStalkSourceIso` at
`DerivedCategory.Q.obj P`, followed by the two factorizations that carry the derived stalk at
`g w` to `DerivedCategory.Q` of the stalk complex and by the comparison `alphaG`, is the derived
pullback along `f` and the derived stalk at `i' w` of the comparison of `Ri_*` with the degreewise
pushforward, then the derived stalk of the canonical map
`AlgebraicGeometry.pullbackComparisonOnComplex` from the derived pullback to the degreewise
pullback, then the factorization of the stalk functor at `i' w` and `DerivedCategory.Q` of a map
of complexes. -/
theorem derivedStalkSourceIso_hom_app_Q_comp_alphaG (w : Z') (hpt : i (g w) = f (i' w))
    (P : CochainComplex Z.Modules ℤ) :
    (derivedStalkSourceIso (i' := i') (f := f) w hpt).hom.app (DerivedCategory.Q.obj P) ≫
        (Lg w hpt).map
          ((ModuleCat.restrictScalars.{u, u, u}
                (i.stalkMap (g w)).hom).mapDerivedCategory.map
              ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                (g w)).mapDerivedCategoryFactors.hom.app P) ≫
            (ModuleCat.restrictScalars.{u, u, u}
                (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.hom.app
              (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
        (alphaG w hpt).app
          (((ModuleCat.restrictScalars.{u, u, u}
              (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) =
      (derivedPullback f.toLRSHom.toShHom ⋙
            AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
                i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P) ≫
            (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app P) ≫
        (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
            (AlgebraicGeometry.pullbackComparisonOnComplex f
              (((Scheme.Modules.pushforward i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X'
                (i' w)).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((Scheme.Modules.pushforward i).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                  (Stacks.ModuleSkyscraper.pullbackStalkIso f (i' w)).symm
                  (ComplexShape.up ℤ)).hom.app
                (((Scheme.Modules.pushforward i).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))) ≫
          DerivedCategory.Q.map
              (((ModuleCat.extendScalars.{u, u, u}
                  (f.stalkMap (i' w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).map
                ((NatIso.mapHomologicalComplex (modulesStalkFunctorCongr hpt.symm)
                      (ComplexShape.up ℤ)).inv.app
                    (((Scheme.Modules.pushforward i).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj P) ≫
                  ((ModuleCat.restrictScalars.{u, u, u}
                    (X.presheaf.stalkCongr
                      (Inseparable.of_eq hpt.symm)).hom.hom).mapHomologicalComplex
                        (ComplexShape.up ℤ)).map
                    ((NatTrans.mapHomologicalComplex
                      (Stacks.ModuleSkyscraper.pushStalkMap i (g w))
                        (ComplexShape.up ℤ)).app P))) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (StacksDraft.DerivedRingIso.extendScalarsRestrictIso
                  (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom
                  (X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom.hom
                  (stalkCongr_symm_hom_hom_apply hpt) (stalkCongr_hom_symm_hom_apply hpt)
                  (f.stalkMap (i' w)).hom).hom (ComplexShape.up ℤ)).app
                (((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) := by
  have hρr :
      ((ModuleCat.restrictScalars.{u, u, u}
            (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.inv.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i.stalkMap (g w)).hom).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
            (g w)).mapDerivedCategoryFactors.inv.app P)) ≫
      ((ModuleCat.restrictScalars.{u, u, u}
            (i.stalkMap (g w)).hom).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
            (g w)).mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.hom.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) = CategoryStruct.id _ := by
    simp only [Functor.comp_obj, Category.assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  exact StacksDraft.DerivedStalkSourceComparisonChase.sourceComparisonChase
    (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor
    (ModuleCat.restrictScalars.{u, u, u}
      (X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategory
    (Lg w hpt)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedStalkSourceIso_hom_app_Q w hpt P)
    (Category.assoc _ _ _).symm
    hρr
    ((derivedExtensionStalkIso w hpt).hom.naturality _)
    (derivedExtensionStalkIso_hom_app_Q_comp_alphaG w hpt
      (((ModuleCat.restrictScalars.{u, u, u}
          (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)))
    (germTransport_comp_restrictFactors w hpt P)
    ((totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).comparison.naturality _)
    (AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison f (i' w)
      (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
