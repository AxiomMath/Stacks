module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeStalkTarget

/-!
# The source chain of the stalk diagram, and the transport of the point

For a cartesian square of schemes with `i : Z ⟶ X` a closed immersion,
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkSourceIso` identifies the derived stalk
at `i' w` of `Lf^*(Ri_* -)` with `𝒪_{X', i' w} ⊗ᴸ_{𝒪_{X, i (g w)}} (-)_{g w}`. This file computes
its components, at an arbitrary object and at a complex, and the components of the transport
`derivedStalkFunctorCongr` of the derived stalk functor along an equality of points.

## Main results

* `StacksDraft.DerivedStalkSourceChase.sourceCollapse`,
  `StacksDraft.DerivedStalkSourceChase.sourceComponentChaseQ`: two identities of composites in
  arbitrary categories.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkFunctorCongr_hom_app_Q` and
  `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkFunctorCongr_inv_app_Q`: the
  components of the transport of the point at a complex.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkFunctorCongr_self`: the transport
  along a self-equality of points is the collapse of derived restriction of scalars.
* `Stacks.Cohomology.ClosedImmersionBaseChange.transportObjEq`: the two transports of a point have
  the same target.
* `Stacks.Cohomology.ClosedImmersionBaseChange.transportResidue`: the transport of the derived
  stalk functor followed by the absorption of the germ comparison is `eqToHom`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkSourceIso_hom_app`: the component of
  the source chain at an object, as the composite of the components of its three nontrivial rungs.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkSourceIso_hom_app_Q`: the component of
  the source chain at a complex.

## Implementation notes

Unfolding `derivedStalkSourceIso` at `DerivedCategory.Q.obj P` runs out of heartbeats, while at a
variable object of the derived category it is cheap; `derivedStalkSourceIso_hom_app_Q` is
therefore obtained from `derivedStalkSourceIso_hom_app` through the abstract identity
`sourceComponentChaseQ`, since the concrete equation is not type-correct at the transparency at
which `rw` and `simp` check their motives. For the same reason `derivedStalkFunctorCongr_self` is
spelled at `(modulesStalkFunctor Y a).mapDerivedCategory` rather than at the same functor
`AlgebraicGeometry.derivedStalkFunctor a`.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

namespace StacksDraft.DerivedStalkSourceChase

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- Removing the identity morphisms from `A ≫ 𝟙 ≫ F.map (B ≫ 𝟙 ≫ G) ≫ F.map 𝟙 ≫ 𝟙 ≫ 𝟙 ≫ E` gives
`A ≫ F.map B ≫ F.map G ≫ E`. -/
theorem sourceCollapse (F : C ⥤ D) {m a₁ a₂ : C} {O₀ O₂ : D}
    (A : O₀ ⟶ F.obj m) (B : m ⟶ a₁) (G : a₁ ⟶ a₂) (E : F.obj a₂ ⟶ O₂) :
    A ≫ CategoryStruct.id (F.obj m) ≫
        F.map (B ≫ CategoryStruct.id a₁ ≫ G) ≫ F.map (CategoryStruct.id a₂) ≫
        CategoryStruct.id (F.obj a₂) ≫ CategoryStruct.id (F.obj a₂) ≫ E =
      A ≫ F.map B ≫ F.map G ≫ E := by
  simp

/-- If `ψ = A ≫ F.map B ≫ F.map (R.map σ) ≫ E` and `σ = S.map c₁ ≫ S.map c₂ ≫ τ`, and if
`B ≫ R.map (S.map (c₁ ≫ c₂)) = b₁ ≫ b₂` and `A ≫ F.map b₁ = x ≫ y`, then
`ψ = x ≫ y ≫ F.map b₂ ≫ F.map (R.map τ) ≫ E`. -/
theorem sourceComponentChaseQ {C' C'' : Type*} [Category C'] [Category C'']
    (F : C ⥤ D) (R : C' ⥤ C) (S : C'' ⥤ C')
    {m p : C} {n₂ : C'} {o₁ o₂ o₃ : C''} {O₀ O₂ N : D}
    {ψ : O₀ ⟶ O₂} {A : O₀ ⟶ F.obj m} {B : m ⟶ R.obj (S.obj o₁)}
    {E : F.obj (R.obj n₂) ⟶ O₂} {σ : S.obj o₁ ⟶ n₂} {c₁ : o₁ ⟶ o₂} {c₂ : o₂ ⟶ o₃}
    {τ : S.obj o₃ ⟶ n₂} {b₁ : m ⟶ p} {b₂ : p ⟶ R.obj (S.obj o₃)}
    {x : O₀ ⟶ N} {y : N ⟶ F.obj p}
    (h₀ : ψ = A ≫ F.map B ≫ F.map (R.map σ) ≫ E)
    (hσ : σ = S.map c₁ ≫ S.map c₂ ≫ τ)
    (hB : B ≫ R.map (S.map (c₁ ≫ c₂)) = b₁ ≫ b₂)
    (hA : A ≫ F.map b₁ = x ≫ y) :
    ψ = x ≫ y ≫ F.map b₂ ≫ F.map (R.map τ) ≫ E := by
  have e₁ : R.map σ = R.map (S.map (c₁ ≫ c₂)) ≫ R.map τ := by
    rw [hσ, S.map_comp, ← R.map_comp, Category.assoc]
  have e₂ : F.map B ≫ F.map (R.map (S.map (c₁ ≫ c₂))) = F.map b₁ ≫ F.map b₂ := by
    rw [← F.map_comp, hB, F.map_comp]
  rw [h₀, e₁]
  simp only [F.map_comp, Category.assoc, reassoc_of% e₂, reassoc_of% hA]

end StacksDraft.DerivedStalkSourceChase

universe u

namespace Stacks.Cohomology.ClosedImmersionBaseChange

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.PerfectComplexTriangles

/-! ### The transport of the point, below `DerivedCategory.Q` -/

section Congr

variable {Y : Scheme.{u}}

/-- For `h : a = b` and a cochain complex `P` of `𝒪_Y`-modules, the component of
`derivedStalkFunctorCongr` at `DerivedCategory.Q.obj P` is the factorization of the stalk functor
at `b`, then the factorization of restriction of scalars along the germ comparison, then
`DerivedCategory.Q` of the degreewise transport `modulesStalkFunctorCongr`, then the factorization
of the stalk functor at `a` read backwards. -/
theorem derivedStalkFunctorCongr_hom_app_Q {a b : Y} (h : a = b)
    (P : CochainComplex Y.Modules ℤ) :
    (derivedStalkFunctorCongr h).hom.app (DerivedCategory.Q.obj P) =
      (ModuleCat.restrictScalars.{u, u, u}
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            b).mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
              (Y.presheaf.stalkCongr
                (Inseparable.of_eq h)).hom.hom).mapDerivedCategoryFactors.hom.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y b).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (modulesStalkFunctorCongr h)
              (ComplexShape.up ℤ)).hom.app P) ≫
            (Stacks.ModuleSkyscraper.modulesStalkFunctor Y
              a).mapDerivedCategoryFactors.inv.app P :=
  StacksDraft.DerivedStalkComponentChase.twoFoldComponentChase rfl
    (mapDerivedCategoryCompIso_inv_app (Stacks.ModuleSkyscraper.modulesStalkFunctor Y b)
      (ModuleCat.restrictScalars.{u, u, u}
        (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom) P)
    (mapDerivedCategoryIsoOfNatIso_hom_app _ _ (modulesStalkFunctorCongr h) P)
    (Iso.inv_hom_id_app _ P)

/-- For `h : a = b` and a cochain complex `P` of `𝒪_Y`-modules, the inverse of
`derivedStalkFunctorCongr` at `DerivedCategory.Q.obj P` is the factorization of the stalk functor
at `a`, then `DerivedCategory.Q` of the degreewise transport read backwards, then the two
factorizations of `(−)_b ⋙ restrictScalars` read backwards. -/
theorem derivedStalkFunctorCongr_inv_app_Q {a b : Y} (h : a = b)
    (P : CochainComplex Y.Modules ℤ) :
    (derivedStalkFunctorCongr h).inv.app (DerivedCategory.Q.obj P) =
      (Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            a).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (modulesStalkFunctorCongr h)
            (ComplexShape.up ℤ)).inv.app P) ≫
          (ModuleCat.restrictScalars.{u, u, u}
                (Y.presheaf.stalkCongr
                  (Inseparable.of_eq h)).hom.hom).mapDerivedCategoryFactors.inv.app
              (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y b).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            (ModuleCat.restrictScalars.{u, u, u}
                (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom).mapDerivedCategory.map
              ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
                b).mapDerivedCategoryFactors.inv.app P) :=
  StacksDraft.DerivedStalkComponentChase.twoFoldComponentChase rfl
    (mapDerivedCategoryIsoOfNatIso_inv_app _ _ (modulesStalkFunctorCongr h) P)
    (mapDerivedCategoryCompIso_hom_app (Stacks.ModuleSkyscraper.modulesStalkFunctor Y b)
      (ModuleCat.restrictScalars.{u, u, u}
        (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom) P)
    (Iso.inv_hom_id_app _ P)

/-- For `h : a = a`, `derivedStalkFunctorCongr h` is the derived stalk functor whiskered with
`StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso` at the germ comparison of `a` with
itself. -/
theorem derivedStalkFunctorCongr_self {a : Y} (h : a = a) :
    derivedStalkFunctorCongr h =
      (Functor.isoWhiskerLeft
          (Stacks.ModuleSkyscraper.modulesStalkFunctor Y a).mapDerivedCategory
          (StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso.{u}
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
            (stalkCongr_self_hom_hom h)) :
        (Stacks.ModuleSkyscraper.modulesStalkFunctor Y a).mapDerivedCategory ⋙
            (ModuleCat.restrictScalars.{u, u, u}
              (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom).mapDerivedCategory ≅
          (Stacks.ModuleSkyscraper.modulesStalkFunctor Y a).mapDerivedCategory) := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)) fun P => ?_)
  have hnat : (ModuleCat.restrictScalars.{u, u, u}
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            a).mapDerivedCategoryFactors.hom.app P) ≫
        (StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso.{u}
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
            (stalkCongr_self_hom_hom h)).hom.app
          (DerivedCategory.Q.obj (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      (StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso.{u}
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
            (stalkCongr_self_hom_hom h)).hom.app
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y a).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P)) ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor Y
          a).mapDerivedCategoryFactors.hom.app P :=
    (StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso.{u}
      (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
      (stalkCongr_self_hom_hom h)).hom.naturality _
  have key : (ModuleCat.restrictScalars.{u, u, u}
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            a).mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
              (Y.presheaf.stalkCongr
                (Inseparable.of_eq h)).hom.hom).mapDerivedCategoryFactors.hom.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (modulesStalkFunctorCongr h)
              (ComplexShape.up ℤ)).hom.app P) ≫
            (Stacks.ModuleSkyscraper.modulesStalkFunctor Y
              a).mapDerivedCategoryFactors.inv.app P =
      (StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso.{u}
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
            (stalkCongr_self_hom_hom h)).hom.app
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y a).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P)) := by
    rw [mapHomologicalComplex_modulesStalkFunctorCongr_hom_app_self h P,
      ← reassoc_of% StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso_hom_app_Q
        (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom (stalkCongr_self_hom_hom h)
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y a).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P),
      reassoc_of% hnat, Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [derivedStalkFunctorCongr_hom_app_Q h P]
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  exact key

/-- For `h : a = b`, derived extension of scalars along `ψ` of the derived stalk at `b` and
derived extension of scalars along `ψ ∘ ε` of the derived stalk at `a`, for `ε` the germ
comparison, are the same object. -/
theorem transportObjEq {a b : Y} (h : a = b) {R' : Type u} [CommRing R']
    (ψ : ToType (Y.presheaf.stalk b) →+* R') (K : DerivedCategory Y.Modules) :
    (totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj
        ((AlgebraicGeometry.derivedStalkFunctor b).obj K) =
      (totalDerivedExtensionScalars.{u, u, u}
          (ψ.comp (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom)).functor.obj
        ((AlgebraicGeometry.derivedStalkFunctor a).obj K) := by
  subst h
  exact congrArg (fun φ => (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
      ((AlgebraicGeometry.derivedStalkFunctor a).obj K))
    ((congrArg ψ.comp (stalkCongr_self_hom_hom (rfl : a = a))).trans
      (RingHom.comp_id ψ)).symm

/-- The transport of the derived stalk functor from `b` to `a` under derived extension of
scalars along `ψ`, followed by the absorption of the germ comparison into `ψ`, is `eqToHom`. -/
theorem transportResidue {a b : Y} (h : a = b) (h' : b = a) {R' : Type u} [CommRing R']
    (ψ : ToType (Y.presheaf.stalk b) →+* R')
    (k₁ : ∀ x, (Y.presheaf.stalkCongr (Inseparable.of_eq h')).hom.hom
        ((Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom x) = x)
    (k₂ : ∀ y, (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
        ((Y.presheaf.stalkCongr (Inseparable.of_eq h')).hom.hom y) = y)
    (K : DerivedCategory Y.Modules) :
    (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
          ((derivedStalkFunctorCongr h').inv.app K) ≫
        (StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
            (Y.presheaf.stalkCongr (Inseparable.of_eq h')).hom.hom k₁ k₂ ψ).hom.app
          ((AlgebraicGeometry.derivedStalkFunctor a).obj K) =
      eqToHom (transportObjEq h ψ K) := by
  subst h
  have h1 := congrArg (fun I => I.inv.app K) (derivedStalkFunctorCongr_self h')
  simp only [Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app] at h1
  have h2 : (derivedStalkFunctorCongr h').inv.app K =
      (StacksDraft.DerivedRingIso.restrictScalarsIdDerivedIso
          (Y.presheaf.stalkCongr (Inseparable.of_eq h')).hom.hom
          (stalkCongr_self_hom_hom h')).inv.app
        ((AlgebraicGeometry.derivedStalkFunctor a).obj K) := h1
  rw [h2, StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso_hom_app_of_eq_id
    (Y.presheaf.stalkCongr (Inseparable.of_eq h')).hom.hom (stalkCongr_self_hom_hom h')
    k₁ k₂ ψ, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp

end Congr

/-! ### The source chain at a free object -/

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}
  [AlgebraicGeometry.IsClosedImmersion i]

/-- The component of `derivedStalkSourceIso` at an object, as the composite of the components
of its three nontrivial rungs: the derived stalk comparison
`AlgebraicGeometry.derivedPullbackStalkIso` for `f` at `i' w`, taken at the derived pushforward
of the object; the transport of the point from `f (i' w)` to `i (g w)` followed by the derived
stalk of `Ri_*` on the image, both under the total derived extension of scalars along the germ map
of `f`; and `derivedExtensionStalkIso`. -/
theorem derivedStalkSourceIso_hom_app (w : Z') (hpt : i (g w) = f (i' w))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    (derivedStalkSourceIso (i' := i') (f := f) w hpt).hom.app K =
      (AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).hom.app
          ((derivedPushforward i.toLRSHom.toShHom).obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor.map
            ((derivedStalkFunctorCongr hpt.symm).inv.app
              ((derivedPushforward i.toLRSHom.toShHom).obj K)) ≫
          (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor.map
              ((ModuleCat.restrictScalars.{u, u, u}
                  (X.presheaf.stalkCongr
                    (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategory.map
                ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing
                  i (g w)).hom.app K)) ≫
            (derivedExtensionStalkIso w hpt).hom.app
              ((ModuleCat.restrictScalars.{u, u, u}
                  (i.stalkMap (g w)).hom).mapDerivedCategory.obj
                ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj K)) := by
  refine Eq.trans ?_ (StacksDraft.DerivedStalkSourceChase.sourceCollapse
    (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor _ _ _ _)
  rfl

/-- For a cochain complex `P` of `𝒪_Z`-modules, the component of `derivedStalkSourceIso` at
`DerivedCategory.Q.obj P` is the derived pullback along `f` and the derived stalk at `i' w` of the
comparison of `Ri_*` with the degreewise pushforward, then the derived stalk comparison for `f` at
`i' w` taken at the *degreewise* pushforward of `P`, then the transport of the point and the last
four factors of the derived stalk of `Ri_*` on the image, both under the total derived extension of
scalars along the germ map of `f`, then `derivedExtensionStalkIso`. -/
theorem derivedStalkSourceIso_hom_app_Q (w : Z') (hpt : i (g w) = f (i' w))
    (P : CochainComplex Z.Modules ℤ) :
    (derivedStalkSourceIso (i' := i') (f := f) w hpt).hom.app (DerivedCategory.Q.obj P) =
      (derivedPullback f.toLRSHom.toShHom ⋙
            AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
                i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P) ≫
            (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app P) ≫
        (AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).hom.app
            (DerivedCategory.Q.obj (((Scheme.Modules.pushforward i).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
          (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor.map
              ((derivedStalkFunctorCongr hpt.symm).inv.app
                (DerivedCategory.Q.obj (((Scheme.Modules.pushforward i).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))) ≫
            (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor.map
                ((ModuleCat.restrictScalars.{u, u, u}
                    (X.presheaf.stalkCongr
                      (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategory.map
                  ((Stacks.ModuleSkyscraper.modulesStalkFunctor X
                        (i (g w))).mapDerivedCategoryFactors.hom.app
                      (((Scheme.Modules.pushforward i).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj P) ≫
                    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
                        (Stacks.ModuleSkyscraper.pushStalkMap i (g w))
                        (ComplexShape.up ℤ)).app P) ≫
                      (ModuleCat.restrictScalars.{u, u, u}
                            (i.toLRSHom.toShHom.hom.stalkMap
                              (g w)).hom).mapDerivedCategoryFactors.inv.app
                          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                            (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
                        (ModuleCat.restrictScalars.{u, u, u}
                            (i.toLRSHom.toShHom.hom.stalkMap (g w)).hom).mapDerivedCategory.map
                          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                            (g w)).mapDerivedCategoryFactors.inv.app P))) ≫
              (derivedExtensionStalkIso w hpt).hom.app
                ((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapDerivedCategory.obj
                  ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj
                    (DerivedCategory.Q.obj P))) :=
  StacksDraft.DerivedStalkSourceChase.sourceComponentChaseQ
    (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor
    (ModuleCat.restrictScalars.{u, u, u}
      (X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategory
    (AlgebraicGeometry.derivedStalkFunctor (i (g w)))
    (derivedStalkSourceIso_hom_app w hpt (DerivedCategory.Q.obj P))
    (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing_hom_app_Q i (g w) P)
    (((derivedStalkFunctorCongr hpt.symm).inv.naturality
      ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
            i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P) ≫
        (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app P)).symm)
    (((AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).hom.naturality
      ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
            i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P) ≫
        (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app P)).symm)

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
