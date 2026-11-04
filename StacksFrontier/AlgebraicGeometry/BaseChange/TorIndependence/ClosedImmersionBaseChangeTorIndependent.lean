module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeStalkRings
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMapUnderived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingPushforwardColimits
public import StacksFrontier.AlgebraicGeometry.Bridge.SchemeBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# Tor-independent base change along a closed immersion

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

where `i` is a closed immersion.  If `Z` and `X'` are Tor independent over `X`, then
`Ri'_* ∘ Lg^* = Lf^* ∘ Ri_*` as functors `D(𝒪_Z) ⟶ D(𝒪_{X'})`: the canonical derived base change
map `Lf^*(Ri_* K) ⟶ Ri'_*(Lg^* K)` of Stacks 08HY is an isomorphism for every `K`.

The proof follows the source.  Invertibility is tested on derived stalks; away from `Z'` both
sides vanish.  At a point `i' w`, write `K` as the class of a K-flat complex `P`.  Since `i_*` and
`i'_*` are exact, and `Lg^*` is computed on `P` by `g^*`, the base change map at `P` is the
comparison `Lf^*(i_* P) ⟶ f^*(i_* P)` followed by the underived base change map
`f^*(i_* P) ⟶ i'_*(g^* P)` (`derivedBaseChangeMap_Qh_comparison`).  On stalks at `i' w` the first
is the comparison `(i_*P)_{x} ⊗ᴸ 𝒪_{X',i'w} ⟶ (i_*P)_{x} ⊗ 𝒪_{X',i'w}`, which is invertible by
Tor independence, `(i_*P)_x` being the restriction of the K-flat complex `P_{gw}`; the second is
invertible because `𝒪_{Z',w} = 𝒪_{Z,gw} ⊗ 𝒪_{X',i'w}`.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedStalk_derivedBaseChangeMap_onImage`:
  the derived stalk of the base change map at a point of `Z'` is invertible.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareAsIso`: **Stacks 0E23**, the
  isomorphism of functors `Lf^* ∘ Ri_* ≅ Ri'_* ∘ Lg^*`.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

noncomputable section

namespace Stacks.Cohomology.ClosedImmersionBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Two-out-of-three for isomorphisms, with the composite given first -/

section TwoOutOfThree

universe v₀ u₀ v₉ u₉ v₈ u₈

variable {𝒞 : Type u₀} [Category.{v₀} 𝒞] {A B E : 𝒞} {a : A ⟶ B} {b : B ⟶ E}

/-- If `a ≫ b` and `b` are isomorphisms, so is `a`. -/
theorem isIso_of_isIso_comp_of_isIso_right (hab : IsIso (a ≫ b)) (hb : IsIso b) : IsIso a :=
  IsIso.of_isIso_comp_right a b

/-- Invertibility passes along an equation of morphisms. -/
theorem isIso_of_eq_of_isIso {a' : A ⟶ B} (e : a = a') (ha : IsIso a) : IsIso a' :=
  e ▸ ha

/-- The image of the second of four composable morphisms is invertible as soon as the image of
the composite and the first, third and fourth morphisms are. -/
theorem isIso_map_of_isIso_map_comp₄ {𝒟 : Type u₉} [Category.{v₉} 𝒟] (F : 𝒞 ⥤ 𝒟)
    {A₀ A₁ A₂ A₃ A₄ : 𝒞} (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄)
    (h : IsIso (F.map (a₁ ≫ a₂ ≫ a₃ ≫ a₄))) (h₁ : IsIso a₁) (h₃ : IsIso a₃) (h₄ : IsIso a₄) :
    IsIso (F.map a₂) := by
  simp only [F.map_comp] at h
  have := IsIso.of_isIso_comp_left (F.map a₁) (F.map a₂ ≫ F.map a₃ ≫ F.map a₄)
  exact IsIso.of_isIso_comp_right (F.map a₂) (F.map a₃ ≫ F.map a₄)

/-- From an equation between the images of two threefold composites, the image of the middle
factor on the left is invertible as soon as the images of the other five factors are. -/
theorem isIso_map_of_map_comp₃_eq {𝒟 : Type u₉} [Category.{v₉} 𝒟] (F : 𝒞 ⥤ 𝒟)
    {A₀ A₁ A₂ A₃ B₁ B₂ : 𝒞} (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃)
    (b₁ : A₀ ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ A₃)
    (h : F.map (a₁ ≫ a₂ ≫ a₃) = F.map (b₁ ≫ b₂ ≫ b₃))
    (hb₁ : IsIso (F.map b₁)) (hb₂ : IsIso (F.map b₂)) (hb₃ : IsIso (F.map b₃))
    (ha₁ : IsIso (F.map a₁)) (ha₃ : IsIso (F.map a₃)) : IsIso (F.map a₂) := by
  simp only [F.map_comp] at h
  have : IsIso (F.map a₁ ≫ F.map a₂ ≫ F.map a₃) := by
    rw [h]
    infer_instance
  have := IsIso.of_isIso_comp_left (F.map a₁) (F.map a₂ ≫ F.map a₃)
  exact IsIso.of_isIso_comp_right (F.map a₂) (F.map a₃)

/-- From an equation between the images of two twofold composites, the image of the second
factor on the left is invertible as soon as the images of the other three factors are. -/
theorem isIso_map_of_map_comp₂_eq {𝒟 : Type u₉} [Category.{v₉} 𝒟] (F : 𝒞 ⥤ 𝒟)
    {A₀ A₁ A₂ B₁ : 𝒞} (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (b₁ : A₀ ⟶ B₁) (b₂ : B₁ ⟶ A₂)
    (h : F.map (a₁ ≫ a₂) = F.map (b₁ ≫ b₂))
    (ha₁ : IsIso (F.map a₁)) (hb₁ : IsIso (F.map b₁)) (hb₂ : IsIso (F.map b₂)) :
    IsIso (F.map a₂) := by
  exact isIso_map_of_map_comp₃_eq F a₁ a₂ (𝟙 _) b₁ b₂ (𝟙 _) (by simpa using h) hb₁ hb₂
    (by rw [F.map_id]; infer_instance) ha₁ (by rw [F.map_id]; infer_instance)

/-- The image under two functors of a threefold composite is invertible as soon as the image of
the first factor and the second and third factors are. -/
theorem isIso_map_map_comp₃ {𝒟 : Type u₉} [Category.{v₉} 𝒟] {ℰ : Type u₈} [Category.{v₈} ℰ]
    (F : 𝒞 ⥤ 𝒟) (G : 𝒟 ⥤ ℰ) {A₀ A₁ A₂ A₃ : 𝒞} (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃)
    (h₁ : IsIso (G.map (F.map a₁))) (h₂ : IsIso a₂) (h₃ : IsIso a₃) :
    IsIso (G.map (F.map (a₁ ≫ a₂ ≫ a₃))) := by
  simp only [F.map_comp, G.map_comp]
  infer_instance

/-- The image under a functor of an isomorphism is an isomorphism. -/
theorem isIso_map_of_isIso {𝒟 : Type u₉} [Category.{v₉} 𝒟] (F : 𝒞 ⥤ 𝒟) (ha : IsIso a) :
    IsIso (F.map a) :=
  Functor.map_isIso F a

end TwoOutOfThree

/-! ### Derived stalks of the class of a morphism of complexes -/

/-- The derived stalk of the class of a morphism of complexes of `𝒪_X`-modules is invertible as
soon as the morphism is invertible on stalks in every degree. -/
theorem isIso_derivedStalkFunctor_map_Qh_map_quotient_map {X : Scheme.{u}} (x : X)
    {C D : CochainComplex X.Modules ℤ} (φ : C ⟶ D)
    (h : ∀ n, IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map (φ.f n))) :
    IsIso ((AlgebraicGeometry.derivedStalkFunctor x).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ))) := by
  let S := Stacks.ModuleSkyscraper.modulesStalkFunctor X x
  have : ∀ n, IsIso (((S.mapHomologicalComplex (ComplexShape.up ℤ)).map φ).f n) := h
  have h₁ : IsIso ((S.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) :=
    HomologicalComplex.Hom.isIso_of_components _
  have h₂ : IsIso (S.mapDerivedCategory.map (DerivedCategory.Q.map φ)) :=
    (NatIso.isIso_map_iff S.mapDerivedCategoryFactors φ).2 (by
      dsimp only [Functor.comp_map]
      infer_instance)
  exact (NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso X.Modules) S.mapDerivedCategory)
    φ).2 h₂

/-! ### The mate on components -/

section Mate

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- The component of a mate: the unit of the second adjunction, then the right adjoint of the
two-square, then the right adjoint of the image of the counit of the first adjunction. -/
theorem mateEquiv_app_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (d : D) :
    (mateEquiv adj₁ adj₂ α).app d =
      adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (α.app (R₁.obj d)) ≫
        R₂.map (H.map (adj₁.counit.app d)) := by
  simp [mateEquiv]

end Mate

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-! ### The unit of `i'^* ⊣ i'_*` on stalks at the pullback of a pushforward -/

/-- **The unit of `i'^* ⊣ i'_*` is invertible on stalks at `f^*(i_* F)`.**  At a point `i' w` the
stalk of the unit is, up to the germ map of `i'`, the unit of extension and restriction of scalars
along the surjection `𝒪_{X',i'w} ⟶ 𝒪_{Z',w}` (the mate of the stalk formula for `i'^*`), and the
stalk of `f^*(i_* F)` there is `𝒪_{X',i'w} ⊗ F_{gw}`, a restriction of an `𝒪_{Z',w}`-module. -/
theorem isIso_stalk_unit_app_pullback_pushforward (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z') (F : Z.Modules) :
    IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' (i' w)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward i).obj F)))) := by
  have := isClosedImmersion_of_isPullback sq
  have := isIso_pushStalkMap_of_isClosedImmersion i' w
  let N := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward i).obj F)
  have h : (Stacks.ModuleSkyscraper.modulesStalkFunctor X' (i' w)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app N) ≫
      (Stacks.ModuleSkyscraper.pushStalkMap i' w).app ((Scheme.Modules.pullback i').obj N) =
      (ModuleCat.extendRestrictScalarsAdj (i'.stalkMap w).hom).unit.app
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' (i' w)).obj N) ≫
        (ModuleCat.restrictScalars (i'.stalkMap w).hom).map
          ((Stacks.ModuleSkyscraper.pullbackStalkIso i' w).hom.app N) :=
    unit_mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction i')
      (ModuleCat.extendRestrictScalarsAdj (i'.stalkMap w).hom)
      (TwoSquare.mk _ _ _ _ (Stacks.ModuleSkyscraper.pullbackStalkIso i' w).hom) N
  obtain ⟨Y, ⟨e₁⟩⟩ := essImage_extendScalars_restrictScalars_stalk sq w (ptEq sq w)
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).obj F)
  let e : (ModuleCat.restrictScalars (i'.stalkMap w).hom).obj Y ≅
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X' (i' w)).obj N :=
    e₁ ≪≫ (ModuleCat.extendScalars (f.stalkMap (i' w)).hom).mapIso
        ((pushforwardStalkIso i (g w) (ptEq sq w).symm).app F).symm ≪≫
      (Stacks.ModuleSkyscraper.pullbackStalkIso f (i' w)).app
        ((Scheme.Modules.pushforward i).obj F)
  have hunit : IsIso ((ModuleCat.extendRestrictScalarsAdj (i'.stalkMap w).hom).unit.app
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' (i' w)).obj N)) :=
    (NatTrans.isIso_app_iff_of_iso _ e).1
      (isIso_unit_app_restrictScalars_of_surjective _ (i'.stalkMap_surjective w) Y)
  have hcomp : IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' (i' w)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app N) ≫
      (Stacks.ModuleSkyscraper.pushStalkMap i' w).app ((Scheme.Modules.pullback i').obj N)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Stacks.ModuleSkyscraper.pushStalkMap i' w).app ((Scheme.Modules.pullback i').obj N))

/-! ### The underived base change map on derived stalks -/

/-- **The class of the underived base change map is invertible on derived stalks at `Z'`**, at
every complex of `𝒪_Z`-modules.  It is the unit of `i'^* ⊣ i'_*` at `f^*(i_* P)`, followed by
`i'_*` of the composite of the two composition isomorphisms of degreewise pullback and of
`g^*` of the counit of `i^* ⊣ i_*`; the latter is invertible because `i_*` is fully faithful. -/
theorem isIso_derivedStalk_Qh_map_underivedBaseChangeSquare_app (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) ℤ) :
    IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map (DerivedCategory.Qh.map
      ((underivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
        f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))) := by
  rw [underivedBaseChangeSquare, mateEquiv_app_eq, Mate.twoSquare_mk_app, NatTrans.comp_app]
  have hε : IsIso ((homotopyPullbackPushforwardAdjunction i.toLRSHom.toShHom).counit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
    have hc : ∀ n, IsIso (((CategoryTheory.Adjunction.mapHomologicalComplexAdjunction
        (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom) (ComplexShape.up ℤ)).counit.app
          P).f n) := by
      have hff : IsIso (Scheme.Modules.pullbackPushforwardAdjunction i).counit :=
        @CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ _ _
          (Scheme.Modules.pullbackPushforwardAdjunction i)
          (Stacks.Tag08KS.full_schemeModulesPushforward_of_isClosedImmersion i)
          (Stacks.Tag08KS.faithful_schemeModulesPushforward_of_isClosedImmersion i)
      exact fun n => @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hff (P.X n)
    have : IsIso ((CategoryTheory.Adjunction.mapHomologicalComplexAdjunction
        (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom) (ComplexShape.up ℤ)).counit.app
          P) := HomologicalComplex.Hom.isIso_of_components _
    exact Functor.map_isIso (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) _
  have hunit := isIso_derivedStalkFunctor_map_Qh_map_quotient_map (i' w)
    ((CategoryTheory.Adjunction.mapHomologicalComplexAdjunction
      (modulePullbackPushforwardAdjunction i'.toLRSHom.toShHom) (ComplexShape.up ℤ)).unit.app
        (((modulePullback f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((modulePushforward i.toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)))
    (fun n => isIso_stalk_unit_app_pullback_pushforward sq w (P.X n))
  refine isIso_map_map_comp₃ DerivedCategory.Qh (AlgebraicGeometry.derivedStalkFunctor (i' w))
    _ _ _ hunit (isIso_map_of_isIso _ ?_) (isIso_map_of_isIso _ (isIso_map_of_isIso _ hε))
  exact IsIso.comp_isIso'
    (Iso.isIso_hom ((pullbackOnHomotopyCompIsoLeft g.toLRSHom.toShHom i'.toLRSHom.toShHom
      i.toLRSHom.toShHom f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)).app _))
    (Iso.isIso_inv ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso
      g.toLRSHom.toShHom i.toLRSHom.toShHom).app _))

/-! ### The comparison of `Lf^*` on derived stalks at a pushforward -/

/-- **The comparison `Lf^* (i_* P) ⟶ f^* (i_* P)` is invertible on derived stalks at `Z'`**, for a
K-flat complex `P` of `𝒪_Z`-modules, when `Z` and `X'` are Tor independent over `X`.  On stalks
at `i' w` it is the comparison of derived and termwise extension of scalars along
`𝒪_{X, f (i' w)} ⟶ 𝒪_{X', i' w}` at `(i_* P)_{f (i' w)}`, the restriction of the K-flat complex
`P_{g w}`. -/
theorem isIso_derivedStalk_derivedPullbackComparison_pushforward (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (w : Z') (P : CochainComplex Z.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P) :
    IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      ((derivedPullbackComparison f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((Scheme.Modules.pushforward i).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)))) := by
  obtain ⟨C, hC⟩ : ∃ C, C =
      ((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
    ⟨_, rfl⟩
  rw [← hC]
  have hcmp := AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison f (i' w) C
  dsimp only at hcmp
  have e : ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (f (i' w))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C ≅
      ((ModuleCat.restrictScalars.{u, u, u}
          ((X.presheaf.stalkCongr (Inseparable.of_eq (ptEq sq w).symm)).hom ≫
            i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
    eqToIso (congrArg ((Stacks.ModuleSkyscraper.modulesStalkFunctor X
      (f (i' w))).mapHomologicalComplex (ComplexShape.up ℤ)).obj hC) ≪≫
      (NatIso.mapHomologicalComplex (pushforwardStalkIso i (g w) (ptEq sq w).symm)
        (ComplexShape.up ℤ)).app P
  have h₁ := (NatTrans.isIso_app_iff_of_iso
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (f.stalkMap (i' w)).hom).comparison e).2
    (isIso_comparison_restrictScalars_stalk sq htor w (ptEq sq w) _
      (AlgebraicGeometry.kFlat_modulesStalkFunctor (g w) P hP))
  have h₂ := IsIso.comp_isIso'
    (Iso.isIso_hom ((AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).app
      (DerivedCategory.Q.obj C)))
    (IsIso.comp_isIso' (Iso.isIso_hom
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (f.stalkMap (i' w)).hom).functor.mapIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor X
          (f (i' w))).mapDerivedCategoryFactors.app C))) h₁)
  have h₃ : IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      (AlgebraicGeometry.pullbackComparisonOnComplex f C)) :=
    isIso_of_isIso_comp_of_isIso_right (isIso_of_eq_of_isIso hcmp h₂) (IsIso.comp_isIso'
      (Iso.isIso_hom ((Stacks.ModuleSkyscraper.modulesStalkFunctor X'
        (i' w)).mapDerivedCategoryFactors.app _))
      (Iso.isIso_hom (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (Stacks.ModuleSkyscraper.pullbackStalkIso f (i' w)).symm (ComplexShape.up ℤ)).app _))))
  have hdef : AlgebraicGeometry.pullbackComparisonOnComplex f C =
      ((derivedPullback f.toLRSHom.toShHom).mapIso
          ((DerivedCategory.quotientCompQhIso X.Modules).app C).symm).hom ≫
        (derivedPullbackComparison f.toLRSHom.toShHom).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
        (DerivedCategory.Qh.mapIso
          (((modulePullback f.toLRSHom.toShHom).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).app C)).hom ≫
        ((DerivedCategory.quotientCompQhIso X'.Modules).app _).hom :=
    rfl
  rw [hdef] at h₃
  exact isIso_map_of_isIso_map_comp₄ _ _ _ _ _ h₃ (Iso.isIso_hom _) (Iso.isIso_hom _)
    (Iso.isIso_hom _)

/-- `isIso_derivedStalk_derivedPullbackComparison_pushforward` in the spelling of the base change
map: the pushforward taken on the homotopy category of `SheafOfModules (structureSheafRing Z)`. -/
theorem isIso_derivedStalk_derivedPullbackComparison_pushforward' (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (w : Z') (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toRingedSpace P) :
    IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      ((derivedPullbackComparison f.toLRSHom.toShHom).app
        (((modulePushforward i.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))) :=
  isIso_derivedStalk_derivedPullbackComparison_pushforward sq htor w P hP

/-! ### Stacks 0E23 -/

/-- The derived stalk of the base change map at a point of `Z'` is invertible at the class of a
K-flat complex. -/
theorem isIso_derivedStalk_derivedBaseChangeMap_Qh (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (w : Z') (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toRingedSpace P) :
    IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
        f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))) := by
  have := isClosedImmersion_of_isPullback sq
  obtain ⟨W, hW⟩ : ∃ W, W = (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P := ⟨_, rfl⟩
  have hWP : Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Z.toRingedSpace W :=
    hW ▸ hP
  rw [← hW]
  have hA : IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      ((derivedPullback f.toLRSHom.toShHom).map
      ((derivedPushforwardUnit i.toLRSHom.toShHom).app W))) :=
    isIso_map_of_isIso _ (isIso_map_of_isIso _
      (Stacks.Cohomology.ClosedEmbeddingPushforward.isIso_derivedPushforwardUnit_app
        i.toLRSHom.toShHom (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i) W))
  have hC : IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      ((derivedPushforward i'.toLRSHom.toShHom).map
      ((derivedPullbackComparison g.toLRSHom.toShHom).app W))) :=
    isIso_map_of_isIso _ (isIso_map_of_isIso _
      (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_isKFlat
        g.toLRSHom.toShHom W hWP))
  have hη : IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      ((derivedPushforwardUnit i'.toLRSHom.toShHom).app
      (((modulePullback g.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj W))) :=
    isIso_map_of_isIso _
      (Stacks.Cohomology.ClosedEmbeddingPushforward.isIso_derivedPushforwardUnit_app
        i'.toLRSHom.toShHom (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i') _)
  have hα := isIso_derivedStalk_derivedPullbackComparison_pushforward' sq htor w P hP
  have hb := isIso_derivedStalk_Qh_map_underivedBaseChangeSquare_app sq w P
  rw [← hW] at hα hb
  have hG := congrArg (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
    (derivedBaseChangeMap_Qh_comparison g.toLRSHom.toShHom i'.toLRSHom.toShHom
      i.toLRSHom.toShHom f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) W)
  exact isIso_map_of_map_comp₃_eq _ _ _ _ _ _ _ hG hα hb hη hA hC

/-- **The derived stalk of the base change map at a point of `Z'` is invertible**, for a cartesian
square with `i` a closed immersion and `Z`, `X'` Tor independent over `X`. -/
theorem isIso_derivedStalk_derivedBaseChangeMap_onImage (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (w : Z') (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
        f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) K)) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlatComplex_representative Z.toRingedSpace K
  let e' := (DerivedCategory.quotientCompQhIso _).app P ≪≫ e
  have hnat := congrArg (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
    (derivedBaseChangeMap_naturality g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) e'.hom)
  exact isIso_map_of_map_comp₂_eq _ _ _ _ _ hnat
    (isIso_map_of_isIso _ (isIso_map_of_isIso _ (isIso_map_of_isIso _ (Iso.isIso_hom e'))))
    (isIso_derivedStalk_derivedBaseChangeMap_Qh sq htor w P hP)
    (isIso_map_of_isIso _ (isIso_map_of_isIso _ (isIso_map_of_isIso _ (Iso.isIso_hom e'))))

/-- **Tor-independent base change along a closed immersion.**  For a cartesian square of schemes
with `i` a closed immersion and `Z`, `X'` Tor independent over `X`, the functors `Lf^* ∘ Ri_*` and
`Ri'_* ∘ Lg^*` from `D(𝒪_Z)` to `D(𝒪_{X'})` are isomorphic, by the canonical derived base change
map of Stacks 08HY. -/
@[stacks 0E23 "Lf^* ∘ Ri_* ≅ Ri'_* ∘ Lg^* on D(𝒪_Z), by the canonical base change map"]
def derivedBaseChangeSquareAsIso (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f) :
    derivedPushforward i.toLRSHom.toShHom ⋙ derivedPullback f.toLRSHom.toShHom ≅
      derivedPullback g.toLRSHom.toShHom ⋙ derivedPushforward i'.toLRSHom.toShHom :=
  have : IsIso (derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom
      i.toLRSHom.toShHom f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)) :=
    isIso_derivedBaseChangeSquare_of_onImage sq fun w K =>
      isIso_derivedStalk_derivedBaseChangeMap_onImage sq htor w K
  asIso (derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
    f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq))

/-- The underlying morphism of `derivedBaseChangeSquareAsIso` is the derived base change map of
Stacks 08HY. -/
theorem derivedBaseChangeSquareAsIso_hom (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f) :
    (derivedBaseChangeSquareAsIso sq htor).hom =
      derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
        f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) :=
  rfl

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
