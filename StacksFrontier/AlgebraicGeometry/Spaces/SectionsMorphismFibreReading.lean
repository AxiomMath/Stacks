module

public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsMorphismToProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSectionAlongComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictToChartSchemeSectionsTransport

/-!
# The pair read at a scheme point which factors through a restriction of sections

Let `p_V : X_V ⟶ X` be a morphism of algebraic spaces, `𝒢` an `𝒪_X`-module and
`j : h_U ⟶ X_V` a scheme point with `j ≫ p_V = p`.  A global section `s` of `p_V^*𝒢` has two
readings on `U`: the pair-reading `AlgebraicGeometry.Space.pointGlobalSection` of `s` along `j`,
on `AlgebraicGeometry.Space.pointModule`, and the restriction
`AlgebraicGeometry.Space.restrictSectionAlong` of `s` to the fibre of Stacks 0D39, a global section
of `p^*𝒢` on `h_U`, read on the Zariski site of `U`.  They agree under the canonical isomorphism
of the two modules produced by `AlgebraicGeometry.Space.exists_pointReadingIso`.

So the pair of Stacks 01NE read at `j` from sections `s₀, …, sᵣ` lifting given sections
`t₀, …, tᵣ` of `𝒢|_U` is the pair `(𝒢|_U, t)`: this identifies the morphism
`φ = φ_{𝒢, s}` of the proof of Stacks 0D3A on the fibre with `φ_{𝒢|_U, t}`.

## Main results

* `AlgebraicGeometry.Space.exists_pointReadingIso`.

## Implementation notes

Composites are written with `AlgebraicGeometry.Space.representedPointHom`, the abbreviation in
which `AlgebraicGeometry.Space.restrictSectionAlong` is spelled, and the comparison of Stacks
03LU at a module with `AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`; the two other
spellings of the same terms meet inside large terms, which the elaborator compares slowly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An isomorphism with a prescribed underlying morphism, as an existential: consumers handle it
as an opaque variable. -/
theorem exists_iso_hom_eq {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) [IsIso f] :
    ∃ e : X ≅ Y, e.hom = f :=
  ⟨asIso f, rfl⟩

/-- The chart restriction of a morphism of modules, on the reading of a section over the chart. -/
theorem chartRestrictionSheafMap_app_top_topEquiv {X : AlgebraicSpaces B S hS}
    {G G' : Modules.{u, u} B S hS X.1 X.2} (κ : G ⟶ G') (A : SmallEtale B S hS X.1)
    (x : G.val.obj (op A)) :
    Scheme.Modules.Hom.app (chartRestrictionSheafMap B S hS X κ A) ⊤
        (chartRestrictionSheafTopEquiv B S hS X G A x) =
      chartRestrictionSheafTopEquiv B S hS X G' A (κ.val.app (op A) x) :=
  congrArg ULift.up (PresheafOfModules.naturality_apply κ.val _ x)

/-- The comparison of Stacks 03LU at a module, in the spelling
`AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`, is an isomorphism. -/
theorem isIso_modulePullbackCompIsoHomApp {X Y Z : AlgebraicSpaces B S hS} (k : Z ⟶ Y) (p : Y ⟶ X)
    (G : Modules.{u, u} B S hS X.1 X.2) : IsIso (modulePullbackCompIsoHomApp k p G) :=
  inferInstanceAs (IsIso ((modulePullbackCompIso B S hS k p).app G).hom)

/-- The chart restriction of an isomorphism of modules, followed by the identification of chart
restrictions with restrictions to the chart scheme, on the reading of a global section. -/
theorem chartRestrictionSheafMapIso_trans_hom_app_topEquiv {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (κ : M ≅ N) (A : SmallEtale B S hS Z.1)
    (y : M.val.obj (op A)) :
    Scheme.Modules.Hom.app (chartRestrictionSheafMapIso B S hS κ A ≪≫
        (restrictToChartSchemeIsoChartRestrictionSheaf B S hS Z N A).symm).hom ⊤
        (chartRestrictionSheafTopEquiv B S hS Z M A y) =
      (restrictToChartSchemeTopSectionsAddEquiv B S hS Z N A).symm (κ.hom.val.app (op A) y) :=
  congrArg
    (Scheme.Modules.Hom.app (restrictToChartSchemeIsoChartRestrictionSheaf B S hS Z N A).inv ⊤)
    (chartRestrictionSheafMap_app_top_topEquiv κ.hom A y)

/-- `AlgebraicGeometry.Space.pointGlobalSection`, unfolded. -/
theorem pointGlobalSection_eq_topEquiv {XV : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS XV.1 XV.2) (U : BigFppfOver B S hS)
    (k : representedAlgebraicSpace B S hS U ⟶ XV)
    (s : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS XV.1 XV.2).O)).obj M) :
    pointGlobalSection B S hS M U k s =
      chartRestrictionSheafTopEquiv B S hS (representedAlgebraicSpace B S hS U)
        ((modulePullback B S hS k).obj M) (idEtaleChart B S hS U)
        (((globalSectionsPullbackMap B S hS k M).hom s).1 (op (idEtaleChart B S hS U))) :=
  rfl

/-- `AlgebraicGeometry.Space.chartRestrictionSheafMapIso_trans_hom_app_topEquiv` on the
pair-reading of a section along a scheme point. -/
theorem chartRestrictionSheafMapIso_trans_hom_app_pointGlobalSection {XV : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS XV.1 XV.2) (U : BigFppfOver B S hS)
    (k : representedAlgebraicSpace B S hS U ⟶ XV)
    {N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS U).2}
    (κ : (modulePullback B S hS k).obj M ≅ N)
    (s : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS XV.1 XV.2).O)).obj M) :
    Scheme.Modules.Hom.app (chartRestrictionSheafMapIso B S hS κ (idEtaleChart B S hS U) ≪≫
        (restrictToChartSchemeIsoChartRestrictionSheaf B S hS (representedAlgebraicSpace B S hS U)
          N (idEtaleChart B S hS U)).symm).hom ⊤ (pointGlobalSection B S hS M U k s) =
      (restrictToChartSchemeTopSectionsAddEquiv B S hS (representedAlgebraicSpace B S hS U) N
        (idEtaleChart B S hS U)).symm
        (κ.hom.val.app (op (idEtaleChart B S hS U))
          (((globalSectionsPullbackMap B S hS k M).hom s).1 (op (idEtaleChart B S hS U)))) := by
  rw [pointGlobalSection_eq_topEquiv]
  exact chartRestrictionSheafMapIso_trans_hom_app_topEquiv κ (idEtaleChart B S hS U) _

/-- An isomorphism of modules gives an isomorphism of chart restrictions, compatible with the
readings of global sections. -/
private theorem exists_chartRestrictionIso_of_isIso {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (A : SmallEtale B S hS Z.1) (f : M ⟶ N) [IsIso f] :
    ∃ β : chartRestrictionSheaf B S hS Z M A ≅ restrictToChartSchemeModules B S hS Z.1 Z.2 N A,
      ∀ y, Scheme.Modules.Hom.app β.hom ⊤ (chartRestrictionSheafTopEquiv B S hS Z M A y) =
        (restrictToChartSchemeTopSectionsAddEquiv B S hS Z N A).symm (f.val.app (op A) y) := by
  obtain ⟨e, he⟩ := exists_iso_hom_eq f
  refine ⟨chartRestrictionSheafMapIso B S hS e A ≪≫
    (restrictToChartSchemeIsoChartRestrictionSheaf B S hS Z N A).symm, fun y ↦ ?_⟩
  rw [← he]
  exact chartRestrictionSheafMapIso_trans_hom_app_topEquiv e A y

/-- **The two readings of `𝒢` at a scheme point `j` of `X_V` agree.**  The reading of `p_V^*𝒢`
along `j` (`AlgebraicGeometry.Space.pointModule`) is the restriction of `(j ≫ p_V)^*𝒢` to the
Zariski site of `U`, through the comparison `j^* p_V^* 𝒢 ≅ (j ≫ p_V)^* 𝒢` of Stacks 03LU, and on
global sections this identification carries the pair-reading of a section `s` to the reading of
its image `(j ≫ p_V)^* s`.  By `AlgebraicGeometry.Space.restrictSectionAlong_eq` that image is the
restriction of `s` to the fibre, up to the identification along `j ≫ p_V = p`. -/
theorem exists_pointReadingIso {X XV : AlgebraicSpaces B S hS} (pV : XV ⟶ X)
    (U : BigFppfOver B S hS) (jV : yoneda.obj U ⟶ XV.1) (G : Modules.{u, u} B S hS X.1 X.2) :
    ∃ β : chartRestrictionSheaf B S hS (representedAlgebraicSpace B S hS U)
          ((modulePullback B S hS (representedPointHom U jV)).obj
            ((modulePullback B S hS pV).obj G)) (idEtaleChart B S hS U) ≅
        restrictToChartSchemeModules B S hS (representedAlgebraicSpace B S hS U).1
          (representedAlgebraicSpace B S hS U).2
          ((modulePullback B S hS (representedPointHom U jV ≫ pV)).obj G)
          (idEtaleChart B S hS U),
      ∀ y, Scheme.Modules.Hom.app β.hom ⊤
            (chartRestrictionSheafTopEquiv B S hS (representedAlgebraicSpace B S hS U)
              ((modulePullback B S hS (representedPointHom U jV)).obj
                ((modulePullback B S hS pV).obj G)) (idEtaleChart B S hS U) y) =
          (restrictToChartSchemeTopSectionsAddEquiv B S hS (representedAlgebraicSpace B S hS U)
            ((modulePullback B S hS (representedPointHom U jV ≫ pV)).obj G)
            (idEtaleChart B S hS U)).symm
            ((modulePullbackCompIsoHomApp (representedPointHom U jV) pV G).val.app
              (op (idEtaleChart B S hS U)) y) := by
  have := isIso_modulePullbackCompIsoHomApp (representedPointHom U jV) pV G
  exact exists_chartRestrictionIso_of_isIso _
    (modulePullbackCompIsoHomApp (representedPointHom U jV) pV G)

/-- `Γ` of a morphism followed by an identification of sections along an equality of morphisms,
on a section, evaluated at an étale chart. -/
theorem spaceModuleSectionsPullbackCongr_hom_map_val {Z Z' : AlgebraicSpaces B S hS}
    {g g' : Z' ⟶ Z} (e : g = g') (G : Modules.{u, u} B S hS Z.1 Z.2)
    {N : Modules.{u, u} B S hS Z'.1 Z'.2} (a : N ⟶ (modulePullback B S hS g).obj G)
    (x : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).obj N)
    (A : SmallEtale B S hS Z'.1) :
    ((spaceModuleSectionsPullbackCongr e G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map a).hom x)).1 (op A) =
      (eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G) e)).val.app (op A)
        (a.val.app (op A) (x.1 (op A))) := by
  subst e
  rfl

/-- **The restriction of a section to the fibre, on the identity chart**: the comparison of
Stacks 03LU applied to the value of the inverse image of the section, followed by the
identification along `j ≫ p_V = p`. -/
theorem restrictSectionAlong_val_idEtaleChart {X XV : AlgebraicSpaces B S hS} (pV : XV ⟶ X)
    (U : BigFppfOver B S hS) (jV : yoneda.obj U ⟶ XV.1) (p : yoneda.obj U ⟶ X.1)
    (h : jV ≫ pV.hom = p) (G : Modules.{u, u} B S hS X.1 X.2)
    (s : spaceModuleSections XV ((modulePullback B S hS pV).obj G)) :
    (restrictSectionAlong pV U jV p h G s).1 (op (idEtaleChart B S hS U)) =
      (eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G)
        (ObjectProperty.hom_ext _ h :
          representedPointHom U jV ≫ pV = ObjectProperty.homMk p))).val.app
        (op (idEtaleChart B S hS U))
        ((modulePullbackCompIsoHomApp (representedPointHom U jV) pV G).val.app
          (op (idEtaleChart B S hS U))
          (((globalSectionsPullbackMap B S hS (representedPointHom U jV)
            ((modulePullback B S hS pV).obj G)).hom s).1 (op (idEtaleChart B S hS U)))) := by
  rw [restrictSectionAlong_eq]
  exact spaceModuleSectionsPullbackCongr_hom_map_val _ G _ _ _

/-- The sections map of a composite of isomorphisms of modules on a scheme. -/
theorem scheme_modules_iso_trans_hom_app {Z : Scheme.{u}} {P Q R : Z.Modules} (e : P ≅ Q)
    (e' : Q ≅ R) (U : Z.Opens) (x : Γ(P, U)) :
    Scheme.Modules.Hom.app (e ≪≫ e').hom U x =
      Scheme.Modules.Hom.app e'.hom U (Scheme.Modules.Hom.app e.hom U x) :=
  rfl

/-- An isomorphism of modules on a scheme undoes its inverse on sections. -/
theorem scheme_modules_iso_hom_app_inv_app {Z : Scheme.{u}} {P Q : Z.Modules} (e : P ≅ Q)
    (U : Z.Opens) (y : Γ(Q, U)) :
    Scheme.Modules.Hom.app e.hom U (Scheme.Modules.Hom.app e.inv U y) = y := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
  rfl

/-- **Passing from the chart reading to the reading at a scheme point.**  An isomorphism out of
the restriction of `k^*M` to the identity chart of `h_U`, computed on chart readings of sections,
is an isomorphism out of `AlgebraicGeometry.Space.pointModule` computed on pair-readings.  Stated
for variables, so that the two spellings of the scheme of `U` are compared on small terms. -/
theorem exists_pointModule_iso_of_chartRestriction {XV : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS XV.1 XV.2) (U : BigFppfOver B S hS)
    (k : representedAlgebraicSpace B S hS U ⟶ XV)
    {N : ((BigFppfOver.toScheme B S hS).obj U).Modules}
    (Ψ : chartRestrictionSheaf B S hS (representedAlgebraicSpace B S hS U)
      ((modulePullback B S hS k).obj M) (idEtaleChart B S hS U) ≅ N)
    {ι : Type*} (s : ι → spaceModuleSections XV M) (t : ι → Γ(N, ⊤))
    (h : ∀ i, Scheme.Modules.Hom.app Ψ.hom ⊤
      (chartRestrictionSheafTopEquiv B S hS (representedAlgebraicSpace B S hS U)
        ((modulePullback B S hS k).obj M) (idEtaleChart B S hS U)
        (((globalSectionsPullbackMap B S hS k M).hom (s i)).1
          (op (idEtaleChart B S hS U)))) = t i) :
    ∃ Φ : pointModule B S hS M U k ≅ N,
      ∀ i, Scheme.Modules.Hom.app Φ.hom ⊤ (pointGlobalSection B S hS M U k (s i)) = t i :=
  ⟨Ψ, h⟩

/-- **The pair read at a scheme point `j` of `X_V`, from sections lifting given sections on the
fibre.**  Let `E` identify the restriction of `p^*𝒢` to the Zariski site of `U` with a module `N`
on `U`, and let the sections `s_i` of `p_V^*𝒢` restrict on the fibre to the sections of `p^*𝒢`
corresponding under `E` to sections `t_i` of `N`.  Then the reading of `p_V^*𝒢` along `j` is
identified with `N` by an isomorphism carrying the pair-readings of the `s_i` to the `t_i`. -/
theorem exists_pointModule_iso_of_restrictSectionAlong {X XV : AlgebraicSpaces B S hS}
    (pV : XV ⟶ X) (U : BigFppfOver B S hS) (jV : yoneda.obj U ⟶ XV.1) (p : yoneda.obj U ⟶ X.1)
    (h : jV ≫ pV.hom = p) (G : Modules.{u, u} B S hS X.1 X.2)
    {N : ((BigFppfOver.toScheme B S hS).obj U).Modules}
    (E : restrictToChartSchemeModules B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS U).2
      ((modulePullback B S hS (ObjectProperty.homMk p :
        representedAlgebraicSpace B S hS U ⟶ X)).obj G) (idEtaleChart B S hS U) ≅ N)
    {ι : Type*} (s : ι → spaceModuleSections XV ((modulePullback B S hS pV).obj G))
    (t : ι → Γ(N, ⊤))
    (hst : ∀ i, (restrictSectionAlong pV U jV p h G (s i)).1 (op (idEtaleChart B S hS U)) =
      restrictToChartSchemeTopSectionsAddEquiv B S hS (representedAlgebraicSpace B S hS U)
        ((modulePullback B S hS (ObjectProperty.homMk p :
          representedAlgebraicSpace B S hS U ⟶ X)).obj G) (idEtaleChart B S hS U)
        (Scheme.Modules.Hom.app E.inv ⊤ (t i))) :
    ∃ Φ : pointModule B S hS ((modulePullback B S hS pV).obj G) U (representedPointHom U jV) ≅ N,
      ∀ i, Scheme.Modules.Hom.app Φ.hom ⊤
        (pointGlobalSection B S hS ((modulePullback B S hS pV).obj G) U
          (representedPointHom U jV) (s i)) = t i := by
  have := isIso_modulePullbackCompIsoHomApp (representedPointHom U jV) pV G
  obtain ⟨β, hβ⟩ := exists_chartRestrictionIso_of_isIso (idEtaleChart B S hS U)
    (modulePullbackCompIsoHomApp (representedPointHom U jV) pV G ≫
      eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G)
        (ObjectProperty.hom_ext _ h :
          representedPointHom U jV ≫ pV = ObjectProperty.homMk p)))
  refine exists_pointModule_iso_of_chartRestriction _ U (representedPointHom U jV) (β ≪≫ E) s t
    (fun i ↦ ?_)
  refine (scheme_modules_iso_trans_hom_app _ _ _ _).trans ?_
  refine (congrArg (Scheme.Modules.Hom.app E.hom ⊤) (hβ _)).trans ?_
  have h₂ := (modules_comp_val_app_apply_eq B S hS _ _ _ _ _ rfl).trans
    (restrictSectionAlong_val_idEtaleChart pV U jV p h G (s i)).symm
  rw [h₂, hst]
  refine (congrArg (Scheme.Modules.Hom.app E.hom ⊤) (AddEquiv.symm_apply_apply _ _)).trans ?_
  exact scheme_modules_iso_hom_app_inv_app _ _ _


section Generic

variable {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
  (hinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property M)
  {r : ℕ} (s : Fin (r + 1) → spaceModuleSections X M)

/-- The read sections have no common zero at a scheme point whose reading is identified with an
invertible module carrying generating sections. -/
theorem isGeneratedReading_of_iso (U : BigFppfOver B S hS)
    (k : representedAlgebraicSpace B S hS U ⟶ X)
    {N : ((BigFppfOver.toScheme B S hS).obj U).Modules} [Stacks.Ample.IsInvertibleModule _ N]
    (Φ : pointModule B S hS M U k ≅ N) (t : Fin (r + 1) → Γ(N, ⊤))
    (ht : Stacks.ProjectiveFromSections.GeneratesStalks t)
    (hΦ : ∀ i, Scheme.Modules.Hom.app Φ.hom ⊤ (pointGlobalSection B S hS M U k (s i)) = t i) :
    IsGeneratedReading B S hS M s U k := fun z ↦ by
  obtain ⟨i, hi⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks t ht z
  refine ⟨i, ?_⟩
  rw [← nonvanishingLocus_hom_app_iso Φ, hΦ i]
  exact hi

/-- The pair read at a scheme point whose reading is identified with an invertible module carrying
given sections is that pair. -/
theorem isomorphic_pointGeneratingTuple_of_iso (U : BigFppfOver B S hS)
    (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op U))
    {N : ((BigFppfOver.toScheme B S hS).obj U).Modules} [hN : Stacks.Ample.IsInvertibleModule _ N]
    (Φ : pointModule B S hS M U (sectionPoint B S hS x.1) ≅ N) (t : Fin (r + 1) → Γ(N, ⊤))
    (ht : Stacks.ProjectiveFromSections.GeneratesStalks t)
    (hΦ : ∀ i, Scheme.Modules.Hom.app Φ.hom ⊤
      (pointGlobalSection B S hS M U (sectionPoint B S hS x.1) (s i)) = t i) :
    Stacks.ProjectiveSpaceModuli.Isomorphic (pointGeneratingTuple B S hS M hinv s U x)
      ⟨N, hN, t, ht⟩ := by
  refine ⟨pointBundleIso B S hS M U _ ≪≫ Φ, fun i ↦ ?_⟩
  change Scheme.Modules.Hom.app (pointBundleIso B S hS M U _ ≪≫ Φ).hom ⊤
    (pointBundleSection B S hS M U (sectionPoint B S hS x.1) (s i)) = t i
  rw [pointBundleSection_def, scheme_modules_iso_trans_hom_app, ← hΦ i]
  exact congrArg (Scheme.Modules.Hom.app Φ.hom ⊤)
    (scheme_modules_iso_hom_app_inv_app (pointBundleIso B S hS M U _) ⊤ _)

end Generic

/-- **The fibre point lies in the generation locus, and `φ` there is `φ_{(N, t)}`.**  Let the
sections `s_i` of `p_V^*𝒢` restrict on the fibre `x₀ : h_U ⟶ X_V` to sections corresponding
under `E` to generating sections `t_i` of an invertible module `N` on `U`.  Then the read sections
have no common zero at `x₀`, and the component of `φ` at `x₀` is the morphism `φ_{(N, t)}` of
Stacks 01ND. -/
theorem exists_mem_sectionsGenerationLocus_pointClassifyingMap_eq {X XV : AlgebraicSpaces B S hS}
    (pV : XV ⟶ X) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    (G : Modules.{u, u} B S hS X.1 X.2)
    (hinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS XV.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS XV.1 XV.2).O)).property
        ((modulePullback B S hS pV).obj G))
    {r : ℕ} (s : Fin (r + 1) → spaceModuleSections XV ((modulePullback B S hS pV).obj G))
    (x₀ : XV.1.obj (op U)) (h : yonedaEquiv.symm x₀ ≫ pV.hom = p)
    {N : ((BigFppfOver.toScheme B S hS).obj U).Modules} [hN : Stacks.Ample.IsInvertibleModule _ N]
    (E : restrictToChartSchemeModules B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS U).2
      ((modulePullback B S hS (ObjectProperty.homMk p :
        representedAlgebraicSpace B S hS U ⟶ X)).obj G) (idEtaleChart B S hS U) ≅ N)
    (t : Fin (r + 1) → Γ(N, ⊤)) (ht : Stacks.ProjectiveFromSections.GeneratesStalks t)
    (hst : ∀ i, (restrictSectionAlong pV U (yonedaEquiv.symm x₀) p h G (s i)).1
        (op (idEtaleChart B S hS U)) =
      restrictToChartSchemeTopSectionsAddEquiv B S hS (representedAlgebraicSpace B S hS U)
        ((modulePullback B S hS (ObjectProperty.homMk p :
          representedAlgebraicSpace B S hS U ⟶ X)).obj G) (idEtaleChart B S hS U)
        (Scheme.Modules.Hom.app E.inv ⊤ (t i))) :
    ∃ hx : x₀ ∈ (sectionsGenerationLocus B S hS ((modulePullback B S hS pV).obj G) hinv s).obj
        (op U),
      pointClassifyingMap B S hS ((modulePullback B S hS pV).obj G) hinv s U ⟨x₀, hx⟩ =
        Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse t ht := by
  obtain ⟨Φ, hΦ⟩ := exists_pointModule_iso_of_restrictSectionAlong pV U (yonedaEquiv.symm x₀) p h
    G E s t hst
  have hx := isGeneratedReading_of_iso _ s U _ Φ t ht hΦ
  exact ⟨hx, pointClassifyingMap_eq_toProjectiveSpaceAtUniverse B S hS _ hinv s U ⟨x₀, hx⟩ N t ht
    (isomorphic_pointGeneratingTuple_of_iso _ hinv s U ⟨x₀, hx⟩ Φ t ht hΦ)⟩

end AlgebraicGeometry.Space

end
