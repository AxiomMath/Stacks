module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SectionsLiftFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyOfIsPullback
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyContractionUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesSurjective
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeChart
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyTotalScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompMate

/-!
# Lifting sections from a fibre with vanishing first cohomology

Let `X ⟶ S` be a family of curves over an affine, locally Noetherian scheme `S`, let `F` be an
invertible `𝒪_X`-module and let `P : Spec k ⟶ S` be the inclusion of a closed point with its
residue field. If `H¹(X_P, F|_{X_P}) = 0`, then every section of `F|_{X_P}` is the restriction of
a global section of `F`, and the same holds after any base change of the family through an open
of `S` containing the point.

The hypothesis that `P` is a closed immersion cannot be dropped: for `S = Spec 𝔽_p`, `X = ℙ¹_S`,
`F = 𝒪_X` and `P : Spec 𝔽_{p²} ⟶ S`, the first cohomology of the fibre vanishes but
`Γ(X, 𝒪_X) = 𝔽_p ⟶ Γ(X_P, 𝒪) = 𝔽_{p²}` is not onto.

## Main definitions

* `AlgebraicGeometry.C1590Private.SectionsPullbackSurjective`: restriction of global sections
  along a morphism of algebraic spaces is onto.
* `AlgebraicGeometry.C1590Private.SectionsLiftOfFibreH1Zero`: the statement.

## Main results

* `AlgebraicGeometry.C1590Private.surjective_globalSectionsPullbackMap_of_fibreH1Zero`: sections
  lift from the fibre to the whole family, with no shrinking of the base.
* `AlgebraicGeometry.C1590Private.surjective_globalSectionsPullbackMap_of_comp`: surjectivity of
  restriction of sections descends along a factorization `h ≫ g`.
* `AlgebraicGeometry.C1590Private.sectionsLiftOfFibreH1Zero`: the statement holds, with `U'` the
  whole base.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)

namespace AlgebraicGeometry.C1590Private

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] Space.hasInjectiveResolutions_modules

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Restriction of global sections is onto: `Γ(Y, 𝓝) ⟶ Γ(Y', g^*𝓝)`, the inverse image of
global sections along `g : Y' ⟶ Y`, is surjective. -/
def SectionsPullbackSurjective {S : Scheme.{u}} {hS : B.Contains S}
    {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (N : Space.Modules.{u, u} B S hS Y.1 Y.2) :
    Prop :=
  Function.Surjective (Space.globalSectionsPullbackMap B S hS g N).hom

/-- `AlgebraicGeometry.C1590Private.SectionsPullbackSurjective` is surjectivity of the inverse
image of global sections. -/
theorem sectionsPullbackSurjective_iff {S : Scheme.{u}} {hS : B.Contains S}
    {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (N : Space.Modules.{u, u} B S hS Y.1 Y.2) :
    SectionsPullbackSurjective B g N ↔
      Function.Surjective (Space.globalSectionsPullbackMap B S hS g N).hom :=
  Iff.rfl

/-- Sections lift from a fibre with vanishing `H¹`: let `X ⟶ S` be a family of curves over
an affine locally Noetherian scheme `S` of the site, `F` an invertible `𝒪_X`-module, and `V` a
scheme presenting the fibre of `X` at a field-valued point `P : Spec k ⟶ S` which is a closed
immersion (a closed point with its residue field). If `H¹(X_P, F|_{X_P}) = 0`, there is an open
`U' ⊆ S` through which `P` factors such that, over `U'`, every section of `F|_{X_P}` lifts to a
global section of `F|_{X_{U'}}`. The base change `X_{U'}` is quantified as any family `Y` with a
morphism `φ : Y ⟶ X` of families whose base morphism factors through `U'`, together with any
lift `q'` of the fibre presentation. -/
def SectionsLiftOfFibreH1Zero : Prop :=
  ∀ (X : CurveFamily B hZ)
    (_ : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (_ : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (F : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (_ : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O).property F)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (_ : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (_ : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (_ : Limits.IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
        (schemeSpace V).1 (schemeSpace V).2).O)).rightDerived 1).obj
        ((Space.modulePullback B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ X.total)).obj F))),
    ∃ (U' : BigFppfOver B integerBase hZ) (j : U' ⟶ X.base),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      (∃ t : P.siteObject ⟶ U', yoneda.map (t ≫ j) = yonedaEquiv.symm P.value) ∧
      ∀ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (k : Y.base ⟶ U'), k ≫ j = φ.baseMap →
        ∀ q' : yoneda.obj V ⟶ Y.total.obj, q' ≫ φ.totalMap.hom = q →
          SectionsPullbackSurjective B (ObjectProperty.homMk q' : schemeSpace V ⟶ Y.total)
            ((Space.modulePullback B integerBase hZ φ.totalMap).obj F)

section Composite

variable {B' : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B'.Contains S}
  {Y Y' Y'' : AlgebraicSpaces B' S hS}

/-- Surjectivity of the inverse image of global sections descends along a factorization: if
`Γ(Y, 𝓝) ⟶ Γ(Y'', (h ≫ g)^*𝓝)` is onto, so is `Γ(Y', g^*𝓝) ⟶ Γ(Y'', h^*g^*𝓝)`. -/
theorem surjective_globalSectionsPullbackMap_of_comp (h : Y'' ⟶ Y') (g : Y' ⟶ Y)
    (k : Y'' ⟶ Y) (hk : h ≫ g = k) (N : Space.Modules.{u, u} B' S hS Y.1 Y.2)
    (hs : Function.Surjective (Space.globalSectionsPullbackMap B' S hS k N).hom) :
    Function.Surjective (Space.globalSectionsPullbackMap B' S hS h
      ((Space.modulePullback B' S hS g).obj N)).hom := by
  subst hk
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B' S hS Y.1 Y.2).O)
  let Γ' := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B' S hS Y'.1 Y'.2).O)
  let ψ := Space.globalSectionsPushforwardIsoSite B' S hS (h ≫ g)
  let ψg := Space.globalSectionsPushforwardIsoSite B' S hS g
  let ψh := Space.globalSectionsPushforwardIsoSite B' S hS h
  let η := (Space.modulePullbackAdjunction B' S hS (h ≫ g)).unit.app N
  let ηg := (Space.modulePullbackAdjunction B' S hS g).unit.app N
  let ηh := (Space.modulePullbackAdjunction B' S hS h).unit.app
    ((Space.modulePullback B' S hS g).obj N)
  have hepi : Epi (Space.globalSectionsPullbackMap B' S hS (h ≫ g) N) :=
    (ModuleCat.epi_iff_surjective _).2 hs
  have h0 : Epi (Γ.map η) :=
    (epi_comp_iff_of_isIso (Γ.map η) (ψ.hom.app ((Space.modulePullback B' S hS (h ≫ g)).obj N))).1
      hepi
  have hunit := Space.unit_comp_map_modulePullbackCompIso_hom_app B' S hS h g N
  have h1 : Epi (Γ.map (ηg ≫ (Space.modulePushforward B' S hS g).map ηh)) := by
    let k := (Space.modulePushforwardCompIso B' S hS h g).hom.app
        ((Space.modulePullback B' S hS g ⋙ Space.modulePullback B' S hS h).obj N) ≫
      (Space.modulePushforward B' S hS (h ≫ g)).map
        ((Space.modulePullbackCompIso B' S hS h g).hom.app N)
    have : IsIso k := by dsimp only [k]; infer_instance
    have e : Γ.map (ηg ≫ (Space.modulePushforward B' S hS g).map ηh) =
        Γ.map η ≫ Γ.map (inv k) := by
      rw [← Functor.map_comp]
      congr 1
      rw [IsIso.eq_comp_inv]
      exact hunit
    rw [e]
    exact epi_comp _ _
  have h1' : Epi (Γ.map ηg ≫ Γ.map ((Space.modulePushforward B' S hS g).map ηh)) := by
    rw [← Functor.map_comp]; exact h1
  have h2 : Epi (Γ.map ((Space.modulePushforward B' S hS g).map ηh)) :=
    @epi_of_epi _ _ _ _ _ (Γ.map ηg) _ h1'
  have hnat := ψg.hom.naturality ηh
  have : Epi ((Space.modulePushforward B' S hS g ⋙ Γ).map ηh) := h2
  have h3 := epi_of_epi_fac hnat.symm
  have h4 : Function.Surjective (Γ'.map ηh).hom := fun x ↦
    (ModuleCat.epi_iff_surjective _).1 h3 x
  have hψ := (ConcreteCategory.bijective_of_isIso (ψh.hom.app
    ((Space.modulePullback B' S hS h).obj ((Space.modulePullback B' S hS g).obj N)))).2
  rw [← Space.globalSectionsPullbackMap_eq, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact hψ.comp h4

end Composite

/-- `AlgebraicGeometry.C1590Private.surjective_globalSectionsPullbackMap_of_comp`, in terms of
`AlgebraicGeometry.C1590Private.SectionsPullbackSurjective`. -/
theorem sectionsPullbackSurjective_of_comp {S : Scheme.{u}} {hS : B.Contains S}
    {Y Y' Y'' : AlgebraicSpaces B S hS} (h : Y'' ⟶ Y') (g : Y' ⟶ Y) (k : Y'' ⟶ Y)
    (hk : h ≫ g = k) (N : Space.Modules.{u, u} B S hS Y.1 Y.2)
    (hs : SectionsPullbackSurjective B k N) :
    SectionsPullbackSurjective B h ((Space.modulePullback B S hS g).obj N) :=
  surjective_globalSectionsPullbackMap_of_comp h g k hk N hs

/-- Sections lift from a fibre with vanishing `H¹`, over the whole base: let `X ⟶ S` be a family
of curves over an affine locally Noetherian scheme `S` of the site, `F` an invertible
`𝒪_X`-module, and `V` a scheme presenting the fibre of `X` at a field-valued point `P` of `S`
which is a closed immersion (a closed point with its residue field). If
`H¹(X_P, F|_{X_P}) = 0`, every section of `F|_{X_P}` is the restriction of a global section of
`F`. -/
theorem surjective_globalSectionsPullbackMap_of_fibreH1Zero (X : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (hN : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (F : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O).property F)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (hP : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (h1 : Limits.IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
        (schemeSpace V).1 (schemeSpace V).2).O)).rightDerived 1).obj
        ((Space.modulePullback B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ X.total)).obj F))) :
    Function.Surjective (Space.globalSectionsPullbackMap B integerBase hZ
      (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) F).hom := by
  let p : P.siteObject ⟶ X.base := P.value
  have hpb : IsPullback q (yoneda.map v) X.toBase.hom (yoneda.map p) :=
    yonedaEquiv_symm_eq_yoneda_map p ▸ hq
  have : Fact (Space.HasEtaleLocalProperty B integerBase hZ X.total.1
      (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :=
    ⟨Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B integerBase hZ
      X.total.property (isAlgebraicSpace_yoneda B integerBase hZ X.base) X.toBase.hom
      X.proper.2.1.1 (Space.hasEtaleLocalProperty_of_representable B integerBase hZ _ _ X.base
        (Iso.refl _) hN)⟩
  have : Space.IsCoherent B integerBase hZ X.total.1 X.total.2 F :=
    Space.isCoherent_of_isInvertible F hinv
  have sq : IsPullback (fibrePresentationMap q) (schemeSpaceMap v) X.toBase (schemeSpaceMap p) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hpb.w) hpb
  have hprop : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) :=
    X.isProper_toScheme_map_of_isPullback_schemeSpaceMap sq
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj P.siteObject) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of P.carrier)))
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj V) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).map v)
  have : CompactSpace ((BigFppfOver.toScheme B integerBase hZ).obj P.siteObject) :=
    inferInstanceAs (CompactSpace (Spec (.of P.carrier)))
  have : CompactSpace ((BigFppfOver.toScheme B integerBase hZ).obj V) :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B integerBase hZ).map v)
  have : IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj V) := {}
  have hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤ 1 :=
    (curveFamilyOfIsPullback X p (fibrePresentationMap q) (schemeSpaceMap v)
      sq).topologicalKrullDim_le_one_of_iso (K := P.carrier) rfl V (Iso.refl _)
  have : TopologicalSpace.NoetherianSpace ((BigFppfOver.toScheme B integerBase hZ).obj V) :=
    inferInstance
  have key := surjective_globalSectionsPullbackMap_of_isZero_fibre (B := B) (S := integerBase)
    (hS := hZ) X.base X.toBase p v q hpb X.proper hP hdim F h1
  dsimp only [fibrePresentationMap] at key
  exact key

/-- `AlgebraicGeometry.C1590Private.SectionsLiftOfFibreH1Zero` holds, with the open `U'` taken to
be the whole base. -/
theorem sectionsLiftOfFibreH1Zero : SectionsLiftOfFibreH1Zero B hZ := by
  intro X hA hN F hinv P V v q hq hP h1
  refine ⟨X.base, 𝟙 _, ?_, ⟨P.value, ?_⟩, ?_⟩
  · rw [CategoryTheory.Functor.map_id]; infer_instance
  · have e : P.value ≫ 𝟙 X.base = P.value := CategoryTheory.Category.comp_id _
    rw [e]
    exact (yonedaEquiv_symm_eq_yoneda_map _).symm
  · intro Y φ k _ q' hq'
    have hcomp : (ObjectProperty.homMk q' : schemeSpace V ⟶ Y.total) ≫ φ.totalMap =
        ObjectProperty.homMk q := ObjectProperty.hom_ext _ hq'
    exact sectionsPullbackSurjective_of_comp B _ _ _ hcomp F
      (surjective_globalSectionsPullbackMap_of_fibreH1Zero B hZ X hA hN F hinv P V v q hq hP h1)

end AlgebraicGeometry.C1590Private

end
