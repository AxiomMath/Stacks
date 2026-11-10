module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.StructureSheafMono
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# `c_*𝒪_X = 𝒪_Y` and `R¹c_*𝒪_X = 0` for a morphism of schemes read as algebraic spaces

Let `g : T' ⟶ T` be a morphism of the big fppf site over a scheme `S`, with underlying morphism
of schemes `φ`, and let `h_g = schemeSpaceMap g` be the morphism of represented algebraic spaces.
The condition `AlgebraicGeometry.Space.IsStructureContraction` on `h_g` is stated on the small
étale sites of the algebraic spaces; the Stacks project's statements about morphisms of schemes
(for instance Stacks 0E7L) are stated on the Zariski sites. This file compares the two, for `φ`
quasi-compact and separated:

`IsStructureContraction h_g ↔ (𝒪_T ⟶ φ_*𝒪_{T'} is an isomorphism) ∧ R¹φ_*𝒪_{T'} = 0`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_unitToPushforwardUnit_iff_bijective_app`: for a
  morphism of schemes `f`, `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism exactly when `f` is bijective on
  the sections over every open.
* `AlgebraicGeometry.Space.isIso_structureSharp_iff_bijective_appTop`: for a representable
  morphism of algebraic spaces, the structure map `f♯` of Stacks 03G8 is an isomorphism exactly
  when pullback of global functions along every cartesian projection `X ×_Y V ⟶ V` over an étale
  chart `V` of `Y` is bijective.
* `AlgebraicGeometry.Space.isIso_structureSharp_schemeSpaceMap_of_isIso` and
  `AlgebraicGeometry.Space.isIso_unitToPushforwardUnit_of_isIso_structureSharp`: the two
  directions in degree zero.
* `AlgebraicGeometry.Space.isZero_rightDerived_one_schemeSpaceMap_iff`: the comparison in
  degree one.
* `AlgebraicGeometry.Space.isStructureContraction_schemeSpaceMap_iff`: **the comparison.**

## The proof

*Degree zero.* By Stacks 03G8, part (2)
(`AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage`), `h_g♯` is,
through an isomorphism, pullback of functions along the cartesian projections
`T' ×_T V ⟶ V` over the étale charts `V` of `T`; these projections are base changes of `φ` along
the étale morphisms `V ⟶ T` of schemes. If `𝒪_T ⟶ φ_*𝒪_{T'}` is an isomorphism then so is its
flat base change (Stacks 02KH in degree zero,
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardUnit_of_isPullback`), which
is bijective on global sections. Conversely the Zariski opens `W` of `T` are étale charts, the
projection over `W` is `φ ∣_ W` up to isomorphism, and its bijectivity on global sections is the
bijectivity of `φ` on the sections over `W`.

*Degree one.* `𝒪_{h_{T'}}` is the associated module of `𝒪_{T'}`
(`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`); the higher direct images of
an associated module are the associated modules of the higher direct images
(Stacks 071N for a quasi-compact separated morphism); the associated-module functor detects the
zero object at the quasi-coherent module `R¹φ_*𝒪_{T'}`
(`AlgebraicGeometry.Space.isZero_representedAssociatedModule_iff`, with Stacks 01XJ for
quasi-coherence); and the two indexings of the right derived functors agree
(`Stacks.DerivedIndexing.rightDerivedIso`).

## Implementation notes

The degree-one comparison of Stacks 071N for a quasi-compact separated morphism is the statement
of `AlgebraicGeometry.Space.nonempty_rightDerived_modulePushforward_representedSpaceMap_iso`
(`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedHigherDirectImageComparison.lean`). It is taken
here as the explicit hypothesis `h071N`, with exactly that statement. No `stacks` attribute is
placed in this file.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a morphism of schemes `f : X ⟶ Y`, the canonical map `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism
exactly when `f` is bijective on the sections over every open of `Y`: on the sections over `U`
that map is the ring map `f.app U`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_unitToPushforwardUnit_iff_bijective_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (Scheme.Modules.unitToPushforwardUnit f) ↔
      ∀ U : Y.Opens, Function.Bijective (f.app U) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  refine forall_congr' fun U => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  rfl

/-- **The structure map of a representable morphism, chartwise.** For a representable morphism
`f : X ⟶ Y` of algebraic spaces, the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8 is an
isomorphism exactly when, for every étale chart `V` of `Y`, pullback of global functions along
the cartesian projection `X ×_Y V ⟶ V` of schemes is bijective. By Stacks 03G8, part (2), `f♯`
is that pullback through an isomorphism. -/
theorem isIso_structureSharp_iff_bijective_appTop {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    IsIso (structureSharp B S hS f) ↔ ∀ V : SmallEtale B S hS Y.1,
      Function.Bijective ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop := by
  let := isContinuous_smallBaseChange B S hS f hf
  have hc := structureSharp_comp_chartProjectionSharpDirectImage B S hS f hf
  have h1 : IsIso (structureSharp B S hS f) ↔ IsIso (cartesianProjectionSharp B S hS f hf) := by
    rw [← hc]
    exact ⟨fun _ => inferInstance, fun _ => IsIso.of_isIso_comp_right _
      (chartProjectionSharpDirectImage B S hS f hf)⟩
  rw [h1, ← isIso_iff_of_reflects_iso _ (sheafToPresheaf (SmallEtale.topology B S hS Y.1)
    RingCat.{u}), NatTrans.isIso_iff_isIso_app]
  simp only [ConcreteCategory.isIso_iff_bijective]
  exact ⟨fun h V => h (op V), fun h Z => h Z.unop⟩

section Represented

variable {B S hS} {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The morphism of schemes underlying an étale chart of a represented algebraic space is
étale. -/
theorem etale_toScheme_map_yonedaEquiv (V : SmallEtale B S hS (yoneda.obj T)) :
    Etale ((BigFppfOver.toScheme B S hS).map (yonedaEquiv V.1.hom)) := by
  have hmap : yoneda.map (yonedaEquiv V.1.hom) = V.1.hom := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map]
  have hV := V.property
  change (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf V.1.hom at hV
  rw [← hmap] at hV
  exact (presheaf_yoneda_map_iff B S hS inferInstance _).1 hV

/-- The base change of a morphism of schemes `g` to an étale chart `V` of the represented
algebraic space of its target is a cartesian square of schemes. -/
theorem isPullback_toScheme_representedChart (V : SmallEtale B S hS (yoneda.obj T)) :
    IsPullback ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_yoneda_map B S hS g).snd V.1.hom))
      ((BigFppfOver.toScheme B S hS).map
        (yonedaEquiv ((relativelyRepresentable_yoneda_map B S hS g).fst V.1.hom)))
      ((BigFppfOver.toScheme B S hS).map (yonedaEquiv V.1.hom))
      ((BigFppfOver.toScheme B S hS).map g) :=
  (isPullback_representedChart_schemes B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) V).map B.inclusion

/-- **Degree zero, from schemes to spaces.** If `φ` is quasi-compact and quasi-separated and
`𝒪_T ⟶ φ_*𝒪_{T'}` is an isomorphism, then so is the structure map of `schemeSpaceMap g`: over
an étale chart `V` of `T` the cartesian projection is a flat base change of `φ`, for which
`𝒪 ⟶ (-)_*𝒪` stays an isomorphism (Stacks 02KH in degree zero). -/
theorem isIso_structureSharp_schemeSpaceMap_of_isIso
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map g)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map g)]
    (h : IsIso (Scheme.Modules.unitToPushforwardUnit ((BigFppfOver.toScheme B S hS).map g))) :
    IsIso (structureSharp B S hS (schemeSpaceMap g)) := by
  rw [isIso_structureSharp_iff_bijective_appTop B S hS (schemeSpaceMap g)
    (relativelyRepresentable_yoneda_map B S hS g)]
  intro (V : SmallEtale B S hS (yoneda.obj T))
  have : Flat ((BigFppfOver.toScheme B S hS).map (yonedaEquiv V.1.hom)) := by
    exact (Etale.iff_flat_and_formallyUnramified.1 (etale_toScheme_map_yonedaEquiv V)).1
  have hiso :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardUnit_of_isPullback
    (isPullback_toScheme_representedChart g V).flip
  exact (Scheme.Modules.isIso_unitToPushforwardUnit_iff_bijective_app _).1 hiso ⊤

/-- **Degree zero, from spaces to schemes.** If the structure map of `schemeSpaceMap g` is an
isomorphism then so is `𝒪_T ⟶ φ_*𝒪_{T'}`: a Zariski open `W` of `T` is an étale chart, over
which the cartesian projection is `φ ∣_ W` up to isomorphism. -/
theorem isIso_unitToPushforwardUnit_of_isIso_structureSharp
    (h : IsIso (structureSharp B S hS (schemeSpaceMap g))) :
    IsIso (Scheme.Modules.unitToPushforwardUnit ((BigFppfOver.toScheme B S hS).map g)) := by
  rw [Scheme.Modules.isIso_unitToPushforwardUnit_iff_bijective_app]
  have hA := (isIso_structureSharp_iff_bijective_appTop B S hS (schemeSpaceMap g)
    (relativelyRepresentable_yoneda_map B S hS g)).1 h
  have key : ∀ W : ((BigFppfOver.toScheme B S hS).obj T).Opens,
      Function.Bijective (((BigFppfOver.toScheme B S hS).map g).app (W.ι ''ᵁ ⊤)) := by
    intro W
    let V := openChart B S hS (yoneda.obj T) (idEtaleChart B S hS T) W
    have H := isPullback_toScheme_representedChart g V
    have hc : (BigFppfOver.toScheme B S hS).map (yonedaEquiv V.1.hom) = W.ι := by
      have hy : yonedaEquiv V.1.hom = openSubHom
          ((SmallEtale.toOver B S hS (yoneda.obj T)).obj (idEtaleChart B S hS T)) W := by
        change yonedaEquiv (yoneda.map (openSubHom _ W) ≫ 𝟙 _) = _
        rw [Category.comp_id, yonedaEquiv_yoneda_map]
        rfl
      rw [hy]
      exact toScheme_map_openSubHom B S hS _ W
    rw [hc] at H
    let e := H.isoIsPullback _ _
      (isPullback_morphismRestrict ((BigFppfOver.toScheme B S hS).map g) W)
    have he := H.isoIsPullback_hom_fst _ _
      (isPullback_morphismRestrict ((BigFppfOver.toScheme B S hS).map g) W)
    have hb : Function.Bijective ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_yoneda_map B S hS g).snd V.1.hom)).appTop := hA V
    have hb2 : Function.Bijective (⇑e.hom.appTop ∘
        ⇑(((BigFppfOver.toScheme B S hS).map g ∣_ W).appTop)) := by
      rw [← he] at hb
      exact hb
    have : IsIso e.hom.appTop := by
      rw [← Scheme.Γ_map_op]
      exact (Scheme.Γ.mapIso e.op).isIso_hom
    have h3 := (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso _) _).1 hb2
    rw [morphismRestrict_appTop] at h3
    exact (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso
      (((BigFppfOver.toScheme B S hS).obj T').presheaf.map (eqToHom
        (image_morphismRestrict_preimage ((BigFppfOver.toScheme B S hS).map g) W ⊤)).op)) _).1 h3
  intro W
  have := key W
  rwa [Scheme.Opens.ι_image_top] at this

/-- **Degree one.** For `φ` quasi-compact and separated, `R¹(h_g)_*𝒪_{h_{T'}} = 0` exactly when
`R¹φ_*𝒪_{T'} = 0`. The degree-one comparison of Stacks 071N for such a morphism is the
hypothesis `h071N`, with exactly the statement of
`AlgebraicGeometry.Space.nonempty_rightDerived_modulePushforward_representedSpaceMap_iso`. -/
theorem isZero_rightDerived_one_schemeSpaceMap_iff
    (h071N : ∀ {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
      (_hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map g))
      (_hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map g))
      (F : ((BigFppfOver.toScheme B S hS).obj T').Modules) (_hF : F.IsQuasicoherent) (k : ℕ),
      have := hasInjectiveResolutions_modules B S hS (yoneda.obj T')
        (isAlgebraicSpace_yoneda B S hS T')
      have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
      Nonempty (((modulePushforward B S hS (representedSpaceMap B S hS g)).rightDerived k).obj
          ((representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')).obj F) ≅
        (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj
          (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).rightDerived k).obj
            F)))
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map g)]
    [_root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map g)] :
    (have := hasInjectiveResolutions_modules B S hS (schemeSpace T').1 (schemeSpace T').2;
      IsZero (((modulePushforward B S hS (schemeSpaceMap g)).rightDerived 1).obj
        (structureSheafModule B S hS (schemeSpace T')))) ↔
      IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf
        ((BigFppfOver.toScheme B S hS).map g)) := by
  have := hasInjectiveResolutions_modules B S hS (schemeSpace T').1 (schemeSpace T').2
  obtain ⟨e⟩ := h071N g inferInstance inferInstance
    (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf) inferInstance 1
  have e₁ := ((modulePushforward B S hS (schemeSpaceMap g)).rightDerived 1).mapIso
    (representedAssociatedModuleObjUnitIso B S hS T' (isAlgebraicSpace_yoneda B S hS T'))
  change IsZero _ ↔ _
  refine (Iso.isZero_iff (e₁.symm ≪≫ e)).trans ?_
  have : (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).rightDerived 1).obj
      (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived _ _ 1
  refine (isZero_representedAssociatedModule_iff B S hS T _).trans ?_
  let := HasDerivedCategory.standard ((BigFppfOver.toScheme B S hS).obj T').Modules
  let := HasDerivedCategory.standard ((BigFppfOver.toScheme B S hS).obj T).Modules
  exact Iso.isZero_iff ((Stacks.DerivedIndexing.rightDerivedIso
    (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)) 1).app _)

/-- **`c_*𝒪 = 𝒪` and `R¹c_*𝒪 = 0` for a morphism of schemes.** Let `g : T' ⟶ T` be a morphism of
the big fppf site whose morphism of schemes `φ` is quasi-compact and separated. Then
`schemeSpaceMap g` satisfies `AlgebraicGeometry.Space.IsStructureContraction` (on the small
étale sites) exactly when `𝒪_T ⟶ φ_*𝒪_{T'}` is an isomorphism and `R¹φ_*𝒪_{T'} = 0` (on the
Zariski sites), in the spellings of Stacks 0E7L. The degree-one comparison of Stacks 071N is the
hypothesis `h071N`, as in `AlgebraicGeometry.Space.isZero_rightDerived_one_schemeSpaceMap_iff`. -/
theorem isStructureContraction_schemeSpaceMap_iff
    (h071N : ∀ {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
      (_hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map g))
      (_hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map g))
      (F : ((BigFppfOver.toScheme B S hS).obj T').Modules) (_hF : F.IsQuasicoherent) (k : ℕ),
      have := hasInjectiveResolutions_modules B S hS (yoneda.obj T')
        (isAlgebraicSpace_yoneda B S hS T')
      have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
      Nonempty (((modulePushforward B S hS (representedSpaceMap B S hS g)).rightDerived k).obj
          ((representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')).obj F) ≅
        (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj
          (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).rightDerived k).obj
            F)))
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map g)]
    [_root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map g)] :
    IsStructureContraction B S hS (schemeSpaceMap g) ↔
      IsIso (Scheme.Modules.unitToPushforwardUnit ((BigFppfOver.toScheme B S hS).map g)) ∧
        IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf
          ((BigFppfOver.toScheme B S hS).map g)) :=
  and_congr ⟨isIso_unitToPushforwardUnit_of_isIso_structureSharp g,
      isIso_structureSharp_schemeSpaceMap_of_isIso g⟩
    (isZero_rightDerived_one_schemeSpaceMap_iff g h071N)

end Represented

end AlgebraicGeometry.Space

end
