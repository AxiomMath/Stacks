module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelRepresented
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelNearFibre
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.StructureSheafSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubsetsOfStructureMapIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# `κ = H⁰` on the fibres gives `f_*𝒪_X = 𝒪_S` universally

Let `f : X ⟶ S` be a family of curves such that `k = H⁰(X_k, 𝒪_{X_k})` for every morphism
`Spec k ⟶ S` from the spectrum of a field. Then `f_*𝒪_X = 𝒪_S`, and this holds after any base
change: this is part (a) of Stacks 0E6B for families of curves, the input `hpush` of
`AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily_of`.

Étale locally on `S` the family is a morphism of schemes `q : Z ⟶ U` (Stacks 0E6F, the hypothesis
`h0E6F`), all of whose fibres have `H⁰` the residue field. For such a morphism of schemes part (a)
of Stacks 0E62 gives `𝒪 = q'_*𝒪` for every base change `q'` of `q`. Read on the small étale site
this is the invertibility of the structure map of Stacks 03G8 of `q'`
(`AlgebraicGeometry.C1590Private.isIso_structureSharp_schemeSpaceMap`), and that invertibility is
étale local on the target
(`AlgebraicGeometry.C1590Private.isIso_structureSharp_of_isPullback_etale`).
So it holds for the base change of `f` to every scheme, then, over an atlas, for the base change
to every algebraic space; an invertible structure map is bijective on global functions.

## Main results

* `AlgebraicGeometry.C1590Private.isIso_structureSharp_fiberProduct_schemeSpace`: the structure
  map of the base change of the family to a scheme is invertible.
* `AlgebraicGeometry.C1590Private.hasUniversallyBijectiveGlobalFunctions_of`: the input `hpush`,
  from Stacks 0E6F.

## References

* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`κ = H⁰` on the fibres is inherited by base changes.** -/
theorem hasBijectiveGlobalFunctionsOnFieldFibres_of_hom {F G : CurveFamily B hZ} (φ : F ⟶ G)
    (hG : CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ G) :
    CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ F := by
  rw [hasBijectiveGlobalFunctionsOnFieldFibres_iff_eq_univ] at hG ⊢
  rw [globalFunctionsFieldLocus_eq_preimage φ, hG, Set.preimage_univ]

/-- **The fibres of a scheme chart have `H⁰` the residue field.** If the family `X` has
`κ = H⁰` on its fibres over fields, then over a chart on which it is a morphism of schemes
`q : Z ⟶ U`, every scheme-theoretic fibre `Z_u` has `κ(u) = H⁰(Z_u, 𝒪_{Z_u})`. -/
theorem bijective_fiber_appTop_of_isPullback (X : CurveFamily B hZ)
    {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ X.base} {p : schemeSpace Z ⟶ X.total}
    {q : Z ⟶ U} (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))
    (hX : CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X)
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U) :
    Function.Bijective (((Scheme.ΓSpecIso
      (((BigFppfOver.toScheme B integerBase hZ).obj U).residueField u)).inv ≫
        (((BigFppfOver.toScheme B integerBase hZ).map q).fiberToSpecResidueField u).appTop) :) := by
  have hXU := hasBijectiveGlobalFunctionsOnFieldFibres_of_hom
    (curveFamilyOfIsPullbackHom X φ p (schemeSpaceMap q) sq) hX
  rw [hasBijectiveGlobalFunctionsOnFieldFibres_iff_eq_univ] at hXU
  exact ((mem_globalFunctionsFieldLocus_curveFamilyOfIsPullback_iff_bijective X sq u).1
    (hXU ▸ Set.mem_univ u)).comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv)

/-- **The structure map of a base change of a scheme chart is invertible.** If `X` has
`κ = H⁰` on its fibres over fields and `q : Z ⟶ U` is a scheme chart of `X`, then for every
`g : V ⟶ U` the structure map of Stacks 03G8 of the base change `Z ×_U V ⟶ V` is an isomorphism,
by part (a) of Stacks 0E62. -/
theorem isIso_structureSharp_schemeSpaceMap_pullback_snd (X : CurveFamily B hZ)
    {U Z V : BigFppfOver B integerBase hZ} {φ : U ⟶ X.base} {p : schemeSpace Z ⟶ X.total}
    {q : Z ⟶ U} (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))
    (hX : CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X) (g : V ⟶ U) :
    IsIso (Space.structureSharp B integerBase hZ (schemeSpaceMap (pullback.snd q g))) := by
  let F := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan F :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  have hZ' := (IsPullback.of_hasPullback q g).map F
  have := CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap X sq
  have := CurveFamily.flat_toScheme_map_of_isPullback X sq
  have hs :=
    Stacks.AlgebraicGeometry.ProperFlatStructureSheafSplitting.properFlat_structureSheaf_splitting
      (F.map q) (finitePresentation_toScheme_map_of_isPullback X sq)
      (bijective_fiber_appTop_of_isPullback X sq hX)
  have hc := hs.1.2 (F.map g) (F.map (pullback.snd q g)) (F.map (pullback.fst q g)) hZ'
  have : QuasiCompact (F.map (pullback.snd q g)) :=
    MorphismProperty.of_isPullback hZ' inferInstance
  have : QuasiSeparated (F.map (pullback.snd q g)) :=
    MorphismProperty.of_isPullback hZ' inferInstance
  exact isIso_structureSharp_schemeSpaceMap B integerBase hZ _
    ((Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
      _).1 hc)

/-- A pullback square over `f` and `c ≫ g` factors through the pullback of `f` and `g` as a
pullback square over `c`. -/
private theorem exists_isPullback_of_isPullback_comp {C : Type*} [Category C]
    {X S Y R P T : C} {f : X ⟶ S} {g : Y ⟶ S} {fst : R ⟶ X} {snd : R ⟶ Y}
    (hR : IsPullback fst snd f g) (c : T ⟶ Y) {a : P ⟶ X} {b : P ⟶ T}
    (s : IsPullback a b f (c ≫ g)) : ∃ j : P ⟶ R, IsPullback j b snd c :=
  ⟨hR.lift a (b ≫ c) (by rw [s.w, Category.assoc]),
    IsPullback.of_right (by rw [hR.lift_fst]; exact s) (hR.lift_snd _ _ _) hR⟩

/-- **The structure map of the base change of the family to a scheme is invertible.** If `X` has
`κ = H⁰` on its fibres over fields, then for every morphism of schemes `m : T ⟶ S` of the site the
structure map `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` of Stacks 03G8 of the base change `f_T : X_T ⟶ T` is an
isomorphism, given the étale local scheme charts of Stacks 0E6F. Over the base change `T'` of each
chart, `f_T` is the base change `q'` of the morphism of schemes `q : Z ⟶ U` of the chart, for which
`𝒪 = q'_*𝒪` by part (a) of Stacks 0E62; the base changes of the charts cover `T`. -/
theorem isIso_structureSharp_fiberProduct_schemeSpace (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (X : CurveFamily B hZ) (hX : CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X)
    {T : BigFppfOver B integerBase hZ} (m : T ⟶ X.base) :
    IsIso (Space.structureSharp B integerBase hZ
      (ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap m).hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap m) ⟶
          schemeSpace T)) := by
  let F := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan F :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  choose U Z φ q p hφ hu sq using fun t : F.obj T => h0E6F X (F.map m t)
  have hT := fun t => IsPullback.of_hasPullback m (φ t)
  have hZ' := fun t => IsPullback.of_hasPullback (q t) (pullback.snd m (φ t))
  have hR := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap m)
  have hbig : ∀ t, IsPullback (schemeSpaceMap (pullback.fst (q t) (pullback.snd m (φ t))) ≫ p t)
      (schemeSpaceMap (pullback.snd (q t) (pullback.snd m (φ t)))) X.toBase
      (schemeSpaceMap (pullback.fst m (φ t)) ≫ schemeSpaceMap m) := fun t => by
    have h := (isPullback_schemeSpaceMap (hZ' t)).paste_horiz (sq t)
    rwa [← schemeSpaceMap_comp, ← (hT t).w, schemeSpaceMap_comp] at h
  choose jA hsq using fun t => exists_isPullback_of_isPullback_comp hR
    (schemeSpaceMap (pullback.fst m (φ t))) (hbig t)
  have hπ : ∀ t, Etale (F.map (pullback.fst m (φ t))) := fun t =>
    MorphismProperty.of_isPullback ((hT t).map F).flip (hφ t)
  have hcov := isEtaleCovering_yoneda_map B integerBase hZ (fun t => pullback.fst m (φ t)) hπ
    (fun w => by
      obtain ⟨u, hu'⟩ := hu w
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback w u hu'.symm
      refine ⟨w, ((hT w).map F).isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz])
  exact isIso_structureSharp_of_isPullback_etale B integerBase hZ _
    (W := fun t => schemeSpace (pullback m (φ t))) (fun t => schemeSpaceMap (pullback.fst m (φ t)))
    jA (fun t => schemeSpaceMap (pullback.snd (q t) (pullback.snd m (φ t)))) hcov hsq
    (fun t => isIso_structureSharp_schemeSpaceMap_pullback_snd X (sq t) hX _)

/-- **Part (a) of Stacks 0E6B for families of curves**, given the étale local scheme charts of
Stacks 0E6F: if `k = H⁰(X_k, 𝒪_{X_k})` at every field-valued point of the base, then
`f_*𝒪_X = 𝒪_S` universally. This is the input `hpush` of
`AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily_of`.

For an algebraic space `Y ⟶ S` with atlas `T ⟶ Y`, the base change of `X ×_S Y ⟶ Y` along the
atlas is the base change `X_T ⟶ T` of the family to the scheme `T`, whose structure map is
invertible (`AlgebraicGeometry.C1590Private.isIso_structureSharp_fiberProduct_schemeSpace`); this
is étale local on `Y`, and an invertible structure map is bijective on global functions. -/
theorem hasUniversallyBijectiveGlobalFunctions_of (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (X : CurveFamily B hZ) (hX : CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X) :
    HasUniversallyBijectiveGlobalFunctions B hZ X := by
  intro Y g
  obtain ⟨T, a, hsurj, het⟩ := Y.property.exists_atlas
  let aY : schemeSpace T ⟶ Y := ObjectProperty.homMk a
  let m : T ⟶ X.base := Yoneda.fullyFaithful.preimage (a ≫ g.hom)
  have hm : schemeSpaceMap m = aY ≫ g :=
    ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)
  have hcov : Space.IsEtaleCovering B integerBase hZ (fun _ : PUnit.{u + 1} => (schemeSpace T).1)
      (fun _ => aY.hom) :=
    Space.isEtaleCovering_atlas B integerBase hZ Y.2 hsurj het
  have hR := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase g
  have hT := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap m)
  let fT : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap m) ⟶
      schemeSpace T := ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap m).hom)
  let f : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase g ⟶ Y :=
    ObjectProperty.homMk (pullback.snd X.toBase.hom g.hom)
  obtain ⟨jA, hsq⟩ := exists_isPullback_of_isPullback_comp hR aY (by rw [← hm]; exact hT)
  have hiso : IsIso (Space.structureSharp B integerBase hZ f) :=
    isIso_structureSharp_of_isPullback_etale B integerBase hZ f (fun _ : PUnit.{u + 1} => aY)
      (fun _ => jA) (fun _ => fT) hcov (fun _ => hsq)
      (fun _ => isIso_structureSharp_fiberProduct_schemeSpace h0E6F X hX m)
  rw [← Space.forgetCommRingSheaf_map_fSharp] at hiso
  have : IsIso (Space.smallEtaleRingedToposHom B integerBase hZ f).fSharp :=
    @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
      (Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf.{u}
        (Space.SmallEtale.topology B integerBase hZ Y.1)) _ _ _ hiso
  exact Space.bijective_globalFunctionsMap_of_isIso_fSharp f

end AlgebraicGeometry.C1590Private

end
