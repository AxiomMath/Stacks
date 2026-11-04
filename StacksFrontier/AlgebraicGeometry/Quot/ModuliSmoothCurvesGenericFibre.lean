module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothingGenericFibre
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStableOverField

/-!
# The generic fibre of a smoothing of a curve of genus `g ≥ 2` lies in `𝓜_g`

Let `g : Y ⟶ Spec k⟦t⟧` be a proper flat morphism of finite presentation with smooth generic
fibre `Y_η ⟶ Spec κ(η)`, whose special fibre `X` is a geometrically connected and geometrically
reduced proper scheme of dimension at most one over `k` with `H⁰(X, 𝒪_X) = k` and genus at least
two; such a `g` is the smoothing of Stacks 0E7Y of a stable curve. The family of curves of the
generic fibre then lies in `𝓜_g` (Stacks 0E83) for `g` the genus of `X`:

* it is smooth, and of relative dimension one: the generic fibre is irreducible (it is smooth
  with `H⁰ = κ(η)`), of dimension at most one, and not of dimension zero since its genus is
  positive;
* `f_*𝒪 = 𝒪` universally: the structure map of every base change of the generic fibre along a
  morphism of schemes is invertible (Stacks 0E0L), and pullback of global functions along a base
  change to an algebraic space is tested on base changes to schemes;
* `R¹f_*𝒪` is locally free of rank the genus of the generic fibre (Stacks 071N, read through the
  comparison of the étale and Zariski direct images), which is the genus of `X`.

## Main results

* `hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism_of_isIso_c`:
  `f_*𝒪 = 𝒪` universally for the family of curves of a morphism of schemes whose base changes
  have invertible structure maps.
* `AlgebraicGeometry.isSmoothH0Family_and_hasGenus_genericFibre`: the generic fibre of a
  smoothing lies in `𝓜_g`.

## References

* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0E0L](https://stacks.math.columbia.edu/tag/0E0L)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`f_*𝒪_X = 𝒪_S` universally for the family of curves of a morphism of schemes**, as soon as
the structure map `𝒪 ⟶ f'_*𝒪` of every base change of the morphism along a morphism of schemes of
the site is invertible. -/
theorem hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism_of_isIso_c
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (hc : ∀ (V : BigFppfOver B integerBase hZ) (v : V ⟶ U),
      IsIso ((BigFppfOver.toScheme B integerBase hZ).map (pullback.snd g v)).c) :
    HasUniversallyBijectiveGlobalFunctions B hZ
      (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) := by
  intro Y' g'
  refine Space.bijective_globalFunctionsMap_of_forall_schemeSpace _ fun V t => ?_
  let hff := schemeSpaceFunctorFullyFaithful B (S := integerBase) hZ
  let v : V ⟶ U := hff.preimage (t ≫ g')
  have hv : schemeSpaceMap v = t ≫ g' := hff.map_preimage _
  have hsite : IsPullback (yoneda.map (pullback.fst g v)) (yoneda.map (pullback.snd g v))
      (yoneda.map g) (yoneda.map v) :=
    Functor.map_isPullback yoneda (IsPullback.of_hasPullback g v)
  have hsp0 : IsPullback (schemeSpaceMap (pullback.fst g v)) (schemeSpaceMap (pullback.snd g v))
      (schemeSpaceMap g) (schemeSpaceMap v) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsite.w) hsite
  have hsp : IsPullback (schemeSpaceMap (pullback.fst g v)) (schemeSpaceMap (pullback.snd g v))
      (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase
      (t ≫ g') := hv ▸ hsp0
  have sq := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
    (ObjectProperty.homMk (pullback.snd
      (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase.hom
        g'.hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase g' ⟶
          Y') t).paste_horiz
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
      (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase g')
  let e := sq.isoIsPullback _ _ hsp
  have he : (ObjectProperty.homMk (pullback.snd (ObjectProperty.homMk (pullback.snd
      (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase.hom
        g'.hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ
          (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase g' ⟶
            Y').hom t.hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ _ t ⟶ schemeSpace V) =
      e.hom ≫ schemeSpaceMap (pullback.snd g v) :=
    (IsPullback.isoIsPullback_hom_snd _ _ _ _).symm
  rw [he, Space.globalFunctionsMap_comp, RingHom.coe_comp]
  refine ((Space.globalFunctionsMapEquiv B integerBase hZ e).bijective.of_comp_iff' _).2 ?_
  rw [Space.bijective_globalFunctionsMap_schemeSpaceMap_iff]
  have := hc V v
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (inferInstanceAs (IsIso (((BigFppfOver.toScheme B integerBase hZ).map
      (pullback.snd g v)).c.app (Opposite.op ⊤))))

/-- An element of `WithBot ℕ∞` which is at most one and not at most zero is one. -/
private theorem eq_one_of_le_one_of_not_le_zero {d : WithBot ℕ∞} (h₁ : d ≤ 1) (h₀ : ¬ d ≤ 0) :
    d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h₀
  | coe d =>
    norm_cast at h₁ h₀ ⊢
    induction d using ENat.recTopCoe with
    | top => simp at h₁
    | coe n =>
      norm_cast at h₁ h₀ ⊢
      omega

open PowerSeriesFamily in
/-- **The generic fibre of a smoothing of a curve of genus `g ≥ 2` lies in `𝓜_g`.** Let
`g : Y ⟶ Spec k⟦t⟧` be proper, flat and of finite presentation with smooth generic fibre, whose
special fibre `X` is a geometrically connected and geometrically reduced proper scheme of
dimension at most one over `k` with `H⁰(X, 𝒪_X) = k` and genus at least two. Then the family of
curves of the generic fibre `Y_η ⟶ Spec κ(η)` is smooth of relative dimension one, has
`f_*𝒪 = 𝒪` universally, and has the genus of `X`. -/
theorem isSmoothH0Family_and_hasGenus_genericFibre {k : Type u} [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of (PowerSeries k))) [IsProper g] [Flat g]
    [LocallyOfFinitePresentation g] [Smooth (g.fiberToSpecResidueField (genericPoint k))]
    {X : Scheme.{u}} {a : X ⟶ Y} (f : X ⟶ Spec (.of k)) (h : IsPullback a f g (specialPoint k))
    [IsProper f] (hdimX : topologicalKrullDim X ≤ 1) [GeometricallyReduced f]
    [GeometricallyConnected f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hg : 2 ≤ genus f)
    (hYη : B.Contains (g.fiber (genericPoint k)))
    (hK : B.Contains (Spec (.of ((Spec (.of (PowerSeries k))).residueField (genericPoint k)))))
    (hflat : Flat (g.fiberToSpecResidueField (genericPoint k)))
    (hproper : IsProper (g.fiberToSpecResidueField (genericPoint k)))
    (hlfp : LocallyOfFinitePresentation (g.fiberToSpecResidueField (genericPoint k)))
    (hdimη : topologicalKrullDim (g.fiber (genericPoint k)) ≤ 1) :
    IsSmoothH0Family B hZ (curveFamilyOfProperFlatMorphism B hZ
        (integerSiteMap B hZ hYη hK (g.fiberToSpecResidueField (genericPoint k)))
        hflat hproper hlfp hdimη) ∧
      CurveFamily.HasGenus B hZ (curveFamilyOfProperFlatMorphism B hZ
        (integerSiteMap B hZ hYη hK (g.fiberToSpecResidueField (genericPoint k)))
        hflat hproper hlfp hdimη) (genus f) := by
  obtain ⟨hc, hcbc⟩ := isIso_c_genericFibre g f h
  have := hc
  have := hproper
  have : IsIso (g.fiberToSpecResidueField (genericPoint k)).appTop :=
    isIso_appTop_of_isIso_c (g.fiberToSpecResidueField (genericPoint k))
  have hΓ : IsIso ((Scheme.ΓSpecIso
      (.of ((Spec (.of (PowerSeries k))).residueField (genericPoint k)))).inv ≫
      (g.fiberToSpecResidueField (genericPoint k)).appTop) := inferInstance
  have hgen : genus (g.fiberToSpecResidueField (genericPoint k)) = genus f :=
    genus_genericFibre_eq g f h hdimX
  have : IrreducibleSpace (g.fiber (genericPoint k)) :=
    irreducibleSpace_of_smooth_of_isIso_appTop
      ((Spec (.of (PowerSeries k))).residueField (genericPoint k))
      (g.fiberToSpecResidueField (genericPoint k)) hΓ
  have hdim1 : topologicalKrullDim (g.fiber (genericPoint k)) = 1 := by
    refine eq_one_of_le_one_of_not_le_zero hdimη fun h0 => ?_
    have hz := isZero_cohomologyOverField_of_topologicalKrullDim_le
      ((Spec (.of (PowerSeries k))).residueField (genericPoint k))
      (g.fiberToSpecResidueField (genericPoint k))
      (SheafOfModules.unit (g.fiber (genericPoint k)).ringCatSheaf) (d := 0) (i := 1)
      (by exact_mod_cast h0) (by omega)
    have h1 : genus (g.fiberToSpecResidueField (genericPoint k)) = 0 := by
      have := ModuleCat.subsingleton_of_isZero hz
      exact ((genus_eq_finrank_structureSheafCohomology _).trans
        (structureSheafCohomologyIsoCohomologyOverField
          ((Spec (.of (PowerSeries k))).residueField (genericPoint k))
          (g.fiberToSpecResidueField (genericPoint k)) 1).toLinearEquiv.finrank_eq).trans
        Module.finrank_zero_of_subsingleton
    omega
  let p := integerSiteMap B hZ hYη hK (g.fiberToSpecResidueField (genericPoint k))
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map p) :=
    inferInstanceAs (LocallyOfFiniteType (g.fiberToSpecResidueField (genericPoint k)))
  refine ⟨⟨⟨(Space.isSmooth_yoneda_map_iff B integerBase hZ p).2
      (inferInstanceAs (Smooth (g.fiberToSpecResidueField (genericPoint k)))), ?_⟩, ?_⟩, ?_⟩
  · refine (hasRelativeDimension_schemeSpaceMap_iff_forall_irreducibleComponents B hZ 1 p
      ((Spec (.of (PowerSeries k))).residueField (genericPoint k)) rfl hft).2 fun W hW => ?_
    have : IrreducibleSpace ((BigFppfOver.toScheme B integerBase hZ).obj
        (integerSiteObject B hZ hYη)) :=
      inferInstanceAs (IrreducibleSpace (g.fiber (genericPoint k)))
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hW
    subst hW
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph]
    exact_mod_cast hdim1
  · exact hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism_of_isIso_c p
      _ _ _ _ _ _ _ fun V v => hcbc (Functor.map_isPullback (BigFppfOver.toScheme B integerBase hZ)
        (IsPullback.of_hasPullback p v))
  · have h₁ := isFiniteLocallyFreeOfRank_firstDirectImage_curveFamilyOverFieldOfProper_genus
      (B := B) (hZ := hZ) ((Spec (.of (PowerSeries k))).residueField (genericPoint k)) p rfl hproper
      hdimη
    have h₂ : CurveFamily.HasGenus B hZ (curveFamilyOfProperFlatMorphism B hZ p hflat hproper
        hlfp hdimη) (genus ((g.fiberToSpecResidueField (genericPoint k)) ≫ eqToHom rfl)) := h₁
    convert h₂ using 2
    rw [← hgen]
    exact congrArg genus (Category.comp_id _).symm

end AlgebraicGeometry

end
