module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleInverseImageSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineCoversTop

/-!
# Inverse image of pro-étale sheaves of modules along an immersion preserves limits

Let `i : Z ⟶ X` be an immersion of schemes and `Λ` a ring. Inverse image of sheaves of
`Λ`-modules on the small pro-étale sites along `i` preserves limits.

Along an open immersion the inverse image is restriction, which preserves limits. Along a closed
immersion of affine schemes it preserves limits by Stacks 09BL (2), which is
`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_proetaleModuleInverseImage_of_isClosedImmersion`
in this library. An immersion is, locally on its source, a closed immersion of affine schemes
followed by an open immersion, and being a limit cone of sheaves can be checked after restriction
to the members of an open covering.

## Main results

* `AlgebraicGeometry.ProEtale.isLimit_of_isLimit_mapCone_proetaleModuleInverseImage`: a cone of
  pro-étale sheaves of modules is a limit cone as soon as its restrictions to the members of an
  open covering are.
* `AlgebraicGeometry.ProEtale.isZero_of_isZero_proetaleModuleInverseImage`: vanishing of a sheaf
  of modules can be checked on the members of an open covering.
* `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_proetaleModuleInverseImage_of_isImmersion`:
  inverse image along an immersion preserves limits.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] proetalePostcompose_isContinuous

variable (Λ : Type v) [CommRing Λ]

/-- Inverse image along an open immersion preserves limits: it is restriction. -/
theorem preservesLimitsOfShape_proetaleModuleInverseImage_of_isOpenImmersion {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : Type*) [Category* K]
    [HasLimitsOfShape K (ModuleCat.{max (u + 1) v w} Λ)] :
    PreservesLimitsOfShape K (proetaleModuleInverseImage.{u, v, w} j Λ) :=
  preservesLimitsOfShape_of_natIso (proetaleModuleInverseImageIsoRestriction.{u, v, w} Λ j).symm

/-- **Limit cones of pro-étale sheaves are local for the Zariski topology.** Let `j a : W a ⟶ Z`
be open immersions jointly covering `Z`. A cone of sheaves of modules on the small pro-étale site
of `Z` is a limit cone as soon as its inverse image along each `j a` is. -/
theorem isLimit_of_isLimit_mapCone_proetaleModuleInverseImage {Z : Scheme.{u}} {ι : Type u}
    {W : ι → Scheme.{u}} (j : ∀ a, W a ⟶ Z) [∀ a, IsOpenImmersion (j a)]
    (hj : ∀ z, ∃ a, z ∈ Set.range (j a)) {K : Type*} [Category* K]
    [HasLimitsOfShape K (ModuleCat.{max (u + 1) v w} Λ)]
    {F : K ⥤ Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) v w} Λ)} (c : Cone F)
    (hc : ∀ a, IsLimit ((proetaleModuleInverseImage.{u, v, w} (j a) Λ).mapCone c)) :
    Nonempty (IsLimit c) := by
  classical
  let A := ModuleCat.{max (u + 1) v w} Λ
  let B : ObjectProperty Z.ProEt := fun T ↦
    ∃ (a : ι) (T' : (W a).ProEt), Nonempty ((proetalePostcompose (j a)).obj T' ≅ T)
  refine isLimit_of_isLimit_mapCone_sheafSections (B := B) ?_ c ?_
  · intro T
    let V (a : ι) : T.left.Opens := T.hom ⁻¹ᵁ (j a).opensRange
    have hV (a : ι) : WeaklyEtale ((V a).ι ≫ T.hom) := by
      have : WeaklyEtale T.hom := T.prop
      infer_instance
    let Ta (a : ι) : Z.ProEt := @Scheme.ProEt.mk Z _ ((V a).ι ≫ T.hom) (hV a)
    let pa (a : ι) : Ta a ⟶ T := MorphismProperty.Over.homMk (V a).ι rfl
    refine ⟨ι, Ta, pa, ?_, fun a ↦ ?_⟩
    · refine Precoverage.generate_mem_toGrothendieck ?_
      change Presieve.map (Scheme.ProEt.forget Z ⋙ Over.forget Z) (Presieve.ofArrows Ta pa) ∈
        Scheme.proetalePrecoverage _
      rw [Presieve.map_ofArrows]
      refine ProEtale.zariskiPrecoverage_le_proetalePrecoverage _ ?_
      refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun a ↦ ?_⟩
      · obtain ⟨a, y, hy⟩ := hj (T.hom x)
        exact ⟨a, ⟨x, ⟨y, hy⟩⟩, rfl⟩
      · change IsOpenImmersion (V a).ι
        infer_instance
    · have hrange : Set.range ((V a).ι ≫ T.hom) ⊆ Set.range (j a) := by
        rintro _ ⟨x, rfl⟩
        exact x.2
      let l := IsOpenImmersion.lift (j a) ((V a).ι ≫ T.hom) hrange
      have hl : l ≫ j a = (V a).ι ≫ T.hom := IsOpenImmersion.lift_fac _ _ _
      have hwl : WeaklyEtale l :=
        MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) l (j a)
          inferInstance (by rw [hl]; exact hV a)
      refine ⟨a, @Scheme.ProEt.mk (W a) _ l hwl, ⟨MorphismProperty.Over.isoMk (Iso.refl _) ?_⟩⟩
      change 𝟙 _ ≫ ((V a).ι ≫ T.hom) = l ≫ j a
      rw [Category.id_comp, hl]
  · rintro T ⟨a, T', ⟨e⟩⟩
    have h1 : IsLimit (((sheafSections (Scheme.ProEt.topology (W a)) A).obj (op T')).mapCone
        ((proetaleModuleInverseImage.{u, v, w} (j a) Λ).mapCone c)) :=
      isLimitOfPreserves (sheafToPresheaf _ A ⋙ (evaluation _ A).obj (op T')) (hc a)
    let iso : proetaleModuleInverseImage.{u, v, w} (j a) Λ ⋙
        (sheafSections (Scheme.ProEt.topology (W a)) A).obj (op T') ≅
        (sheafSections (Scheme.ProEt.topology Z) A).obj (op T) :=
      Functor.isoWhiskerRight (proetaleModuleInverseImageIsoRestriction.{u, v, w} Λ (j a))
          ((sheafSections (Scheme.ProEt.topology (W a)) A).obj (op T')) ≪≫
        (sheafSections (Scheme.ProEt.topology Z) A).mapIso e.op.symm
    exact ⟨IsLimit.mapConeEquiv iso h1⟩

/-- **Vanishing of pro-étale sheaves is local for the Zariski topology.** Let `j a : W a ⟶ Z` be
open immersions jointly covering `Z`. A sheaf of modules on the small pro-étale site of `Z` whose
inverse image along each `j a` vanishes is zero: it is a limit of the empty diagram, by
`AlgebraicGeometry.ProEtale.isLimit_of_isLimit_mapCone_proetaleModuleInverseImage`. -/
theorem isZero_of_isZero_proetaleModuleInverseImage {Z : Scheme.{u}} {ι : Type u}
    {W : ι → Scheme.{u}} (j : ∀ a, W a ⟶ Z) [∀ a, IsOpenImmersion (j a)]
    (hj : ∀ z, ∃ a, z ∈ Set.range (j a))
    (F : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) v w} Λ))
    (h : ∀ a, IsZero ((proetaleModuleInverseImage.{u, v, w} (j a) Λ).obj F)) : IsZero F := by
  have : HasLimitsOfShape (Discrete PEmpty.{1}) (ModuleCat.{max (u + 1) v w} Λ) :=
    hasLimitsOfShape_of_hasFiniteLimits _ _
  exact IsTerminal.isZero (isLimit_of_isLimit_mapCone_proetaleModuleInverseImage Λ j hj
    (asEmptyCone F) fun a => isLimitEmptyConeEquiv _ (asEmptyCone _)
      ((proetaleModuleInverseImage.{u, v, w} (j a) Λ).mapCone (asEmptyCone F)) (Iso.refl _)
      (h a).isTerminal).some

/-- **Inverse image along an immersion preserves limits.** Restricted to the preimage of an
affine open `V` of the open subscheme in which `i` is closed, `i` is a closed immersion of affine
schemes followed by the open immersion of `V` into `X`; inverse image along either preserves
limits, and limit cones are local for the Zariski topology. -/
theorem preservesLimitsOfShape_proetaleModuleInverseImage_of_isImmersion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (K : Type*) [Category* K]
    [HasLimitsOfShape K (ModuleCat.{max (u + 1) v w} Λ)] :
    PreservesLimitsOfShape K (proetaleModuleInverseImage.{u, v, w} i Λ) := by
  constructor
  intro F
  refine preservesLimit_of_preserves_limit_cone (limit.isLimit F) ?_
  let c := i.liftCoborder
  let j (a : (i.coborderRange : Scheme).affineOpens) : (c ⁻¹ᵁ a.1 : Scheme) ⟶ Z := (c ⁻¹ᵁ a.1).ι
  refine (isLimit_of_isLimit_mapCone_proetaleModuleInverseImage Λ j (fun z ↦ ?_) _
    fun a ↦ ?_).some
  · obtain ⟨V, hV, hzV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (i.coborderRange : Scheme).isBasis_affineOpens
      (show c z ∈ (⊤ : (i.coborderRange : Scheme).Opens) from trivial)
    exact ⟨⟨V, hV⟩, by rwa [Scheme.Opens.range_ι]⟩
  · have : IsAffine (a.1 : Scheme) := a.2
    let t := c ∣_ a.1
    let o := a.1.ι ≫ i.coborderRange.ι
    have : IsAffine (c ⁻¹ᵁ a.1 : Scheme) := isAffine_of_isAffineHom t
    have hfac : j a ≫ i = t ≫ o := by
      calc j a ≫ i = (c ⁻¹ᵁ a.1).ι ≫ c ≫ i.coborderRange.ι := by
            rw [Scheme.Hom.liftCoborder_ι i]
        _ = t ≫ o := by
          rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    have := preservesLimitsOfShape_proetaleModuleInverseImage_of_isClosedImmersion.{w} t Λ K
    have := preservesLimitsOfShape_proetaleModuleInverseImage_of_isOpenImmersion.{w} Λ o K
    have h2 : IsLimit ((proetaleModuleInverseImage.{u, v, w} o Λ ⋙
        proetaleModuleInverseImage.{u, v, w} t Λ).mapCone (limit.cone F)) :=
      isLimitOfPreserves _ (limit.isLimit F)
    let e : proetaleModuleInverseImage.{u, v, w} o Λ ⋙ proetaleModuleInverseImage.{u, v, w} t Λ ≅
        proetaleModuleInverseImage.{u, v, w} i Λ ⋙ proetaleModuleInverseImage.{u, v, w} (j a) Λ :=
      proetaleModuleInverseImageCompIso Λ t o ≪≫
        eqToIso (congrArg (fun f ↦ proetaleModuleInverseImage.{u, v, w} f Λ) hfac.symm) ≪≫
        (proetaleModuleInverseImageCompIso Λ (j a) i).symm
    exact IsLimit.mapConeEquiv e h2

end AlgebraicGeometry.ProEtale

end
