module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineBaseChangeModuli
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
import all StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantModuliSpace

/-!
# The moduli morphism of a well-nigh affine stack is a uniform categorical moduli space

Let `𝒳` be a well-nigh affine algebraic stack with chart `x : U ⟶ 𝒳`, relation `s, t : R ⟶ U`
and moduli morphism `f : 𝒳 ⟶ M = Spec C`. For a flat morphism `T ⟶ M` from an affine scheme
`T = Spec C'`, the base change `(U', R', s', t')` of the groupoid along `C ⟶ C'` (Stacks 03BK,
`AlgebraicGeometry.GroupoidScheme.exists_affineInvariantBaseChange`) has `U' = T ×_M U`, and
`U' ⟶ T` is a categorical quotient of `s', t'` in the category of affine schemes because the
invariant functions of the base change are `C'` (Stacks 03BK, part (3)). By
`AlgebraicGeometry.Stack.WellNighAffineChart.isCategoricalModuliSpaceIn_baseChange` the base
change `T ×_M 𝒳 ⟶ T` of `f` is then a categorical moduli space in affine schemes, which is the
uniformity assertion of Stacks 0DUP
(`AlgebraicGeometry.Stack.WellNighAffineChart.isUniformCategoricalModuliSpaceIn_moduliMap`).

## References

* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Morphisms

namespace AlgebraicGeometry.Stack.WellNighAffineChart

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : WellNighAffineChart.{u, w} B S hS 𝒳)

/-- **The scheme-level input of uniformity.** For a flat extension `C ⟶ C'` of the invariant ring
and an affine object `T` of the site identified with `Spec C'` over `M`, the base change of the
groupoid of the chart is an affine groupoid of the site over `T ×_M U ⇉ U'` whose quotient map
`U' ⟶ T` is a categorical quotient in the category of affine schemes. -/
theorem exists_flatBaseChange {C' : Type u} [CommRing C']
    [Algebra (invariantRing K.groupoidScheme) C'] [Module.Flat (invariantRing K.groupoidScheme) C']
    {T : BigFppfOver B S hS} (a₀ : T ⟶ K.moduliObject)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of C'))
    (heT : eT.hom ≫ GroupoidScheme.invariantSpectrumMap K.groupoidScheme C' =
      (BigFppfOver.toScheme B S hS).map a₀) :
    ∃ (U' : BigFppfOver B S hS) (pr₁ : U' ⟶ T) (pr₂ : U' ⟶ K.U)
      (_ : IsPullback pr₂ pr₁ K.quotientMap a₀) (V' : BigFppfOver B S hS) (s' t' : V' ⟶ U')
      (ρ : V' ⟶ K.V), s' ≫ pr₂ = ρ ≫ K.s ∧ t' ≫ pr₂ = ρ ≫ K.t ∧ s' ≫ pr₁ = t' ≫ pr₁ ∧
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ ψ : U' ⟶ Z, s' ≫ ψ = t' ≫ ψ → ∃! h : T ⟶ Z, pr₁ ≫ h = ψ := by
  classical
  obtain ⟨G'⟩ := GroupoidScheme.exists_affineInvariantBaseChange K.groupoidScheme C'
  have : IsAffine G'.groupoid.objects.left := IsAffine.of_isIso G'.objectsIso.hom
  have : IsAffine G'.groupoid.arrows.left := IsAffine.of_isIso G'.arrowsIso.hom
  have : IsFiniteLocallyFree G'.groupoid.source.left := G'.source_isFiniteLocallyFree
  have : IsFiniteLocallyFree G'.groupoid.target.left := G'.target_isFiniteLocallyFree
  -- the base-changed object and arrow schemes lie in the site
  have hC' : B.Contains (Spec (.of C')) := BigFppfSite.contains_of_mono B eT.inv T.left.2
  have hU'c : B.Contains G'.groupoid.objects.left :=
    BigFppfSite.contains_of_mono B G'.objects_isPullback.isoPullback.hom
      (Scheme.size_pullback_lt _ _ K.U.left.2 hC')
  have hV'c : B.Contains G'.groupoid.arrows.left :=
    BigFppfSite.contains_of_mono B G'.arrows_isPullback.isoPullback.hom
      (Scheme.size_pullback_lt _ _ K.V.left.2 hC')
  let XU : Over S := Over.mk (G'.objectsProjection ≫ K.groupoidScheme.objects.hom)
  let XV : Over S := Over.mk (G'.arrowsProjection ≫ K.groupoidScheme.arrows.hom)
  let U' : BigFppfOver B S hS := Space.schemeSiteObject B hS (X := XU) hU'c
  let V' : BigFppfOver B S hS := Space.schemeSiteObject B hS (X := XV) hV'c
  let α : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of (invariantRing K.groupoidScheme)) :=
    (BigFppfOver.toScheme B S hS).map a₀
  have heT' : eT.hom ≫ GroupoidScheme.invariantSpectrumMap K.groupoidScheme C' = α := heT
  have hinvM : eT.inv ≫ α = GroupoidScheme.invariantSpectrumMap K.groupoidScheme C' := by
    rw [← heT', Iso.inv_hom_id_assoc]
  have ha₀S : α ≫ GroupoidScheme.invariantSpectrumToBase K.groupoidScheme =
      ((Space.siteToOver B hS).obj T).hom := Over.w ((Space.siteToOver B hS).map a₀)
  have hpbw : G'.objectsProjection ≫ GroupoidScheme.objectsToInvariantSpectrum K.groupoidScheme =
      G'.groupoid.objects.hom ≫ GroupoidScheme.invariantSpectrumMap K.groupoidScheme C' :=
    G'.objects_isPullback.w
  have w₁ : (G'.groupoid.objects.hom ≫ eT.inv) ≫ ((Space.siteToOver B hS).obj T).hom =
      XU.hom := by
    rw [← ha₀S, Category.assoc, ← Category.assoc eT.inv, hinvM, ← Category.assoc, ← hpbw,
      Category.assoc, GroupoidScheme.objectsToInvariantSpectrum_comp_invariantSpectrumToBase]
    rfl
  have key : ∀ {X Y : BigFppfOver B S hS}
      (g : (Space.siteToOver B hS).obj X ⟶ (Space.siteToOver B hS).obj Y),
      (BigFppfOver.toScheme B S hS).map ((Space.siteToOver B hS).preimage g) = g.left :=
    fun g => congrArg Over.Hom.left (Functor.map_preimage _ g)
  let pr₂ : U' ⟶ K.U := (Space.siteToOver B hS).preimage
    (Over.homMk G'.objectsProjection rfl : XU ⟶ K.groupoidScheme.objects)
  let pr₁ : U' ⟶ T := (Space.siteToOver B hS).preimage
    (Over.homMk (G'.groupoid.objects.hom ≫ eT.inv) w₁ : XU ⟶ (Space.siteToOver B hS).obj T)
  have hpr₂ : (BigFppfOver.toScheme B S hS).map pr₂ = G'.objectsProjection :=
    key _
  have hpr₁ : (BigFppfOver.toScheme B S hS).map pr₁ = G'.groupoid.objects.hom ≫ eT.inv :=
    key _
  -- the pullback square
  have hpbS : IsPullback G'.objectsProjection (G'.groupoid.objects.hom ≫ eT.inv)
      (GroupoidScheme.objectsToInvariantSpectrum K.groupoidScheme) α :=
    G'.objects_isPullback.of_iso (Iso.refl _) (Iso.refl _) eT.symm (Iso.refl _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (Category.id_comp _).symm
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans hinvM.symm)
  have hcommU : pr₂ ≫ K.quotientMap = pr₁ ≫ a₀ := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, hpr₂, hpr₁, toScheme_map_quotientMap]
    exact hpbS.w
  have hpb : IsPullback pr₂ pr₁ K.quotientMap a₀ :=
    IsPullback.of_map (BigFppfOver.toScheme B S hS) hcommU
      (by rwa [hpr₂, hpr₁, toScheme_map_quotientMap])
  -- the base-changed relation
  have hw : ∀ (m : K.groupoidScheme.arrows ⟶ K.groupoidScheme.objects)
      (g : G'.groupoid.arrows.left ⟶ G'.groupoid.objects.left),
      G'.arrowsProjection ≫ m.left = g ≫ G'.objectsProjection → g ≫ XU.hom = XV.hom :=
    fun m g hg => by
      change g ≫ G'.objectsProjection ≫ K.groupoidScheme.objects.hom =
        G'.arrowsProjection ≫ K.groupoidScheme.arrows.hom
      rw [← Category.assoc, ← hg, Category.assoc, Over.w m]
  have ws := hw _ _ G'.projection_source
  have wt := hw _ _ G'.projection_target
  let s' : V' ⟶ U' := (Space.siteToOver B hS).preimage (Over.homMk G'.groupoid.source.left ws :
    XV ⟶ XU)
  let t' : V' ⟶ U' := (Space.siteToOver B hS).preimage (Over.homMk G'.groupoid.target.left wt :
    XV ⟶ XU)
  let ρ : V' ⟶ K.V := (Space.siteToOver B hS).preimage
    (Over.homMk G'.arrowsProjection rfl : XV ⟶ K.groupoidScheme.arrows)
  have hs' : (BigFppfOver.toScheme B S hS).map s' = G'.groupoid.source.left :=
    key _
  have ht' : (BigFppfOver.toScheme B S hS).map t' = G'.groupoid.target.left :=
    key _
  have hρ : (BigFppfOver.toScheme B S hS).map ρ = G'.arrowsProjection :=
    key _
  have hstS : G'.groupoid.source.left ≫ G'.groupoid.objects.hom =
      G'.groupoid.target.left ≫ G'.groupoid.objects.hom := by
    rw [Over.w G'.groupoid.source, Over.w G'.groupoid.target]
  refine ⟨U', pr₁, pr₂, hpb, V', s', t', ρ, ?_, ?_, ?_, ?_⟩
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, hs', hpr₂, hρ]
    exact G'.projection_source.symm
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, ht', hpr₂, hρ]
    exact G'.projection_target.symm
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, hs', ht', hpr₁]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun g => g ≫ eT.inv) hstS).trans
      (Category.assoc _ _ _))
  · intro Z hZ ψ hψ
    have hψS : G'.groupoid.target.left ≫ (BigFppfOver.toScheme B S hS).map ψ =
        G'.groupoid.source.left ≫ (BigFppfOver.toScheme B S hS).map ψ := by
      have := congrArg (BigFppfOver.toScheme B S hS).map hψ
      rw [Functor.map_comp, Functor.map_comp, hs', ht'] at this
      exact this.symm
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) := hZ
    obtain ⟨χ, hχ, hu⟩ := GroupoidScheme.existsUnique_comp_objects_hom_of_flat_of_isAffine
      K.groupoidScheme G' ((BigFppfOver.toScheme B S hS).map ψ) hψS
    -- `U' ⟶ T` is an epimorphism of schemes
    have hepi : ∀ {W : Scheme.{u}} (c d : (BigFppfOver.toScheme B S hS).obj T ⟶ W),
        (G'.groupoid.objects.hom ≫ eT.inv) ≫ c = (G'.groupoid.objects.hom ≫ eT.inv) ≫ d →
          c = d := by
      intro W c d hcd
      have := GroupoidScheme.isIso_specMap_canonicalMap K.groupoidScheme G'
      have hobj := GroupoidScheme.objects_hom_eq_objectsToInvariantSpectrum_comp K.groupoidScheme G'
      have h₁ : GroupoidScheme.objectsToInvariantSpectrum G'.groupoid ≫
            (Spec.map (CommRingCat.ofHom G'.canonicalMapToInvariantFunctions) ≫ eT.inv ≫ c) =
          GroupoidScheme.objectsToInvariantSpectrum G'.groupoid ≫
            (Spec.map (CommRingCat.ofHom G'.canonicalMapToInvariantFunctions) ≫ eT.inv ≫ d) := by
        rw [← Category.assoc, hobj, ← Category.assoc, ← Category.assoc, hobj]
        simpa only [Category.assoc] using hcd
      exact (cancel_epi eT.inv).1 ((cancel_epi _).1
        (GroupoidScheme.ext_of_comp_objectsToInvariantSpectrum G'.groupoid _ _ h₁))
    have hψZ := Over.w ((Space.siteToOver B hS).map ψ)
    have hover : (eT.hom ≫ χ) ≫ ((Space.siteToOver B hS).obj Z).hom =
        ((Space.siteToOver B hS).obj T).hom := by
      refine hepi _ _ (Eq.trans ?_ w₁.symm)
      exact ((Category.assoc _ _ _).trans (congrArg (fun g => G'.groupoid.objects.hom ≫ g)
        ((congrArg (fun g => eT.inv ≫ g) (Category.assoc _ _ _)).trans
          (Iso.inv_hom_id_assoc eT _)))).trans
        (((Category.assoc _ _ _).symm.trans
          (congrArg (fun g => g ≫ ((Space.siteToOver B hS).obj Z).hom) hχ)).trans hψZ)
    let h : T ⟶ Z := (Space.siteToOver B hS).preimage
      (Over.homMk (eT.hom ≫ χ) hover :
        (Space.siteToOver B hS).obj T ⟶ (Space.siteToOver B hS).obj Z)
    have hh : (BigFppfOver.toScheme B S hS).map h = eT.hom ≫ χ :=
      key _
    refine ⟨h, ?_, fun h' hh' => ?_⟩
    · apply (BigFppfOver.toScheme B S hS).map_injective
      rw [Functor.map_comp, hpr₁, hh]
      exact (Category.assoc _ _ _).trans ((congrArg (fun g => G'.groupoid.objects.hom ≫ g)
        (Iso.inv_hom_id_assoc eT χ)).trans hχ)
    · apply (BigFppfOver.toScheme B S hS).map_injective
      have h₀ := congrArg (BigFppfOver.toScheme B S hS).map hh'
      rw [Functor.map_comp, hpr₁] at h₀
      have h₁ : G'.groupoid.objects.hom ≫ (eT.inv ≫ (BigFppfOver.toScheme B S hS).map h') =
          (BigFppfOver.toScheme B S hS).map ψ := (Category.assoc _ _ _).symm.trans h₀
      rw [hh, ← hu _ h₁, Iso.hom_inv_id_assoc]

/-- The ring map `C ⟶ Γ(T)` induced by a morphism `T ⟶ M = Spec C` of the site. -/
noncomputable abbrev baseRingHom {T : BigFppfOver B S hS} (a₀ : T ⟶ K.moduliObject) :
    CommRingCat.of (invariantRing K.groupoidScheme) ⟶ Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  (Scheme.ΓSpecIso (.of (invariantRing K.groupoidScheme))).inv ≫
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map a₀ :
      (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of (invariantRing K.groupoidScheme))).op

/-- A morphism from `T` to `M = Spec C` is the unit of `T` followed by the spectrum of the
induced ring map. -/
theorem toSpecΓ_comp_specMap_baseRingHom {T : BigFppfOver B S hS} (a₀ : T ⟶ K.moduliObject) :
    ((BigFppfOver.toScheme B S hS).obj T).toSpecΓ ≫ Spec.map (K.baseRingHom a₀) =
      ((BigFppfOver.toScheme B S hS).map a₀ :
        (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of (invariantRing K.groupoidScheme))) := by
  refine ext_to_Spec ?_
  rw [Scheme.Γ_map_op, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  simp only [baseRingHom]
  exact congrArg (fun g => _ ≫ g) (Iso.hom_inv_id_assoc _ _)

/-- **Flatness of a morphism from an affine algebraic space to `M`, read on schemes.** -/
theorem flat_of_isFlat {Y' : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (e : Y'.obj ≅ yoneda.obj T) (a : Y' ⟶ K.moduliSpace) (ha : Space.IsFlat B S hS a.hom)
    (a₀ : T ⟶ K.moduliObject) (ha₀ : e.inv ≫ a.hom = yoneda.map a₀) :
    Flat ((BigFppfOver.toScheme B S hS).map a₀) := by
  let V : Space.SmallEtale B S hS Y'.obj :=
    ⟨CostructuredArrow.mk e.inv,
      Space.presheaf_etale_of_isEtale B S hS (Space.isEtale_of_isIso B S hS e.inv)⟩
  let W : Space.SmallEtale B S hS K.moduliSpace.obj :=
    ⟨CostructuredArrow.mk (𝟙 K.moduliSpace.obj),
      Space.presheaf_etale_of_isEtale B S hS (Space.isEtale_of_isIso B S hS (𝟙 K.moduliSpace.obj))⟩
  have h := Space.isFlat_yoneda_map_of_comp_eq B S hS a ha (V := V) (W := W) a₀
    (by
      change yoneda.map a₀ ≫ 𝟙 _ = e.inv ≫ a.hom
      rw [Category.comp_id, ha₀])
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS Flat.isEtaleLocalOnSourceAndTarget
    a₀).1 h

/-- **Stacks 0DUP, uniformity: the moduli morphism `f : 𝒳 ⟶ M` of a well-nigh affine algebraic
stack is a uniform categorical moduli space in the category of affine schemes.** For a flat
morphism `Y' ⟶ M` from an affine scheme, the base change `Y' ×_M 𝒳 ⟶ Y'` is a categorical
moduli space in affine schemes, presented by any 2-fibre product. -/
theorem isUniformCategoricalModuliSpaceIn_moduliMap :
    IsUniformCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj)
      K.moduliSpace K.moduliMap.hom := by
  refine ⟨K.isAffineSpace_moduliSpace, fun Y' hY' a ha P hP => ?_⟩
  obtain ⟨T, hT, ⟨e⟩⟩ := hY'
  let a₀ : T ⟶ K.moduliObject := yoneda.preimage (e.inv ≫ a.hom)
  have ha₀ : e.inv ≫ a.hom = yoneda.map a₀ := (Functor.map_preimage _ _).symm
  have hflat := K.flat_of_isFlat e a ha a₀ ha₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  let : Algebra (invariantRing K.groupoidScheme) Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    (K.baseRingHom a₀).hom.toAlgebra
  have hspec : (Scheme.isoSpec ((BigFppfOver.toScheme B S hS).obj T)).hom ≫
      GroupoidScheme.invariantSpectrumMap K.groupoidScheme
        Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) = (BigFppfOver.toScheme B S hS).map a₀ :=
    K.toSpecΓ_comp_specMap_baseRingHom a₀
  let α : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (.of (invariantRing K.groupoidScheme)) :=
    (BigFppfOver.toScheme B S hS).map a₀
  have hα : Flat α := hflat
  have : Module.Flat (invariantRing K.groupoidScheme)
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := by
    have heq : (Scheme.isoSpec ((BigFppfOver.toScheme B S hS).obj T)).inv ≫ α =
        GroupoidScheme.invariantSpectrumMap K.groupoidScheme
          Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := (Iso.inv_comp_eq _).2 hspec.symm
    have hf : Flat (GroupoidScheme.invariantSpectrumMap K.groupoidScheme
        Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) := by
      rw [← heq]
      infer_instance
    exact Flat.SpecMap_iff.1 hf
  obtain ⟨U', pr₁, pr₂, hpb, V', s', t', ρ, hs, ht, hpr, hmod⟩ :=
    K.exists_flatBaseChange a₀ (Scheme.isoSpec ((BigFppfOver.toScheme B S hS).obj T)) hspec
  exact isCategoricalModuliSpaceIn_of_isTwoFibreProduct _ hP
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
    (K.isCategoricalModuliSpaceIn_baseChange ha₀ hpb hT s' t' ρ hs ht hpr hmod)

end AlgebraicGeometry.Stack.WellNighAffineChart

end
