module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverAffineFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.ChartEqualizerLift
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SpacesEtaleEquivalenceGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsThickeningSequence

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# A thickening of an affine algebraic space with a nilpotent chart is affine

Let `S` be a scheme of a big fppf site, let `i : G ⟶ X` be a thickening of algebraic spaces over
`S` with `G` affine, and suppose `X` has a surjective étale chart `w' : U' ⟶ X` from an affine
object over which the base change of `i` is cut out by a nilpotent ideal. Then `X` is affine. In
particular a thickening of finite order of an affine algebraic space is affine.

## Main results

* `C1573.exists_desc_yoneda_of_surjectiveEtale`: a morphism of the site out of a surjective étale
  chart which is invariant under the kernel pair descends to the algebraic space.
* `C1573.isAffineSpace_of_isPullback_of_isThickeningHom`: an étale space over the ambient space of
  a thickening with the same base change as an affine chart is affine (Stacks 05ZH).
* `C1573.isAffineSpace_of_isThickeningHom_of_isNilpotent_chart`: the statement above.
* `C1573.isAffineSpace_of_isThickeningHom_of_isNilpotent_chart_of_isTerminal`: the statement
  above over a terminal base.
* A finite-order thickening of an affine algebraic space is affine:
  `isAffineSpace_of_isFiniteOrderThickening`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/AffineOfFiniteOrderThickening.lean`.

All names are in the namespace `AlgebraicGeometry.Space`.

## Implementation notes

Over a terminal base, the proof follows the plan of Stacks 05ZR for finite order thickenings, with
the deformation-theoretic step (Stacks 05YT) replaced by topological invariance of the étale site.

* `X` is separated, being the image of the separated `G` under a surjective universally closed
  morphism (Stacks 05Z2), so the chart is an affine morphism (Stacks 08GB, part (4)) and its kernel
  pair `R' = U' ×_X U'` is affine.
* The ring `A' = {b ∈ Γ(U') | q₁^* b = q₂^* b}` maps onto `Γ(G)`, with nilpotent kernel, by
  `AlgebraicGeometry.Space.C1573.exists_appTop_eq_of_isThickeningHom_chart`; so `G ⊂ Spec A'` is a
  thickening of affine schemes, and the chart descends to a morphism `p : X ⟶ Spec A'` extending
  it.
* The étale chart `U ⟶ G` lifts across the thickening `G ⊂ Spec A'` to an affine étale surjection
  `V ⟶ Spec A'` (Stacks 039R and Stacks 06AD).
* `P = X ×_{Spec A'} V` and `U'` are objects of the spaces-étale site of `X` whose base changes to
  `G` are both `U`, so they are isomorphic by full faithfulness of base change (Stacks 05ZH); in
  particular `P` is affine, and `X` is affine by fpqc descent along `V ⟶ Spec A'`.

A general base is reduced to the terminal one by the lower-shriek extension of Stacks 03I5,
which preserves closed immersions, surjectivity on points, étale charts and their base changes,
and preserves and reflects affineness.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 05Z2](https://stacks.math.columbia.edu/tag/05Z2)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- **Descent of a morphism to a representable along a surjective étale chart.** A morphism of
the site out of a surjective étale chart `f : U ⟶ F` of an algebraic space which is invariant
under the kernel pair of `f` is the restriction of a morphism `F ⟶ Y`. -/
theorem C1573.exists_desc_yoneda_of_surjectiveEtale {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {R U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    {Y : BigFppfOver B S hS} (g : U ⟶ Y) (hg : s ≫ g = t ≫ g) :
    ∃ d : F ⟶ yoneda.obj Y, f ≫ d = yoneda.map g := by
  classical
  let J := BigFppfOver.topology B S hS
  obtain ⟨hRsh, hUsh, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS f s t hR hF hsurj hetale
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let YF : Sheaf J (Type u) := ⟨yoneda.obj Y, (isAlgebraicSpace_yoneda B S hS Y).isSheaf⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let k : UF ⟶ YF := ⟨yoneda.map g⟩
  have hw : sf ≫ k = tf ≫ k := by
    apply Sheaf.hom_ext
    show yoneda.map s ≫ yoneda.map g = yoneda.map t ≫ yoneda.map g
    rw [← Functor.map_comp, ← Functor.map_comp, hg]
  let c : Cofork sf tf := Cofork.ofπ k hw
  let d := hc.desc c
  have hfac : (⟨f⟩ : UF ⟶ ⟨F, hF.isSheaf⟩) ≫ d = k := by
    exact hc.fac c WalkingParallelPair.one
  exact ⟨d.hom, congrArg (fun q => q.hom) hfac⟩

/-- The subring of regular functions on `U'` whose pullbacks along two maps `R' ⟶ U'` agree. -/
def C1573.chartEqualizer {U R : Scheme.{u}} (q₁ q₂ : R ⟶ U) : Subring Γ(U, ⊤) :=
  RingHom.eqLocus q₁.appTop.hom q₂.appTop.hom

/-- A regular function lies in `chartEqualizer q₁ q₂` if and only if its pullbacks along `q₁` and
`q₂` agree. -/
theorem C1573.mem_chartEqualizer {U R : Scheme.{u}} {q₁ q₂ : R ⟶ U} {y : Γ(U, ⊤)} :
    y ∈ chartEqualizer q₁ q₂ ↔ q₁.appTop y = q₂.appTop y :=
  Iff.rfl

/-- The spectrum of the equalizer ring, as an object of the site over a terminal base. -/
noncomputable def C1573.chartEqualizerObj (hterm : IsTerminal S) {W' R' : BigFppfOver B S hS}
    (q₁ q₂ : R' ⟶ W') : BigFppfOver B S hS :=
  terminalSiteObject B S hS hterm (T := Spec (CommRingCat.of
    (chartEqualizer ((BigFppfOver.toScheme B S hS).map q₁)
      ((BigFppfOver.toScheme B S hS).map q₂))))
    (Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (p := CommRingCat.ofHom (chartEqualizer ((BigFppfOver.toScheme B S hS).map q₁)
        ((BigFppfOver.toScheme B S hS).map q₂)).subtype) Subtype.val_injective
      W'.left.property)

/-- The morphism of schemes from `U'` to the spectrum of the equalizer ring. -/
noncomputable def C1573.toChartEqualizer {U R : Scheme.{u}} (q₁ q₂ : R ⟶ U) :
    U ⟶ Spec (CommRingCat.of (chartEqualizer q₁ q₂)) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartEqualizer q₁ q₂).subtype)

/-- On global sections, `toChartEqualizer q₁ q₂` sends a section of the spectrum of the equalizer
ring to the underlying regular function on `U` of the corresponding element of the ring. -/
theorem C1573.toChartEqualizer_appTop {U R : Scheme.{u}} (q₁ q₂ : R ⟶ U)
    (x : Γ(Spec (CommRingCat.of (chartEqualizer q₁ q₂)), ⊤)) :
    (toChartEqualizer q₁ q₂).appTop x =
      ((Scheme.ΓSpecIso (CommRingCat.of (chartEqualizer q₁ q₂))).hom x).1 := by
  simp only [toChartEqualizer, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Scheme.toSpecΓ_appTop]
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
  simp

/-- The morphism `toChartEqualizer q₁ q₂` equalizes `q₁` and `q₂`. -/
theorem C1573.toChartEqualizer_comp_eq {U R : Scheme.{u}} (q₁ q₂ : R ⟶ U) :
    q₁ ≫ toChartEqualizer q₁ q₂ = q₂ ≫ toChartEqualizer q₁ q₂ := by
  refine ext_of_isAffine ?_
  ext x
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, toChartEqualizer_appTop]
  exact ((Scheme.ΓSpecIso _).hom x).2

/-- **An étale space over a thickening with the base change of an affine chart is affine.** Let
`i : G ⟶ X` be a thickening of algebraic spaces and let `a : P ⟶ X` and `w' : U' ⟶ X` be étale,
with `U'` an affine object of the site. If `a` and `w'` have the same base change `U ⟶ G` along
`i`, then `P` is affine: base change along a thickening is fully faithful on spaces-étale sites
(Stacks 05ZH), so `P ≅ U'` over `X`. -/
theorem C1573.isAffineSpace_of_isPullback_of_isThickeningHom {X G : AlgebraicSpaces B S hS}
    (i : G ⟶ X) (hi : IsThickeningHom B S hS i)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P) (a : P ⟶ X.1)
    (ha : IsEtale B S hS a)
    {W' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W')]
    (w' : yoneda.obj W' ⟶ X.1) (hw' : IsEtale B S hS w')
    {W : BigFppfOver B S hS} (η : yoneda.obj W ⟶ G.1) (j : W ⟶ W')
    (hW : IsPullback η (yoneda.map j) i.hom w')
    (b : yoneda.obj W ⟶ P) (hb : IsPullback η b i.hom a) :
    IsAffineSpace B S hS P := by
  let Psp : AlgebraicSpaces B S hS := ⟨P, hP⟩
  let Wsp : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let W'sp : AlgebraicSpaces B S hS := ⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩
  let aA : Psp ⟶ X := ObjectProperty.homMk a
  let w'A : W'sp ⟶ X := ObjectProperty.homMk w'
  let VP : SpacesEtale B S hS X := ⟨Over.mk aA, ha⟩
  let VW : SpacesEtale B S hS X := ⟨Over.mk w'A, hw'⟩
  let ηA : Wsp ⟶ G := ObjectProperty.homMk η
  have hbA : IsPullback (ObjectProperty.homMk b : Wsp ⟶ Psp) ηA aA i :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hb.flip
  have hWA : IsPullback (ObjectProperty.homMk (yoneda.map j) : Wsp ⟶ W'sp) ηA w'A i :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hW.flip
  let e₁ := (IsPullback.of_hasPullback aA i).isoIsPullback _ _ hbA
  let e₂ := (IsPullback.of_hasPullback w'A i).isoIsPullback _ _ hWA
  have he₁ : e₁.hom ≫ ηA = pullback.snd aA i :=
    (IsPullback.of_hasPullback aA i).isoIsPullback_hom_snd _ _ hbA
  have he₂ : e₂.hom ≫ ηA = pullback.snd w'A i :=
    (IsPullback.of_hasPullback w'A i).isoIsPullback_hom_snd _ _ hWA
  let Fu := (spacesBaseChange B S hS i).functor
  have := isEquivalence_spacesBaseChange_of_isThickeningHom B S hS i hi
  let φ : Fu.obj VP ≅ Fu.obj VW :=
    ObjectProperty.isoMk _ (Over.isoMk (e₁ ≪≫ e₂.symm) (by
      show (e₁.hom ≫ e₂.inv) ≫ pullback.snd w'A i = pullback.snd aA i
      rw [Category.assoc, ← he₂, Iso.inv_hom_id_assoc, he₁]))
  let ψ : VP ≅ VW := (Functor.FullyFaithful.ofFullyFaithful Fu).preimageIso φ
  let χ : P ≅ yoneda.obj W' :=
    (ObjectProperty.ι _).mapIso ((SpacesEtale.toSpaces B S hS X).mapIso ψ)
  exact ⟨W', inferInstance, ⟨χ⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **A thickening of an affine algebraic space with a nilpotent affine chart is affine**, over a
terminal base. Let `i : G ⟶ X` be a thickening of algebraic spaces over a terminal scheme `S`
with `G` affine, let `w' : U' ⟶ X` be a surjective étale chart from an affine object of the site,
and suppose the base change `j : U ⟶ U'` of `i` along `w'` has nilpotent kernel on global
sections. Then `X` is affine. -/
theorem C1573.isAffineSpace_of_isThickeningHom_of_isNilpotent_chart_of_isTerminal
    (hterm : IsTerminal S) {X G : AlgebraicSpaces B S hS} (i : G ⟶ X)
    (hi : IsThickeningHom B S hS i) (hG : IsAffineSpace B S hS G.1)
    {W' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W')]
    (w' : yoneda.obj W' ⟶ X.1)
    (hw'e : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w')
    (hw's : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w')
    {W : BigFppfOver B S hS} (j : W ⟶ W') (η : yoneda.obj W ⟶ G.1)
    (hW : IsPullback η (yoneda.map j) i.hom w')
    (hJ : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map j).appTop.hom)) :
    IsAffineSpace B S hS X.1 := by
  classical
  have hZ := B.contains_terminal
  -- The ambient space is separated and the chart has an affine kernel pair.
  have hsep : IsAbsolutelySeparated B S hS hZ X.1 :=
    isAbsolutelySeparated_of_isSurjective_of_universallyClosed B S hS hZ G.property X.property
      i.hom hi.surjective_pointsMap
      (universallyClosed_of_isClosedImmersion B S hS G.property X.property i.hom
        hi.isClosedImmersion)
      (isAbsolutelySeparated_of_isAffineSpace B S hS hZ hG)
  have haff : IsAffineHom B S hS w' :=
    isAffineHom_of_affine_source_of_isAbsolutelySeparated B S hS hZ ⟨W', inferInstance⟩ w' hsep
  obtain ⟨R'a, pa, q₂, hR'a⟩ := haff ⟨W', inferInstance⟩ w'
  let R' := (BigAffineFppf.inclusion B S hS).obj R'a
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj R') := R'a.property
  let q₁ : R' ⟶ W' := yoneda.preimage pa
  have hR' : IsPullback (yoneda.map q₁) (yoneda.map q₂) w' w' := by
    rwa [Functor.map_preimage]
  obtain ⟨T, hT, ⟨e⟩⟩ := hG
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  let k : W ⟶ T := yoneda.preimage (η ≫ e.hom)
  have hk : yoneda.map k = η ≫ e.hom := Functor.map_preimage _ _
  have hjci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) :=
    hi.isClosedImmersion.property w' η j hW
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map j)
  have hbc : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange],
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf w' →
        P ((BigFppfOver.toScheme B S hS).map k) := fun P _ hw ↦ by
    have : MorphismProperty.IsStableUnderBaseChange
        (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf :=
      MorphismProperty.relative_isStableUnderBaseChange _
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).1 ?_
    rw [hk]
    exact MorphismProperty.RespectsIso.postcomp _ e.hom η
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hW.flip hw)
  have hke : Etale ((BigFppfOver.toScheme B S hS).map k) := hbc _ hw'e
  have hks : Surjective ((BigFppfOver.toScheme B S hS).map k) := hbc _ hw's
  -- The spectrum of the equalizer ring and the descended morphism to it.
  let T' := chartEqualizerObj B S hS hterm q₁ q₂
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := by
    show IsAffine (Spec _)
    infer_instance
  let ψ : W' ⟶ T' := overMapOfSchemeHom B S hS hterm W' T'
    (toChartEqualizer ((BigFppfOver.toScheme B S hS).map q₁) ((BigFppfOver.toScheme B S hS).map q₂))
  have hFψ : (BigFppfOver.toScheme B S hS).map ψ = toChartEqualizer
      ((BigFppfOver.toScheme B S hS).map q₁) ((BigFppfOver.toScheme B S hS).map q₂) :=
    B.inclusion.map_preimage _
  have hψ : q₁ ≫ ψ = q₂ ≫ ψ := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, Functor.map_comp, hFψ]
    exact toChartEqualizer_comp_eq _ _)
  obtain ⟨f', hf'⟩ :=
    exists_desc_yoneda_of_surjectiveEtale B S hS X.property w' q₁ q₂ hR' hw's hw'e ψ hψ
  let φ : T ⟶ T' := yoneda.preimage (e.inv ≫ i.hom ≫ f')
  have hφ : yoneda.map φ = e.inv ≫ i.hom ≫ f' := Functor.map_preimage _ _
  have hkφ : k ≫ φ = j ≫ ψ := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, hk, hφ, ← hf', Category.assoc,
      Iso.hom_inv_id_assoc, ← Category.assoc, hW.w, Category.assoc])
  -- `G ⊂ Spec A'` is a thickening of affine schemes.
  have hψapp : ∀ x, ((BigFppfOver.toScheme B S hS).map ψ).appTop x =
      ((Scheme.ΓSpecIso (CommRingCat.of (chartEqualizer ((BigFppfOver.toScheme B S hS).map q₁)
        ((BigFppfOver.toScheme B S hS).map q₂)))).hom x).1 :=
    fun x ↦ (congrArg (fun g ↦ g.appTop x) hFψ).trans (toChartEqualizer_appTop _ _ x)
  have happ : ∀ t, ((BigFppfOver.toScheme B S hS).map k).appTop
      (((BigFppfOver.toScheme B S hS).map φ).appTop t) =
      ((BigFppfOver.toScheme B S hS).map j).appTop
        (((BigFppfOver.toScheme B S hS).map ψ).appTop t) := by
    intro t
    have h := congrArg (fun g ↦ ((BigFppfOver.toScheme B S hS).map g).appTop t) hkφ
    simpa only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h
  have hinjk : Function.Injective ((BigFppfOver.toScheme B S hS).map k).appTop :=
    gamma_injective_of_etale_surjection B S hS k hks hke
  have hinjψ : Function.Injective ((BigFppfOver.toScheme B S hS).map ψ).appTop := by
    intro x y hxy
    rw [hψapp, hψapp] at hxy
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).1 (Subtype.ext hxy)
  have hsurjφ : Function.Surjective ((BigFppfOver.toScheme B S hS).map φ).appTop := by
    intro z
    obtain ⟨y, hy₁, hy₂⟩ := exists_appTop_eq_of_isThickeningHom_chart i hi e w' hw'e hw's q₁ q₂
      hR' j η hW hJ k hk z
    let w := (Scheme.ΓSpecIso (CommRingCat.of (chartEqualizer
      ((BigFppfOver.toScheme B S hS).map q₁) ((BigFppfOver.toScheme B S hS).map q₂)))).inv
        ⟨y, mem_chartEqualizer.2 hy₁⟩
    refine ⟨w, hinjk ((happ w).trans ?_)⟩
    refine Eq.trans (congrArg _ ((hψapp w).trans ?_)) hy₂
    simp [w]
  have hnilφ :
      ∀ x ∈ RingHom.ker ((BigFppfOver.toScheme B S hS).map φ).appTop.hom, IsNilpotent x := by
    intro x hx
    have h₁ : ((BigFppfOver.toScheme B S hS).map j).appTop
        (((BigFppfOver.toScheme B S hS).map ψ).appTop x) = 0 := by
      rw [← happ, RingHom.mem_ker.1 hx, map_zero]
    obtain ⟨n, hn⟩ := hJ
    have h₂ : ((BigFppfOver.toScheme B S hS).map ψ).appTop x ^ n = 0 := by
      have : ((BigFppfOver.toScheme B S hS).map ψ).appTop x ^ n ∈
          RingHom.ker ((BigFppfOver.toScheme B S hS).map j).appTop.hom ^ n :=
        Ideal.pow_mem_pow h₁ n
      rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact ⟨n, hinjψ (by rw [map_pow, h₂, map_zero])⟩
  have hφthick : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map φ) := by
    have hspec := Deformation.Artin.SectionsSheaf.isThickening_specMap_of_surjective
      ((BigFppfOver.toScheme B S hS).map φ).appTop.hom hsurjφ hnilφ
    refine ⟨IsClosedImmersion.of_surjective_of_isAffine _ hsurjφ, ?_⟩
    have : Surjective (Spec.map ((BigFppfOver.toScheme B S hS).map φ).appTop) := ⟨hspec.2⟩
    exact ((MorphismProperty.arrow_mk_iso_iff @Surjective
      (arrowIsoSpecΓOfIsAffine ((BigFppfOver.toScheme B S hS).map φ))).2 this).1
  -- Lift the étale chart `U ⟶ G` across the thickening `G ⊂ Spec A'` (Stacks 039R).
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map φ) :=
    hφthick.1
  obtain ⟨V, q, p₀, hqE, hqEt, hsite, hpres⟩ := exists_etaleLift_isPullback_of_chart B S hS
    (g := yoneda.map φ) φ hφthick.2 (𝟙 _) (𝟙 _) (isEtale_of_isIso B S hS _)
    (IsPullback.id_vert _) k hke
  have hsiteF := hsite.map (BigFppfOver.toScheme B S hS)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
    Stacks.Thickenings.isAffine_of_isThickening
      (Stacks.Thickenings.isThickening_of_isPullback hsiteF hφthick)
  have hqs : Surjective ((BigFppfOver.toScheme B S hS).map q) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨t, rfl⟩ := hφthick.2 y
    obtain ⟨w, rfl⟩ := hks.surj t
    refine ⟨((BigFppfOver.toScheme B S hS).map p₀).base w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsiteF.w]
  -- The fibre product `P = X ×_{Spec A'} V`.
  let P := pullback f' (yoneda.map q)
  have hP : IsPullback (pullback.fst f' (yoneda.map q)) (pullback.snd f' (yoneda.map q)) f'
      (yoneda.map q) := IsPullback.of_hasPullback _ _
  have hPalg : IsAlgebraicSpace B S hS P :=
    isAlgebraicSpace_pullback B S hS f' (yoneda.map q) X.property
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS T')
  have hqEtale : IsEtale B S hS (yoneda.map q) := by simpa using hqEt
  have hfst : IsEtale B S hS (pullback.fst f' (yoneda.map q)) := by
    let PA : AlgebraicSpaces B S hS := ⟨P, hPalg⟩
    let VA : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
    let TA : AlgebraicSpaces B S hS := ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩
    exact isEtale_of_isPullback B S hS (X' := PA) (X := VA) (Z := X) (Y := TA)
      (ObjectProperty.homMk (pullback.snd _ _)) (ObjectProperty.homMk (pullback.fst _ _))
      (ObjectProperty.homMk (yoneda.map q)) (ObjectProperty.homMk f')
      (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hP.flip) hqEtale
  have hcomp : (η ≫ i.hom) ≫ f' = yoneda.map p₀ ≫ yoneda.map q := by
    rw [← Functor.map_comp, hsite.w, Functor.map_comp, hφ, hk]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  let b : yoneda.obj W ⟶ P := hP.lift _ _ hcomp
  have hb : IsPullback η b i.hom (pullback.fst f' (yoneda.map q)) := by
    refine (IsPullback.of_right ?_ (hP.lift_fst _ _ hcomp) hP.flip).flip
    rw [hP.lift_snd]
    have h' : IsPullback (yoneda.map p₀) (yoneda.map k) (yoneda.map q) (yoneda.map φ) := by
      simpa using hpres
    rw [hk, hφ] at h'
    exact h'.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp)
  have hPaff : IsAffineSpace B S hS P :=
    isAffineSpace_of_isPullback_of_isThickeningHom B S hS i hi hPalg
      (pullback.fst f' (yoneda.map q)) hfst w'
      ((isEtale_iff_presheaf_of_yoneda B S hS w').2 hw'e) η j hW b hb
  -- Descent along the fpqc covering `V ⟶ Spec A'`.
  have hqflat : Flat ((BigFppfOver.toScheme B S hS).map q) := inferInstance
  have hqaff : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map q) :=
    inferInstance
  exact isAffineSpace_of_isAffineSpace_pullback_of_fpqcSingleton B S hS hZ X.property
    (WA := ⟨T', inferInstance⟩) (WB := ⟨V, inferInstance⟩) f' q hqaff hqflat hqs hP hPaff

set_option synthInstance.maxHeartbeats 400000 in
/-- **A thickening of an affine algebraic space with a nilpotent affine chart is affine.** Let
`i : G ⟶ X` be a thickening of algebraic spaces over `S` with `G` affine, let `w' : U' ⟶ X` be a
surjective étale chart from an affine object of the site, and suppose the base change
`j : U ⟶ U'` of `i` along `w'` has nilpotent kernel on global sections. Then `X` is affine.

This is `isAffineSpace_of_isThickeningHom_of_isNilpotent_chart_of_isTerminal` read over the
terminal scheme along the lower-shriek extension of Stacks 03I5, which preserves and reflects
affineness, thickenings and charts. -/
theorem C1573.isAffineSpace_of_isThickeningHom_of_isNilpotent_chart
    {X G : AlgebraicSpaces B S hS} (i : G ⟶ X)
    (hi : IsThickeningHom B S hS i) (hG : IsAffineSpace B S hS G.1)
    {W' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W')]
    (w' : yoneda.obj W' ⟶ X.1)
    (hw'e : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w')
    (hw's : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w')
    {W : BigFppfOver B S hS} (j : W ⟶ W') (η : yoneda.obj W ⟶ G.1)
    (hW : IsPullback η (yoneda.map j) i.hom w')
    (hJ : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map j).appTop.hom)) :
    IsAffineSpace B S hS X.1 := by
  have hZ := B.contains_terminal
  let h : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let Λ := OverShriek.relocalizePresheafFunctor h
  let X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ :=
    ⟨Λ.obj X.1, isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ h X.1 X.property⟩
  let G₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ :=
    ⟨Λ.obj G.1, isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ h G.1 G.property⟩
  let i₀ : G₀ ⟶ X₀ := ObjectProperty.homMk (Λ.map i.hom)
  have hi₀ : IsThickeningHom B (⊤_ Scheme.{u}) hZ i₀ := by
    rw [isThickeningHom_iff_isClosedImmersion_and_isSurjective] at hi ⊢
    exact ⟨isClosedImmersion_relocalize B S hS hZ h hi.1,
      isSurjective_relocalize B S hS (⊤_ Scheme.{u}) hZ h i.hom hi.2⟩
  have hPre : PreservesLimitsOfShape WalkingCospan Λ :=
    relocalizePresheaf_preservesConnectedLimits h
  have hW₀ : IsPullback (relocalizeChart B S (⊤_ Scheme.{u}) hS hZ h η)
      (yoneda.map ((Over.map h).map j)) i₀.hom (relocalizeChart B S (⊤_ Scheme.{u}) hS hZ h w') :=
    (hW.map Λ).of_iso (relocalizedYonedaIso B (B.obj hS) (B.obj hZ) h W) (Iso.refl _)
      (relocalizedYonedaIso B (B.obj hS) (B.obj hZ) h W') (Iso.refl _)
      (by simp [relocalizeChart, Λ])
      (relocalizedYonedaIso_naturality B (B.obj hS) (B.obj hZ) h j) (by simp; rfl)
      (by simp [relocalizeChart, Λ])
  have : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj ((Over.map h).obj W')) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj W'))
  have hX₀ := isAffineSpace_of_isThickeningHom_of_isNilpotent_chart_of_isTerminal B
    (⊤_ Scheme.{u}) hZ terminalIsTerminal i₀ hi₀
    (isAffineSpace_relocalize B S (⊤_ Scheme.{u}) hS hZ h hG)
    (relocalizeChart B S (⊤_ Scheme.{u}) hS hZ h w')
    ((presheaf_relocalizeChart_iff B S (⊤_ Scheme.{u}) hS hZ h _ w').2 hw'e)
    ((presheaf_relocalizeChart_iff B S (⊤_ Scheme.{u}) hS hZ h _ w').2 hw's)
    ((Over.map h).map j) (relocalizeChart B S (⊤_ Scheme.{u}) hS hZ h η) hW₀ hJ
  exact isAffineSpace_of_isAffineSpace_relocalize B S (⊤_ Scheme.{u}) hS hZ h hX₀

end AlgebraicGeometry.Space

end
