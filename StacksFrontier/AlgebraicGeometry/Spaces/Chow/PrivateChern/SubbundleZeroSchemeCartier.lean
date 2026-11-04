module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SubbundleZeroSchemeIso
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleZeroScheme
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionIntTensorPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem

/-!
# `Z(σ) ≅ 𝐏(ℱ)` is a relative effective Cartier divisor of `𝐏(ℰ)` over `X`

Let `0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` be short exact on an algebraic space `X`, with `ℒ` invertible and `ℰ`,
`ℱ` finite locally free, and `Z(σ) ⊆ 𝐏(ℰ)` the zero scheme of the section of
`𝒪(1) ⊗ π^*ℒ^{-1}` attached to `π^*ℒ ⟶ π^*ℰ ⟶ 𝒪(1)`. Then `Z(σ)` is an effective Cartier
divisor of `𝐏(ℰ)` flat over `X`. On the presenting chart `𝐏(ℰ_U)` its inverse image is the
closed subscheme `𝐏(ℱ_U)` (`AlgebraicGeometry.Space.PrivateChern.preimage_subbundleZeroScheme`),
which is an effective Cartier divisor by the computation on schemes
(`Stacks.Chow.GenuineChern.zeroScheme_bundleSection_eq_ker_bundleEmbedding`); so `Z(σ)` is an
effective Cartier divisor by Stacks 083C. It is flat over `X` since it is isomorphic to `𝐏(ℱ)`
over `X` (`AlgebraicGeometry.Space.PrivateChern.exists_iso_subbundleZeroScheme`).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.isRelativeEffectiveCartierDivisor_subbundleZeroScheme`:
  `Z(σ)` is a relative effective Cartier divisor over `X`.
* `AlgebraicGeometry.Space.PrivateChern.isEffectiveCartierDivisor_subbundleZeroScheme`.
* `AlgebraicGeometry.Space.PrivateChern.preimage_subbundleZeroScheme`: the inverse image of
  `Z(σ)` on the presenting chart.
* `Stacks.Divisors.isEffectiveCartierDivisor_map_of_isIso`: the image of an effective Cartier
  divisor under an isomorphism of schemes is one.

## References

* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- The image of an ideal sheaf under an isomorphism is its inverse image under the inverse. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_eq_comap_inv {X Y : Scheme.{u}}
    (I : X.IdealSheafData) (g : X ⟶ Y) [IsIso g] : I.map g = I.comap (inv g) := by
  have hfst : pullback.fst (inv g) I.subschemeι =
      pullback.snd (inv g) I.subschemeι ≫ I.subschemeι ≫ g := by
    rw [← pullback.condition_assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Scheme.IdealSheafData.comap, hfst, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp,
    Scheme.IdealSheafData.ker_subschemeι]

/-- **The image of an effective Cartier divisor under an isomorphism of schemes is an effective
Cartier divisor.** -/
theorem isEffectiveCartierDivisor_map_of_isIso {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (g : X ⟶ Y) [IsIso g] :
    IsEffectiveCartierDivisor (I.map g) := by
  rw [Scheme.IdealSheafData.map_eq_comap_inv]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion I hI (inv g)

/-- The kernel of a morphism composed on both sides with isomorphisms is an effective Cartier
divisor when the kernel of the morphism is. -/
theorem isEffectiveCartierDivisor_ker_comp_comp {X' X Y Y' : Scheme.{u}} (a : X' ⟶ X) [IsIso a]
    (f : X ⟶ Y) (b : Y ⟶ Y') [IsIso b] (hf : IsEffectiveCartierDivisor f.ker) :
    IsEffectiveCartierDivisor (a ≫ f ≫ b).ker := by
  rw [Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp]
  exact isEffectiveCartierDivisor_map_of_isIso _ hf b

/-- `Stacks.Divisors.isEffectiveCartierDivisor_ker_comp_comp` for a morphism given up to
equality. -/
theorem isEffectiveCartierDivisor_ker_of_eq_comp_comp {X' X Y Y' : Scheme.{u}} {g : X' ⟶ Y'}
    (a : X' ⟶ X) [IsIso a] (f : X ⟶ Y) (b : Y ⟶ Y') [IsIso b] (hg : g = a ≫ f ≫ b)
    (hf : IsEffectiveCartierDivisor f.ker) : IsEffectiveCartierDivisor g.ker := by
  subst hg
  exact isEffectiveCartierDivisor_ker_comp_comp a f b hf

/-- A closed immersion composed on both sides with isomorphisms is a closed immersion. -/
theorem isClosedImmersion_comp_comp {X' X Y Y' : Scheme.{u}} (a : X' ⟶ X) [IsIso a]
    (f : X ⟶ Y) [IsClosedImmersion f] (b : Y ⟶ Y') [IsIso b] :
    IsClosedImmersion (a ≫ f ≫ b) :=
  inferInstance

end Stacks.Divisors

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {E F L : Modules.{u, u} B S hS X.1 X.2}
  [hE : E.IsQuasicoherentOnSite] [hF : F.IsQuasicoherentOnSite]
  (hfreeE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfreeF : SheafOfModules.IsFiniteLocallyFreeOnSite F) (q : E ⟶ F)
  (hq : ∀ V : SmallEtale B S hS X.1, Epi (chartModuleMap q V)) (i : L ⟶ E)
  (hL : IsInvertibleModule X L)

include hL in
/-- **The reading of an invertible module on an étale chart is invertible.** -/
theorem isInvertible_schemeReading_chartToSpace (_hLq : L.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible (chartScheme V).sheaf.obj
      (chartScheme V).ringCatSheaf.property (schemeReading L (chartToSpace B S hS X V)) := by
  have := hL
  have h1 : Stacks.Ample.IsInvertibleModule (chartScheme V)
      (chartRestrictionSchemeModule B S hS X L V) := inferInstance
  have e : chartRestrictionSchemeModule B S hS X L V ≅
      schemeReading L (chartToSpace B S hS X V) :=
    eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2 L V) ≪≫
      (schemeReadingChartIso L V).symm
  have h2 : Stacks.Ample.IsInvertibleModule (chartScheme V)
      (schemeReading L (chartToSpace B S hS X V)) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ h2

/-- The closed immersion of chart bundles over the presenting chart is a closed immersion of
schemes. -/
instance isClosedImmersion_siteSchemeHom_chartEmbedding :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (siteSchemeHom (chartEmbedding hfreeE hfreeF q hq)) := by
  have := isFiniteLocallyFree_chartBundleModule E hfreeE (bundleBaseChart X)
  have := isFiniteLocallyFree_chartBundleModule F hfreeF (bundleBaseChart X)
  have := hq (bundleBaseChart X)
  exact @Stacks.Divisors.isClosedImmersion_comp_comp _ _ _ _ _ (Iso.isIso_inv _) _
    (Stacks.Chow.GenuineChern.isClosedImmersion_bundleEmbedding _) _ (Iso.isIso_hom _)

include hE hF hL in
/-- **The closed subscheme `𝐏(ℱ_U) ⊆ 𝐏(ℰ_U)` of the presenting chart is an effective Cartier
divisor**: it is the zero scheme of the section of `𝒪(1) ⊗ π^*ℒ_U^{-1}` attached to
`π^*ℒ_U ⟶ π^*ℰ_U ⟶ 𝒪(1)` (Stacks 0ES8, on schemes). -/
theorem isEffectiveCartierDivisor_ker_siteSchemeHom_chartEmbedding (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (siteSchemeHom (chartEmbedding hfreeE hfreeF q hq)).ker := by
  have := isFiniteLocallyFree_chartBundleModule E hfreeE (bundleBaseChart X)
  have := isFiniteLocallyFree_chartBundleModule F hfreeF (bundleBaseChart X)
  have := hq (bundleBaseChart X)
  have := isInvertible_schemeReading_chartToSpace hL hLq (bundleBaseChart X)
  have hSch := shortExact_moduleReadingMap q i hiq hC hLq
    (chartToSpace B S hS X (bundleBaseChart X)) (isEtale_chartToSpace B S hS X (bundleBaseChart X))
  obtain ⟨hker, hD⟩ :=
    Stacks.Chow.GenuineChern.zeroScheme_bundleSection_eq_ker_bundleEmbedding _ hSch
  rw [hker] at hD
  have hbe : Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Chow.GenuineChern.bundleEmbedding (chartModuleMap q (bundleBaseChart X))).ker :=
    @Stacks.Divisors.isEffectiveCartierDivisor_of_eq _ _ _ rfl hD
  exact @Stacks.Divisors.isEffectiveCartierDivisor_ker_of_eq_comp_comp _ _ _ _ _
    (Stacks.RelativeProj.bundlePresentationIso (chartBundleModule F (bundleBaseChart X))).inv
    (Iso.isIso_inv _) _ (Stacks.RelativeProj.bundlePresentationIso
      (chartBundleModule E (bundleBaseChart X))).hom (Iso.isIso_hom _) rfl hbe

section Chart

attribute [-instance] CategoryTheory.catToReflQuiver

/-- The Yoneda image of a morphism acts by postcomposition. -/
theorem yoneda_map_app_apply_eq {T U' U : BigFppfOver B S hS} (j : U' ⟶ U) (x' : T ⟶ U') :
    (yoneda.map j).app (op T) x' = x' ≫ j :=
  rfl

/-- **A subfunctor of `P` pulled back along `u : h_U ⟶ P` is the range of `h_j` for
`j : V ⟶ U`** as soon as a point of `U` lies in it exactly when it factors through `j`. -/
theorem preimage_eq_range_yoneda_map {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor P)
    {U V : BigFppfOver B S hS} (u : yoneda.obj U ⟶ P) (j : V ⟶ U)
    (h₁ : ∀ (T : BigFppfOver B S hS) (x : T ⟶ U), u.app (op T) x ∈ Z.obj (op T) →
      ∃ x' : T ⟶ V, x' ≫ j = x)
    (h₂ : ∀ (T : BigFppfOver B S hS) (x' : T ⟶ V), u.app (op T) (x' ≫ j) ∈ Z.obj (op T)) :
    Z.preimage u = Subfunctor.range (yoneda.map j) := by
  ext ⟨T⟩ x
  rw [Subfunctor.range_obj]
  constructor
  · intro hx
    obtain ⟨x', hx'⟩ := h₁ T x hx
    exact ⟨x', hx'⟩
  · rintro ⟨x', rfl⟩
    exact h₂ T x'

include hE hF in
/-- **The inverse image of `Z(σ)` on the presenting chart `𝐏(ℰ_U)` is `𝐏(ℱ_U)`.** -/
theorem preimage_subbundleZeroScheme (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite) :
    (subbundleZeroScheme hfreeE i hL).1.preimage
        (projectiveBundleChartPresentation E hfreeE).toSpace =
      Subfunctor.range (yoneda.map (chartEmbedding hfreeE hfreeF q hq)) := by
  obtain ⟨e, he⟩ := exists_iso_subbundleZeroScheme hfreeE hfreeF q hq i hL hiq hC hLq
  have hhom : e.hom.hom ≫ (subbundleZeroScheme hfreeE i hL).1.ι =
      (projectiveBundleEmbedding hfreeE hfreeF q hq).hom := congrArg (fun m => m.hom) he
  have hatlas := toSpace_comp_projectiveBundleEmbedding hfreeE hfreeF q hq
  refine preimage_eq_range_yoneda_map _ _ _ (fun T x hx => ?_) (fun T x' => ?_)
  · exact exists_comp_chartEmbedding_eq_of_modulePullback_map_eq_zero (hfreeE := hfreeE)
      (hfreeF := hfreeF) (q := q) (hq := hq) (i := i) (hiq := hiq) (hC := hC) (hLq := hLq)
      (x := x) (modulePullback_map_subbundleMorphism_eq_zero_of_mem hfreeE i hL x hx)
  · have k : (projectiveBundleChartPresentation E hfreeE).toSpace.app (op T)
        ((yoneda.map (chartEmbedding hfreeE hfreeF q hq)).app (op T) x') =
        (subbundleZeroScheme hfreeE i hL).1.ι.app (op T) (e.hom.hom.app (op T)
          ((projectiveBundleChartPresentation F hfreeF).toSpace.app (op T) x')) := by
      rw [← NatTrans.comp_app_apply, ← hatlas, NatTrans.comp_app_apply, ← hhom,
        NatTrans.comp_app_apply]
    rw [← yoneda_map_app_apply_eq, k]
    exact (e.hom.hom.app (op T) _).2

end Chart

include hF hfreeF hq in
/-- **`Z(σ)` is an effective Cartier divisor of `𝐏(ℰ)`** (Stacks 083C): its inverse image on
the presenting chart is the effective Cartier divisor `𝐏(ℱ_U) ⊆ 𝐏(ℰ_U)`. -/
theorem isEffectiveCartierDivisor_subbundleZeroScheme (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite) :
    IsEffectiveCartierDivisor B S hS (projectiveBundle E hfreeE)
      (subbundleZeroScheme hfreeE i hL) :=
  isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover B S hS _ _
    ⟨_, (projectiveBundleChartPresentation E hfreeE).toSpace,
      presentationAtlas_isEtale (projectiveBundleChartPresentation E hfreeE),
      surjective_pointsMap_projectiveBundleAtlas E hfreeE,
      (siteSchemeHom (chartEmbedding hfreeE hfreeF q hq)).ker, _, chartEmbedding hfreeE hfreeF q hq,
      asIso (siteSchemeHom (chartEmbedding hfreeE hfreeF q hq)).toImage,
      isEffectiveCartierDivisor_ker_siteSchemeHom_chartEmbedding hfreeE hfreeF q hq i hL hiq hC hLq,
      (Scheme.Hom.toImage_imageι _).symm,
      preimage_subbundleZeroScheme hfreeE hfreeF q hq i hL hiq hC hLq⟩

include hF hfreeF hq in
/-- **`Z(σ)` is a relative effective Cartier divisor of `𝐏(ℰ)` over `X`**: it is an effective
Cartier divisor, and it is flat over `X` since it is isomorphic to `𝐏(ℱ)` over `X`. -/
theorem isRelativeEffectiveCartierDivisor_subbundleZeroScheme (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite) (n : ℕ)
    (hrF : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) F (n + 1)) :
    IsRelativeEffectiveCartierDivisor B S hS (projectiveBundleProj E hfreeE)
      (subbundleZeroScheme hfreeE i hL) := by
  refine ⟨isEffectiveCartierDivisor_subbundleZeroScheme hfreeE hfreeF q hq i hL hiq hC hLq, ?_⟩
  obtain ⟨e, he⟩ := exists_iso_subbundleZeroScheme hfreeE hfreeF q hq i hL hiq hC hLq
  have h1 : e.inv ≫ projectiveBundleEmbedding hfreeE hfreeF q hq =
      ObjectProperty.homMk (subbundleZeroScheme hfreeE i hL).1.ι := by
    rw [← he, Iso.inv_hom_id_assoc]
  have h2 : ObjectProperty.homMk (subbundleZeroScheme hfreeE i hL).1.ι ≫
      projectiveBundleProj E hfreeE = e.inv ≫ projectiveBundleProj F hfreeF := by
    rw [← h1, Category.assoc, projectiveBundleEmbedding_comp_proj]
  have hι : (subbundleZeroScheme hfreeE i hL).1.ι ≫ (projectiveBundleProj E hfreeE).hom =
      e.inv.hom ≫ (projectiveBundleProj F hfreeF).hom := congrArg (fun m => m.hom) h2
  rw [hι]
  have : IsIso e.inv.hom := (ObjectProperty.ι _).map_isIso e.inv
  exact isFlat_comp B S hS (subbundleZeroScheme hfreeE i hL).2.1 (projectiveBundle F hfreeF).2 X.2
    _ _ (isFlat_of_isIso _ (projectiveBundle F hfreeF).2)
    (isFlat_projectiveBundleProj F n hrF hfreeF)

end AlgebraicGeometry.Space.PrivateChern

end
