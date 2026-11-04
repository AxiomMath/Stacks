module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.SetSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# Direct image along an integral universally injective morphism

Let `f : X ⟶ Y` be an integral and universally injective morphism of schemes. Then `f` factors
through its scheme-theoretic image as a universal homeomorphism followed by a closed immersion,
and the two factors contribute in complementary ways to the direct image on the small étale
sites: base change along a universal homeomorphism is a dense subsite, so direct image along it
is an equivalence, while direct image along a closed immersion is fully faithful with the
essential image computed in the closed-immersion development. Consequently
`f_{small, *}` is fully faithful on sheaves of sets and on abelian sheaves, with essential image
the sheaves that are trivial away from `f(X)`, and `f_{small}^{-1}` is a left inverse to it.

## Main definitions

* `Stacks.EtaleCohomology.openComplementRange` — the open complement of the image of a
  universally closed morphism.
* `Stacks.EtaleCohomology.AbelianEssImageClosedImmersion` — the abelian essential image
  description for a closed immersion, carried as a hypothesis; see below.

## Main results

* `Stacks.EtaleCohomology.universalHomeomorphism_toImage` — the first factor of the
  scheme-theoretic image factorization of an integral universally injective morphism is a
  universal homeomorphism.
* `Stacks.EtaleCohomology.smallEtalePushforwardFullyFaithful_of_integral_universallyInjective`
  and `Stacks.EtaleCohomology.smallEtalePushforwardAbFullyFaithful_of_integral_universallyInjective`
  — full faithfulness of the direct image on sheaves of sets and on abelian sheaves.
* `Stacks.EtaleCohomology.smallEtalePushforward_essImage_iff_of_integral_universallyInjective`
  and
  `Stacks.EtaleCohomology.smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective`
  — the two descriptions of the essential image.
* `Stacks.EtaleCohomology.smallEtalePushforwardCompInverseImageIso_of_integral_universallyInjective`
  and
  `Stacks.EtaleCohomology.smallEtalePushforwardAbCompPullbackIso_of_integral_universallyInjective`
  — in both cases the inverse image is a left inverse to the direct image.

## Implementation notes

The factorization is Mathlib's `AlgebraicGeometry.Scheme.Hom.toImage` followed by
`AlgebraicGeometry.Scheme.Hom.imageι`. Integrality of the first factor is cancellation of
integrality against the separated second factor; universal injectivity of the first factor is
cancellation in the characterization of universal injectivity by injectivity on field-valued
points; surjectivity holds because the first factor is dominant and, being integral, closed.

Both essential image descriptions are the condition on the restriction of the sheaf to the open
complement of `f(X)`: for sheaves of sets that the restriction is the singleton sheaf, for
abelian sheaves that it vanishes. The abelian condition is the source's "support contained in
`f(X)`" rewritten as the vanishing of the restriction away from `f(X)`; the two agree because
the support is the set of points with nonvanishing stalk and the stalks of a restriction to an
open are the stalks at the points of that open.

## No unconditional abelian essential image

The abelian essential image is carried with one hypothesis,
`Stacks.EtaleCohomology.AbelianEssImageClosedImmersion`: the same description of the essential
image for a *closed immersion*, which is Stacks 04CA part (2). What is proved here is the
reduction of the integral universally injective case to the closed immersion case, which is the
content of the source's proof. The hypothesis is not available in the site of this development:
Stacks 04CA part (2) is carried by
`AlgebraicGeometry.smallEtalePushforward_essImage_iff_abelian` in the module
`ClosedImmersionsPushforward.AbelianSheafEssentialImage` of this development,
line 449, where it is stated for the small étale site
`AlgebraicGeometry.SmallEtale.topology` of a chosen big étale site and phrased with
`AlgebraicGeometry.SmallEtale.supportSheaf`, whereas the present module and Stacks 04CA part (1)
(`Stacks.EtaleCohomology.smallEtalePushforward_essImage_iff`,
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.SetSheafEssentialImage`,
line 484) use Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`. The two sheaf categories
are equivalent by `AlgebraicGeometry.SmallEtale.sheafEquiv`, but that equivalence has not been
shown to carry one direct image comparison to the other. Everything else in this module is
unconditional.

## References

* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04FZ](https://stacks.math.columbia.edu/tag/04FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-! ### The scheme-theoretic image factorization -/

/-- An integral universally injective morphism maps onto its scheme-theoretic image by a
universal homeomorphism: it is integral and universally injective by cancellation against the
closed immersion of the image, and surjective because it is dominant with closed range. -/
public theorem universalHomeomorphism_toImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] : UniversalHomeomorphism f.toImage := by
  have : IsIntegralHom (f.toImage ≫ f.imageι) := by
    simpa using (inferInstance : IsIntegralHom f)
  have : IsIntegralHom f.toImage := IsIntegralHom.of_comp f.toImage f.imageι
  have : UniversallyInjective f.toImage := by
    apply ((tfae_universallyInjective f.toImage).out 1 2).mpr
    intro K _ a b hab
    have h : ∀ (L : Type u) [Field L],
        Function.Injective (fun g : Spec (.of L) ⟶ X => g ≫ f) :=
      ((tfae_universallyInjective f).out 1 2).mp (inferInstance : UniversallyInjective f)
    apply h K
    simpa using congrArg (fun k => k ≫ f.imageι) hab
  have : Surjective f.toImage := ⟨by
    rw [← Set.range_eq_univ, ← f.toImage.isClosedMap.isClosed_range.closure_eq]
    exact f.toImage.denseRange.closure_eq⟩
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective _).2
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- The open complement of the image of a universally closed morphism; the image is closed
because a universally closed morphism is a closed map. -/
public def openComplementRange {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f] : Y.Opens :=
  ⟨(Set.range f.base)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩

/-- An integral universally injective morphism and the closed immersion of its scheme-theoretic
image have the same image, because the first factor of the factorization is surjective. -/
public theorem openComplement_imageι {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] :
    openComplement f.imageι = openComplementRange f := by
  have := universalHomeomorphism_toImage f
  have hsurj : Surjective f.toImage :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective
      f.toImage).1 inferInstance).2.2
  apply TopologicalSpace.Opens.ext
  show (Set.range f.imageι.base)ᶜ = (Set.range f.base)ᶜ
  congr 1
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := f.toImage.surjective z
    exact ⟨x, (congrArg (fun k : X ⟶ Y => k x) f.toImage_imageι).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨f.toImage x, ?_⟩
    show (f.toImage ≫ f.imageι) x = f x
    rw [f.toImage_imageι]

/-- If `G ⋙ H ≅ K` with `G` essentially surjective, then `K` and `H` have the same essential
image. -/
private theorem essImage_iff_of_comp_iso {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (G : C ⥤ D) (H : D ⥤ E) (K : C ⥤ E) [G.EssSurj] (e : G ⋙ H ≅ K) (F : E) :
    K.essImage F ↔ H.essImage F :=
  ⟨fun h => Functor.essImage_comp_apply_of_essSurj.mp (Functor.essImage.ofNatIso e.symm h),
    fun h => Functor.essImage.ofNatIso e (Functor.essImage_comp_apply_of_essSurj.mpr h)⟩

/-! ### Sheaves of sets -/

section SetSheaves

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f]

/-- The factorization of the direct image of sheaves of sets through the small étale site of the
scheme-theoretic image. -/
public def smallEtalePushforwardImageFactorIso :
    (smallEtaleBaseChange f.toImage).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology f.image) (smallEtaleTopology X) ⋙
      (smallEtaleBaseChange f.imageι).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology f.image) ≅
      (smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X) :=
  smallEtalePushforwardCompIso.{u, v} f.toImage f.imageι ≪≫
    eqToIso (congrArg (fun g : X ⟶ Y =>
      (smallEtaleBaseChange g).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X)) f.toImage_imageι)

/-- **Stacks 04FZ, part (1).** Direct image of sheaves of sets along an integral universally
injective morphism is fully faithful. -/
@[stacks 04FZ "part (1): fully faithful"]
public def smallEtalePushforwardFullyFaithful_of_integral_universallyInjective :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
      (smallEtaleTopology Y) (smallEtaleTopology X)).FullyFaithful := by
  have := universalHomeomorphism_toImage f
  have := isDenseSubsite_of_universalHomeomorphism f.toImage
  have := (smallEtalePushforwardFullyFaithful.{u, v} f.imageι).full
  have := (smallEtalePushforwardFullyFaithful.{u, v} f.imageι).faithful
  have := Functor.Full.of_iso (smallEtalePushforwardImageFactorIso.{u, v} f)
  have := Functor.Faithful.of_iso (smallEtalePushforwardImageFactorIso.{u, v} f)
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- **Stacks 04FZ, part (1).** A sheaf of sets on `Y_étale` lies in the essential image of direct
image along an integral universally injective morphism exactly when its restriction to the open
complement of `f(X)` is the singleton sheaf. -/
@[stacks 04FZ "part (1): essential image"]
public theorem smallEtalePushforward_essImage_iff_of_integral_universallyInjective
    (F : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X)).essImage F ↔
      Nonempty (IsTerminal
        ((smallEtaleInverseImage.{u, v} (openComplementRange f).ι).obj F)) := by
  have := universalHomeomorphism_toImage f
  have := isDenseSubsite_of_universalHomeomorphism f.toImage
  rw [essImage_iff_of_comp_iso _ _ _ (smallEtalePushforwardImageFactorIso.{u, v} f),
    smallEtalePushforward_essImage_iff.{u, v} f.imageι F, openComplement_imageι f]

/-- **Stacks 04FZ, trailing clause.** Inverse image along an integral universally injective
morphism is a left inverse to direct image on sheaves of sets. -/
@[stacks 04FZ "trailing clause for sheaves of sets: left inverse"]
public def smallEtalePushforwardCompInverseImageIso_of_integral_universallyInjective :
    (smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X) ⋙
      smallEtaleInverseImage.{u, v} f ≅
      𝟭 (Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) :=
  letI := (smallEtalePushforwardFullyFaithful_of_integral_universallyInjective.{u, v} f).full
  letI := (smallEtalePushforwardFullyFaithful_of_integral_universallyInjective.{u, v} f).faithful
  asIso (smallEtaleInverseImageAdjunction.{u, v} f).counit

end SetSheaves

/-! ### Abelian sheaves -/

/-- **Stacks 04CA, part (2)** for the small étale sites of this development: an abelian sheaf on
`W_étale` is a direct image along a closed immersion `j` exactly when its restriction to an open
subscheme `U` complementary to the image of `j` vanishes. -/
public def AbelianEssImageClosedImmersion : Prop :=
  ∀ {Z W : Scheme.{u}} (j : Z ⟶ W) [IsClosedImmersion j] (U : W.Opens)
    (_ : (U : Set W) = (Set.range j.base)ᶜ) (G : Sheaf (smallEtaleTopology W) Ab.{u + 1}),
      (smallEtalePushforwardAb j).essImage G ↔
        IsZero (((smallEtaleBaseChange U.ι).sheafPullback Ab.{u + 1}
          (smallEtaleTopology W) (smallEtaleTopology U.toScheme)).obj G)

section AbelianSheaves

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f]

/-- The factorization of the direct image of abelian sheaves through the small étale site of the
scheme-theoretic image. -/
public def smallEtalePushforwardAbImageFactorIso :
    smallEtalePushforwardAb f.toImage ⋙ smallEtalePushforwardAb f.imageι ≅
      smallEtalePushforwardAb f :=
  smallEtalePushforwardAbCompIso f.toImage f.imageι ≪≫
    eqToIso (congrArg (fun g : X ⟶ Y => smallEtalePushforwardAb g) f.toImage_imageι)

/-- **Stacks 04FZ, part (2).** Direct image of abelian sheaves along an integral universally
injective morphism is fully faithful. -/
@[stacks 04FZ "part (2): fully faithful"]
public def smallEtalePushforwardAbFullyFaithful_of_integral_universallyInjective :
    (smallEtalePushforwardAb f).FullyFaithful := by
  have := universalHomeomorphism_toImage f
  have := isDenseSubsite_of_universalHomeomorphism f.toImage
  have hI : (smallEtalePushforwardAb f.imageι).Full :=
    inferInstanceAs (((smallEtaleBaseChange f.imageι).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology Y) (smallEtaleTopology f.image)).Full)
  have hI' : (smallEtalePushforwardAb f.imageι).Faithful :=
    inferInstanceAs (((smallEtaleBaseChange f.imageι).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology Y) (smallEtaleTopology f.image)).Faithful)
  have hH : (smallEtalePushforwardAb f.toImage).IsEquivalence :=
    inferInstanceAs (((smallEtaleBaseChange f.toImage).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology f.image) (smallEtaleTopology X)).IsEquivalence)
  have := Functor.Full.of_iso (smallEtalePushforwardAbImageFactorIso f)
  have := Functor.Faithful.of_iso (smallEtalePushforwardAbImageFactorIso f)
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- **Stacks 04FZ, part (2).** An abelian sheaf on `Y_étale` lies in the essential image of
direct image along an integral universally injective morphism exactly when its support is
contained in `f(X)`, that is, exactly when its restriction to the open complement of `f(X)`
vanishes. -/
@[stacks 04FZ "part (2): essential image"]
public theorem smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective
    (h04CA : AbelianEssImageClosedImmersion.{u})
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtalePushforwardAb f).essImage F ↔
      IsZero (((smallEtaleBaseChange (openComplementRange f).ι).sheafPullback Ab.{u + 1}
        (smallEtaleTopology Y)
        (smallEtaleTopology (openComplementRange f).toScheme)).obj F) := by
  have := universalHomeomorphism_toImage f
  have := isDenseSubsite_of_universalHomeomorphism f.toImage
  have hH : (smallEtalePushforwardAb f.toImage).IsEquivalence :=
    inferInstanceAs (((smallEtaleBaseChange f.toImage).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology f.image) (smallEtaleTopology X)).IsEquivalence)
  have hU : ((openComplementRange f : Y.Opens) : Set Y) = (Set.range f.imageι.base)ᶜ :=
    congrArg (fun U : Y.Opens => (U : Set Y)) (openComplement_imageι f).symm
  rw [essImage_iff_of_comp_iso _ _ _ (smallEtalePushforwardAbImageFactorIso f),
    h04CA f.imageι (openComplementRange f) hU F]

/-- **Stacks 04FZ, trailing clause.** Inverse image along an integral universally injective
morphism is a left inverse to direct image on abelian sheaves. -/
@[stacks 04FZ "trailing clause for abelian sheaves: left inverse"]
public def smallEtalePushforwardAbCompPullbackIso_of_integral_universallyInjective :
    smallEtalePushforwardAb f ⋙ (smallEtaleBaseChange f).sheafPullback Ab.{u + 1}
        (smallEtaleTopology Y) (smallEtaleTopology X) ≅
      𝟭 (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  letI := (smallEtalePushforwardAbFullyFaithful_of_integral_universallyInjective f).full
  letI := (smallEtalePushforwardAbFullyFaithful_of_integral_universallyInjective f).faithful
  asIso (smallEtaleAdjunctionAb f).counit

end AbelianSheaves

end Stacks.EtaleCohomology

end
