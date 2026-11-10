module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackGroupoidFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineModuleExtension

/-!
# Extending quasi-coherent modules from the pointwise quotient to the quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces, `[U/_pR]` its pointwise groupoid
fibration and `[U/R]` its quotient stack (Stacks 044Q). The canonical map
`[U/_pR] ⟶ [U/R]` is fully faithful and every object of `[U/R]` is fppf locally in its image
(Stacks 044X), so it is a dense subsite inclusion for the two fppf topologies. Its comma
categories embed into the slices of `[U/R]`, which are essentially small at the universe of the
schemes because `[U/R]` is fibred in groupoids over an essentially small site. So the Comparison
Lemma applies at that universe: restriction of sheaves of modules from `[U/R]` to `[U/_pR]` is an
equivalence, and a sheaf of modules on `[U/R]` is quasi-coherent as soon as its restriction is.
This is the reduction "it suffices to prove the lemma with `𝒳 = [U/_pR]`" of the proof of
Stacks 06WT, at the level of modules.

The argument is the one of `AlgebraicGeometry.Stack.AffineCategory.isEquivalence_moduleRestriction`
and `AlgebraicGeometry.Stack.AffineCategory.isQuasicoherentOnSite_of_moduleRestriction` for the
affine inclusion, which works for any fully faithful dense subsite inclusion between categories
fibred in groupoids; it is stated here in that generality.

## Main results

* `AlgebraicGeometry.Stack.FibredDenseSubsite.isEquivalence_moduleRestriction`: the Comparison
  Lemma for sheaves of modules along a fully faithful dense subsite inclusion of categories
  fibred in groupoids, at the universe of the schemes.
* `AlgebraicGeometry.Stack.FibredDenseSubsite.isQuasicoherentOnSite_of_moduleRestriction`:
  quasi-coherence is reflected by such a restriction.
* `AlgebraicGeometry.Stack.isDenseSubsite_pointwiseToQuotientStack`: the canonical map from the
  pointwise groupoid fibration to the quotient stack is a dense subsite inclusion.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

namespace AlgebraicGeometry.Stack.FibredDenseSubsite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (i : 𝒳 ⥤ 𝒴) [i.Full] [i.Faithful]
  (J : GrothendieckTopology 𝒳) (K : GrothendieckTopology 𝒴) [i.IsDenseSubsite J K]

/-- Comma categories `StructuredArrow y F.op` of a fully faithful functor are essentially small as
soon as the slice `Over y.unop` is. -/
private theorem essentiallySmall_structuredArrow_of_over {C : Type*} [Category C] {D : Type*}
    [Category D] (F : C ⥤ D) [F.Full] [F.Faithful] (y : Dᵒᵖ)
    [EssentiallySmall.{u} (Over y.unop)] : EssentiallySmall.{u} (StructuredArrow y F.op) :=
  have : EssentiallySmall.{u} (CostructuredArrow F y.unop) :=
    essentiallySmall_of_fully_faithful (CostructuredArrow.toOver F y.unop)
  (essentiallySmall_congr (costructuredArrowOpEquivalence F y.unop)).mp inferInstance

include hq in
/-- The shapes of the limits computing the extension of a sheaf along `i` are essentially small
at the universe of the schemes: the comma category at `y` embeds into the slice `𝒴/y`. -/
theorem essentiallySmall_structuredArrow (y : 𝒴ᵒᵖ) :
    EssentiallySmall.{u} (StructuredArrow y i.op) :=
  have := hq.essentiallySmall_over y.unop
  essentiallySmall_structuredArrow_of_over i y

include hq in
/-- **The Comparison Lemma for sheaves of modules along `i`**, at the universe of the schemes. -/
theorem isEquivalence_moduleRestriction (R : Sheaf K RingCat.{u}) :
    (Stacks.DenseSubsiteModules.moduleRestriction J K i R).IsEquivalence :=
  have : ∀ y : 𝒴ᵒᵖ, HasLimitsOfShape (StructuredArrow y i.op) AddCommGrpCat.{u} := fun y =>
    have := essentiallySmall_structuredArrow q hq i y
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  inferInstance

include hq in
/-- The shapes of the limits computing the extension of a sheaf from a slice of `𝒳` to the
corresponding slice of `𝒴` are essentially small at the universe of the schemes. -/
theorem essentiallySmall_structuredArrow_overPost (x : 𝒳) (V : (Over (i.obj x))ᵒᵖ) :
    EssentiallySmall.{u} (StructuredArrow V (Over.post (X := x) i).op) := by
  have : EssentiallySmall.{u} (Over V.unop) :=
    have := hq.essentiallySmall_over V.unop.left
    (essentiallySmall_congr (Over.iteratedSliceEquiv V.unop)).mpr inferInstance
  exact essentiallySmall_structuredArrow_of_over (Over.post (X := x) i) V

include hq in
/-- **Restriction of sheaves of modules from a slice of `𝒴` to the corresponding slice of `𝒳`
is an equivalence**, at the universe of the schemes. -/
theorem isEquivalence_moduleRestriction_over (R : Sheaf K RingCat.{u}) (x : 𝒳) :
    letI := Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) i x
    (Stacks.DenseSubsiteModules.moduleRestriction (J.over x) (K.over (i.obj x))
      (Over.post (X := x) i) (R.over (i.obj x))).IsEquivalence := by
  let := Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) i x
  have : ∀ V : (Over (i.obj x))ᵒᵖ,
      HasLimitsOfShape (StructuredArrow V (Over.post (X := x) i).op) AddCommGrpCat.{u} :=
    fun V =>
    have := essentiallySmall_structuredArrow_overPost q hq i x V
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  infer_instance

include hp hq in
/-- **A global presentation on a slice of `𝒳` extends to the corresponding slice of `𝒴`.** -/
theorem hasGlobalPresentation_over_of_moduleRestriction (R : Sheaf K RingCat.{u})
    (M : SheafOfModules.{u} R) (x : 𝒳)
    (h : (((Stacks.DenseSubsiteModules.moduleRestriction J K i R).obj M).over
      x).HasGlobalPresentation) :
    (M.over (i.obj x)).HasGlobalPresentation := by
  let := Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) i x
  have := hp.essentiallySmall_over x
  have := hq.essentiallySmall_over (i.obj x)
  have := GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} (J.over x)
  have := GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u}
    (K.over (i.obj x))
  have : (J.over x).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have : (K.over (i.obj x)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have := isEquivalence_moduleRestriction_over q hq i J K R x
  let E := Stacks.DenseSubsiteModules.moduleRestriction (J.over x) (K.over (i.obj x))
    (Over.post (X := x) i) (R.over (i.obj x))
  let e := E.asEquivalence
  have : PreservesColimitsOfSize.{u, u} e.inverse :=
    e.symm.toAdjunction.leftAdjoint_preservesColimits
  obtain ⟨P⟩ := Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation h
  let η : SheafOfModules.unit (R.over (i.obj x)) ≅ e.inverse.obj (SheafOfModules.unit _) :=
    e.unitIso.app _ ≪≫ e.inverse.mapIso (Iso.refl _)
  let P₀ : SheafOfModules.Presentation (E.obj (M.over (i.obj x))) := P
  let P' := P₀.map e.inverse η
  let P'' := SheafOfModules.Presentation.ofIsIso (e.unitIso.inv.app (M.over (i.obj x))) P'
  exact Stacks.SheafOfModules.hasGlobalPresentation_of_presentation P''

omit [i.Full] [i.Faithful] in
/-- The images of a family of objects of `𝒳` covering the final object of `𝒳` cover the final
object of `𝒴`. -/
theorem coversTop_obj {I : Type*} {X : I → 𝒳} (hX : J.CoversTop X) :
    K.CoversTop (fun k => i.obj (X k)) := by
  intro W
  have := Functor.IsDenseSubsite.isCoverDense J K i
  refine K.transitive (Functor.is_cover_of_isCoverDense i K W) _ ?_
  rintro Z f ⟨⟨y, a, b, hab⟩⟩
  have hy : (Sieve.ofObjects X y).functorPushforward i ∈ K (i.obj y) :=
    (Functor.functorPushforward_mem_iff J K i).mpr (hX y)
  refine K.superset_covering ?_ (K.pullback_stable a hy)
  rintro Z' g ⟨Y', h, k, ⟨j, ⟨c⟩⟩, hk⟩
  exact ⟨j, ⟨k ≫ i.map c⟩⟩

include hp hq in
/-- **A sheaf of modules on `𝒴` whose restriction to `𝒳` is quasi-coherent is
quasi-coherent.** -/
theorem isQuasicoherentOnSite_of_moduleRestriction (R : Sheaf K RingCat.{u})
    (M : SheafOfModules.{u} R)
    (h : ((Stacks.DenseSubsiteModules.moduleRestriction J K i R).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  obtain ⟨I, X, hX, hpres⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation _).mp h
  exact (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation _).mpr
    ⟨I, fun k => i.obj (X k), coversTop_obj i J K hX,
      fun k => hasGlobalPresentation_over_of_moduleRestriction p q hp hq i J K R M (X k)
        (hpres k)⟩

end AlgebraicGeometry.Stack.FibredDenseSubsite

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- **The pointwise quotient is cover-dense in the quotient stack**: the charted points already
are (`AlgebraicGeometry.Stack.isCoverDense_chartedPointFunctor`). -/
theorem isCoverDense_pointwiseToQuotientStack :
    (pointwiseToQuotientStack G).IsCoverDense
      (BigFppfOver.associatedTopology C S hS (quotientStack G).p .fppf) := by
  constructor
  intro y
  refine (BigFppfOver.associatedTopology C S hS (quotientStack G).p .fppf).superset_covering ?_
    ((isCoverDense_chartedPointFunctor G).is_cover y)
  rintro Z f ⟨d⟩
  exact ⟨{ obj := (inducedFunctor _).obj d.obj, lift := d.lift, map := d.map, fac := d.fac }⟩

/-- The functor `pointwiseToQuotientStack G` is full. -/
instance : (pointwiseToQuotientStack G).Full := (fullyFaithfulPointwiseToQuotientStack G).full

/-- The functor `pointwiseToQuotientStack G` is faithful. -/
instance : (pointwiseToQuotientStack G).Faithful :=
  (fullyFaithfulPointwiseToQuotientStack G).faithful

/-- **The canonical map `[U/_pR] ⟶ [U/R]` is a dense subsite inclusion** for the two fppf
topologies. -/
theorem isDenseSubsite_pointwiseToQuotientStack :
    (pointwiseToQuotientStack G).IsDenseSubsite
      (BigFppfOver.associatedTopology C S hS
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p .fppf)
      (BigFppfOver.associatedTopology C S hS (quotientStack G).p .fppf) :=
  Functor.isDenseSubsite_inheritedTopology
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p (𝟭 _)
    (pointwiseToQuotientStack G) (quotientStack G).p
    (BigFppfOver.baseOverTopology C S hS .fppf) (BigFppfOver.baseOverTopology C S hS .fppf)
    (isFiberedInGroupoids_presheafOfGroupoids _) (isFiberedInGroupoids_quotientStack G)
    { functorPushforward_mem_iff := fun {_ R} => by
        rw [Sieve.functorPushforward_id]; exact Iff.rfl }
    (fun y R => by
      rw [Sieve.functorPushforward_id, ← Sieve.functorPushforward_comp]
      exact Iff.rfl)
    (isCoverDense_pointwiseToQuotientStack G)

end AlgebraicGeometry.Stack

end
