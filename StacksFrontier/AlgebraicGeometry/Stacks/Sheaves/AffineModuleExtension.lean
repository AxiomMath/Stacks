module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# Sheaves of modules on the affine subcategory extend, at the universe of the schemes

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, with `𝒳 : Type v` and
`Category.{w} 𝒳` for universes unrelated to the universe `u` of the schemes. For topologies `J₀`
on the affine subcategory `𝒳_{affine}` of Stacks 0H0A and `J` on `𝒳` for which the affine
inclusion is a dense subsite — the five pairs of Stacks 0H0B — restriction of sheaves of modules
along the affine inclusion is an equivalence, with sections in the universe `u` of the rings of
functions on the schemes; and a sheaf of modules on `𝒳` is quasi-coherent as soon as its
restriction to `𝒳_{affine}` is.

The Comparison Lemma computes the extension of a sheaf by limits over the comma categories of
the affine inclusion. Those are not small in general, because `𝒳` need not be; but the comma
category at an object `x` embeds fully faithfully into the slice `𝒳/x`, which embeds fully
faithfully into the slice of the big fppf site of `S` at `p(x)`, because `p` is fibred in
groupoids. So they are essentially small at `u`, and the limits exist in abelian groups of the
universe `u`.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.essentiallySmall_costructuredArrow_inclusion`: the comma
  categories of the affine inclusion are essentially small at the universe of the schemes.
* `AlgebraicGeometry.Stack.AffineCategory.isEquivalence_sheafPushforwardContinuous_addCommGrpCat`:
  the Comparison Lemma for sheaves of abelian groups along the affine inclusion.
* `AlgebraicGeometry.Stack.AffineCategory.isEquivalence_moduleRestriction`: **restriction of
  sheaves of modules along the affine inclusion is an equivalence**, at the universe of the
  schemes.
* `AlgebraicGeometry.Stack.AffineCategory.isEquivalence_moduleRestriction_over`: the same for the
  localizations at an object of the affine subcategory.
* `AlgebraicGeometry.Stack.AffineCategory.isQuasicoherentOnSite_of_moduleRestriction`: **a sheaf
  of modules on `𝒳` whose restriction to `𝒳_{affine}` is quasi-coherent is quasi-coherent.**

## References

* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack.AffineCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- If the comma category `F ↓ d` is essentially small, so is the opposite comma category
`d ↓ Fᵒᵖ`. -/
private theorem essentiallySmall_structuredArrow_op {C : Type*} [Category C] {D : Type*}
    [Category D] (F : C ⥤ D) (d : D) [EssentiallySmall.{u} (CostructuredArrow F d)] :
    EssentiallySmall.{u} (StructuredArrow (op d) F.op) :=
  (essentiallySmall_congr (costructuredArrowOpEquivalence F d)).mp inferInstance

/-- The comma categories of the affine inclusion are essentially small at the universe of the
schemes: the comma category at `x` embeds fully faithfully into the slice `𝒳/x`. -/
theorem essentiallySmall_costructuredArrow_inclusion (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    EssentiallySmall.{u} (CostructuredArrow (inclusion B S hS p) x) :=
  have := hp.essentiallySmall_over x
  essentiallySmall_of_fully_faithful (CostructuredArrow.toOver (inclusion B S hS p) x)

/-- The shapes of the limits computing the extension of a sheaf from the affine subcategory are
essentially small at the universe of the schemes. -/
theorem essentiallySmall_structuredArrow_inclusion (hp : p.IsFiberedInGroupoids) (x : 𝒳ᵒᵖ) :
    EssentiallySmall.{u} (StructuredArrow x (inclusion B S hS p).op) :=
  have := essentiallySmall_costructuredArrow_inclusion B S hS p hp x.unop
  essentiallySmall_structuredArrow_op (inclusion B S hS p) x.unop

/-- **The Comparison Lemma for sheaves of abelian groups along the affine inclusion**, at the
universe of the schemes. -/
theorem isEquivalence_sheafPushforwardContinuous_addCommGrpCat (hp : p.IsFiberedInGroupoids)
    (J₀ : GrothendieckTopology (AffineCategory B S hS p)) (J : GrothendieckTopology 𝒳)
    [(inclusion B S hS p).IsDenseSubsite J₀ J] :
    ((inclusion B S hS p).sheafPushforwardContinuous AddCommGrpCat.{u} J₀ J).IsEquivalence := by
  have : ∀ x : 𝒳ᵒᵖ, HasLimitsOfShape (StructuredArrow x (inclusion B S hS p).op)
      AddCommGrpCat.{u} := fun x =>
    have := essentiallySmall_structuredArrow_inclusion B S hS p hp x
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  infer_instance

/-- **Restriction of sheaves of modules along the affine inclusion is an equivalence**, at the
universe of the schemes, for any topologies `J₀` on the affine subcategory and `J` on `𝒳` for
which the affine inclusion is a dense subsite. This is the module-level form of Stacks 0H0B and
0H0C. -/
theorem isEquivalence_moduleRestriction (hp : p.IsFiberedInGroupoids)
    (J₀ : GrothendieckTopology (AffineCategory B S hS p)) (J : GrothendieckTopology 𝒳)
    [(inclusion B S hS p).IsDenseSubsite J₀ J] (R : Sheaf J RingCat.{u}) :
    (Stacks.DenseSubsiteModules.moduleRestriction J₀ J (inclusion B S hS p) R).IsEquivalence :=
  have := isEquivalence_sheafPushforwardContinuous_addCommGrpCat B S hS p hp J₀ J
  inferInstance

/-- The slices of the affine subcategory of a category fibred in groupoids are essentially small
at the universe of the schemes. -/
theorem essentiallySmall_over_affine (hp : p.IsFiberedInGroupoids)
    (y : AffineCategory B S hS p) : EssentiallySmall.{u} (Over y) :=
  have : EssentiallySmall.{u} (BigAffineFppf B S hS) :=
    essentiallySmall_fullSubcategory (IsAffineOver B S hS)
  (isFiberedInGroupoids_toAffine B S hS p hp).essentiallySmall_over y

/-- The shapes of the limits computing the extension of a sheaf from a slice of the affine
subcategory to the corresponding slice of `𝒳` are essentially small at the universe of the
schemes. -/
theorem essentiallySmall_structuredArrow_overPost (hp : p.IsFiberedInGroupoids)
    (y : AffineCategory B S hS p) (V : (Over ((inclusion B S hS p).obj y))ᵒᵖ) :
    EssentiallySmall.{u} (StructuredArrow V (Over.post (X := y) (inclusion B S hS p)).op) := by
  have : EssentiallySmall.{u} (Over V.unop) :=
    have := hp.essentiallySmall_over V.unop.left
    (essentiallySmall_congr (Over.iteratedSliceEquiv V.unop)).mpr inferInstance
  have := essentiallySmall_of_fully_faithful
    (CostructuredArrow.toOver (Over.post (X := y) (inclusion B S hS p)) V.unop)
  exact essentiallySmall_structuredArrow_op (Over.post (X := y) (inclusion B S hS p)) V.unop

section Restriction

variable (J₀ : GrothendieckTopology (AffineCategory B S hS p)) (J : GrothendieckTopology 𝒳)
  [(inclusion B S hS p).IsDenseSubsite J₀ J]

/-- **Restriction of sheaves of modules from a slice of `𝒳` to the corresponding slice of the
affine subcategory is an equivalence**, at the universe of the schemes. -/
theorem isEquivalence_moduleRestriction_over (hp : p.IsFiberedInGroupoids)
    (R : Sheaf J RingCat.{u}) (y : AffineCategory B S hS p) :
    letI := Stacks.Sites.overPost_isDenseSubsite (J := J₀) (K := J) (inclusion B S hS p) y
    (Stacks.DenseSubsiteModules.moduleRestriction (J₀.over y)
      (J.over ((inclusion B S hS p).obj y)) (Over.post (X := y) (inclusion B S hS p))
      (R.over ((inclusion B S hS p).obj y))).IsEquivalence := by
  let := Stacks.Sites.overPost_isDenseSubsite (J := J₀) (K := J) (inclusion B S hS p) y
  have : ∀ V : (Over ((inclusion B S hS p).obj y))ᵒᵖ,
      HasLimitsOfShape (StructuredArrow V (Over.post (X := y) (inclusion B S hS p)).op)
        AddCommGrpCat.{u} := fun V =>
    have := essentiallySmall_structuredArrow_overPost B S hS p hp y V
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  infer_instance

/-- **A global presentation on a slice of the affine subcategory extends to the corresponding
slice of `𝒳`.** If the restriction of a sheaf of modules `𝒢` on `𝒳` to `𝒳_{affine}` has a global
presentation on the slice at `y`, then `𝒢` has one on the slice at `y`: the extension functor
inverse to restriction on the slices preserves colimits and the structure sheaf. -/
theorem hasGlobalPresentation_over_of_moduleRestriction (hp : p.IsFiberedInGroupoids)
    (R : Sheaf J RingCat.{u}) (G : SheafOfModules.{u} R) (y : AffineCategory B S hS p)
    (h : (((Stacks.DenseSubsiteModules.moduleRestriction J₀ J (inclusion B S hS p) R).obj
      G).over y).HasGlobalPresentation) :
    (G.over ((inclusion B S hS p).obj y)).HasGlobalPresentation := by
  let := Stacks.Sites.overPost_isDenseSubsite (J := J₀) (K := J) (inclusion B S hS p) y
  let i := inclusion B S hS p
  have := essentiallySmall_over_affine B S hS p hp y
  have := hp.essentiallySmall_over (i.obj y)
  have := GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u}
    (J₀.over y)
  have := GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u}
    (J.over (i.obj y))
  have : (J₀.over y).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have : (J.over (i.obj y)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have := isEquivalence_moduleRestriction_over B S hS p J₀ J hp R y
  let E := Stacks.DenseSubsiteModules.moduleRestriction (J₀.over y) (J.over (i.obj y))
    (Over.post (X := y) i) (R.over (i.obj y))
  let e := E.asEquivalence
  have : PreservesColimitsOfSize.{u, u} e.inverse :=
    e.symm.toAdjunction.leftAdjoint_preservesColimits
  obtain ⟨P⟩ := Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation h
  let η : SheafOfModules.unit (R.over (i.obj y)) ≅ e.inverse.obj (SheafOfModules.unit _) :=
    e.unitIso.app _ ≪≫ e.inverse.mapIso (Iso.refl _)
  let P₀ : SheafOfModules.Presentation (E.obj (G.over (i.obj y))) := P
  let P' := P₀.map e.inverse η
  let P'' := SheafOfModules.Presentation.ofIsIso (e.unitIso.inv.app (G.over (i.obj y))) P'
  exact Stacks.SheafOfModules.hasGlobalPresentation_of_presentation P''

/-- The images of a family of objects of the affine subcategory covering the final object of
`𝒳_{affine}` cover the final object of `𝒳`. -/
theorem coversTop_inclusion_obj {I : Type*} {U : I → AffineCategory B S hS p}
    (hU : J₀.CoversTop U) : J.CoversTop (fun k => (inclusion B S hS p).obj (U k)) := by
  intro W
  let i := inclusion B S hS p
  have := Functor.IsDenseSubsite.isCoverDense J₀ J i
  refine J.transitive (Functor.is_cover_of_isCoverDense i J W) _ ?_
  rintro Z f ⟨⟨y, a, b, hab⟩⟩
  have hy : (Sieve.ofObjects U y).functorPushforward i ∈ J (i.obj y) :=
    (Functor.functorPushforward_mem_iff J₀ J i).mpr (hU y)
  refine J.superset_covering ?_ (J.pullback_stable a hy)
  rintro Z' g ⟨Y', h, k, ⟨j, ⟨c⟩⟩, hk⟩
  refine ⟨j, ⟨k ≫ i.map c⟩⟩

/-- **A sheaf of modules on `𝒳` whose restriction to the affine subcategory is quasi-coherent is
quasi-coherent.** This is the reflection half of Stacks 03DM along the equivalence of Stacks
0H0C. The restriction has a global presentation on the slices at a family of objects covering
`𝒳_{affine}`; those presentations extend to the slices of `𝒳` at the same objects, by
`hasGlobalPresentation_over_of_moduleRestriction`, and the objects still cover `𝒳`. -/
theorem isQuasicoherentOnSite_of_moduleRestriction (hp : p.IsFiberedInGroupoids)
    (R : Sheaf J RingCat.{u}) (G : SheafOfModules.{u} R)
    (h : ((Stacks.DenseSubsiteModules.moduleRestriction J₀ J (inclusion B S hS p) R).obj
      G).IsQuasicoherentOnSite) :
    G.IsQuasicoherentOnSite := by
  obtain ⟨I, U, hU, hpres⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation _).mp h
  exact (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation _).mpr
    ⟨I, fun k => (inclusion B S hS p).obj (U k), coversTop_inclusion_obj B S hS p J₀ J hU,
      fun k => hasGlobalPresentation_over_of_moduleRestriction B S hS p J₀ J hp R G (U k)
        (hpres k)⟩

end Restriction

end AlgebraicGeometry.Stack.AffineCategory

end
