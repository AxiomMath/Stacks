module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.CechExactFromSheaf
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteFpqcSheafCriterion

/-!
# The Čech condition for the affine sections of a sheaf of modules on a big site

`AdequateFunctor.cechExactOn_of_isSheafFor` derives the Čech condition of [Stacks, Tag 06VH]
from the sheaf condition, for a module-valued functor realized as the sections of a presheaf
along a "spectrum" functor. This module instantiates it at the affine-section functor of a
sheaf of modules on a chosen big site, and discharges its fibre-product hypothesis.

## Main results

* `Stacks.Adequate.isPullback_affineSpecOver_map`: `Stacks.Adequate.affineSpecOver` carries a
  pushout of the site algebras to a fibre-product square of the site. With
  `Stacks.CechSite.isPushout_of_isColimit_binaryCofan` this says that the degree-two Čech term
  `B₂` of [Stacks, Tag 06VH] has for spectrum the fibre product of `Spec B₁` with itself over
  `Spec B`.
* `Stacks.Adequate.cechExactOn_affineSectionFunctor`: `AdequateFunctor.CechExactOn` for the
  affine-section functor, from the sheaf condition for the one-element coverings
  `Spec B₁ → Spec B`. This is the only hypothesis left; the fibre-product one is discharged.
* `Stacks.Adequate.cechExactOn_affineSectionFunctor_of_isAffineSingletonSheaf` asks that
  hypothesis as `Stacks.Adequate.IsAffineSingletonSheaf`, which
  `Stacks.Adequate.isAffineSingletonSheaf_of_isSheaf_fpqc` supplies from the fpqc sheaf
  condition, together with flatness and surjectivity of the base-changed morphisms.

## Implementation notes

The comparison that `AdequateFunctor.cechExactOn_of_isSheafFor` asks for between the values of
the functor and the sections of the presheaf is the identity here, and its naturality equation
is `rfl`: `Stacks.Adequate.affineSectionFunctor_obj` and
`Stacks.Adequate.affineSectionFunctor_map` hold by definition, so the affine sections *are* the
sheaf's sections over the spectra and not merely identified with them.

The remaining hypothesis is the one-element sheaf condition itself. It is the fpqc one and not
the `τ` one: a flat surjective morphism between affines of the site is an fpqc covering of the
site by `Stacks.Adequate.sieve_generate_singleton_mem_fpqc`, and
`Stacks.Adequate.isAffineSingletonSheaf_of_isSheaf_fpqc` turns the fpqc sheaf condition into
exactly this hypothesis.

For a module **presented** as in [Stacks, Tag 06VK] (5) — the kernel of a map `𝓖ᵃ ⟶ 𝓗ᵃ` of the
associated modules of two quasi-coherent `𝒪_S`-modules — that hypothesis is now discharged, by
`Stacks.Adequate.isAffineSingletonSheaf_of_isAssociatedKernel` in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedModuleFpqcSheaf.lean`, and
`Stacks.Adequate.cechExactOn_affineSectionFunctor_of_isAssociatedKernel` is the resulting form
of the Čech condition. That route does not pass through [Stacks, Tag 03O1] at all: the presheaf
of an associated module *is* the restriction along `Stacks.Adequate.BigSite.toOver` of the
presheaf of [Stacks, Tag 03DS] on all schemes over `S`, which is an fpqc sheaf by [Stacks, Tag
03DT]. What is still not available is the same hypothesis for a module given only as satisfying
`Stacks.Adequate.IsAdequate`, which supplies no presentation of the sheaf; see the
implementation notes of that module and of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/BigSiteFpqcSheafCriterion.lean`.

Flatness and surjectivity of the base-changed morphism `Spec (B ⊗_A A') → Spec B` are not
asserted here either; they are hypotheses of
`Stacks.Adequate.cechExactOn_affineSectionFunctor_of_isAffineSingletonSheaf`. They hold because
a base change of a faithfully flat ring map is faithfully flat, but that is read off the
coproduct hypothesis rather than from an available lemma about the morphism, and is not done.

## References

* [Stacks Project, Tag 06VH](https://stacks.math.columbia.edu/tag/06VH)
* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- Pushouts of commutative algebras are computed on the underlying commutative rings: the
forgetful functor preserves them. Both factors of the identification of `CommAlgCat A` with the
commutative rings under `A` do: an equivalence preserves every colimit, and the forgetful
functor of a coslice category creates the connected ones, `WalkingSpan` being connected. -/
private instance preservesColimitsOfShape_walkingSpan_forget₂ {A : Type u} [CommRing A] :
    PreservesColimitsOfShape WalkingSpan (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}) :=
  inferInstanceAs (PreservesColimitsOfShape WalkingSpan
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙ Under.forget (CommRingCat.of A)))

/-- **Taking spectra carries a pushout of the site algebras to a fibre-product square of the
site.**

This is the second geometric hypothesis of
`Stacks.Adequate.cechExactOn_affineSectionFunctor`, discharged. Together with
`Stacks.CechSite.isPushout_of_isColimit_binaryCofan` it says that the degree-two Čech term
`B₂` of [Stacks, Tag 06VH] has for spectrum the fibre product of `Spec B₁` with itself over
`Spec B`, which is what makes the sheaf condition for the one-element covering
`Spec B₁ → Spec B` a statement about the two Čech faces.

The square is reflected from the schemes: `Stacks.Adequate.BigSite.toOver` composed with the
forgetful functor to the schemes over `S` is the forgetful functor of the slice followed by a
fully faithful inclusion, so it reflects fibre products; on the schemes the square is
`AlgebraicGeometry.isPullback_SpecMap_of_isPushout` applied to the pushout of the underlying
commutative rings. -/
public theorem isPullback_affineSpecOver_map (B : BigSite τ S) (A : CommRingCat.{u})
    (f : Spec A ⟶ S)
    {C₀ C₁ C₂ : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)}
    (iB : C₀ ⟶ C₁) (jB q : C₁ ⟶ C₂)
    (h : IsPushout
      ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iB)
      ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iB)
      ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map jB)
      ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map q)) :
    IsPullback ((affineSpecOver B A f).map jB.op) ((affineSpecOver B A f).map q.op)
      ((affineSpecOver B A f).map iB.op) ((affineSpecOver B A f).map iB.op) := by
  have hD : iB ≫ jB = iB ≫ q :=
    (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map_injective
      (by rw [Functor.map_comp, Functor.map_comp, h.w])
  refine IsPullback.of_map (B.toOver ⋙ Over.forget S) ?_ ?_
  · rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hD]
  · exact AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
      (h.map (forget₂ (CommAlgCat A) CommRingCat))

/-- **The Čech condition for the affine-section functor of a sheaf of modules on a big site.**

The values of `Stacks.Adequate.affineSectionFunctor` are, by
`Stacks.Adequate.affineSectionFunctor_obj` and `Stacks.Adequate.affineSectionFunctor_map`, the
sections of the sheaf over the spectra of the algebras — on the nose, not up to an
identification. So the comparison that `AdequateFunctor.cechExactOn_of_isSheafFor` asks for is
the identity, and the Čech condition of [Stacks, Tag 06VH] for the affine-section functor is
exactly the one-element sheaf condition for the base changes of `Spec A' → Spec A`, together
The fibre-product property of their spectra is supplied by
`Stacks.Adequate.isPullback_affineSpecOver_map`, so the sheaf condition is the only hypothesis
left. It does not mention the module structure or adequacy: `CechExactOn` speaks only about
values of the sheaf, so it is independent of adequacy of the kernels on the site domain. -/
public theorem cechExactOn_affineSectionFunctor (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (A' : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (hsf : ∀ {C₀ C₁ : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)}
      (iB : C₀ ⟶ C₁) (iA : A' ⟶ C₁),
      IsColimit (BinaryCofan.mk
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iB)
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iA)) →
      Presieve.IsSheafFor (F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max u m})
        (Presieve.singleton ((affineSpecOver B A f).map iB.op))) :
    AdequateFunctor.CechExactOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f) A' :=
  AdequateFunctor.cechExactOn_of_isSheafFor _ (affineSectionFunctor B F A f) A'
    (affineSpecOver B A f) (F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max u m})
    (fun _ => Equiv.refl _) (fun _ _ => rfl) hsf
    (isPullback_affineSpecOver_map B A f)

/-- The spectra of the site algebras are affine. -/
private instance isAffine_left_toOver_affineSpecOver (B : BigSite τ S) (A : CommRingCat.{u})
    (f : Spec A ⟶ S) (C : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    IsAffine ((B.toOver.obj ((affineSpecOver B A f).obj (op C))).left) := by
  have he : (B.toOver.obj ((affineSpecOver B A f).obj (op C))).left =
      Spec (CommRingCat.of
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).obj C)) := rfl
  rw [he]
  infer_instance

/-- **`Stacks.Adequate.cechExactOn_affineSectionFunctor` with its sheaf hypothesis in the
repository's own form.**

`Stacks.Adequate.IsAffineSingletonSheaf` is the descent condition along a flat surjective
morphism between affines of the site -- the second condition of the big-site form of [Stacks,
Tag 03O1] -- and `Stacks.Adequate.isAffineSingletonSheaf_of_isSheaf_fpqc` supplies it from the
fpqc sheaf condition. So in this form the Čech condition of [Stacks, Tag 06VH] follows for the
affine-section functor from `F` being an fpqc sheaf, together with flatness and surjectivity of
the base-changed morphisms `Spec (B ⊗_A A') → Spec B`, which is the shape in which [Stacks, Tag
06VL] argues. Affineness is automatic: the objects are spectra. -/
public theorem cechExactOn_affineSectionFunctor_of_isAffineSingletonSheaf (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (A' : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (hF : IsAffineSingletonSheaf B
      (F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max u m}))
    (hflat : ∀ {C₀ C₁ : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)}
      (iB : C₀ ⟶ C₁) (iA : A' ⟶ C₁),
      IsColimit (BinaryCofan.mk
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iB)
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iA)) →
      Flat ((B.toOver.map ((affineSpecOver B A f).map iB.op)).left))
    (hsurj : ∀ {C₀ C₁ : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)}
      (iB : C₀ ⟶ C₁) (iA : A' ⟶ C₁),
      IsColimit (BinaryCofan.mk
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iB)
        ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iA)) →
      Surjective ((B.toOver.map ((affineSpecOver B A f).map iB.op)).left)) :
    AdequateFunctor.CechExactOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f) A' :=
  cechExactOn_affineSectionFunctor B F A f A' fun iB iA hc =>
    hF _ (isAffine_left_toOver_affineSpecOver B A f _)
      (isAffine_left_toOver_affineSpecOver B A f _) (hflat iB iA hc) (hsurj iB iA hc)

end Stacks.Adequate

end
