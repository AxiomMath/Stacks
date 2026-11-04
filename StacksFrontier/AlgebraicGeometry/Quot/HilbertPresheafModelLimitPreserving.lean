module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreservingDirected
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertLimitStageProper
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPresheafCanonicalModel
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable

/-!
# The Hilbert functor is locally of finite presentation over the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
separated and of finite presentation. The morphism to `Y` of the canonical model of the Hilbert
presheaf of `f` (Stacks 0CZY) is relatively limit preserving in the sense of Stacks 049J, and
therefore locally of finite presentation (Stacks 04AK). This is the second assertion of
Stacks 0DM7, which the source quotes from Stacks 0D01.

## Main definitions

* `AlgebraicGeometry.Space.overToSchemesOverPresheaf`: the schemes over a scheme `A` of the site,
  read as schemes over `Y` through a morphism `A ⟶ Y`.
* `AlgebraicGeometry.Space.sectionFiberOfHilbertFamily`: a family of the Hilbert functor over a
  scheme over `A`, read as a lift over that scheme of a point `y` of `Y` over `A`.

## Main results

* `AlgebraicGeometry.Space.relativelyLimitPreserving_toBase_canonical`: relative limit
  preservation.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_toBase_canonical`: local finite
  presentation.

## Implementation notes

Relative limit preservation is tested on directed inverse systems of affine schemes over a scheme
`A` of the site with a point `y` of `Y`, by
`AlgebraicGeometry.relativelyLimitPreserving_of_directed`. A section of the presheaf of lifts of
`y` over a scheme `V ⟶ A` is a family of the Hilbert functor over `V`, read as a scheme over `Y`
through `y`; `AlgebraicGeometry.Space.sectionFiberOfHilbertFamily` is that identification. The
colimit statement is then the pair of finite-stage descent statements
`AlgebraicGeometry.Space.exists_hilbertFamily_baseChange_eq` and
`AlgebraicGeometry.Space.exists_hilbertFamily_baseChange_eq_of_eq`.

## References

* [Stacks Project, Tag 0DM7](https://stacks.math.columbia.edu/tag/0DM7)
* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The schemes over a scheme `A` of the site, read as schemes over `Y` through a morphism
`ŷ : A ⟶ Y`. -/
def overToSchemesOverPresheaf {A : BigFppfOver B S hS} (ŷ : yoneda.obj A ⟶ Y.obj) :
    Over A ⥤ SchemesOverPresheaf B S hS Y where
  obj V := CostructuredArrow.mk (yoneda.map V.hom ≫ ŷ)
  map {V V'} g := CostructuredArrow.homMk g.left (by
    change yoneda.map g.left ≫ yoneda.map V'.hom ≫ ŷ = yoneda.map V.hom ≫ ŷ
    rw [← Category.assoc, ← Functor.map_comp, Over.w g])
  map_id V := CostructuredArrow.hom_ext _ _ rfl
  map_comp g g' := CostructuredArrow.hom_ext _ _ rfl

/-- Base change of a family along two morphisms of schemes over `Y` with the same underlying
morphism, whose sources differ only by an equality of morphisms to `Y`, gives the same family. -/
theorem HilbertFamily.heq_baseChange {T₀ : SchemesOverPresheaf B S hS Y}
    {T : BigFppfOver B S hS} {b₁ b₂ : yoneda.obj T ⟶ Y.obj} (h : b₁ = b₂)
    (g₁ : (CostructuredArrow.mk b₁ : SchemesOverPresheaf B S hS Y) ⟶ T₀)
    (g₂ : (CostructuredArrow.mk b₂ : SchemesOverPresheaf B S hS Y) ⟶ T₀)
    (hg : g₁.left = g₂.left) (z : HilbertFamily f T₀) :
    (z.baseChange g₁).Z ≍ (z.baseChange g₂).Z := by
  subst h
  obtain rfl : g₁ = g₂ := CostructuredArrow.hom_ext _ _ hg
  rfl

variable {A : BigFppfOver B S hS} (yA : Y.obj.obj (op A))

/-- **A family of the Hilbert functor over a scheme over `A` is a lift of `y`.** -/
def sectionFiberOfHilbertFamily (V : Over A)
    (z : HilbertFamily f ((overToSchemesOverPresheaf (yonedaEquiv.symm yA)).obj V)) :
    (sectionFiber B S hS (HilbertPresheafModel.canonical f).toBase A yA).obj (op V) :=
  ⟨equivShrink (HilbertFamilyOver f V.left) ⟨yoneda.map V.hom ≫ yonedaEquiv.symm yA, z⟩, by
    change yonedaEquiv ((equivShrink (HilbertFamilyOver f V.left)).symm
      (equivShrink (HilbertFamilyOver f V.left)
        ⟨yoneda.map V.hom ≫ yonedaEquiv.symm yA, z⟩)).toBase = _
    rw [Equiv.symm_apply_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact (yonedaEquiv_symm_app_apply yA (op V.left) V.hom)⟩

/-- Distinct families of the Hilbert functor give distinct lifts of `y`. -/
theorem sectionFiberOfHilbertFamily_injective (V : Over A) :
    Function.Injective (sectionFiberOfHilbertFamily f yA V) := by
  intro z z' h
  have h' := (equivShrink (HilbertFamilyOver f V.left)).injective (congrArg Subtype.val h)
  exact eq_of_heq (HilbertFamilyOver.mk.inj h').2

/-- Every lift of `y` over a scheme over `A` comes from a family of the Hilbert functor. -/
theorem sectionFiberOfHilbertFamily_surjective (V : Over A) :
    Function.Surjective (sectionFiberOfHilbertFamily f yA V) := by
  rintro ⟨s, hs⟩
  obtain ⟨⟨b, fam⟩, rfl⟩ := (equivShrink (HilbertFamilyOver f V.left)).surjective s
  have hb : b = yoneda.map V.hom ≫ yonedaEquiv.symm yA := by
    apply yonedaEquiv.injective
    change yonedaEquiv ((equivShrink (HilbertFamilyOver f V.left)).symm
      (equivShrink (HilbertFamilyOver f V.left) ⟨b, fam⟩)).toBase = _ at hs
    rw [Equiv.symm_apply_apply] at hs
    rw [hs, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact (yonedaEquiv_symm_app_apply yA (op V.left) V.hom).symm
  subst hb
  exact ⟨fam, rfl⟩

/-- Restricting the lift of `y` given by a family along a morphism of schemes over `A` gives the
lift given by the base change of the family. -/
theorem map_sectionFiberOfHilbertFamily {V V' : Over A} (g : V' ⟶ V)
    (z : HilbertFamily f ((overToSchemesOverPresheaf (yonedaEquiv.symm yA)).obj V)) :
    (sectionFiber B S hS (HilbertPresheafModel.canonical f).toBase A yA).map g.op
        (sectionFiberOfHilbertFamily f yA V z) =
      sectionFiberOfHilbertFamily f yA V'
        (z.baseChange ((overToSchemesOverPresheaf (yonedaEquiv.symm yA)).map g)) := by
  apply Subtype.ext
  show equivShrink (HilbertFamilyOver f V'.left)
      (((equivShrink (HilbertFamilyOver f V.left)).symm (equivShrink (HilbertFamilyOver f V.left)
        ⟨yoneda.map V.hom ≫ yonedaEquiv.symm yA, z⟩)).baseChange g.left) =
    equivShrink (HilbertFamilyOver f V'.left) ⟨yoneda.map V'.hom ≫ yonedaEquiv.symm yA,
      z.baseChange ((overToSchemesOverPresheaf (yonedaEquiv.symm yA)).map g)⟩
  rw [Equiv.symm_apply_apply]
  congr 1
  have hb : yoneda.map g.left ≫ yoneda.map V.hom ≫ yonedaEquiv.symm yA =
      yoneda.map V'.hom ≫ yonedaEquiv.symm yA := by
    rw [← Category.assoc, ← Functor.map_comp, Over.w g]
  exact HilbertFamilyOver.ext hb (HilbertFamily.heq_baseChange f hb _ _ rfl z)

variable {f} in
omit yA in
/-- **The morphism to the base of the Hilbert functor is relatively limit preserving.** For a
morphism `f : X ⟶ Y` of algebraic spaces which is separated and of finite presentation, the
morphism to `Y` of the canonical model of the Hilbert presheaf of `f` turns every cofiltered
limit of affine schemes over `Y` into a colimit of sets (Stacks 049J, part (2)). -/
theorem relativelyLimitPreserving_toBase_canonical (hfp : IsFinitePresentation B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) :
    RelativelyLimitPreserving.{u, u, u, u} B S hS (HilbertPresheafModel.canonical f).toBase := by
  refine relativelyLimitPreserving_of_directed B S hS _ ?_
  intro A yA Λ _ _ _ D c hc hDaff hTaff
  let Φ := overToSchemesOverPresheaf (yonedaEquiv.symm yA)
  have hc' : IsLimit ((CostructuredArrow.proj yoneda Y.obj ⋙ BigFppfOver.toScheme B S hS).mapCone
      (Φ.mapCone c)) := hc
  refine nonempty_isColimit_mapCocone_of_exists_of_eventually_eq
    (sectionFiber B S hS (HilbertPresheafModel.canonical f).toBase A yA) D c ?_ ?_
  · intro x
    obtain ⟨z, rfl⟩ := sectionFiberOfHilbertFamily_surjective f yA c.pt x
    obtain ⟨j, z', hz'⟩ := exists_hilbertFamily_baseChange_eq f (D ⋙ Φ) (Φ.mapCone c) hc'
      hDaff hTaff hfp hsep z
    refine ⟨j, sectionFiberOfHilbertFamily f yA (D.obj j) z', ?_⟩
    rw [map_sectionFiberOfHilbertFamily]
    exact congrArg _ hz'
  · intro i x y hxy
    obtain ⟨z, rfl⟩ := sectionFiberOfHilbertFamily_surjective f yA (D.obj i) x
    obtain ⟨z', rfl⟩ := sectionFiberOfHilbertFamily_surjective f yA (D.obj i) y
    rw [map_sectionFiberOfHilbertFamily, map_sectionFiberOfHilbertFamily] at hxy
    obtain ⟨j, e, he⟩ := exists_hilbertFamily_baseChange_eq_of_eq f (D ⋙ Φ) (Φ.mapCone c) hc'
      hDaff hfp hsep i z z' (sectionFiberOfHilbertFamily_injective f yA c.pt hxy)
    refine ⟨j, e, ?_⟩
    rw [map_sectionFiberOfHilbertFamily, map_sectionFiberOfHilbertFamily]
    exact congrArg _ he

variable {f} in
omit yA in
/-- **The morphism to the base of the Hilbert functor is locally of finite presentation.** For
`f : X ⟶ Y` separated and of finite presentation, the morphism to `Y` of the canonical model of
the Hilbert presheaf of `f` is locally of finite presentation (the second assertion of
Stacks 0DM7, through Stacks 04AK). -/
theorem isLocallyOfFinitePresentation_toBase_canonical (hfp : IsFinitePresentation B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) :
    IsLocallyOfFinitePresentation B S hS (HilbertPresheafModel.canonical f).toBase :=
  AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving B S hS
    (relativelyLimitPreserving_toBase_canonical hfp hsep)

end AlgebraicGeometry.Space

end
