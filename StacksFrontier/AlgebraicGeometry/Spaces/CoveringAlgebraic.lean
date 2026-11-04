module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coproducts of the restrictions of an fppf sheaf along a covering of the base

Let `F` be a presheaf on the big fppf site of a scheme `S`, and let `{Xᵢ → S}` be a family
of objects of that site covering `S`. The base scheme is the terminal object
`Over.mk (𝟙 (B.obj hS))` of the site, so the restriction of `F` to `Xᵢ`, viewed again as a
presheaf over `S`, is the binary product `yoneda.obj Xᵢ ⨯ F`. Whenever these products have
a coproduct `G` in the category of fppf sheaves, the second projections
`yoneda.obj Xᵢ ⨯ F ⟶ F` induce a morphism `G ⟶ F`. This file constructs that morphism and
shows that it is locally surjective, hence an epimorphism of sheaves.

This is the surjectivity half of the data to which Stacks 04SK applies the bootstrap
theorem: it identifies `∐ᵢ (h_{Xᵢ} × F) → F` as a surjection of sheaves.

## Main definitions

* `AlgebraicGeometry.Space.isTerminal_yoneda_obj_base` presents the presheaf represented by
  the base, `yoneda.obj (Over.mk (𝟙 (B.obj hS)))`, as a terminal object of the category of
  presheaves on the site; the structure morphism of a presheaf `F` "to `S`" is
  `(isTerminal_yoneda_obj_base B S hS).from F`.
* `AlgebraicGeometry.Space.coverCoproductProj` is the morphism `G ⟶ F` induced by the
  projections, where `G` is a sheaf coproduct of the `yoneda.obj Xᵢ ⨯ F`.

## Main results

* `CategoryTheory.Limits.IsTerminal.isPullback_prod`: a binary product is the fibre product
  over a terminal object.
* `AlgebraicGeometry.Space.isPullback_prod_fst_snd_yoneda_obj`: the restriction
  `yoneda.obj a ⨯ F` of a presheaf `F` to an object `a` of the site is the base change of
  `a ⟶ S` along the structure morphism of `F`. This is the first sentence of the proof of
  Stacks 04SK.
* `AlgebraicGeometry.Space.relativelyRepresentable_prod_snd`: consequently the projection
  `yoneda.obj a ⨯ F ⟶ F` is representable.
* `AlgebraicGeometry.Space.presheaf_prod_snd`: and it has every property of `a ⟶ S` which is
  stable under base change — flatness and being locally of finite presentation, for a member
  of an fppf covering of the base.
* `AlgebraicGeometry.Space.isAlgebraicSpace_prod_yoneda_obj`: the restriction of an algebraic
  space to an object of the site is an algebraic space.
* `AlgebraicGeometry.Space.coverCoproductProj_ι` identifies the composition of the `i`-th
  coproduct injection with `AlgebraicGeometry.Space.coverCoproductProj` as the projection.
* `AlgebraicGeometry.Space.isLocallySurjective_coverCoproductProj` and
  `AlgebraicGeometry.Space.epi_coverCoproductProj`: the induced morphism is locally
  surjective for the fppf topology, hence an epimorphism of fppf sheaves.

## Implementation notes

The binders are those of Stacks 04SK: the covering family is a
`CategoryTheory.PreZeroHypercover` of the terminal object whose sieve is a covering sieve,
its index type may be one universe above the values of the presheaves, the coproduct is
taken in sheaves rather than presheaves, and it is supplied as a colimit cocone rather than
assumed to exist. Nothing about schemes, flatness or finite presentation enters: the two
results hold verbatim for a sheaf of types on any site with a terminal object, and the
hypothesis that each `yoneda.obj Xᵢ ⨯ F` is an algebraic space is used only through its
sheaf condition, which is what makes the coproduct a coproduct of sheaves.

The identification of the restriction as a base change is carried out over an arbitrary
terminal object rather than over `⊤_`: the object `Over.mk (𝟙 (B.obj hS))` is the terminal
object of the site by `CategoryTheory.Over.mkIdTerminal`, but it is not the one a
`CategoryTheory.Limits.HasTerminal` instance would produce, and the covering family of
Stacks 04SK is indexed over it on the nose.

Stacks 04SK itself — that `F` is an algebraic space as soon as it is a sheaf, each
restriction `h_{Xᵢ} × F` is an algebraic space, and their coproduct is an algebraic space —
is *not* proved here. In the source it is a corollary of the bootstrap theorem Stacks 04S6,
applied to the morphism constructed in this file, and that theorem has no formalization in
this library yet. What this file supplies of that corollary is everything but the appeal to
Stacks 04S6: the coproduct morphism `∐ᵢ (h_{Xᵢ} × F) ⟶ F` is a surjection of sheaves, and
each of the morphisms `h_{Xᵢ} × F ⟶ F` it is assembled from is representable and inherits
flatness and local finite presentation from `Xᵢ ⟶ S`.

## References

* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ u

namespace CategoryTheory.Limits

/-- A binary product is the fibre product over a terminal object: the square with the two
projections on top and the two morphisms to a terminal object on the bottom is Cartesian. -/
@[sga "3 I 1.2" "more general", sga "4 IV 5.2" "partial"]
theorem IsTerminal.isPullback_prod {C : Type u₁} [Category.{v₁} C] {T : C} (hT : IsTerminal T)
    (A A' : C) [HasBinaryProduct A A'] :
    IsPullback (prod.fst : A ⨯ A' ⟶ A) (prod.snd : A ⨯ A' ⟶ A') (hT.from A) (hT.from A') :=
  IsPullback.of_isLimit
    (isPullbackOfIsTerminalIsProduct (hT.from A) (hT.from A') prod.fst prod.snd hT
      (prodIsProd A A'))

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

/-- The presheaf on the big fppf site of `S` represented by the base, that is by the terminal
object `Over.mk (𝟙 (B.obj hS))` of the site, is a terminal object of the category of
presheaves on the site.

Yoneda preserves limits, so this is the terminality of the base in the site, transported. The
structure morphism of a presheaf `F` of the site over `S` is the resulting unique morphism
`(isTerminal_yoneda_obj_base B S hS).from F`. -/
noncomputable def isTerminal_yoneda_obj_base (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS))) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.mkIdTerminal.isTerminalObj yoneda _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The restriction of a presheaf to an object of the site is a base change.** For an object
`a` of the big fppf site of `S` and a presheaf `F` on that site, the square with the two
projections of `yoneda.obj a ⨯ F` on top, the morphism of the site `a ⟶ S` below the first and
the structure morphism of `F` below the second is Cartesian.

This is the first sentence of the proof of Stacks 04SK: the restriction `h_a × F` of `F` to `a`
is the base change of `a ⟶ S` along `F ⟶ S`. -/
theorem isPullback_prod_fst_snd_yoneda_obj (a : BigFppfOver B S hS)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsPullback (prod.fst : yoneda.obj a ⨯ F ⟶ yoneda.obj a) prod.snd
      (yoneda.map (Over.mkIdTerminal.from a))
      ((isTerminal_yoneda_obj_base B S hS).from F) := by
  have he : (isTerminal_yoneda_obj_base B S hS).from (yoneda.obj a) =
      yoneda.map (Over.mkIdTerminal.from a) :=
    (isTerminal_yoneda_obj_base B S hS).hom_ext _ _
  rw [← he]
  exact (isTerminal_yoneda_obj_base B S hS).isPullback_prod (yoneda.obj a) F

/-- **The projection from the restriction of a presheaf to an object of the site is
representable.** It is the base change of a morphism of the site along the structure morphism
of the presheaf, by
`AlgebraicGeometry.Space.isPullback_prod_fst_snd_yoneda_obj`, and the site has fibre
products. -/
theorem relativelyRepresentable_prod_snd (a : BigFppfOver B S hS)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    yoneda.relativelyRepresentable (prod.snd : yoneda.obj a ⨯ F ⟶ F) :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    (isPullback_prod_fst_snd_yoneda_obj a F)
    (Functor.relativelyRepresentable.map yoneda (Over.mkIdTerminal.from a))

/-- **The projection from the restriction of a presheaf to an object of the site inherits
every base-change stable property of that object's structure morphism.** If `P` is a property
of morphisms of schemes which is stable under base change and holds for the structure morphism
`a ⟶ S` of an object of the site, then the projection `yoneda.obj a ⨯ F ⟶ F` is representable
with `P`.

For a member of an fppf covering of the base this gives flatness and local finite
presentation of `h_a × F ⟶ F`, which is what Stacks 04SK feeds to the bootstrap theorem
Stacks 04S6. -/
theorem presheaf_prod_snd {P : MorphismProperty Scheme.{u}} (hP : P.IsStableUnderBaseChange)
    (a : BigFppfOver B S hS) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hPa : P ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a))) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (prod.snd : yoneda.obj a ⨯ F ⟶ F) :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (P.inverseImage (BigFppfOver.toScheme B S hS))).of_isPullback
      (isPullback_prod_fst_snd_yoneda_obj a F)
      (presheaf_yoneda_map_of_inverseImage B S hS hP (Over.mkIdTerminal.from a) hPa)

/-- **The restriction of an algebraic space to an object of the site is an algebraic space.**
The projection to it is representable by
`AlgebraicGeometry.Space.relativelyRepresentable_prod_snd`, so this is Stacks 02WY.

The hypothesis `hFi` of Stacks 04SK is therefore implied by its conclusion; the content of
that tag is the converse. -/
theorem isAlgebraicSpace_prod_yoneda_obj (a : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    IsAlgebraicSpace B S hS (yoneda.obj a ⨯ F) :=
  isAlgebraicSpace_of_relativelyRepresentable B S hS _
    (relativelyRepresentable_prod_snd a F) hF

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
  (E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS))))
  (hFi : ∀ i : E.I₀, IsAlgebraicSpace B S hS (yoneda.obj (E.X i) ⨯ F))
  {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
  (ι : ∀ i : E.I₀,
    (⟨yoneda.obj (E.X i) ⨯ F, (hFi i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
  (hcoprod : IsColimit (Cofan.mk G ι))

/-- The morphism to `F` from a sheaf coproduct `G` of the restrictions
`yoneda.obj (E.X i) ⨯ F` of `F` to the members of a covering family of the base, induced by
the projections to `F`. -/
noncomputable def coverCoproductProj :
    G ⟶ (⟨F, hF⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
  hcoprod.desc (Cofan.mk _ fun _ ↦ ObjectProperty.homMk Limits.prod.snd)

/-- The `i`-th coproduct injection followed by `AlgebraicGeometry.Space.coverCoproductProj`
is the projection `yoneda.obj (E.X i) ⨯ F ⟶ F`. -/
lemma coverCoproductProj_ι (i : E.I₀) :
    (ι i).hom ≫ (coverCoproductProj hF E hFi ι hcoprod).hom = Limits.prod.snd := by
  have h := hcoprod.fac (Cofan.mk _ fun j ↦
    (ObjectProperty.homMk Limits.prod.snd :
      (⟨yoneda.obj (E.X j) ⨯ F, (hFi j).isSheaf⟩ :
        Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨F, hF⟩)) ⟨i⟩
  simp only [Cofan.mk_ι_app] at h
  exact Sheaf.hom_ext_iff.mp h

/-- The coproduct of the restrictions of `F` to the members of a covering family of the base
surjects onto `F` locally for the fppf topology: a section of `F` over an object `Y` of the
site lifts after restriction along any morphism `Y' ⟶ Y` which factors through a member of
the family, and those morphisms form a covering sieve. -/
lemma isLocallySurjective_coverCoproductProj
    (hE : E.sieve₀ ∈ BigFppfOver.topology B S hS (Over.mk (𝟙 (B.obj hS)))) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (coverCoproductProj hF E hFi ι hcoprod).hom where
  imageSieve_mem {X} x := by
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      ((BigFppfOver.topology B S hS).pullback_stable
        (Over.mkIdTerminal.from X) hE)
    rintro Y g hg
    obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    refine ⟨yonedaEquiv (Limits.prod.lift (yoneda.map a)
      (yonedaEquiv.symm (F.map g.op x)) ≫ (ι i).hom), ?_⟩
    rw [← yonedaEquiv_comp, Category.assoc, coverCoproductProj_ι hF E hFi ι hcoprod i,
      Limits.prod.lift_snd, Equiv.apply_symm_apply]

/-- The coproduct of the restrictions of `F` to the members of a covering family of the base
is an epimorphism onto `F` in the category of fppf sheaves. -/
lemma epi_coverCoproductProj
    (hE : E.sieve₀ ∈ BigFppfOver.topology B S hS (Over.mk (𝟙 (B.obj hS)))) :
    Epi (coverCoproductProj hF E hFi ι hcoprod) :=
  have := isLocallySurjective_coverCoproductProj hF E hFi ι hcoprod hE
  inferInstance

end AlgebraicGeometry.Space

end
