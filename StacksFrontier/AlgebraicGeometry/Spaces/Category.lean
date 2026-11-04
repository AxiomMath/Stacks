module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# The category of algebraic spaces over a scheme

The algebraic spaces over a scheme `S` contained in a big fppf site `B` form the full
subcategory of presheaves on the big fppf site of `S` cut out by
`AlgebraicGeometry.IsAlgebraicSpace`; its morphisms are therefore exactly the natural
transformations of Tag 0260. Every scheme over `S` is an algebraic space over `S`: the big
fppf topology is subcanonical, so a representable presheaf is a sheaf, its diagonal is
representable because the Yoneda embedding is fully faithful and the site has fibre products,
and the identity is a surjective étale atlas.

The category has fibre products, and they are computed in presheaves: the presheaf fibre
product of two algebraic spaces over an algebraic space is again an algebraic space, and the
resulting square stays cartesian in the full subcategory.

For a morphism `S ⟶ S'` of the site, an algebraic space over `S'` equipped with a morphism to
the representable algebraic space of `S` is the same thing as an algebraic space over `S`; the
category of such pairs is `AlgebraicGeometry.SpacesOverSmallerBase`, and
`AlgebraicGeometry.algebraicSpaceMap` reads the structural morphism of such a pair as a
morphism of algebraic spaces over the original base.

## Main definitions

* `AlgebraicGeometry.AlgebraicSpaces`: **Stacks 02X2**, the category of algebraic spaces
  over `S`.
* `AlgebraicGeometry.AlgebraicSpaces.fiberProduct` equips the presheaf fibre product with its
  algebraic-space property.
* `AlgebraicGeometry.SpacesOverSmallerBase`: **Stacks 04SG**, algebraic spaces over `S'` with
  a morphism to `S`, for `S ⟶ S'`.
* `AlgebraicGeometry.algebraicSpaceMap`: the structural morphism of such a pair, as a morphism
  of `AlgebraicGeometry.AlgebraicSpaces`.
* `CategoryTheory.Over.isInitialOfIsInitialLeft` promotes an initial object of the base
  category to an initial object of a slice, and
  `AlgebraicGeometry.isInitial_schemeBelow` promotes an initial scheme to an initial object
  of a big fppf site.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_yoneda`: **Stacks 025Z**.
* `AlgebraicGeometry.isAlgebraicSpace_pullback`: the presheaf fibre product of algebraic
  spaces is an algebraic space.
* `AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`: it is a fibre product in the
  category of algebraic spaces, whence the instances
  `AlgebraicGeometry.AlgebraicSpaces.hasPullback` and
  `AlgebraicGeometry.AlgebraicSpaces.hasPullbacks`.
* `CategoryTheory.MorphismProperty.diag_pullback`: for a multiplicative morphism property
  stable under base change, the absolute diagonal of a fibre product lies in the property as
  soon as the absolute diagonals of the two factors do.

## Implementation notes

`AlgebraicGeometry.AlgebraicSpaces` is an abbreviation for a
`CategoryTheory.ObjectProperty.FullSubcategory`, so the full-subcategory API — in particular
`CategoryTheory.ObjectProperty.homMk`, `CategoryTheory.ObjectProperty.hom_ext` and
`CategoryTheory.ObjectProperty.ι` — applies to its morphisms directly, and a morphism of
algebraic spaces is a morphism of the underlying presheaves.

Subcanonicity of the big fppf topology is deduced from subcanonicity of the fppf topology on
all schemes: the inclusion of the size-bounded schemes is full and faithful and continuous for
the comparison of the fppf precoverage with its comap, and every covering of the site is an
fppf covering, so the site's topology lies below the comapped one and subcanonicity descends
along `CategoryTheory.GrothendieckTopology.Subcanonical.of_le`. Subcanonicity of the big fppf
site of `S` then follows from the localization instance.

Surjectivity and étaleness of the identity atlas in Tag 025Z are instances of the general fact
that a property of morphisms of the site which holds for isomorphisms is inherited by the
identity of a representable presheaf in the sense of
`CategoryTheory.MorphismProperty.presheaf`; that is `AlgebraicGeometry.presheaf_id_of_iso`.
`CategoryTheory.MorphismProperty.presheaf_id` in
`StacksFrontier/AlgebraicGeometry/Spaces/Representable.lean` is the variant whose hypotheses are
`ContainsIdentities` and `RespectsIso`; neither set of hypotheses implies the other, so both
are kept.

The three conditions of `AlgebraicGeometry.IsAlgebraicSpace` for a fibre product are
discharged separately and each by a statement that is general in the site. The sheaf condition
is an instance of closure of sheaves under limits. Representability of the diagonal is
`CategoryTheory.MorphismProperty.diag_pullback` applied to
`CategoryTheory.Functor.relativelyRepresentable`, which is multiplicative and stable under
base change. The proof of that lemma passes to the relative diagonal, where
`CategoryTheory.MorphismProperty.diagonal` is again multiplicative and stable under base
change: the canonical morphism `X ×_Z Y ⟶ X ×_{⊤} Y` is a monomorphism, so its relative
diagonal is an isomorphism, and the structure morphism of `X ×_Z Y` to the terminal object
factors through it and through the first projection of `X ×_{⊤} Y`, which is a base change of
the structure morphism of `Y`. Note that the diagonal of the base `Z` plays no part. The atlas
is obtained from the atlases of the two factors.

The parent instances of `CategoryTheory.MorphismProperty.IsMultiplicative` are not found by
instance synthesis for `AlgebraicGeometry.Etale` or `AlgebraicGeometry.Surjective`, and
neither is the inverse image of a stable-under-composition property along a functor, so the
structural properties used for the atlas are recorded here as private instances with explicit
proof terms.

`StacksFrontier/AlgebraicGeometry/Spaces/FibreProduct.lean` carries the stronger Tag 04T9, where
the base is only required to be an fppf sheaf with representable diagonal; the 02X2 corollary
`AlgebraicGeometry.isAlgebraicSpace_pullback` is stated here because it is needed by consumers
which do not import that file.

`AlgebraicGeometry.SpacesOverSmallerBase` is the full subcategory of the slice over the
representable presheaf of `S` on those objects whose underlying presheaf is an algebraic space
over `S'`. Morphisms to `S` in the category of algebraic spaces are exactly such objects,
because that category is a full subcategory of presheaves. The equivalence of Tag 04SG between
this category and `AlgebraicGeometry.AlgebraicSpaces` over `S` is **not** here.

`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces` is the presheaf-level notion of
Tag 02YQ. It is not the same as
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` of Tag 02ZW, which is a condition
on a 1-morphism of categories fibred in groupoids. It is defined, with its base-change and
sheaf-descent API, in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces`; consumers
take it from there directly.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 02YQ](https://stacks.math.columbia.edu/tag/02YQ)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

/-! ### Diagonals of fibre products -/

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] [Limits.HasTerminal C] [Limits.HasBinaryProducts C]
  [Limits.HasPullbacks C]

/-- The absolute diagonal of an object lies in a morphism property invariant under
isomorphisms exactly when the relative diagonal of its structure morphism to the terminal
object does. -/
theorem diag_iff_diagonal_terminal (P : MorphismProperty C) [P.RespectsIso] (X : C) :
    P (Limits.diag X) ↔ P.diagonal (terminal.from X) := by
  rw [show Limits.diag X
      = pullback.diagonal (terminal.from X) ≫ (prodIsoPullback X X).inv from by cat_disch,
    P.cancel_right_of_respectsIso]
  rfl

/-- Let `P` be a multiplicative morphism property stable under base change. If the absolute
diagonals of `X` and of `Y` lie in `P`, then so does the absolute diagonal of `X ×_Z Y`,
for every cospan `f : X ⟶ Z`, `g : Y ⟶ Z`. -/
theorem diag_pullback (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (hX : P (Limits.diag X)) (hY : P (Limits.diag Y)) :
    P (Limits.diag (pullback f g)) := by
  let m : pullback f g ⟶ pullback (terminal.from X) (terminal.from Y) :=
    pullback.lift (pullback.fst f g) (pullback.snd f g) (terminal.hom_ext _ _)
  have hm : Mono m := by
    refine ⟨fun {W} a b hab => pullback.hom_ext ?_ ?_⟩
    · simpa [m, pullback.lift_fst] using hab =≫ pullback.fst (terminal.from X) (terminal.from Y)
    · simpa [m, pullback.lift_snd] using hab =≫ pullback.snd (terminal.from X) (terminal.from Y)
  have hmd : P.diagonal m := by
    rw [MorphismProperty.diagonal_iff]
    exact P.of_isIso _
  refine (P.diag_iff_diagonal_terminal _).mpr ?_
  rw [show terminal.from (pullback f g)
      = m ≫ (pullback.fst (terminal.from X) (terminal.from Y) ≫ terminal.from X) from
    terminal.hom_ext _ _]
  exact P.diagonal.comp_mem _ _ hmd (P.diagonal.comp_mem _ _
    (P.diagonal.pullback_fst _ _ ((P.diag_iff_diagonal_terminal Y).mp hY))
    ((P.diag_iff_diagonal_terminal X).mp hX))

end MorphismProperty

/-! ### Initial objects of a slice category -/

namespace Over

/-- An object of a slice category whose underlying object is initial is itself initial. -/
noncomputable def isInitialOfIsInitialLeft {C : Type*} [Category C] {T : C} {Y : Over T}
    (hY : IsInitial Y.left) : IsInitial Y :=
  letI : ∀ Z : Over T, Unique (Y ⟶ Z) := fun Z =>
    { default := Over.homMk (hY.to Z.left) (hY.hom_ext _ _)
      uniq := fun _ => Over.OverMorphism.ext (hY.hom_ext _ _) }
  IsInitial.ofUnique Y

end Over

end CategoryTheory

namespace AlgebraicGeometry

/-! ### Initial objects of a big fppf site -/

/-- An object of a big fppf site whose underlying scheme is initial is initial, the inclusion
into schemes being fully faithful. -/
noncomputable def isInitial_schemeBelow (B : BigFppfSite.{u}) {X : B.Schemes}
    (hX : IsInitial (B.inclusion.obj X)) : IsInitial X :=
  letI : ∀ Y : B.Schemes, Unique (X ⟶ Y) := fun Y =>
    { default := B.inclusion.preimage (hX.to (B.inclusion.obj Y))
      uniq := fun _f => B.inclusion.map_injective (hX.hom_ext _ _) }
  IsInitial.ofUnique X

/-! ### Schemes as algebraic spaces -/

/-- A property of morphisms of the big fppf site which holds for all isomorphisms is inherited,
in the sense of `CategoryTheory.MorphismProperty.presheaf`, by any isomorphism of presheaves. -/
private theorem presheaf_of_isIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (BigFppfOver B S hS))
    (hP : ∀ ⦃X Y⦄ (f : X ⟶ Y), IsIso f → P f) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : X ⟶ Y) [IsIso e] : P.presheaf e := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro A C g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  exact hP snd (Yoneda.fullyFaithful.isIso_of_isIso_map snd)

/-- A property of morphisms of the big fppf site of `S` which holds for all isomorphisms is
inherited, in the sense of `CategoryTheory.MorphismProperty.presheaf`, by the identity of a
representable presheaf. -/
theorem presheaf_id_of_iso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (BigFppfOver B S hS))
    (hP : ∀ ⦃X Y⦄ (f : X ⟶ Y), IsIso f → P f) (T : BigFppfOver B S hS) :
    P.presheaf (𝟙 (yoneda.obj T)) :=
  presheaf_of_isIso B S hS P hP _

/-- **Stacks 025Z.** The representable presheaf of a scheme over `S` is an algebraic space
over `S`. -/
@[stacks 025Z]
theorem isAlgebraicSpace_yoneda (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) : IsAlgebraicSpace B S hS (yoneda.obj T) := by
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  have hSheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj T) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type
      (J := BigFppfOver.topology B S hS) (yoneda.obj T)).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := BigFppfOver.topology B S hS) (yoneda.obj T))
  let _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hDiag : yoneda.relativelyRepresentable (diag (yoneda.obj T)) := by
    apply (Functor.relativelyRepresentable.diag_iff
      (F := yoneda) (X := yoneda.obj T)).2
    intro U g
    simpa using Functor.relativelyRepresentable.map yoneda (yoneda.preimage g)
  refine ⟨hSheaf, hDiag, T, 𝟙 (yoneda.obj T), ?_, ?_⟩
  all_goals
    refine presheaf_id_of_iso B S hS _ (fun X Y f _ => ?_) T
    dsimp only [MorphismProperty.inverseImage]
    infer_instance

/-! ### The category of algebraic spaces -/

/-- **Stacks 02X2.** The category of algebraic spaces over a scheme `S` of a big fppf site:
the full subcategory of presheaves on the big fppf site of `S` whose objects are algebraic
spaces over `S`. -/
@[stacks 02X2 "the category of algebraic spaces over the base"]
abbrev AlgebraicSpaces (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :=
  ObjectProperty.FullSubcategory
    (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)

/-- **The algebraic space represented by an object of the big fppf site**, i.e. Stacks 025Z
packaged as an object of `AlgebraicGeometry.AlgebraicSpaces`.

The canonical home for this one-line wrapper: it sits beside
`AlgebraicGeometry.isAlgebraicSpace_yoneda`, which every consumer of the wrapper already uses,
so no consumer needs a new import. -/
public noncomputable abbrev yonedaSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (T : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩

/-- **Stacks 04SG.** For a morphism `g : S ⟶ S'` of a big fppf site, the category of
algebraic spaces over `S'` endowed with a morphism to the representable algebraic space of
`S`. -/
@[stacks 04SG "the category of algebraic spaces with a morphism to the smaller base"]
abbrev SpacesOverSmallerBase (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS') :=
  ObjectProperty.FullSubcategory
    (fun X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) =>
      IsAlgebraicSpace B S' hS' X.left)

/-- The structural morphism to `U` of an algebraic space over `U`, read as a morphism of
algebraic spaces over `S`. -/
abbrev algebraicSpaceMap (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (Fy : SpacesOverSmallerBase B U.left.1 S U.left.2 hS U.hom) :
    (⟨Fy.1.left, Fy.property⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩ :
        AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk Fy.1.hom

/-! ### Fibre products -/

section FibreProduct

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! #### Structural properties of the representable surjective and étale properties -/

/-- Surjective morphisms of schemes are stable under composition. -/
@[ega "I 2.2.7"]
private instance surjectiveIsStableUnderComposition : MorphismProperty.IsStableUnderComposition
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Morphisms of the big fppf site of `S` with surjective underlying scheme morphism are
stable under composition. -/
public instance siteSurjectiveIsStableUnderComposition :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage _

/-- Morphisms of the big fppf site of `S` with étale underlying scheme morphism are stable
under composition. -/
public instance siteEtaleIsStableUnderComposition :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage _

/-- The representable surjective property of morphisms of presheaves on the big fppf site
of `S` is stable under base change. -/
private instance presheafSurjectiveIsStableUnderBaseChange :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- The representable étale property of morphisms of presheaves on the big fppf site of `S`
is stable under base change. -/
private instance presheafEtaleIsStableUnderBaseChange :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-! #### The presheaf fibre product of algebraic spaces -/

/-- **Stacks 02X2.** The presheaf fibre product of two algebraic spaces over an algebraic
space is an algebraic space. -/
@[stacks 02X2 "algebraicity of the fibre product"]
theorem isAlgebraicSpace_pullback {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) :
    IsAlgebraicSpace B S hS (pullback f g) where
  isSheaf :=
    Presheaf.isSheaf_pullback _ f g hF.isSheaf hG.isSheaf hH.isSheaf
  diagonal_representable :=
    MorphismProperty.diag_pullback yoneda.relativelyRepresentable f g
      hF.diagonal_representable hG.diagonal_representable
  exists_atlas := by
    obtain ⟨U, a, haS, haE⟩ := hF.exists_atlas
    obtain ⟨V, b, hbS, hbE⟩ := hG.exists_atlas
    let _ : HasBinaryProducts (BigFppfOver B S hS) :=
      hasBinaryProducts_of_hasTerminal_and_pullbacks _
    have hrep : yoneda.relativelyRepresentable (a ≫ f) :=
      Functor.relativelyRepresentable.of_diag hH.diagonal_representable (a ≫ f)
    refine ⟨hrep.pullback (b ≫ g), (hrep.isPullback (b ≫ g)).isoPullback.hom ≫
      pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 H) (by simp) (by simp), ?_, ?_⟩
    · exact MorphismProperty.RespectsIso.precomp _ _ _
        (MorphismProperty.pullbackMap haS hbS rfl rfl)
    · exact MorphismProperty.RespectsIso.precomp _ _ _
        (MorphismProperty.pullbackMap haE hbE rfl rfl)

namespace Space

/-- An isomorphism of presheaves on the big fppf site of `S` is an étale chart: every
represented base change of it is an isomorphism of schemes, hence étale. -/
theorem presheaf_etale_of_iso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ Y) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e.hom := by
  refine presheaf_of_isIso B S hS _ (fun X Y f _ => ?_) e.hom
  dsimp only [MorphismProperty.inverseImage]
  infer_instance

/-- The algebraic space over `S` represented by an object of the big fppf site of `S`: its
underlying presheaf is syntactically the presheaf the scheme represents. -/
abbrev representedAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩

end Space

namespace AlgebraicSpaces

/-- The algebraic space whose underlying presheaf is the presheaf fibre product. -/
noncomputable def fiberProduct {F G H : AlgebraicSpaces B S hS} (f : F ⟶ H) (g : G ⟶ H) :
    AlgebraicSpaces B S hS :=
  ⟨pullback f.hom g.hom,
    isAlgebraicSpace_pullback B S hS f.hom g.hom F.property G.property H.property⟩

/-- **Stacks 02X2.** The presheaf fibre product of two algebraic spaces is a fibre product
in the category of algebraic spaces over the base. -/
@[stacks 02X2 "universal property among algebraic spaces"]
theorem isPullback_fiberProduct {F G H : AlgebraicSpaces B S hS} (f : F ⟶ H) (g : G ⟶ H) :
    IsPullback (ObjectProperty.homMk (pullback.fst f.hom g.hom) : fiberProduct B S hS f g ⟶ F)
      (ObjectProperty.homMk (pullback.snd f.hom g.hom) : fiberProduct B S hS f g ⟶ G) f g :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ pullback.condition)
    (by simpa [fiberProduct] using IsPullback.of_hasPullback f.hom g.hom)

/-- A cartesian square in the category of algebraic spaces over `S` is cartesian as a square
of presheaves on the big fppf site of `S`, that category having its fibre products computed
in presheaves. -/
theorem isPullback_hom {F G H P : AlgebraicSpaces B S hS} {f : F ⟶ H} {g : G ⟶ H}
    {fst : P ⟶ F} {snd : P ⟶ G} (sq : IsPullback fst snd f g) :
    IsPullback fst.hom snd.hom f.hom g.hom := by
  have c := isPullback_fiberProduct B S hS f g
  let e := c.isoIsPullback F G sq
  exact IsPullback.of_iso_pullback ⟨congrArg (fun k => k.hom) sq.w⟩
    { hom := e.inv.hom, inv := e.hom.hom,
      hom_inv_id := congrArg (fun k => k.hom) e.inv_hom_id,
      inv_hom_id := congrArg (fun k => k.hom) e.hom_inv_id }
    (congrArg (fun k => k.hom) (c.isoIsPullback_inv_fst F G sq))
    (congrArg (fun k => k.hom) (c.isoIsPullback_inv_snd F G sq))

/-- Any two morphisms of algebraic spaces with a common target have a fibre product. -/
instance hasPullback {F G H : AlgebraicSpaces B S hS} (f : F ⟶ H) (g : G ⟶ H) :
    HasPullback f g :=
  (isPullback_fiberProduct B S hS f g).hasPullback

/-- The category of algebraic spaces over a scheme has fibre products: they are the presheaf
fibre products, which are again algebraic spaces. -/
@[stacks 043C "fibre products of algebraic spaces"]
instance hasPullbacks : HasPullbacks (AlgebraicSpaces B S hS) :=
  hasPullbacks_of_hasLimit_cospan _

end AlgebraicSpaces

end FibreProduct

end AlgebraicGeometry

end
