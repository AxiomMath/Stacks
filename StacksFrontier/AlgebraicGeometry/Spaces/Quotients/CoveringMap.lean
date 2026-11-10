module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PreEquivalenceRelation
public import Mathlib.CategoryTheory.Sites.LocallyBijective
-- for `AlgebraicGeometry.Space.exists_point_lift_of_sieve_mem`, used in a proof below; not
-- `public`, since no statement of this module mentions it
import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FinitenessConditions

/-!
# The covering map of a quotient algebraic space

Let `j : R ⟶ U ×_Z U` be a pre-relation of presheaves on the big fppf site of `S` and let
`U/R` be its quotient sheaf (Stacks 044J). This file proves the three properties of the
canonical map `U ⟶ U/R` that Stacks 06PG asserts.

Surjectivity holds for every pre-relation: the quotient map is a surjection of fppf sheaves,
and an fppf-locally surjective map of presheaves is surjective on the points of Stacks 03BU.

Flatness and local finite presentation need the relation to be an equivalence relation. Then
`R` *is* the fibre square `U ×_{U/R} U`, by Stacks 046O together with monicity of `j`, so
every base change of `U ⟶ U/R` along a chart of `U/R` is, locally on that chart, a base
change of the target map `t : R ⟶ U`. Both properties are étale local on the source and
target and local at the target for the fpqc topology, so this is enough.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_toQuotientSheaf`: the quotient map is a
  surjection of fppf sheaves.
* `AlgebraicGeometry.Space.isPullback_toQuotientSheaf`: for an equivalence relation, the
  square cut out by the source and the target of `j` is the fibre square of the quotient map
  with itself, which is `R = U ×_{U/R} U`.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_toQuotientSheaf`: an étale-local property
  of morphisms of schemes which the target map of the relation has, and which is local at the
  target for the fpqc topology, is inherited by the quotient map.
* `AlgebraicGeometry.Space.isSurjective_toQuotientSheaf`,
  `AlgebraicGeometry.Space.isFlat_toQuotientSheaf` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_toQuotientSheaf`: **Stacks 06PG**,
  the three properties of the covering map of a quotient algebraic space.

## Implementation notes

The three tagged statements are weaker in their hypotheses than Stacks 06PG. Surjectivity is
proved for an arbitrary pre-relation of presheaves, with no groupoid, no equivalence relation
and no algebraicity. Flatness and local finite presentation each use only the corresponding
property of the *target* map of the groupoid; the source map enters the source's proof only
through the symmetry of the relation, which is already part of the equivalence-relation
hypothesis. The algebraic-space hypothesis is imposed on the quotient sheaf itself rather
than on an isomorphic copy, since the conclusion is about the canonical map into it.

`AlgebraicGeometry.Space.isPullback_toQuotientSheaf` asks only that `R` and `U` be fppf
sheaves, not that they be algebraic spaces: the comparison map `R ⟶ U ×_{U/R} U` is locally
surjective by Stacks 046O and locally injective because `j` is a monomorphism, hence an
isomorphism of sheaves, and the sheaf condition is all that is needed to pass between the
two categories.

Local surjectivity of the unit of sheafification is not an instance at these universes,
because the big fppf site has objects one universe above its morphisms; as with its local
injectivity in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Quotient/PreEquivalenceRelation.lean`, it
follows from the site being essentially small.

Monicity of the comparison map runs on the slice of presheaves rather than on the category of
algebraic spaces, where two maps out of a test presheaf into `R` which agree after the source
and the target of `j` are packaged as maps over `Z` and separated by the product projections.
This is `AlgebraicGeometry.Space.eq_of_comp_source_eq_of_comp_target_eq`, and it is the only
place monicity of `j` is used.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 046O](https://stacks.math.columbia.edu/tag/046O)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 06PG](https://stacks.math.columbia.edu/tag/06PG)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}

/-! ### Surjectivity of the quotient map -/

/-- The unit of sheafification on the big fppf site is locally surjective. This is not
available as an instance at these universes, and follows from the site being essentially
small. -/
theorem isLocallySurjective_toSheafify_bigFppfOver
    (J : GrothendieckTopology (BigFppfOver site S hS)) [HasWeakSheafify J (Type u)]
    (P : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u) :
    Presheaf.IsLocallySurjective J (toSheafify J P) := by
  have : EssentiallySmall.{u} (BigFppfOver site S hS) := essentiallySmall_bigFppfOver site S hS
  let : J.WEqualsLocallyBijective (Type u) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  exact (J.W_toSheafify P).isLocallySurjective

/-- The relative version, over yoneda, of the inverse image under `BigFppfOver.toScheme` of a
base-change stable property of schemes is stable under base change. -/
private theorem presheaf_inverseImage_isStableUnderBaseChange {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderBaseChange) :
    (P.inverseImage (BigFppfOver.toScheme site S hS)).presheaf.IsStableUnderBaseChange :=
  have := inverseImage_isStableUnderBaseChange site S hS hP
  MorphismProperty.relative_isStableUnderBaseChange _

/-- The relative version, over yoneda, of the inverse image under `BigFppfOver.toScheme` of a
composition stable property of schemes is stable under composition. -/
private theorem presheaf_inverseImage_isStableUnderComposition {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderComposition) :
    (P.inverseImage (BigFppfOver.toScheme site S hS)).presheaf.IsStableUnderComposition :=
  have := inverseImage_isStableUnderComposition site S hS hP
  MorphismProperty.relative_isStableUnderComposition _

variable {Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}
  [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

/-- The quotient map of a pre-relation is a surjection of fppf sheaves: it is the coequalizer
projection onto the quotient presheaf, which is surjective on sections, followed by the unit
of sheafification. -/
theorem isLocallySurjective_toQuotientSheaf (j : PreRelation R U) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology site S hS) (toQuotientSheaf j) := by
  have h1 : Presheaf.IsLocallySurjective (BigFppfOver.topology site S hS)
      (coequalizer.π j.target.left j.source.left) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun X =>
      (CategoryTheory.epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app _).1 inferInstance X)
  -- Both factors are passed positionally: local surjectivity of the sheafification unit is
  -- not an instance at these universes, so it has to be handed to the composition lemma.
  exact @Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1
    (isLocallySurjective_toSheafify_bigFppfOver (BigFppfOver.topology site S hS)
      (quotientPresheaf j))

/-- **Stacks 06PG.** The object presheaf of a pre-relation surjects onto its quotient sheaf.

A point of the quotient is represented by a section over the spectrum of a field in the site;
the quotient map is a surjection of fppf sheaves, so that section lifts to `U` on a covering,
and the spectrum of a residue field of a member of the covering is again an object of the
site and gives a field-valued point of `U` dominating the original one.

This also discharges the surjectivity clause of **Stacks 06PH**, that `X ⟶ X/G` is surjective
for a free action of a group algebraic space: the quotient `X/G` of [Stacks, Tag 044J] is the
quotient sheaf of the pre-relation of the action, so that clause is this lemma at that
pre-relation. It is stated here for an arbitrary pre-relation, which is more general and uses
neither freeness of the action nor flatness of `G ⟶ B`; the remaining clauses of Stacks 06PH —
algebraicity of `X/G`, flatness and local finite presentation of `X ⟶ X/G`, and the fppf
torsor property — are not proved here and nothing in this file assumes them. -/
@[stacks 06PG "surjectivity",
  stacks 06PH "surjectivity of the quotient map, for an arbitrary pre-relation"]
theorem isSurjective_toQuotientSheaf (j : PreRelation R U) :
    IsSurjective site S hS (toQuotientSheaf j) := by
  classical
  intro x
  induction x using Quot.inductionOn with
  | h p =>
    let T := p.siteObject
    have := isLocallySurjective_toQuotientSheaf j
    have hcover : Presheaf.imageSieve (toQuotientSheaf j) p.value ∈
        BigFppfOver.topology site S hS T :=
      Presheaf.imageSieve_mem _ (toQuotientSheaf j) p.value
    obtain ⟨V, g, z, ⟨a, hva⟩, -⟩ :=
      exists_point_lift_of_sieve_mem site S hS hcover (IsLocalRing.closedPoint p.carrier)
    obtain ⟨κ, instκ, hκ, ρ, -⟩ :=
      exists_fieldSpec_at_point site (X := (BigFppfOver.toScheme site S hS).obj V)
        V.left.2 z
    let i : site.obj hκ ⟶ V.left := ⟨ρ⟩
    let r : BigFppfOver site S hS := Over.mk (i ≫ V.hom)
    let i' : r ⟶ V := Over.homMk i
    let m : r ⟶ T := i' ≫ g
    refine ⟨FieldValuedPoint.class site S hS U.left
      { carrier := κ
        contained := hκ
        toBase := ρ ≫ site.inclusion.map V.hom
        value := U.left.map i'.op a }, ?_⟩
    rw [pointsMap_class]
    apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
    refine ⟨_, FieldValuedPoint.dominates_refl _ _ _ _ _, m, ?_⟩
    change (quotientSheaf j).obj.map m.op p.value =
      (toQuotientSheaf j).app (op r) (U.left.map i'.op a)
    calc (quotientSheaf j).obj.map m.op p.value
        = (quotientSheaf j).obj.map i'.op ((quotientSheaf j).obj.map g.op p.value) := by
          rw [show m.op = g.op ≫ i'.op from rfl, Functor.map_comp]
          rfl
      _ = (quotientSheaf j).obj.map i'.op ((toQuotientSheaf j).app (op V) a) := by rw [hva]
      _ = (toQuotientSheaf j).app (op r) (U.left.map i'.op a) :=
          (NatTrans.naturality_apply (toQuotientSheaf j) i'.op a).symm

/-! ### The relation as the fibre square of the quotient map -/

omit [HasSheafify (BigFppfOver.topology site S hS) (Type u)] in
/-- Two maps into the source of a *relation* which agree after both the source and the target
of the relation are equal: packaged as maps over the base, they are separated by the two
projections of the product. -/
theorem eq_of_comp_source_eq_of_comp_target_eq {j : PreRelation R U} [Mono j]
    {W : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {a b : W ⟶ R.left}
    (hs : a ≫ j.source.left = b ≫ j.source.left)
    (ht : a ≫ j.target.left = b ≫ j.target.left) : a = b := by
  have hb : b ≫ R.hom = a ≫ R.hom := by
    rw [← Over.w j.source, ← Category.assoc, ← hs, Category.assoc, Over.w j.source]
  let aa : Over.mk (a ≫ R.hom) ⟶ R := Over.homMk a
  let bb : Over.mk (a ≫ R.hom) ⟶ R := Over.homMk b hb
  have he : aa ≫ j = bb ≫ j :=
    prod.hom_ext (Over.OverMorphism.ext (by simpa [aa, bb, PreRelation.target] using ht))
      (Over.OverMorphism.ext (by simpa [aa, bb, PreRelation.source] using hs))
  exact congrArg (fun k : Over.mk (a ≫ R.hom) ⟶ R => k.left) ((cancel_mono j).mp he)

/-- **Stacks 06PG.** For an equivalence relation the square cut out by the source and the
target of the relation is the fibre square of the quotient map with itself: `R = U ×_{U/R} U`.

The comparison map `R ⟶ U ×_{U/R} U` is locally surjective by Stacks 046O and injective on
sections because the relation is a monomorphism, so it is an isomorphism of fppf sheaves. -/
theorem isPullback_toQuotientSheaf (j : PreRelation R U)
    (hj : CategoryTheory.IsEquivalenceRelation j.target j.source)
    (hR : Presheaf.IsSheaf (BigFppfOver.topology site S hS) R.left)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology site S hS) U.left) :
    IsPullback j.source.left j.target.left (toQuotientSheaf j) (toQuotientSheaf j) := by
  let J := BigFppfOver.topology site S hS
  obtain ⟨_, hpre⟩ :=
    (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp hj
  let lift := pullback.lift j.source.left j.target.left
    (target_toQuotientSheaf_eq_source j).symm
  have hlift : Mono lift := ⟨fun a b hab => eq_of_comp_source_eq_of_comp_target_eq (j := j)
    (by simpa only [lift, Category.assoc, pullback.lift_fst] using hab =≫ pullback.fst _ _)
    (by simpa only [lift, Category.assoc, pullback.lift_snd] using hab =≫ pullback.snd _ _)⟩
  let liftSheaf : (⟨R.left, hR⟩ : Sheaf J (Type u)) ⟶
      ⟨pullback (toQuotientSheaf j) (toQuotientSheaf j),
        Presheaf.isSheaf_pullback J (toQuotientSheaf j) (toQuotientSheaf j) hU hU
          (quotientSheaf j).property⟩ :=
    ⟨lift⟩
  have _ : Presheaf.IsLocallySurjective J lift :=
    isLocallySurjective_relationToQuotientPullback j hpre
  have _ : Presheaf.IsLocallyInjective J lift :=
    Presheaf.isLocallyInjective_of_injective J lift (fun T =>
      (CategoryTheory.mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app lift).mp hlift T))
  have _ : IsIso liftSheaf :=
    (Sheaf.isLocallyBijective_iff_isIso liftSheaf).mp ⟨inferInstance, inferInstance⟩
  have _ : IsIso lift := (sheafToPresheaf J (Type u)).map_isIso liftSheaf
  exact IsPullback.of_iso_pullback ⟨(target_toQuotientSheaf_eq_source j).symm⟩
    (asIso lift) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-! ### Étale-local properties of the quotient map -/

omit [HasSheafify (BigFppfOver.topology site S hS) (Type u)] in
/-- An étale chart of a presheaf over a representable one, base changed along a morphism of
the site, inherits an every-étale-chart property of the second leg of the given fibre square.

This is the step that turns a fibre square of presheaves into a statement about a fibre
product of schemes: the base change of the chart along the morphism of the site is again a
chart of the fibre square's source, so the property holds of it, and the fibre product of
schemes is identified with the image of the fibre product taken in the site. -/
private theorem holdsOnEveryEtaleChart_pullbackSnd_of_isPullback
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {A V W : BigFppfOver site S hS}
    {f : X ⟶ yoneda.obj V} {m : Y ⟶ X} {n : Y ⟶ yoneda.obj W} {k : W ⟶ V}
    (sq : IsPullback m n f (yoneda.map k))
    (hn : HoldsOnEveryEtaleChart site S hS P n)
    (a : yoneda.obj A ⟶ X) (h : A ⟶ V)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme site S hS)).presheaf a)
    (comm : yoneda.map h = a ≫ f) :
    P (pullback.snd ((BigFppfOver.toScheme site S hS).map h)
      ((BigFppfOver.toScheme site S hS).map k)) := by
  let T := BigFppfOver.toScheme site S hS
  let E := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  have _ : E.presheaf.IsStableUnderBaseChange :=
    presheaf_inverseImage_isStableUnderBaseChange Etale.etale_isStableUnderBaseChange
  let r := pullback.fst h k
  let s := pullback.snd h k
  let p : yoneda.obj (pullback h k) ⟶ Y :=
    sq.lift (yoneda.map r ≫ a) (yoneda.map s)
      (by rw [Category.assoc, ← comm, ← yoneda.map_comp, pullback.condition, yoneda.map_comp])
  have hp₂ : p ≫ n = yoneda.map s := sq.lift_snd _ _ _
  have houter : IsPullback (p ≫ n) (yoneda.map r) (yoneda.map k) (a ≫ f) := by
    rw [hp₂, ← comm]
    exact ((IsPullback.of_hasPullback h k).map yoneda).flip
  have hchart : E.presheaf p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (houter.of_right (sq.lift_fst _ _ _) sq.flip).flip ha
  have hid : E.presheaf (𝟙 (yoneda.obj W)) := by
    have hh : E (𝟙 W) := by
      change AlgebraicGeometry.Etale (T.map (𝟙 W))
      infer_instance
    simpa using MorphismProperty.relative_map (F := yoneda) (P := E) hh
  have hsq := (IsPullback.of_hasPullback h k).map T
  let e := (IsPullback.of_hasPullback (T.map h) (T.map k)).isoIsPullback _ _ hsq
  have he : e.hom ≫ T.map s = pullback.snd (T.map h) (T.map k) :=
    (IsPullback.of_hasPullback (T.map h) (T.map k)).isoIsPullback_hom_snd _ _ hsq
  exact he ▸ (P.cancel_left_of_respectsIso e.hom (T.map s)).mpr
    (hn (pullback h k) W p (𝟙 _) s hchart hid (by simpa using hp₂.symm))

/-- Let `b` be a chart of the quotient sheaf and `a` an étale chart of `U ×_{U/R} V` above it.
Over a morphism `k : W ⟶ V` along which `b` lifts to `U`, the base change of the projection
of `a` to `V` inherits a property of morphisms of schemes which holds on every étale chart of
the target map of the relation: there the base change of the quotient map is a base change of
the target map. -/
private theorem holdsOnEveryEtaleChart_pullbackSnd_of_mem_imageSieve (j : PreRelation R U)
    (hR : IsAlgebraicSpace site S hS R.left) (hU : IsAlgebraicSpace site S hS U.left)
    (hpull : IsPullback j.source.left j.target.left (toQuotientSheaf j) (toQuotientSheaf j))
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hbc : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces site S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart site S hS P f.hom))
    (ht : HoldsOnEveryEtaleChart site S hS P j.target.left)
    {A V W : BigFppfOver site S hS} {b : yoneda.obj V ⟶ (quotientSheaf j).obj}
    (a : yoneda.obj A ⟶ pullback (toQuotientSheaf j) b)
    (haE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme site S hS)).presheaf a)
    {h : A ⟶ V} (hh : yoneda.map h = a ≫ pullback.snd (toQuotientSheaf j) b) {k : W ⟶ V}
    (hk : Presheaf.imageSieve (toQuotientSheaf j) (yonedaEquiv b) k) :
    P (pullback.snd ((BigFppfOver.toScheme site S hS).map h)
      ((BigFppfOver.toScheme site S hS).map k)) := by
  obtain ⟨l, hl⟩ := hk
  let lift : yoneda.obj W ⟶ U.left := yonedaEquiv.symm l
  have hlift : lift ≫ toQuotientSheaf j = yoneda.map k ≫ b := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, yonedaEquiv_comp]
    simpa only [lift, Equiv.apply_symm_apply] using hl
  let Rsp : AlgebraicSpaces site S hS := ⟨R.left, hR⟩
  let Usp : AlgebraicSpaces site S hS := ⟨U.left, hU⟩
  let Wsp : AlgebraicSpaces site S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda site S hS W⟩
  let tsp : Rsp ⟶ Usp := ObjectProperty.homMk j.target.left
  let lsp : Wsp ⟶ Usp := ObjectProperty.homMk lift
  have hbase : HoldsOnEveryEtaleChart site S hS P (pullback.snd j.target.left lift) :=
    hbc.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct site S hS tsp lsp) ht
  have hsq : IsPullback
      (pullback.fst j.target.left lift ≫ j.source.left)
      (pullback.snd j.target.left lift) (toQuotientSheaf j) (yoneda.map k ≫ b) := by
    rw [← hlift]
    exact (IsPullback.of_hasPullback j.target.left lift).paste_horiz hpull
  let m := pullback.lift
    (pullback.fst j.target.left lift ≫ j.source.left)
    (pullback.snd j.target.left lift ≫ yoneda.map k)
    (by simpa only [Category.assoc] using hsq.w)
  have hsq' : IsPullback m (pullback.snd j.target.left lift)
      (pullback.snd (toQuotientSheaf j) b) (yoneda.map k) := by
    have houter : IsPullback (m ≫ pullback.fst (toQuotientSheaf j) b)
        (pullback.snd j.target.left lift) (toQuotientSheaf j) (yoneda.map k ≫ b) := by
      simpa only [m, pullback.lift_fst] using hsq
    exact houter.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ b)
  exact holdsOnEveryEtaleChart_pullbackSnd_of_isPullback P hsq' hbase a h haE hh

/-- Let `j` be an equivalence relation, `b` a chart of its quotient sheaf and `a` an étale
chart of `U ×_{U/R} V` above it. A property of morphisms of schemes which is local at the
target for the fpqc topology and holds on every étale chart of the target map of the relation
holds of the projection of `a` to `V`: it holds over a covering of `V` on which `b` lifts. -/
private theorem toScheme_map_of_comp_pullbackSnd_toQuotientSheaf (j : PreRelation R U)
    (hj : CategoryTheory.IsEquivalenceRelation j.target j.source)
    (hR : IsAlgebraicSpace site S hS R.left) (hU : IsAlgebraicSpace site S hS U.left)
    (P : MorphismProperty Scheme.{u}) [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    (hbc : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces site S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart site S hS P f.hom))
    (ht : HoldsOnEveryEtaleChart site S hS P j.target.left)
    {A V : BigFppfOver site S hS} {b : yoneda.obj V ⟶ (quotientSheaf j).obj}
    (a : yoneda.obj A ⟶ pullback (toQuotientSheaf j) b)
    (haE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme site S hS)).presheaf a)
    {h : A ⟶ V} (hh : yoneda.map h = a ≫ pullback.snd (toQuotientSheaf j) b) :
    P ((BigFppfOver.toScheme site S hS).map h) := by
  have := isLocallySurjective_toQuotientSheaf j
  obtain ⟨E, hE, hle⟩ := exists_fppf_hypercover_refining_sieve hS V
    (Presheaf.imageSieve (toQuotientSheaf j) (yonedaEquiv b))
    (Presheaf.imageSieve_mem (BigFppfOver.topology site S hS) (toQuotientSheaf j) (yonedaEquiv b))
  have hcov : ((E.map (BigFppfOver.forget site S hS)).map site.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme site S hS).obj V) := by
    simpa [IsFppfCovering, Scheme.fppfPrecoverage, PreZeroHypercover.presieve₀_map]
      using site.isFppfCovering_of_isCovering hE
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := P) (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hcov)
  rintro _ _ _ ⟨i⟩
  exact holdsOnEveryEtaleChart_pullbackSnd_of_mem_imageSieve j hR hU
    (isPullback_toQuotientSheaf j hj hR.isSheaf hU.isSheaf) P hbc ht a haE hh
    (hle _ _ (Presieve.ofArrows.mk i))

/-- **Stacks 06PG.** Let `j` be an equivalence relation whose quotient sheaf is an algebraic
space. A property of morphisms of schemes which is étale local on the source and target, and
local at the target for the fpqc topology, is inherited by the quotient map `U ⟶ U/R` from
the target map of the relation.

Since `R = U ×_{U/R} U` by `AlgebraicGeometry.Space.isPullback_toQuotientSheaf`, pulling the
quotient map back along a chart of `U/R` gives, after refining that chart by an fppf covering
on which it lifts to `U`, a base change of the target map of the relation. Locality at the
target assembles those pieces, and Stacks 03MJ upgrades the one resulting surjective chart
square to every chart square. -/
theorem holdsOnEveryEtaleChart_toQuotientSheaf (j : PreRelation R U)
    (hj : CategoryTheory.IsEquivalenceRelation j.target j.source)
    (hR : IsAlgebraicSpace site S hS R.left) (hU : IsAlgebraicSpace site S hS U.left)
    (hF : IsAlgebraicSpace site S hS (quotientSheaf j).obj)
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    (hbc : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces site S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart site S hS P f.hom))
    (ht : HoldsOnEveryEtaleChart site S hS P j.target.left) :
    HoldsOnEveryEtaleChart site S hS P (toQuotientSheaf j) := by
  let q := toQuotientSheaf j
  let T := BigFppfOver.toScheme site S hS
  let Et := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  let Su := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) T
  have _ : Et.presheaf.IsStableUnderBaseChange :=
    presheaf_inverseImage_isStableUnderBaseChange Etale.etale_isStableUnderBaseChange
  have _ : Su.presheaf.IsStableUnderBaseChange :=
    presheaf_inverseImage_isStableUnderBaseChange inferInstance
  have _ : Et.presheaf.IsStableUnderComposition :=
    presheaf_inverseImage_isStableUnderComposition etale_isStableUnderComposition.{u}
  have _ : Su.presheaf.IsStableUnderComposition :=
    presheaf_inverseImage_isStableUnderComposition
      surjective_isStableUnderComposition.{u}
  -- A chart `b` of the quotient, and a chart `a` of `U ×_{U/R} V` above it.
  obtain ⟨V, b, hbS, hbE⟩ := hF.exists_atlas
  obtain ⟨A, a, haS, haE⟩ := (isAlgebraicSpace_pullback site S hS q b hU
    (isAlgebraicSpace_yoneda site S hS V) hF).exists_atlas
  let h : A ⟶ V := yoneda.preimage (a ≫ pullback.snd q b)
  have hh : yoneda.map h = a ≫ pullback.snd q b := yoneda.map_preimage _
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart site S hS P hP hU hF q).mpr
    ⟨A, V, a ≫ pullback.fst q b, b, h, ?_, hbE, ?_, ?_,
      toScheme_map_of_comp_pullbackSnd_toQuotientSheaf j hj hR hU P hbc ht a haE hh⟩
  · exact Et.presheaf.comp_mem _ _ haE
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback q b).flip hbE)
  · exact Su.presheaf.comp_mem _ _ haS
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback q b).flip hbS)
  · simp only [hh, Category.assoc, pullback.condition]

/-! ### Flatness and local finite presentation of the quotient map of a groupoid -/

variable {B : AlgebraicSpaces site S hS} (G : GroupoidInAlgebraicSpaces site S hS B)

/-- **Stacks 06PG.** The object space of a groupoid in algebraic spaces is flat over its
sheaf quotient, as soon as that quotient is an algebraic space, the relation cut out by the
groupoid is an equivalence relation and the target map of the groupoid is flat. -/
@[stacks 06PG "flatness"]
theorem isFlat_toQuotientSheaf
    (hrel : CategoryTheory.IsEquivalenceRelation
      (groupoidPreRelation G).target (groupoidPreRelation G).source)
    (hF : IsAlgebraicSpace site S hS (quotientSheaf (groupoidPreRelation G)).obj)
    (ht : IsFlat site S hS G.target.hom) :
    IsFlat site S hS (toQuotientSheaf (groupoidPreRelation G)) :=
  holdsOnEveryEtaleChart_toQuotientSheaf (groupoidPreRelation G) hrel
    G.arrows.property G.objects.property hF
    (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    Flat.isEtaleLocalOnSourceAndTarget
    (holdsOnEveryEtaleChart_isStableUnderBaseChange site S hS
      (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
      Flat.isEtaleLocalOnSourceAndTarget)
    (by simpa [groupoidPreRelation, PreRelation.target] using ht)

/-- **Stacks 06PG.** The object space of a groupoid in algebraic spaces is locally of finite
presentation over its sheaf quotient, as soon as that quotient is an algebraic space, the
relation cut out by the groupoid is an equivalence relation and the target map of the groupoid
is locally of finite presentation. -/
@[stacks 06PG "local finite presentation"]
theorem isLocallyOfFinitePresentation_toQuotientSheaf
    (hrel : CategoryTheory.IsEquivalenceRelation
      (groupoidPreRelation G).target (groupoidPreRelation G).source)
    (hF : IsAlgebraicSpace site S hS (quotientSheaf (groupoidPreRelation G)).obj)
    (ht : IsLocallyOfFinitePresentation site S hS G.target.hom) :
    IsLocallyOfFinitePresentation site S hS (toQuotientSheaf (groupoidPreRelation G)) :=
  holdsOnEveryEtaleChart_toQuotientSheaf (groupoidPreRelation G) hrel
    G.arrows.property G.objects.property hF
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    (holdsOnEveryEtaleChart_isStableUnderBaseChange site S hS
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget)
    (by simpa [groupoidPreRelation, PreRelation.target] using ht)

end AlgebraicGeometry.Space

end
