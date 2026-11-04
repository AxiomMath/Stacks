module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective

/-!
# Descending an invariant subscheme of an atlas to a subspace of the quotient

Let `R ⇉ U` be an étale equivalence relation on a scheme over `S` in the big fppf site of `S`,
and let `X = U/R` be its quotient, presented by a surjective étale atlas `U ⟶ X`. An *invariant
locally closed subscheme* of `U` is a subobject of `U` in schemes whose inclusion is an
immersion and which is invariant for the canonical groupoid scheme of the relation. This file
builds the descent of such a subscheme to a subfunctor of `X` and proves the characterising
property: pulling the descended subfunctor back along the atlas returns exactly the functor of
points of the subscheme.

## Main definitions

* `AlgebraicGeometry.Space.sitePreRelation`: the pre-relation on schemes over `S` induced by a
  pair of arrows of the big fppf site over `S`.
* `AlgebraicGeometry.Space.relationGroupoid`: the canonical groupoid scheme extending that
  pre-relation.
* `AlgebraicGeometry.Space.GroupoidInvariantLocallyClosedSubscheme`: locally closed subschemes
  of the presenting scheme, invariant for the canonical groupoid of the relation. This is a
  different condition from `AlgebraicGeometry.Space.InvariantLocallyClosedSubscheme`, which
  states invariance against a presentation rather than against that groupoid.
* `AlgebraicGeometry.Space.descendedInvariantSubfunctor`: the descent of an invariant
  subscheme, the sheafification of the image of its points along the atlas.

The functor of points of a subobject of a scheme of the site,
`AlgebraicGeometry.Space.subschemePoints`, and the subtype of locally closed subspaces of the
quotient, `AlgebraicGeometry.Space.LocallyClosedQuotientSubspace`, are imported from
`StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace`, as is the behaviour of the former
under pullback, `AlgebraicGeometry.Space.subschemePoints_pullback`, from
`StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection`.

## Main results

* `AlgebraicGeometry.Space.descendedInvariantSubfunctor_preimage`: the descended subfunctor
  pulls back along the atlas to the functor of points of the subscheme. This is the descent
  statement; invariance is what makes it true, and it is proved by covering a section of the
  descended subfunctor and moving the resulting point across the relation.
* `AlgebraicGeometry.Space.pullbackInvariantSubscheme`: conversely, a locally closed subspace
  of the quotient pulls back to an invariant locally closed subscheme of the atlas, and
  `AlgebraicGeometry.Space.quotientSubspacePullbackSubobject_points` identifies its points.

## Implementation notes

A subobject of a scheme of the site need not itself be an object of the site, so its functor of
points is defined directly, by the existence of a factorisation through the subobject, rather
than by representability. When the inclusion is an immersion the underlying scheme is small
enough to lie in the site — `AlgebraicGeometry.Space.siteObjectOfImmersedSubobject` — and the
functor of points is then the image of a site morphism, which is how it is shown to be a sheaf.

Invariance is transported between the groupoid scheme and the site: the canonical groupoid of
Stacks 0233 has its object and arrow schemes equal to the given ones only propositionally, so
the source and target comparisons carry `eqToHom` casts, isolated in the four
`relationGroupoid_*_eq` lemmas.

The two conclusions of Stacks 07TW that this file does not reach — the bijection itself and its
preservation of closedness — need effectivity of fppf descent for immersions, which is not
available: the only route in the sources runs through Stacks 02W8 and hence Stacks 0APK, and
`AlgebraicGeometry.DescentData.IsEffectiveForFamily` has no producer in this library.

## References

* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 0233](https://stacks.math.columbia.edu/tag/0233)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

/-- The underlying scheme of an immersed subobject of a scheme of the site is itself small
enough to lie in the site. -/
theorem site_contains_underlying_of_isImmersion
    (B : BigFppfSite.{u}) {U : Scheme.{u}}
    (hU : B.Contains U) (Z : Subobject U) (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow) :
    B.Contains (Subobject.underlying.obj Z) := by
  obtain ⟨W, i, j, hi, hj, hij⟩ :=
    (_root_.AlgebraicGeometry.IsImmersion.isImmersion_iff_exists (f := Z.arrow)).mp hZ
  exact Scheme.size_lt_of_isClosedImmersion i (Scheme.size_lt_of_isOpenImmersion j hU)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {R U : BigFppfOver B S hS}

/-- The pre-relation on schemes over `S` induced by a pair of arrows of the big fppf site over
`S`. It is the pair whose target is the first arrow and whose source is the second. -/
noncomputable abbrev sitePreRelation (target source : R ⟶ U) :
    PreRelation ((Over.post B.inclusion).obj R) ((Over.post B.inclusion).obj U) :=
  prod.lift ((Over.post B.inclusion).map target) ((Over.post B.inclusion).map source)

variable (target source : R ⟶ U)
variable [IsEtaleEquivalenceRelation (sitePreRelation B S hS target source)]

/-- The canonical groupoid scheme extending the presenting relation. -/
noncomputable abbrev relationGroupoid : GroupoidScheme S :=
  groupoidSchemeOfIsEquivalenceRelation (sitePreRelation B S hS target source)

private theorem relationTarget_prodLift {T : Scheme.{u}} {R U : Over T} (s t : R ⟶ U) :
    PreRelation.target (prod.lift s t) = s := by
  dsimp [PreRelation.target]
  rw [prod.lift_fst]

private theorem relationSource_prodLift {T : Scheme.{u}} {R U : Over T} (s t : R ⟶ U) :
    PreRelation.source (prod.lift s t) = t := by
  dsimp [PreRelation.source]
  rw [prod.lift_snd]

/-- The object scheme of the canonical groupoid of the relation is the underlying scheme of `U`. -/
theorem relationGroupoid_objects_eq :
    (relationGroupoid B S hS target source).objects.left =
      (BigFppfOver.toScheme B S hS).obj U :=
  congrArg Over.left
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
      (sitePreRelation B S hS target source)).objects_eq

/-- The arrow scheme of the canonical groupoid of the relation is the underlying scheme of `R`. -/
theorem relationGroupoid_arrows_eq :
    (relationGroupoid B S hS target source).arrows.left =
      (BigFppfOver.toScheme B S hS).obj R :=
  congrArg Over.left
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
      (sitePreRelation B S hS target source)).arrows_eq

/-- Up to the identifications of `relationGroupoid_arrows_eq` and `relationGroupoid_objects_eq`,
the target of the canonical groupoid of the relation is the arrow `target`. -/
theorem relationGroupoid_target_eq :
    eqToHom (congrArg Over.left
        (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
          (sitePreRelation B S hS target source)).arrows_eq).symm ≫
      (relationGroupoid B S hS target source).target.left ≫
        eqToHom (congrArg Over.left
          (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
            (sitePreRelation B S hS target source)).objects_eq) =
      ((Over.post B.inclusion).map target).left := by
  have hh := congrArg Over.Hom.left
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
      (sitePreRelation B S hS target source)).target_eq
  rw [relationTarget_prodLift ((Over.post B.inclusion).map target)
    ((Over.post B.inclusion).map source)] at hh
  simpa [relationGroupoid, Over.comp_left, Over.eqToHom_left] using hh

/-- Up to the identifications of `relationGroupoid_arrows_eq` and `relationGroupoid_objects_eq`,
the source of the canonical groupoid of the relation is the arrow `source`. -/
theorem relationGroupoid_source_eq :
    eqToHom (congrArg Over.left
        (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
          (sitePreRelation B S hS target source)).arrows_eq).symm ≫
      (relationGroupoid B S hS target source).source.left ≫
        eqToHom (congrArg Over.left
          (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
            (sitePreRelation B S hS target source)).objects_eq) =
      ((Over.post B.inclusion).map source).left := by
  have hh := congrArg Over.Hom.left
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
      (sitePreRelation B S hS target source)).source_eq
  rw [relationSource_prodLift ((Over.post B.inclusion).map target)
    ((Over.post B.inclusion).map source)] at hh
  simpa [relationGroupoid, Over.comp_left, Over.eqToHom_left] using hh

/-- Locally closed subschemes of `U`, invariant as scheme-theoretic subobjects under the
canonical groupoid of the relation. -/
noncomputable abbrev GroupoidInvariantLocallyClosedSubscheme :=
  {Z : Subobject ((BigFppfOver.toScheme B S hS).obj U) //
    _root_.AlgebraicGeometry.IsImmersion Z.arrow ∧
      (let G := relationGroupoid B S hS target source
       let h : G.objects.left = (BigFppfOver.toScheme B S hS).obj U :=
         congrArg Over.left
           (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
             (sitePreRelation B S hS target source)).objects_eq
       IsInvariantMonomorphism G (Z.arrow ≫ eqToHom h.symm))}

private noncomputable def invariantGroupoidSubobject
    (Z : GroupoidInvariantLocallyClosedSubscheme B S hS target source) :
    Subobject (relationGroupoid B S hS target source).objects.left := by
  let hobj : (relationGroupoid B S hS target source).objects.left =
      (BigFppfOver.toScheme B S hS).obj U :=
    congrArg Over.left
      (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
        (sitePreRelation B S hS target source)).objects_eq
  letI : Mono (Z.1.arrow ≫ eqToHom hobj.symm) := by infer_instance
  exact Subobject.mk (Z.1.arrow ≫ eqToHom hobj.symm)

private theorem invariant_factorOfRelated
    (Z : GroupoidInvariantLocallyClosedSubscheme B S hS target source)
    {T : Scheme.{u}} (r : T ⟶ (relationGroupoid B S hS target source).arrows.left)
    (a b : T ⟶ (relationGroupoid B S hS target source).objects.left)
    (htar : r ≫ (relationGroupoid B S hS target source).target.left = a)
    (hsrc : r ≫ (relationGroupoid B S hS target source).source.left = b)
    (hb : (invariantGroupoidSubobject B S hS target source Z).Factors b) :
    (invariantGroupoidSubobject B S hS target source Z).Factors a := by
  let G := relationGroupoid B S hS target source
  let hobj : G.objects.left = (BigFppfOver.toScheme B S hS).obj U :=
    congrArg Over.left
      (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
        (sitePreRelation B S hS target source)).objects_eq
  let Q : Subobject G.objects.left := Subobject.mk (Z.1.arrow ≫ eqToHom hobj.symm)
  have hinv : (Subobject.pullback G.target.left).obj Q =
      (Subobject.pullback G.source.left).obj Q := by
    simpa [Q, invariantGroupoidSubobject, IsInvariantMonomorphism] using Z.2.2
  have hb' : (Subobject.pullback G.source.left).obj Q |>.Factors r :=
    (Limits.pullback_factors_iff G.source.left Q r).2 (by rwa [hsrc])
  rw [← hinv] at hb'
  have ha : Q.Factors (r ≫ G.target.left) :=
    (Limits.pullback_factors_iff G.target.left Q r).1 hb'
  rwa [htar] at ha

private theorem comp_eqToHom_of_eqToHom_comp {C : Type*} [Category C] {T X X' Y Y' : C}
    (hX : X' = X) (hY : Y = Y') {g : X ⟶ Y} {k : X' ⟶ Y'}
    (h : eqToHom hX ≫ g ≫ eqToHom hY = k) {r : T ⟶ X'} {a : T ⟶ Y'} (hr : r ≫ k = a) :
    (r ≫ eqToHom hX) ≫ g = a ≫ eqToHom hY.symm := by
  subst hX hY h hr
  simp

/-- Invariance, in the form it is used: a point of the atlas related by `R` to a point that
factors through the invariant subscheme itself factors through it. -/
theorem invariant_factorOfSiteRelation
    (Z : GroupoidInvariantLocallyClosedSubscheme B S hS target source)
    {T : Scheme.{u}} (r : T ⟶ (BigFppfOver.toScheme B S hS).obj R)
    (a b : T ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (htar : r ≫ ((Over.post B.inclusion).map target).left = a)
    (hsrc : r ≫ ((Over.post B.inclusion).map source).left = b)
    (hb : Z.1.Factors b) : Z.1.Factors a := by
  have hobj := congrArg Over.left (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
    (sitePreRelation B S hS target source)).objects_eq
  have harr := congrArg Over.left (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
    (sitePreRelation B S hS target source)).arrows_eq
  have ho := relationGroupoid_objects_eq B S hS target source
  have htar' : (r ≫ eqToHom harr.symm) ≫ (relationGroupoid B S hS target source).target.left =
      a ≫ eqToHom ho.symm :=
    comp_eqToHom_of_eqToHom_comp harr.symm hobj
      (relationGroupoid_target_eq B S hS target source) htar
  have hsrc' : (r ≫ eqToHom harr.symm) ≫ (relationGroupoid B S hS target source).source.left =
      b ≫ eqToHom ho.symm :=
    comp_eqToHom_of_eqToHom_comp harr.symm hobj
      (relationGroupoid_source_eq B S hS target source) hsrc
  have hQ : invariantGroupoidSubobject B S hS target source Z =
      Subobject.mk (Z.1.arrow ≫ eqToHom ho.symm) := rfl
  have hb' : (invariantGroupoidSubobject B S hS target source Z).Factors
      (b ≫ eqToHom ho.symm) := by
    rw [hQ, Subobject.mk_factors_iff]
    refine ⟨Z.1.factorThru b hb, ?_⟩
    show _ ≫ Z.1.arrow ≫ _ = _
    rw [← Category.assoc, Subobject.factorThru_arrow]
  have ha := invariant_factorOfRelated B S hS target source Z _ _ _ htar' hsrc' hb'
  rw [hQ, Subobject.mk_factors_iff] at ha
  obtain ⟨g, hg⟩ := ha
  exact (Subobject.factors_iff Z.1 a).2
    ⟨g, (cancel_mono (eqToHom ho.symm)).1 ((Category.assoc _ _ _).trans hg)⟩

/-- An immersed subobject of a scheme of the site is small enough to be an object of the site;
this is that object, over `S` through the inclusion. -/
noncomputable abbrev siteObjectOfImmersedSubobject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U : BigFppfOver B S hS}
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow) : BigFppfOver B S hS := by
  let hsize : B.Contains (Subobject.underlying.obj Z) :=
    site_contains_underlying_of_isImmersion B U.left.property Z hZ
  let V : B.Schemes := B.obj hsize
  let f : V ⟶ U.left := B.inclusion.preimage Z.arrow
  exact Over.mk (f ≫ U.hom)

/-- The inclusion of an immersed subobject, as a morphism of the site, maps to the inclusion of
the subobject. -/
private theorem toScheme_map_homMk_preimage {U : BigFppfOver B S hS}
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow) :
    (BigFppfOver.toScheme B S hS).map (Over.homMk (B.inclusion.preimage Z.arrow) :
      siteObjectOfImmersedSubobject B S hS Z hZ ⟶ U) = Z.arrow :=
  B.inclusion.map_preimage
    (X := B.obj (site_contains_underlying_of_isImmersion B U.left.property Z hZ))
    (Y := U.left) Z.arrow

/-- The inclusion of an immersed subobject, as a morphism of the site, maps to a monomorphism. -/
private theorem mono_toScheme_map_homMk_preimage {U : BigFppfOver B S hS}
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow) :
    Mono ((BigFppfOver.toScheme B S hS).map (Over.homMk (B.inclusion.preimage Z.arrow) :
      siteObjectOfImmersedSubobject B S hS Z hZ ⟶ U)) := by
  rw [toScheme_map_homMk_preimage]
  infer_instance

/-- The inclusion of an immersed subobject, as a morphism of the site, is a monomorphism. -/
private theorem mono_homMk_preimage {U : BigFppfOver B S hS}
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow) :
    Mono (Over.homMk (B.inclusion.preimage Z.arrow) :
      siteObjectOfImmersedSubobject B S hS Z hZ ⟶ U) := by
  have : B.inclusion.ReflectsMonomorphisms :=
    Functor.reflectsMonomorphisms_of_faithful B.inclusion
  have := mono_toScheme_map_homMk_preimage B S hS Z hZ
  have : Mono (B.inclusion.preimage Z.arrow :
      B.obj (site_contains_underlying_of_isImmersion B U.left.property Z hZ) ⟶ U.left) :=
    Functor.ReflectsMonomorphisms.reflects (F := B.inclusion) _ this
  exact Over.mono_of_mono_left _

/-- The functor of points of the subobject given by a monomorphism `f : V ⟶ U` of the site is the
image of `yoneda.map f`. -/
private theorem subschemePoints_mk_eq_range {V : BigFppfOver B S hS} (f : V ⟶ U)
    [Mono ((BigFppfOver.toScheme B S hS).map f)] :
    subschemePoints B S hS (Subobject.mk ((BigFppfOver.toScheme B S hS).map f)) =
      Subfunctor.range (yoneda.map f) := by
  ext T x
  show (∃ g, g ≫ _ = _) ↔ ∃ y, y ≫ f = x
  apply (Subobject.factors_iff _ _).symm.trans
  rw [Subobject.mk_factors_iff]
  show (∃ g, g ≫ (BigFppfOver.toScheme B S hS).map f =
    (BigFppfOver.toScheme B S hS).map x) ↔ ∃ y, y ≫ f = x
  constructor
  · rintro ⟨g, hg⟩
    let g' : T.unop.left ⟶ V.left := B.inclusion.preimage g
    have hmapg : B.inclusion.map g' = g := B.inclusion.map_preimage g
    have hg' : g ≫ B.inclusion.map f.left = B.inclusion.map x.left := hg
    have hw : g' ≫ V.hom = T.unop.hom := by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, hmapg]
      calc
        g ≫ B.inclusion.map V.hom = g ≫ B.inclusion.map (f.left ≫ U.hom) := by rw [Over.w]
        _ = B.inclusion.map x.left ≫ B.inclusion.map U.hom := by
          rw [Functor.map_comp, ← Category.assoc, hg']
        _ = B.inclusion.map T.unop.hom := by rw [← Functor.map_comp, Over.w]
    refine ⟨Over.homMk g' hw, ?_⟩
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show B.inclusion.map (g' ≫ f.left) = B.inclusion.map x.left
    rw [Functor.map_comp, hmapg, hg']
  · rintro ⟨g, rfl⟩
    exact ⟨(BigFppfOver.toScheme B S hS).map g, (Functor.map_comp _ _ _).symm⟩

/-- For an immersed subobject, the functor of points is the image of the corresponding morphism
of the site. -/
theorem subschemePoints_eq_range_of_isImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U : BigFppfOver B S hS}
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow) :
    subschemePoints B S hS Z =
      Subfunctor.range (yoneda.map (Over.homMk (B.inclusion.preimage Z.arrow) :
        siteObjectOfImmersedSubobject B S hS Z hZ ⟶ U)) := by
  have := mono_toScheme_map_homMk_preimage B S hS Z hZ
  let m : siteObjectOfImmersedSubobject B S hS Z hZ ⟶ U :=
    Over.homMk (B.inclusion.preimage Z.arrow)
  have hm : Subobject.mk ((BigFppfOver.toScheme B S hS).map m) = Z :=
    Subobject.mk_eq_of_comm _ (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, toScheme_map_homMk_preimage])
  exact (congrArg (subschemePoints B S hS) hm).symm.trans (subschemePoints_mk_eq_range B S hS m)

/-- The functor of points of an immersed subobject is a sheaf for the big fppf topology. -/
theorem subschemePoints_isSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U : BigFppfOver B S hS}
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (subschemePoints B S hS Z).toFunctor := by
  let m : siteObjectOfImmersedSubobject B S hS Z hZ ⟶ U :=
    Over.homMk (B.inclusion.preimage Z.arrow)
  have : Mono m := mono_homMk_preimage B S hS Z hZ
  rw [subschemePoints_eq_range_of_isImmersion B S hS Z hZ]
  exact (isSheaf_iff_isSheaf_of_type
      (J := BigFppfOver.topology B S hS) ((Subfunctor.range (yoneda.map m)).toFunctor)).2
    (Presieve.isSheaf_iso (BigFppfOver.topology B S hS)
      (asIso (Subfunctor.toRange (yoneda.map m)))
      ((isSheaf_iff_isSheaf_of_type (J := BigFppfOver.topology B S hS)
        (yoneda.obj (siteObjectOfImmersedSubobject B S hS Z hZ))).mp
        (isAlgebraicSpace_yoneda B S hS (siteObjectOfImmersedSubobject B S hS Z hZ)).isSheaf))

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (P : Presentation B S hS X hX)

/-- The relation of a presentation is an étale equivalence relation. -/
local instance presentation_isEtaleEquivalenceRelation :
    IsEtaleEquivalenceRelation (sitePreRelation B S hS P.target P.source) :=
  P.isEtaleEquivalenceRelation

/-- Invariance on points of the site: a point of the atlas with the same image in the quotient as
a point of the invariant subscheme is itself a point of the subscheme. -/
private theorem mem_subschemePoints_of_toSpace_eq
    (Z : GroupoidInvariantLocallyClosedSubscheme B S hS P.target P.source)
    {T : BigFppfOver B S hS} {u v : T ⟶ P.U}
    (h : yoneda.map u ≫ P.toSpace = yoneda.map v ≫ P.toSpace)
    (hv : v ∈ (subschemePoints B S hS Z.1).obj (op T)) :
    u ∈ (subschemePoints B S hS Z.1).obj (op T) := by
  let r : T ⟶ P.R := Yoneda.fullyFaithful.preimage (P.isPullback.lift _ _ h)
  have hr : yoneda.map r = P.isPullback.lift _ _ h := Yoneda.fullyFaithful.map_preimage _
  have hrt : r ≫ P.target = u := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, hr]
    exact P.isPullback.lift_fst _ _ _)
  have hrs : r ≫ P.source = v := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, hr]
    exact P.isPullback.lift_snd _ _ _)
  have hu : (BigFppfOver.toScheme B S hS).map r ≫ (BigFppfOver.toScheme B S hS).map P.target =
      (BigFppfOver.toScheme B S hS).map u := by
    rw [← Functor.map_comp, hrt]
  have hv' : (BigFppfOver.toScheme B S hS).map r ≫ (BigFppfOver.toScheme B S hS).map P.source =
      (BigFppfOver.toScheme B S hS).map v := by
    rw [← Functor.map_comp, hrs]
  exact (Subobject.factors_iff Z.1 _).mp
    (invariant_factorOfSiteRelation B S hS P.target P.source Z _ _ _ hu hv'
      ((Subobject.factors_iff Z.1 ((BigFppfOver.toScheme B S hS).map v)).2 hv))

/-- The descent of an invariant subscheme of the atlas: the sheafification of the image of its
functor of points along the atlas morphism. -/
noncomputable def descendedInvariantSubfunctor
    (Z : GroupoidInvariantLocallyClosedSubscheme B S hS P.target P.source) : Subfunctor X :=
  (Subfunctor.range ((subschemePoints B S hS Z.1).ι ≫ P.toSpace)).sheafify
    (BigFppfOver.topology B S hS)

/-- **The descent statement.** Pulling the descended subfunctor back along the atlas returns
exactly the functor of points of the invariant subscheme. -/
theorem descendedInvariantSubfunctor_preimage
    (Z : GroupoidInvariantLocallyClosedSubscheme B S hS P.target P.source) :
    (descendedInvariantSubfunctor B S hS P Z).preimage P.toSpace =
      subschemePoints B S hS Z.1 := by
  let J := BigFppfOver.topology B S hS
  let Q := subschemePoints B S hS Z.1
  let k : Q.toFunctor ⟶ X := Q.ι ≫ P.toSpace
  ext T x
  show P.toSpace.app T x ∈ ((Subfunctor.range k).sheafify J).obj T ↔ x ∈ Q.obj T
  refine ⟨fun hx => ?_, fun hx => Subfunctor.le_sheafify J (Subfunctor.range k) T ⟨⟨x, hx⟩, rfl⟩⟩
  · change (Subfunctor.range k).sieveOfSection (P.toSpace.app T x) ∈ J T.unop at hx
    have hQsheaf : Presieve.IsSheaf J Q.toFunctor :=
      (isSheaf_iff_isSheaf_of_type (J := J) (Q.toFunctor)).mp
        (subschemePoints_isSheaf B S hS Z.1 Z.2.1)
    have hbaseSheaf : Presieve.IsSheaf J (yoneda.obj P.U) :=
      (isSheaf_iff_isSheaf_of_type (J := J) (yoneda.obj P.U)).mp
        (isAlgebraicSpace_yoneda B S hS P.U).isSheaf
    have hQcover : Q.sieveOfSection x ∈ J T.unop := by
      apply J.superset_covering ?_ hx
      intro T' i hi
      change (X.map i.op) (P.toSpace.app T x) ∈ Set.range (k.app (Opposite.op T')) at hi
      obtain ⟨z, hz⟩ := hi
      have hvalue : P.toSpace.app (op T') (i ≫ x) = P.toSpace.app (op T') z.1 :=
        calc
          _ = (X.map i.op) (P.toSpace.app T x) := by
            simpa using NatTrans.naturality_apply P.toSpace i.op x
          _ = k.app (op T') z := hz.symm
      show i ≫ x ∈ Q.obj (op T')
      exact mem_subschemePoints_of_toSpace_eq B S hS P Z (u := i ≫ x) (v := z.1)
        (yonedaEquiv.injective (by
          simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hvalue)) z.2
    exact (Subfunctor.isSheaf_iff (G := Q) hbaseSheaf).mp hQsheaf T x hQcover

/-- The inverse image of a subfunctor is the pullback of its inclusion. -/
theorem isPullback_subfunctor_preimage_base {C : Type*} [Category C] {F G : Cᵒᵖ ⥤ Type u}
    (Z : Subfunctor F) (f : G ⟶ F) :
    IsPullback (Z.preimage f).ι (Z.fromPreimage f) f Z.ι := by
  have hsquare := (Subfunctor.fromPreimage_ι Z f).symm
  let lift (s : PullbackCone f Z.ι) :=
    Subfunctor.lift (G := Z.preimage f) s.fst (by
      intro W x hx
      obtain ⟨y, rfl⟩ := hx
      show f.app W (s.fst.app W y) ∈ Z.obj W
      have hh' : f.app W (s.fst.app W y) = Z.ι.app W (s.snd.app W y) := by
        simpa [NatTrans.comp_app] using congrFun (congrArg (fun k => k.app W) s.condition) y
      rw [hh']
      exact (s.snd.app W y).property)
  have hfacLeft (s : PullbackCone f Z.ι) : lift s ≫ (Z.preimage f).ι = s.fst := by
    ext W x
    rfl
  refine ⟨CommSq.mk hsquare, ⟨PullbackCone.IsLimit.mk hsquare lift hfacLeft
    (fun s => (cancel_mono Z.ι).1 ((congrArg (· ≫ f) (hfacLeft s)).trans s.condition))
    (fun s m hm₁ _ => (cancel_mono (Z.preimage f).ι).1 (hm₁.trans (hfacLeft s)))⟩⟩

/-- A representation of the descended subfunctor's base change to the atlas by an immersion of
schemes of the site. -/
structure InvariantDescentPullbackData
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (P : Presentation B S hS X hX)
    (Z : GroupoidInvariantLocallyClosedSubscheme B S hS P.target P.source) where
  /-- The representing object of the site. -/
  V : BigFppfOver B S hS
  /-- Its morphism to the atlas. -/
  toAtlas : V ⟶ P.U
  /-- Its morphism to the descended subfunctor. -/
  toSubspace : yoneda.obj V ⟶ (descendedInvariantSubfunctor B S hS P Z).toFunctor
  /-- The two together form a pullback square over the atlas. -/
  isPullback : IsPullback toSubspace (yoneda.map toAtlas)
    (descendedInvariantSubfunctor B S hS P Z).ι P.toSpace
  /-- The morphism to the atlas is an immersion of schemes. -/
  immersion : _root_.AlgebraicGeometry.IsImmersion
    ((BigFppfOver.toScheme B S hS).map toAtlas)

/-- The base change to the atlas of the descended subfunctor of an invariant subscheme is
represented by an immersion of schemes of the site. -/
theorem invariantDescentPullbackData_nonempty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (P : Presentation B S hS X hX)
    (Z : GroupoidInvariantLocallyClosedSubscheme B S hS P.target P.source) :
    Nonempty (InvariantDescentPullbackData B S hS P Z) := by
  have hZ : _root_.AlgebraicGeometry.IsImmersion Z.1.arrow := Z.2.1
  let V := siteObjectOfImmersedSubobject B S hS Z.1 hZ
  let p : V ⟶ P.U := Over.homMk (B.inclusion.preimage Z.1.arrow)
  have hpmap : (BigFppfOver.toScheme B S hS).map p = Z.1.arrow :=
    toScheme_map_homMk_preimage B S hS Z.1 hZ
  let Q := (descendedInvariantSubfunctor B S hS P Z).preimage P.toSpace
  have hQRange : Q = Subfunctor.range (yoneda.map p) :=
    (descendedInvariantSubfunctor_preimage B S hS P Z).trans
      (subschemePoints_eq_range_of_isImmersion B S hS Z.1 hZ)
  have : Mono p := mono_homMk_preimage B S hS Z.1 hZ
  let eRange : yoneda.obj V ≅ (Subfunctor.range (yoneda.map p)).toFunctor :=
    asIso (Subfunctor.toRange (yoneda.map p))
  let eQ : Q.toFunctor ≅ (Subfunctor.range (yoneda.map p)).toFunctor :=
    eqToIso (congrArg Subfunctor.toFunctor hQRange)
  let e : yoneda.obj V ≅ Q.toFunctor := eRange ≪≫ eQ.symm
  have he : e.hom ≫ Q.ι = yoneda.map p := by
    have htransport : eQ.symm.hom ≫ Q.ι = (Subfunctor.range (yoneda.map p)).ι := by
      dsimp [eQ]
      generalize hq : Q = Q' at hQRange ⊢
      cases hQRange
      rfl
    show eRange.hom ≫ eQ.symm.hom ≫ Q.ι = yoneda.map p
    rw [htransport]
    exact Subfunctor.toRange_ι _
  let i := e.hom ≫ (descendedInvariantSubfunctor B S hS P Z).fromPreimage P.toSpace
  have hpull : IsPullback i (yoneda.map p)
      (descendedInvariantSubfunctor B S hS P Z).ι P.toSpace := by
    apply IsPullback.of_iso
      (isPullback_subfunctor_preimage_base (descendedInvariantSubfunctor B S hS P Z)
        P.toSpace).flip
      e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [i]
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]
      rfl
    · simp
    · simp
  exact ⟨⟨V, p, i, hpull, by rwa [hpmap]⟩⟩

/-- A representation of a locally closed subspace's base change to the atlas by an immersion of
schemes of the site. -/
structure QuotientSubspacePullbackData
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (P : Presentation B S hS X hX) (W : LocallyClosedQuotientSubspace B S hS (X := X)) where
  /-- The representing object of the site. -/
  V : BigFppfOver B S hS
  /-- Its morphism to the atlas. -/
  toAtlas : V ⟶ P.U
  /-- Its morphism to the subspace. -/
  toSubspace : yoneda.obj V ⟶ W.1.toFunctor
  /-- The two together form a pullback square over the atlas. -/
  isPullback : IsPullback toSubspace (yoneda.map toAtlas) W.1.ι P.toSpace
  /-- The morphism to the atlas is an immersion of schemes. -/
  immersion : _root_.AlgebraicGeometry.IsImmersion
    ((BigFppfOver.toScheme B S hS).map toAtlas)

/-- The base change to the atlas of a locally closed subspace of the quotient is represented by
an immersion of schemes of the site. -/
theorem quotientSubspacePullbackData_nonempty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (P : Presentation B S hS X hX) (W : LocallyClosedQuotientSubspace B S hS (X := X)) :
    Nonempty (QuotientSubspacePullbackData B S hS P W) := by
  obtain ⟨V, p, i, hpull⟩ := W.2.2.rep P.toSpace
  exact ⟨⟨V, p, i, hpull, W.2.2.property P.toSpace i p hpull⟩⟩

/-- The subscheme of the atlas cut out by a locally closed subspace of the quotient. -/
noncomputable def quotientSubspacePullbackSubobject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (P : Presentation B S hS X hX) (W : LocallyClosedQuotientSubspace B S hS (X := X)) :
    Subobject ((BigFppfOver.toScheme B S hS).obj P.U) := by
  let d := Classical.choice (quotientSubspacePullbackData_nonempty B S hS P W)
  let f := (BigFppfOver.toScheme B S hS).map d.toAtlas
  letI : _root_.AlgebraicGeometry.IsImmersion f := d.immersion
  letI : Mono f := by infer_instance
  exact Subobject.mk f

/-- The inclusion of the subscheme of the atlas cut out by a locally closed subspace of the
quotient is an immersion. -/
theorem quotientSubspacePullbackSubobject_isImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (P : Presentation B S hS X hX) (W : LocallyClosedQuotientSubspace B S hS (X := X)) :
    _root_.AlgebraicGeometry.IsImmersion
      (quotientSubspacePullbackSubobject B S hS P W).arrow := by
  unfold quotientSubspacePullbackSubobject
  have := (Classical.choice (quotientSubspacePullbackData_nonempty B S hS P W)).immersion
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- The atlas morphism of a presentation is locally surjective for the fppf topology. -/
theorem presentation_locallySurjective :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) P.toSpace := by
  let a : (⟨yoneda.obj P.U, (isAlgebraicSpace_yoneda B S hS P.U).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨X, hX.isSheaf⟩ := ⟨P.toSpace⟩
  apply isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
    B S hS a
  refine ⟨P.surjective.rep, ?_⟩
  intro T V q i p hp
  have : Etale ((BigFppfOver.toScheme B S hS).map p) := P.etale.property q i p hp
  exact ⟨inferInstance, inferInstance, P.surjective.property q i p hp⟩

/-- A locally closed subspace of the quotient is determined by its base change to the atlas. -/
theorem subspace_preimage_injective (W₁ W₂ : LocallyClosedQuotientSubspace B S hS (X := X))
    (h : W₁.1.preimage P.toSpace = W₂.1.preimage P.toSpace) : W₁ = W₂ := by
  let J := BigFppfOver.topology B S hS
  have := presentation_locallySurjective B S hS P
  have hle (W V : LocallyClosedQuotientSubspace B S hS (X := X))
      (he : W.1.preimage P.toSpace = V.1.preimage P.toSpace) : W.1 ≤ V.1 := by
    intro T x hx
    apply (Subfunctor.isSheaf_iff V.1 ((isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf)).1
      ((isSheaf_iff_isSheaf_of_type _ _).1 V.2.1.isSheaf) T x
    apply J.superset_covering ?_ (Presheaf.imageSieve_mem J P.toSpace x)
    intro T' i hi
    obtain ⟨y, hy⟩ := hi
    show X.map i.op x ∈ V.1.obj (op T')
    rw [← hy]
    show y ∈ (V.1.preimage P.toSpace).obj (op T')
    rw [← he]
    show P.toSpace.app (op T') y ∈ W.1.obj (op T')
    rw [hy]
    exact W.1.map i.op hx
  exact Subtype.ext (le_antisymm (hle W₁ W₂ h) (hle W₂ W₁ h.symm))

/-- The functor of points of the subobject given by a monomorphism `f : V ⟶ U` of the site is the
image of `yoneda.map f`. -/
theorem subschemePoints_mk {V : BigFppfOver B S hS} (f : V ⟶ U)
    [Mono ((BigFppfOver.toScheme B S hS).map f)] :
    subschemePoints B S hS (Subobject.mk ((BigFppfOver.toScheme B S hS).map f)) =
      Subfunctor.range (yoneda.map f) :=
  subschemePoints_mk_eq_range B S hS f

/-- The image of a base change along a representable morphism is the inverse image of the
subfunctor. -/
theorem range_eq_preimage_of_isPullback {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type u} {U V : C}
    (W : Subfunctor F) (q : yoneda.obj U ⟶ F) (p : V ⟶ U)
    (i : yoneda.obj V ⟶ W.toFunctor) (h : IsPullback i (yoneda.map p) W.ι q) :
    Subfunctor.range (yoneda.map p) = W.preimage q := by
  ext T x
  show (∃ y, y ≫ p = x) ↔ q.app T x ∈ W.obj T
  constructor
  · rintro ⟨y, rfl⟩
    have hh : (i.app T y).val = q.app T (y ≫ p) :=
      congrFun (congrArg (fun k => k.app T) h.w) y
    rw [← hh]
    exact (i.app T y).property
  · intro hx
    let a : yoneda.obj T.unop ⟶ W.toFunctor := yonedaEquiv.symm ⟨q.app T x, hx⟩
    have ha : a ≫ W.ι = yoneda.map x ≫ q := by
      ext T' y
      show F.map y.op (q.app T x) = q.app T' (y ≫ x)
      exact (NatTrans.naturality_apply q y.op x).symm
    let b := h.lift a (yoneda.map x) ha
    refine ⟨Yoneda.fullyFaithful.preimage b, ?_⟩
    apply Yoneda.fullyFaithful.map_injective
    rw [Functor.map_comp, Yoneda.fullyFaithful.map_preimage]
    exact h.lift_snd _ _ _

/-- The subscheme cut out of the atlas by a locally closed subspace has, as functor of points,
the base change of that subspace. -/
theorem quotientSubspacePullbackSubobject_points
    (W : LocallyClosedQuotientSubspace B S hS (X := X)) :
    subschemePoints B S hS (quotientSubspacePullbackSubobject B S hS P W) =
      W.1.preimage P.toSpace := by
  let d := Classical.choice (quotientSubspacePullbackData_nonempty B S hS P W)
  have := d.immersion
  show subschemePoints B S hS
    (Subobject.mk ((BigFppfOver.toScheme B S hS).map d.toAtlas)) = _
  rw [subschemePoints_mk]
  exact range_eq_preimage_of_isPullback W.1 P.toSpace d.toAtlas d.toSubspace d.isPullback

private theorem subobject_pullback_isImmersion {T V : Scheme.{u}} (f : T ⟶ V)
    (Z : Subobject V) (h : _root_.AlgebraicGeometry.IsImmersion Z.arrow) :
    _root_.AlgebraicGeometry.IsImmersion ((Subobject.pullback f).obj Z).arrow :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (Subobject.isPullback f Z) h

/-- The subscheme of the atlas cut out by a locally closed subspace of the quotient has the same
pullback along the target and along the source of the relation. -/
theorem quotientSubspacePullbackSubobject_relation
    (W : LocallyClosedQuotientSubspace B S hS (X := X)) :
    (Subobject.pullback ((BigFppfOver.toScheme B S hS).map P.target)).obj
      (quotientSubspacePullbackSubobject B S hS P W) =
    (Subobject.pullback ((BigFppfOver.toScheme B S hS).map P.source)).obj
      (quotientSubspacePullbackSubobject B S hS P W) := by
  apply subschemePoints_injective B S hS
  · exact subobject_pullback_isImmersion _ _
      (quotientSubspacePullbackSubobject_isImmersion B S hS P W)
  · exact subobject_pullback_isImmersion _ _
      (quotientSubspacePullbackSubobject_isImmersion B S hS P W)
  rw [subschemePoints_pullback, subschemePoints_pullback,
    quotientSubspacePullbackSubobject_points]
  ext T x
  show P.toSpace.app T ((yoneda.map P.target).app T x) ∈ W.1.obj T ↔
    P.toSpace.app T ((yoneda.map P.source).app T x) ∈ W.1.obj T
  have hh : P.toSpace.app T ((yoneda.map P.target).app T x) =
      P.toSpace.app T ((yoneda.map P.source).app T x) :=
    congrFun (congrArg (fun k => k.app T) P.isPullback.w) x
  rw [hh]

/-- The subscheme of the atlas cut out by a locally closed subspace of the quotient is invariant
for the canonical groupoid of the relation. -/
theorem quotientSubspacePullbackSubobject_invariant
    (W : LocallyClosedQuotientSubspace B S hS (X := X)) :
    let Z := quotientSubspacePullbackSubobject B S hS P W
    let G := relationGroupoid B S hS P.target P.source
    let h : G.objects.left = (BigFppfOver.toScheme B S hS).obj P.U :=
      congrArg Over.left
      (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
        (sitePreRelation B S hS P.target P.source)).objects_eq
    IsInvariantMonomorphism G (Z.arrow ≫ eqToHom h.symm) := by
  let Z := quotientSubspacePullbackSubobject B S hS P W
  let G := relationGroupoid B S hS P.target P.source
  let hext := groupoidSchemeOfIsEquivalenceRelation_extendsRelation
    (sitePreRelation B S hS P.target P.source)
  let ho : G.objects.left = (BigFppfOver.toScheme B S hS).obj P.U :=
    congrArg Over.left hext.objects_eq
  let hr : G.arrows.left = (BigFppfOver.toScheme B S hS).obj P.R :=
    congrArg Over.left hext.arrows_eq
  have he : Subobject.mk (Z.arrow ≫ eqToHom ho.symm) =
      (Subobject.pullback (eqToHom ho)).obj Z := by
    have hp : IsPullback (𝟙 (Z : Scheme)) (Z.arrow ≫ eqToHom ho.symm)
        Z.arrow (eqToHom ho) := IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa only [Subobject.mk_arrow] using (Subobject.pullback_obj_mk hp).symm
  have ht : G.target.left ≫ eqToHom ho =
      eqToHom hr ≫ (BigFppfOver.toScheme B S hS).map P.target := by
    have hh := relationGroupoid_target_eq B S hS P.target P.source
    change eqToHom hr.symm ≫ G.target.left ≫ eqToHom ho =
      (BigFppfOver.toScheme B S hS).map P.target at hh
    exact (cancel_epi (eqToHom hr.symm)).1 (hh.trans (by simp))
  have hs : G.source.left ≫ eqToHom ho =
      eqToHom hr ≫ (BigFppfOver.toScheme B S hS).map P.source := by
    have hh := relationGroupoid_source_eq B S hS P.target P.source
    change eqToHom hr.symm ≫ G.source.left ≫ eqToHom ho =
      (BigFppfOver.toScheme B S hS).map P.source at hh
    exact (cancel_epi (eqToHom hr.symm)).1 (hh.trans (by simp))
  show (Subobject.pullback G.target.left).obj (Subobject.mk (Z.arrow ≫ eqToHom ho.symm)) =
    (Subobject.pullback G.source.left).obj (Subobject.mk (Z.arrow ≫ eqToHom ho.symm))
  rw [he, ← Subobject.pullback_comp, ← Subobject.pullback_comp, ht, hs,
    Subobject.pullback_comp, Subobject.pullback_comp]
  exact congrArg (Subobject.pullback (eqToHom hr)).obj
    (quotientSubspacePullbackSubobject_relation B S hS P W)

/-- The invariant locally closed subscheme of the atlas cut out by a locally closed subspace of
the quotient. -/
noncomputable def pullbackInvariantSubscheme (W : LocallyClosedQuotientSubspace B S hS (X := X)) :
    GroupoidInvariantLocallyClosedSubscheme B S hS P.target P.source :=
  ⟨quotientSubspacePullbackSubobject B S hS P W,
    quotientSubspacePullbackSubobject_isImmersion B S hS P W,
    quotientSubspacePullbackSubobject_invariant B S hS P W⟩

/-- Descending an invariant subscheme and pulling the result back recovers the subscheme. -/
theorem pullbackInvariantSubscheme_descendedInvariantSubfunctor
    (Z : GroupoidInvariantLocallyClosedSubscheme B S hS P.target P.source)
    (hd : IsLocallyClosedSubspace B S hS (descendedInvariantSubfunctor B S hS P Z)) :
    pullbackInvariantSubscheme B S hS P
      ⟨descendedInvariantSubfunctor B S hS P Z, hd⟩ = Z := by
  apply Subtype.ext
  apply subschemePoints_injective B S hS
  · exact (pullbackInvariantSubscheme B S hS P
      ⟨descendedInvariantSubfunctor B S hS P Z, hd⟩).2.1
  · exact Z.2.1
  exact (quotientSubspacePullbackSubobject_points B S hS P _).trans
    (descendedInvariantSubfunctor_preimage B S hS P Z)

/-- Pulling a locally closed subspace of the quotient back and descending it again recovers the
subspace. -/
theorem descendedInvariantSubfunctor_pullbackInvariantSubscheme
    (W : LocallyClosedQuotientSubspace B S hS (X := X))
    (hd : IsLocallyClosedSubspace B S hS
      (descendedInvariantSubfunctor B S hS P (pullbackInvariantSubscheme B S hS P W))) :
    (⟨descendedInvariantSubfunctor B S hS P (pullbackInvariantSubscheme B S hS P W), hd⟩ :
      LocallyClosedQuotientSubspace B S hS (X := X)) = W :=
  subspace_preimage_injective B S hS P _ _ ((descendedInvariantSubfunctor_preimage B S hS P
    (pullbackInvariantSubscheme B S hS P W)).trans
    (quotientSubspacePullbackSubobject_points B S hS P W))

end AlgebraicGeometry.Space

end
