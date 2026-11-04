module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.RelativeOverBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending a scheme over the base along a covering family, and gluing it over the base

Let `𝒰 = {X i ⟶ S}` be a covering family for the fpqc topology. The schemes over `S` then sit
inside the descent data relative to `𝒰` as a full subcategory: a scheme over `S` is determined,
up to unique isomorphism, by its canonical descent datum, and a morphism of canonical descent
data is the canonical datum of exactly one morphism of schemes over `S`. This holds over an
arbitrary base and with no quasi-compactness hypothesis, because the family refines the
one-member family of the identity of `S` and pullback of descent data along a refinement whose
source is an fpqc covering is fully faithful.

The second half of the file is the Zariski side of the same circle of ideas: pieces lying over
the members of an open covering of `S`, with transition morphisms over the double overlaps,
assemble into a single scheme over `S` restricting to the given pieces. This is
`AlgebraicGeometry.Scheme.RelativeGlueData` of Stacks 01LH, presented so that the transition on
triple overlaps is constructed rather than supplied: a transition morphism lies over the base,
so it carries the part of a piece lying over a third member of the covering to the part of the
next piece lying over that same member.

## Main definitions

* `AlgebraicGeometry.pullbackFunctorCanonicalIso`: the natural isomorphism identifying the
  pullback along a refinement of the canonical descent data relative to the coarser family with
  the canonical descent data relative to the refining family.
* `AlgebraicGeometry.idFamily`: the one-member family consisting of the identity of the base.
* `AlgebraicGeometry.toIdFamilyHom`: any family with target `S` as a refinement of that one.
* `AlgebraicGeometry.Scheme.RelativeGlueCore`: a relative gluing datum with the transitions
  given only over the double overlaps, and
  `AlgebraicGeometry.Scheme.RelativeGlueCore.ofPieces` its presentation in which the pieces are
  given as schemes over the members of the covering of the base.
* `AlgebraicGeometry.Scheme.RelativeGlueCore.t'`: the transition on triple overlaps that such a
  datum carries.

## Main results

* `AlgebraicGeometry.DescentData.canonicalFamilyDescentFunctor_fullyFaithful_of_fpqc`: **the
  canonical-descent-datum functor of a covering family for the fpqc topology is fully
  faithful.**
* `AlgebraicGeometry.DescentData.existsUnique_canonicalFamilyDatum_hom` and
  `AlgebraicGeometry.DescentData.eq_of_canonicalFamilyDatum_map_eq`: the descended morphism
  exists and is unique.
* `AlgebraicGeometry.DescentData.nonempty_iso_of_canonicalFamilyDatum_iso`: the descended scheme
  is unique up to isomorphism over the base.
* `AlgebraicGeometry.DescentData.nonempty_iso_of_restrictBase_canonicalFamilyDatum_iso` and
  `AlgebraicGeometry.DescentData.eq_of_restrictBase_canonicalFamilyDatum_map_eq`: the same two
  uniqueness statements over an open of the base, for the restricted family.
* `AlgebraicGeometry.Scheme.RelativeGlueCore.toRelativeGlueData` and
  `AlgebraicGeometry.Scheme.RelativeGlueCore.exists_isPullback_of_toRelativeGlueData`: **the
  transitions over the double overlaps suffice to glue**, producing a scheme over `S` whose part
  over each member of the covering is the corresponding piece.

## Implementation notes

Full faithfulness of the canonical-descent-datum functor is the composite of two full
faithfulnesses, and the natural isomorphism `pullbackFunctorCanonicalIso` is what lets them be
composed: `AlgebraicGeometry.pullbackFunctorCanonicalObjIso` identifies the two functors only
object by object, which is enough to compare essential images but not to transport full
faithfulness. Naturality reduces, component by component, to naturality of
`AlgebraicGeometry.pullbackCompObjIso` in the scheme over the base, which is a pair of
projection identities on the fibre products.

The one-member family is indexed by `PUnit` in the universe of the schemes, since a
`AlgebraicGeometry.MorphismOfSchemeFamilies` carries its families indexed there. Its
canonical-descent-datum functor is fully faithful for a formal reason: its single component is
base change along the identity, which `CategoryTheory.Over.pullbackId` identifies with the
identity functor.

The pullback functor on descent data is made `implicit_reducible` locally, so that a component
of a pulled-back datum and its chosen base change are interchangeable in statements; the
identifications `AlgebraicGeometry.MorphismOfSchemeFamilies.pulledBackDatumObjIso` and the
`obj_eq` field of `AlgebraicGeometry.MorphismOfSchemeFamilies.PullbackFunctor` are then
identities.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

section PullbackComp

variable {S : Scheme.{u}}

/-- The identification of `(W ×_S Y) ×_Y X` with `W ×_S X` preserves the projection to `X`. -/
lemma pullbackCompObjIso_hom_left_snd (W : Over S) {X Y : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ S)
    (b : X ⟶ S) (hw : a ≫ g = b) :
    (pullbackCompObjIso W a g b hw).hom.left ≫ pullback.snd W.hom b =
      pullback.snd (pullback.snd W.hom g) a := by
  simpa only [Over.pullback_obj_hom] using Over.w (pullbackCompObjIso W a g b hw).hom

/-- The identification of `(W ×_S Y) ×_Y X` with `W ×_S X` is natural in `W`. -/
lemma pullbackCompObjIso_naturality {X Y : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ S) (b : X ⟶ S)
    (hw : a ≫ g = b) {W W' : Over S} (k : W ⟶ W') :
    (Over.pullback a).map ((Over.pullback g).map k) ≫ (pullbackCompObjIso W' a g b hw).hom =
      (pullbackCompObjIso W a g b hw).hom ≫ (Over.pullback b).map k := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;>
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, Over.pullback_obj_hom,
      pullback.lift_fst, pullback.lift_snd, pullbackCompObjIso_hom_left_fst,
      reassoc_of% (pullbackCompObjIso_hom_left_fst W a g b hw), pullback.lift_fst_assoc,
      pullbackCompObjIso_hom_left_snd]

end PullbackComp

section CanonicalRefinement

open MorphismOfSchemeFamilies

attribute [local implicit_reducible] MorphismOfSchemeFamilies.pullbackFunctor
  CanonicalDatum.datum CanonicalDatum.functor

/-- The component at `i` of the pullback of a morphism of descent data along a morphism of
families is the base change of the component at the corresponding index. -/
lemma pullbackFunctor_map_hom (F : MorphismOfSchemeFamilies.{u})
    {D E : DescentData F.targetFamily.f} (φ : D ⟶ E) (i : F.sourceFamily.I₀) :
    ((pullbackFunctor F).functor.map φ).hom i =
      (Over.pullback (F.familyHom.h₀ i)).map (φ.hom (F.familyHom.s₀ i)) := by
  have h := (pullbackFunctor F).map D E φ i
  simp only [pulledBackDatumObjIso, eqToIso.hom, eqToHom_refl] at h
  exact h.symm

variable {S : Scheme.{u}} {U V : PreZeroHypercover.{u} S}

/-- The component at `i` of the identification of the pullback along a refinement of the
canonical descent datum of `W` with the canonical descent datum of `W`. -/
lemma pullbackFunctorCanonicalObjIso_hom_hom (α : U.HomOver V (𝟙 S)) (W : Over S) (i : U.I₀) :
    ((pullbackFunctorCanonicalObjIso α W).hom).hom i =
      (refinementCanonicalObjIso α W i).hom := by
  simp [pullbackFunctorCanonicalObjIso, pulledBackCanonicalDatumIso,
    DescentData.isoCanonicalDatum, DescentData.toCanonicalDatum]

/-- **The canonical-descent-datum functors are identified along a refinement.** Pulling the
canonical descent datum relative to `𝒱` back along a refinement of `𝒱` by `𝒰` is, naturally in
the scheme over the base, the canonical descent datum relative to `𝒰`. -/
def pullbackFunctorCanonicalIso (α : U.HomOver V (𝟙 S)) :
    (canonicalFamilyDescentFunctor V.f).functor ⋙ (pullbackFunctor (ofRefinement α)).functor ≅
      (canonicalFamilyDescentFunctor U.f).functor :=
  NatIso.ofComponents (pullbackFunctorCanonicalObjIso α) fun {W W'} g ↦
    DescentData.hom_ext fun i ↦ by
      simp only [DescentData.comp_hom, Functor.comp_map,
        pullbackFunctorCanonicalObjIso_hom_hom, pullbackFunctor_map_hom,
        refinementCanonicalObjIso]
      exact pullbackCompObjIso_naturality (α.h₀ i) (V.f (α.s₀ i)) (U.f i)
        ((α.w₀ i).trans (Category.comp_id _)) g

end CanonicalRefinement

section FullyFaithful

open MorphismOfSchemeFamilies

attribute [local implicit_reducible] MorphismOfSchemeFamilies.pullbackFunctor
  CanonicalDatum.datum CanonicalDatum.functor

/-- The component at `i` of the canonical descent datum of a morphism of schemes over the base
is its base change along the `i`-th member of the family. -/
lemma canonicalFamilyDescentFunctor_map_hom {I : Type*} {T : Scheme.{u}} {Z : I → Scheme.{u}}
    (f : ∀ i, Z i ⟶ T) {W W' : Over T} (g : W ⟶ W') (i : I) :
    ((canonicalFamilyDescentFunctor f).functor.map g).hom i = (Over.pullback (f i)).map g := rfl

variable (S : Scheme.{u})

/-- The one-member family consisting of the identity of `S`, indexed by `PUnit` in the universe of
the schemes. -/
abbrev idFamily : PreZeroHypercover.{u} S where
  I₀ := PUnit.{u + 1}
  X _ := S
  f _ := 𝟙 S

/-- The canonical descent datum relative to the one-member family of the identity of `S` is a
fully faithful embedding of the schemes over `S`. -/
def canonicalIdFamilyFullyFaithful :
    (canonicalFamilyDescentFunctor (idFamily S).f).functor.FullyFaithful :=
  let h : (Over.pullback (𝟙 S)).FullyFaithful :=
    Functor.FullyFaithful.ofIso (Functor.FullyFaithful.ofFullyFaithful (𝟭 (Over S)))
      Over.pullbackId.symm
  { preimage := fun {_ _} φ ↦ h.preimage (φ.hom ⟨⟩)
    map_preimage := fun {_ _} φ ↦ DescentData.hom_ext fun i ↦ by
      obtain ⟨⟩ := i
      exact h.map_preimage (φ.hom ⟨⟩)
    preimage_map := fun {_ _} g ↦ h.preimage_map g }

variable {S}

/-- A family of morphisms with target `S` refines the one-member family of the identity
of `S`. -/
def toIdFamilyHom (𝒰 : PreZeroHypercover.{u} S) : 𝒰.HomOver (idFamily S) (𝟙 S) where
  s₀ _ := ⟨⟩
  h₀ i := 𝒰.f i
  w₀ _ := by simp

namespace DescentData

/-- **Fully faithful descent along an fpqc covering family.** If `𝒰` is a covering family for the
fpqc topology over an arbitrary base, the canonical-descent-datum functor from the schemes over the
base to the descent data relative to `𝒰` is fully faithful. -/
theorem canonicalFamilyDescentFunctor_fullyFaithful_of_fpqc {𝒰 : PreZeroHypercover.{u} S}
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) :
    Nonempty (canonicalFamilyDescentFunctor 𝒰.f).functor.FullyFaithful := by
  obtain ⟨hP⟩ := pullbackFunctor_fullyFaithful_of_fpqcRefiningFamily (toIdFamilyHom 𝒰) h𝒰
  exact ⟨Functor.FullyFaithful.ofIso ((canonicalIdFamilyFullyFaithful S).comp hP)
    (pullbackFunctorCanonicalIso (toIdFamilyHom 𝒰))⟩

/-- **Uniqueness of the descended morphism.** Along a covering family for the fpqc topology, a
morphism between the canonical descent data of two schemes over the base is the canonical datum
of exactly one morphism of schemes over the base. -/
theorem existsUnique_canonicalFamilyDatum_hom {𝒰 : PreZeroHypercover.{u} S}
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) {W W' : Over S}
    (φ : (canonicalFamilyDescentFunctor 𝒰.f).functor.obj W ⟶
      (canonicalFamilyDescentFunctor 𝒰.f).functor.obj W') :
    ∃! ψ : W ⟶ W', (canonicalFamilyDescentFunctor 𝒰.f).functor.map ψ = φ := by
  obtain ⟨hff⟩ := canonicalFamilyDescentFunctor_fullyFaithful_of_fpqc h𝒰
  exact ⟨hff.preimage φ, hff.map_preimage φ, fun ψ hψ ↦ by rw [← hψ, hff.preimage_map]⟩

/-- **Uniqueness of the descended scheme.** Two schemes over the base whose canonical descent
data relative to a covering family for the fpqc topology are isomorphic are isomorphic over the
base. -/
theorem nonempty_iso_of_canonicalFamilyDatum_iso {𝒰 : PreZeroHypercover.{u} S}
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) {W W' : Over S}
    (e : (canonicalFamilyDescentFunctor 𝒰.f).functor.obj W ≅
      (canonicalFamilyDescentFunctor 𝒰.f).functor.obj W') :
    Nonempty (W ≅ W') :=
  (canonicalFamilyDescentFunctor_fullyFaithful_of_fpqc h𝒰).elim fun hff ↦ ⟨hff.preimageIso e⟩

/-- Two morphisms of schemes over the base with the same canonical datum relative to a covering
family for the fpqc topology are equal. -/
@[sga "3 X 4.3" "Injectivity"]
theorem eq_of_canonicalFamilyDatum_map_eq {𝒰 : PreZeroHypercover.{u} S}
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) {W W' : Over S}
    {ψ₁ ψ₂ : W ⟶ W'}
    (h : (canonicalFamilyDescentFunctor 𝒰.f).functor.map ψ₁ =
      (canonicalFamilyDescentFunctor 𝒰.f).functor.map ψ₂) : ψ₁ = ψ₂ :=
  (canonicalFamilyDescentFunctor_fullyFaithful_of_fpqc h𝒰).elim fun hff ↦ hff.map_injective h

/-- **Uniqueness of the descended scheme over an open of the base.** Two schemes over an open
`U` of `S` whose canonical descent data relative to the restriction to `U` of a covering family
for the fpqc topology are isomorphic are isomorphic over `U`. -/
theorem nonempty_iso_of_restrictBase_canonicalFamilyDatum_iso {𝒰 : PreZeroHypercover.{u} S}
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) (U : S.Opens)
    {W W' : Over U.toScheme}
    (e : (canonicalFamilyDescentFunctor (PreZeroHypercover.restrictBase 𝒰 U).f).functor.obj W ≅
      (canonicalFamilyDescentFunctor (PreZeroHypercover.restrictBase 𝒰 U).f).functor.obj W') :
    Nonempty (W ≅ W') :=
  nonempty_iso_of_canonicalFamilyDatum_iso
    (PreZeroHypercover.mem_fpqcPrecoverage_restrictBase 𝒰 U h𝒰) e

/-- **Uniqueness of the descended morphism over an open of the base.** Two morphisms of schemes
over an open `U` of `S` with the same canonical datum relative to the restriction to `U` of a
covering family for the fpqc topology are equal. -/
@[sga "3 X 4.3" "Injectivity clause"]
theorem eq_of_restrictBase_canonicalFamilyDatum_map_eq {𝒰 : PreZeroHypercover.{u} S}
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) (U : S.Opens)
    {W W' : Over U.toScheme} {ψ₁ ψ₂ : W ⟶ W'}
    (h : (canonicalFamilyDescentFunctor (PreZeroHypercover.restrictBase 𝒰 U).f).functor.map ψ₁ =
      (canonicalFamilyDescentFunctor (PreZeroHypercover.restrictBase 𝒰 U).f).functor.map ψ₂) :
    ψ₁ = ψ₂ :=
  eq_of_canonicalFamilyDatum_map_eq
    (PreZeroHypercover.mem_fpqcPrecoverage_restrictBase 𝒰 U h𝒰) h

end DescentData

end FullyFaithful

namespace Scheme

/-- A gluing datum relative to an open cover of a base scheme `S` in which the transition
morphisms are given only over the double overlaps: an open cover `{base i}` of `S`, a scheme
`obj i` over each `base i`, and transition morphisms over the base between the preimages of
`base j` in `obj i` and of `base i` in `obj j`. -/
structure RelativeGlueCore (S : Scheme.{u}) where
  /-- The index type of the cover of the base. -/
  J : Type u
  /-- The `i`-th member of the open cover of the base. -/
  base : J → S.Opens
  /-- The members of `base` cover the base. -/
  iSup_base : ⨆ i, base i = ⊤
  /-- The scheme living over the `i`-th member of the cover. -/
  obj : J → Scheme.{u}
  /-- The structure morphism of `obj i`, as a morphism to the base. -/
  proj : ∀ i, obj i ⟶ S
  /-- The structure morphism of `obj i` factors through `base i`. -/
  proj_preimage_eq_top : ∀ i, proj i ⁻¹ᵁ base i = ⊤
  /-- The transition morphism over `base i ⊓ base j`. -/
  t : ∀ i j, (proj i ⁻¹ᵁ base j).toScheme ⟶ (proj j ⁻¹ᵁ base i).toScheme
  /-- The transitions are morphisms over the base. -/
  t_over : ∀ i j, t i j ≫ (proj j ⁻¹ᵁ base i).ι ≫ proj j = (proj i ⁻¹ᵁ base j).ι ≫ proj i

namespace RelativeGlueCore

variable {S : Scheme.{u}}

/-- A morphism which factors through an open of its target has that open as its whole
preimage. -/
lemma preimage_comp_ι_eq_top {X : Scheme.{u}} {U : S.Opens} (p : X ⟶ U.toScheme) :
    (p ≫ U.ι) ⁻¹ᵁ U = ⊤ := by
  rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

/-- A relative gluing datum whose pieces are presented as schemes over the members of the open
cover of the base: the structure morphism of the `i`-th piece is its structure morphism over
`base i` followed by the inclusion of `base i`. -/
def ofPieces {J : Type u} (base : J → S.Opens) (hbase : ⨆ i, base i = ⊤)
    (P : ∀ i, Over (base i).toScheme)
    (t : ∀ i j, (((P i).hom ≫ (base i).ι) ⁻¹ᵁ base j).toScheme ⟶
      (((P j).hom ≫ (base j).ι) ⁻¹ᵁ base i).toScheme)
    (t_over : ∀ i j, t i j ≫ ((((P j).hom ≫ (base j).ι)) ⁻¹ᵁ base i).ι ≫
        ((P j).hom ≫ (base j).ι) =
      ((((P i).hom ≫ (base i).ι)) ⁻¹ᵁ base j).ι ≫ ((P i).hom ≫ (base i).ι)) :
    RelativeGlueCore S where
  J := J
  base := base
  iSup_base := hbase
  obj i := (P i).left
  proj i := (P i).hom ≫ (base i).ι
  proj_preimage_eq_top i := preimage_comp_ι_eq_top (P i).hom
  t := t
  t_over := t_over

variable (C : RelativeGlueCore S)

/-- The overlap `pᵢ⁻¹(Sⱼ)`, an open subscheme of `obj i`. -/
abbrev overlap (i j : C.J) : (C.obj i).Opens := C.proj i ⁻¹ᵁ C.base j

/-- The transition morphism restricted to the triple overlap inside `obj i`. -/
def tripleMap (i j k : C.J) :
    (C.overlap i j ⊓ C.overlap i k).toScheme ⟶ (C.overlap j i).toScheme :=
  (C.obj i).homOfLE inf_le_left ≫ C.t i j

/-- The restricted transition morphism lies over the base. -/
lemma tripleMap_ι_proj (i j k : C.J) :
    C.tripleMap i j k ≫ (C.overlap j i).ι ≫ C.proj j =
      (C.overlap i j ⊓ C.overlap i k).ι ≫ C.proj i := by
  rw [tripleMap, Category.assoc, C.t_over i j, ← Category.assoc, Scheme.homOfLE_ι]

/-- The restricted transition morphism lands in the triple overlap inside `obj j`: a point of
`obj i` over `base j ⊓ base k` is carried to a point of `obj j` over the same member of the
cover of the base. -/
lemma range_tripleMap_ι (i j k : C.J) :
    Set.range (C.tripleMap i j k ≫ (C.overlap j i).ι) ⊆
      Set.range (C.overlap j k ⊓ C.overlap j i).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have hx : (C.overlap i j ⊓ C.overlap i k).ι x ∈ C.overlap i j ⊓ C.overlap i k :=
    (Scheme.Opens.range_ι _).le ⟨x, rfl⟩
  refine ⟨?_, (Scheme.Opens.range_ι _).le
    ⟨C.tripleMap i j k x, (Scheme.Hom.comp_apply _ _ _).symm⟩⟩
  show C.proj j ((C.tripleMap i j k ≫ (C.overlap j i).ι) x) ∈ C.base k
  rw [← Scheme.Hom.comp_apply, Category.assoc, C.tripleMap_ι_proj i j k, Scheme.Hom.comp_apply]
  exact hx.2

/-- The transition morphism on triple overlaps, built from the transition on double overlaps
by restriction. -/
def t' (i j k : C.J) :
    (C.overlap i j ⊓ C.overlap i k).toScheme ⟶ (C.overlap j k ⊓ C.overlap j i).toScheme :=
  IsOpenImmersion.lift (C.overlap j k ⊓ C.overlap j i).ι
    (C.tripleMap i j k ≫ (C.overlap j i).ι) (C.range_tripleMap_ι i j k)

/-- The transition morphism on triple overlaps, followed by the inclusion of the triple
overlap, is the restricted transition morphism. -/
@[reassoc]
lemma t'_ι (i j k : C.J) :
    C.t' i j k ≫ (C.overlap j k ⊓ C.overlap j i).ι =
      C.tripleMap i j k ≫ (C.overlap j i).ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- On triple overlaps the constructed transition morphism restricts the one on double
overlaps. -/
lemma t'_fac (i j k : C.J) :
    C.t' i j k ≫ (C.obj j).homOfLE inf_le_right =
      (C.obj i).homOfLE inf_le_left ≫ C.t i j := by
  rw [← cancel_mono (C.overlap j i).ι, Category.assoc, Scheme.homOfLE_ι, C.t'_ι, tripleMap,
    Category.assoc]

/-- **The transitions on double overlaps suffice.** A relative gluing datum whose transition
morphisms are given only over the double overlaps, and which satisfies the reflexivity and
cocycle conditions, is a relative gluing datum in the sense of
`AlgebraicGeometry.Scheme.RelativeGlueData`. -/
def toRelativeGlueData (ht : ∀ i, C.t i i = 𝟙 _)
    (hc : ∀ i j k, C.t' i j k ≫ C.t' j k i ≫ C.t' k i j = 𝟙 _) : RelativeGlueData S where
  J := C.J
  base := C.base
  iSup_base := C.iSup_base
  obj := C.obj
  proj := C.proj
  proj_preimage_eq_top := C.proj_preimage_eq_top
  t := C.t
  t_over := C.t_over
  t_self := ht
  t' := C.t'
  t'_fac := C.t'_fac
  cocycle := hc

/-- **Relative gluing from transitions on double overlaps.** The pieces of a relative gluing
datum whose transitions satisfy the reflexivity and cocycle conditions assemble into a single
scheme over the base, each piece being its part over the corresponding member of the open cover
of the base. -/
theorem exists_isPullback_of_toRelativeGlueData (ht : ∀ i, C.t i i = 𝟙 _)
    (hc : ∀ i j k, C.t' i j k ≫ C.t' j k i ≫ C.t' k i j = 𝟙 _) :
    ∃ (W : Over S) (q : ∀ i, C.obj i ⟶ (C.base i).toScheme) (p : ∀ i, C.obj i ⟶ W.left),
      ∀ i, q i ≫ (C.base i).ι = C.proj i ∧ IsPullback (q i) (p i) (C.base i).ι W.hom :=
  ⟨Over.mk (C.toRelativeGlueData ht hc).toBase, (C.toRelativeGlueData ht hc).projRestrict,
    (C.toRelativeGlueData ht hc).ι, fun i ↦
      ⟨(C.toRelativeGlueData ht hc).projRestrict_ι i,
        (C.toRelativeGlueData ht hc).isPullback_projRestrict_ι i⟩⟩

end RelativeGlueCore

end Scheme

end AlgebraicGeometry

end

end
