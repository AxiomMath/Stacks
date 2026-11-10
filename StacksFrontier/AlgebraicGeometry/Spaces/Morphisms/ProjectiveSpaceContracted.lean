module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceRationalPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ConstantOverAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SliceFiniteProducts

/-!
# A projective space over an affine part of the base, mapping into something finite, is contracted

Let `S` be a scheme contained in a big fppf site, let `L` be the functor of points of `ℙⁿ_S` over
that site, and let `V` be an object of the site whose underlying scheme is affine — a
field-valued point of an algebraic space, say.  This file proves that a morphism
`L × V ⟶ Z` of algebraic spaces over `S` which factors through an algebraic space *finite over
`V`* does not depend on the `L` coordinate: it is the projection `L × V ⟶ V` followed by a
`V`-valued point of `Z`.

That statement is the geometric input of the rigidity argument of [Stacks, Tag 0AEL], and it is
exactly the hypothesis `hc` of
`AlgebraicGeometry.Space.exists_eq_comp_snd_of_contracted_on_dense_base`: [Stacks, Tag 0AEJ]
produces an open neighbourhood over which a proper family factors through a closed subspace
finite over the base, and what turns such a factorization into a *contraction* is that a
projective space over a field has no nonconstant functions.

## What the transport consists of

The corresponding statement for schemes is
`AlgebraicGeometry.exists_comp_eq_structureMorphism_of_projectiveSpaceOver`.  Three steps carry
it to algebraic spaces, that is, to functors of points over the site.

*The target is representable by an affine object of the site.*  Finiteness of a morphism of
algebraic spaces is tested on affine test objects of the target, and here the target is the
functor of points of the affine object `V` itself, so the test along the identity presents the
source of the finite morphism as the functor of points of an affine object of the site.  Only
affineness of that representative is used below — not the finiteness of its projection, and not
that the subspace it sits in is closed.

*The product is projective space over `V`.*  The comparison functor from the site to schemes
over `S` preserves finite products, a binary product in a slice is a fibre product over the
base, and `ℙⁿ_S ×_S V = ℙⁿ_V` because projective space is stable under base change.  So the
product formed in the site has `ℙⁿ_{V}` as its underlying scheme, compatibly with the
projection to `V`.

*The factorization descends to the site.*  The comparison functor is fully faithful, so the
scheme-level factorization is a factorization of morphisms of the site once its second factor is
known to lie over `S`; and it does, because the projection `ℙⁿ_V ⟶ V` has a section
(`AlgebraicGeometry.exists_section_projectiveSpaceOver`) and is therefore a split epimorphism.

## Main results

* `AlgebraicGeometry.Space.contains_projectiveSpaceOver` and
  `AlgebraicGeometry.Space.projectiveSpaceSiteObject`: `ℙⁿ_S` as an object of the site.
* `AlgebraicGeometry.Space.exists_iso_prod_projectiveSpaceOver`: the product of `ℙⁿ_S` with an
  object `V` of the site is projective space over the scheme underlying `V`.
* `AlgebraicGeometry.Space.exists_isIso_yoneda_of_isFinite`: an algebraic space finite over the
  functor of points of an affine object of the site is itself the functor of points of an affine
  object of the site.
* `AlgebraicGeometry.Space.exists_comp_eq_prod_snd_of_isFinite`: **a morphism out of
  `ℙⁿ_S × V`, with `V` affine, which factors through something finite over `V` is contracted** —
  it is the projection to `V` followed by a `V`-valued point of the target.
* `AlgebraicGeometry.Space.exists_comp_eq_prod_snd_of_isFinite_projectiveSpaceFunctor`: the same
  with the first factor given as the restricted functor of points of `ℙⁿ_S`, which is the shape
  the rigidity statements are phrased with — for `n = 1` and `S = Spec k` that first factor is
  `AlgebraicGeometry.Space.projectiveLineFunctor`.
* `AlgebraicGeometry.Space.exists_comp_eq_prod_snd_of_isFinite_fieldValuedPoint`: **the same at a
  field-valued point of an algebraic space**, which is the part of the base a contraction
  argument reads the hypothesis `hc` on.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEL](https://stacks.math.columbia.edu/tag/0AEL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (n : ℕ)

/-! ### Projective space over the base as an object of the site -/

include hS in
/-- **Projective space over the base belongs to the big fppf site**, being proper, hence locally
of finite type and quasi-compact, over the base. -/
theorem contains_projectiveSpaceOver : B.Contains (projectiveSpaceOver n S) := by
  let : _root_.AlgebraicGeometry.IsProper (projectiveSpaceOver n S ↘ S) := inferInstance
  change (projectiveSpaceOver n S).size < B.cutoff
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (projectiveSpaceOver n S ↘ S) hS

/-- **Projective space over the base, as an object of the big fppf site over the base.** -/
def projectiveSpaceSiteObject : BigFppfOver B S hS :=
  siteObject B S hS (contains_projectiveSpaceOver B S hS n) (projectiveSpaceOver n S ↘ S)

/-- **The restricted functor of points of projective space over the base.** For `n = 1` and
`S = Spec k` this is `AlgebraicGeometry.Space.projectiveLineFunctor`. -/
abbrev projectiveSpaceFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Over.post (X := B.obj hS) B.inclusion).op ⋙
    yoneda.obj (Over.mk (projectiveSpaceOver n S ↘ S))

/-- **The restricted functor of points of projective space over the base is represented by the
corresponding object of the site.** -/
def projectiveSpaceFunctorIso :
    projectiveSpaceFunctor B S hS n ≅ yoneda.obj (projectiveSpaceSiteObject B S hS n) :=
  bigFppfOverRestrictedYonedaIso B S hS (projectiveSpaceSiteObject B S hS n)

/-! ### The product with an object of the site is projective space over that object -/

/-- **The product of `ℙⁿ_S` with an object `V` of the site is projective space over the scheme
underlying `V`**, compatibly with the projection to `V`.

The comparison functor to schemes over `S` preserves finite products, and a binary product in a
slice category is a fibre product over the base, so the underlying scheme of the product is the
fibre product `ℙⁿ_S ×_S V`; and that is `ℙⁿ_V`, projective space being stable under base change
(`AlgebraicGeometry.isPullback_projectiveSpaceOverMap`). -/
theorem exists_iso_prod_projectiveSpaceOver (V : BigFppfOver B S hS) :
    ∃ α : ((Over.post (X := B.obj hS) B.inclusion).obj
          (projectiveSpaceSiteObject B S hS n ⨯ V)).left ≅
        projectiveSpaceOver n ((Over.post (X := B.obj hS) B.inclusion).obj V).left,
      α.hom ≫ (projectiveSpaceOver n ((Over.post (X := B.obj hS) B.inclusion).obj V).left ↘
          ((Over.post (X := B.obj hS) B.inclusion).obj V).left) =
        ((Over.post (X := B.obj hS) B.inclusion).map
          (prod.snd : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ V)).left := by
  have := preservesFiniteProducts_overPost_bigFppfInclusion B S hS
  have hfan : IsLimit (BinaryFan.mk
      ((Over.post (X := B.obj hS) B.inclusion).map
        (prod.fst : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ projectiveSpaceSiteObject B S hS n))
      ((Over.post (X := B.obj hS) B.inclusion).map
        (prod.snd : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ V))) :=
    mapIsLimitOfPreservesOfIsLimit _ _ _ (prodIsProd _ _)
  have hmine : IsPullback
      ((Over.post (X := B.obj hS) B.inclusion).map
        (prod.fst : projectiveSpaceSiteObject B S hS n ⨯ V ⟶
          projectiveSpaceSiteObject B S hS n)).left
      ((Over.post (X := B.obj hS) B.inclusion).map
        (prod.snd : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ V)).left
      (projectiveSpaceOver n S ↘ S)
      ((Over.post (X := B.obj hS) B.inclusion).obj V).hom :=
    IsPullback.of_isLimit (IsLimit.pullbackConeEquivBinaryFanInverse hfan)
  exact ⟨hmine.isoIsPullback _ _ (isPullback_projectiveSpaceOverMap n
      ((Over.post (X := B.obj hS) B.inclusion).obj V).hom),
    hmine.isoIsPullback_hom_snd _ _ _⟩

/-! ### An algebraic space finite over an affine object of the site -/

/-- **An algebraic space finite over the functor of points of an affine object of the site is
the functor of points of an affine object of the site.** Finiteness is tested on affine test
objects of the target, and the target is already such a test object: the test along the identity
exhibits the source as a base change along an identity, hence as the representable itself.

Only the affineness of the representative is recorded; the finiteness of its projection to `V`
is not used by the contraction statement. -/
theorem exists_isIso_yoneda_of_isFinite {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (w : W ⟶ yoneda.obj V) (hw : IsFinite B S hS w) :
    ∃ (V' : BigFppfOver B S hS) (ι : yoneda.obj V' ⟶ W),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V') ∧ IsIso ι := by
  obtain ⟨V', _, ι, hV', _, hpb⟩ := hw V hV (𝟙 _)
  exact ⟨V', ι, hV', hpb.isIso_fst_of_isIso⟩

/-! ### Contraction -/

/-- The product of `L ≅ ℙⁿ_S` with the functor of points of `V` is the functor of points of the
product in the site, compatibly with the second projection. -/
private theorem exists_iso_prod_yoneda_projectiveSpaceSiteObject
    {L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (eL : L ≅ yoneda.obj (projectiveSpaceSiteObject B S hS n)) (V : BigFppfOver B S hS)
    [HasBinaryProduct L (yoneda.obj V)] :
    ∃ E : (L ⨯ yoneda.obj V) ≅ yoneda.obj (projectiveSpaceSiteObject B S hS n ⨯ V),
      E.hom ≫ yoneda.map (prod.snd : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ V) =
        prod.snd := by
  have hyfan : IsLimit (BinaryFan.mk
      (yoneda.map (prod.fst : projectiveSpaceSiteObject B S hS n ⨯ V ⟶
        projectiveSpaceSiteObject B S hS n) ≫ eL.inv)
      (yoneda.map (prod.snd : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ V))) :=
    BinaryFan.isLimitCompLeftIso _ eL.inv
      (mapIsLimitOfPreservesOfIsLimit yoneda _ _ (prodIsProd _ _))
  refine ⟨IsLimit.conePointUniqueUpToIso (prodIsProd L (yoneda.obj V)) hyfan, ?_⟩
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (prodIsProd L (yoneda.obj V)) hyfan ⟨WalkingPair.right⟩

/-- **A projective space over an affine part of the base, mapping into something finite over
that part, is contracted.** Let `V` be an object of the big fppf site over `S` with affine
underlying scheme, let `L` be the functor of points of `ℙⁿ_S`, and let `θ : L × V ⟶ Z` be a
morphism of algebraic spaces over `S` which factors as `μ ≫ i` through an algebraic space `W`
finite over `V`.  Then `θ` factors through the projection `L × V ⟶ V`.

So the morphism does not depend on the `L` coordinate: the complete fibre `ℙⁿ` is contracted to
a `V`-valued point of `Z`.  Nothing is assumed of `i` — in the application it is the inclusion
of a closed subspace, but closedness plays no role; and the finiteness of `W` over `V` is used
only through the affineness of the scheme representing `W`. -/
theorem exists_comp_eq_prod_snd_of_isFinite {L W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (eL : L ≅ yoneda.obj (projectiveSpaceSiteObject B S hS n))
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [HasBinaryProduct L (yoneda.obj V)]
    (w : W ⟶ yoneda.obj V) (hw : IsFinite B S hS w) (i : W ⟶ Z)
    (μ : L ⨯ yoneda.obj V ⟶ W) (θ : L ⨯ yoneda.obj V ⟶ Z) (hθ : μ ≫ i = θ) :
    ∃ c : yoneda.obj V ⟶ Z, θ = prod.snd ≫ c := by
  classical
  obtain ⟨V', ι, hV', hι⟩ := exists_isIso_yoneda_of_isFinite B S hS V hV w hw
  obtain ⟨α, hα⟩ := exists_iso_prod_projectiveSpaceOver B S hS n V
  have := hι
  have : IsAffine ((Over.post (X := B.obj hS) B.inclusion).obj V).left := hV
  have : IsAffine ((Over.post (X := B.obj hS) B.inclusion).obj V').left := hV'
  obtain ⟨E, hE⟩ := exists_iso_prod_yoneda_projectiveSpaceSiteObject B S hS n eL V
  -- The induced morphism of the site.
  set ρ : (projectiveSpaceSiteObject B S hS n ⨯ V) ⟶ V' :=
    Yoneda.fullyFaithful.preimage (E.inv ≫ μ ≫ inv ι)
  have hρ : yoneda.map ρ = E.inv ≫ μ ≫ inv ι := Yoneda.fullyFaithful.map_preimage _
  -- Factor the underlying morphism of schemes through the structure morphism of `ℙⁿ_V`.
  obtain ⟨d, hd⟩ := exists_comp_eq_of_isoProjectiveSpaceOver n
    ((Over.post (X := B.obj hS) B.inclusion).map
      (prod.snd : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ V)).left α hα
    ((Over.post (X := B.obj hS) B.inclusion).map ρ).left
  -- The second factor lies over `S`, the projection being a split epimorphism.
  obtain ⟨s, hs⟩ := exists_section_projectiveSpaceOver
    ((Over.post (X := B.obj hS) B.inclusion).obj V).left n
  have hsplit : (s ≫ α.inv) ≫ ((Over.post (X := B.obj hS) B.inclusion).map
      (prod.snd : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ V)).left = 𝟙 _ := by
    rw [← hα]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact hs
  have : IsSplitEpi ((Over.post (X := B.obj hS) B.inclusion).map
      (prod.snd : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ V)).left :=
    IsSplitEpi.mk' { section_ := s ≫ α.inv, id := hsplit }
  have hdover : d ≫ ((Over.post (X := B.obj hS) B.inclusion).obj V').hom =
      ((Over.post (X := B.obj hS) B.inclusion).obj V).hom := by
    refine (cancel_epi ((Over.post (X := B.obj hS) B.inclusion).map
      (prod.snd : projectiveSpaceSiteObject B S hS n ⨯ V ⟶ V)).left).1 ?_
    rw [← Category.assoc, ← hd, Over.w, Over.w]
  set δ : V ⟶ V' := (fullyFaithful_overPost_bigFppfInclusion B S hS).preimage
    (Over.homMk d hdover) with hδdef
  have hδ : ((Over.post (X := B.obj hS) B.inclusion).map δ).left = d := by
    rw [hδdef, (fullyFaithful_overPost_bigFppfInclusion B S hS).map_preimage]
    rfl
  have hρδ : ρ = prod.snd ≫ δ := by
    refine (fullyFaithful_overPost_bigFppfInclusion B S hS).map_injective
      (Over.OverMorphism.ext ?_)
    rw [Functor.map_comp, Over.comp_left, hδ, hd]
  refine ⟨yoneda.map δ ≫ ι ≫ i, ?_⟩
  rw [← hθ, ← hE, Category.assoc, ← Functor.map_comp_assoc, ← hρδ, hρ]
  simp

/-- **The contraction statement with the first factor given as the restricted functor of points
of `ℙⁿ_S`**, which is the shape the rigidity statements of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FamilyRigidity` are phrased with: for `n = 1`
and `S = Spec k` the first factor is `AlgebraicGeometry.Space.projectiveLineFunctor`.

This is the hypothesis `hc` of
`AlgebraicGeometry.Space.exists_eq_comp_snd_of_contracted_on_dense_base` at a part of the base
which is an affine object of the site. -/
theorem exists_comp_eq_prod_snd_of_isFinite_projectiveSpaceFunctor
    {W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [HasBinaryProduct (projectiveSpaceFunctor B S hS n) (yoneda.obj V)]
    (w : W ⟶ yoneda.obj V) (hw : IsFinite B S hS w) (i : W ⟶ Z)
    (μ : projectiveSpaceFunctor B S hS n ⨯ yoneda.obj V ⟶ W)
    (θ : projectiveSpaceFunctor B S hS n ⨯ yoneda.obj V ⟶ Z) (hθ : μ ≫ i = θ) :
    ∃ c : yoneda.obj V ⟶ Z, θ = prod.snd ≫ c :=
  exists_comp_eq_prod_snd_of_isFinite B S hS n (projectiveSpaceFunctorIso B S hS n) V hV w hw i
    μ θ hθ

/-- **A projective space over a field-valued point, mapping into something finite over that
point, is contracted.** A field-valued point of an algebraic space over `S` is represented by an
object of the site whose underlying scheme is the spectrum of a field, hence affine, so this is
`AlgebraicGeometry.Space.exists_comp_eq_prod_snd_of_isFinite_projectiveSpaceFunctor` at that
object.

This is the form in which a contraction argument meets the hypothesis `hc` of
`AlgebraicGeometry.Space.exists_eq_comp_snd_of_contracted_on_dense_base`: the projective line
over the residue field of a point of the base is contracted to a field-valued point of the
target, because the target of the family near that point is finite over the base there
([Stacks, Tag 0AEJ]). -/
theorem exists_comp_eq_prod_snd_of_isFinite_fieldValuedPoint
    {T W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS T)
    [HasBinaryProduct (projectiveSpaceFunctor B S hS n) (yoneda.obj p.siteObject)]
    (w : W ⟶ yoneda.obj p.siteObject) (hw : IsFinite B S hS w) (i : W ⟶ Z)
    (μ : projectiveSpaceFunctor B S hS n ⨯ yoneda.obj p.siteObject ⟶ W)
    (θ : projectiveSpaceFunctor B S hS n ⨯ yoneda.obj p.siteObject ⟶ Z) (hθ : μ ≫ i = θ) :
    ∃ c : yoneda.obj p.siteObject ⟶ Z, θ = prod.snd ≫ c :=
  exists_comp_eq_prod_snd_of_isFinite_projectiveSpaceFunctor B S hS n p.siteObject
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))) w hw i μ θ hθ

end AlgebraicGeometry.Space

end
