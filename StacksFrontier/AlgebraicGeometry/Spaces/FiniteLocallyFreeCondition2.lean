module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeZariskiCover

/-!
# Condition (2) of Stacks 03ZW

Stacks 03ZW asserts the equivalence of four conditions on a morphism `f : X ⟶ Y` of algebraic
spaces over a scheme `S`:

1. `f` is representable and finite locally free,
2. `f` is finite locally free,
3. there exists a scheme `V` and a surjective étale morphism `V ⟶ Y` such that `V ×_Y X ⟶ V`
   is finite locally free, and
4. there exists a Zariski covering `Y = ⋃ Yᵢ` such that each `f⁻¹(Yᵢ) ⟶ Yᵢ` is finite locally
   free.

`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal` proves the equivalence of
(1), (3) and (4), and
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart` proves Stacks 03ZU:
for a *representable* `f`, condition (1) is condition (2).  **This file adds condition (2) to the
equivalence**, by removing the representability hypothesis from Stacks 03ZU and composing.

Condition (2) is the definition of Stacks 03ZV,
`AlgebraicGeometry.Space.IsFiniteLocallyFree` — `f` is affine and the direct image `f_*𝒪_X` is a
finite locally free `𝒪_Y`-module on the small étale ringed site of `Y` — and unlike conditions
(1), (3) and (4) it carries no representability assumption.  It needs none: its affineness
conjunct already gives representability, by
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`, the representability conjunct
of condition (1) of Stacks 03WG.  So the absence of a representability hypothesis in condition
(2) costs nothing, and that is the only thing between Stacks 03ZU and condition (2) of
Stacks 03ZW.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFree_tfae`: **Stacks 03ZW**, the equivalence of all
  four conditions, assembled from the pairwise equivalences below.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isFiniteLocallyFree`: a finite locally free
  morphism of algebraic spaces is representable.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree`: **Stacks 03ZW,
  conditions (1) and (2)**.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_iff_exists_etaleChart` and
  `AlgebraicGeometry.Space.isFiniteLocallyFree_iff_exists_zariskiCover`: conditions (2) and (3),
  and conditions (2) and (4).

## Implementation notes

The comparison of the two notions of finite local freeness at a chart — condition (1) imposes
finite local freeness on the Zariski site of a chart scheme, through
`Stacks.Morphisms.pushforwardStructureSheaf` of the represented base change, while condition (2)
imposes it on the small étale site of `Y`, through
`AlgebraicGeometry.Space.pushforwardStructureModule` — is not performed here.  It is Stacks 03ZU,
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree`, whose chart comparison is
`AlgebraicGeometry.Space.isFiniteLocallyFree_baseChange_iff_chart` and whose module conjunct
rests on `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sliceAssociatedModule_iff`.

*No rank clause.*  Stacks 03ZW states no rank, so the rank refinements of its conditions are not
stated here.  The rank form of Stacks 03ZU is not available either: it would need the rank
analogue of `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff`, which
the tree does not carry, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart` record.  The rank
statement this file does prove, `relativelyRepresentable_of_isFiniteLocallyFreeOfRank`, concerns
only representability and so needs no rank transport.

## References

* [Stacks Project, Tag 03HA](https://stacks.math.columbia.edu/tag/03HA)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Condition (2) implies representability -/

/-- **A finite locally free morphism of algebraic spaces is representable.**

Condition (2) of Stacks 03ZW makes no representability assumption, and it needs none: its
affineness conjunct already gives representability, by
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`, which is the representability
conjunct of condition (1) of Stacks 03WG reached from condition (2) of that tag. -/
theorem relativelyRepresentable_of_isFiniteLocallyFree {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFiniteLocallyFree B S hS f) : yoneda.relativelyRepresentable f.hom :=
  relativelyRepresentable_of_isAffineHom B S hS f hf.1

/-- A morphism of algebraic spaces which is finite locally free of rank `r` is representable. -/
theorem relativelyRepresentable_of_isFiniteLocallyFreeOfRank {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {r : ℕ} (hf : IsFiniteLocallyFreeOfRank B S hS f r) :
    yoneda.relativelyRepresentable f.hom :=
  relativelyRepresentable_of_isFiniteLocallyFree B S hS f hf.1

/-- Pullbacks of presheaves on `BigFppfOver B S hS` (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_FiniteLocallyFreeCondition2
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Stacks 03ZW, condition (2) -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03ZW, conditions (1) and (2).** A morphism of algebraic spaces over `S` is
representable with every represented base change a finite locally free morphism of schemes
exactly when it is finite locally free in the sense of Stacks 03ZV.

No representability hypothesis is imposed, which is what distinguishes this from Stacks 03ZU,
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree`: from condition (1) representability
is `CategoryTheory.MorphismProperty.relative.rep`, and from condition (2) it is
`AlgebraicGeometry.Space.relativelyRepresentable_of_isFiniteLocallyFree`. -/
@[stacks 03ZW "conditions (1) and (2)"]
theorem isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree (f : X ⟶ Y) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f.hom ↔
      IsFiniteLocallyFree B S hS f :=
  ⟨fun h => (presheaf_iff_isFiniteLocallyFree B S hS f h.rep).1 h,
    fun h => (presheaf_iff_isFiniteLocallyFree B S hS f
      (relativelyRepresentable_of_isFiniteLocallyFree B S hS f h)).2 h⟩

/-- **Stacks 03ZW, conditions (2) and (3).** A morphism of algebraic spaces over `S` is finite
locally free in the sense of Stacks 03ZV exactly when there is one surjective étale morphism from
a representable presheaf onto its target along which its base change is representable and finite
locally free.

This is `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree` composed
with `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_exists_etaleChart`, conditions (1)
and (3). -/
@[stacks 03ZW "conditions (2) and (3)"]
theorem isFiniteLocallyFree_iff_exists_etaleChart (f : X ⟶ Y) :
    IsFiniteLocallyFree B S hS f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1),
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage
          (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f.hom g) :=
  (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS f).symm.trans
    (isFiniteLocallyFree_presheaf_iff_exists_etaleChart B S hS X.2 Y.2 f.hom)

/-- **Stacks 03ZW, conditions (2) and (4).** A morphism of algebraic spaces over `S` is finite
locally free in the sense of Stacks 03ZV exactly when there is a Zariski covering `Y = ⋃ Yᵢ` of
its target such that each `f⁻¹(Yᵢ) ⟶ Yᵢ` is representable and finite locally free.

This is `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree` composed
with `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_exists_zariskiCover`, conditions
(1) and (4). -/
@[stacks 03ZW "conditions (2) and (4)"]
theorem isFiniteLocallyFree_iff_exists_zariskiCover (f : X ⟶ Y) :
    IsFiniteLocallyFree B S hS f ↔
      ∃ (I : Type u) (U : I → Subfunctor Y.1),
        IsZariskiCover B S hS I U ∧
        ∀ i, (MorphismProperty.inverseImage
          (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f.hom (U i).ι) :=
  (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS f).symm.trans
    (isFiniteLocallyFree_presheaf_iff_exists_zariskiCover B S hS X.2 Y.2 f.hom)

/-! ### Stacks 03ZW, all four conditions -/

/-- **Stacks 03ZW.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are
equivalent:

1. `f` is representable and finite locally free, i.e. every represented base change of `f` is a
   finite locally free morphism of schemes;
2. `f` is finite locally free in the sense of Stacks 03ZV: affine, with `f_*𝒪_X` a finite
   locally free `𝒪_Y`-module;
3. there exists a scheme `V` and a surjective étale morphism `V ⟶ Y` such that
   `V ×_Y X ⟶ V` is (representable and) finite locally free;
4. there exists a Zariski covering `Y = ⋃ Yᵢ` such that each `f⁻¹(Yᵢ) ⟶ Yᵢ` is (representable
   and) finite locally free.

Assembled from the pairwise equivalences
`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree`,
`AlgebraicGeometry.Space.isFiniteLocallyFree_iff_exists_etaleChart` and
`AlgebraicGeometry.Space.isFiniteLocallyFree_iff_exists_zariskiCover`. -/
@[stacks 03ZW]
theorem isFiniteLocallyFree_tfae (f : X ⟶ Y) :
    List.TFAE
      [(MorphismProperty.inverseImage
          (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f.hom,
        IsFiniteLocallyFree B S hS f,
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1),
          (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf g ∧
          (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf g ∧
          (MorphismProperty.inverseImage
            (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f.hom g),
        ∃ (I : Type u) (U : I → Subfunctor Y.1),
          IsZariskiCover B S hS I U ∧
          ∀ i, (MorphismProperty.inverseImage
            (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f.hom (U i).ι)] := by
  tfae_have 1 ↔ 2 := isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS f
  tfae_have 2 ↔ 3 := isFiniteLocallyFree_iff_exists_etaleChart B S hS f
  tfae_have 2 ↔ 4 := isFiniteLocallyFree_iff_exists_zariskiCover B S hS f
  tfae_finish

end AlgebraicGeometry.Space

end
