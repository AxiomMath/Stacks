module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteFreeActionSchematicLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient of an affine object by a free action of a finite group is affine

Let `S` be a scheme, let `V` be an object of a big fppf site over `S` with *affine* underlying
scheme and let a finite group `G` act freely on `V` over `S`. Then the quotient `V/G` of
[Stacks, Tag 071S] is an affine algebraic space over `S`: it is represented by the spectrum of
the ring of invariant functions.

## Main results

* `AlgebraicGeometry.Space.isAffine_toScheme_obj_of_isAffineSpace`: an object of the site whose
  represented presheaf is an affine algebraic space has affine underlying scheme.
* `AlgebraicGeometry.Space.isAffineSpace_actionQuotient_of_isAffine`: the quotient of an affine
  object of the site by a free action of a finite group is an affine algebraic space.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-- **An object of the big fppf site whose represented presheaf is an affine algebraic space
has affine underlying scheme.** -/
theorem isAffine_toScheme_obj_of_isAffineSpace {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (V : BigFppfOver B S hS)
    (hV : IsAffineSpace B S hS (yoneda.obj V)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) := by
  obtain ⟨T, hT, ⟨i⟩⟩ := hV
  exact _root_.AlgebraicGeometry.IsAffine.of_isIso
    ((BigFppfOver.toScheme B S hS).map (Yoneda.fullyFaithful.preimageIso i).hom)

section FreeFiniteAction

variable (G : Type v) [Group G] [Finite G] [Small.{u} G] (B : BigFppfSite.{u})
  (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (V : BigFppfOver B S hS) (a : G →* Aut (underlyingOver B hS V))
  (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a)

include ha in
/-- **The quotient of an affine object by a free action of a finite group is affine.** If the
object `V` of the site has affine underlying scheme and the finite group `G` acts freely on it,
then the quotient `V/G` is an affine algebraic space. -/
@[sga "3 V 4.1" "special case"]
theorem isAffineSpace_actionQuotient_of_isAffine
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsAffineSpace B S hS (actionQuotient G B hS V a) := by
  have hcon := contains_actionRelationScheme_of_actsFreely G B S hS V a ha
  have _ := isEtaleEquivalenceRelation_relation_of_actsFreely G B S hS V a ha
  set s := siteActionRelationSource G B hS V hcon
  set t := siteActionRelationTarget G B hS V hcon a
  have hflfs : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map s).left :=
    isFiniteLocallyFree_actionRelationSource (underlyingOver B hS V) G
  have hflft : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map t).left :=
    isFiniteLocallyFree_actionRelationTarget (underlyingOver B hS V) G a
  have _ : IsAffine ((Over.post B.inclusion).obj V).left := hV
  have _ : _root_.AlgebraicGeometry.IsFinite ((Over.post B.inclusion).map s).left :=
    Stacks.Morphisms.IsFiniteLocallyFree.isFinite _
  have _ : IsAffine
      ((Over.post B.inclusion).obj (siteActionRelationScheme G B hS V hcon)).left :=
    isAffine_of_isAffineHom ((Over.post B.inclusion).map s).left
  have _ : IsEquivalenceRelation ((Over.post B.inclusion).map t)
      ((Over.post B.inclusion).map s) :=
    isEquivalenceRelation_of_isPullback B S hS
      (freeActionQuotientMap G B S hS V a ha) t s
      (isPullback_freeActionQuotientMap G B S hS V a ha)
  obtain ⟨A, _, g, π, hsize, hflf, hsurjπ, hpb⟩ :=
    exists_quotient_of_isFiniteLocallyFree_relation S
      ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)
  have hA : B.Contains (Spec (CommRingCat.of A)) := lt_of_le_of_lt hsize V.left.2
  obtain ⟨m, e, hmπ, he⟩ :=
    exists_iso_yoneda_of_isPullback B S hS
      (isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints G B hS V a ha)
      (freeActionQuotientMap G B S hS V a ha) t s
      (isPullback_freeActionQuotientMap G B S hS V a ha)
      (surjective_presheaf_freeActionQuotientMap G B S hS V a ha)
      (quotientMap_etale_unconditional B S hS s t)
      (U' := Over.mk (⟨g⟩ : B.obj hA ⟶ B.obj hS)) π
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left)
      hsurjπ hpb
  refine ⟨Over.mk (⟨g⟩ : B.obj hA ⟶ B.obj hS), ?_, ⟨e⟩⟩
  exact inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))

end FreeFiniteAction

end AlgebraicGeometry.Space

end
