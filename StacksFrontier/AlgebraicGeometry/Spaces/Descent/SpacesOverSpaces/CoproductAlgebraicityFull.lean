module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductAlgebraicityEquivalence

/-!
# Descent data for a family and for the coproduct of its members

Let `{X i → T}` be a family of morphisms of algebraic spaces over `S` with fixed target, and
let `Y = ∐ X i` be the coproduct of the sources, taken in sheaves on the big fppf site. This
file proves Stacks 0ADK: the category of descent data relative to the family is canonically
equivalent to the category of descent data relative to `Y → T`, by the functor sending
`(V i, φ i j)` to `(∐ V i, ∐ φ i j)`.

## Main definitions

* `AlgebraicGeometry.Space.Descent.fullTotalCoproduct` is the chosen algebraic sheaf coproduct
  of the objects of a descent datum.
* `AlgebraicGeometry.Space.Descent.FullFamilyCoproductEquivalence` is an equivalence between
  the category of descent data for the family and the category of descent data relative to an
  algebraic sheaf coproduct `Y → T` of the sources, together with its action on objects,
  gluing isomorphisms and morphisms.

## Main results

* `AlgebraicGeometry.Space.Descent.fullFamilyCoproductEquivalenceData`: such an equivalence
  exists for every algebraic sheaf coproduct `Y` of the sources.
* `AlgebraicGeometry.Space.Descent.familyCoproductEquivalenceOfAdmitsCoproductIndex`:
  Stacks 0ADK, the canonical equivalence for `Y` the coproduct of the sources in sheaves.

## Size of the index type

The index type is `u`-small and admissible for the site in the sense of
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`: of cardinality below the cofinality of the
size cutoff. This is the size bound under which a coproduct of algebraic spaces over `S` is
again one (Stacks 02WQ asks that the members and the index set be "not too large"), and it
holds for every countable index type, by
`AlgebraicGeometry.BigFppfSite.admitsCoproductIndex_of_countable`, these being the coproducts
Stacks 000R(2) guarantees in the underlying category of a big site. Some bound is necessary:
`AlgebraicGeometry.exists_family_lt_cutoff_not_nonempty_algebraicSheafCoproduct` exhibits a
big fppf site and a family of schemes over `Spec ℤ`, indexed by a type of cardinality the
cofinality of the cutoff, whose coproduct in sheaves is not an algebraic space, so that the
category of descent data relative to `Y → T` cannot be formed.

## References

* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
* [Stacks Project, Tag 0ADG](https://stacks.math.columbia.edu/tag/0ADG)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I]
  {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (f : ∀ i, X i ⟶ T) (hT : IsAlgebraicSpace B S hS T)
  (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-- A chosen algebraic sheaf coproduct of the objects of an arbitrary descent datum. -/
public def fullTotalCoproduct (D : DescentData f hT hX) :
    AlgebraicSheafCoproduct (fun i => (D.obj i).left) D.obj_isAlgebraicSpace :=
  totalCoproduct f hT hX (algebraicCoproductDescentData f hT hX D)

/-- An equivalence from the category of descent data for the family `{X i → T}` to the category
of descent data relative to an algebraic sheaf coproduct `Y → T` of the sources, specified by
its action on objects, gluing isomorphisms and morphisms: a descent datum `(V i, φ i j)` goes to
`(∐ V i, φ)` with `φ` restricting to `φ i j` on each pair of summands, and a morphism `(ψ i)`
goes to `∐ ψ i`.

The fields are those of `AlgebraicGeometry.Space.Descent.FamilyCoproductEquivalence`, with
source category the whole of `AlgebraicGeometry.Space.Descent.DescentData`. -/
public structure FullFamilyCoproductEquivalence (Y : AlgebraicSheafCoproduct X hX) where
  /-- The equivalence of categories, on the whole category of descent data. -/
  equivalence :
    DescentData f hT hX ≌
      DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
        hT (fun _ => Y.isAlgebraicSpace)
  /-- The object of the corresponding singleton descent datum is the sheaf coproduct. -/
  objIso (D : DescentData f hT hX) :
    (equivalence.functor.obj D).obj PUnit.unit ≅
      Over.mk ((fullTotalCoproduct f hT hX D).map Y (fun i => (D.obj i).hom))
  /-- Inclusion of a pairwise source fibre product into the coproduct fibre product. -/
  sourceMap (D : DescentData f hT hX) (i j : I) :
    pullback ((D.obj i).hom ≫ f i) (f j) ⟶
      pullback
        (((equivalence.functor.obj D).obj PUnit.unit).hom ≫ Y.desc (spaceSheaf T hT) f)
        (Y.desc (spaceSheaf T hT) f)
  /-- The first source projection is the inclusion of the object summand. -/
  sourceMap_fst (D : DescentData f hT hX) (i j : I) :
    sourceMap D i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ ((fullTotalCoproduct f hT hX D).ι i).hom ≫ (objIso D).inv.left
  /-- The second source projection is the inclusion of the base summand. -/
  sourceMap_snd (D : DescentData f hT hX) (i j : I) :
    sourceMap D i j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (Y.ι j).hom
  /-- The pairwise source fibre products cover the coproduct source fibre product: two maps to
  a sheaf agreeing on every summand are equal. -/
  sourceMap_jointly_epi (D : DescentData f hT hX)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    {g h : pullback
        (((equivalence.functor.obj D).obj PUnit.unit).hom ≫ Y.desc (spaceSheaf T hT) f)
        (Y.desc (spaceSheaf T hT) f) ⟶ W}
    (hgh : ∀ i j, sourceMap D i j ≫ g = sourceMap D i j ≫ h) : g = h
  /-- Inclusion of a pairwise target fibre product into the coproduct fibre product. -/
  targetMap (D : DescentData f hT hX) (i j : I) :
    pullback (f i) ((D.obj j).hom ≫ f j) ⟶
      pullback
        (Y.desc (spaceSheaf T hT) f)
        (((equivalence.functor.obj D).obj PUnit.unit).hom ≫ Y.desc (spaceSheaf T hT) f)
  /-- The first target projection is the inclusion of the base summand. -/
  targetMap_fst (D : DescentData f hT hX) (i j : I) :
    targetMap D i j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (Y.ι i).hom
  /-- The second target projection is the inclusion of the object summand. -/
  targetMap_snd (D : DescentData f hT hX) (i j : I) :
    targetMap D i j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ ((fullTotalCoproduct f hT hX D).ι j).hom ≫ (objIso D).inv.left
  /-- The pairwise target fibre products cover the coproduct target fibre product. -/
  targetMap_jointly_epi (D : DescentData f hT hX)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    {g h : pullback (Y.desc (spaceSheaf T hT) f)
        (((equivalence.functor.obj D).obj PUnit.unit).hom ≫ Y.desc (spaceSheaf T hT) f) ⟶ W}
    (hgh : ∀ i j, targetMap D i j ≫ g = targetMap D i j ≫ h) : g = h
  /-- The singleton gluing isomorphism restricts to the original one on each pair. -/
  gluing (D : DescentData f hT hX) (i j : I) :
    sourceMap D i j ≫
        (gluingPullbackIso _ _ _ (equivalence.functor.obj D) PUnit.unit PUnit.unit).hom =
      (gluingPullbackIso f hT hX D i j).hom ≫ targetMap D i j
  /-- Maps of descent data are sent to sheaf coproducts of their component maps. -/
  map {D E : DescentData f hT hX} (α : D ⟶ E) :
    (objIso D).hom.left ≫
        (fullTotalCoproduct f hT hX D).map (fullTotalCoproduct f hT hX E)
          (fun i => (α.hom i).left) =
      ((equivalence.functor.map α).hom PUnit.unit).left ≫ (objIso E).hom.left

/-- Every algebraic sheaf coproduct `Y` of the sources carries the canonical equivalence from
the category of descent data for the family to the category of descent data relative to
`Y → T`, together with its action on objects, gluing isomorphisms and morphisms. -/
public def fullFamilyCoproductEquivalenceData (Y : AlgebraicSheafCoproduct X hX) :
    FullFamilyCoproductEquivalence.{u, v, w} f hT hX Y where
  equivalence := fullFamilyCoproductEquivalence.{u, v, w} f hT hX Y
  objIso D := (familyCoproductEquivalence.{u, v, w} f hT hX Y).objIso
    (algebraicCoproductDescentData f hT hX D)
  sourceMap D i j := (familyCoproductEquivalence.{u, v, w} f hT hX Y).sourceMap
    (algebraicCoproductDescentData f hT hX D) i j
  sourceMap_fst D i j := (familyCoproductEquivalence.{u, v, w} f hT hX Y).sourceMap_fst
    (algebraicCoproductDescentData f hT hX D) i j
  sourceMap_snd D i j := (familyCoproductEquivalence.{u, v, w} f hT hX Y).sourceMap_snd
    (algebraicCoproductDescentData f hT hX D) i j
  sourceMap_jointly_epi D :=
    (familyCoproductEquivalence.{u, v, w} f hT hX Y).sourceMap_jointly_epi
      (algebraicCoproductDescentData f hT hX D)
  targetMap D i j := (familyCoproductEquivalence.{u, v, w} f hT hX Y).targetMap
    (algebraicCoproductDescentData f hT hX D) i j
  targetMap_fst D i j := (familyCoproductEquivalence.{u, v, w} f hT hX Y).targetMap_fst
    (algebraicCoproductDescentData f hT hX D) i j
  targetMap_snd D i j := (familyCoproductEquivalence.{u, v, w} f hT hX Y).targetMap_snd
    (algebraicCoproductDescentData f hT hX D) i j
  targetMap_jointly_epi D :=
    (familyCoproductEquivalence.{u, v, w} f hT hX Y).targetMap_jointly_epi
      (algebraicCoproductDescentData f hT hX D)
  gluing D i j := (familyCoproductEquivalence.{u, v, w} f hT hX Y).gluing
    (algebraicCoproductDescentData f hT hX D) i j
  map α := (familyCoproductEquivalence.{u, v, w} f hT hX Y).map
    (algebraicCoproductDescentDataHom f hT hX α)

/-- Let `{f i : X i → T}` be a family of morphisms of algebraic spaces over `S` with fixed
target, and let `Y = ∐ X i` be the coproduct of the sources in sheaves on the big fppf site, an
algebraic space over `S` by `AlgebraicGeometry.Space.Descent.sigmaAlgebraicSheafCoproduct`. There
is a canonical equivalence from the category of descent data relative to the family to the
category of descent data relative to `Y → T`, which sends `(V i, φ i j)` to `(V, φ)` with
`V = ∐ V i` and `φ` restricting to `φ i j` on each pair of summands, and a morphism `(ψ i)` to
`∐ ψ i`.

The index type is `u`-small and of cardinality below the cofinality of the site's size cutoff,
as is every countable index type. -/
@[stacks 0ADK]
public def familyCoproductEquivalenceOfAdmitsCoproductIndex :
    FullFamilyCoproductEquivalence.{u, v, w} f hT hX (sigmaAlgebraicSheafCoproduct X hX) :=
  fullFamilyCoproductEquivalenceData.{u, v, w} f hT hX _

end AlgebraicGeometry.Space.Descent

end
