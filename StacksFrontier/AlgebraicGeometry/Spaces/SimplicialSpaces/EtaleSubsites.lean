module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import StacksCore.Tactic.StacksAttribute

/-!
# The affine and scheme subsites of the small étale site of a simplicial algebraic space

Let `a : U → X` be an augmented simplicial algebraic space and `U_{spaces, étale}` the site of
Lemma 09WC of the simplicial object in sites `n ↦ U_{n, spaces, étale}` (Section 0DE7). Its full
subcategories `U_{affine, étale} ⊂ U_étale ⊂ U_{spaces, étale}` of the objects whose underlying
algebraic space is an affine scheme, respectively a scheme, with the topologies induced from
`U_{spaces, étale}`, have the same topos: every object of `U_{spaces, étale}`, an algebraic space
étale over some `U_n`, is covered by affine étale charts through each of its points.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleSchemeObject` and `AlgebraicGeometry.Space.IsEtaleAffineObject`:
  the objects whose underlying algebraic space is a scheme, respectively an affine scheme.
* `AlgebraicGeometry.Space.etaleSchemeTopology` and `AlgebraicGeometry.Space.etaleAffineTopology`:
  the induced topologies on `U_étale` and `U_{affine, étale}`.
* `AlgebraicGeometry.Space.etaleSchemeSheafEquiv`,
  `AlgebraicGeometry.Space.etaleAffineSheafEquiv` and
  `AlgebraicGeometry.Space.etaleAffineSchemeSheafEquiv`: the equivalences of topoi
  `Sh(U_{affine, étale}) = Sh(U_étale) = Sh(U_{spaces, étale})`.

## Main results

* `AlgebraicGeometry.Space.etaleAffineObject_isCoverDense` and
  `AlgebraicGeometry.Space.etaleSchemeObject_isCoverDense`: the two inclusions are cover dense.

## Implementation notes

The source endows `U_{affine, étale}` and `U_étale` with their natural topologies, those of
Lemma 09WC for the simplicial objects in sites `n ↦ U_{n, affine, étale}` and
`n ↦ U_{n, étale}`. Here they carry the topologies induced from `U_{spaces, étale}`; in each
degree the coverings are the families of étale morphisms jointly surjective on points, as in
Lemma 04JS and Definition 03ED, and the families of `U_{spaces, étale}` covering in a single
degree are such families.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

open EtaleComponent

/-- The algebraic space represented by an object of the big fppf site over `S`. -/
abbrev representedSpace (W : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩

/-- An object of `U_{spaces, étale}` belongs to `U_étale` when its underlying algebraic space is a
scheme. -/
def IsEtaleSchemeObject : ObjectProperty (Pseudofunctor.CoGrothendieck
    (etaleSimplicialSite A).totalPseudofunctor) :=
  fun x => ∃ W : BigFppfOver B S hS, Nonempty ((etaleTotalToSpaces A).obj x ≅ representedSpace W)

/-- An object of `U_{spaces, étale}` belongs to `U_{affine, étale}` when its underlying algebraic
space is an affine scheme. -/
def IsEtaleAffineObject : ObjectProperty (Pseudofunctor.CoGrothendieck
    (etaleSimplicialSite A).totalPseudofunctor) :=
  fun x => ∃ W : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
    Nonempty ((etaleTotalToSpaces A).obj x ≅ representedSpace W)

variable {A}

/-- An object of `U_{affine, étale}` is an object of `U_étale`. -/
theorem IsEtaleAffineObject.isEtaleSchemeObject {x} (hx : IsEtaleAffineObject A x) :
    IsEtaleSchemeObject A x :=
  let ⟨W, _, e⟩ := hx
  ⟨W, e⟩

/-- An affine étale chart of an object `V` étale over `U_n`, as an object étale over `U_n`. -/
def affineChartObj {n : SimplexCategory} (V : SpacesEtale B S hS (A.left.obj (op n)))
    (W : BigFppfOver B S hS)
    (b : yoneda.obj W ⟶ ((SpacesEtale.toSpaces B S hS _).obj V).obj)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    SpacesEtale B S hS (A.left.obj (op n)) :=
  ⟨Over.mk ((ObjectProperty.homMk b : representedSpace W ⟶ (SpacesEtale.toSpaces B S hS _).obj V) ≫
      ((SpacesEtale.inclusion B S hS _).obj V).hom),
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hb) V.property⟩

/-- The chart, as a morphism of the spaces-étale site of `U_n`. -/
def affineChartHom {n : SimplexCategory} (V : SpacesEtale B S hS (A.left.obj (op n)))
    (W : BigFppfOver B S hS)
    (b : yoneda.obj W ⟶ ((SpacesEtale.toSpaces B S hS _).obj V).obj)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    affineChartObj (A := A) V W b hb ⟶ V :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk b) rfl)

/-- **Every object of `U_{spaces, étale}` is covered by affine objects.** The sieve of the arrows
from objects whose underlying algebraic space is an affine scheme covers: through every point of
the realization of an object in degree `n` passes an affine étale chart of it (Stacks 03FX). -/
theorem etaleAffineObject_isCoverDense :
    (IsEtaleAffineObject A).ι.IsCoverDense (etaleSimplicialSite A).totalTopology where
  is_cover x := by
    obtain ⟨⟨n⟩, y⟩ := x
    change EtaleComponent A n at y
    -- the arrows of degree `n` from affine objects
    let R : Presieve (y : EtaleComponent A n) := fun Z _ =>
      IsEtaleAffineObject A ((Pseudofunctor.CoGrothendieck.ι
        (etaleSimplicialSite A).totalPseudofunctor (op n)).obj Z)
    have hR : R ∈ precoverage (A := A) n y := by
      refine (SpacesEtale.map_mem_precoverage_iff B S hS (realizeFunctor (A := A) n) R).2
        fun q => ?_
      obtain ⟨W, b, hW, hb, w, hw⟩ := exists_affine_etale_chart_at_point B S hS _
        ((realize y).obj.left.property) q
      let V := affineChartObj (A := A) (realize y) W b hb
      let e := realizeOfSpacesEtaleIso (A := A) V
      refine ⟨ofSpacesEtale V, (realizeFullyFaithful n).preimage
        (e.hom ≫ affineChartHom (realize y) W b hb), ?_,
        pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS _).map e.inv).hom
          (show points B S hS ((SpacesEtale.toSpaces B S hS _).obj V).obj from w), ?_⟩
      · exact ⟨W, hW, ⟨(SpacesEtale.toSpaces B S hS _).mapIso e⟩⟩
      · rw [Functor.comp_map, Functor.FullyFaithful.map_preimage, ← pointsMap_comp_apply,
          ← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp, Iso.inv_hom_id_assoc]
        exact hw
    refine GrothendieckTopology.superset_covering _ ?_
      (Precoverage.generate_mem_toGrothendieck (R := R.map
        (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)))
        ⟨R, hR, rfl⟩)
    rintro Z f ⟨T, g, k, ⟨hZ'⟩, rfl⟩
    exact ⟨⟨⟨_, hZ'⟩, g, _, rfl⟩⟩

/-- Every object of `U_{spaces, étale}` is covered by objects of `U_étale`, the affine ones
already covering it. -/
theorem etaleSchemeObject_isCoverDense :
    (IsEtaleSchemeObject A).ι.IsCoverDense (etaleSimplicialSite A).totalTopology where
  is_cover x := by
    refine GrothendieckTopology.superset_covering _ ?_
      ((etaleAffineObject_isCoverDense (A := A)).is_cover x)
    rintro Z f ⟨⟨⟨Y, hY⟩, l, m, hlm⟩⟩
    exact ⟨⟨⟨Y, hY.isEtaleSchemeObject⟩, l, m, hlm⟩⟩

/-- The inclusion of `U_{affine, étale}` into `U_{spaces, étale}` is cover dense. -/
instance : (IsEtaleAffineObject A).ι.IsCoverDense (etaleSimplicialSite A).totalTopology :=
  etaleAffineObject_isCoverDense

/-- The inclusion of `U_étale` into `U_{spaces, étale}` is cover dense. -/
instance : (IsEtaleSchemeObject A).ι.IsCoverDense (etaleSimplicialSite A).totalTopology :=
  etaleSchemeObject_isCoverDense

variable (A)

/-- **The small étale site `U_étale`.** The objects of `U_{spaces, étale}` whose underlying
algebraic space is a scheme, with the topology induced from `U_{spaces, étale}`. -/
abbrev etaleSchemeTopology : GrothendieckTopology (IsEtaleSchemeObject A).FullSubcategory :=
  (IsEtaleSchemeObject A).ι.inducedTopology (etaleSimplicialSite A).totalTopology

/-- **The site `U_{affine, étale}`.** The objects of `U_{spaces, étale}` whose underlying
algebraic space is an affine scheme, with the topology induced from `U_{spaces, étale}`. -/
abbrev etaleAffineTopology : GrothendieckTopology (IsEtaleAffineObject A).FullSubcategory :=
  (IsEtaleAffineObject A).ι.inducedTopology (etaleSimplicialSite A).totalTopology

/-- **`Sh(U_étale) = Sh(U_{spaces, étale})`.** Restriction along the inclusion is an equivalence
of topoi. -/
def etaleSchemeSheafEquiv :
    Sheaf (etaleSchemeTopology A) (Type (u + 1)) ≌
      Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)) :=
  Functor.IsDenseSubsite.sheafEquiv (etaleSchemeTopology A) (etaleSimplicialSite A).totalTopology
    (IsEtaleSchemeObject A).ι (Type (u + 1))

/-- **`Sh(U_{affine, étale}) = Sh(U_{spaces, étale})`.** Restriction along the inclusion is an
equivalence of topoi. -/
def etaleAffineSheafEquiv :
    Sheaf (etaleAffineTopology A) (Type (u + 1)) ≌
      Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)) :=
  Functor.IsDenseSubsite.sheafEquiv (etaleAffineTopology A) (etaleSimplicialSite A).totalTopology
    (IsEtaleAffineObject A).ι (Type (u + 1))

/-- **`Sh(U_{affine, étale}) = Sh(U_étale)`.** The two equivalences with
`Sh(U_{spaces, étale})`, composed. -/
def etaleAffineSchemeSheafEquiv :
    Sheaf (etaleAffineTopology A) (Type (u + 1)) ≌ Sheaf (etaleSchemeTopology A) (Type (u + 1)) :=
  (etaleAffineSheafEquiv A).trans (etaleSchemeSheafEquiv A).symm

end AlgebraicGeometry.Space

end
