module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeGluingOverBasis
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Union
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic

/-!
# The glued relative Proj and the scheme representing the functor of quadruples

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN). The relative
homogeneous spectrum `Proj_S(A)` glued from the projective spectra of the graded rings of sections
of `A` over the affine opens of `S`, and a scheme representing the functor `F` of quadruples, are
canonically isomorphic as schemes over `S`; and the morphism `r_{d, L, ψ}` attached to a quadruple
`(f : T → S, d, L, ψ)` is a morphism over `S`.

## Main definitions

* `situationAlgebra`: Situation 01NN's graded algebra read as a sheaf of `ℤ`-graded algebras in the
  sense of Tag 0FQW.
* `affineProjGluingData`: the gluing datum over the basis of affine opens of `S` whose piece over
  `U` is `Proj Γ(U, A)`.
* `canonicalIso`: the canonical isomorphism over `S` between `Proj_S(A)` and a scheme carrying the
  same charts.
* `representableByEquiv`: for an arbitrary functor on `Sch^{opp}`, being represented by `Proj_S(A)`
  is equivalent to being represented by any scheme carrying the same charts.
* `RepresentingProjData`: a scheme over `S` with projective-spectrum charts on the affine opens of
  `S` which represents the functor `F`.
* `RepresentingProjData.relativeProjRepresentableBy`: the representation of `F` by `Proj_S(A)`
  transported along the canonical isomorphism.
* `RepresentingProjData.associatedMorphism`: the morphism `r_{d, L, ψ} : T → Proj_S(A)` attached to
  a quadruple.

## Main results

* `existsUnique_isoOver`: between `Proj_S(A)` and any scheme over `S` carrying projective-spectrum
  charts on the affine opens of `S` there is exactly one isomorphism compatible with the charts,
  and it is an isomorphism over `S`.
* `RepresentingProjData.existsUnique_isoOver_representing`: the same for a scheme representing `F`
  (Tag 01NZ).
* `RepresentingProjData.associatedMorphism_comp_toBase`: the morphism attached to a quadruple is a
  morphism over `S` (Tag 01O1).
* `RepresentingProjData.eq_associatedMorphism` and
  `RepresentingProjData.associatedMorphism_eq_of_equivalent`: that morphism is the only one
  representing the point of `F(T)` the quadruple defines, and it depends only on that point.

## Implementation notes

`situationAlgebra` keeps, of Situation 01NN's
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, the structure of a sheaf of
graded algebras in the sense of Tag 0FQW, and forgets commutativity, vanishing in negative degrees
and quasi-coherence of the homogeneous pieces. Its multiplication and unit are those of `A`
reindexed from the opens of `S` to the objects of the opposite category.

The gluing datum indexes the affine opens of `S` by the subtype `S.affineOpens` rather than by
`AlgebraicGeometry.Scheme.AffineZariskiSite`, because Tag 01LH is stated for a basis of the
topology presented as a set of opens, and the affine opens are such a basis by
`AlgebraicGeometry.Scheme.isBasis_affineOpens`. Its cocycle condition is Tag 01NP, in the form
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.projInclusionMap_comp`.

`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.chart_isPullback` puts the chart first and
its structure morphism second, while Tag 01LH's gluing datum wants them the other way round; the
two squares are transposes of one another, and `CategoryTheory.IsPullback.flip` exchanges them.

## References

* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue

universe u w

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### Situation 01NN as a sheaf of graded algebras -/

/-- Situation 01NN's quasi-coherent graded `𝒪_S`-algebra, read as a sheaf of `ℤ`-graded
`𝒪_S`-algebras in the sense of Tag 0FQW: the same homogeneous pieces, the same multiplication of
homogeneous local sections and the same degree-zero unit, with commutativity, vanishing in
negative degrees and quasi-coherence forgotten. -/
def situationAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace) where
  piece := A.piece
  mul i j :=
    { app := fun U => (A.mul i j).app U.unop
      map_smul_left := fun U r x y => (A.mul i j).map_smul_left U.unop r x y
      map_smul_right := fun U r x y => (A.mul i j).map_smul_right U.unop r x y
      naturality := fun {_U _V} f x y => (A.mul i j).naturality (leOfHom f.unop) x y }
  one := PresheafOfModules.sectionsMk (fun U => A.one U.unop)
    (fun {_U _V} f => A.one_res (leOfHom f.unop))
  mul_assoc i j k U a b c := A.mul_assoc i j k U.unop a b c
  one_mul i U a := A.one_mul i U.unop a
  mul_one i U a := A.mul_one i U.unop a

/-! ### The gluing problem over the affine opens of the base -/

/-- The gluing datum over the basis of affine opens of `S` whose piece over an affine open `U` is
the projective spectrum `Proj Γ(U, A)` of the graded ring of homogeneous sections of `A` over `U`,
with the morphisms induced by restriction of homogeneous sections as its restriction
morphisms. -/
def affineProjGluingData : Scheme.BasisGluingData S S.affineOpens where
  obj U := AlgebraicGeometry.Proj (A.grading U.1)
  proj U := projInclusionToOpen A U.1 U.2
  res := fun {V U} h => projInclusionMap A V.1 U.1 h V.2 U.2
  isPullback_res := fun {V U} h => projInclusion_isPullback A V.1 U.1 h V.2 U.2
  res_trans := fun {W V U} hWV hVU =>
    (projInclusionMap_comp A W.1 V.1 U.1 hWV hVU W.2 V.2 U.2).symm

/-- A scheme over `S` carrying projective-spectrum charts on the affine opens of `S`, read as a
solution of the gluing problem of `affineProjGluingData`. -/
def gluingOfProjData (P : RelativeProjData A) : (affineProjGluingData A).Gluing where
  base := P.scheme
  toBase := P.toBase
  chart U := P.chart U.1 U.2
  isPullback_chart U := (P.chart_isPullback U.1 U.2).flip
  res_comp_chart := fun {V U} h => P.chart_transition V.1 U.1 h V.2 U.2

/-- The canonical isomorphism over `S` between the relative homogeneous spectrum glued from the
projective spectra of the graded rings of sections of `A` and any scheme over `S` carrying the same
projective-spectrum charts on the affine opens of `S`. -/
def canonicalIso (P : RelativeProjData A) : (relativeProj A).scheme ≅ P.scheme :=
  (gluingOfProjData A (relativeProj A)).isoOfGluing S.isBasis_affineOpens (gluingOfProjData A P)

/-- The canonical isomorphism `canonicalIso A P` carries each chart of the relative homogeneous
spectrum of `A` to the corresponding chart of `P`. -/
@[simp]
theorem chart_comp_canonicalIso_hom (P : RelativeProjData A) (U : S.affineOpens) :
    (relativeProj A).chart U.1 U.2 ≫ (canonicalIso A P).hom = P.chart U.1 U.2 :=
  (gluingOfProjData A (relativeProj A)).chart_comp_desc S.isBasis_affineOpens
    (gluingOfProjData A P) U

/-- The canonical isomorphism `canonicalIso A P` is an isomorphism over `S`. -/
@[simp]
theorem canonicalIso_hom_comp_toBase (P : RelativeProjData A) :
    (canonicalIso A P).hom ≫ P.toBase = (relativeProj A).toBase :=
  (gluingOfProjData A (relativeProj A)).desc_comp_toBase S.isBasis_affineOpens
    (gluingOfProjData A P)

/-- Between the relative homogeneous spectrum of `A` and any scheme over `S` carrying
projective-spectrum charts on the affine opens of `S` there is exactly one isomorphism compatible
with the charts, and it is an isomorphism over `S`. -/
theorem existsUnique_isoOver (P : RelativeProjData A) :
    ∃! e : (relativeProj A).scheme ≅ P.scheme,
      (∀ U : S.affineOpens, (relativeProj A).chart U.1 U.2 ≫ e.hom = P.chart U.1 U.2) ∧
        e.hom ≫ P.toBase = (relativeProj A).toBase :=
  (gluingOfProjData A (relativeProj A)).existsUnique_isoOfGluing S.isBasis_affineOpens
    (gluingOfProjData A P)

/-! ### Transport of a representation along the canonical isomorphism -/

/-- Let `P` be a scheme over `S` carrying projective-spectrum charts on the affine opens of `S`.
For any functor `G : Sch^{opp} ⥤ Type w`, the representations of `G` by `P.scheme` and the
representations of `G` by the relative homogeneous spectrum `Proj_S(A)` correspond bijectively, by
transport along `canonicalIso`. -/
def representableByEquiv (P : RelativeProjData A) (G : Scheme.{u}ᵒᵖ ⥤ Type w) :
    G.RepresentableBy P.scheme ≃ G.RepresentableBy (relativeProj A).scheme :=
  Functor.RepresentableBy.equivOfIsoObj (canonicalIso A P)

/-! ### A scheme representing the functor of quadruples -/

/-- A scheme over `S` which represents the functor `F` of the display 01NX and which carries
projective-spectrum charts on the affine opens of `S`. -/
structure RepresentingProjData where
  /-- The functor `F` of the display 01NX. -/
  functor : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)
  /-- It is a sheaf for the Zariski topology. -/
  isSheaf : Presheaf.IsSheaf Scheme.zariskiTopology.{u} functor
  /-- The quadruples of positive degree over a test scheme, modulo strict equivalence inside a
  degree and equivalence across degrees, give points of `F` on that scheme. -/
  incl (T : Scheme.{u}) : F (situationAlgebra A) T → functor.obj (op T)
  /-- Over an affine test scheme that assignment is bijective: there `F(T)` is exactly the union of
  the sets `F_d(T)`. -/
  bijective_incl (T : Scheme.{u}) [IsAffine T] : Function.Bijective (incl T)
  /-- The scheme over `S` with its projective-spectrum charts. -/
  data : RelativeProjData A
  /-- It represents the functor. -/
  representableBy : functor.RepresentableBy data.scheme
  /-- The representation is a representation over `S`: the morphism attached to a quadruple,
  followed by the structure morphism, is the morphism to `S` that the quadruple records. -/
  homEquiv_symm_incl_comp_toBase (T : Scheme.{u}) (ξ : F (situationAlgebra A) T) :
    representableBy.homEquiv.symm (incl T ξ) ≫ data.toBase = ξ.1

namespace RepresentingProjData

variable {A} (R : RepresentingProjData A)

/-- The relative homogeneous spectrum `Proj_S(A)` glued from the projective spectra of the graded
rings of sections of `A`, and a scheme representing the functor `F` of quadruples, are canonically
isomorphic as schemes over `S`: there is exactly one isomorphism between them compatible with the
projective-spectrum charts, and it is an isomorphism over `S`. -/
theorem existsUnique_isoOver_representing :
    ∃! e : (relativeProj A).scheme ≅ R.data.scheme,
      (∀ U : S.affineOpens, (relativeProj A).chart U.1 U.2 ≫ e.hom = R.data.chart U.1 U.2) ∧
        e.hom ≫ R.data.toBase = (relativeProj A).toBase :=
  existsUnique_isoOver A R.data

/-- The relative homogeneous spectrum `Proj_S(A)` represents the functor `F`: the representation
`R.representableBy` transported along `canonicalIso`. -/
def relativeProjRepresentableBy : R.functor.RepresentableBy (relativeProj A).scheme :=
  representableByEquiv A R.data R.functor R.representableBy

/-- Under `relativeProjRepresentableBy`, the morphism representing a point of `F(T)` is the one
under `R.representableBy` followed by the inverse of `canonicalIso`. -/
@[simp]
theorem relativeProjRepresentableBy_homEquiv_symm {T : Scheme.{u}} (ξ : R.functor.obj (op T)) :
    R.relativeProjRepresentableBy.homEquiv.symm ξ =
      R.representableBy.homEquiv.symm ξ ≫ (canonicalIso A R.data).inv :=
  rfl

/-! ### The morphism attached to a quadruple -/

variable {T : Scheme.{u}} {f : T ⟶ S} {d : ℤ}

/-- The morphism `r_{d, L, ψ} : T → Proj_S(A)` attached to a quadruple `(f : T → S, d, L, ψ)` of
positive degree: the morphism representing the point of `F(T)` that the quadruple defines, read
through `relativeProjRepresentableBy`. -/
def associatedMorphism (hd : 0 < d) (Q : Quadruple f (situationAlgebra A) d) :
    T ⟶ (relativeProj A).scheme :=
  R.relativeProjRepresentableBy.homEquiv.symm (R.incl T (F.mk f hd Q))

/-- The morphism `r_{d, L, ψ}` attached to a quadruple `(f : T → S, d, L, ψ)` is a morphism over
`S`: composed with the structure morphism of the relative homogeneous spectrum it is `f`. -/
theorem associatedMorphism_comp_toBase (hd : 0 < d) (Q : Quadruple f (situationAlgebra A) d) :
    R.associatedMorphism hd Q ≫ (relativeProj A).toBase = f := by
  rw [associatedMorphism, relativeProjRepresentableBy_homEquiv_symm, Category.assoc,
    (canonicalIso A R.data).inv_comp_eq.mpr (canonicalIso_hom_comp_toBase A R.data).symm]
  exact R.homEquiv_symm_incl_comp_toBase T (F.mk f hd Q)

/-- The morphism attached to a quadruple is the *only* morphism representing the point of `F(T)`
that the quadruple defines. -/
theorem eq_associatedMorphism (hd : 0 < d) (Q : Quadruple f (situationAlgebra A) d)
    {g : T ⟶ (relativeProj A).scheme}
    (hg : R.relativeProjRepresentableBy.homEquiv g = R.incl T (F.mk f hd Q)) :
    g = R.associatedMorphism hd Q := by
  rw [associatedMorphism, ← hg, Equiv.symm_apply_apply]

/-- Equivalent quadruples, of possibly different degrees, have the same associated morphism: the
morphism depends only on the point of `F(T)`, as the identification of Tag 01NW demands. -/
theorem associatedMorphism_eq_of_equivalent {d' : ℤ} (hd : 0 < d) (hd' : 0 < d')
    {Q : Quadruple f (situationAlgebra A) d} {Q' : Quadruple f (situationAlgebra A) d'}
    (h : Quadruple.Equivalent Q Q') :
    R.associatedMorphism hd Q = R.associatedMorphism hd' Q' := by
  rw [associatedMorphism, associatedMorphism, F.mk_eq_mk_of_equivalent hd hd' h]

end RepresentingProjData

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
