module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Presheaf
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The quotient sheaf of a pre-relation (Stacks 044J)

The *quotient sheaf* `U/R` of a pre-relation `j : R ⟶ U ×_Z U` is the fppf sheafification of the
quotient presheaf of Stacks 044I. This file constructs it, together with the canonical map from
`U`, its universal property, and the canonical map to the base.

## Main definitions

* `AlgebraicGeometry.Space.quotientSheaf`: the quotient sheaf `U/R`.
* `AlgebraicGeometry.Space.toQuotientSheaf`: the canonical map `U ⟶ U/R`.
* `AlgebraicGeometry.Space.quotientSheafDesc`: the map out of `U/R` determined by a map out of
  `U` that equalizes the relation.
* `AlgebraicGeometry.Space.baseSheaf` and `AlgebraicGeometry.Space.quotientSheafToBase`: the
  base read as a sheaf and the canonical map `U/R ⟶ Z`.

## Main results

* `AlgebraicGeometry.Space.target_toQuotientSheaf_eq_source`: the quotient projection
  equalizes the two maps of the relation.
* `AlgebraicGeometry.Space.toQuotientSheaf_quotientSheafDesc` and
  `AlgebraicGeometry.Space.quotientSheafDesc_unique`: the universal property — a map out of `U`
  constant on the relation factors uniquely through `U/R`.
* `AlgebraicGeometry.Space.toQuotientSheaf_quotientSheafToBase`: the map to the base extends
  the structure map of `U`.

## References

* [Stacks Project, Tag 044I](https://stacks.math.columbia.edu/tag/044I)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}

/-- The two maps of a pre-relation have the same composite to the base. -/
theorem target_toBase_eq_source (j : PreRelation R U) :
    j.target.left ≫ U.hom = j.source.left ≫ U.hom :=
  (Over.w j.target).trans (Over.w j.source).symm

variable [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

/-- The quotient sheaf `U/R` of a pre-relation: the fppf sheafification of its quotient
presheaf. -/
@[stacks 044J "quotient by a pre-relation"]
noncomputable abbrev quotientSheaf (j : PreRelation R U) :
    Sheaf (BigFppfOver.topology site S hS) (Type u) :=
  (presheafToSheaf (BigFppfOver.topology site S hS) (Type u)).obj (quotientPresheaf j)

/-- The canonical map from `U` to its quotient sheaf: the coequalizer projection followed by the
unit of sheafification. -/
noncomputable abbrev toQuotientSheaf (j : PreRelation R U) : U.left ⟶ (quotientSheaf j).obj :=
  coequalizer.π j.target.left j.source.left ≫
    toSheafify (BigFppfOver.topology site S hS) (quotientPresheaf j)

/-- The quotient projection identifies the target and the source of every arrow of the
relation. -/
@[stacks 044J "relation equalized by the quotient projection"]
theorem target_toQuotientSheaf_eq_source (j : PreRelation R U) :
    j.target.left ≫ toQuotientSheaf j = j.source.left ≫ toQuotientSheaf j :=
  congrArg (fun f => f ≫ toSheafify (BigFppfOver.topology site S hS) (quotientPresheaf j))
    (coequalizer.condition j.target.left j.source.left)

/-- A map from `U` to a sheaf which is constant on the relation descends to the quotient
sheaf. -/
noncomputable def quotientSheafDesc (j : PreRelation R U)
    (A : Sheaf (BigFppfOver.topology site S hS) (Type u)) (k : U.left ⟶ A.obj)
    (h : j.target.left ≫ k = j.source.left ≫ k) : quotientSheaf j ⟶ A :=
  ⟨sheafifyLift (BigFppfOver.topology site S hS) (coequalizer.desc k h) A.property⟩

/-- The descended map restricts to the original map on `U`. -/
@[stacks 044J "descent of maps from the quotient"]
theorem toQuotientSheaf_quotientSheafDesc (j : PreRelation R U)
    (A : Sheaf (BigFppfOver.topology site S hS) (Type u)) (k : U.left ⟶ A.obj)
    (h : j.target.left ≫ k = j.source.left ≫ k) :
    toQuotientSheaf j ≫ (quotientSheafDesc j A k h).hom = k := by
  change (coequalizer.π j.target.left j.source.left ≫
      toSheafify (BigFppfOver.topology site S hS) (quotientPresheaf j)) ≫
      sheafifyLift (BigFppfOver.topology site S hS) (coequalizer.desc k h) A.property = k
  unfold quotientPresheaf
  rw [Category.assoc, toSheafify_sheafifyLift, coequalizer.π_desc]

/-- A map out of the quotient sheaf is determined by its restriction to `U`. -/
@[stacks 044J "uniqueness of descent"]
theorem quotientSheafDesc_unique (j : PreRelation R U)
    (A : Sheaf (BigFppfOver.topology site S hS) (Type u)) (k : U.left ⟶ A.obj)
    (h : j.target.left ≫ k = j.source.left ≫ k) (d : quotientSheaf j ⟶ A)
    (hd : toQuotientSheaf j ≫ d.hom = k) : d = quotientSheafDesc j A k h := by
  apply Sheaf.hom_ext
  apply sheafifyLift_unique (BigFppfOver.topology site S hS)
    (coequalizer.desc k h) A.property d.hom
  apply (cancel_epi (coequalizer.π j.target.left j.source.left)).1
  rw [coequalizer.π_desc]
  exact hd

/-- The base, read as a sheaf. -/
abbrev baseSheaf (hZ : Presheaf.IsSheaf (BigFppfOver.topology site S hS) Z) :
    Sheaf (BigFppfOver.topology site S hS) (Type u) :=
  ⟨Z, hZ⟩

/-- The canonical map from the quotient sheaf to the base. -/
@[stacks 044J "canonical morphism to the base"]
noncomputable def quotientSheafToBase
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology site S hS) Z) (j : PreRelation R U) :
    quotientSheaf j ⟶ baseSheaf hZ :=
  quotientSheafDesc j (baseSheaf hZ) U.hom (target_toBase_eq_source j)

/-- The map from the quotient to the base extends the structure map of `U`. -/
@[stacks 044J "compatibility of the base morphism"]
theorem toQuotientSheaf_quotientSheafToBase
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology site S hS) Z) (j : PreRelation R U) :
    toQuotientSheaf j ≫ (quotientSheafToBase hZ j).hom = U.hom :=
  toQuotientSheaf_quotientSheafDesc j (baseSheaf hZ) U.hom (target_toBase_eq_source j)

end AlgebraicGeometry.Space

end
