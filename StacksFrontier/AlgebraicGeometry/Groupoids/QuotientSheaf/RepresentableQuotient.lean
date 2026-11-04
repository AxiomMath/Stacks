module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf

/-!
# Representable quotients

A pre-relation `j : R ⟶ U ×_S U` of schemes over `S` has a *representable quotient* when its
quotient sheaf `U/R` is represented by an object of the site, and a groupoid scheme
`(U, R, s, t, c)` has a representable quotient when the pre-relation `(t, s)` does. The site is
given by a functor `F : C ⥤ Over S` into `S`-schemes, and representability is
`CategoryTheory.Functor.IsRepresentable` for the presheaf underlying the quotient sheaf.

## Main definitions

* `Stacks.Groupoids.PreRelation.HasRepresentableQuotient`: representability of the quotient
  sheaf of a pre-relation.
* `Stacks.Groupoids.GroupoidScheme.HasRepresentableQuotient`: the same condition for the
  pre-relation `(t, s)` of a groupoid scheme.

## Main results

* `Stacks.Groupoids.PreRelation.hasRepresentableQuotient_congr`: the condition only depends on
  the quotient sheaf up to isomorphism.

## References

* [Stacks Project, Tag 03BD](https://stacks.math.columbia.edu/tag/03BD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- A pre-relation has a *representable quotient* when its quotient sheaf `U/R` is represented by
an object of the site. -/
@[stacks 03BD "pre-relation: representable quotient", sga "3 IV 3.3.2" "(ii)"]
noncomputable abbrev PreRelation.HasRepresentableQuotient (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) {R U : Over S}
    (j : PreRelation R U) : Prop :=
  (quotientSheaf J F j).obj.IsRepresentable

/-- A groupoid scheme has a *representable quotient* when the quotient sheaf `U/R` of its
pre-relation `(t, s)` is represented by an object of the site. -/
@[stacks 03BD "groupoid scheme: representable quotient", sga "3 IV 3.3.2" "(ii)"]
noncomputable abbrev GroupoidScheme.HasRepresentableQuotient (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S) : Prop :=
  (AlgebraicGeometry.groupoidPreRelation G).HasRepresentableQuotient J F

/-- Two pre-relations with isomorphic quotient sheaves have representable quotients
together. -/
theorem PreRelation.hasRepresentableQuotient_congr (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) {R U R' U' : Over S}
    (j : PreRelation R U) (j' : PreRelation R' U')
    (e : quotientSheaf J F j ≅ quotientSheaf J F j') :
    j.HasRepresentableQuotient J F ↔ j'.HasRepresentableQuotient J F := by
  have i : (quotientSheaf J F j).obj ≅ (quotientSheaf J F j').obj :=
    (sheafToPresheaf J (Type u)).mapIso e
  exact ⟨fun _ => isRepresentable_of_natIso _ i, fun _ => isRepresentable_of_natIso _ i.symm⟩

end Stacks.Groupoids

end
