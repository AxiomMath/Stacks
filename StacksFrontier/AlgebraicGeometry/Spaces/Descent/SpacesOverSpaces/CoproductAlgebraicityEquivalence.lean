module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductAlgebraicity

/-!
# Descent data for a family as descent data for its coproduct, at the full category

`AlgebraicGeometry.Space.Descent.familyCoproductEquivalence` is the canonical equivalence of
Stacks 0ADK on `AlgebraicGeometry.Space.Descent.AlgebraicCoproductDescentData`, the full
subcategory of those descent data whose objects admit an algebraic sheaf coproduct. For an index
type admissible for the site,
`AlgebraicGeometry.Space.Descent.nonempty_algebraicSheafCoproduct_descentData` says that every
descent datum lies in it. So the full subcategory is the whole category, the inclusion is an
equivalence, and composing with it gives the equivalence on the whole category of descent data
for the family.

## Main results

* `CategoryTheory.ObjectProperty.fullSubcategoryEquivalenceOfForall`: the inclusion of the full
  subcategory on a property that holds everywhere is an equivalence.
* `AlgebraicGeometry.Space.Descent.algebraicCoproductDescentDataEquivalence`: hence
  `AlgebraicGeometry.Space.Descent.AlgebraicCoproductDescentData` is equivalent to
  `AlgebraicGeometry.Space.Descent.DescentData`.
* `AlgebraicGeometry.Space.Descent.fullFamilyCoproductEquivalence`: the equivalence from the
  category of descent data for the family to the category of descent data relative to an
  algebraic sheaf coproduct `Y → T` of the sources.
* `AlgebraicGeometry.Space.Descent.exists_fullFamilyCoproductEquivalence`: the same, for an
  algebraic sheaf coproduct of the sources that is produced rather than given.

## Implementation notes

The inverse of the subcategory equivalence is `CategoryTheory.ObjectProperty.lift` of the
identity, so it sends `D` to `⟨D, _⟩` definitionally and the comparison isomorphisms are
`CategoryTheory.Iso.refl`; the property being a `Prop`, no coherence is needed. Downstream, the
composite functor applied to `D` is then definitionally the functor of
`AlgebraicGeometry.Space.Descent.familyCoproductEquivalence` applied to `⟨D, _⟩`, so the action
of the equivalence on objects, on gluing isomorphisms and on morphisms is transported with no
coherence argument.

The equivalence is stated for a given algebraic sheaf coproduct `Y` of the sources, since the
category of descent data relative to `Y` cannot be named without one. The statement of
Stacks 0ADK, with `Y` the coproduct of the sources in sheaves and the full description of the
functor, is `AlgebraicGeometry.Space.Descent.familyCoproductEquivalenceOfAdmitsCoproductIndex`.

## References

* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

namespace CategoryTheory.ObjectProperty

/-- **The full subcategory on a property that holds of every object is the whole category.**

The inverse sends an object to itself with the given witness, so both comparison isomorphisms
are the identity: the property is a `Prop`, so the witness carried by an object of the full
subcategory is irrelevant to it. -/
public def fullSubcategoryEquivalenceOfForall {C : Type*} [Category C] (P : ObjectProperty C)
    (hP : ∀ X, P X) : P.FullSubcategory ≌ C where
  functor := P.ι
  inverse := ObjectProperty.lift P (𝟭 C) hP
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by cat_disch

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I]
  {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (f : ∀ i, X i ⟶ T) (hT : IsAlgebraicSpace B S hS T)
  (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-! ### The full subcategory of descent data is the whole category -/

/-- A descent datum, regarded as an object of the full subcategory of those whose objects admit
an algebraic sheaf coproduct. The witness is
`AlgebraicGeometry.Space.Descent.nonempty_algebraicSheafCoproduct_descentData`. -/
public def algebraicCoproductDescentData (D : DescentData f hT hX) :
    AlgebraicCoproductDescentData f hT hX :=
  ⟨D, nonempty_algebraicSheafCoproduct_descentData f hT hX D⟩

/-- A morphism of descent data, regarded as a morphism of the full subcategory of those whose
objects admit an algebraic sheaf coproduct. Morphisms of a full subcategory are those of the
ambient category, so this only inserts the wrapper. -/
public abbrev algebraicCoproductDescentDataHom {D E : DescentData f hT hX} (α : D ⟶ E) :
    algebraicCoproductDescentData f hT hX D ⟶ algebraicCoproductDescentData f hT hX E :=
  ObjectProperty.homMk α

/-- The components of a morphism of descent data are unchanged by regarding it as a morphism of
the full subcategory. -/
@[simp]
public lemma algebraicCoproductDescentDataHom_hom_hom {D E : DescentData f hT hX} (α : D ⟶ E)
    (i : I) : (algebraicCoproductDescentDataHom f hT hX α).hom.hom i = α.hom i :=
  rfl

/-- **The descent data whose objects admit an algebraic sheaf coproduct are all of them**, when
the index type of the family is admissible for the site.

The property cutting out `AlgebraicGeometry.Space.Descent.AlgebraicCoproductDescentData` holds
of every descent datum, by
`AlgebraicGeometry.Space.Descent.nonempty_algebraicSheafCoproduct_descentData`, so the inclusion
of the full subcategory is an equivalence. -/
public def algebraicCoproductDescentDataEquivalence :
    AlgebraicCoproductDescentData f hT hX ≌ DescentData f hT hX :=
  ObjectProperty.fullSubcategoryEquivalenceOfForall _
    (nonempty_algebraicSheafCoproduct_descentData f hT hX)

/-- The inverse of the subcategory equivalence is the tautological inclusion of a descent
datum. -/
@[simp]
public lemma algebraicCoproductDescentDataEquivalence_inverse_obj (D : DescentData f hT hX) :
    (algebraicCoproductDescentDataEquivalence f hT hX).inverse.obj D =
      algebraicCoproductDescentData f hT hX D :=
  rfl

/-- The functor of the subcategory equivalence forgets the witness. -/
@[simp]
public lemma algebraicCoproductDescentDataEquivalence_functor_obj
    (D : AlgebraicCoproductDescentData f hT hX) :
    (algebraicCoproductDescentDataEquivalence f hT hX).functor.obj D = D.obj :=
  rfl

/-! ### Stacks 0ADK at the full category of descent data -/

/-- The equivalence from the category of descent data for the family `{X i → T}` to the
category of descent data relative to an algebraic sheaf coproduct `Y → T` of the sources, for an
index type admissible for the site.

This is `AlgebraicGeometry.Space.Descent.familyCoproductEquivalence` composed with
`AlgebraicGeometry.Space.Descent.algebraicCoproductDescentDataEquivalence`. -/
public def fullFamilyCoproductEquivalence (Y : AlgebraicSheafCoproduct X hX) :
    DescentData f hT hX ≌
      DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
        hT (fun _ => Y.isAlgebraicSpace) :=
  (algebraicCoproductDescentDataEquivalence f hT hX).symm.trans
    (familyCoproductEquivalence.{u, v, w} f hT hX Y).equivalence

/-- The functor of the full equivalence is the functor of
`AlgebraicGeometry.Space.Descent.familyCoproductEquivalence` on the tautological inclusion of a
descent datum. This is a definitional unfolding, recorded so that the action of the equivalence
on objects, gluing isomorphisms and morphisms can be read off the corresponding fields. -/
public lemma fullFamilyCoproductEquivalence_functor_obj (Y : AlgebraicSheafCoproduct X hX)
    (D : DescentData f hT hX) :
    (fullFamilyCoproductEquivalence.{u, v, w} f hT hX Y).functor.obj D =
      (familyCoproductEquivalence.{u, v, w} f hT hX Y).equivalence.functor.obj
        (algebraicCoproductDescentData f hT hX D) :=
  rfl

/-- The functor of the full equivalence acts on morphisms as the functor of
`AlgebraicGeometry.Space.Descent.familyCoproductEquivalence` on the corresponding morphism of
the full subcategory. This too is a definitional unfolding. -/
public lemma fullFamilyCoproductEquivalence_functor_map (Y : AlgebraicSheafCoproduct X hX)
    {D E : DescentData f hT hX} (α : D ⟶ E) :
    (fullFamilyCoproductEquivalence.{u, v, w} f hT hX Y).functor.map α =
      (familyCoproductEquivalence.{u, v, w} f hT hX Y).equivalence.functor.map
        (algebraicCoproductDescentDataHom f hT hX α) :=
  rfl

/-- For a family of algebraic spaces over `S` whose index type is admissible for the site,
there is an algebraic sheaf coproduct `Y` of the sources, and the category of descent data for
the family is equivalent to the category of descent data relative to `Y → T`. The coproduct is
`AlgebraicGeometry.Space.Descent.sigmaAlgebraicSheafCoproduct`. -/
public theorem exists_fullFamilyCoproductEquivalence :
    ∃ Y : AlgebraicSheafCoproduct X hX,
      Nonempty (DescentData f hT hX ≌
        DescentData (fun _ : PUnit.{w + 1} => Y.desc (spaceSheaf T hT) f)
          hT (fun _ => Y.isAlgebraicSpace)) :=
  ⟨sigmaAlgebraicSheafCoproduct X hX,
    ⟨fullFamilyCoproductEquivalence.{u, v, w} f hT hX _⟩⟩

end AlgebraicGeometry.Space.Descent

end
