module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSpace02WQ
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductEquivalence

/-!
# Algebraicity of the sheaf coproduct of an admissibly indexed family

`AlgebraicGeometry.Space.Descent.AlgebraicSheafCoproduct` bundles a coproduct of a family of
algebraic spaces in sheaves on the big fppf site together with a scheme atlas of the vertex.
Its three colimit fields are available for every `u`-small index type, by
`AlgebraicGeometry.Space.hasColimitsOfShape_discrete_sheaf`; the atlas field is the one that
is a genuine restriction, and the whole content of this file is to discharge it.

The condition under which it is dischargeable is the one this repository already names for
exactly this purpose, `AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`: the index type is
`u`-small and its canonical `u`-small copy has cardinality below `cof (B.cutoff.ord)`. Under
it, `AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit` makes the coproduct sheaf an
algebraic space, and its atlas clause is literally the missing field. Every countable index
type is admissible, by `AlgebraicGeometry.BigFppfSite.admitsCoproductIndex_of_countable`.

The hypothesis is on the index type and the site alone — never on the family. That is what
makes the descent-data corollary below uniform in the descent datum: the objects of a descent
datum are algebraic spaces whose atlases carry no common size bound, and a bound on their
supremum is exactly what the cofinality condition supplies.

## Main results

* `AlgebraicGeometry.Space.Descent.isAlgebraicSpace_sigma_spaceSheaf`: the vertex of the sheaf
  coproduct of an admissibly indexed family of algebraic spaces is an algebraic space.
* `AlgebraicGeometry.Space.Descent.sigmaAlgebraicSheafCoproduct`: that coproduct, packaged as
  an `AlgebraicGeometry.Space.Descent.AlgebraicSheafCoproduct`.
* `AlgebraicGeometry.Space.Descent.nonempty_algebraicSheafCoproduct`: hence every admissibly
  indexed family of algebraic spaces has an algebraic sheaf coproduct.
* `AlgebraicGeometry.Space.Descent.nonempty_algebraicSheafCoproduct_descentData`: the
  predicate cutting out `AlgebraicGeometry.Space.Descent.AlgebraicCoproductDescentData` inside
  `AlgebraicGeometry.Space.Descent.DescentData` holds of every descent datum.

## Implementation notes

The atlas is not constructed here. `AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit`
builds it from the coproduct of chosen atlases of the members, which lies in the site by
`AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof`; that is the set-theoretic content,
and it is reused rather than repeated. What is done here is the reindexing: the index type of
an `AlgebraicGeometry.Space.Descent.AlgebraicSheafCoproduct` lives in an arbitrary universe
`v`, whereas that theorem asks for one in the working universe `u`, so the colimit cofan is
transported along `Equiv.symm (equivShrink I)` by
`CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv`. This is the same device, and the same
bijection, that `AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le` uses.

Nothing here carries a `@[stacks 02WQ]` attribute: that tag is attached to
`AlgebraicGeometry.isAlgebraicSpace_coproduct`, and the statements below are that theorem
specialized to the coproduct taken in sheaves, not a second formalization of it.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Algebraicity of a coproduct taken in sheaves -/

section Sigma

variable {I : Type v} [Small.{u} I] [hadm : B.AdmitsCoproductIndex I]
  (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

include hadm in
/-- **The vertex of a coproduct of algebraic spaces taken in sheaves is an algebraic space**,
when the index type is admissible for the site.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit` — the coproduct of a family of
algebraic spaces indexed below the cofinality of the site's size cutoff — with the index type
transported to the working universe along `Equiv.symm (equivShrink I)`, the cofinality bound
being read off `AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex` on that copy. -/
public theorem isAlgebraicSpace_of_isColimit_cofan_spaceSheaf
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, spaceSheaf (X i) (hX i) ⟶ G) (hG : IsColimit (Cofan.mk G ι)) :
    IsAlgebraicSpace B S hS G.obj :=
  AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit B S hS
    hadm.mk_shrink_lt_cutoff_cof (fun k => hX ((equivShrink.{u} I).symm k))
    (fun k => ι ((equivShrink.{u} I).symm k))
    ((Cofan.isColimitEquivOfEquiv (equivShrink.{u} I).symm (Cofan.mk G ι)) hG)

include hadm in
/-- **The coproduct in sheaves of an admissibly indexed family of algebraic spaces is an
algebraic space.**

The coproduct exists because the index type is `u`-small, by
`AlgebraicGeometry.Space.hasColimitsOfShape_discrete_sheaf`, and it is a colimit cofan by
`CategoryTheory.Limits.coproductIsCoproduct`. -/
public theorem isAlgebraicSpace_sigma_spaceSheaf :
    IsAlgebraicSpace B S hS (∐ fun i => spaceSheaf (X i) (hX i)).obj :=
  isAlgebraicSpace_of_isColimit_cofan_spaceSheaf X hX _
    (coproductIsCoproduct fun i => spaceSheaf (X i) (hX i))

include hadm in
/-- **An admissibly indexed family of algebraic spaces has an algebraic sheaf coproduct**,
namely its coproduct in sheaves on the big fppf site over `S`.

The colimit fields are the coproduct of sheaves and its universal property; the atlas field is
`AlgebraicGeometry.Space.Descent.isAlgebraicSpace_sigma_spaceSheaf`, whose atlas clause is
exactly it. -/
public def sigmaAlgebraicSheafCoproduct : AlgebraicSheafCoproduct X hX where
  sheaf := ∐ fun i => spaceSheaf (X i) (hX i)
  ι := Sigma.ι _
  isColimit := coproductIsCoproduct fun i => spaceSheaf (X i) (hX i)
  exists_atlas := (isAlgebraicSpace_sigma_spaceSheaf X hX).exists_atlas

include hadm in
/-- **Every admissibly indexed family of algebraic spaces over `S` admits an algebraic sheaf
coproduct.**

This is the form in which the hypothesis cutting out
`AlgebraicGeometry.Space.Descent.AlgebraicCoproductDescentData` is consumed. -/
public theorem nonempty_algebraicSheafCoproduct : Nonempty (AlgebraicSheafCoproduct X hX) :=
  ⟨sigmaAlgebraicSheafCoproduct X hX⟩

end Sigma

/-! ### The full subcategory of descent data is everything -/

section DescentData

variable {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I]
  {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (f : ∀ i, X i ⟶ T) (hT : IsAlgebraicSpace B S hS T)
  (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-- **The objects of a descent datum always admit an algebraic sheaf coproduct**, when the
index type of the family is admissible for the site.

This is the predicate that `AlgebraicGeometry.Space.Descent.AlgebraicCoproductDescentData`
imposes on an object of `AlgebraicGeometry.Space.Descent.DescentData`, so the statement says
that that full subcategory is the whole category. Note that no size hypothesis on the descent
datum appears: the objects `D.obj i` are algebraic spaces whose chosen atlases need not be
uniformly bounded, and bounding their supremum below the cutoff is precisely what the
cofinality condition on the index type does. -/
public theorem nonempty_algebraicSheafCoproduct_descentData (D : DescentData f hT hX) :
    Nonempty (AlgebraicSheafCoproduct (fun i => (D.obj i).left) D.obj_isAlgebraicSpace) :=
  nonempty_algebraicSheafCoproduct _ D.obj_isAlgebraicSpace

end DescentData

end AlgebraicGeometry.Space.Descent

end
