module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# The skyscraper sheaf functor is exact, and the derived stalk is a left adjoint

Let `Φ` be a point of a site `(C, J)` and let `A` be a category with products. The stalk functor
`Φ.sheafFiber : Sheaf J A ⥤ A` is exact, and Mathlib's
`CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction` makes the skyscraper sheaf
functor `A ⥤ Sheaf J A` right adjoint to it. Being a right adjoint, the skyscraper functor is
left exact for free; this file proves that it is also **right** exact as soon as products indexed
by the fibres of `Φ` are exact in `A`, that is, as soon as `A` satisfies Grothendieck's axiom
AB4*.

A skyscraper presheaf is a pointwise product of copies of its value, so the skyscraper presheaf
functor is right exact objectwise; the skyscraper *sheaf* functor is that functor followed by
sheafification, which is a left adjoint, hence right exact as well. Nothing else enters: no
vanishing theorem and no hypothesis on the site.

The consequence drawn here is the one that makes the stalk of an unbounded derived direct image a
right derived functor. Both the stalk and the skyscraper functor being exact, each acts on
unbounded derived categories degreewise and the adjunction between them descends to the
localizations, so the derived stalk is a left adjoint. For the small étale site of a scheme and a
geometric point this is
`Stacks.EtaleCohomology.smallEtaleStalkAb_mapDerivedCategory_isLeftAdjoint`, which is the
deferred input of `AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections`.

## Main definitions

* `CategoryTheory.Limits.piFunctorFlipObjIsoConstCompLim` — the functor taking an object to the
  product of copies of itself indexed by a fixed type is the constant diagram on the discrete
  category of that type, followed by the limit functor.
* `CategoryTheory.GrothendieckTopology.Point.skyscraperSheafFunctorIso` — the skyscraper sheaf
  functor of a point is the skyscraper presheaf functor followed by sheafification.

## Main results

* `CategoryTheory.Limits.preservesFiniteColimits_piFunctor_flip_obj` — the functor taking an
  object to the product of copies of itself indexed by a fixed type `I` is right exact when
  `I`-indexed products are exact.
* `CategoryTheory.GrothendieckTopology.Point.preservesFiniteColimits_skyscraperPresheafFunctor`
  and
  `CategoryTheory.GrothendieckTopology.Point.preservesFiniteColimits_skyscraperSheafFunctor` —
  the skyscraper presheaf and sheaf functors of a point are right exact under AB4*.
* `Stacks.EtaleCohomology.smallEtaleSkyscraperAb_preservesFiniteColimits` — the skyscraper sheaf
  functor of a geometric point of a scheme, on abelian sheaves of the small étale site, is right
  exact.
* `Stacks.EtaleCohomology.smallEtaleStalkAb_mapDerivedCategory_isLeftAdjoint` — the stalk at a
  geometric point of abelian sheaves on the small étale site is a left adjoint on unbounded
  derived categories.

## Implementation notes

Exactness of `I`-indexed products in `A` is taken in the form `AB4StarOfSize.{w} A`, which is
exactly `HasExactLimitsOfShape (Discrete I) A` for every `I : Type w`; the `I`-fold product
functor is identified with `Functor.const (Discrete I) ⋙ lim`, whose first factor is a left
adjoint and whose second is right exact by that axiom. For abelian groups the axiom is Mathlib's
`AB4Star AddCommGrpCat.{v}`, which covers index types in `Type v`; the fibres of a point of the
small étale site of a scheme in `Scheme.{u}` are in `Type u` while the coefficients are
`Ab.{u + 1}`, so the index universe is lowered with
`CategoryTheory.AB4StarOfSize_shrink`.

The passage to unbounded derived categories is the repo's
`CategoryTheory.Adjunction.mapDerivedCategory`, the localization of the adjunction induced
degreewise on cochain complexes: both functors are exact, so both invert quasi-isomorphisms.
Nothing is derived in the sense of a Kan extension, and no K-injective resolution is involved;
the derived stalk is the degreewise action of the stalk, and the right adjoint produced is the
degreewise action of the skyscraper functor.

## References

* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w v' u' v u

namespace CategoryTheory.Limits

/-! ### Products of copies of a single object -/

section Pi

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]

/-- The functor taking an object of `A` to the product of copies of itself indexed by a fixed
type `I`, that is, `CategoryTheory.Limits.piConst` evaluated at `I`, is the constant diagram on
the discrete category of `I` followed by the limit functor. -/
def piFunctorFlipObjIsoConstCompLim (I : Type w) :
    (piConst.{w}.flip.obj (op I) : A ⥤ A) ≅ Functor.const (Discrete I) ⋙ lim := by
  refine NatIso.ofComponents
    (fun M => HasLimit.isoOfNatIso (Discrete.natIso (fun _ => Iso.refl M))) ?_
  intro M N f
  apply limit.hom_ext
  intro j
  obtain ⟨j⟩ := j
  simp [piConst]

/-- The functor taking an object to the product of copies of itself indexed by a fixed type `I`
is right exact as soon as `I`-indexed products are exact: it is a constant diagram functor, which
is a left adjoint, followed by the limit functor. -/
instance preservesFiniteColimits_piFunctor_flip_obj [AB4StarOfSize.{w} A] (I : Type w) :
    PreservesFiniteColimits (piConst.{w}.flip.obj (op I) : A ⥤ A) :=
  preservesFiniteColimits_of_natIso (piFunctorFlipObjIsoConstCompLim I).symm

end Pi

end CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology.Point

/-! ### Exactness of the skyscraper sheaf functor -/

section Skyscraper

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] (Φ : Point.{w} J)

/-- The skyscraper presheaf functor of a point is right exact as soon as products indexed by the
fibres of the point are exact: evaluated at an object of the site it is the product functor
indexed by the fibre there. -/
instance preservesFiniteColimits_skyscraperPresheafFunctor [AB4StarOfSize.{w} A] :
    PreservesFiniteColimits (Φ.skyscraperPresheafFunctor (A := A)) := by
  refine preservesFiniteColimits_of_evaluation _ fun X => ?_
  rw [skyscraperPresheafFunctor, flip_comp_evaluation]
  exact preservesFiniteColimits_of_natIso
    (piFunctorFlipObjIsoConstCompLim (A := A) (Φ.fiber.obj X.unop)).symm

variable [Abelian A] [HasSheafify J A]

/-- The skyscraper sheaf functor of a point is the skyscraper presheaf functor followed by
sheafification: a skyscraper presheaf is already a sheaf, so sheafifying it changes nothing. -/
def skyscraperSheafFunctorIso :
    (Φ.skyscraperSheafFunctor (A := A) ⋙ sheafToPresheaf J A) ⋙ presheafToSheaf J A ≅
      Φ.skyscraperSheafFunctor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft Φ.skyscraperSheafFunctor
      (asIso (sheafificationAdjunction J A).counit) ≪≫ Functor.rightUnitor _

/-- The skyscraper sheaf functor of a point is right exact as soon as products indexed by the
fibres of the point are exact: it is the skyscraper presheaf functor, which is then right exact,
followed by sheafification, which is a left adjoint. -/
instance preservesFiniteColimits_skyscraperSheafFunctor [AB4StarOfSize.{w} A] :
    PreservesFiniteColimits (Φ.skyscraperSheafFunctor (A := A)) := by
  have : PreservesFiniteColimits
      ((Φ.skyscraperSheafFunctor (A := A) ⋙ sheafToPresheaf J A) ⋙ presheafToSheaf J A) := by
    have : PreservesFiniteColimits (Φ.skyscraperSheafFunctor (A := A) ⋙ sheafToPresheaf J A) :=
      inferInstanceAs (PreservesFiniteColimits (Φ.skyscraperPresheafFunctor (A := A)))
    infer_instance
  exact preservesFiniteColimits_of_natIso (skyscraperSheafFunctorIso Φ)

end Skyscraper

end CategoryTheory.GrothendieckTopology.Point

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The derived stalk of an abelian étale sheaf is a left adjoint -/

section Stalk

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)

/-- Abelian groups one universe up satisfy Grothendieck's axiom AB4* for index types in the lower
universe: products of abelian groups are exact, and the index universe is lowered along the
equivalence of a discrete category with the discrete category of a lift. -/
theorem ab4StarOfSize_ab : AB4StarOfSize.{u} Ab.{u + 1} :=
  AB4StarOfSize_shrink.{u, u + 1} _

/-- The skyscraper sheaf functor at a geometric point of a scheme, right adjoint to the stalk on
abelian sheaves of the small étale site, is right exact, because products of abelian groups
indexed by the étale neighbourhoods' fibres are exact. -/
instance smallEtaleSkyscraperAb_preservesFiniteColimits :
    PreservesFiniteColimits
      ((Scheme.pointSmallEtale x).skyscraperSheafFunctor (A := Ab.{u + 1})) :=
  letI := ab4StarOfSize_ab.{u}
  inferInstance

/-- The skyscraper sheaf functor at a geometric point is additive, being a right adjoint. -/
instance smallEtaleSkyscraperAb_additive :
    ((Scheme.pointSmallEtale x).skyscraperSheafFunctor (A := Ab.{u + 1})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The stalk at a geometric point is a left adjoint on unbounded derived categories.** Both
the stalk and its right adjoint, the skyscraper sheaf functor, are exact, so each acts on
unbounded derived categories degreewise and the adjunction between them descends to the
localizations. -/
instance smallEtaleStalkAb_mapDerivedCategory_isLeftAdjoint :
    (smallEtaleStalkAb x).mapDerivedCategory.IsLeftAdjoint :=
  (Adjunction.mapDerivedCategory
    (Scheme.pointSmallEtale x).skyscraperSheafAdjunction).isLeftAdjoint

end Stalk

end Stacks.EtaleCohomology

end
