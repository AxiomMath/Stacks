module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Cohomology
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SiteEquivalenceGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE

/-!
# Cohomology over an object of the small étale site is étale cohomology of its scheme

Let `B` be a big étale site containing a scheme `X` and let `V` be an object of the small étale
site of `X`, that is, a scheme of `B` whose structure morphism to `X` is étale. The small étale
site of the scheme of `V` is the localization of the small étale site of `X` at `V`
(`AlgebraicGeometry.SmallEtale.localizationEquivalence`), and this file draws the cohomological
consequence: for an abelian sheaf `𝓕` on the small étale site of `X`, the global cohomology of
the restriction of `𝓕` to the slice at `V` is the library's étale cohomology of the *scheme* of
`V` with the restriction of `𝓕` to its small étale site,

`H^p(X_étale/V, 𝓕|_V) = H^p_étale(V, 𝓕|_V)`.

Together with
`Stacks.Cohomology.OverObjectCohomology.h'IsoHOver` — cohomology over an object of a site is
global cohomology on the slice site, available whenever the coefficient universe is the morphism
universe of the site — this is the comparison that turns a statement about `H^p` over an *object*
of `X_étale` into a statement about the étale cohomology of a *scheme*. The slice half is the
geometric one and is what is proved here; the `h'IsoHOver` half is pure site theory and already
exists.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLocalization.restrictToObject` — restriction of an abelian
  sheaf on the slice of the small étale site of `X` at `V` to the small étale site of the scheme
  of `V`, along `AlgebraicGeometry.SmallEtale.localizationEquivalence`.
* `Stacks.EtaleCohomology.SmallEtaleLocalization.sliceCohomologyFunctor` — the cohomology of the
  slice site, the `Ext`-groups out of its constant sheaf on `ℤ`.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLocalization.isEquivalence_restrictToObject` — restriction to
  the small étale site of the scheme of `V` is an equivalence on abelian sheaves.
* `Stacks.EtaleCohomology.SmallEtaleLocalization.localizationCohomologyFunctorIso` — **the
  cohomology of the slice at `V` is the étale cohomology of the scheme of `V`**, naturally in the
  abelian sheaf on the slice.
* `Stacks.EtaleCohomology.SmallEtaleLocalization.etaleCohomologyOverObjectIso` — the same at a
  fixed abelian sheaf `𝓕` on the small étale site of `X`, restricted to the slice.
* `Stacks.EtaleCohomology.SmallEtaleLocalization.restrictToObject_over_sections` — the sheaf whose
  étale cohomology appears is the expected one: its sections over an object `W` étale over the
  scheme of `V` are the sections of `𝓕` over `W` read as an object étale over `X`.

## Implementation notes

The comparison is `Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence`
applied to `AlgebraicGeometry.SmallEtale.localizationEquivalence`: that functor is continuous,
cocontinuous and a dense subsite inclusion for the two topologies, so restriction along it is an
equivalence of abelian sheaf categories, and an equivalence of sites changes neither the constant
sheaf on `ℤ` nor the injective objects, hence not the `Ext`-groups out of the constant sheaf. No
terminal object of either site enters, and `V` is an arbitrary object: no affineness and no open
immersion is assumed.

The four facts that abelian sheaf cohomology needs on the slice site — sheafification, local
smallness, enough injectives and `Ext` — are proved here from the general constructions, because
the slice of the small étale site is not a shape instance search reaches through.

Coefficients are `AddCommGrpCat.{u + 1}`, the universe of the *objects* of the small étale site,
which is the universe the library's `Stacks.EtaleCohomology.etaleCohomologyFunctor` is stated at.

## References

* [Stacks 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u

namespace Stacks.EtaleCohomology.SmallEtaleLocalization

open AlgebraicGeometry AlgebraicGeometry.SmallEtale

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (V : AlgebraicGeometry.SmallEtale B X hX)

/-- The slice of the small étale site of `X` at `V`, with its slice topology. -/
abbrev sliceTopology : GrothendieckTopology (Over V) := (SmallEtale.topology B X hX).over V

/-- The small étale topology of the scheme underlying `V`. -/
abbrev objTopology : GrothendieckTopology
    (AlgebraicGeometry.SmallEtale B V.obj.left.obj V.obj.left.property) :=
  SmallEtale.topology B V.obj.left.obj V.obj.left.property

/-! ### The abelian machinery of the slice site -/

/-- Abelian sheaves on the slice of the small étale site at `V` admit sheafification. -/
theorem hasSheafify_slice :
    HasSheafify (sliceTopology B X hX V) AddCommGrpCat.{u + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

attribute [local instance] hasSheafify_slice

/-- Abelian sheaves on the slice of the small étale site at `V` are locally `(u + 1)`-small. -/
theorem locallySmall_slice :
    LocallySmall.{u + 1} (Sheaf (sliceTopology B X hX V) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.locallySmall_of_small.{u + 1, u + 1, u, u + 1, u + 2}
    (sliceTopology B X hX V) AddCommGrpCat.{u + 1}

attribute [local instance] locallySmall_slice

/-- Abelian sheaves on the slice of the small étale site at `V` have enough injectives. -/
theorem enoughInjectives_slice :
    EnoughInjectives (Sheaf (sliceTopology B X hX V) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u + 1, u + 2}
    (sliceTopology B X hX V) AddCommGrpCat.{u + 1}

attribute [local instance] enoughInjectives_slice

/-- `Ext`-groups of abelian sheaves on the slice of the small étale site at `V` exist. -/
theorem hasExt_slice :
    HasExt.{u + 1} (Sheaf (sliceTopology B X hX V) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

attribute [local instance] hasExt_slice

/-- Abelian sheaves on the small étale site of the scheme of `V` admit sheafification. -/
theorem hasSheafify_obj :
    HasSheafify (objTopology B X hX V) AddCommGrpCat.{u + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

attribute [local instance] hasSheafify_obj

/-- Abelian sheaves on the small étale site of the scheme of `V` are locally `(u + 1)`-small. -/
theorem locallySmall_obj :
    LocallySmall.{u + 1} (Sheaf (objTopology B X hX V) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.locallySmall_of_small.{u + 1, u + 1, u, u + 1, u + 2}
    (objTopology B X hX V) AddCommGrpCat.{u + 1}

attribute [local instance] locallySmall_obj

/-- Abelian sheaves on the small étale site of the scheme of `V` have enough injectives. -/
theorem enoughInjectives_obj :
    EnoughInjectives (Sheaf (objTopology B X hX V) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u + 1, u + 2}
    (objTopology B X hX V) AddCommGrpCat.{u + 1}

attribute [local instance] enoughInjectives_obj

/-- `Ext`-groups of abelian sheaves on the small étale site of the scheme of `V` exist. -/
theorem hasExt_obj :
    HasExt.{u + 1} (Sheaf (objTopology B X hX V) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

attribute [local instance] hasExt_obj

/-! ### Restriction to the small étale site of the scheme of `V` -/

/-- **Restriction of an abelian sheaf on the slice of the small étale site of `X` at `V` to the
small étale site of the scheme of `V`**, along the localization equivalence. On sections it is
restriction along post-composition with the structure morphism of `V`. -/
abbrev restrictToObject :
    Sheaf (sliceTopology B X hX V) AddCommGrpCat.{u + 1} ⥤
      Sheaf (objTopology B X hX V) AddCommGrpCat.{u + 1} :=
  (localizationEquivalence B X hX V).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (objTopology B X hX V) (sliceTopology B X hX V)

/-- **Restriction to the small étale site of the scheme of `V` is an equivalence on abelian
sheaves.** The localization equivalence is a dense subsite inclusion for the two topologies. -/
theorem isEquivalence_restrictToObject : (restrictToObject B X hX V).IsEquivalence :=
  inferInstance

attribute [local instance] isEquivalence_restrictToObject

/-- The sections of the restriction of an abelian sheaf `𝓖` on the slice at `V` over an object
`W` of the small étale site of the scheme of `V` are the sections of `𝓖` over `W` read as an
object of the slice, that is, over `W ⟶ V ⟶ X` with its arrow to `V`. -/
theorem restrictToObject_sections
    (G : Sheaf (sliceTopology B X hX V) AddCommGrpCat.{u + 1})
    (W : AlgebraicGeometry.SmallEtale B V.obj.left.obj V.obj.left.property) :
    ((restrictToObject B X hX V).obj G).obj.obj (op W) =
      G.obj.obj (op ((localizationEquivalence B X hX V).functor.obj W)) :=
  rfl

/-- The sections, over an object `W` étale over the scheme of `V`, of the restriction of an
abelian sheaf `𝓕` on the small étale site of `X`: they are the sections of `𝓕` over `W` read as
an object étale over `X` by post-composition with the structure morphism of `V`. So the sheaf on
the small étale site of the scheme of `V` whose étale cohomology appears in
`Stacks.EtaleCohomology.SmallEtaleLocalization.etaleCohomologyOverObjectIso` is the expected
restriction of `𝓕`. -/
theorem restrictToObject_over_sections
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (W : AlgebraicGeometry.SmallEtale B V.obj.left.obj V.obj.left.property) :
    ((restrictToObject B X hX V).obj (F.over V)).obj.obj (op W) =
      F.obj.obj (op ((postcompose B X hX V).obj W)) :=
  rfl

/-! ### The comparison on cohomology -/

/-- The `p`-th cohomology functor of abelian sheaves on the slice of the small étale site of `X`
at `V`: the `Ext`-groups out of the constant sheaf on `ℤ`. -/
abbrev sliceCohomologyFunctor (p : ℕ) :
    Sheaf (sliceTopology B X hX V) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.functorH.{u + 1, u + 1, u, u + 1} (sliceTopology B X hX V) p

/-- **The cohomology of the slice of the small étale site of `X` at `V` is the étale cohomology
of the scheme of `V`.** For every degree `p`,

`H^p(V_étale, 𝓖|_{V_étale}) ≅ H^p(X_étale/V, 𝓖)`

naturally in the abelian sheaf `𝓖` on the slice, where the left hand side is the library's étale
cohomology functor of the scheme underlying `V`.

No affineness of `X` or of `V` is used, and `V` is an arbitrary object of the small étale site of
`X`: the small étale site of the scheme of `V` *is* the localization of the small étale site of
`X` at `V` (`AlgebraicGeometry.SmallEtale.localizationEquivalence`), so restriction along that
equivalence is an equivalence of abelian sheaf categories, which changes neither the constant
sheaf on `ℤ` nor the injective objects, hence not the `Ext`-groups out of the constant sheaf. -/
def localizationCohomologyFunctorIso (p : ℕ) :
    restrictToObject B X hX V ⋙
        Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨V.obj.left.obj, V.obj.left.property⟩ p ≅
      sliceCohomologyFunctor B X hX V p :=
  Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence.{u + 1, u, u, u + 1}
    (objTopology B X hX V) (sliceTopology B X hX V)
    (localizationEquivalence B X hX V).functor p

/-- **Cohomology over the object `V` is the étale cohomology of the scheme of `V`.** For an
abelian sheaf `𝓕` on the small étale site of `X` and a degree `p`,

`H^p(X_étale/V, 𝓕|_V) ≅ H^p_étale(V, 𝓕|_{V_étale})`,

the left hand side being the global cohomology of the restriction of `𝓕` to the slice at `V`,
which `Stacks.Cohomology.OverObjectCohomology.h'IsoHOver` identifies with the cohomology of `𝓕`
over the object `V`. The abelian sheaf on the right is the restriction of `𝓕` to the small étale
site of the scheme of `V`; `restrictToObject_over_sections` reads off its sections. -/
def etaleCohomologyOverObjectIso
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (sliceCohomologyFunctor B X hX V p).obj (F.over V) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨V.obj.left.obj, V.obj.left.property⟩ p).obj
        ((restrictToObject B X hX V).obj (F.over V)) :=
  ((localizationCohomologyFunctorIso B X hX V p).app (F.over V)).symm

end Stacks.EtaleCohomology.SmallEtaleLocalization

end
