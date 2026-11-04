module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmallSchemes
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoverings

/-!
# The small étale site of an algebraic space

Let `B` be a big fppf site containing a scheme `S`, and let `F` be a presheaf on the big
fppf site of `S` — in the intended application an algebraic space over `S`, in the sense of
`AlgebraicGeometry.IsAlgebraicSpace`. The *small étale site* of `F` has

* as objects the morphisms `φ : yoneda.obj U ⟶ F` from a representable presheaf which are
  representable and étale, i.e. the *étale charts* of `F`;
* as morphisms from `φ : yoneda.obj U ⟶ F` to `φ' : yoneda.obj U' ⟶ F` the morphisms
  `U ⟶ U'` of the big fppf site of `S` making the triangle over `F` commute;
* as covering families those whose family of underlying morphisms of schemes is a covering
  family of the big étale site carried by `B`.

This file constructs that site and shows that it is essentially small at the universe of
its schemes, which is what allows sheaves on it to take coefficients in universe `u`.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleChart` is the property of a scheme chart of `F` that it is
  representable and étale.
* `AlgebraicGeometry.Space.SmallEtale` is the small étale site of `F`, as a category, with
  `AlgebraicGeometry.Space.SmallEtale.toOver` and
  `AlgebraicGeometry.Space.SmallEtale.toSchemes` the projections to the big fppf site of `S`
  and to `Sch_κ`.
* `AlgebraicGeometry.Space.chartScheme` is the scheme underlying an étale chart.
* `AlgebraicGeometry.Space.SmallEtale.IsCovering` specifies its covering families,
  `AlgebraicGeometry.Space.SmallEtale.precoverage` is the precoverage they present, and
  `AlgebraicGeometry.Space.SmallEtale.topology` the Grothendieck topology they generate.

## Main results

* `AlgebraicGeometry.Space.instEssentiallySmallSchemes`: the underlying category `Sch_κ` of a
  big fppf site is essentially small at universe `u`, registered as an instance.
* `AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall` and
  `AlgebraicGeometry.Space.SmallEtale.instEssentiallySmallOver`: the small étale site and
  each of its slices are essentially small at universe `u`.
* The `instHasSheafify*` and `instWEqualsLocallyBijective*` instances supply sheafification
  and the characterization of local equivalences as locally bijective morphisms, for
  concrete coefficients and in particular for modules over a ring in an unrelated universe.

## Implementation notes

An object of the small étale site is a `CategoryTheory.CostructuredArrow yoneda F` — that
is, a pair of an object `U` of the big fppf site of `S` and a morphism
`yoneda.obj U ⟶ F` — cut out by the property that the morphism is representable and étale.
Taking the costructured-arrow category rather than defining the morphisms by hand is what
makes a morphism of charts *exactly* a commuting triangle, and it also makes the projection
to `U` a functor without any further work. The étaleness condition is spelled with the same
idiom as every other étaleness condition for algebraic spaces,
`CategoryTheory.MorphismProperty.presheaf` of the inverse image of
`AlgebraicGeometry.Etale` along `AlgebraicGeometry.BigFppfOver.toScheme`, so it is
definitionally the condition appearing in `AlgebraicGeometry.Space.IsEtale` and in the
étale-chart conditions of Stacks 03MJ.

The covering families are those of the big étale site in the sense of Stacks 03FF, i.e.
`AlgebraicGeometry.BigFppfSite.etaleCovering`: the big étale site carried by `B` has the
*same* underlying category `Sch_κ` as `B`, so a family of charts can be tested by its image
under `toSchemes` without any comparison of sites.

Essential smallness is where the size cutoff of the big fppf site is used. It passes from
`Sch_κ` (`AlgebraicGeometry.essentiallySmall_schemeBelow`) to the slice over `S`, which is a
costructured-arrow category over the identity functor; from there the presheaf category on
the slice is locally small at universe `u`, because restriction along the equivalence with a
small model is faithful; and a fully faithful functor from the charts into the
costructured-arrow category then makes the charts essentially small too.

The sheafification instances are given low priority. They fix the morphism universe of the
coefficient category to `u`; tried first on larger coefficients — `AddCommGrpCat.{max (u+1) v}`,
say — they leave behind a universe constraint that fails outright instead of backtracking to
Mathlib's general instances.

Mathlib's direct `PreservesFilteredColimits` instance for `ModuleCat` ties the universe of
the scalar ring to the universe of the modules. The local instance here routes through the
forgetful functor to abelian groups instead, so the scalar ring may live in an unrelated
universe `v`; this is needed because the structure sheaf of the small étale site takes
values in modules over rings of sections, whose universe is not the universe of the site.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- An *étale chart* of a presheaf `F` on the big fppf site of `S` is a scheme chart
`φ : yoneda.obj U ⟶ F` which is representable and whose every represented base change is an
étale morphism of schemes. -/
abbrev IsEtaleChart : ObjectProperty (CostructuredArrow yoneda F) :=
  fun X ↦ (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) X.hom

/-- **Stacks 03ED, parts (1) and (2).** The *small étale site* of a presheaf `F` on the big
fppf site of `S`, as a category: its objects are the étale charts of `F`, and its morphisms
are the morphisms of the big fppf site of `S` whose triangle over `F` commutes. -/
@[stacks 03ED "objects and morphisms", sga "4½ Arcata 2.1.4" "étale X-schemes"]
abbrev SmallEtale := (IsEtaleChart B S hS F).FullSubcategory

namespace SmallEtale

/-- The canonical full embedding of the étale charts of `F` into all its scheme charts. -/
abbrev inclusion : SmallEtale B S hS F ⥤ CostructuredArrow yoneda F :=
  (IsEtaleChart B S hS F).ι

/-- The object of the big fppf site of `S` underlying an étale chart. -/
abbrev toOver : SmallEtale B S hS F ⥤ BigFppfOver B S hS :=
  inclusion B S hS F ⋙ CostructuredArrow.proj yoneda F

/-- The object of `Sch_κ` underlying an étale chart. -/
abbrev toSchemes : SmallEtale B S hS F ⥤ B.Schemes :=
  toOver B S hS F ⋙ BigFppfOver.forget B S hS

/-- **Stacks 03ED, part (3).** A family of étale charts of `F` is a covering family exactly
when its family of underlying objects of `Sch_κ` is a chosen étale covering family of the
big étale site carried by `B`. -/
@[stacks 03ED "coverings", sga "4½ Arcata 2.1.4" "étale topology"]
abbrev IsCovering (E : Covering (SmallEtale B S hS F)) : Prop :=
  B.etaleCovering ⟨(toSchemes B S hS F).obj E.1, E.2.map (toSchemes B S hS F)⟩

/-- The precoverage presented by the covering families of étale charts. -/
def precoverage : Precoverage (SmallEtale B S hS F) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ IsCovering B S hS F ⟨X, E⟩}

/-- Membership in the small étale precoverage is characterized by a presenting covering
family of charts. -/
theorem mem_precoverage_iff {X : SmallEtale B S hS F} {R : Presieve X} :
    R ∈ precoverage B S hS F X ↔ ∃ E : PreZeroHypercover.{u + 1} X,
      R = E.presieve₀ ∧ IsCovering B S hS F ⟨X, E⟩ := Iff.rfl

/-- **Stacks 03ED.** The small étale topology of `F`, generated by its covering families of
étale charts. -/
abbrev topology : GrothendieckTopology (SmallEtale B S hS F) :=
  (precoverage B S hS F).toGrothendieck

/-- The small étale site has a small model at the universe of its schemes. -/
instance instEssentiallySmall : EssentiallySmall.{u} (SmallEtale B S hS F) := by
  have : EssentiallySmall.{u} (BigFppfOver B S hS) :=
    inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 B.Schemes) (B.obj hS)))
  have : LocallySmall.{u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    locallySmall_of_faithful
      ((Functor.whiskeringLeft _ _ (Type u)).obj
        (equivSmallModel.{u} (BigFppfOver B S hS)).inverse.op)
  exact essentiallySmall_of_fully_faithful (inclusion B S hS F)

/-- Every slice of the small étale site has a small model at the same universe. -/
instance instEssentiallySmallOver (U : SmallEtale B S hS F) : EssentiallySmall.{u} (Over U) :=
  inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 (SmallEtale B S hS F)) U))

section ConcreteSheafification

variable (A : Type v) [Category.{u} A]
  {FA : A → A → Type*} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- Sheafification on the small étale site, with concrete coefficients, transported from a
small model of the site. -/
instance (priority := low) instHasSheafify : HasSheafify (topology B S hS F) A :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Sheafification with concrete coefficients on each slice of the small étale site. -/
instance (priority := low) instHasSheafifyOver (U : SmallEtale B S hS F) :
    HasSheafify ((topology B S hS F).over U) A :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- The local equivalences of concrete presheaves on the small étale site are exactly the
locally bijective morphisms. -/
instance (priority := low) instWEqualsLocallyBijective :
    (topology B S hS F).WEqualsLocallyBijective A :=
  .ofEssentiallySmall.{u} _

/-- The same characterization of local equivalences on each slice of the small étale site. -/
instance (priority := low) instWEqualsLocallyBijectiveOver (U : SmallEtale B S hS F) :
    ((topology B S hS F).over U).WEqualsLocallyBijective A :=
  .ofEssentiallySmall.{u} _

end ConcreteSheafification

section ModuleCoefficients

variable (R : Type v) [Ring R]

/-- Forgetting a module to its underlying abelian group preserves filtered colimits. Unlike
Mathlib's direct instance for `ModuleCat`, this leaves the universe of the scalar ring
unconstrained by the universe of the modules. -/
local instance moduleCatForget_preservesFilteredColimits :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u} R)) := by
  have : PreservesColimitsOfSize.{u, u} (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u, v, u, u} R
  exact comp_preservesFilteredColimits (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (CategoryTheory.forget AddCommGrpCat.{u})

/-- Sheafification of presheaves of modules on the small étale site, for a scalar ring in an
unrelated universe. -/
instance (priority := low) instHasSheafifyModuleCat :
    HasSheafify (topology B S hS F) (ModuleCat.{u} R) :=
  instHasSheafify B S hS F _

/-- Sheafification of presheaves of modules on each slice of the small étale site, for a
scalar ring in an unrelated universe. -/
instance (priority := low) instHasSheafifyOverModuleCat (U : SmallEtale B S hS F) :
    HasSheafify ((topology B S hS F).over U) (ModuleCat.{u} R) :=
  instHasSheafifyOver B S hS F _ U

/-- The local equivalences of presheaves of modules on the small étale site are exactly the
locally bijective morphisms. -/
instance (priority := low) instWEqualsLocallyBijectiveModuleCat :
    (topology B S hS F).WEqualsLocallyBijective (ModuleCat.{u} R) :=
  instWEqualsLocallyBijective B S hS F _

/-- The same characterization of local equivalences of presheaves of modules on each slice. -/
instance (priority := low) instWEqualsLocallyBijectiveOverModuleCat
    (U : SmallEtale B S hS F) :
    ((topology B S hS F).over U).WEqualsLocallyBijective (ModuleCat.{u} R) :=
  instWEqualsLocallyBijectiveOver B S hS F _ U

end ModuleCoefficients

end SmallEtale

/-- The scheme underlying an étale chart of `F`. -/
abbrev chartScheme {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : SmallEtale B S hS F) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)

end AlgebraicGeometry.Space
