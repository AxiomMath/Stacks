module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CompatibilityWithRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.CohomologyOnACofilteredLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.NativeLongExactSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback map on native sheaf cohomology commutes with the connecting morphism

`Stacks.Cohomology.AbelianColimit.H'longExactSequence_exact` supplies the long exact sequence of
`Sheaf.H'` over a fixed open of a fixed space, with connecting morphism
`Stacks.Cohomology.AbelianColimit.H'δ`.  What the degree induction of Stacks 0A37 needs on top of
it is that the comparison arrows -- the maps on cohomology attached to a map of abelian sheaves
over a continuous map -- are *morphisms of δ-functors*, i.e. commute with `H'δ`.  **This file
supplies that.**

The route is `Ext`, not resolutions.  Native cohomology over `U` is `Ext` out of `freeOfOpen U`
(`H'functor_eq_extFunctorObj`), `H'δ` is postcomposition with `ShortComplex.ShortExact.extClass`,
and Mathlib's `CategoryTheory.Abelian.Ext.mapExactFunctor` transports an `Ext`-class along an
exact functor compatibly with `Ext`-composition (`Ext.mapExactFunctor_comp`), with `Ext.mk₀`
(`Ext.mapExactFunctor_mk₀`) and -- this is the input that makes the whole thing formal -- with the
`Ext`-class of a short exact sequence (`Ext.mapExactFunctor_extClass`).  So no comparison of
resolutions, and in particular no injective analogue of the horseshoe lemma, is involved: every
square below is an instance of associativity of `Ext`-composition.

## Main definitions

* `ModuleSheafCohomology.extMapExactHom`: **acting by an exact functor is a morphism of
  δ-functors** `extDeltaFunctor F X ⟶ extDeltaFunctor (F ⋙ Ψ) (Ψ.obj X)`.  This is the one new
  piece of homological algebra; the other two ways of mapping between the δ-functors
  `extDeltaFunctor` are precomposition in the corepresenting object, which is
  `ModuleSheafCohomology.extDeltaFunctorPrecomp`, and `extNatTransHom` below.
* `ModuleSheafCohomology.extNatTransHom`: a natural transformation of the exact functors induces a
  morphism of δ-functors `extDeltaFunctor F X ⟶ extDeltaFunctor F' X`.
* `ModuleSheafCohomology.extPullbackHom`: the composite of `extMapExactHom` with
  `extDeltaFunctorPrecomp`, which is the shape a comparison of cohomology across an exact functor
  has: act by the functor, then precompose with a map of corepresenting objects.
* `Stacks.Cohomology.AbelianColimit.H'deltaFunctor`: native cohomology over an open, as a
  δ-functor in the sheaf variable.  Its component functors are the `H'functor U n` and its
  connecting morphism is `H'δ`.
* `Stacks.Cohomology.AbelianColimit.H'pullback`: the induced map on native cohomology, for an
  exact functor `Ψ` of abelian sheaf categories and a map `freeOfOpen U ⟶ Ψ.obj (freeOfOpen V)`.
* `Stacks.Cohomology.AbelianColimit.H'restriction`: `H'pullback` for the identity functor and the
  map of corepresenting objects attached to `U ≤ V`, i.e. restriction of cohomology classes to a
  smaller open on a fixed space.
* `Stacks.Cohomology.AbelianColimit.sheafPullback`: the inverse image of abelian sheaves along a
  continuous map, at the spelling of the site of opens.
* `Stacks.Cohomology.AbelianColimit.freeOfOpenPullbackMap`: the map
  `freeOfOpen U ⟶ f⁻¹ (freeOfOpen V)` of corepresenting objects attached to a continuous map `f`
  and opens `U ≤ f⁻¹ V`, obtained from the adjunction unit.
* `Stacks.Cohomology.AbelianColimit.H'spacePullback`: the pullback map
  `Hⁿ(V, F) ⟶ Hⁿ(U, f⁻¹ F)` on native cohomology along a continuous map.
* `Stacks.Cohomology.AbelianColimit.rightDerivedSectionsDeltaFunctor`: right-derived sections over
  an open, as a universal δ-functor, transported from `Ext` along the canonical comparison.
* `Stacks.Cohomology.AbelianColimit.H'isoRightDerivedDelta`: the comparison of the two cohomology
  theories as an **isomorphism of δ-functors**, extending a degree-zero identification.

## Main results

* `Stacks.Cohomology.AbelianColimit.H'δ_naturality`: `H'δ` is natural in the short exact sequence.
  This field of the δ-functor was not previously available at the `H'δ` spelling.
* `Stacks.Cohomology.AbelianColimit.H'pullback_comp_H'δ`: **the pullback map on native cohomology
  commutes with the connecting morphism.**
* `Stacks.Cohomology.AbelianColimit.H'pullback_map_comp_H'δ`: the same square for an arbitrary map
  of short exact sequences over `Ψ`, which is the form the degree induction applies: a short exact
  sequence upstairs, one downstairs, and a map between the image of the first and the second.
* `Stacks.Cohomology.AbelianColimit.H'restriction_comp_H'δ`: the special case of restriction to a
  smaller open on a fixed space, which exhibits the hypotheses of the general statement at a map of
  corepresenting objects that is not the identity.
* `Stacks.Cohomology.AbelianColimit.H'spacePullback_comp_H'δ`: **the same square for the inverse
  image along an actual continuous map of spaces**, which is the case Stacks 0A37 needs.
* `Stacks.Cohomology.AbelianColimit.H'spacePullback_map_comp_H'δ`: **the comparison of the two long
  exact sequences across a continuous map**, for a short exact sequence upstairs, one downstairs,
  and a morphism between the inverse image of the first and the second.
* `Stacks.Cohomology.AbelianColimit.H'isoRightDerivedDelta_comm`: the comparison with right-derived
  sections commutes with the connecting morphisms.
* `Stacks.Cohomology.AbelianColimit.H'deltaFunctor_isUniversal`: native cohomology over an open is
  a **universal** δ-functor, because `Ext` out of anything against an injective object vanishes
  in positive degree (`CategoryTheory.Abelian.Ext.eq_zero_of_injective`).  This is the input that
  lets `CategoryTheory.DeltaFunctor.IsUniversal.isoOfIso` and
  `CategoryTheory.DeltaFunctor.Effaceable.hom_ext` compare two cohomology theories from their
  degree-zero parts alone.

## Implementation notes

The δ-functors here are `ModuleSheafCohomology.extDeltaFunctor F X`, whose degree-`n`
component is `F ⋙ extFunctorObj X n`; for `F` the identity and `X = freeOfOpen U` that functor is
`H'functor U n` on the nose, and the connecting morphism is `H'δ`, both by definitional unfolding.
So the statements below are phrased at the `H'functor`/`H'δ` spelling of
`Stacks.Cohomology.AbelianColimit` and proved by handing over the corresponding field of a
morphism of δ-functors.

The inverse-image functor is the only place where a spelling crossing has to be handled.
`TopCat.Sheaf C X` is a `def` for `Sheaf (Opens.grothendieckTopology X) C` with a `Category`
instance of its own (`deriving Category`), so the two spellings of the category of abelian sheaves
on a space are definitionally equal without being the same term, and instance search does not cross
between them.  With the type written out as `Sheaf J A ⥤ Sheaf J' A`, instance search for
`PreservesZeroMorphisms`, `PreservesFiniteColimits` and `Additive` of the inverse image *fails*
(it exhausts `synthInstance` heartbeats), because Mathlib's instances are keyed on
`TopCat.Sheaf.pullback`; and with the generic `Functor.sheafPullback` spelling it fails too,
because Mathlib's instances there go through the generic `leftAdjoint` machinery.  The fix is the
one used elsewhere for this family: supply each instance explicitly, by `inferInstanceAs` at the
spelling Mathlib keyed it on, and let the definitional equality be checked once in term position.
No option is needed for this.

`extMapExactHom` is stated for a general exact `F` and not only for the identity, because the
comparison the degree induction of Stacks 0A37 needs is between cohomology at two *different*
stages of a system: the source δ-functor there is cohomology over an open of one stage composed
with evaluation at that stage, and the target is cohomology over an open of another stage composed
with evaluation there, so neither `F` is the identity.

The identification of these maps with the maps
`Stacks.Cohomology.SpectralLimit.spaceCohomologyMap` that
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` prescribes, for the canonical identifications of
cohomology with right-derived sections, is
`Stacks.Cohomology.ExtComparison.isCohomologyMap_extSpacePullbackMap`
(`Topology/Sheaves/Cohomology/SpectralSpaceLimit/ExtComparisonInPositiveDegree.lean`).

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010R](https://stacks.math.columbia.edu/tag/010R)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Abelian

namespace ModuleSheafCohomology

/-! ### Acting by an exact functor is a morphism of δ-functors -/

section ExtMapExact

universe w v v' v'' u u' u''

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
  {A' : Type u'} [Category.{v'} A'] [Abelian A'] [HasExt.{w} A']
  {B : Type u''} [Category.{v''} B] [Abelian B]

variable (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (Ψ : A ⥤ A') [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] (X : A)

/-- The degree-`n` component of `extMapExactHom`: the additive map
`Ext X (F G) n ⟶ Ext (Ψ X) (Ψ (F G)) n` given by acting with the exact functor `Ψ` on
`Ext`-classes, natural in `G`. -/
def extMapExactNatTrans (n : ℕ) :
    (extDeltaFunctor F X).functor n ⟶ (extDeltaFunctor (F ⋙ Ψ) (Ψ.obj X)).functor n where
  app G := AddCommGrpCat.ofHom (Ψ.mapExtAddHom X (F.obj G) n)
  naturality {G G'} χ := by
    ext (e : Ext X (F.obj G) n)
    change Ext.mapExactFunctor Ψ (e.comp (Ext.mk₀ (F.map χ)) (add_zero n)) =
      (Ext.mapExactFunctor Ψ e).comp (Ext.mk₀ (Ψ.map (F.map χ))) (add_zero n)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- **Acting by an exact functor on `Ext`-classes is a morphism of δ-functors.**  The connecting
morphism of `extDeltaFunctor F X` at a short exact sequence `S` is postcomposition with the
`Ext`-class of `F(S)`, and `Ext.mapExactFunctor` turns a composition of `Ext`-classes into the
composition of their images (`Ext.mapExactFunctor_comp`) and the `Ext`-class of a short exact
sequence into the `Ext`-class of its image (`Ext.mapExactFunctor_extClass`); the compatibility is
exactly those two facts. -/
def extMapExactHom : extDeltaFunctor F X ⟶ extDeltaFunctor (F ⋙ Ψ) (Ψ.obj X) where
  app n := extMapExactNatTrans F Ψ X n
  comm {S} hS n := by
    ext (e : Ext X (F.obj S.X₃) n)
    change (Ext.mapExactFunctor Ψ e).comp (hS.map_of_exact (F ⋙ Ψ)).extClass rfl =
      Ext.mapExactFunctor Ψ (e.comp (hS.map_of_exact F).extClass rfl)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]

/-- The components of `extMapExactHom` are the action of `Ψ` on `Ext`-classes. -/
theorem extMapExactHom_app (n : ℕ) :
    (extMapExactHom F Ψ X).app n = extMapExactNatTrans F Ψ X n :=
  rfl

/-- **A natural transformation of the exact functors induces a morphism of δ-functors.**  The
degree-`n` component is postcomposition with `Ext.mk₀ (θ.app G)`, and the compatibility with the
connecting morphisms is the naturality of the `Ext`-class of a short exact sequence
(`ShortComplex.ShortExact.extClass_naturality`) applied to the morphism of short exact sequences
that `θ` induces. -/
def extNatTransHom {F F' : B ⥤ A} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (θ : F ⟶ F') (X : A) :
    extDeltaFunctor F X ⟶ extDeltaFunctor F' X where
  app n :=
    { app := fun G => AddCommGrpCat.ofHom ((Ext.mk₀ (θ.app G)).postcomp X (add_zero n))
      naturality := fun {G G'} χ => by
        ext (e : Ext X (F.obj G) n)
        change (e.comp (Ext.mk₀ (F.map χ)) (add_zero n)).comp
            (Ext.mk₀ (θ.app G')) (add_zero n) =
          (e.comp (Ext.mk₀ (θ.app G)) (add_zero n)).comp (Ext.mk₀ (F'.map χ)) (add_zero n)
        rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_second_deg_zero,
          Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, θ.naturality] }
  comm {S} hS n := by
    ext (e : Ext X (F.obj S.X₃) n)
    change (e.comp (Ext.mk₀ (θ.app S.X₃)) (add_zero n)).comp (hS.map_of_exact F').extClass rfl =
      (e.comp (hS.map_of_exact F).extClass rfl).comp (Ext.mk₀ (θ.app S.X₁)) (add_zero (n + 1))
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]
    exact congrArg (fun a => e.comp a rfl)
      ((hS.map_of_exact F).extClass_naturality (hS.map_of_exact F')
        { τ₁ := θ.app S.X₁, τ₂ := θ.app S.X₂, τ₃ := θ.app S.X₃
          comm₁₂ := (θ.naturality S.f).symm
          comm₂₃ := (θ.naturality S.g).symm }).symm

end ExtMapExact

/-! ### The comparison across an exact functor, as a morphism of δ-functors -/

section ExtPullback

universe v u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
  {A' : Type u'} [Category.{v} A'] [Abelian A'] [HasExt.{v} A']

/-- **The comparison of `Ext`-δ-functors across an exact functor**: act with `Ψ` on `Ext`-classes
and precompose with a map `X' ⟶ Ψ.obj X` of corepresenting objects.  This is the shape of every
comparison arrow of Stacks 0A37: the exact functor is an inverse image of abelian sheaves and the
map of corepresenting objects comes from the inclusion of opens. -/
def extPullbackHom (Ψ : A ⥤ A') [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ] (X : A) {X' : A'} (ρ : X' ⟶ Ψ.obj X) :
    extDeltaFunctor (𝟭 A) X ⟶ extDeltaFunctor Ψ X' :=
  extMapExactHom (𝟭 A) Ψ X ≫ extDeltaFunctorPrecomp Ψ ρ

end ExtPullback

end ModuleSheafCohomology

namespace Stacks.Cohomology.AbelianColimit

/-! ### Native cohomology over an open as a δ-functor -/

universe u

section DeltaFunctor

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- **Native cohomology over an open, as a cohomological δ-functor in the sheaf variable.**  Its
degree-`n` component functor is `H'functor U n` and its connecting morphism is `H'δ`, both by
definitional unfolding of `ModuleSheafCohomology.extDeltaFunctor`. -/
abbrev H'deltaFunctor (U : Opens X) :
    CategoryTheory.DeltaFunctor (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      AddCommGrpCat.{u} :=
  ModuleSheafCohomology.extDeltaFunctor
    (𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) (freeOfOpen U)

/-- The component functors of `H'deltaFunctor` are the native cohomology functors. -/
theorem H'deltaFunctor_functor (U : Opens X) (n : ℕ) :
    (H'deltaFunctor U).functor n = H'functor U n :=
  rfl

/-- The connecting morphism of `H'deltaFunctor` is `H'δ`. -/
theorem H'deltaFunctor_δ (U : Opens X)
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ) :
    (H'deltaFunctor U).δ hS n = H'δ hS U (rfl : n + 1 = n + 1) :=
  rfl

/-- **The connecting morphism is natural in the short exact sequence.**  For a morphism `Φ` of
short exact sequences of abelian sheaves, `Hⁿ⁰(U, Φ₃)` followed by the connecting morphism of the
target is the connecting morphism of the source followed by `Hⁿ¹(U, Φ₁)`.  This is the
`δ_naturality` field of `H'deltaFunctor`. -/
theorem H'δ_naturality (U : Opens X)
    {S T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hT : T.ShortExact) (Φ : S ⟶ T) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (H'functor U n₀).map Φ.τ₃ ≫ H'δ hT U h = H'δ hS U h ≫ (H'functor U n₁).map Φ.τ₁ := by
  subst h
  exact (H'deltaFunctor U).δ_naturality hS hT Φ n₀

/-- **Native cohomology over an open is a universal δ-functor.**  `Ext` out of any object against
an injective object vanishes in positive degree, so `H'deltaFunctor U` is effaceable, hence
universal by Stacks 010T.  This is what makes a comparison of two cohomology theories over an open
determined by -- and constructible from -- its degree-zero part alone. -/
theorem H'deltaFunctor_isUniversal (U : Opens X)
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] :
    (H'deltaFunctor U).IsUniversal := by
  refine ModuleSheafCohomology.extDeltaFunctor_isUniversal _ _ ?_
  intro I hI n e
  have : Injective
    ((𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).obj I) := hI
  exact Ext.eq_zero_of_injective e

end DeltaFunctor

/-! ### The δ-compatible comparison with right-derived sections -/

section RightDerived

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- Sections over an open are additive.  Stated locally because the existing statement of the same
fact, in `Stacks.Cohomology.ModuleComparison`, is itself a `local instance`. -/
local instance additive_abSections (U : Opens X) : (abSections U).Additive where
  map_add := by intros; rfl

/-- **Right-derived sections over an open, as a cohomological δ-functor.**  This is the
`Ext`-δ-functor transported along the canonical -- not chosen -- comparison
`ModuleSheafCohomology.extFunctorObjIsoRightDerived`, so its component functors are *literally*
the `(abSections U).rightDerived n`, and its connecting morphism is the conjugate of `H'δ`. -/
def rightDerivedSectionsDeltaFunctor (U : Opens X) :
    CategoryTheory.DeltaFunctor (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      AddCommGrpCat.{u} :=
  ModuleSheafCohomology.selfDerivedDeltaFunctor (abSections U) (freeOfOpen U)
    (ModuleSheafCohomology.evaluationRepresentation (Opens.grothendieckTopology X) U)

/-- The component functors of `rightDerivedSectionsDeltaFunctor` are the right-derived functors of
sections. -/
theorem rightDerivedSectionsDeltaFunctor_functor (U : Opens X) (n : ℕ) :
    (rightDerivedSectionsDeltaFunctor U).functor n = (abSections U).rightDerived n :=
  rfl

/-- Right-derived sections over an open form a **universal** δ-functor. -/
theorem rightDerivedSectionsDeltaFunctor_isUniversal (U : Opens X) :
    (rightDerivedSectionsDeltaFunctor U).IsUniversal :=
  ModuleSheafCohomology.selfDerivedDeltaFunctor_isUniversal _ _ _

/-- **The comparison of native cohomology with right-derived sections, as an isomorphism of
δ-functors.**  Both sides are universal δ-functors, so by Stacks 010U a degree-zero identification
extends uniquely to an isomorphism in every degree -- and that isomorphism is, by the definition of
a morphism of δ-functors, **compatible with the connecting morphisms**.

This is the shape in which the identifications that
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` takes as parameters
have to be supplied if the map it prescribes is to commute with anything: an unconstrained family
of isomorphisms `Sheaf.H' F p U ≅ ((sections X U).rightDerived p).obj F` satisfies no relation to
`H'δ`, whereas the components of this one do. -/
def H'isoRightDerivedDelta (U : Opens X)
    (e₀ : H'functor U 0 ≅ (abSections U).rightDerived 0) :
    H'deltaFunctor U ≅ rightDerivedSectionsDeltaFunctor U :=
  have := H'deltaFunctor_isUniversal U
  have := rightDerivedSectionsDeltaFunctor_isUniversal U
  CategoryTheory.DeltaFunctor.IsUniversal.isoOfIso e₀

/-- **The comparison isomorphism commutes with the connecting morphisms**, which is the content of
its being an isomorphism of δ-functors. -/
theorem H'isoRightDerivedDelta_comm (U : Opens X)
    (e₀ : H'functor U 0 ≅ (abSections U).rightDerived 0)
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ) :
    ((H'isoRightDerivedDelta U e₀).hom.app n).app S.X₃ ≫
        (rightDerivedSectionsDeltaFunctor U).δ hS n =
      H'δ hS U (rfl : n + 1 = n + 1) ≫
        ((H'isoRightDerivedDelta U e₀).hom.app (n + 1)).app S.X₁ :=
  (H'isoRightDerivedDelta U e₀).hom.comm hS n

end RightDerived

/-! ### The pullback map on native cohomology, and its compatibility with `H'δ` -/

section Pullback

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  (Ψ : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
  {V : Opens Y} {U : Opens X} (ρ : freeOfOpen U ⟶ Ψ.obj (freeOfOpen V))

/-- **The pullback map on native sheaf cohomology across an exact functor of abelian sheaf
categories.**  For an exact functor `Ψ` of abelian sheaf categories and a map
`ρ : freeOfOpen U ⟶ Ψ.obj (freeOfOpen V)` of the objects corepresenting sections, this is the
natural map `Hⁿ(V, F) ⟶ Hⁿ(U, Ψ F)`: act with `Ψ` on `Ext`-classes, then precompose with `ρ`. -/
def H'pullbackHom : H'deltaFunctor V ⟶ ModuleSheafCohomology.extDeltaFunctor Ψ (freeOfOpen U) :=
  ModuleSheafCohomology.extPullbackHom Ψ (freeOfOpen V) ρ

/-- The degree-`n` component of `H'pullbackHom`, as a natural transformation of cohomology
functors. -/
def H'pullback (n : ℕ) : H'functor V n ⟶ Ψ ⋙ H'functor U n :=
  (H'pullbackHom Ψ ρ).app n

/-- **The pullback map on native cohomology commutes with the connecting morphism.**  For a short
exact sequence `S` of abelian sheaves on `Y`, whose image under the exact functor `Ψ` is short
exact on `X`, the square

    Hⁿ⁰(V, S.X₃) ⟶ Hⁿ¹(V, S.X₁)
         ↓                ↓
    Hⁿ⁰(U, Ψ S.X₃) ⟶ Hⁿ¹(U, Ψ S.X₁)

with horizontal arrows the connecting morphisms and vertical arrows the pullback maps, commutes.
Equivalently: the pullback maps are the components of a morphism of δ-functors, which is the
statement the degree induction of Stacks 0A37 consumes. -/
theorem H'pullback_comp_H'δ
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})}
    (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (H'pullback Ψ ρ n₀).app S.X₃ ≫ H'δ (hS.map_of_exact Ψ) U h =
      H'δ hS V h ≫ (H'pullback Ψ ρ n₁).app S.X₁ := by
  subst h
  exact (H'pullbackHom Ψ ρ).comm hS n₀

/-- **The pullback map commutes with the connecting morphism, for a map of short exact
sequences.**  This is the form the comparison of two long exact sequences over a map of spaces
takes: a short exact sequence `S` of sheaves on `Y`, a short exact sequence `T` of sheaves on `X`,
and a morphism `Φ : Ψ(S) ⟶ T`.  It is `H'pullback_comp_H'δ` followed by the naturality of `H'δ`
in the short exact sequence. -/
@[ega "0 12.1.6" "more general"]
theorem H'pullback_map_comp_H'δ
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})}
    {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hT : T.ShortExact) (Φ : S.map Ψ ⟶ T) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    ((H'pullback Ψ ρ n₀).app S.X₃ ≫ (H'functor U n₀).map Φ.τ₃) ≫ H'δ hT U h =
      H'δ hS V h ≫ ((H'pullback Ψ ρ n₁).app S.X₁ ≫ (H'functor U n₁).map Φ.τ₁) := by
  rw [Category.assoc, H'δ_naturality U (hS.map_of_exact Ψ) hT Φ h,
    ← Category.assoc, H'pullback_comp_H'δ Ψ ρ hS h, Category.assoc]

end Pullback

/-! ### Restriction to a smaller open on a fixed space -/

section Restriction

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- **Restriction of native cohomology classes to a smaller open on a fixed space**, as a morphism
of δ-functors: `H'pullback` for the identity functor and the map of corepresenting objects
attached to `U ≤ V`.  This exhibits the general statement at a map of corepresenting objects that
is not an identity. -/
def H'restrictionHom {U V : Opens X} (h : U ≤ V) :
    H'deltaFunctor V ⟶ H'deltaFunctor U :=
  H'pullbackHom (𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (Stacks.Cohomology.ModuleComparison.freeYonedaSheafMap (Opens.grothendieckTopology X)
      (homOfLE h))

/-- The degree-`n` component of restriction to a smaller open. -/
def H'restriction {U V : Opens X} (h : U ≤ V) (n : ℕ) : H'functor V n ⟶ H'functor U n :=
  (H'restrictionHom h).app n

/-- **Restriction to a smaller open commutes with the connecting morphism.** -/
theorem H'restriction_comp_H'δ {U V : Opens X} (hUV : U ≤ V)
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (H'restriction hUV n₀).app S.X₃ ≫ H'δ hS U h =
      H'δ hS V h ≫ (H'restriction hUV n₁).app S.X₁ :=
  H'pullback_comp_H'δ _ _ hS h

end Restriction

/-! ### The inverse image along a continuous map of spaces -/

section Spaces

variable {X Y : TopCat.{u}}
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}]

/-- **The inverse image of abelian sheaves along a continuous map**, read at the spelling of the
site of opens, which is the one `H'functor` and `H'δ` are stated in.  It is `TopCat.Sheaf.pullback`
with its type written out; the ascription matters, because `TopCat.Sheaf` carries a `Category`
instance of its own and the two spellings of the category of abelian sheaves on a space are
definitionally equal without being the same term. -/
abbrev sheafPullback (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} f

variable (f : X ⟶ Y)

/-- The inverse image preserves zero morphisms, being a left adjoint.  Stated with
`inferInstanceAs` because the instance Mathlib declares is keyed on the `TopCat.Sheaf` spelling of
the category, and instance search does not cross between the two spellings. -/
instance sheafPullback_preservesZeroMorphisms : (sheafPullback f).PreservesZeroMorphisms :=
  inferInstanceAs ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).PreservesZeroMorphisms)

/-- The inverse image preserves finite colimits, being a left adjoint. -/
instance sheafPullback_preservesFiniteColimits : PreservesFiniteColimits (sheafPullback f) :=
  inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f))

/-- The inverse image preserves finite limits.  This is
`Stacks.Cohomology.BaseChange.abelianInverseImage_preservesFiniteLimits`, and it is the one of
the four exactness inputs that is not formal: it needs that the site of opens is small and that
`Opens.map f` is representably flat. -/
@[ega "0 12.1.3" "partial"]
instance sheafPullback_preservesFiniteLimits : PreservesFiniteLimits (sheafPullback f) :=
  Stacks.Cohomology.BaseChange.abelianInverseImage_preservesFiniteLimits f

/-- The inverse image is additive, preserving binary coproducts and zero morphisms. -/
instance sheafPullback_additive : (sheafPullback f).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (sheafPullback f)
  Functor.additive_of_preservesBinaryBiproducts _

/-- **The map of corepresenting objects attached to a continuous map and a compatible pair of
opens.**  `freeOfOpen U` corepresents sections over `U`, so a map
`freeOfOpen U ⟶ f⁻¹ (freeOfOpen V)` is the same thing as a section of `f⁻¹ (freeOfOpen V)` over
`U`, and the canonical one is the tautological section of `freeOfOpen V` over `V`, carried across
the adjunction unit `freeOfOpen V ⟶ f_* f⁻¹ (freeOfOpen V)` -- whose value over `V` is a section
of `f⁻¹ (freeOfOpen V)` over `f⁻¹ V` -- and then restricted to `U ≤ f⁻¹ V`.

Both corepresentations are read through the sheafification adjunction and
`ModuleSheafCohomology.freeEvaluationHomAddEquiv`, exactly as
`ModuleSheafCohomology.evaluationRepresentation` is; the step
`(f_* H)(V) = H(f⁻¹ V)` is definitional. -/
def freeOfOpenPullbackMap (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V) :
    freeOfOpen U ⟶ (sheafPullback f).obj (freeOfOpen V) :=
  let P := (sheafPullback f).obj (freeOfOpen V)
  let η : freeOfOpen V ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj P :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app (freeOfOpen V)
  let τ : P.obj.obj (op ((Opens.map f).obj V)) :=
    ModuleSheafCohomology.freeEvaluationHomAddEquiv V
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj P).obj)
      ((sheafificationAdjunction (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}).homEquiv
        (yoneda.obj V ⋙ AddCommGrpCat.free) _ η)
  ((sheafificationAdjunction (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}).homEquiv
      (yoneda.obj U ⋙ AddCommGrpCat.free) P).symm
    ((ModuleSheafCohomology.freeEvaluationHomAddEquiv U P.obj).symm
      (P.obj.map (homOfLE h).op τ))

/-- **The pullback map on native sheaf cohomology along a continuous map of spaces**,
`Hⁿ(V, F) ⟶ Hⁿ(U, f⁻¹ F)` for `U ≤ f⁻¹ V`, natural in the abelian sheaf `F` on the target. -/
def H'spacePullback (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V) (n : ℕ) :
    H'functor V n ⟶ sheafPullback f ⋙ H'functor U n :=
  H'pullback (sheafPullback f) (freeOfOpenPullbackMap f V U h) n

/-- **The pullback map on native sheaf cohomology along a continuous map commutes with the
connecting morphism.**  For a short exact sequence `S` of abelian sheaves on `Y`, an open
`V ⊆ Y`, an open `U ⊆ f⁻¹ V` and `n₀ + 1 = n₁`, the square

    Hⁿ⁰(V, S.X₃) ⟶ Hⁿ¹(V, S.X₁)
         ↓                ↓
    Hⁿ⁰(U, f⁻¹S.X₃) ⟶ Hⁿ¹(U, f⁻¹S.X₁)

commutes, the horizontal arrows being the connecting morphisms `H'δ` and the vertical arrows the
pullback maps.  This is the statement that the comparison maps of Tag 0A37 are the components of a
morphism of δ-functors, in the `Ext`-side description of those maps. -/
theorem H'spacePullback_comp_H'δ (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V)
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u})}
    (hS : S.ShortExact) {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁) :
    (H'spacePullback f V U h n₀).app S.X₃ ≫ H'δ (hS.map_of_exact (sheafPullback f)) U hn =
      H'δ hS V hn ≫ (H'spacePullback f V U h n₁).app S.X₁ :=
  H'pullback_comp_H'δ (sheafPullback f) (freeOfOpenPullbackMap f V U h) hS hn

/-- **The comparison of the two long exact sequences over a continuous map of spaces.**  Given a
short exact sequence `S` of abelian sheaves on `Y`, a short exact sequence `T` on `X`, and a
morphism `Φ : f⁻¹ S ⟶ T` -- equivalently, by adjunction, a morphism `S ⟶ f_* T` of short exact
sequences over `f`, which is the data a map of systems of abelian sheaves supplies at each stage --
the maps on cohomology commute with the connecting morphisms of the two sequences.

This is the form the degree induction of Stacks 0A37 applies, and it is what was missing: the
long exact sequence over an open of a stage and the long exact sequence over an open of the limit
were available separately, with no map between them in positive degree. -/
theorem H'spacePullback_map_comp_H'δ (V : Opens ↥Y) (U : Opens ↥X)
    (h : U ≤ (Opens.map f).obj V)
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u})}
    {T : ShortComplex (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hT : T.ShortExact) (Φ : S.map (sheafPullback f) ⟶ T)
    {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁) :
    ((H'spacePullback f V U h n₀).app S.X₃ ≫ (H'functor U n₀).map Φ.τ₃) ≫ H'δ hT U hn =
      H'δ hS V hn ≫ ((H'spacePullback f V U h n₁).app S.X₁ ≫ (H'functor U n₁).map Φ.τ₁) :=
  H'pullback_map_comp_H'δ (sheafPullback f) (freeOfOpenPullbackMap f V U h) hS hT Φ hn

end Spaces

end Stacks.Cohomology.AbelianColimit

end
