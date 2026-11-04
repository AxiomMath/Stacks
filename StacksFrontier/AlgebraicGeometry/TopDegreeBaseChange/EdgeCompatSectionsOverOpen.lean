module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatCollapseMirror
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowEdgeIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomologyEdge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayViaPlus

/-!
# The cohomology edge morphism of the derived direct image, against sections over an open

`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyComparison` is the
edge morphism `H^q(Rf_* K) ⟶ f_* H^q(K)` of the derived direct image. Conclusion (c) of
[Stacks, Tag 0EX3] meets it under sections over an affine open `V` of the base, where everything
else in sight is computed in the model of derived sections over an open. This file supplies the
one identity that lets it be read there: the edge morphism of `Rf_*` read under `Γ(V, -)` is
determined by the edge morphisms of derived sections over `V` and over `f⁻¹V`, together with the
Leray comparison of [Stacks, Tag 0D5W].

Nothing new is proved. `Stacks.EdgeCompat.derivedHomologyComparison_comp` says that the edge
morphism of a composite of two left exact functors splits as the cohomology of the comparison of
the two derived functors, the edge morphism of the outer functor, and the outer functor of the
edge morphism of the inner one. The direct image and sections over `V` are such a pair: their
composite is sections over `f⁻¹V` with scalars restricted, which is
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections` on the nose, and the comparison between
the two derived functors is the Leray comparison, whose characterising factorisation
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app_refl` is already written in
exactly the shape that splitting asks for. So the content here is the instantiation, and the
hypotheses are the ones either edge morphism needs anyway: K-injective resolutions upstairs and
downstairs, which is [Stacks, Tag 079P].

## Main results

* `Stacks.EdgeCompat.derivedPreimageSectionsHomologyComparison_eq`: **the edge morphism of
  derived sections over `f⁻¹V` splits** as the degree-`q` cohomology of the Leray comparison, the
  edge morphism of derived sections over `V` at `Rf_* -`, and `Γ(V, -)` of the edge morphism of
  `Rf_*`. No hypothesis on `f`, on `V`, on `q` or on the object.
* `Stacks.EdgeCompat.derivedPreimageSectionsHomologyComparison_app_eq`: the same read at an
  object of the unbounded derived category, which is the form a consumer meets. This is the
  compatibility of the edge morphism of `Rf_*` with `Γ(V, -)`: it exhibits
  `Γ(V, -)` of that edge morphism inside a composite whose other two factors are a cohomology of
  the Leray comparison and the edge morphism of `RΓ(V, -)`.
* `Stacks.EdgeCompat.isIso_sectionsOverOpenHomologyComparison_app_of_isGE`: the edge morphism of
  `RΓ(V, -)` is invertible at a cohomologically bounded below object whose cohomology sheaves are
  right acyclic for `Γ(V, -)`. This is the sections counterpart of
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`
  `.isIso_derivedPushforwardHomologyComparison_app_of_isGE`, and it is what supplies the inverse
  the form below consumes.
* `Stacks.EdgeCompat.map_sectionsOverOpen_derivedPushforwardHomologyComparison_app_eq`: **the
  compatibility solved for `Γ(V, -)` of the edge morphism of `Rf_*`.** The other two factors are
  the degree-`q` cohomology of the Leray comparison — invertible with no hypothesis, by
  `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison` — and the edge morphism of
  `RΓ(V, -)`, and their inverses are taken as hypotheses on plain morphisms, so that a consumer
  supplies whichever invertibility it holds.
* `Stacks.EdgeCompat.singleCompDerivedSections_hom_app_comp_rightDerivedCompNatIso_inv`:
  **[Stacks, Tag 01XK]'s collapse factor for the pair `(f_*, Γ(V, -))`, at the unbounded model.**
  `Stacks.EdgeCompat.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv` at that pair —
  the mirror lemma recorded in `BaseChangeSectionsTail.lean`. It is
  the other half of the dictionary: where the results above read `Γ(V, -)` of the edge morphism of
  `Rf_*`, this one reads the crossing from the unbounded model to the classical right derived
  functors, which is the model the `ψ` side of (c) is computed in.

## Implementation notes

*The unit of derived sections over the inverse image is passed at the composite's spelling.*
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsUnit` is stated for
`preimageSections f V`, and the splitting asks for a unit of
`(f_* ⋙ Γ(V, -)).mapHomotopyCategory _ ⋙ Qh`. The two functors are definitionally equal — which
is why `Stacks.Cohomology.DerivedSectionsLeray.pushforwardPreimageSectionsIso` is
`CategoryTheory.Iso.refl` — but instance search does not cross between them, so
`Stacks.Cohomology.DerivedSectionsLeray.isRightDerivedFunctor_derivedPreimageSections_comp`
records the right-derived-functor instance at the second spelling and the unit is written here
through the same `show`.

*Left exactness of the direct image is a local instance*, for the reason `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/HomologyEdge.lean`
records: the statement of an edge morphism needs it to elaborate, not only to prove.

*Enough injectives is a local instance too.* The invertibility criterion
`Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE` asks for it in the source
category, and on sheaves of modules over a ringed space it is `SheafOfModules.enoughInjectivesU`
at three equal universes; the instance Lean finds unaided is stated at `max u v` and does not
apply. The K-injective resolutions the edge morphisms themselves need are separate — they are
[Stacks, Tag 079P] in the form
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective` — and are passed
as arguments.

*The two inverses are hypotheses on plain morphisms rather than `CategoryTheory.IsIso` instances.*
That is the shape this directory measures as affordable: an identity whose factors are components
of natural transformations between iterated derived functors is matched by the unifier at
variables, and a hypothesis phrased with `CategoryTheory.inv` would have to be reconciled against
an instance found at the point of use.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison)

namespace Stacks.EdgeCompat

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Sheaves of modules on a ringed space have enough injectives: they form a Grothendieck abelian
category, in the one module universe available there. This is
`SheafOfModules.enoughInjectivesU` at three equal universes, which is not the shape instance
search finds unaided. -/
local instance moduleSheaves_enoughInjectives (Z : RingedSpace.{u, u}) :
    EnoughInjectives (SheafOfModules.{u} (structureSheafRing Z)) :=
  SheafOfModules.enoughInjectivesU.{u, u, u} (structureSheafRing Z)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier) (q : ℤ)

/-- **The unit of derived sections over an inverse image, at the spelling of the composite.**
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections` and `f_* ⋙ Γ(V, -)` are the same
functor, so this is the same natural transformation; the `show` is what lets the
right-derived-functor instance for it be found at the composite's spelling. -/
abbrev derivedPreimageSectionsUnitComp :
    (modulePushforward f ⋙ sectionsOverOpen Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedPreimageSections f V :=
  derivedPreimageSectionsUnit f V

/-- **The cohomology edge morphism of derived sections over an inverse image splits.** For a
morphism `f : X ⟶ Y` of ringed spaces, an open `V ⊆ Y` and a degree `q`, the edge morphism

> `H^q(RΓ(f⁻¹V, -)) ⟶ Γ(f⁻¹V, H^q(-))`

is the degree-`q` cohomology of the Leray comparison of [Stacks, Tag 0D5W], then the edge
morphism of `RΓ(V, -)` at `Rf_* -`, then `Γ(V, -)` of the edge morphism
`H^q(Rf_* -) ⟶ f_* H^q(-)` of the derived direct image.

This is the compatibility of that last edge morphism with sections over `V`: it is the only place
`Γ(V, -)` of it occurs in a composite all of whose other factors are computed in the model of
derived sections over an open.

There is no hypothesis on `f`, on `V`, on `q` or on the object: it is
`Stacks.EdgeCompat.derivedHomologyComparison_comp` at the pair `(f_*, Γ(V, -))`, whose
characterising factorisation is
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app_refl`. -/
theorem derivedPreimageSectionsHomologyComparison_eq :
    derivedHomologyComparison (modulePushforward f ⋙ sectionsOverOpen Y V)
        (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V)
        (exists_quasiIso_isKInjective X) q =
      Functor.whiskerRight (lerayComparison f V)
          (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q) ≫
        (Functor.associator (derivedPushforward f) (derivedSectionsOverOpen Y V)
            (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q)).hom ≫
          Functor.whiskerLeft (derivedPushforward f)
              (derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
                (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) q) ≫
            (Functor.associator (derivedPushforward f)
                (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) q)
                (sectionsOverOpen Y V)).inv ≫
              Functor.whiskerRight (derivedPushforwardHomologyComparison f q)
                  (sectionsOverOpen Y V) ≫
                (Functor.associator
                    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q)
                    (modulePushforward f) (sectionsOverOpen Y V)).hom :=
  derivedHomologyComparison_comp (modulePushforward f) (sectionsOverOpen Y V) q
    (derivedPushforward f) (derivedPushforwardUnit f)
    (derivedSectionsOverOpen Y V) (derivedSectionsOverOpenUnit Y V)
    (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V) (lerayComparison f V)
    (exists_quasiIso_isKInjective X) (exists_quasiIso_isKInjective Y)
    (lerayComparison_fac_app_refl f V)

/-- **The edge morphism of `Rf_*` read under `Γ(V, -)`, at an object.** This is
`derivedPreimageSectionsHomologyComparison_eq` evaluated at `K` in the unbounded derived category
of `𝒪_X`-modules, with the two associators discharged: the edge morphism of derived sections over
`f⁻¹V` at `K` is the degree-`q` cohomology of the Leray comparison at `K`, then the edge morphism
of `RΓ(V, -)` at `Rf_* K`, then `Γ(V, -)` of the edge morphism of `Rf_*` at `K`.

Both sides are maps `H^q(RΓ(f⁻¹V, K)) ⟶ Γ(V, f_* H^q(K))`, the right-hand end being sections over
`f⁻¹V` of the degree-`q` cohomology sheaf of `K`. Nothing is assumed of `K`. -/
theorem derivedPreimageSectionsHomologyComparison_app_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedHomologyComparison (modulePushforward f ⋙ sectionsOverOpen Y V)
          (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V)
          (exists_quasiIso_isKInjective X) q).app K =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).map
          ((lerayComparison f V).app K) ≫
        (derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
              (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) q).app
            ((derivedPushforward f).obj K) ≫
          (sectionsOverOpen Y V).map ((derivedPushforwardHomologyComparison f q).app K) :=
  (congr_app (derivedPreimageSectionsHomologyComparison_eq f V q) K).trans (by
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id])

/-- **The cohomology edge morphism of derived sections over an open is invertible** at a
cohomologically bounded below object whose cohomology sheaves are right acyclic for `Γ(V, -)`.

This is `Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE` at
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen`, which is left exact — evaluation of a
sheaf of modules at an open preserves finite limits. No hypothesis is placed on `V`: for an affine
open of an affine scheme and a `K` with quasi-coherent cohomology the acyclicity is
[Stacks, Tag 01XB]. -/
theorem isIso_sectionsOverOpenHomologyComparison_app_of_isGE (n : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) [K.IsGE n]
    (hH : ∀ j : ℤ, (sectionsOverOpen Y V).rightAcyclic
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) j).obj K)) :
    IsIso ((derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
      (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) q).app K) :=
  Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE (sectionsOverOpen Y V)
    (derivedSectionsOverOpen Y V) (derivedSectionsOverOpenUnit Y V)
    (exists_quasiIso_isKInjective Y) q K n hH

/-- **Two invertible leading factors moved to the other side of a three-fold composite.** From
`a ≫ b ≫ c = m` together with left inverses of `a` and of `b` one gets `c = b' ≫ a' ≫ m`. Stated
at variables of an abstract category, where the reassociation is free, and with each
invertibility on plain morphisms. -/
private theorem eq_of_comp_comp_eq {C : Type*} [Category* C] {P Q R T : C}
    {a : P ⟶ Q} {a' : Q ⟶ P} (ha : a' ≫ a = 𝟙 Q)
    {b : Q ⟶ R} {b' : R ⟶ Q} (hb : b' ≫ b = 𝟙 R)
    {c : R ⟶ T} {m : P ⟶ T} (h : a ≫ b ≫ c = m) : c = b' ≫ a' ≫ m := by
  rw [← h, ← Category.assoc a' a (b ≫ c), ha, Category.id_comp, ← Category.assoc b' b c, hb,
    Category.id_comp]

/-- **The edge morphism of `Rf_*` read under `Γ(V, -)`, solved for.** For a morphism `f : X ⟶ Y`
of ringed spaces, an open `V ⊆ Y`, a degree `q` and an object `K` of `D(𝒪_X)`,

> `Γ(V, -)` of the edge morphism `H^q(Rf_* K) ⟶ f_* H^q(K)`

is the inverse of the edge morphism of `RΓ(V, -)` at `Rf_* K`, then the inverse of the degree-`q`
cohomology of the Leray comparison of [Stacks, Tag 0D5W] at `K`, then the edge morphism of
`RΓ(f⁻¹V, -)` at `K`.

Both inverses are taken as left inverses of plain morphisms. The second exists with no
hypothesis, `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison` being unconditional;
the first is `isIso_sectionsOverOpenHomologyComparison_app_of_isGE` whenever `Rf_* K` is
cohomologically bounded below with `Γ(V, -)`-acyclic cohomology sheaves.

This is the form in which the compatibility is consumed: it exhibits `Γ(V, -)` of the edge
morphism of `Rf_*` — the one factor of the `γ⁺` side of [Stacks, Tag 0EX3] (c) that is not
computed in the model of derived sections over an open — as a composite entirely inside that
model. -/
theorem map_sectionsOverOpen_derivedPushforwardHomologyComparison_app_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {lInv : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).obj
        ((derivedSectionsOverOpen Y V).obj ((derivedPushforward f).obj K)) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).obj
        ((derivedPreimageSections f V).obj K)}
    (hl : lInv ≫ (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).map
          ((lerayComparison f V).app K) = 𝟙 _)
    {sInv : (sectionsOverOpen Y V).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) q).obj
          ((derivedPushforward f).obj K)) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).obj
        ((derivedSectionsOverOpen Y V).obj ((derivedPushforward f).obj K))}
    (hs : sInv ≫ (derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
            (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) q).app
          ((derivedPushforward f).obj K) = 𝟙 _) :
    (sectionsOverOpen Y V).map ((derivedPushforwardHomologyComparison f q).app K) =
      sInv ≫ lInv ≫ (derivedHomologyComparison (modulePushforward f ⋙ sectionsOverOpen Y V)
        (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V)
        (exists_quasiIso_isKInjective X) q).app K :=
  eq_of_comp_comp_eq hl hs
    (derivedPreimageSectionsHomologyComparison_app_eq f V q K).symm

/-- **One invertible leading factor moved to the other side of a composite.** From `a ≫ c = m`
together with a left inverse of `a` one gets `c = a' ≫ m`. Stated at variables of an abstract
category, with the invertibility on plain morphisms. -/
private theorem eq_of_comp_eq {C : Type*} [Category* C] {P Q T : C}
    {a : P ⟶ Q} {a' : Q ⟶ P} (ha : a' ≫ a = 𝟙 Q)
    {c : Q ⟶ T} {m : P ⟶ T} (h : a ≫ c = m) : c = a' ≫ m := by
  rw [← h, ← Category.assoc a' a c, ha, Category.id_comp]

/-- **The edge morphism of `RΓ(V, -)` and `Γ(V, -)` of the edge morphism of `Rf_*`, absorbed
together.** For a morphism `f : X ⟶ Y` of ringed spaces, an open `V ⊆ Y`, a degree `q` and an
object `K` of `D(𝒪_X)`, the composite

> `H^q(RΓ(V, Rf_* K)) ⟶ Γ(V, H^q(Rf_* K)) ⟶ Γ(V, f_* H^q(K))`

— the edge morphism of `RΓ(V, -)` at `Rf_* K` followed by `Γ(V, -)` of the edge morphism of
`Rf_*` at `K` — is the inverse of the degree-`q` cohomology of the Leray comparison of
[Stacks, Tag 0D5W] at `K`, followed by the edge morphism of `RΓ(f⁻¹V, -)` at `K`.

This is `derivedPreimageSectionsHomologyComparison_app_eq` solved for its **last two** factors
rather than for its last one, and that is the difference that matters: the only inverse it asks
for is the Leray one, which exists with no hypothesis at all by
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`. The companion
`map_sectionsOverOpen_derivedPushforwardHomologyComparison_app_eq` solves for `Γ(V, -)` of the
edge morphism of `Rf_*` alone, and so must additionally invert the edge morphism of `RΓ(V, -)` at
`Rf_* K` — which `isIso_sectionsOverOpenHomologyComparison_app_of_isGE` supplies only when the
cohomology sheaves of `Rf_* K` are `Γ(V, -)`-acyclic, a condition carrying a quasi-coherence
demand on `Rf_* K` and hence a quasi-compactness and quasi-separatedness demand on `f`.

A consumer that meets the edge morphism of `RΓ(V, -)` at `Rf_* K` immediately in front of
`Γ(V, -)` of the edge morphism of `Rf_*` — which is what the naturality of the edge morphism of
`RΓ(V, -)` produces, since it moves that edge morphism along any morphism of `D(𝒪_Y)` landing on
`Rf_* K` — should use this form and assume nothing of `f`. The left inverse is taken on a plain
morphism, as in the companion. -/
theorem sectionsOverOpenHomologyComparison_comp_map_derivedPushforwardHomologyComparison_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {lInv : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).obj
        ((derivedSectionsOverOpen Y V).obj ((derivedPushforward f).obj K)) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).obj
        ((derivedPreimageSections f V).obj K)}
    (hl : lInv ≫ (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).map
          ((lerayComparison f V).app K) = 𝟙 _) :
    (derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
            (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) q).app
          ((derivedPushforward f).obj K) ≫
        (sectionsOverOpen Y V).map ((derivedPushforwardHomologyComparison f q).app K) =
      lInv ≫ (derivedHomologyComparison (modulePushforward f ⋙ sectionsOverOpen Y V)
        (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V)
        (exists_quasiIso_isKInjective X) q).app K :=
  eq_of_comp_eq hl (derivedPreimageSectionsHomologyComparison_app_eq f V q K).symm

/-- **The edge morphism of `RΓ(V, -)` carried along a morphism into `Rf_* K` and absorbed.** For
a morphism `f : X ⟶ Y` of ringed spaces, an open `V ⊆ Y`, a degree `q`, an object `K` of `D(𝒪_X)`
and **any** morphism `β : A ⟶ Rf_* K` of `D(𝒪_Y)`, the composite

> `H^q(RΓ(V, A)) ⟶ Γ(V, H^q(A)) ⟶ Γ(V, f_* H^q(K))`

— the edge morphism of `RΓ(V, -)` at `A`, then `Γ(V, -)` of `H^q(β)` followed by the edge
morphism of `Rf_*` at `K` — is `H^q(RΓ(V, β))`, then the inverse of the degree-`q` cohomology of
the Leray comparison of [Stacks, Tag 0D5W] at `K`, then the edge morphism of `RΓ(f⁻¹V, -)` at `K`.

This is the naturality of the edge morphism of `RΓ(V, -)` along `β`, which moves it from `A` to
`Rf_* K`, followed by
`sectionsOverOpenHomologyComparison_comp_map_derivedPushforwardHomologyComparison_eq`. Only the
Leray inverse is asked for, and it is unconditional.

This is the form the tail of [Stacks, Tag 0EX3] (c) consumes. There the `γ⁺` side's tail is a
composite whose middle two factors are the degree-`d` cohomology of a morphism of `D(𝒪_{Y'})`
landing on `Rh_*` of the derived direct image along `f''`, followed by the edge morphism of
`Rh_*`; the morphism of derived categories is arbitrary, and `h` carries no hypothesis, so the
pair has to be read off in exactly this generality. -/
theorem sectionsOverOpenHomologyComparison_comp_map_comp_derivedPushforwardHomologyComparison_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {A : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (β : A ⟶ (derivedPushforward f).obj K)
    {lInv : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).obj
        ((derivedSectionsOverOpen Y V).obj ((derivedPushforward f).obj K)) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).obj
        ((derivedPreimageSections f V).obj K)}
    (hl : lInv ≫ (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).map
          ((lerayComparison f V).app K) = 𝟙 _) :
    (derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
            (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) q).app A ≫
        (sectionsOverOpen Y V).map
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) q).map β ≫
            (derivedPushforwardHomologyComparison f q).app K) =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).map
          ((derivedSectionsOverOpen Y V).map β) ≫
        lInv ≫ (derivedHomologyComparison (modulePushforward f ⋙ sectionsOverOpen Y V)
          (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V)
          (exists_quasiIso_isKInjective X) q).app K := by
  have hnat :
      (derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
              (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) q).app A ≫
          (sectionsOverOpen Y V).map
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing Y)) q).map β) =
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q).map
            ((derivedSectionsOverOpen Y V).map β) ≫
          (derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
              (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) q).app
            ((derivedPushforward f).obj K) :=
    ((derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
      (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) q).naturality β).symm
  rw [Functor.map_comp, ← Category.assoc, hnat, Category.assoc,
    sectionsOverOpenHomologyComparison_comp_map_derivedPushforwardHomologyComparison_eq f V q K hl]

/-! ### The collapse mirror of [Stacks, Tag 01XK] at the pair `(f_*, Γ(V, -))` -/

section Mirror

variable {Dc : Type*} [Category* Dc]
  (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X)) (n : ℕ)

/-- **[Stacks, Tag 01XK]'s collapse factor for the pair `(f_*, Γ(V, -))`, at the unbounded
model.** For a morphism `f : X ⟶ Y` of ringed spaces, an open `V ⊆ Y`, a functor
`E : Dc ⥤ Mod(𝒪_X)` and a degree `n`, the crossing of the two models of the iterated derived
functor of `Γ(V, -) ∘ f_*` at `E Z`, followed by Grothendieck's comparison
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` inverted, is

> the degree-`n` cohomology of the Leray comparison of [Stacks, Tag 0D5W] at `(E Z)[0]`, then the
> edge morphism of `RΓ(V, -)` at `Rf_*((E Z)[0])`, then `Γ(V, -)` of the crossing of the two
> models of `Rf_*` at `E Z`.

This is `Stacks.EdgeCompat.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv` at that
pair, whose characterising factorisation is
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app_refl`. The functor `E` is kept
general for the reason the mirror records: [Stacks, Tag 01XK] whiskers by the inclusion of the
quasi-coherent modules, and an `(𝟭 _).obj` in that slot obstructs unfolding.

Nothing is assumed of `f`, of `V` or of the object beyond `hpl`, the pointwise
homology-preservation hypothesis Grothendieck's comparison itself carries. -/
theorem singleCompDerivedSections_hom_app_comp_rightDerivedCompNatIso_inv
    (hpl : ∀ Z : Dc, (sectionsOverOpen Y V).PreservesLeftHomologyOf
      ((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (Z : Dc)
    [(sectionsOverOpen Y V).PreservesLeftHomologyOf
      ((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n)] :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (modulePushforward f ⋙ sectionsOverOpen Y V) (derivedPreimageSections f V)
            (derivedPreimageSectionsUnitComp f V) (exists_quasiIso_isKInjective X) n).hom.app
          (E.obj Z) ≫
        (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso E (modulePushforward f)
          (sectionsOverOpen Y V) n hpl).inv.app Z =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) (n : ℤ)).map
          ((lerayComparison f V).app
            ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
              (E.obj Z))) ≫
        (derivedHomologyComparison (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
              (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y) (n : ℤ)).app
            ((derivedPushforward f).obj
              ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
                (E.obj Z))) ≫
          (sectionsOverOpen Y V).map
            ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
              (modulePushforward f) (derivedPushforward f) (derivedPushforwardUnit f)
              (exists_quasiIso_isKInjective X) n).hom.app (E.obj Z)) :=
  singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv E (modulePushforward f)
    (sectionsOverOpen Y V) n (derivedPushforward f) (derivedPushforwardUnit f)
    (derivedSectionsOverOpen Y V) (derivedSectionsOverOpenUnit Y V)
    (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V) (lerayComparison f V)
    (exists_quasiIso_isKInjective X) (exists_quasiIso_isKInjective Y)
    (lerayComparison_fac_app_refl f V) hpl Z

end Mirror

end Stacks.EdgeCompat

end
