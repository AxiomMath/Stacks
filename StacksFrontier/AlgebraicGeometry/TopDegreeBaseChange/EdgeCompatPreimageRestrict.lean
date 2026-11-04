module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatRestrictSections
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# The cohomology edge morphism of derived sections over an inverse image, across the two models

`Stacks.Cohomology.DerivedSectionsLeray.preimageSections f V` is **by definition** sections over
`f⁻¹V` followed by restriction of scalars along `f^♯`, so two different functors derive it: the
total right derived functor `…DerivedSectionsLeray.derivedPreimageSections f V`, with its own
unit, and `RΓ(f⁻¹V, -)` followed by the functor the exact restriction of scalars induces on
derived categories. The identification of the degreewise functors is free — it is the definition,
which is why `…DerivedSectionsLeray.pushforwardPreimageSectionsIso` is `CategoryTheory.Iso.refl`
— but the two **right derived functors** are different objects with different units, and the edge
morphism is indexed by the unit. This file supplies the comparison and the compatibility of the
edge morphism with it, which is what lets
`Stacks.EdgeCompat.derivedHomologyComparison_sectionsOverOpenRestrict` — the compatibility of the
edge morphism of derived sections with restriction to a smaller open, stated for
`…DerivedSectionsLeray.sectionsOverOpen` at two opens of one space — be applied to the edge
morphism of `RΓ(f⁻¹V, -)` that the tail of conclusion (c) of [Stacks, Tag 0EX3] leaves behind.

`EdgeCompatRestrictSections.lean` is the template one-for-one: there the transformation fed to
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison_naturality_natTrans` — the naturality of the edge morphism in the
**functor** — is restriction of sections to a smaller open, here it is the **identity**, and in
both cases the work is the unit exhibiting the second right derived functor.

## Main results

* `Stacks.EdgeCompat.preimageRestrictScalars`: restriction of scalars along `f^♯`, with its
  source ring ascribed. See the implementation note: the ascription is what makes exactness
  synthesisable.
* `Stacks.EdgeCompat.preimageSectionsCompUnit` and
  `Stacks.EdgeCompat.isRightDerivedFunctor_preimageSectionsCompUnit`: `RΓ(f⁻¹V, -)` followed by
  restriction of scalars along `f^♯` is a right derived functor of sections over `f⁻¹V` read over
  `Γ(V, 𝒪_Y)`. The criterion is
  `…DerivedSectionsLeray.isRightDerivedFunctor_of_isIso_app_isKInjective`: restriction of scalars
  carries the invertibility of the unit at a K-injective complex along.
* `Stacks.EdgeCompat.preimageSectionsCompUnitComp` and
  `Stacks.EdgeCompat.isRightDerivedFunctor_preimageSectionsCompUnitComp`: the same transformation
  and the same instance at the definitionally equal spelling `f_* ⋙ Γ(V, -)` of the degreewise
  functor, which instance search does not reach from the other one.
* `Stacks.EdgeCompat.preimageSectionsModelComparison` and
  `Stacks.EdgeCompat.preimageSectionsModelComparison_fac_app`: the comparison of the two right
  derived functors, through the universal property of the first, and the factorisation that
  characterises it.
* `Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsModelComparison`: **the edge
  morphism of `RΓ(f⁻¹V, -)` in the `derivedPreimageSections` model is the comparison followed by
  the edge morphism in the other model.** No hypothesis on `f`, on `V` or on `q`.
* `Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsCompUnitComp_eq`: that edge
  morphism at the two spellings of the degreewise functor, which is `rfl`.
* `Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsCompUnit_eq`: **the edge morphism
  in the second model splits**, as the edge morphism of restriction of scalars followed by
  restriction of scalars applied to the edge morphism of `RΓ(f⁻¹V, -)` over `Γ(f⁻¹V, 𝒪_X)` —
  which is the one `derivedHomologyComparison_sectionsOverOpenRestrict` applies to. This is
  `derivedHomologyComparison_comp` at the pair `(Γ(f⁻¹V, -), res)` with the comparison of the
  two iterated derived functors the identity.

## Implementation notes

*No named iso for the functor-level identification, and none is declared.* `preimageSections f V`
*is* `sectionsOverOpen X (f⁻¹V) ⋙ ModuleCat.restrictScalars (f^♯ at V)`, as an `abbrev`, so the
transformation fed to the naturality lemma is the identity;
`…TopDegreeBaseChange.preimageSectionsRightDerivedIso` already passes `CategoryTheory.Iso.refl _`
at exactly this triple. The naturality lemma is stated along a natural transformation, so no
iso-shaped variant is needed either.

*Everything is stated at the spelling `f_* ⋙ Γ(V, -)` of the degreewise functor*, which is the
one `Stacks.EdgeCompat.derivedPreimageSectionsUnitComp` and
`…DerivedSectionsLeray.isRightDerivedFunctor_derivedPreimageSections_comp` use and therefore the
one the composite of the first three factors of the tail,
`…TopDegreeBaseChange.prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`,
ends at. It is definitionally `preimageSections f V`, but `RingedSpaceModuleAdjunction`
`.modulePushforward` is not reducible, so instance search does not cross between the two and a
statement at the other spelling would not match.

*Why the source ring of the restriction of scalars is ascribed.* `ModuleCat.restrictScalars`
takes its source ring as an implicit argument, and the type of `(structureSheafHom f).hom.app
(op V)` presents that ring as the sections over `V` of the **pushforward** of
`structureSheafRing X` along `opensMap f`. Elaborated with no expected type the functor is keyed
on that spelling, for which `CategoryTheory.Limits.PreservesFiniteLimits` is not synthesised,
while the ascribed spelling `Γ(f⁻¹V, 𝒪_X)` — the one the composition inside `preimageSections`
forces — is one for which it is. With the ring homomorphism ascribed, all three of
additivity and preservation of finite limits and colimits are found, and
`preimageSections f V = sectionsOverOpen X (f⁻¹V) ⋙ preimageRestrictScalars f V` holds by `rfl`.

*Only the `sectionsOverOpen` spelling of the inner factor is definitional.* The open-subscheme
reading of sections over `f⁻¹V` through `Stacks.Cohomology.AffineBase.moduleGlobalSections` needs
an `AlgebraicGeometry.Scheme.Opens.topIso` factor, which
`…TopDegreeBaseChange.app_comp_topIso_inv` supplies; nothing here crosses that divide.

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
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison
  derivedHomologyComparison_naturality_natTrans exactPostcomposeUnit
  isRightDerivedFunctor_exactPostcomposeUnit)

namespace Stacks.EdgeCompat

universe u vA uA vB uB vC uC

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Sheaves of modules on a ringed space have enough injectives: they form a Grothendieck abelian
category, in the one module universe available there. This is
`SheafOfModules.enoughInjectivesU` at three equal universes, which is not the shape instance
search finds unaided. -/
local instance moduleSheaves_enoughInjectives_preimage (Z : RingedSpace.{u, u}) :
    EnoughInjectives (SheafOfModules.{u} (structureSheafRing Z)) :=
  SheafOfModules.enoughInjectivesU.{u, u, u} (structureSheafRing Z)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier)

/-- **Restriction of scalars along `f^♯ : Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹V, 𝒪_X)`**, the second factor of
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections f V`, with the source ring of the
homomorphism ascribed so that exactness is synthesisable; see the implementation notes. -/
abbrev preimageRestrictScalars :
    ModuleCat.{u} ((structureSheafRing X).obj.obj (op ((opensMap f).obj V))) ⥤
      ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)) :=
  ModuleCat.restrictScalars
    (show ((structureSheafRing Y).obj.obj (op V)) →+*
        ((structureSheafRing X).obj.obj (op ((opensMap f).obj V))) from
      ((structureSheafHom f).hom.app (op V)).hom)

/-- **The unit exhibiting `RΓ(f⁻¹V, -)` followed by restriction of scalars along `f^♯` as a right
derived functor** of sections over `f⁻¹V` read over `Γ(V, 𝒪_Y)`. It is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` at the pair
`(Γ(f⁻¹V, -), res_{f^♯})`: the comparison of the two readings of restriction of scalars on the
derived category, followed by the unit of `RΓ(f⁻¹V, -)` pushed along restriction of scalars.
Restriction of scalars is exact, which is the general brick's only hypothesis on the second
factor — and the ascription of the source ring in `preimageRestrictScalars` is what makes that
exactness synthesisable; see the implementation notes.

`sectionsOverOpenRestrictCompUnit` is the same brick at a restriction map of the structure sheaf
in place of `f^♯`.

The type is written at the spelling `Γ(f⁻¹V, -) ⋙ res` of the degreewise functor, which is the
one the body lives at; `preimageSectionsCompUnitComp` is the same transformation at the spelling
`f_* ⋙ Γ(V, -)` that the consumers use. -/
def preimageSectionsCompUnit :
    (sectionsOverOpen X ((opensMap f).obj V) ⋙
          preimageRestrictScalars f V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
        (preimageRestrictScalars f V).mapDerivedCategory :=
  exactPostcomposeUnit (sectionsOverOpen X ((opensMap f).obj V)) (preimageRestrictScalars f V)
    (derivedSectionsOverOpen X ((opensMap f).obj V))
    (derivedSectionsOverOpenUnit X ((opensMap f).obj V))

/-- **`preimageSectionsCompUnit` does exhibit a right derived functor.** The general brick
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isRightDerivedFunctor_exactPostcomposeUnit`, with the K-injective resolutions on `X` supplied by
`Stacks.Cohomology.DerivedSectionsLeray.exists_quasiIso_isKInjective`. -/
instance isRightDerivedFunctor_preimageSectionsCompUnit :
    (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
        (preimageRestrictScalars f V).mapDerivedCategory).IsRightDerivedFunctor
      (preimageSectionsCompUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_exactPostcomposeUnit _ _ _ _ (exists_quasiIso_isKInjective X)

/-- **`preimageSectionsCompUnit` at the spelling `f_* ⋙ Γ(V, -)` of the degreewise functor.**
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections` and `f_* ⋙ Γ(V, -)` are the same
functor, so this is the same natural transformation; the `show` is what lets a statement at the
second spelling elaborate, and it is the spelling the composite of the first three factors
of the tail of [Stacks, Tag 0EX3] (c) ends at. This mirrors
`derivedPreimageSectionsUnitComp`. -/
abbrev preimageSectionsCompUnitComp :
    (modulePushforward f ⋙ sectionsOverOpen Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
        (preimageRestrictScalars f V).mapDerivedCategory :=
  preimageSectionsCompUnit f V

/-- **`isRightDerivedFunctor_preimageSectionsCompUnit`, re-registered at the second spelling.**
`CategoryTheory.Functor.IsRightDerivedFunctor` is indexed by the unit, whose type names the
degreewise functor, and instance search does not cross between the two definitionally equal
spellings because `RingedSpaceModuleAdjunction.modulePushforward` is not reducible. Nothing is
proved: the inhabitant is the one Lean already has. This is the pattern
`…DerivedSectionsLeray.isRightDerivedFunctor_derivedPreimageSections_comp` records. -/
instance isRightDerivedFunctor_preimageSectionsCompUnitComp :
    (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
        (preimageRestrictScalars f V).mapDerivedCategory).IsRightDerivedFunctor
      (show (modulePushforward f ⋙ sectionsOverOpen Y V).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
            (preimageRestrictScalars f V).mapDerivedCategory from
        preimageSectionsCompUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs ((derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
    (preimageRestrictScalars f V).mapDerivedCategory).IsRightDerivedFunctor
      (preimageSectionsCompUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)))

/-- **The comparison of the two right derived functors of sections over `f⁻¹V` read over
`Γ(V, 𝒪_Y)`**: the transformation from the total right derived functor
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections` to `RΓ(f⁻¹V, -)` followed by
restriction of scalars, induced by `preimageSectionsCompUnit` through the universal property of
the former. By `preimageSectionsModelComparison_fac_app` its composite with the unit of the
former is `preimageSectionsCompUnit`, and that equation determines it. -/
def preimageSectionsModelComparison :
    derivedPreimageSections f V ⟶
      derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
        (preimageRestrictScalars f V).mapDerivedCategory :=
  (derivedPreimageSections f V).rightDerivedDesc (derivedPreimageSectionsUnitComp f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (preimageSectionsCompUnitComp f V)

/-- The equation characterising `preimageSectionsModelComparison`, pointwise: composing it with
the unit of the total right derived functor recovers `preimageSectionsCompUnit`. -/
theorem preimageSectionsModelComparison_fac_app
    (L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnitComp f V).app L ≫
        (preimageSectionsModelComparison f V).app (DerivedCategory.Qh.obj L) =
      (preimageSectionsCompUnitComp f V).app L :=
  (derivedPreimageSections f V).rightDerived_fac_app (derivedPreimageSectionsUnitComp f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (preimageSectionsCompUnitComp f V) L

/-- **The cohomology edge morphism of derived sections over an inverse image does not depend on
which right derived functor computes it.** For a morphism `f : X ⟶ Y` of ringed spaces, an open
`V ⊆ Y` and a degree `q`, the edge morphism

> `H^q(RΓ(f⁻¹V, K)) ⟶ Γ(f⁻¹V, H^q K)`,

read over `Γ(V, 𝒪_Y)` and taken in the model
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections`, is
`preimageSectionsModelComparison` followed by the same edge morphism taken in the model
`RΓ(f⁻¹V, -)` followed by restriction of scalars along `f^♯`.

This is `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison_naturality_natTrans` at the **identity** transformation of the
degreewise functor, the two right derived functors being the two models and the coherence datum
being `preimageSectionsModelComparison_fac_app`. Nothing is assumed of `f`, of `V` or of `q`.

The left-hand side is the edge morphism the composite of the first three factors of the
tail of [Stacks, Tag 0EX3] (c) ends at, and the right-hand side is the one
`derivedHomologyComparison_sectionsOverOpenRestrict` can be applied to. -/
theorem derivedHomologyComparison_preimageSectionsModelComparison (q : ℤ) :
    derivedHomologyComparison (modulePushforward f ⋙ sectionsOverOpen Y V)
        (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V)
        (exists_quasiIso_isKInjective X) q =
      Functor.whiskerRight (preimageSectionsModelComparison f V)
          (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q) ≫
        derivedHomologyComparison (modulePushforward f ⋙ sectionsOverOpen Y V)
          (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
            (preimageRestrictScalars f V).mapDerivedCategory)
          (preimageSectionsCompUnitComp f V) (exists_quasiIso_isKInjective X) q := by
  have hcoh : Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (𝟙 (modulePushforward f ⋙ sectionsOverOpen Y V))
            (ComplexShape.up ℤ)) DerivedCategory.Qh ≫ preimageSectionsCompUnitComp f V =
      derivedPreimageSectionsUnitComp f V ≫
        Functor.whiskerLeft DerivedCategory.Qh (preimageSectionsModelComparison f V) := by
    ext L
    simpa only [NatTrans.mapHomotopyCategory_id, Functor.whiskerRight_id', NatTrans.comp_app,
      NatTrans.id_app, Functor.whiskerLeft_app, Category.id_comp] using
      (preimageSectionsModelComparison_fac_app f V L).symm
  have key := derivedHomologyComparison_naturality_natTrans
    (modulePushforward f ⋙ sectionsOverOpen Y V)
    (𝟙 (modulePushforward f ⋙ sectionsOverOpen Y V))
    (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V)
    (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
      (preimageRestrictScalars f V).mapDerivedCategory)
    (preimageSectionsCompUnitComp f V) (preimageSectionsModelComparison f V) hcoh
    (exists_quasiIso_isKInjective X) q
  simpa only [Functor.whiskerLeft_id', Category.comp_id] using key

/-- **A trailing identity dropped, at variables of an abstract category.** The coherence datum
that `derivedHomologyComparison_comp` asks for carries the comparison of the two iterated derived
functors, which is the identity here, and `CategoryTheory.Category.comp_id` cannot be rewritten
in the concrete goal: the motive it would build is not type-correct at `implicit` transparency,
restriction of scalars along `f^♯` being keyed on the ascribed spelling of its source ring. At
variables the check is at default transparency, where the two agree. -/
private theorem comp_id_eq {C : Type*} [Category* C] {P Q : C} {a b : P ⟶ Q} (h : a = b) :
    a ≫ 𝟙 Q = b := by
  rw [Category.comp_id, h]

/-- **The edge morphism in the second model, at the two spellings of the degreewise functor.**
`f_* ⋙ Γ(V, -)` and `Γ(f⁻¹V, -) ⋙ res` are the same functor and `preimageSectionsCompUnitComp`
is `preimageSectionsCompUnit`, so the two edge morphisms are the same morphism; the
identification is `rfl`. It is split off as its own lemma because `RingedSpaceModuleAdjunction`
`.modulePushforward` is semireducible, so a tactic that has to see through it inside a longer
proof does not, while a standalone `rfl` is cheap. -/
theorem derivedHomologyComparison_preimageSectionsCompUnitComp_eq (q : ℤ) :
    derivedHomologyComparison (modulePushforward f ⋙ sectionsOverOpen Y V)
        (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
          (preimageRestrictScalars f V).mapDerivedCategory)
        (preimageSectionsCompUnitComp f V) (exists_quasiIso_isKInjective X) q =
      derivedHomologyComparison
        (sectionsOverOpen X ((opensMap f).obj V) ⋙ preimageRestrictScalars f V)
        (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
          (preimageRestrictScalars f V).mapDerivedCategory)
        (preimageSectionsCompUnit f V) (exists_quasiIso_isKInjective X) q :=
  rfl

/-- **The edge morphism of a model `RF ⋙ G.mapDerivedCategory` splits along the two factors**,
for `F` left exact additive with right derived functor `RF` presented by `unit`, and `G` **exact**:
it is the edge morphism of `G` at `RF K` — which, `G` being exact, is invertible by
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isIso_derivedHomologyComparison_mapDerivedCategory` — followed by `G` applied to the edge
morphism of `RF`.

This is `derivedHomologyComparison_comp` at the pair `(F, G)` with the comparison of the two
iterated derived functors the **identity**: the second model is `RF` followed by the functor `G`
induces on derived categories, on the nose, so the coherence datum the splitting asks for is the
definition of
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit`. Nothing is
assumed of `F` beyond left exactness, nothing of `G` beyond exactness, and nothing of `q`; the
K-injective resolutions upstairs and downstairs are explicit.

That `RF ⋙ G.mapDerivedCategory` is a right derived functor is taken as an instance argument
rather than built here; it is **not** an extra hypothesis, being
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isRightDerivedFunctor_exactPostcomposeUnit` at `hA`, and every call site has it registered as an
instance already. It is an argument only because `derivedHomologyComparison` needs it to *state*
the left-hand side, before any proof has run.

Stated once because the tail of [Stacks, Tag 0EX3] (c) splits two such models — sections over
`f⁻¹V` read over `Γ(V, 𝒪_Y)`, and sections over a smaller open `W` read over `Γ(V, 𝒪_Y)` through
two restrictions of scalars — and the two splittings are this lemma at two pairs. -/
theorem derivedHomologyComparison_exactPostcomposeUnit_eq {A : Type uA} [Category.{vA} A]
    [Abelian A] [HasDerivedCategory A] {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory B] {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (G : B ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (unit : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor unit (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [G.mapDerivedCategory.IsRightDerivedFunctor G.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    [(RF ⋙ G.mapDerivedCategory).IsRightDerivedFunctor (exactPostcomposeUnit F G RF unit)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g)
    (hB : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g) (q : ℤ) :
    derivedHomologyComparison (F ⋙ G) (RF ⋙ G.mapDerivedCategory)
        (exactPostcomposeUnit F G RF unit) hA q =
      (Functor.associator RF G.mapDerivedCategory
            (DerivedCategory.homologyFunctor C q)).hom ≫
        Functor.whiskerLeft RF
            (derivedHomologyComparison G G.mapDerivedCategory
              G.mapDerivedCategoryFactorsh.inv hB q) ≫
          (Functor.associator RF (DerivedCategory.homologyFunctor B q) G).inv ≫
            Functor.whiskerRight (derivedHomologyComparison F RF unit hA q) G ≫
              (Functor.associator (DerivedCategory.homologyFunctor A q) F G).hom := by
  have hsplit := derivedHomologyComparison_comp F G q RF unit G.mapDerivedCategory
    G.mapDerivedCategoryFactorsh.inv (RF ⋙ G.mapDerivedCategory)
    (exactPostcomposeUnit F G RF unit) (𝟙 _) hA hB
    (fun L => comp_id_eq (by
      simp only [exactPostcomposeUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Category.assoc]))
  simpa only [Functor.whiskerRight_id', Category.id_comp] using hsplit

/-- **The cohomology edge morphism in the second model splits along the two factors.** For a
morphism `f : X ⟶ Y` of ringed spaces, an open `V ⊆ Y` and a degree `q`, the edge morphism

> `H^q(res(RΓ(f⁻¹V, K))) ⟶ Γ(f⁻¹V, H^q K)` over `Γ(V, 𝒪_Y)`

of the model `RΓ(f⁻¹V, -)` followed by restriction of scalars along `f^♯` is the edge morphism of
restriction of scalars at `RΓ(f⁻¹V, K)` — which, restriction of scalars being exact, is the
commutation of `H^q` with it — followed by restriction of scalars applied to the edge morphism of
`RΓ(f⁻¹V, -)` over `Γ(f⁻¹V, 𝒪_X)`.

This is `derivedHomologyComparison_exactPostcomposeUnit_eq` at the pair
`(Γ(f⁻¹V, -), ModuleCat.restrictScalars (f^♯ at V))` — that general lemma being
`Stacks.EdgeCompat.derivedHomologyComparison_comp` with the comparison of the two iterated
derived functors the **identity**, the second model being `RΓ(f⁻¹V, -)` followed by the functor
restriction of scalars induces on derived categories, on the nose. The K-injective resolutions
downstairs are `Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian` in the
module category over `Γ(f⁻¹V, 𝒪_X)`. Nothing is assumed of `f`, of `V` or of `q`.

Together with `derivedHomologyComparison_preimageSectionsModelComparison` this exposes
`Γ(f⁻¹V, -)`'s own edge morphism, which is the one
`derivedHomologyComparison_sectionsOverOpenRestrict` — factor 4 of the tail of
[Stacks, Tag 0EX3] (c) — applies to. -/
theorem derivedHomologyComparison_preimageSectionsCompUnit_eq (q : ℤ) :
    derivedHomologyComparison
        (sectionsOverOpen X ((opensMap f).obj V) ⋙ preimageRestrictScalars f V)
        (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
          (preimageRestrictScalars f V).mapDerivedCategory)
        (preimageSectionsCompUnit f V) (exists_quasiIso_isKInjective X) q =
      (Functor.associator (derivedSectionsOverOpen X ((opensMap f).obj V))
            (preimageRestrictScalars f V).mapDerivedCategory
            (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q)).hom ≫
        Functor.whiskerLeft (derivedSectionsOverOpen X ((opensMap f).obj V))
            (derivedHomologyComparison (preimageRestrictScalars f V)
              (preimageRestrictScalars f V).mapDerivedCategory
              (preimageRestrictScalars f V).mapDerivedCategoryFactorsh.inv
              (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
                (C := ModuleCat.{u} ((structureSheafRing X).obj.obj
                  (op ((opensMap f).obj V))))) q) ≫
          (Functor.associator (derivedSectionsOverOpen X ((opensMap f).obj V))
              (DerivedCategory.homologyFunctor
                (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ((opensMap f).obj V)))) q)
              (preimageRestrictScalars f V)).inv ≫
            Functor.whiskerRight
                (derivedHomologyComparison (sectionsOverOpen X ((opensMap f).obj V))
                  (derivedSectionsOverOpen X ((opensMap f).obj V))
                  (derivedSectionsOverOpenUnit X ((opensMap f).obj V))
                  (exists_quasiIso_isKInjective X) q) (preimageRestrictScalars f V) ≫
              (Functor.associator
                  (DerivedCategory.homologyFunctor
                    (SheafOfModules.{u} (structureSheafRing X)) q)
                  (sectionsOverOpen X ((opensMap f).obj V))
                  (preimageRestrictScalars f V)).hom := by
  have : (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
      (preimageRestrictScalars f V).mapDerivedCategory).IsRightDerivedFunctor
      (exactPostcomposeUnit (sectionsOverOpen X ((opensMap f).obj V))
        (preimageRestrictScalars f V) (derivedSectionsOverOpen X ((opensMap f).obj V))
        (derivedSectionsOverOpenUnit X ((opensMap f).obj V)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
    isRightDerivedFunctor_preimageSectionsCompUnit f V
  exact derivedHomologyComparison_exactPostcomposeUnit_eq (sectionsOverOpen X ((opensMap f).obj V))
    (preimageRestrictScalars f V) (derivedSectionsOverOpen X ((opensMap f).obj V))
    (derivedSectionsOverOpenUnit X ((opensMap f).obj V)) (exists_quasiIso_isKInjective X)
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
      (C := ModuleCat.{u} ((structureSheafRing X).obj.obj (op ((opensMap f).obj V))))) q

end Stacks.EdgeCompat

end
