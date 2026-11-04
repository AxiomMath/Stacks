module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.AbelianLowerShriek
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Lower shriek on sheaves of modules for a morphism of fibred categories

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, and let `g : (Sh(C'), O_{C'}) ⟶ (Sh(C), O_C)` be the morphism of
ringed topoi it induces, `Stacks.Sites.FibredCategory.MorphismSituation.gRinged`. This file is
the module-sheaf counterpart of the abelian lower-shriek development
`Stacks.Sites.FibredCategory.MorphismSituation.abelianLowerShriekAdjunction`: it shows that
`g^* = Stacks.Sheaves.RingedToposModules.pullbackModules S.gRinged.toModulesHom` admits a left
adjoint `g_!`,
which is **Stacks 08PC part (1) for sheaves of modules**, and records the exactness and
additivity statements that the forgetful squares of parts (2) and (4) take as inputs.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.moduleLowerShriek`: `g_! : Mod(O_{C'}) ⥤
  Mod(O_C)`, the chosen left adjoint of `g^*`.
* `Stacks.Sites.FibredCategory.MorphismSituation.moduleLowerShriekAdjunction`: the adjunction
  `g_! ⊣ g^*`.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.moduleDiagramInverseImage_isRightAdjoint`:
  **Stacks 08PC, part (1) for sheaves of modules.** `g^*` admits a left adjoint, for the `g` of
  an arbitrary commutative triangle of ringed topoi over the situation.
* `Stacks.Sites.FibredCategory.MorphismSituation.moduleInverseImage_isRightAdjoint`: the same at
  the canonical triangle, which is the form the functors below are defined from.
* `Stacks.Sites.FibredCategory.MorphismSituation.moduleInverseImage_exact`: `g^*` is exact.
* `Stacks.Sites.FibredCategory.MorphismSituation.moduleInverseImage_additive` and
  `Stacks.Sites.FibredCategory.MorphismSituation.moduleLowerShriek_additive`: both functors are
  additive, which is what lets them be applied degreewise to complexes.

## Implementation notes

Part (1) is stated twice. The tagged form takes a `MorphismSituation.RingedToposDiagram`, as
Stacks 08PC does, because that is where the two facts the proof needs are recorded: its
`g_underlying` and `g_inverseImage` fields say that `g⁻¹` is restriction along `u`, and
`gRinged_fSharpInverseImage_isIso` that the structure map is invertible. The untagged form at the
canonical `MorphismSituation.gRinged` — which is built from the situation `S` alone, needing no
diagram — is the one the lower-shriek functor and the exactness statements below are phrased at,
so that a consumer holding only `S` does not have to produce a diagram; it follows from the
tagged form instantiated at `MorphismSituation.ringedToposDiagram`, and is proved here directly
by the same route.

The two sheafification instances have to be restated at `(S.sourceTopos π').J` and not only
at `S.sourceTopology`, even though those are the *same* topology: `sourceTopos` is a `def`, so
instance search does not see through the projection, and given only the hypotheses at
`S.sourceTopology` it goes off to re-derive `HasWeakSheafify` from scratch and fails with a
universe constraint `max u₂ v₂ =?= max w u₀ u₁ u₂ v₀ v₁ v₂` — the site's universes against the
universe of the sections. Restating them is the whole fix; it is the same step that the
ringed-topos-of-a-morphism development takes for its `HasSheafCompose` instances at
`S.baseTopos.J`.

**How `g_!` is obtained, and why it needed two separate inputs.** `g^*` is the inverse image of
Stacks 03D2 followed by extension of scalars along `g♯ : g⁻¹O_C ⟶ O_{C'}`, so it is a right
adjoint as soon as both factors are. Neither is formal:

* the inverse image of Stacks 03D2 is built from the inverse image of sheaves of *sets*, in which
  it is a left adjoint and nothing says it is a right one. It becomes one because here `g⁻¹` is
  restriction along the continuous functor `u`, where the transported module structure on the
  sections is the original one
  (`Stacks.Sheaves.ToposPullback.restrictionModuleIso`) and restriction of sheaves of modules has
  the left adjoint `SheafOfModules.pullback` of Stacks 03D7. That is
  `Stacks.Sheaves.ToposPullback.pullbackModuleFunctor_restriction_isRightAdjoint`, which is where
  the independence of the universes of the two sites from the universe of the sections is used;
* extension of scalars is a left adjoint always, and a right adjoint here because `g♯` is the
  *isomorphism* `g⁻¹O_C ≅ O_{C'}` of Stacks 08PA
  (`Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharp_isRightAdjoint`).

The second of these also needed an identification that the development had deliberately left
unrecorded: `MorphismSituation.structureComparison` is an isomorphism of sheaves of *commutative*
rings, while scalars are extended along the adjunct taken in sheaves of *rings*. The two agree,
and that is `AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage`.

Both inputs live in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackModulesOfIsoStructureMap.lean`, stated for
an arbitrary morphism of ringed topoi with invertible structure map and at independent universes.
Stating them there rather than here is not presentation: at this situation's universes every
object universe sits inside the `max` that fixes the sections, and a type such as
`(restrictionModules S.sourceTopology S.totalTopology S.u O).IsRightAdjoint` written out by hand
asks for a `Category` instance on `SheafOfModules O` at a universe expression that Lean's level
normaliser does not identify with the one the instance carries. At plain universe variables the
same statements elaborate immediately, and instantiating them here needs no such comparison.

## What this file does not contain

Stacks 08PC parts (2), (3) and (4) for sheaves of modules are **not** here. Specifically, of the
module-side assertions of the tag:

* `inverseImageForgetIso` and `inverseImageForgetIso_underlying` — the canonical comparison of
  `g^*` with `g^{-1}` on underlying abelian sheaves, normalised through the unit of extension of
  scalars — are absent;
* `lowerShriekForgetComparison` and `lowerShriekForgetComparison_isIso` — part (2), that the
  square of `g_!`, `g_!^{Ab}` and the two forgetful functors commutes — are absent. The source
  reduces this to the invertibility of `g_!^{Ab} j_{U'!} O_{U'} ⟶ j_{u(U')!} O_{u(U')}` for every
  object `U'` of `C'` (Stacks 0798 and 08PB), which is genuine content and not a consequence of
  part (1). The criterion of Stacks 0798 itself *is* proved, as
  `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff`; what part (2) still owes is the
  section of Stacks 08PB that makes those maps invertible here;
* the derived assertions of parts (3) and (4) are absent.

Stacks 0D6X is **available**: it is proved in general form, for an arbitrary continuous functor of sites, as
`Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor`; Stacks 0D6Y and condition
(1) of Stacks 07A1 for the inverse image of an injective module are proved beside it in
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/TotalAcyclicityOfTheInverseImage.lean`.
Part (3) for modules is accordingly not blocked on 0D6X: the derived functor and its adjunction
are built in `StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedAdjunction.lean`
from the single acyclicity statement of Stacks 0794 at the class of direct sums of the
`j_{U!} O_U`, and
`Stacks.Cohomology.DerivedLowerShriek.lowerShriekAcyclic_of_ext_vanishing` reduces that
statement to the object-level vanishing of 0D6X read as an `Ext` group. What remains on
that route is the identification of `Ext^n(j_{U!} O_U, g^* I)` with the cohomology of
`g^{-1} I` over `U`. Part (4) is a forgetful-square comparison and is a separate assertion,
untouched by any of this.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})
  [HasWeakSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.sourceTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]

/-- Abelian sheaves can be sheafified on the source ringed topos. Registered separately from
the instance for `S.sourceTopology`: instance search does not see through the `sourceTopos`
projection, so a consumer that speaks of `(S.sourceTopos π').J` would re-derive it. -/
instance hasWeakSheafifySourceTopos
    (π' : _root_.MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    HasWeakSheafify (S.sourceTopos π').J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  inferInstanceAs
    (HasWeakSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- On the source ringed topos the weak equivalences of abelian sheaves are the locally
bijective morphisms. Registered at the projection spelling for the same reason as
`hasWeakSheafifySourceTopos`. -/
instance wEqualsLocallyBijectiveSourceTopos
    (π' : _root_.MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.sourceTopos π').J.WEqualsLocallyBijective
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  inferInstanceAs (S.sourceTopology.WEqualsLocallyBijective
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- The inverse image of sheaves of modules along `g` is additive, being a left adjoint of the
additive direct image `g_*`. `g^*` is
`Stacks.Sheaves.RingedToposModules.pullbackModules S.gRinged.toModulesHom`, the inverse image of
Stacks 03D2
followed by extension of scalars along `g^{-1}O_C ⟶ O_{C'}`, which in this situation is the
isomorphism `structureComparison`. Additivity is what lets it be applied degreewise to
complexes, which is how the total inverse image of Stacks 08PC part (3) is formed. -/
instance moduleInverseImage_additive :
    (S.gRinged.toModulesHom.pullbackModules).Additive :=
  inferInstance

section LowerShriek

variable [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]

/-- The inverse image of sheaves of modules of Stacks 03D2 along `g`, *before* extension of
scalars, admits a left adjoint: `g⁻¹` is restriction along the continuous functor `u`, and
restriction of sheaves of modules has the left adjoint of Stacks 03D7. -/
instance moduleRawInverseImage_isRightAdjoint :
    (Stacks.Sheaves.RingedToposModules.inverseImageModules S.gRinged.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O)).IsRightAdjoint :=
  Stacks.Sheaves.ToposPullback.pullbackModuleFunctor_restriction_isRightAdjoint
    S.sourceTopology S.totalTopology S.u
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O)

/-- The inverse image of sheaves of modules of Stacks 03D2 along the `g` of an *arbitrary*
commutative triangle of ringed topoi over the situation, before extension of scalars, admits a
left adjoint. A `MorphismSituation.RingedToposDiagram` carries exactly what the argument needs:
`g_underlying` and `g_inverseImage` together say that its `g⁻¹` is restriction along `u`. -/
instance moduleRawDiagramInverseImage_isRightAdjoint (D : S.RingedToposDiagram) :
    (Stacks.Sheaves.RingedToposModules.inverseImageModules D.gRinged.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos D.pi).O)).IsRightAdjoint :=
  Stacks.Sheaves.ToposPullback.inverseImageModules_isRightAdjoint_of_eq
    S.sourceTopology S.totalTopology S.u
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos D.pi).O)
    D.gRinged.toToposHom
    ((congrArg _root_.MorphismOfTopoi.inverseImage D.g_underlying).trans D.g_inverseImage)

/-- **Stacks 08PC, part (1) for sheaves of modules.** The inverse image of sheaves of modules
along the `g` of a commutative triangle of ringed topoi over the situation admits a left adjoint
`g_!`. The inverse image is the one of Stacks 03D2 followed by extension of scalars along `g♯`;
the first factor is a right adjoint because `g⁻¹` is restriction along the continuous functor
`u`, and the second because `g♯` is an isomorphism, which the triangle records. -/
@[stacks 08PC "part (1), modules"]
instance moduleDiagramInverseImage_isRightAdjoint (D : S.RingedToposDiagram) :
    (D.gRinged.toModulesHom.pullbackModules).IsRightAdjoint :=
  have := D.gRinged_fSharpInverseImage_isIso
  inferInstance

/-- Part (1) for sheaves of modules at the canonical triangle — the `g` of
`MorphismSituation.gRinged`, which is what the lower-shriek functor below is defined from. -/
instance moduleInverseImage_isRightAdjoint :
    (S.gRinged.toModulesHom.pullbackModules).IsRightAdjoint :=
  have : (Stacks.Sheaves.RingedToposModules.inverseImageModules S.gRinged.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O)).IsRightAdjoint :=
    S.moduleRawInverseImage_isRightAdjoint
  inferInstance

/-- `g^*` with every universe written out.
`Stacks.Sheaves.RingedToposModules.pullbackModules S.gRinged.toModulesHom` leaves the universe of
the module sections an unsolved metavariable whenever the surrounding statement does not pin it:
that universe occurs in the type of `MorphismSituation.gRinged` only inside the `max` fixing the
sections of the situation, and a `max` cannot be inverted. Writing it out once here, as a
`reducible` name, is what lets the statements below be about `g^*` and nothing else. -/
abbrev moduleInverseImage :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    max w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁} (gRinged.{u₀, u₁, u₂, v₀, v₁, v₂, w} S).toModulesHom

/-- `g_! : Mod(O_{C'}) ⥤ Mod(O_C)`, the lower-shriek functor on sheaves of modules: the chosen
left adjoint of `g^*`. -/
abbrev moduleLowerShriek := S.moduleInverseImage.leftAdjoint

/-- The adjunction `g_! ⊣ g^*` of Stacks 08PC, part (1) for sheaves of modules. -/
abbrev moduleLowerShriekAdjunction : S.moduleLowerShriek ⊣ S.moduleInverseImage :=
  Adjunction.ofIsRightAdjoint S.moduleInverseImage

/-- The lower-shriek functor on sheaves of modules is additive, being a left adjoint of the
additive functor `g^*`. This is what lets it be applied degreewise to complexes of sheaves of
modules, which is how the derived functor `Lg_!` of Stacks 08PC part (3) is formed. -/
instance moduleLowerShriek_additive : S.moduleLowerShriek.Additive :=
  S.moduleLowerShriekAdjunction.left_adjoint_additive

/-- The inverse image of sheaves of modules along `g` is a left adjoint, by Stacks 03D7: its
right adjoint is the direct image `g_*`. Recorded so that the colimit-preservation instance
below is available. -/
instance moduleInverseImage_isLeftAdjoint : S.moduleInverseImage.IsLeftAdjoint :=
  (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
    (gRinged.{u₀, u₁, u₂, v₀, v₁, v₂, w} S)).isLeftAdjoint

/-- The inverse image of sheaves of modules along `g` preserves finite limits, being a right
adjoint by part (1). -/
instance moduleInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits S.moduleInverseImage :=
  inferInstance

/-- The inverse image of sheaves of modules along `g` preserves finite colimits, being the left
adjoint of `g_*` in Stacks 03D7. -/
instance moduleInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits S.moduleInverseImage :=
  have : PreservesColimitsOfSize.{0, 0} S.moduleInverseImage :=
    (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (gRinged.{u₀, u₁, u₂, v₀, v₁, v₂, w} S)).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **The inverse image of sheaves of modules along `g` is exact.** Left exactness holds because
`g^*` is a right adjoint by part (1) — which is where the exactness of restriction along `u` and
the invertibility of `g♯` enter — and right exactness because it is the left adjoint of `g_*` in
Stacks 03D7. -/
theorem moduleInverseImage_exact : exactFunctor _ _ S.moduleInverseImage :=
  (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩

end LowerShriek

end Stacks.Sites.FibredCategory.MorphismSituation

end
