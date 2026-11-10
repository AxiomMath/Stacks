module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCartesianModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleAffineCechCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictionOfUniv

/-!
# Čech vanishing for a quasi-coherent module on the spaces-étale site of an algebraic space

Let `Y` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `ℳ` be
a quasi-coherent module on the ringed spaces-étale site of `Y` of [Stacks, Tag 03G0], with its
sections in the universe `u + 1` of that site.  Restricting `ℳ` along the comparison functor of
[Stacks, Tag 03G1] gives an abelian presheaf on the *small* étale site of `Y`, and this file
proves that **its Čech cohomology vanishes in positive degrees on every finite covering family,
by affine charts, of an affine chart.**

That vanishing is the one hypothesis of the Čech-to-derived criterion
`AlgebraicGeometry.Space.subsingleton_sheafH_spacesEtale_of_isZero_cechCohomology`, and the
positive-degree vanishing of the cohomology of `ℳ` on an *affine* algebraic space follows at
once; that is the one input of the alternating Čech recursion of [Stacks, Tag 072C] which the
recursion cannot supply itself.

## The three pieces

`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_of_isoAtFibreProducts_baseChange`
reduces the vanishing to a comparison of the coefficients with the base-change presheaf
`V ↦ Γ(V, 𝒪) ⊗_R M₀` of [Stacks, Tag 03FJ], asked only at the iterated fibre products of the
family.  Supplying that comparison is what this file does, in three steps.

* **The coefficient module.** The sections of `ℳ` over the algebraic space attached to a chart
  `V` are a module over the ring of global regular functions of that algebraic space, and
  `AlgebraicGeometry.Space.comparisonGlobalFunctionsRingEquiv` identifies the latter with
  `Γ(V, 𝒪)`.  Restricting scalars along that identification is
  `AlgebraicGeometry.Space.SmallEtale.moduleChartSections`, and the restriction maps of the
  coefficients are semilinear for it
  (`AlgebraicGeometry.Space.SmallEtale.chartSectionsRestrict_smul`), because the identification
  is natural.
* **The comparison.** `AlgebraicGeometry.Space.SmallEtale.baseChangeComparison` is the map
  `a ⊗ x ↦ a • x|_V`, built from the semilinear restriction maps by
  `TensorProduct.liftAddHom`.  Balancedness over the base ring is
  `AlgebraicGeometry.overAffineAlgΓBase_algebraMap`: the lifted base ring acts on a coordinate
  algebra through pullback of global sections along the structure morphism, which is exactly the
  ring map the restriction maps are semilinear over.
* **Invertibility at an affine object.** This is cartesianness of `ℳ`.  The module is carried to
  the affine étale site of [Stacks, Tag 0H01] — restricted along the comparison functor, then
  along the comparison of structure sheaves
  `AlgebraicGeometry.Space.comparisonStructureSheafIso`, then to the affine charts — where
  `AlgebraicGeometry.Space.isIso_restrictionBaseChange_of_isQuasicoherentOnSite` is
  [Stacks, Tag 0H04].  The base-change comparison it provides tensors over the *lifted* ring
  `ULift Γ(W, 𝒪)` of the affine étale structure sheaf, while the comparison above tensors over
  the lift `ULift.{u} Γ(W, 𝒪)` that the Amitsur side forces; `Stacks.RingSquare.tensorMap`
  transports one tensor product to the other.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.comparisonCoefficients`: the coefficients, the restriction
  of the underlying abelian sheaf of `ℳ` along the comparison functor of [Stacks, Tag 03G1].
* `AlgebraicGeometry.Space.SmallEtale.chartSections` and
  `AlgebraicGeometry.Space.SmallEtale.moduleChartSections`: the sections of `ℳ` over a chart, as
  a module over the coordinate ring of the chart's scheme.
* `AlgebraicGeometry.Space.SmallEtale.baseChangeComparison`: **the comparison
  `a ⊗ x ↦ a • x|_V`** of the coefficients with the base-change presheaf, on the slice at an
  affine chart.
* `AlgebraicGeometry.Space.SmallEtale.affineEtaleModule`: `ℳ` read as a module on the affine
  étale site of `Y`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isQuasicoherentOnSite_affineEtaleModule`: the reading of
  `ℳ` on the affine étale site is quasi-coherent.
* `AlgebraicGeometry.Space.SmallEtale.isIso_baseChangeComparisonApp`: **the comparison is an
  isomorphism at an object of the slice whose chart is affine.**
* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_comparisonCoefficients`: **the Čech
  cohomology of the coefficients vanishes in positive degrees on a finite affine covering family
  of an affine chart.**
* `AlgebraicGeometry.Space.SmallEtale.subsingleton_sheafH_quasicoherent`: **the positive-degree
  cohomology of a quasi-coherent module on the spaces-étale site of an affine algebraic space
  vanishes.**
* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_comparisonCoefficients_forall`: the
  Čech vanishing packaged as 072C's Čech hypothesis, quantified over the algebraic space, the
  module, the chart and the family.

## Implementation notes

*Two spellings of one ring.*  `Γ(chartScheme V, ⊤)` and
`(AlgebraicGeometry.Space.structurePresheaf …).obj (op V)` are definitionally equal and
syntactically different, and instance search does not cross between them.  Every module
structure here is keyed on the first spelling, which is the one
`AlgebraicGeometry.baseChangeAbelianPresheaf` asks for, and the restriction maps are written as
`AlgebraicGeometry.Scheme.Hom.appTop` of `AlgebraicGeometry.Space.chartSchemeMap`, which is the
same spelling.  Rewriting through `AlgebraicGeometry.Space.SmallEtale.chartStructureRingHom`
breaks type-correctness at `implicit` transparency, so the two proofs that cross the boundary
are term-mode chains of `Eq.trans` rather than `rw`.

*`HasFiniteLimits (Over U)` is a `local instance`*, for the reason
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheafCohomologyVanishing` records: the small
étale site has no terminal object in general, so a global instance would oblige every consumer of
the site to a full library build.

*The auxiliary objects of the proof of
`AlgebraicGeometry.Space.SmallEtale.isIso_baseChangeComparisonApp` are introduced with `let` and
not with `set`.*  `set` abstracts occurrences in the goal and in the context, and the goal
mentions the transported module, whose type is a four-fold restriction; abstracting it costs more
than the heartbeat budget.

No `@[stacks]` attribute is claimed.  The conclusion is one clause of Descent, Lemma 03FJ and of
Cohomology on Sites, Lemma 03F9 read on the sites of [Stacks, Tag 03P2]; the tags are registered
elsewhere in this tree, on the statements the source makes.

## References

* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : AlgebraicSpaces B S hS)

/-- The slice of the small étale site at a chart has finite limits: the chart is a terminal
object of its own slice, and the site has pullbacks.  Local to this file, as the module
documentation explains. -/
local instance hasFiniteLimits_overChartOfSpace (U : SmallEtale B S hS Y.obj) :
    HasFiniteLimits (Over U) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

namespace SmallEtale

variable (M : SheafOfModules.{u + 1}
  (ringSheaf (spacesEtaleRingedSite B S hS Y).O))

/-! ### The coefficients and their module structure -/

/-- **The coefficients of the Čech hypothesis of [Stacks, Tag 072C]**: the underlying abelian
sheaf of `ℳ`, restricted along the comparison functor of [Stacks, Tag 03G1] to the small étale
site. -/
abbrev comparisonCoefficients : (SmallEtale B S hS Y.obj)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (comparisonFunctor B S hS Y).op ⋙
    ((SheafOfModules.toSheaf.{u + 1}
      (ringSheaf (spacesEtaleRingedSite B S hS Y).O)).obj M).obj

/-- The sections of `ℳ` over the algebraic space attached to an étale chart. -/
abbrev chartSections (V : SmallEtale B S hS Y.obj) : Type (u + 1) :=
  M.val.obj (op ((comparisonFunctor B S hS Y).obj V))

/-- The ring map making the sections of `ℳ` over a chart a module over the coordinate ring of
the chart's scheme: the inverse of the identification
`AlgebraicGeometry.Space.comparisonGlobalFunctionsRingEquiv` of that coordinate ring with the
global regular functions of the chart's algebraic space. -/
def chartStructureRingHom (V : SmallEtale B S hS Y.obj) :
    (Γ(chartScheme V, ⊤) : Type u) →+*
      ((ringSheaf (spacesEtaleRingedSite B S hS Y).O).obj.obj
        (op ((comparisonFunctor B S hS Y).obj V)) : Type (u + 1)) :=
  (comparisonGlobalFunctionsRingEquiv B S hS Y V).symm.toRingHom

/-- `chartStructureRingHom` sends `a` to its image under the inverse of the ring isomorphism
`comparisonGlobalFunctionsRingEquiv`. -/
theorem chartStructureRingHom_apply (V : SmallEtale B S hS Y.obj)
    (a : (Γ(chartScheme V, ⊤) : Type u)) :
    chartStructureRingHom B S hS Y V a =
      (comparisonGlobalFunctionsRingEquiv B S hS Y V).symm a := rfl

/-- **The sections of `ℳ` over a chart are a module over the coordinate ring of the chart's
scheme**, by restriction of scalars along
`AlgebraicGeometry.Space.SmallEtale.chartStructureRingHom`. -/
instance moduleChartSections (V : SmallEtale B S hS Y.obj) :
    Module (Γ(chartScheme V, ⊤) : Type u) (chartSections B S hS Y M V) :=
  Module.compHom _ (chartStructureRingHom B S hS Y V)

/-- A section of the coordinate ring acts on sections of `ℳ` over a chart through
`chartStructureRingHom`. -/
theorem chartSections_smul (V : SmallEtale B S hS Y.obj) (a : (Γ(chartScheme V, ⊤) : Type u))
    (x : chartSections B S hS Y M V) :
    a • x = chartStructureRingHom B S hS Y V a • x := rfl

/-- The same module structure, read at the values of the coefficient presheaf. -/
instance moduleComparisonCoefficients (V : SmallEtale B S hS Y.obj) :
    Module (Γ(chartScheme V, ⊤) : Type u)
      ((comparisonCoefficients B S hS Y M).obj (op V)) :=
  inferInstanceAs (Module (Γ(chartScheme V, ⊤) : Type u) (chartSections B S hS Y M V))

/-- Restriction of sections of `ℳ` along a morphism of étale charts. -/
def chartSectionsRestrict {V V' : SmallEtale B S hS Y.obj} (g : V' ⟶ V) :
    chartSections B S hS Y M V →+ chartSections B S hS Y M V' :=
  AddMonoidHom.mk' (fun m => (comparisonCoefficients B S hS Y M).map g.op m)
    (fun x y => map_add _ x y)

/-- `chartSectionsRestrict` along `g` is the restriction map of the coefficient presheaf at
`g`. -/
theorem chartSectionsRestrict_apply {V V' : SmallEtale B S hS Y.obj} (g : V' ⟶ V)
    (m : chartSections B S hS Y M V) :
    chartSectionsRestrict B S hS Y M g m =
      (comparisonCoefficients B S hS Y M).map g.op m := rfl

/-- Restriction along `g` followed by restriction along `h` is restriction along `h ≫ g`. -/
theorem chartSectionsRestrict_comp {V V' V'' : SmallEtale B S hS Y.obj} (g : V' ⟶ V)
    (h : V'' ⟶ V') (m : chartSections B S hS Y M V) :
    chartSectionsRestrict B S hS Y M h (chartSectionsRestrict B S hS Y M g m) =
      chartSectionsRestrict B S hS Y M (h ≫ g) m := by
  change ((comparisonCoefficients B S hS Y M).map g.op ≫
    (comparisonCoefficients B S hS Y M).map h.op) m = _
  rw [← (comparisonCoefficients B S hS Y M).map_comp, ← op_comp]
  rfl

/-! ### Naturality of the comparison of structure rings -/

/-- **Naturality of the identification of the global functions of a chart's algebraic space with
the coordinate ring of its scheme**: `AlgebraicGeometry.Space.comparisonStructureSheafIso` with
the universe lift of its values removed. -/
theorem comparisonGlobalFunctionsRingEquiv_naturality {V V' : SmallEtale B S hS Y.obj}
    (g : V' ⟶ V)
    (s : ((ringSheaf (spacesEtaleRingedSite B S hS Y).O).obj.obj
      (op ((comparisonFunctor B S hS Y).obj V)) : Type (u + 1))) :
    comparisonGlobalFunctionsRingEquiv B S hS Y V'
        (((ringSheaf (spacesEtaleRingedSite B S hS Y).O).obj.map
          ((comparisonFunctor B S hS Y).map g).op).hom s) =
      ((chartSchemeMap g).appTop).hom
        (comparisonGlobalFunctionsRingEquiv B S hS Y V s) :=
  ULift.up_injective (congrArg (fun φ => (CommRingCat.Hom.hom φ) s)
    ((comparisonStructureSheafIso B S hS Y).hom.naturality g.op))

/-- The change-of-scalars map of the coefficients is natural. -/
theorem chartStructureRingHom_naturality {V V' : SmallEtale B S hS Y.obj} (g : V' ⟶ V)
    (a : (Γ(chartScheme V, ⊤) : Type u)) :
    ((ringSheaf (spacesEtaleRingedSite B S hS Y).O).obj.map
        ((comparisonFunctor B S hS Y).map g).op).hom (chartStructureRingHom B S hS Y V a) =
      chartStructureRingHom B S hS Y V' (((chartSchemeMap g).appTop).hom a) := by
  apply (comparisonGlobalFunctionsRingEquiv B S hS Y V').injective
  rw [comparisonGlobalFunctionsRingEquiv_naturality, chartStructureRingHom_apply,
    chartStructureRingHom_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- **The restriction maps of the coefficients are semilinear** over pullback of regular
functions along the underlying morphism of schemes. -/
theorem chartSectionsRestrict_smul {V V' : SmallEtale B S hS Y.obj} (g : V' ⟶ V)
    (a : (Γ(chartScheme V, ⊤) : Type u)) (x : chartSections B S hS Y M V) :
    chartSectionsRestrict B S hS Y M g (a • x) =
      ((chartSchemeMap g).appTop).hom a • chartSectionsRestrict B S hS Y M g x := by
  have h1 : chartSectionsRestrict B S hS Y M g (a • x) =
      (M.val.map ((comparisonFunctor B S hS Y).map g).op).hom
        (chartStructureRingHom B S hS Y V a • x) := rfl
  have h2 := PresheafOfModules.map_smul M.val ((comparisonFunctor B S hS Y).map g).op
    (chartStructureRingHom B S hS Y V a) x
  rw [h1, h2, chartStructureRingHom_naturality B S hS Y g a]
  rfl

/-! ### `ℳ` read on the affine étale site -/

/-- The ring sheaf of the small étale site of `Y` at the universe of the charts. -/
abbrev liftedRingSheaf : Sheaf (SmallEtale.topology B S hS Y.obj) RingCat.{u + 1} :=
  (sheafCompose (SmallEtale.topology B S hS Y.obj)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (liftedStructureSheaf B S hS Y.obj).val

/-- The restriction along the comparison functor of the spaces-étale ring sheaf. -/
abbrev comparisonRingSheaf : Sheaf (SmallEtale.topology B S hS Y.obj) RingCat.{u + 1} :=
  ((comparisonFunctor B S hS Y).sheafPushforwardContinuous RingCat.{u + 1}
      (SmallEtale.topology B S hS Y.obj) (SpacesEtale.topology B S hS Y)).obj
    (ringSheaf (spacesEtaleRingedSite B S hS Y).O)

/-- **The comparison of the two sheaves of rings on the small étale site**, at the level of
sheaves: `AlgebraicGeometry.Space.comparisonStructureSheafIso` with the ring multiplication
forgotten. -/
def comparisonRingSheafHom : liftedRingSheaf B S hS Y ⟶ comparisonRingSheaf B S hS Y :=
  ObjectProperty.homMk (Functor.whiskerRight (comparisonStructureSheafIso B S hS Y).inv
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))

/-- The comparison `comparisonRingSheafHom` of the two sheaves of rings is an isomorphism. -/
instance isIso_comparisonRingSheafHom : IsIso (comparisonRingSheafHom B S hS Y) :=
  ⟨ObjectProperty.homMk (Functor.whiskerRight (comparisonStructureSheafIso B S hS Y).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})), by
    apply ObjectProperty.hom_ext
    change Functor.whiskerRight _ _ ≫ Functor.whiskerRight _ _ = _
    rw [← Functor.whiskerRight_comp, Iso.inv_hom_id]
    rfl, by
    apply ObjectProperty.hom_ext
    change Functor.whiskerRight _ _ ≫ Functor.whiskerRight _ _ = _
    rw [← Functor.whiskerRight_comp, Iso.hom_inv_id]
    rfl⟩

/-- **`ℳ` read as a module on the small étale site of `Y`**: restricted along the comparison
functor of [Stacks, Tag 03G1], then along the comparison of structure sheaves. -/
abbrev moduleToSmallEtale : SheafOfModules.{u + 1} (liftedRingSheaf B S hS Y) :=
  (SheafOfModules.pushforward.{u + 1} (comparisonRingSheafHom B S hS Y)).obj M

/-- **The reading of a quasi-coherent module on the small étale site is quasi-coherent.**  The
comparison functor is continuous, cocontinuous and a dense subsite inclusion on each slice, so
`Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv` applies — the two
sites have the same object universe and different morphism universes, which is what that
statement separates — and quasi-coherence survives the restriction of scalars along an
isomorphism of sheaves of rings. -/
theorem isQuasicoherentOnSite_moduleToSmallEtale (hM : M.IsQuasicoherentOnSite) :
    (moduleToSmallEtale B S hS Y M).IsQuasicoherentOnSite := by
  have _ : ∀ X : SmallEtale B S hS Y.obj,
      (Over.post (X := X) (comparisonFunctor B S hS Y)).IsContinuous
        ((SmallEtale.topology B S hS Y.obj).over X)
        ((SpacesEtale.topology B S hS Y).over
          ((comparisonFunctor B S hS Y).obj X)) := fun X => by
    have _ := comparisonFunctor_full B S hS Y
    have _ := comparisonFunctor_faithful B S hS Y
    have _ := Stacks.Sites.overPost_isDenseSubsite
      (J := SmallEtale.topology B S hS Y.obj) (K := SpacesEtale.topology B S hS Y)
      (comparisonFunctor B S hS Y) X
    infer_instance
  have _ : (comparisonFunctor B S hS Y).IsCocontinuous
      (SmallEtale.topology B S hS Y.obj) (SpacesEtale.topology B S hS Y) :=
    (comparisonFunctor_specialCocontinuous B S hS Y).1
  exact Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv.{
      u + 1, u + 1, u + 1, u, u + 1, u + 1}
    (comparisonFunctor B S hS Y) (comparisonRingSheafHom B S hS Y) inferInstance M hM

/-- The inclusion of the affine étale charts into all étale charts is a dense subsite
inclusion. -/
theorem affineEtale_inclusion_isDenseSubsite (hY : IsAlgebraicSpace B S hS Y.obj) :
    (AffineEtale.inclusion B S hS Y.obj).IsDenseSubsite
      (AffineEtale.topology B S hS Y.obj) (SmallEtale.topology B S hS Y.obj) :=
  (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.obj hY).2

/-- **`ℳ` read as a module on the affine étale site of `Y`** of [Stacks, Tag 0H01]. -/
def affineEtaleModule (hY : IsAlgebraicSpace B S hS Y.obj) :
    SheafOfModules.{u + 1} (affineEtaleRingSheaf B S hS Y.obj hY) := by
  have _ := affineEtale_inclusion_isDenseSubsite B S hS Y hY
  exact (SheafOfModules.pushforward.{u + 1} (F := AffineEtale.inclusion B S hS Y.obj)
    (R := liftedRingSheaf B S hS Y) (𝟙 _)).obj (moduleToSmallEtale B S hS Y M)

/-- **The reading of a quasi-coherent module on the affine étale site is quasi-coherent.** -/
theorem isQuasicoherentOnSite_affineEtaleModule (hY : IsAlgebraicSpace B S hS Y.obj)
    (hM : M.IsQuasicoherentOnSite) :
    (affineEtaleModule B S hS Y M hY).IsQuasicoherentOnSite := by
  have _ := affineEtale_inclusion_isDenseSubsite B S hS Y hY
  have _ : (AffineEtale.inclusion B S hS Y.obj).IsCocontinuous
      (AffineEtale.topology B S hS Y.obj) (SmallEtale.topology B S hS Y.obj) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.obj hY).1
  have _ : ∀ X : AffineEtale B S hS Y.obj,
      (Over.post (X := X) (AffineEtale.inclusion B S hS Y.obj)).IsContinuous
        ((AffineEtale.topology B S hS Y.obj).over X)
        ((SmallEtale.topology B S hS Y.obj).over
          ((AffineEtale.inclusion B S hS Y.obj).obj X)) := fun X => by
    have _ := Stacks.Sites.overPost_isDenseSubsite
      (J := AffineEtale.topology B S hS Y.obj) (K := SmallEtale.topology B S hS Y.obj)
      (AffineEtale.inclusion B S hS Y.obj) X
    infer_instance
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (J := SmallEtale.topology B S hS Y.obj) (K := AffineEtale.topology B S hS Y.obj)
    (AffineEtale.inclusion B S hS Y.obj) (liftedRingSheaf B S hS Y)
    (moduleToSmallEtale B S hS Y M) (isQuasicoherentOnSite_moduleToSmallEtale B S hS Y M hM)

/-- **[Stacks, Tag 0H04] for the reading of `ℳ` on the affine étale site**: its base-change
comparison along every morphism of affine étale charts is invertible. -/
theorem isIso_restrictionBaseChange_affineEtaleModule (hY : IsAlgebraicSpace B S hS Y.obj)
    (hM : M.IsQuasicoherentOnSite) {U V : AffineEtale B S hS Y.obj} (f : U ⟶ V) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
      (R := (affineEtaleStructureSheaf B S hS Y.obj hY).obj)
      (affineEtaleModule B S hS Y M hY).val f.op) :=
  isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u + 1} B S hS Y.obj hY
    (affineEtaleModule B S hS Y M hY)
    (isQuasicoherentOnSite_affineEtaleModule B S hS Y M hY hM) f

/-! ### The base-change comparison on the slice at an affine chart -/

section Slice

variable {W : SmallEtale B S hS Y.obj} [IsAffine (chartScheme W)]

/-- The module structure over the coordinate ring of the terminal object of the slice at `W`,
which is the spelling `AlgebraicGeometry.baseChangeAbelianPresheaf` asks for. -/
local instance moduleTerminalOverChartSections :
    Module (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u)
      (chartSections B S hS Y M W) :=
  inferInstanceAs (Module (Γ(chartScheme W, ⊤) : Type u) (chartSections B S hS Y M W))

/-- The coordinate algebra of an object of the slice at `W`, over the lifted coordinate ring of
the chart's scheme. -/
abbrev sliceAlg (Zo : (Over W)ᵒᵖ) : CommAlgCat.{u} (ULift.{u}
    (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u)) :=
  ((overAffineAlgΓBase (terminalOver (chartScheme W))).obj
    ((sliceToOver B S hS Y.obj W).obj Zo.unop)).unop

/-- The module structure on the sections, in the coordinate-algebra spelling. -/
instance moduleSliceAlgChartSections (Zo : (Over W)ᵒᵖ) :
    Module (sliceAlg (B := B) (S := S) (hS := hS) (Y := Y) Zo : Type u)
      (chartSections B S hS Y M Zo.unop.left) :=
  moduleChartSections B S hS Y M Zo.unop.left

/-- The bilinear data of the comparison: `(a, x) ↦ a • x|_V`. -/
def baseChangeBilin (Zo : (Over W)ᵒᵖ) :
    (sliceAlg (B := B) (S := S) (hS := hS) (Y := Y) Zo : Type u) →+
      (chartSections B S hS Y M W →+ chartSections B S hS Y M Zo.unop.left) where
  toFun a :=
    { toFun := fun m => a • chartSectionsRestrict B S hS Y M Zo.unop.hom m
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' := fun x y => by simp only [map_add, smul_add] }
  map_zero' := AddMonoidHom.ext fun m => zero_smul _ _
  map_add' a b := AddMonoidHom.ext fun m => add_smul _ _ _

/-- `baseChangeBilin` sends `(a, m)` to `a • m|_V`. -/
theorem baseChangeBilin_apply (Zo : (Over W)ᵒᵖ)
    (a : (sliceAlg (B := B) (S := S) (hS := hS) (Y := Y) Zo : Type u))
    (m : chartSections B S hS Y M W) :
    baseChangeBilin B S hS Y M Zo a m =
      a • chartSectionsRestrict B S hS Y M Zo.unop.hom m := rfl

/-- **The bilinear data is balanced over the base ring.**  The lifted coordinate ring of the
chart's scheme acts on the coordinate algebra of an object of the slice through pullback of
global sections along its structure morphism
(`AlgebraicGeometry.overAffineAlgΓBase_algebraMap`), and that is exactly the ring map the
restriction maps of the coefficients are semilinear over. -/
theorem baseChangeBilin_balanced (Zo : (Over W)ᵒᵖ)
    (c : ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
    (a : (sliceAlg (B := B) (S := S) (hS := hS) (Y := Y) Zo : Type u))
    (m : chartSections B S hS Y M W) :
    baseChangeBilin B S hS Y M Zo (c • a) m =
      baseChangeBilin B S hS Y M Zo a (c • m) := by
  have hc : chartSectionsRestrict B S hS Y M Zo.unop.hom (c • m) =
      algebraMap (ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
          (sliceAlg (B := B) (S := S) (hS := hS) (Y := Y) Zo) c •
        chartSectionsRestrict B S hS Y M Zo.unop.hom m := by
    refine Eq.trans (chartSectionsRestrict_smul B S hS Y M Zo.unop.hom c.down m) ?_
    exact congrArg (fun r => r • chartSectionsRestrict B S hS Y M Zo.unop.hom m)
      (overAffineAlgΓBase_algebraMap (terminalOver (chartScheme W))
        ((sliceToOver B S hS Y.obj W).obj Zo.unop) c).symm
  rw [baseChangeBilin_apply, baseChangeBilin_apply, hc, Algebra.smul_def, smul_smul, mul_comm]

/-- The component of the base-change comparison at an object of the slice. -/
def baseChangeComparisonApp (Zo : (Over W)ᵒᵖ) :
    ((sliceToOver B S hS Y.obj W).op ⋙
        baseChangeAbelianPresheaf (chartScheme W) (chartSections B S hS Y M W)).obj Zo ⟶
      ((Over.forget W).op ⋙ comparisonCoefficients B S hS Y M).obj Zo :=
  AddCommGrpCat.ofHom (TensorProduct.liftAddHom (baseChangeBilin B S hS Y M Zo)
    (baseChangeBilin_balanced B S hS Y M Zo))

/-- `baseChangeComparisonApp` sends `a ⊗ₜ m` to `a • m|_V`. -/
theorem baseChangeComparisonApp_tmul (Zo : (Over W)ᵒᵖ)
    (a : (sliceAlg (B := B) (S := S) (hS := hS) (Y := Y) Zo : Type u))
    (m : chartSections B S hS Y M W) :
    baseChangeComparisonApp B S hS Y M Zo (a ⊗ₜ m) =
      a • chartSectionsRestrict B S hS Y M Zo.unop.hom m := rfl

/-- **The base-change comparison of the coefficients on the slice at an affine chart**: the map
`a ⊗ x ↦ a • x|_V` from the base-change presheaf of the sections over `W` to the coefficients.

Naturality is semilinearity of the restriction maps together with their functoriality; the
comparison is given by the same formula at *every* object of the slice, and only its
invertibility needs the object to have affine chart. -/
def baseChangeComparison :
    (sliceToOver B S hS Y.obj W).op ⋙
        baseChangeAbelianPresheaf (chartScheme W) (chartSections B S hS Y M W) ⟶
      (Over.forget W).op ⋙ comparisonCoefficients B S hS Y M where
  app Zo := baseChangeComparisonApp B S hS Y M Zo
  naturality Zo Zo' g := by
    apply AddCommGrpCat.hom_ext
    refine Stacks.Sites.addHom_ext_tmul
      (Rr := ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
      (fun a m => ?_)
    change baseChangeComparisonApp B S hS Y M Zo'
        ((((chartSchemeMap g.unop.left).appTop).hom a) ⊗ₜ m) =
      chartSectionsRestrict B S hS Y M g.unop.left
        (baseChangeComparisonApp B S hS Y M Zo (a ⊗ₜ m))
    have hw : chartSectionsRestrict B S hS Y M g.unop.left
          (chartSectionsRestrict B S hS Y M Zo.unop.hom m) =
        chartSectionsRestrict B S hS Y M Zo'.unop.hom m :=
      (chartSectionsRestrict_comp B S hS Y M Zo.unop.hom g.unop.left m).trans
        (congrArg (fun h => chartSectionsRestrict B S hS Y M h m) (Over.w g.unop))
    refine (baseChangeComparisonApp_tmul B S hS Y M Zo' _ m).trans
      ((congrArg (fun z => (((chartSchemeMap g.unop.left).appTop).hom a) • z) hw.symm).trans
        (chartSectionsRestrict_smul B S hS Y M g.unop.left a
          (chartSectionsRestrict B S hS Y M Zo.unop.hom m)).symm)

/-- **The base-change comparison is an isomorphism at an object of the slice whose chart is
affine.**

This is cartesianness of `ℳ`, in the form
`AlgebraicGeometry.Space.SmallEtale.isIso_restrictionBaseChange_affineEtaleModule`.  The
comparison there tensors over the lifted ring `ULift Γ(W, 𝒪)` of the affine étale structure
sheaf, this one over the lift `ULift.{u} Γ(W, 𝒪)` that the Amitsur side forces;
`Stacks.RingSquare.tensorMap` transports the one tensor product to the other, bijectively, and
the two comparisons agree on the generators `a ⊗ x`. -/
theorem bijective_baseChangeComparisonApp (hY : IsAlgebraicSpace B S hS Y.obj)
    (hM : M.IsQuasicoherentOnSite) (Zo : (Over W)ᵒᵖ)
    (hZ : IsAffine (chartScheme Zo.unop.left)) :
    Function.Bijective (baseChangeComparisonApp B S hS Y M Zo).hom := by
  let Uaff : AffineEtale B S hS Y.obj := ⟨Zo.unop.left, hZ⟩
  let Vaff : AffineEtale B S hS Y.obj := ⟨W, ‹IsAffine (chartScheme W)›⟩
  let f : Uaff ⟶ Vaff := ObjectProperty.homMk Zo.unop.hom
  let N := affineEtaleModule B S hS Y M hY
  have hbij : Function.Bijective
      (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
        (R := (affineEtaleStructureSheaf B S hS Y.obj hY).obj) N.val f.op) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      (isIso_restrictionBaseChange_affineEtaleModule B S hS Y M hY hM f)
  let algVU : Algebra
      ((affineEtaleStructureSheaf B S hS Y.obj hY).obj.obj (op Vaff) : Type (u + 1))
      ((affineEtaleStructureSheaf B S hS Y.obj hY).obj.obj (op Uaff) : Type (u + 1)) :=
    (((affineEtaleStructureSheaf B S hS Y.obj hY).obj.map f.op).hom).toAlgebra
  let modVP : Module
      ((affineEtaleStructureSheaf B S hS Y.obj hY).obj.obj (op Vaff) : Type (u + 1))
      (chartSections B S hS Y M W) :=
    (N.val.obj (op Vaff)).isModule
  let eW : ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u) ≃+*
      ((affineEtaleStructureSheaf B S hS Y.obj hY).obj.obj (op Vaff) : Type (u + 1)) :=
    ULift.ringEquiv.trans ULift.ringEquiv.symm
  let eZ : (sliceAlg (B := B) (S := S) (hS := hS) (Y := Y) Zo : Type u) ≃+*
      ((affineEtaleStructureSheaf B S hS Y.obj hY).obj.obj (op Uaff) : Type (u + 1)) :=
    ULift.ringEquiv.symm
  let b := (((affineEtaleStructureSheaf B S hS Y.obj hY).obj.map f.op).hom)
  let a := algebraMap (ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
    (sliceAlg (B := B) (S := S) (hS := hS) (Y := Y) Zo)
  have hsq : ∀ t, eZ (a t) = b (eW t) := fun t =>
    congrArg ULift.up (overAffineAlgΓBase_algebraMap (terminalOver (chartScheme W))
      ((sliceToOver B S hS Y.obj W).obj Zo.unop) t)
  have hA : ∀ (t : ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
      (c : (sliceAlg (B := B) (S := S) (hS := hS) (Y := Y) Zo : Type u)),
      t • c = a t * c := fun t c => Algebra.smul_def t c
  have hB : ∀ (s : ((affineEtaleStructureSheaf B S hS Y.obj hY).obj.obj (op Vaff) : Type (u + 1)))
      (d : ((affineEtaleStructureSheaf B S hS Y.obj hY).obj.obj (op Uaff) : Type (u + 1))),
      s • d = b s * d := fun s d => rfl
  have hP : ∀ (t : ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
      (x : chartSections B S hS Y M W), t • x = eW t • x := fun t x => rfl
  let T := Stacks.RingSquare.tensorMap a b eW eZ hsq hA hB hP
  let rbc := Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
    (R := (affineEtaleStructureSheaf B S hS Y.obj hY).obj) N.val f.op
  have key : (baseChangeComparisonApp B S hS Y M Zo).hom = rbc.hom.toAddMonoidHom.comp T := by
    refine Stacks.Sites.addHom_ext_tmul
      (Rr := ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
      (fun c m => ?_)
    exact (baseChangeComparisonApp_tmul B S hS Y M Zo c m).trans
      (Stacks.PresheafOfModules.restrictionBaseChange_tmul.{u + 1, u, u + 1, u + 1}
        (R := (affineEtaleStructureSheaf B S hS Y.obj hY).obj) N.val f.op (eZ c) m).symm
  rw [key]
  exact hbij.comp (Stacks.RingSquare.bijective_tensorMap a b eW eZ hsq hA hB hP)

/-- **The base-change comparison is an isomorphism at an object of the slice whose chart is
affine.** -/
theorem isIso_baseChangeComparisonApp (hY : IsAlgebraicSpace B S hS Y.obj)
    (hM : M.IsQuasicoherentOnSite) (Zo : (Over W)ᵒᵖ)
    (hZ : IsAffine (chartScheme Zo.unop.left)) :
    IsIso (baseChangeComparisonApp B S hS Y M Zo) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_baseChangeComparisonApp B S hS Y M hY hM Zo hZ)

end Slice

/-! ### The Čech vanishing -/

/-- **The Čech cohomology of the coefficients of [Stacks, Tag 072C] vanishes in positive degrees
on a finite affine covering family of an affine chart.**

This is
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_of_isoAtFibreProducts_baseChange` with
its coefficient comparison supplied by
`AlgebraicGeometry.Space.SmallEtale.baseChangeComparison` and its invertibility at the iterated
fibre products by `AlgebraicGeometry.Space.SmallEtale.isIso_baseChangeComparisonApp`, those
fibre products being affine charts again
(`AlgebraicGeometry.Space.SmallEtale.isAffine_chartScheme_piObj`). -/
theorem isZero_cechCohomology_comparisonCoefficients (hM : M.IsQuasicoherentOnSite)
    {W : SmallEtale B S hS Y.obj} (hW : IsAffine (chartScheme W))
    (E : PreZeroHypercover.{u + 1} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS Y.obj W)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E (comparisonCoefficients B S hS Y M) p) :=
  isZero_cechCohomology_of_isoAtFibreProducts_baseChange E hfin haff hcov
    (chartSections B S hS Y M W) (comparisonCoefficients B S hS Y M)
    (baseChangeComparison B S hS Y M)
    (fun n i => isIso_baseChangeComparisonApp B S hS Y M Y.property hM _
      (isAffine_chartScheme_piObj B S hS Y.obj hW E haff n i))
    p hp

/-- **The positive-degree cohomology of a quasi-coherent module on the spaces-étale site of an
affine algebraic space vanishes.**

This is the Čech-to-derived criterion
`AlgebraicGeometry.Space.subsingleton_sheafH_spacesEtale_of_isZero_cechCohomology` with its one
hypothesis discharged by
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_comparisonCoefficients`.  It is the
input of the alternating Čech recursion of [Stacks, Tag 072C] which the recursion cannot
supply. -/
theorem subsingleton_sheafH_quasicoherent (hYa : IsAffineSpace B S hS Y.obj)
    (hM : M.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((SheafOfModules.toSheaf.{u + 1}
        (ringSheaf (spacesEtaleRingedSite B S hS Y).O)).obj M) q) :=
  subsingleton_sheafH_spacesEtale_of_isZero_cechCohomology hYa
    ((SheafOfModules.toSheaf.{u + 1}
      (ringSheaf (spacesEtaleRingedSite B S hS Y).O)).obj M)
    (fun hW E hfin haff hcov p hp =>
      isZero_cechCohomology_comparisonCoefficients B S hS Y M hM hW E hfin haff hcov p hp)
    q hq

/-- **072C's Čech hypothesis.**  The Čech vanishing of the previous theorem, packaged in the
shape in which the reduction of the affine Serre vanishing to a Čech vanishing consumes it: for
every affine algebraic space, every quasi-coherent module on its ringed spaces-étale site, every
affine chart and every finite covering family of that chart by affine charts.

The affineness hypothesis on the algebraic space is not used — the vanishing holds on the
covering families of an affine chart of *any* algebraic space — and is carried only so that the
statement is the one the reduction asks for. -/
theorem isZero_cechCohomology_comparisonCoefficients_forall :
    ∀ (Z : AlgebraicSpaces B S hS), IsAffineSpace B S hS Z.obj →
      ∀ N : SheafOfModules.{u + 1}
          (ringSheaf (spacesEtaleRingedSite B S hS Z).O),
        N.IsQuasicoherentOnSite →
        ∀ {V : SmallEtale B S hS Z.obj}, IsAffine (chartScheme V) →
          ∀ E : PreZeroHypercover.{u + 1} V, Finite E.I₀ →
            (∀ i, IsAffine (chartScheme (E.X i))) →
            E.sieve₀ ∈ SmallEtale.topology B S hS Z.obj V →
            ∀ p : ℕ, 0 < p →
              IsZero (Stacks.CechSite.cechCohomology E
                ((comparisonFunctor B S hS Z).op ⋙
                  ((SheafOfModules.toSheaf.{u + 1}
                    (ringSheaf
                      (spacesEtaleRingedSite B S hS Z).O)).obj N).obj) p) :=
  fun Z _ N hN _ hV E hfin haff hcov p hp =>
    isZero_cechCohomology_comparisonCoefficients B S hS Z N hN hV E hfin haff hcov p hp

end SmallEtale

end AlgebraicGeometry.Space

end
