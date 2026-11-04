module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiToBig
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology

/-!
# Cohomology on the big and the small Zariski site agree

For an abelian sheaf on the big Zariski site of a scheme `S`, the cohomology over `S` agrees with
the cohomology of its restriction to the small Zariski site of `S`, naturally in the sheaf.

## Main definitions

* `AlgebraicGeometry.bigSmallZariskiCohomologyIso` is the comparison of the two cohomology
  groups.

## Main results

* `AlgebraicGeometry.smallZariskiInclusion_isCocontinuous`: the inclusion of the small Zariski
  site of `S` in its big Zariski site is cocontinuous.
* `AlgebraicGeometry.smallZariskiSheaf_isGrothendieckAbelian` and
  `AlgebraicGeometry.bigZariskiSheaf_isGrothendieckAbelian`: abelian sheaves on the two Zariski
  sites of `S` form Grothendieck abelian categories, the sites being essentially small.
* `AlgebraicGeometry.bigSmallZariskiCohomologyIso_naturality`: the comparison commutes with
  morphisms of abelian sheaves.

## Implementation notes

Cohomology is Mathlib's `Ext`-based `CategoryTheory.Sheaf.H`, whose `Ext` universe is independent
of the site; the two Zariski sites of `S` have their objects and their morphisms in different
universes, so a cohomology theory tied to the morphism universe would not serve. Restriction is
the sheaf pushforward along the full inclusion of the small site in the big one.

Both statements are `Stacks.Cohomology.BiggerSite.sheafHAddEquiv` — Stacks 03YU, statement 1 — at
the small-site inclusion, and the work here is to supply its hypotheses: the inclusion is
continuous and cocontinuous (Stacks 020Z, 020Y), the small Zariski site has `S / S` as a final
object (Stacks 020V) and the inclusion carries it to the final object of the slice, and the small
site has fibre products and equalizers which the inclusion preserves (Stacks 020V), so that lower
shriek on abelian sheaves is exact and restriction therefore preserves injectives.

Those inputs are introduced as local instances inside each proof rather than as instances of the
module: the two Zariski sites of an object `S` of a big Zariski site are indexed by the two
projections of `S`, and an instance in that shape is not found by instance search.

## References

* [Stacks Project, Tag 03YX](https://stacks.math.columbia.edu/tag/03YX)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : B.Schemes)

/-- **The inclusion of the small Zariski site of `S` in its big Zariski site is cocontinuous.**
It is the functor of Stacks 020Y for the identity morphism of `S`. -/
public theorem smallZariskiInclusion_isCocontinuous :
    (SmallZariski.inclusion B S.obj S.property).IsCocontinuous
      (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property) := by
  have e : smallZariskiToBigZariskiFunctor B S S (𝟙 S) =
      SmallZariski.inclusion B S.obj S.property := by
    dsimp [smallZariskiToBigZariskiFunctor]
    rw [Over.mapId_eq]
    rfl
  exact e ▸ smallZariskiToBigZariskiFunctor_isCocontinuous B S S (𝟙 S)

/-- Abelian sheaves on an essentially small site form a Grothendieck abelian category. -/
private theorem isGrothendieckAbelian_sheaf_of_essentiallySmall {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{u + 1}] :
    IsGrothendieckAbelian.{u + 1, u + 1, u + 2} (Sheaf J Ab.{u + 1}) := by
  let e := equivSmallModel.{u + 1} C
  let K := e.inverse.inducedTopology J
  have : HasSheafify K Ab.{u + 1} :=
    Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J K e.functor
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2} Ab.{u + 1} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall J Ab.{u + 1}

/-- **Abelian sheaves on the small Zariski site of `S` form a Grothendieck abelian category.**
The site is essentially small. -/
public lemma smallZariskiSheaf_isGrothendieckAbelian
    [HasSheafify (SmallZariski.topology B S.obj S.property) Ab.{u + 1}] :
    IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (SmallZariski.topology B S.obj S.property) Ab.{u + 1}) :=
  isGrothendieckAbelian_sheaf_of_essentiallySmall _

/-- **Abelian sheaves on the big Zariski site of `S` form a Grothendieck abelian category.**
The site is essentially small. -/
public lemma bigZariskiSheaf_isGrothendieckAbelian
    [HasSheafify (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}] :
    IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}) :=
  isGrothendieckAbelian_sheaf_of_essentiallySmall _

/-- `Ext`-groups of abelian sheaves on the small Zariski site of `S` live in the morphism
universe of that sheaf category. -/
public lemma smallZariskiSheaf_hasExt
    [HasSheafify (SmallZariski.topology B S.obj S.property) Ab.{u + 1}] :
    HasExt.{u + 1} (Sheaf (SmallZariski.topology B S.obj S.property) Ab.{u + 1}) := by
  let := smallZariskiSheaf_isGrothendieckAbelian B S
  exact IsGrothendieckAbelian.hasExt _

/-- `Ext`-groups of abelian sheaves on the big Zariski site of `S` live in the morphism universe
of that sheaf category. -/
public lemma bigZariskiSheaf_hasExt
    [HasSheafify (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}] :
    HasExt.{u + 1} (Sheaf (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}) := by
  let := bigZariskiSheaf_isGrothendieckAbelian B S
  exact IsGrothendieckAbelian.hasExt _

/-- Abelian sheaves on the small Zariski site of `S` have injective resolutions. -/
public lemma smallZariskiSheaf_hasInjectiveResolutions
    [HasSheafify (SmallZariski.topology B S.obj S.property) Ab.{u + 1}] :
    HasInjectiveResolutions (Sheaf (SmallZariski.topology B S.obj S.property) Ab.{u + 1}) := by
  let := smallZariskiSheaf_isGrothendieckAbelian B S
  infer_instance

/-- Abelian sheaves on the big Zariski site of `S` have injective resolutions. -/
public lemma bigZariskiSheaf_hasInjectiveResolutions
    [HasSheafify (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}] :
    HasInjectiveResolutions (Sheaf (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}) := by
  let := bigZariskiSheaf_isGrothendieckAbelian B S
  infer_instance

/-- Abelian presheaves on the small Zariski site of `S` have pointwise left Kan extensions along
the small-site inclusion. -/
public lemma smallZariskiInclusion_hasPointwiseLeftKanExtension :
    ∀ P : (SmallZariski B S.obj S.property)ᵒᵖ ⥤ Ab.{u + 1},
      (SmallZariski.inclusion B S.obj S.property).op.HasPointwiseLeftKanExtension P :=
  fun _ => inferInstance

/-- **Restriction from the big to the small Zariski site of `S` is right exact.** The inclusion is
cocontinuous, so restriction is itself a left adjoint. -/
public lemma smallZariskiRestriction_preservesFiniteColimits
    [HasSheafify (SmallZariski.topology B S.obj S.property) Ab.{u + 1}] :
    PreservesFiniteColimits
      ((SmallZariski.inclusion B S.obj S.property).sheafPushforwardContinuous
        Ab.{u + 1} (SmallZariski.topology B S.obj S.property)
        (BigZariskiOver.topology B S.obj S.property)) := by
  let := smallZariskiInclusion_isCocontinuous B S
  let : ∀ P : (SmallZariski B S.obj S.property)ᵒᵖ ⥤ Ab.{u + 1},
      (SmallZariski.inclusion B S.obj S.property).op.HasPointwiseRightKanExtension P :=
    fun _ => inferInstance
  exact Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous
    (SmallZariski.topology B S.obj S.property)
    (BigZariskiOver.topology B S.obj S.property)
    (SmallZariski.inclusion B S.obj S.property) Ab.{u + 1}

/-- **Restriction from the big to the small Zariski site of `S` preserves injective abelian
sheaves.** Lower shriek along the inclusion is exact, the small site having fibre products and
equalizers which the inclusion preserves. -/
public lemma smallZariskiRestriction_preservesInjectiveObjects
    [HasSheafify (SmallZariski.topology B S.obj S.property) Ab.{u + 1}]
    [HasSheafify (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}] :
    ((SmallZariski.inclusion B S.obj S.property).sheafPushforwardContinuous
        Ab.{u + 1} (SmallZariski.topology B S.obj S.property)
        (BigZariskiOver.topology B S.obj S.property)).PreservesInjectiveObjects := by
  let : HasBinaryProducts (SmallZariski B S.obj S.property) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : HasEqualizers (SmallZariski B S.obj S.property) :=
    hasEqualizers_of_hasPullbacks_and_binary_products
  let : HasBinaryProducts (BigZariskiOver B S.obj S.property) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let : PreservesLimitsOfShape (Discrete WalkingPair)
      (SmallZariski.inclusion B S.obj S.property) :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks _
  let : PreservesLimitsOfShape WalkingParallelPair
      (SmallZariski.inclusion B S.obj S.property) :=
    preservesEqualizers_of_preservesPullbacks_and_binaryProducts _
  let := smallZariskiInclusion_hasPointwiseLeftKanExtension B S
  exact Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous
    (SmallZariski.topology B S.obj S.property)
    (BigZariskiOver.topology B S.obj S.property)
    (SmallZariski.inclusion B S.obj S.property)

/-- **Stacks 03YX, Zariski case.** Big Zariski cohomology over `S` agrees, naturally in the
abelian sheaf, with the cohomology of its restriction to the small Zariski site. -/
@[stacks 03YX "Zariski case"]
public noncomputable def bigSmallZariskiCohomologyIso
    (F : Sheaf (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1})
    [HasSheafify (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}]
    [HasSheafify (SmallZariski.topology B S.obj S.property) Ab.{u + 1}]
    [HasExt.{w} (Sheaf (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1})]
    [HasExt.{w} (Sheaf (SmallZariski.topology B S.obj S.property) Ab.{u + 1})]
    (p : ℕ) :
    Sheaf.H.{w, u + 1} F p ≃+
      (((SmallZariski.inclusion B S.obj S.property).sheafPushforwardContinuous
          Ab.{u + 1} (SmallZariski.topology B S.obj S.property)
          (BigZariskiOver.topology B S.obj S.property)).obj F).H p :=
  Stacks.Cohomology.BiggerSite.sheafHAddEquiv.{w, u + 1}
    (extJ := smallZariskiSheaf_hasExt B S) (extK := bigZariskiSheaf_hasExt B S)
    (injJ := smallZariskiSheaf_hasInjectiveResolutions B S)
    (injK := bigZariskiSheaf_hasInjectiveResolutions B S)
    (lanG := smallZariskiInclusion_hasPointwiseLeftKanExtension B S)
    (rexG := smallZariskiRestriction_preservesFiniteColimits B S)
    (injG := smallZariskiRestriction_preservesInjectiveObjects B S)
    (SmallZariski.topology B S.obj S.property)
    (BigZariskiOver.topology B S.obj S.property)
    (SmallZariski.inclusion B S.obj S.property)
    (SmallZariski.finalIsTerminal B S.obj S.property)
    ((SmallZariski.finalIsTerminal B S.obj S.property).isTerminalObj
      (SmallZariski.inclusion B S.obj S.property) (SmallZariski.final B S.obj S.property))
    rfl F p

/-- **`bigSmallZariskiCohomologyIso` is the comparison of Stacks 03YU at the small-site
inclusion.** This records the definition, so that general facts about
`Stacks.Cohomology.BiggerSite.sheafHAddEquiv` can be transported to the Zariski comparison
without unfolding it. -/
public lemma bigSmallZariskiCohomologyIso_eq
    (F : Sheaf (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1})
    [HasSheafify (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}]
    [HasSheafify (SmallZariski.topology B S.obj S.property) Ab.{u + 1}]
    [HasExt.{w} (Sheaf (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1})]
    [HasExt.{w} (Sheaf (SmallZariski.topology B S.obj S.property) Ab.{u + 1})]
    (p : ℕ) :
    bigSmallZariskiCohomologyIso B S F p =
      Stacks.Cohomology.BiggerSite.sheafHAddEquiv.{w, u + 1}
    (extJ := smallZariskiSheaf_hasExt B S) (extK := bigZariskiSheaf_hasExt B S)
    (injJ := smallZariskiSheaf_hasInjectiveResolutions B S)
    (injK := bigZariskiSheaf_hasInjectiveResolutions B S)
    (lanG := smallZariskiInclusion_hasPointwiseLeftKanExtension B S)
    (rexG := smallZariskiRestriction_preservesFiniteColimits B S)
    (injG := smallZariskiRestriction_preservesInjectiveObjects B S)
    (SmallZariski.topology B S.obj S.property)
    (BigZariskiOver.topology B S.obj S.property)
    (SmallZariski.inclusion B S.obj S.property)
    (SmallZariski.finalIsTerminal B S.obj S.property)
    ((SmallZariski.finalIsTerminal B S.obj S.property).isTerminalObj
      (SmallZariski.inclusion B S.obj S.property) (SmallZariski.final B S.obj S.property))
    rfl F p :=
  rfl

/-- **Stacks 03YX, Zariski naturality.** The Zariski comparison commutes with morphisms of
abelian sheaves. -/
@[stacks 03YX "Zariski naturality"]
public theorem bigSmallZariskiCohomologyIso_naturality
    [HasSheafify (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}]
    [HasSheafify (SmallZariski.topology B S.obj S.property) Ab.{u + 1}]
    [HasExt.{w} (Sheaf (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1})]
    [HasExt.{w} (Sheaf (SmallZariski.topology B S.obj S.property) Ab.{u + 1})]
    {F G : Sheaf (BigZariskiOver.topology B S.obj S.property) Ab.{u + 1}}
    (f : F ⟶ G) (p : ℕ) (x : Sheaf.H.{w, u + 1} F p) :
    bigSmallZariskiCohomologyIso B S G p (Sheaf.H.map f p x) =
      Sheaf.H.map
        (((SmallZariski.inclusion B S.obj S.property).sheafPushforwardContinuous
          Ab.{u + 1} (SmallZariski.topology B S.obj S.property)
          (BigZariskiOver.topology B S.obj S.property)).map f) p
        (bigSmallZariskiCohomologyIso B S F p x) := by
  simp only [bigSmallZariskiCohomologyIso_eq]
  exact Stacks.Cohomology.BiggerSite.sheafHAddEquiv_naturality.{w, u + 1}
    (extJ := smallZariskiSheaf_hasExt B S) (extK := bigZariskiSheaf_hasExt B S)
    (injJ := smallZariskiSheaf_hasInjectiveResolutions B S)
    (injK := bigZariskiSheaf_hasInjectiveResolutions B S)
    (lanG := smallZariskiInclusion_hasPointwiseLeftKanExtension B S)
    (rexG := smallZariskiRestriction_preservesFiniteColimits B S)
    (injG := smallZariskiRestriction_preservesInjectiveObjects B S) _ _ _ _ _ rfl f p x

end AlgebraicGeometry

end
