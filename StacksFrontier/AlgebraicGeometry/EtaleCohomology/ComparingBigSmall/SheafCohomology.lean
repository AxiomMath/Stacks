module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.Cohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology

/-!
# `Ext`-based cohomology on the big and the small étale site agree

For an abelian sheaf on the big étale site of a scheme `S`, the cohomology over `S` agrees with
the cohomology of its restriction to the small étale site of `S`, naturally in the sheaf.

## Main definitions

* `AlgebraicGeometry.bigSmallEtaleSheafCohomologyIso` is the comparison of the two cohomology
  groups.

## Main results

* `AlgebraicGeometry.smallEtaleInclusion_isCocontinuous`: the inclusion of the small étale site
  of `S` in its big étale site is cocontinuous.
* `AlgebraicGeometry.smallEtaleRestriction_preservesFiniteColimits'` and
  `AlgebraicGeometry.smallEtaleRestriction_preservesInjectiveObjects`: restriction is right exact
  and preserves injective abelian sheaves.  The primed name is the variant of
  `AlgebraicGeometry.smallEtaleRestriction_preservesFiniteColimits` of
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.DerivedRestriction` which
  asks for sheafification on the *small* site rather than on the big one; neither hypothesis
  implies the other, so both statements are kept.
* `AlgebraicGeometry.bigSmallEtaleSheafCohomologyIso_naturality`: the comparison commutes with
  morphisms of abelian sheaves.

## Implementation notes

Cohomology is Mathlib's `Ext`-based `CategoryTheory.Sheaf.H`, whose `Ext` universe is independent
of the site; the two étale sites of `S` have their objects and their morphisms in different
universes, so a cohomology theory tied to the morphism universe would not serve. Restriction is
the sheaf pushforward along the full inclusion of the small site in the big one.

This is the `Ext`-based counterpart of
`AlgebraicGeometry.bigSmallEtaleCohomologyIso`, which compares the two *derived sections*
functors on unbounded derived categories; the two statements are independent, and neither is
obtained from the other.

Both statements here are `Stacks.Cohomology.BiggerSite.sheafHAddEquiv` — Stacks 03YU, statement 1
— at the small-site inclusion, and the work is to supply its hypotheses: the inclusion is
continuous and cocontinuous (Stacks 021G, 021E), the small étale site has `S / S` as a final
object (Stacks 021D) and the inclusion carries it to the final object of the slice, and
restriction preserves injective abelian sheaves (Stacks 0758,
`AlgebraicGeometry.injective_smallEtaleRestriction`).

## References

* [Stacks Project, Tag 03YX](https://stacks.math.columbia.edu/tag/03YX)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inclusion of the small étale site of `S` in its big étale site is cocontinuous.**
It is the functor of Stacks 021E for the identity morphism of `S`. -/
public theorem smallEtaleInclusion_isCocontinuous :
    (SmallEtale.inclusion B S hS).IsCocontinuous
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) := by
  have e : smallEtaleToBigEtaleFunctor B (B.obj S hS) (B.obj S hS) (𝟙 (B.obj S hS)) =
      SmallEtale.inclusion B S hS := by
    dsimp [smallEtaleToBigEtaleFunctor]
    rw [Over.mapId_eq]
    rfl
  exact e ▸ smallEtaleToBigEtaleFunctor_isCocontinuous B (B.obj S hS) (B.obj S hS)
    (𝟙 (B.obj S hS))

/-- `Ext`-groups of abelian sheaves on the small étale site of `S` live in the morphism universe
of that sheaf category. -/
public lemma smallEtaleSheaf_hasExt
    [HasSheafify (SmallEtale.topology B S hS) Ab.{u + 1}] :
    HasExt.{u + 1} (Sheaf (SmallEtale.topology B S hS) Ab.{u + 1}) := by
  let := smallEtaleSheaf_isGrothendieckAbelian B (B.obj S hS)
  exact IsGrothendieckAbelian.hasExt _

/-- `Ext`-groups of abelian sheaves on the big étale site of `S` live in the morphism universe of
that sheaf category. -/
public lemma bigEtaleSheaf_hasExt
    [HasSheafify (BigEtaleOver.topology B S hS) Ab.{u + 1}] :
    HasExt.{u + 1} (Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1}) := by
  let := bigEtaleSheaf_isGrothendieckAbelian B (B.obj S hS)
  exact IsGrothendieckAbelian.hasExt _

/-- Abelian sheaves on the small étale site of `S` have injective resolutions. -/
public lemma smallEtaleSheaf_hasInjectiveResolutions
    [HasSheafify (SmallEtale.topology B S hS) Ab.{u + 1}] :
    HasInjectiveResolutions (Sheaf (SmallEtale.topology B S hS) Ab.{u + 1}) := by
  let := smallEtaleSheaf_isGrothendieckAbelian B (B.obj S hS)
  infer_instance

/-- Abelian sheaves on the big étale site of `S` have injective resolutions. -/
public lemma bigEtaleSheaf_hasInjectiveResolutions
    [HasSheafify (BigEtaleOver.topology B S hS) Ab.{u + 1}] :
    HasInjectiveResolutions (Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1}) := by
  let := bigEtaleSheaf_isGrothendieckAbelian B (B.obj S hS)
  infer_instance

/-- Abelian presheaves on the small étale site of `S` have pointwise left Kan extensions along
the small-site inclusion. -/
public lemma smallEtaleInclusion_hasPointwiseLeftKanExtension :
    ∀ P : (SmallEtale B S hS)ᵒᵖ ⥤ Ab.{u + 1},
      (SmallEtale.inclusion B S hS).op.HasPointwiseLeftKanExtension P :=
  fun _ => inferInstance

/-- **Restriction from the big to the small étale site of `S` is right exact.** The inclusion is
cocontinuous, so restriction is itself a left adjoint.

This asks for sheafification on the small site, which is what the route through
`Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous` consumes;
`AlgebraicGeometry.smallEtaleRestriction_preservesFiniteColimits` is the same conclusion from
sheafification on the big site instead. -/
public lemma smallEtaleRestriction_preservesFiniteColimits'
    [HasSheafify (SmallEtale.topology B S hS) Ab.{u + 1}] :
    PreservesFiniteColimits
      ((SmallEtale.inclusion B S hS).sheafPushforwardContinuous
        Ab.{u + 1} (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)) := by
  let := smallEtaleInclusion_isCocontinuous B S hS
  let : ∀ P : (SmallEtale B S hS)ᵒᵖ ⥤ Ab.{u + 1},
      (SmallEtale.inclusion B S hS).op.HasPointwiseRightKanExtension P :=
    fun _ => inferInstance
  exact Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous
    (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
    (SmallEtale.inclusion B S hS) Ab.{u + 1}

/-- **Restriction from the big to the small étale site of `S` preserves injective abelian
sheaves.** This is Stacks 0758, `AlgebraicGeometry.injective_smallEtaleRestriction`, read as a
property of the restriction functor. -/
public lemma smallEtaleRestriction_preservesInjectiveObjects :
    ((SmallEtale.inclusion B S hS).sheafPushforwardContinuous
        Ab.{u + 1} (SmallEtale.topology B S hS)
        (BigEtaleOver.topology B S hS)).PreservesInjectiveObjects :=
  ⟨fun {I} h => @injective_smallEtaleRestriction B S hS I h⟩

/-- **Stacks 03YX, étale case.** Big étale cohomology over `S` agrees, naturally in the abelian
sheaf, with the cohomology of its restriction to the small étale site. -/
@[stacks 03YX "étale case",
  stacks 03PJ "big-site cohomology over S agrees with that of the restriction to S_etale"]
public noncomputable def bigSmallEtaleSheafCohomologyIso
    (F : Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1})
    [HasSheafify (BigEtaleOver.topology B S hS) Ab.{u + 1}]
    [HasSheafify (SmallEtale.topology B S hS) Ab.{u + 1}]
    [HasExt.{w} (Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) Ab.{u + 1})]
    (p : ℕ) :
    Sheaf.H.{w, u + 1} F p ≃+
      (((SmallEtale.inclusion B S hS).sheafPushforwardContinuous
          Ab.{u + 1} (SmallEtale.topology B S hS)
          (BigEtaleOver.topology B S hS)).obj F).H p :=
  Stacks.Cohomology.BiggerSite.sheafHAddEquiv.{w, u + 1}
    (extJ := smallEtaleSheaf_hasExt B S hS) (extK := bigEtaleSheaf_hasExt B S hS)
    (injJ := smallEtaleSheaf_hasInjectiveResolutions B S hS)
    (injK := bigEtaleSheaf_hasInjectiveResolutions B S hS)
    (lanG := smallEtaleInclusion_hasPointwiseLeftKanExtension B S hS)
    (rexG := smallEtaleRestriction_preservesFiniteColimits' B S hS)
    (injG := smallEtaleRestriction_preservesInjectiveObjects B S hS)
    (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
    (SmallEtale.inclusion B S hS) (SmallEtale.finalIsTerminal B S hS)
    ((SmallEtale.finalIsTerminal B S hS).isTerminalObj
      (SmallEtale.inclusion B S hS) (SmallEtale.final B S hS))
    rfl F p

/-- **`bigSmallEtaleSheafCohomologyIso` is the comparison of Stacks 03YU at the small-site
inclusion.** This records the definition, so that general facts about
`Stacks.Cohomology.BiggerSite.sheafHAddEquiv` can be transported to the étale comparison without
unfolding it. -/
public lemma bigSmallEtaleSheafCohomologyIso_eq
    (F : Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1})
    [HasSheafify (BigEtaleOver.topology B S hS) Ab.{u + 1}]
    [HasSheafify (SmallEtale.topology B S hS) Ab.{u + 1}]
    [HasExt.{w} (Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) Ab.{u + 1})]
    (p : ℕ) :
    bigSmallEtaleSheafCohomologyIso B S hS F p =
      Stacks.Cohomology.BiggerSite.sheafHAddEquiv.{w, u + 1}
        (extJ := smallEtaleSheaf_hasExt B S hS) (extK := bigEtaleSheaf_hasExt B S hS)
        (injJ := smallEtaleSheaf_hasInjectiveResolutions B S hS)
        (injK := bigEtaleSheaf_hasInjectiveResolutions B S hS)
        (lanG := smallEtaleInclusion_hasPointwiseLeftKanExtension B S hS)
        (rexG := smallEtaleRestriction_preservesFiniteColimits' B S hS)
        (injG := smallEtaleRestriction_preservesInjectiveObjects B S hS)
        (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
        (SmallEtale.inclusion B S hS) (SmallEtale.finalIsTerminal B S hS)
        ((SmallEtale.finalIsTerminal B S hS).isTerminalObj
          (SmallEtale.inclusion B S hS) (SmallEtale.final B S hS))
        rfl F p :=
  rfl

/-- **Stacks 03YX, étale naturality.** The étale comparison commutes with morphisms of abelian
sheaves. -/
@[stacks 03YX "étale naturality"]
public theorem bigSmallEtaleSheafCohomologyIso_naturality
    [HasSheafify (BigEtaleOver.topology B S hS) Ab.{u + 1}]
    [HasSheafify (SmallEtale.topology B S hS) Ab.{u + 1}]
    [HasExt.{w} (Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) Ab.{u + 1})]
    {F G : Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1}}
    (f : F ⟶ G) (p : ℕ) (x : Sheaf.H.{w, u + 1} F p) :
    bigSmallEtaleSheafCohomologyIso B S hS G p (Sheaf.H.map f p x) =
      Sheaf.H.map
        (((SmallEtale.inclusion B S hS).sheafPushforwardContinuous
          Ab.{u + 1} (SmallEtale.topology B S hS)
          (BigEtaleOver.topology B S hS)).map f) p
        (bigSmallEtaleSheafCohomologyIso B S hS F p x) := by
  simp only [bigSmallEtaleSheafCohomologyIso_eq]
  exact Stacks.Cohomology.BiggerSite.sheafHAddEquiv_naturality.{w, u + 1}
    (extJ := smallEtaleSheaf_hasExt B S hS) (extK := bigEtaleSheaf_hasExt B S hS)
    (injJ := smallEtaleSheaf_hasInjectiveResolutions B S hS)
    (injK := bigEtaleSheaf_hasInjectiveResolutions B S hS)
    (lanG := smallEtaleInclusion_hasPointwiseLeftKanExtension B S hS)
    (rexG := smallEtaleRestriction_preservesFiniteColimits' B S hS)
    (injG := smallEtaleRestriction_preservesInjectiveObjects B S hS)
    (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
    (SmallEtale.inclusion B S hS) (SmallEtale.finalIsTerminal B S hS)
    ((SmallEtale.finalIsTerminal B S hS).isTerminalObj
      (SmallEtale.inclusion B S hS) (SmallEtale.final B S hS))
    rfl f p x

end AlgebraicGeometry

end
