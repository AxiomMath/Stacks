module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Faithful
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModel
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# The morphism of small étale ringed sites of a morphism of schemes

Let `f : T ⟶ S` be a morphism of schemes of a big étale site `B`. Stacks 070R, part (2) says
that the morphism of small étale sites `f_small : T_étale → S_étale` becomes a morphism of
*ringed* sites

```
  (f_small, f_small^♯) : (T_étale, 𝒪_T) ⟶ (S_étale, 𝒪_S)
```

in the sense of Stacks 03AD, the structure map being pullback of global functions along the
projection `T ×_S V ⟶ V`.

The small étale site of a scheme has objects in `Type (u + 1)` and morphisms in `Type u`, while
a morphism of ringed sites is read at the universe `u` of the sections of the structure sheaf.
So the site condition is needed for sheaves of sets in `Type u`, rather than in `Type (u + 1)`
as in `AlgebraicGeometry.smallEtaleBaseChange_isMorphismOfSites`; neither of the two implies the
other. It holds because the small étale site is essentially small at `u`
(`AlgebraicGeometry.SmallEtale.essentiallySmall`), so the question can be transported to a small
model at `Type u`.

## Main definitions

* `AlgebraicGeometry.smallEtaleRingedSiteHom` is the morphism of ringed sites
  `(f_small, f_small^♯)` of a morphism of schemes.

## Main results

* `AlgebraicGeometry.smallEtaleBaseChange_isMorphismOfSites_ringUniverse`: small étale base
  change defines a morphism of sites for sheaves of sets valued in the universe of the structure
  rings.

## Implementation notes

The left exact left adjoint of the direct image is the pullback along the transported base
change on the small models, conjugated by the two restriction equivalences between sheaves on a
small étale site and on its small model. The transport is the one of
`AlgebraicGeometry.Space.spacesToposMorphismTypeU` for the spaces-étale sites of algebraic
spaces.

## What is missing: Stacks 04I5

Stacks 04I5 says that `(f_small, f_small^♯)` is a morphism of *locally* ringed sites, that is
`(smallEtaleRingedSiteHom B a).IsLocallyRinged` in the form of
`AlgebraicGeometry.RingedSite.HomGeneral.IsLocallyRinged`. It is **not proved here**, and this
file carries no `@[stacks 04I5]` tag.

The source proves it by feeding condition (3) of Stacks 04H9 — at every point of `X_étale` the
induced map of stalks `(𝒪_Y)_ȳ ⟶ (𝒪_X)_x̄` is a local ring map — to the stalk criterion. Three
inputs of that argument are absent from the library.

* The stalk criterion of Stacks 04H9 is available only for
  `Stacks.Sheaves.LocallyRingedTopos.RingedTopos`, which has `C : Type u` with `Category.{u} C`,
  so the small étale site is not an instance of it; and its
  `Stacks.Sheaves.LocallyRingedTopos.RingedToposHom` carries the identification
  `f⁻¹(𝒪_Y^*) ≅ (f⁻¹𝒪_Y)^*` as *data*, so its conclusion is not stated about
  `AlgebraicGeometry.RingedToposHom.IsLocallyRinged`.
* That identification, and the corresponding `(𝒪^*)_p ≅ (𝒪_p)^*` for a point, are not available
  for `AlgebraicGeometry.RingedSite.unitsSheaf`. Both would follow from exactness of the two
  functors once the units sheaf is exhibited as the fibre product of the multiplication
  `Stacks.Sheaves.ToposPullback.Sheaf.ringMulHom` along the unit section
  `Stacks.Sheaves.ToposPullback.Sheaf.ringOneHom`.
* No declaration asserts `IsLocalHom` for the map of étale local rings at a geometric point and
  its image.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Conjugate

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- Conjugating a left adjoint by equivalences on both sides: if `P₀ ⊣ W ⋙ R ⋙ V` with `V` and
`W` equivalences, then `V ⋙ P₀ ⋙ W` is a left adjoint of `R`. -/
private def adjunction_of_conjugate
    {A : Type u₁} [Category.{v₁} A] {A₀ : Type u₂} [Category.{v₂} A₀]
    {B₀ : Type u₃} [Category.{v₃} B₀] {E : Type u₄} [Category.{v₄} E]
    (V : A ⥤ A₀) (W : B₀ ⥤ E) (R : E ⥤ A) (P₀ : A₀ ⥤ B₀)
    [V.IsEquivalence] [W.IsEquivalence] (adj₀ : P₀ ⊣ W ⋙ R ⋙ V) :
    (V ⋙ P₀) ⋙ W ⊣ R :=
  have hiso : W.asEquivalence.inverse ⋙ ((W ⋙ R ⋙ V) ⋙ V.asEquivalence.inverse) ≅ R :=
    Functor.isoWhiskerLeft W.asEquivalence.inverse
        (Functor.associator W (R ⋙ V) V.asEquivalence.inverse) ≪≫
      W.asEquivalence.invFunIdAssoc ((R ⋙ V) ⋙ V.asEquivalence.inverse) ≪≫
      Functor.associator R V V.asEquivalence.inverse ≪≫
      Functor.isoWhiskerLeft R V.asEquivalence.unitIso.symm ≪≫ R.rightUnitor
  ((V.asEquivalence.toAdjunction.comp adj₀).comp
    W.asEquivalence.toAdjunction).ofNatIsoRight hiso

end Conjugate

variable (B : BigEtaleSite.{u})

section RingUniverse

variable {S T : B.Scheme} (f : T ⟶ S)

/-- The small étale topology of `S`, transported to a small model of the small étale site at the
universe of the structure rings. -/
private abbrev smallModelEtaleTopology (Z : B.Scheme) :
    GrothendieckTopology (SmallModel.{u} (SmallEtale B Z.obj Z.property)) :=
  RingedTopos.smallModelTopology (SmallEtale.topology B Z.obj Z.property)

/-- Small étale base change, transported to the small models of the two sites. -/
private abbrev smallModelEtaleBaseChange :
    SmallModel.{u} (SmallEtale B S.obj S.property) ⥤
      SmallModel.{u} (SmallEtale B T.obj T.property) :=
  (equivSmallModel.{u} (SmallEtale B S.obj S.property)).inverse ⋙
    smallEtaleBaseChange B f ⋙ (equivSmallModel.{u} (SmallEtale B T.obj T.property)).functor

/-- The transported base change is continuous for the transported topologies. -/
private instance isContinuous_smallModelEtaleBaseChange :
    (smallModelEtaleBaseChange B f).IsContinuous
      (smallModelEtaleTopology B S) (smallModelEtaleTopology B T) :=
  have : (smallEtaleBaseChange B f ⋙
      (equivSmallModel.{u} (SmallEtale B T.obj T.property)).functor).IsContinuous
      (SmallEtale.topology B S.obj S.property) (smallModelEtaleTopology B T) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B T.obj T.property) _
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S.obj S.property) _

/-- The comma categories indexing the right Kan extension along the comparison of a small étale
site with its small model have limits of sets in universe `u`. -/
private instance hasLimitsOfShape_structuredArrow_smallModelEtale_inverse_op
    (Z : B.Scheme) (W : (SmallEtale B Z.obj Z.property)ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow W (equivSmallModel.{u} (SmallEtale B Z.obj Z.property)).inverse.op)
      (Type u) :=
  inferInstance

/-- The comma categories indexing the right Kan extension along the comparison of the small model
of a small étale site with the site have limits of sets in universe `u`. -/
private instance hasLimitsOfShape_structuredArrow_smallModelEtale_functor_op
    (Z : B.Scheme) (W : (SmallModel.{u} (SmallEtale B Z.obj Z.property))ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow W (equivSmallModel.{u} (SmallEtale B Z.obj Z.property)).functor.op)
      (Type u) :=
  inferInstance

/-- Restriction of sheaves of sets along the comparison of the small étale site of the source
with its small model. -/
private abbrev smallModelEtaleRestrictSource (Z : B.Scheme) :
    Sheaf (SmallEtale.topology B Z.obj Z.property) (Type u) ⥤
      Sheaf (smallModelEtaleTopology B Z) (Type u) :=
  (equivSmallModel.{u} (SmallEtale B Z.obj Z.property)).inverse.sheafPushforwardContinuous
    (Type u) (smallModelEtaleTopology B Z) (SmallEtale.topology B Z.obj Z.property)

/-- Restriction of sheaves of sets along the comparison, in the other direction, of the small
étale site of the target with its small model. -/
private abbrev smallModelEtaleRestrictTarget (Z : B.Scheme) :
    Sheaf (smallModelEtaleTopology B Z) (Type u) ⥤
      Sheaf (SmallEtale.topology B Z.obj Z.property) (Type u) :=
  (equivSmallModel.{u} (SmallEtale B Z.obj Z.property)).functor.sheafPushforwardContinuous
    (Type u) (SmallEtale.topology B Z.obj Z.property) (smallModelEtaleTopology B Z)

/-- The direct image of base change on sheaves of sets valued in the universe of the structure
rings. -/
private abbrev smallEtaleDirectImageRingUniverse :
    Sheaf (SmallEtale.topology B T.obj T.property) (Type u) ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) (Type u) :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- The inverse image of the transported base change, on the small models. -/
private abbrev smallModelEtalePullback :
    Sheaf (smallModelEtaleTopology B S) (Type u) ⥤ Sheaf (smallModelEtaleTopology B T) (Type u) :=
  (smallModelEtaleBaseChange B f).sheafPullback (Type u)
    (smallModelEtaleTopology B S) (smallModelEtaleTopology B T)

/-- The direct image of the transported base change is the direct image of base change,
conjugated by the two restrictions along the comparisons with the small models. -/
private theorem sheafPushforwardContinuous_smallModelEtaleBaseChange :
    ((equivSmallModel.{u} (SmallEtale B T.obj T.property)).functor.sheafPushforwardContinuous
        (Type u) (SmallEtale.topology B T.obj T.property) (smallModelEtaleTopology B T)) ⋙
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)) ⋙
      ((equivSmallModel.{u} (SmallEtale B S.obj S.property)).inverse.sheafPushforwardContinuous
        (Type u) (smallModelEtaleTopology B S) (SmallEtale.topology B S.obj S.property)) =
    (smallModelEtaleBaseChange B f).sheafPushforwardContinuous (Type u)
      (smallModelEtaleTopology B S) (smallModelEtaleTopology B T) := rfl

/-- **Stacks 021I at the universe of the structure rings.** Base change along `f : T ⟶ S` defines
a morphism of sites from the small étale site of `T` to that of `S`, for sheaves of sets valued in
the universe `u` of the sections of the structure sheaves. -/
@[stacks 021I "small_etale_morphism at the universe of the structure rings"]
public instance smallEtaleBaseChange_isMorphismOfSites_ringUniverse :
    IsMorphismOfSites.{u} (smallEtaleBaseChange B f)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) := by
  have hP₀ : PreservesFiniteLimits (smallModelEtalePullback B f) :=
    Functor.preservesFiniteLimits_sheafPullback _ _ _
  have : PreservesFiniteLimits
      (smallModelEtaleRestrictSource B S ⋙ smallModelEtalePullback B f) :=
    comp_preservesFiniteLimits _ _
  exact
    { __ := (inferInstance : (smallEtaleBaseChange B f).IsContinuous
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property))
      hasExactLeftAdjoint :=
        ⟨(smallModelEtaleRestrictSource B S ⋙ smallModelEtalePullback B f) ⋙
            smallModelEtaleRestrictTarget B T,
          ⟨adjunction_of_conjugate (smallModelEtaleRestrictSource B S)
            (smallModelEtaleRestrictTarget B T) (smallEtaleDirectImageRingUniverse B f)
            (smallModelEtalePullback B f)
            (((smallModelEtaleBaseChange B f).sheafAdjunctionContinuous (Type u)
                (smallModelEtaleTopology B S) (smallModelEtaleTopology B T)).ofNatIsoRight
              (eqToIso (sheafPushforwardContinuous_smallModelEtaleBaseChange B f).symm))⟩,
          comp_preservesFiniteLimits _ _⟩ }

end RingUniverse

/-- **Stacks 070R, part (2).** The morphism of ringed sites
`(f_small, f_small^♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` attached to a morphism of schemes
`a : X ⟶ Y`: the underlying morphism of sites is base change of étale `Y`-schemes along `a`, and
the structure map pulls a global function on an étale `V / Y` back along the projection
`X ×_Y V ⟶ V`. -/
@[stacks 070R "part (2): the morphism of ringed sites of the small étale sites of schemes"]
public def smallEtaleRingedSiteHom {X Y : B.Scheme} (a : X ⟶ Y) :
    RingedSite.HomGeneral (smallEtaleRingedSite B X.obj X.property)
      (smallEtaleRingedSite B Y.obj Y.property) where
  u := smallEtaleBaseChange B a
  isMorphismOfSites := smallEtaleBaseChange_isMorphismOfSites_ringUniverse B a
  fsharp := structureSharp B a

/-- The underlying morphism of sites of `(f_small, f_small^♯)` is small étale base change. -/
@[simp]
public theorem smallEtaleRingedSiteHom_u {X Y : B.Scheme} (a : X ⟶ Y) :
    (smallEtaleRingedSiteHom B a).u = smallEtaleBaseChange B a := rfl

/-- The structure map of `(f_small, f_small^♯)` is `AlgebraicGeometry.structureSharp`, that is
pullback of global functions along the base-change projection. -/
@[simp]
public theorem smallEtaleRingedSiteHom_fsharp {X Y : B.Scheme} (a : X ⟶ Y) :
    (smallEtaleRingedSiteHom B a).fsharp = structureSharp B a := rfl

end AlgebraicGeometry

end
