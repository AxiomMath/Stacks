module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiToBig
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismsOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Continuous

/-!
# The small Zariski topos as a retract of the big Zariski topos

For a scheme `S` in a big Zariski site, the inclusion of its small Zariski site into the big
Zariski site over `S` is a morphism of sites, and the resulting morphism of topoi

`π_S : Sh((Sch/S)_Zar) ⟶ Sh(S_Zar)`

is a retraction of the morphism `i_S = i_{id_S}` of Stacks 020Y: `π_S ∘ i_S = id`. Inverse
image along `i_S` is direct image along `π_S`, namely restriction of a big-site sheaf to the
small site, so `i_S⁻¹(𝒢)(U/S) = 𝒢(U/S)`.

## Main definitions

* `AlgebraicGeometry.smallZariskiProjection` — the morphism of topoi `π_S`.

## Main results

* `AlgebraicGeometry.smallZariskiInclusion_isContinuous` and
  `AlgebraicGeometry.smallZariskiInclusion_preservesFiniteLimits` are the site-level
  hypotheses which make `π_S` a morphism of topoi.
* `AlgebraicGeometry.smallZariskiProjection_comp_identity` is the retraction.
* `AlgebraicGeometry.smallZariskiIdentityInverseImageIsoProjectionPushforward` and
  `AlgebraicGeometry.smallZariskiIdentityInverseImageSections` identify inverse image along
  `i_S` with restriction, as a natural isomorphism of functors and on sections.

## Implementation notes

The inclusion functor is the one from Stacks 020T, and its cocontinuity is the cocontinuity
of Stacks 020Y at the identity of `S`, so no second copy of either is introduced; the two
preservation properties it needs are in the file on limits in the Zariski sites. Continuity
and left exactness on sheaves are stated separately from the bundled morphism-of-sites API,
which is limited to sites whose object and morphism universes coincide.

Equality of geometric morphisms is expressed throughout by a natural isomorphism of their
inverse-image functors; being an isomorphism of functors rather than a bijection on global
sections, the last statement carries the naturality in both the sheaf and the small-site
object that the source's formula on sections asserts.

## References

* [Stacks Project, Tag 020Z](https://stacks.math.columbia.edu/tag/020Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry


add_to_stacks 020Z "full faithfulness of the small-site inclusion"
  CategoryTheory.ObjectProperty.fullyFaithfulι

add_to_stacks 020Z "cocontinuity of the small-site inclusion"
  smallZariskiToBigZariskiFunctor_isCocontinuous

variable (B : BigZariskiSite.{u}) (S : B.Schemes)

/-- The inclusion of the small Zariski site in the big slice site is continuous. -/
@[stacks 020Z "continuity of the site morphism"]
public instance smallZariskiInclusion_isContinuous :
    (SmallZariski.inclusion B S.obj S.property).IsContinuous
      (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property) := by
  let v := smallZariskiToBigZariskiFunctor B S S (𝟙 S)
  have e : v = SmallZariski.inclusion B S.obj S.property := by
    dsimp [v, smallZariskiToBigZariskiFunctor]
    rw [Over.mapId_eq]
    rfl
  exact e ▸ smallZariskiToBigZariskiFunctor_isContinuous B S S (𝟙 S)

/-- The inverse-image functor of the site morphism is left exact. -/
@[stacks 020Z "exactness of the site morphism"]
public instance smallZariskiInclusion_preservesFiniteLimits :
    PreservesFiniteLimits
      ((SmallZariski.inclusion B S.obj S.property).sheafPullback (Type (u + 1))
        (SmallZariski.topology B S.obj S.property)
        (BigZariskiOver.topology B S.obj S.property)) := by
  let : HasFiniteLimits (SmallZariski B S.obj S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits (SmallZariski.inclusion B S.obj S.property) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks
      (SmallZariski.inclusion B S.obj S.property)
  have : RepresentablyFlat (SmallZariski.inclusion B S.obj S.property) :=
    flat_of_preservesFiniteLimits (SmallZariski.inclusion B S.obj S.property)
  let : PreservesFiniteLimits
      ((SmallZariski.inclusion B S.obj S.property).op.lan :
        ((SmallZariski B S.obj S.property)ᵒᵖ ⥤ Type (u + 1)) ⥤
          (BigZariskiOver B S.obj S.property)ᵒᵖ ⥤ Type (u + 1)) :=
    CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat.{u, u, u + 1, u + 1, u + 1}
      (SmallZariski.inclusion B S.obj S.property)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (SmallZariski.inclusion B S.obj S.property)
    (Type (u + 1))
    (SmallZariski.topology B S.obj S.property)
    (BigZariskiOver.topology B S.obj S.property)

/-- The projection `π_S` from the big Zariski topos to the small one. -/
@[stacks 020Z "the projection of topoi",
  stacks 04BS "restriction to the small Zariski site is its direct image"]
public noncomputable def smallZariskiProjection :
    MorphismOfTopoi
      (Sheaf (BigZariskiOver.topology B S.obj S.property) (Type (u + 1)))
      (Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1))) :=
  { pushforward := (SmallZariski.inclusion B S.obj S.property).sheafPushforwardContinuous
      (Type (u + 1)) (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property)
    inverseImage := (SmallZariski.inclusion B S.obj S.property).sheafPullback
      (Type (u + 1)) (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property)
    adj := (SmallZariski.inclusion B S.obj S.property).sheafAdjunctionContinuous
      (Type (u + 1)) (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property)
    preservesFiniteLimits := smallZariskiInclusion_preservesFiniteLimits B S }

/-- The inverse-image functor of `π_S ∘ i_{id_S}` is naturally the identity. -/
@[stacks 020Z "the retraction"]
public noncomputable def smallZariskiProjection_comp_identity :
    ((smallZariskiProjection B S).comp
      (smallZariskiToBigZariskiMorphism B S S (𝟙 S))).inverseImage ≅
        𝟭 (Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1))) := by
  let j := SmallZariski.inclusion B S.obj S.property
  let v := smallZariskiToBigZariskiFunctor B S S (𝟙 S)
  have e : v = j := by
    dsimp [v, j, smallZariskiToBigZariskiFunctor]
    rw [Over.mapId_eq]
    rfl
  let := smallZariskiToBigZariskiFunctor_isContinuous B S S (𝟙 S)
  let := smallZariskiToBigZariskiFunctor_isCocontinuous B S S (𝟙 S)
  let : j.IsCocontinuous (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property) := e ▸ inferInstance
  let : j.Full := by
    dsimp [j, SmallZariski.inclusion]
    infer_instance
  let : j.Faithful := by
    dsimp [j, SmallZariski.inclusion]
    infer_instance
  let : ∀ F : (SmallZariski B S.obj S.property)ᵒᵖ ⥤ Type (u + 1),
      j.op.HasPointwiseRightKanExtension F := fun _ => inferInstance
  have hff := Functor.full_and_faithful_sheafPullback j (Type (u + 1))
    (SmallZariski.topology B S.obj S.property)
    (BigZariskiOver.topology B S.obj S.property)
  let : (smallZariskiProjection B S).inverseImage.Full := by
    change (j.sheafPullback (Type (u + 1)) (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property)).Full
    exact hff.1
  let : (smallZariskiProjection B S).inverseImage.Faithful := by
    change (j.sheafPullback (Type (u + 1)) (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property)).Faithful
    exact hff.2
  let : IsIso ((smallZariskiProjection B S).adj.unit) :=
    Adjunction.unit_isIso_of_L_fully_faithful (smallZariskiProjection B S).adj
  have hIso : (smallZariskiToBigZariskiMorphism B S S (𝟙 S)).inverseImage ≅
      (smallZariskiProjection B S).pushforward := by
    change v.sheafPullbackCocontinuous (Type (u + 1))
        (SmallZariski.topology B S.obj S.property)
        (BigZariskiOver.topology B S.obj S.property) ≅
      j.sheafPushforwardContinuous (Type (u + 1))
        (SmallZariski.topology B S.obj S.property)
        (BigZariskiOver.topology B S.obj S.property)
    exact (v.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type (u + 1)) (SmallZariski.topology B S.obj S.property)
        (BigZariskiOver.topology B S.obj S.property)).trans
      (Functor.sheafPushforwardContinuousIso (eqToIso e) (Type (u + 1))
        (SmallZariski.topology B S.obj S.property)
        (BigZariskiOver.topology B S.obj S.property))
  change (smallZariskiProjection B S).inverseImage ⋙
      (smallZariskiToBigZariskiMorphism B S S (𝟙 S)).inverseImage ≅
    𝟭 (Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1)))
  exact (Functor.isoWhiskerLeft (smallZariskiProjection B S).inverseImage
      hIso).trans
    (asIso ((smallZariskiProjection B S).adj.unit)).symm

/-- Inverse image along `i_S = i_{id_S}` is the direct image along `π_S`,
namely restriction of a big-site sheaf to the small site. -/
@[stacks 020Z "the inverse-image formula"]
public noncomputable def smallZariskiIdentityInverseImageIsoProjectionPushforward :
    (smallZariskiToBigZariskiMorphism B S S (𝟙 S)).inverseImage ≅
      (smallZariskiProjection B S).pushforward := by
  let v := smallZariskiToBigZariskiFunctor B S S (𝟙 S)
  have e : v = SmallZariski.inclusion B S.obj S.property := by
    dsimp [v, smallZariskiToBigZariskiFunctor]
    rw [Over.mapId_eq]
    rfl
  let := smallZariskiToBigZariskiFunctor_isContinuous B S S (𝟙 S)
  let := smallZariskiToBigZariskiFunctor_isCocontinuous B S S (𝟙 S)
  change v.sheafPullbackCocontinuous (Type (u + 1))
      (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property) ≅
    (SmallZariski.inclusion B S.obj S.property).sheafPushforwardContinuous
      (Type (u + 1)) (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property)
  exact (v.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (Type (u + 1)) (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property)).trans
    (Functor.sheafPushforwardContinuousIso (eqToIso e) (Type (u + 1))
      (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property))

/-- For a big-site sheaf `G` and an open subscheme `U / S`, inverse image
along `i_S` has sections canonically isomorphic to `G(U / S)`. -/
@[stacks 020Z "the formula on sections"]
public noncomputable def smallZariskiIdentityInverseImageSections
    (G : Sheaf (BigZariskiOver.topology B S.obj S.property) (Type (u + 1)))
    (U : SmallZariski B S.obj S.property) :
    (((smallZariskiToBigZariskiMorphism B S S (𝟙 S)).inverseImage.obj G).obj.obj
      (Opposite.op U)) ≅ G.obj.obj (Opposite.op U.obj) :=
  ((sheafToPresheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1)) ⋙
      (evaluation _ _).obj (Opposite.op U)).mapIso
    ((smallZariskiIdentityInverseImageIsoProjectionPushforward B S).app G)).trans
    (eqToIso ((SmallZariski.inclusion B S.obj S.property).sheafPushforwardContinuous_obj_obj_obj
      (Type (u + 1)) (SmallZariski.topology B S.obj S.property)
      (BigZariskiOver.topology B S.obj S.property) G (Opposite.op U)))

end AlgebraicGeometry
